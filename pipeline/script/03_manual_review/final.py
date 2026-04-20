"""
Final reasoned verdicts for all sampled transactions in cat1, cat2, cat5.

For each transaction:
  1. Parse the inspect file (cycle structure, addresses, amounts)
  2. Resolve addresses (pools, tokens, routers, bots, EOAs)
  3. Verify the cycle makes economic sense
  4. Produce a reasoned verdict

Reads from:
  - manual_review/inspections/cat*/tx_*.txt
  - manual_review/addresses/resolved_addresses.csv
Writes to:
  - manual_review/verdicts/final_verdicts_cat{1,2,5}.csv
  - manual_review/verdicts/final_verdicts_summary.txt
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import re
from collections import Counter

from config import (
    INSPECTIONS_DIR, ADDRESSES_DIR, VERDICTS_DIR,
    CATEGORY_FOLDERS, KNOWN_ADDRESSES,
    is_dex_pool, is_router,
)

FINAL_VERDICTS_DIR = VERDICTS_DIR / "12_final_verdicts"
FINAL_VERDICTS_DIR.mkdir(parents=True, exist_ok=True)

ETH_ADDR_RE = re.compile(r"0x[0-9a-f]{40}")


def load_address_labels():
    """Load resolved addresses into a dict: addr -> (name, is_contract)."""
    labels = {}
    # Start with hardcoded
    for addr, name in KNOWN_ADDRESSES.items():
        labels[addr] = (name, True)
    # Load Blockscout resolutions
    path = ADDRESSES_DIR / "resolved_addresses.csv"
    if path.exists():
        with open(path, "r") as f:
            reader = csv.reader(f)
            next(reader)
            for row in reader:
                addr = row[0].lower()
                name = row[1]
                is_contract = row[2] == "True"
                labels[addr] = (name or ("contract" if is_contract else "EOA"), is_contract)
    return labels


    # is_dex_pool, is_router imported from config


def is_token(name):
    """Check if the name is a known token."""
    token_names = {
        "weth", "usdc", "usdt", "dai", "wbtc", "1inch",
        "link", "wsteth", "uni", "frax", "crv", "eth",
    }
    return name.lower().split()[0].lower() in token_names


def parse_transfers(content):
    """Parse all transfers from an inspect file."""
    transfers = []
    lines = content.split("\n")
    current = {}
    section = "unknown"

    for line in lines:
        s = line.strip()
        if "CYCLES:" in s and "LEFTOVER" not in s:
            section = "cycle"
            continue
        elif "LEFTOVER CYCLES" in s:
            section = "leftover_cycle"
            continue
        elif "LEFTOVERS (unexplained)" in s:
            section = "leftover"
            continue
        elif "TRANSACTION COSTS:" in s:
            section = "costs"
            continue

        if section not in ("cycle", "leftover_cycle"):
            continue

        addrs = ETH_ADDR_RE.findall(s.lower())
        if s.startswith("[") and addrs:
            current = {"from": addrs[0], "section": section}
        elif s.startswith("->") and addrs:
            current["to"] = addrs[0]
        elif current.get("to") and s and not s.startswith("[") and not s.startswith("->"):
            current["amount_line"] = s
            transfers.append(current)
            current = {}
        elif addrs and not s.startswith("[") and not s.startswith("->"):
            if "from" not in current:
                current = {"from": addrs[0], "section": section}
            elif "to" not in current:
                current["to"] = addrs[0]

    return transfers


def analyze_transaction(filepath, addr_labels):
    """Analyze a single transaction and return a reasoned verdict."""
    content = filepath.read_text()

    if "NOT IN ARGOS" in content:
        tx_match = re.search(r"TRANSACTION: (0x[0-9a-f]+)", content)
        eigenphi_main = "In Eigenphi main set:     YES" in content
        return {
            "tx_hash": tx_match.group(1) if tx_match else "?",
            "final_verdict": "N/A",
            "reasoning": "Transaction not in Argos dataset",
            "arb_type": "N/A",
            "has_lending": False,
            "pools": [],
            "routers": [],
            "n_transfers": 0,
            "n_cycles": 0,
            "tokens": [],
            "unverified_contracts": 0,
            "eigenphi": eigenphi_main,
            "profit_eth": None,
            "profit_other": {},
        }

    # Extract basic fields
    tx_hash = ""
    verdict = ""
    reasons = ""
    final_balances = []
    for line in content.split("\n"):
        s = line.strip()
        if s.startswith("TRANSACTION:"):
            tx_hash = s.split(":", 1)[1].strip()
        elif s.startswith("Verdict:"):
            verdict = s.split(":", 1)[1].strip()
        elif s.startswith("Reasons:"):
            reasons = s.split(":", 1)[1].strip()
        elif s.startswith("FINAL BALANCE:"):
            final_balances.append(s.split(":", 1)[1].strip())

    # Parse profit from final balances
    # ETH (null) and WETH are equivalent — sum them
    profit_eth = 0.0
    has_eth_balance = False
    profit_other = {}
    for bal in final_balances:
        parts = bal.split()
        if len(parts) >= 2:
            try:
                amount = float(parts[0].replace(",", ""))
            except ValueError:
                continue
            token = parts[-1]
            if token in ("ETH", "WETH", "(null)", "?"):
                profit_eth += amount
                has_eth_balance = True
            else:
                profit_other[token] = amount
    if not has_eth_balance:
        profit_eth = None

    transfers = parse_transfers(content)
    cycle_transfers = [t for t in transfers if t.get("section") == "cycle"]
    leftover_transfers = [t for t in transfers if t.get("section") == "leftover_cycle"]

    eigenphi_main = "In Eigenphi main set:     YES" in content

    if not cycle_transfers:
        return {
            "tx_hash": tx_hash,
            "final_verdict": "INCONCLUSIVE",
            "reasoning": "No cycle transfers parsed from inspect file",
            "arb_type": "unknown",
            "has_lending": False,
            "pools": [],
            "routers": [],
            "n_transfers": 0,
            "n_cycles": 0,
            "tokens": [],
            "unverified_contracts": 0,
            "eigenphi": eigenphi_main,
            "profit_eth": None,
            "profit_other": {},
        }

    # Resolve all addresses in the cycle
    all_addrs = set()
    for t in cycle_transfers:
        all_addrs.add(t.get("from", ""))
        all_addrs.add(t.get("to", ""))

    # Classify addresses
    pools = []
    routers = []
    unknown_contracts = []
    eoas = []

    for addr in all_addrs:
        if not addr:
            continue
        name, is_contract = addr_labels.get(addr, ("unknown", False))
        if is_dex_pool(name):
            pools.append((addr, name))
        elif is_router(name):
            routers.append((addr, name))
        elif name in ("EOA", "unknown") and not is_contract:
            eoas.append(addr)
        elif is_contract and name == "unverified contract":
            unknown_contracts.append(addr)
        # else: known token contracts, factories, etc.

    # Check cycle closure
    first_from = cycle_transfers[0].get("from", "")
    last_to = cycle_transfers[-1].get("to", "")
    cycle_closes = first_from == last_to

    # Check token flow
    first_token = cycle_transfers[0].get("amount_line", "").split()[-1] if cycle_transfers[0].get("amount_line") else ""
    last_token = cycle_transfers[-1].get("amount_line", "").split()[-1] if cycle_transfers[-1].get("amount_line") else ""

    # ETH/WETH equivalence
    eth_equiv = {"WETH", "ETH", "(native)"}
    stable_equiv = {"USDC", "USDT", "DAI"}
    tokens_match = (
        first_token == last_token
        or {first_token, last_token} <= eth_equiv
        or {first_token, last_token} <= stable_equiv
    )

    # Collect unique tokens
    tokens = set()
    for t in cycle_transfers:
        amt = t.get("amount_line", "")
        if amt:
            tok = amt.split()[-1]
            if tok:
                tokens.add(tok)

    # Check lending in leftover cycles
    has_lending = False
    i = 0
    while i + 1 < len(leftover_transfers):
        t1 = leftover_transfers[i]
        t2 = leftover_transfers[i + 1]
        tok1 = t1.get("amount_line", "").split()[-1] if t1.get("amount_line") else ""
        tok2 = t2.get("amount_line", "").split()[-1] if t2.get("amount_line") else ""
        if (tok1 and tok1 == tok2
                and t1.get("from", "").lower() == t2.get("to", "").lower()
                and t1.get("to", "").lower() == t2.get("from", "").lower()):
            has_lending = True
            break
        i += 2

    # Count cycles
    n_cycles_match = re.search(r"CYCLES: (\d+)", content)
    n_cycles = int(n_cycles_match.group(1)) if n_cycles_match else 0

    # Determine arbitrage type
    if n_cycles == 0:
        arb_type = "no cycles"
    elif n_cycles == 1 and len(cycle_transfers) <= 4:
        arb_type = "triangular"
    elif n_cycles == 1 and len(cycle_transfers) <= 8:
        arb_type = "multi-hop"
    elif n_cycles == 1:
        arb_type = "complex"
    else:
        arb_type = f"multi-cycle({n_cycles})"

    if has_lending:
        arb_type += "+lending"

    # Build reasoning
    reasoning_parts = []

    # Evidence FOR arbitrage
    evidence_for = []
    if cycle_closes:
        evidence_for.append("cycle closes (same initiator)")
    if tokens_match:
        evidence_for.append(f"token match ({first_token} in/out)")
    if len(pools) > 0:
        pool_names = [name for _, name in pools]
        evidence_for.append(f"routes through {len(pools)} DEX pools ({', '.join(list(set(pool_names))[:3])})")
    if n_cycles >= 1:
        evidence_for.append(f"{n_cycles} cycle(s) detected")
    if has_lending:
        evidence_for.append("flash loan borrow-repay detected in leftover cycles")

    # Evidence AGAINST / uncertainty
    evidence_against = []
    if not cycle_closes:
        evidence_against.append("cycle does not close")
    if not tokens_match:
        evidence_against.append(f"token mismatch ({first_token} vs {last_token})")
    if len(pools) == 0 and len(unknown_contracts) > 0:
        evidence_against.append(f"{len(unknown_contracts)} unverified contracts (may be pools)")
    if "negativeProfit" in reasons:
        evidence_against.append("negative profit after gas")
    if "leftoverTransaction" in reasons:
        evidence_against.append("unexplained leftover transfers")
    if "Mixed" in reasons:
        evidence_against.append("mixed multi-token balance")

    # Final verdict
    if cycle_closes and len(cycle_transfers) >= 2:
        if verdict == "arbitrage":
            if evidence_against:
                final_verdict = "ARBITRAGE"
                reasoning_parts.append("Confirmed arbitrage despite minor flags")
            else:
                final_verdict = "ARBITRAGE"
                reasoning_parts.append("Clean arbitrage")
        elif verdict == "warning":
            if "Mixed" in reasons:
                # Mixed multi-token balance — can't determine profitability
                # without a price oracle, even if negativeProfit is also set
                # (the ETH component may be negative while another token is positive)
                final_verdict = "UNCERTAIN_ARBITRAGE"
                reasoning_parts.append("Arbitrage structure but multi-token balance is indeterminate")
            elif "negativeProfit" in reasons or "finalBalanceNegative" in reasons:
                final_verdict = "ATTEMPTED_ARBITRAGE"
                reasoning_parts.append("Real arbitrage structure but unprofitable")
            elif "leftoverTransaction" in reasons:
                final_verdict = "PROBABLE_ARBITRAGE"
                reasoning_parts.append("Arbitrage cycle found but chain incomplete")
            else:
                final_verdict = "PROBABLE_ARBITRAGE"
                reasoning_parts.append("Warning-level arbitrage")
    elif not cycle_closes and len(cycle_transfers) >= 2:
        final_verdict = "SUSPICIOUS"
        reasoning_parts.append("Transfers exist but cycle does not close")
    else:
        final_verdict = "INCONCLUSIVE"
        reasoning_parts.append("Insufficient transfer data")

    # Compose full reasoning
    if evidence_for:
        reasoning_parts.append("Evidence: " + "; ".join(evidence_for))
    if evidence_against:
        reasoning_parts.append("Flags: " + "; ".join(evidence_against))

    return {
        "tx_hash": tx_hash,
        "final_verdict": final_verdict,
        "reasoning": ". ".join(reasoning_parts),
        "arb_type": arb_type,
        "has_lending": has_lending,
        "pools": [name for _, name in pools],
        "routers": [name for _, name in routers],
        "n_transfers": len(cycle_transfers),
        "n_cycles": n_cycles,
        "tokens": list(tokens),
        "unverified_contracts": len(unknown_contracts),
        "eigenphi": eigenphi_main,
        "profit_eth": profit_eth,
        "profit_other": profit_other,
    }


def main():
    print("Loading address labels...")
    addr_labels = load_address_labels()
    print(f"  {len(addr_labels)} addresses loaded")

    categories = [
        (CATEGORY_FOLDERS[1], 1),
        (CATEGORY_FOLDERS[2], 2),
        (CATEGORY_FOLDERS[3], 3),
    ]

    all_summaries = []

    for folder, cat_num in categories:
        folder_path = INSPECTIONS_DIR / folder
        if not folder_path.exists():
            print(f"  Skipping {folder} (not found)")
            continue

        results = []
        for txt_file in sorted(folder_path.glob("tx_*.txt")):
            result = analyze_transaction(txt_file, addr_labels)
            results.append(result)

        if not results:
            print(f"  Skipping {folder} (no tx files)")
            continue

        # Write CSV
        out_path = FINAL_VERDICTS_DIR / f"final_verdicts_cat{cat_num}.csv"
        with open(out_path, "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow([
                "tx_hash", "final_verdict", "arb_type",
                "has_lending", "n_cycles", "n_transfers",
                "n_tokens", "tokens", "pools", "routers",
                "unverified_contracts", "eigenphi",
                "profit_eth", "reasoning",
            ])
            for r in results:
                writer.writerow([
                    r["tx_hash"], r["final_verdict"], r["arb_type"],
                    r["has_lending"], r["n_cycles"], r["n_transfers"],
                    len(r["tokens"]), "|".join(r["tokens"][:5]),
                    "|".join(r["pools"][:5]),
                    "|".join(r["routers"][:5]),
                    r["unverified_contracts"], r["eigenphi"],
                    r["profit_eth"] if r["profit_eth"] is not None else "",
                    r["reasoning"],
                ])

        # Aggregate
        verdict_counts = Counter(r["final_verdict"] for r in results)
        type_counts = Counter(r["arb_type"] for r in results)
        lending_count = sum(1 for r in results if r["has_lending"])
        pool_counts = Counter()
        for r in results:
            for p in r["pools"]:
                pool_counts[p] += 1

        summary = []
        summary.append(f"\n{'=' * 60}")
        summary.append(f"CATEGORY {cat_num}: {folder}")
        summary.append(f"{'=' * 60}")
        summary.append(f"Total: {len(results)}")

        summary.append(f"\nFinal verdicts:")
        for v, c in verdict_counts.most_common():
            pct = 100 * c / len(results) if results else 0
            summary.append(f"  {v:25s}  {c:4d}  ({pct:.0f}%)")

        summary.append(f"\nArbitrage types:")
        for t, c in type_counts.most_common():
            summary.append(f"  {t:30s}  {c}")

        summary.append(f"\nFlash loan lending: {lending_count}/{len(results)} ({100*lending_count/len(results):.0f}%)")

        router_count = sum(1 for r in results if r["routers"])
        router_counts = Counter()
        for r in results:
            for rt in r["routers"]:
                router_counts[rt] += 1
        summary.append(f"\nRouter/aggregator involvement: {router_count}/{len(results)} ({100*router_count/len(results):.0f}%)")
        if router_counts:
            for rt, c in router_counts.most_common(10):
                summary.append(f"  {rt:30s}  {c}")

        # Eigenphi overlap
        eigenphi_count = sum(1 for r in results if r["eigenphi"])
        summary.append(f"\nEigenphi overlap: {eigenphi_count}/{len(results)} ({100*eigenphi_count/len(results):.0f}%)")

        # Token stats
        token_counts_per_tx = [len(r["tokens"]) for r in results if r["tokens"]]
        if token_counts_per_tx:
            avg_tokens = sum(token_counts_per_tx) / len(token_counts_per_tx)
            summary.append(f"\nTokens per tx: avg={avg_tokens:.1f}, min={min(token_counts_per_tx)}, max={max(token_counts_per_tx)}")
        all_tokens = Counter()
        for r in results:
            for t in r["tokens"]:
                all_tokens[t] += 1
        summary.append(f"Top tokens:")
        for t, c in all_tokens.most_common(10):
            summary.append(f"  {t:20s}  {c}")

        # Pool stats
        pool_counts_per_tx = [len(r["pools"]) for r in results if r["pools"]]
        if pool_counts_per_tx:
            avg_pools = sum(pool_counts_per_tx) / len(pool_counts_per_tx)
            summary.append(f"\nPools per tx: avg={avg_pools:.1f}, min={min(pool_counts_per_tx)}, max={max(pool_counts_per_tx)}")
        summary.append(f"Top pools:")
        for p, c in pool_counts.most_common(10):
            summary.append(f"  {p:30s}  {c}")

        # Unverified contracts
        unverified_count = sum(1 for r in results if r["unverified_contracts"] > 0)
        total_unverified = sum(r["unverified_contracts"] for r in results)
        summary.append(f"\nTxs with unverified contracts: {unverified_count}/{len(results)} ({100*unverified_count/len(results):.0f}%), total unverified: {total_unverified}")

        # Profit stats (ETH/WETH only)
        profits = [r["profit_eth"] for r in results if r["profit_eth"] is not None]
        if profits:
            profitable = [p for p in profits if p > 0]
            unprofitable = [p for p in profits if p <= 0]
            summary.append(f"\nProfit (ETH/WETH): {len(profits)} txs with parseable profit")
            summary.append(f"  Profitable: {len(profitable)}, Unprofitable: {len(unprofitable)}")
            if profitable:
                fmt = lambda v: f"{v:.18f}".rstrip("0").rstrip(".")
                summary.append(f"  Profitable range: {fmt(min(profitable))} — {fmt(max(profitable))} ETH")
                summary.append(f"  Median profit: {fmt(sorted(profitable)[len(profitable)//2])} ETH")

        # Multi-cycle breakdown
        multi_cycle = sum(1 for r in results if r["n_cycles"] > 1)
        summary.append(f"\nMulti-cycle txs: {multi_cycle}/{len(results)} ({100*multi_cycle/len(results):.0f}%)")

        summary.append(f"\nSaved to {out_path}")

        for line in summary:
            print(line)
        all_summaries.extend(summary)

    # Save summary
    summary_path = FINAL_VERDICTS_DIR / "final_verdicts_summary.txt"
    with open(summary_path, "w") as f:
        f.write("\n".join(all_summaries) + "\n")
    print(f"\nSummary saved to {summary_path}")


if __name__ == "__main__":
    main()
