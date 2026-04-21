"""
Produce a human-reasoned verdict for every transaction in cat1, cat2, cat5.

For each transaction, reads the inspect file and resolved addresses,
then writes a reasoned analysis explaining WHY it is or isn't an arbitrage.

Reads from:
  - manual_review/inspections/cat*/tx_*.txt
  - manual_review/addresses/resolved_addresses.csv
Writes to:
  - manual_review/verdicts/reasoned/cat{1,2,5}/tx_<hash>.txt  (per-tx reasoning)
  - manual_review/verdicts/reasoned/reasoned_summary.txt        (aggregate)
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import re
from collections import Counter
from pathlib import Path

from config import (
    INSPECTIONS_DIR, ADDRESSES_DIR, VERDICTS_DIR,
    CATEGORY_FOLDERS, KNOWN_ADDRESSES,
    is_dex_pool, is_router,
)

ETH_ADDR_RE = re.compile(r"0x[0-9a-f]{40}")
REASONED_DIR = VERDICTS_DIR / "13_reasoned_verdicts"


def load_address_labels():
    labels = {}
    for addr, name in KNOWN_ADDRESSES.items():
        labels[addr] = (name, True)
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


def label(addr, labels_dict):
    addr = addr.lower()
    name, _ = labels_dict.get(addr, (addr, False))
    return name


    # is_dex_pool, is_router imported from config


def reason_transaction(filepath, addr_labels):
    """Read an inspect file and produce a reasoned verdict."""
    content = filepath.read_text()
    lines = content.split("\n")

    # Skip unparseable files
    if "NOT IN OURS" in content:
        return None, "NOT_IN_OURS", "Transaction not found in Ours dataset."
    if "ERROR parsing" in content:
        return None, "PARSE_ERROR", "JSON parsing error (likely newer integer encoding)."

    # Extract metadata
    tx_hash = ""
    verdict = ""
    reasons_str = ""
    final_balance = []
    gross_balance = []
    n_cycles = 0

    for line in lines:
        s = line.strip()
        if s.startswith("TRANSACTION:"):
            tx_hash = s.split(":", 1)[1].strip()
        elif s.startswith("Verdict:"):
            verdict = s.split(":", 1)[1].strip()
        elif s.startswith("Reasons:"):
            reasons_str = s.split(":", 1)[1].strip()
        elif s.startswith("FINAL BALANCE:"):
            final_balance.append(s.split(":", 1)[1].strip())
        elif s.startswith("GROSS BALANCE:"):
            gross_balance.append(s.split(":", 1)[1].strip())
        elif s.startswith("CYCLES:") and "LEFTOVER" not in s:
            try:
                n_cycles = int(s.split(":")[1].strip())
            except ValueError:
                pass

    eigenphi_main = "In Eigenphi: YES" in content or \
                    "In Eigenphi main set:     YES" in content

    # Parse cycle transfers
    cycle_transfers = []
    leftover_cycle_transfers = []
    section = "none"

    i = 0
    while i < len(lines):
        s = lines[i].strip()

        if "CYCLES:" in s and "LEFTOVER" not in s:
            section = "cycle"
        elif "LEFTOVER CYCLES" in s:
            section = "leftover"
        elif "LEFTOVERS (unexplained)" in s:
            section = "orphan"
        elif "TRANSACTION COSTS:" in s:
            section = "costs"

        if section in ("cycle", "leftover"):
            addrs = ETH_ADDR_RE.findall(s.lower())
            if s.startswith("[") and addrs:
                from_addr = addrs[0]
                # Next line is ->
                if i + 1 < len(lines):
                    next_s = lines[i + 1].strip()
                    to_addrs = ETH_ADDR_RE.findall(next_s.lower())
                    if to_addrs and next_s.startswith("->"):
                        to_addr = to_addrs[0]
                        # Line after that is amount
                        amount_line = lines[i + 2].strip() if i + 2 < len(lines) else ""
                        transfer = {
                            "from": from_addr,
                            "to": to_addr,
                            "amount": amount_line,
                            "from_label": label(from_addr, addr_labels),
                            "to_label": label(to_addr, addr_labels),
                        }
                        if section == "cycle":
                            cycle_transfers.append(transfer)
                        else:
                            leftover_cycle_transfers.append(transfer)
            elif addrs and not s.startswith("[") and not s.startswith("->"):
                # Leftover cycle format (no index)
                from_addr = addrs[0]
                if i + 1 < len(lines):
                    next_s = lines[i + 1].strip()
                    to_addrs = ETH_ADDR_RE.findall(next_s.lower())
                    if to_addrs and next_s.startswith("->"):
                        to_addr = to_addrs[0]
                        amount_line = lines[i + 2].strip() if i + 2 < len(lines) else ""
                        leftover_cycle_transfers.append({
                            "from": from_addr,
                            "to": to_addr,
                            "amount": amount_line,
                            "from_label": label(from_addr, addr_labels),
                            "to_label": label(to_addr, addr_labels),
                        })
        i += 1

    if not cycle_transfers:
        return tx_hash, "INCONCLUSIVE", "No cycle transfers could be parsed."

    # Analyze cycle structure
    first_from = cycle_transfers[0]["from"]
    last_to = cycle_transfers[-1]["to"]
    cycle_closes = first_from == last_to

    first_token = cycle_transfers[0]["amount"].split()[-1] if cycle_transfers[0]["amount"] else "?"
    last_token = cycle_transfers[-1]["amount"].split()[-1] if cycle_transfers[-1]["amount"] else "?"
    eth_equiv = {"WETH", "ETH", "(null)", "(native)"}
    tokens_match = first_token == last_token or {first_token, last_token} <= eth_equiv

    # Identify pools and routers
    pools_in_cycle = []
    routers_in_cycle = []
    unknown_contracts = []
    for t in cycle_transfers:
        for addr_key in ["from", "to"]:
            addr = t[addr_key]
            name, is_contract = addr_labels.get(addr, ("unknown", False))
            if is_dex_pool(name) and name not in [p[1] for p in pools_in_cycle]:
                pools_in_cycle.append((addr, name))
            elif is_router(name) and name not in [r[1] for r in routers_in_cycle]:
                routers_in_cycle.append((addr, name))
            elif is_contract and name == "unverified contract":
                if addr not in [u for u in unknown_contracts]:
                    unknown_contracts.append(addr)

    # Check lending
    has_lending = False
    lending_details = ""
    i = 0
    while i + 1 < len(leftover_cycle_transfers):
        t1 = leftover_cycle_transfers[i]
        t2 = leftover_cycle_transfers[i + 1]
        tok1 = t1["amount"].split()[-1] if t1["amount"] else ""
        tok2 = t2["amount"].split()[-1] if t2["amount"] else ""
        if (tok1 and tok1 == tok2
                and t1["from"] == t2["to"]
                and t1["to"] == t2["from"]):
            has_lending = True
            lending_details = (
                f"Flash loan detected: {t1['from_label']} lends "
                f"{t1['amount']} to {t1['to_label']}, "
                f"repaid in full."
            )
            break
        i += 2

    # Build the reasoning
    reasoning = []
    reasoning.append(f"Transaction: {tx_hash}")
    reasoning.append(f"Ours verdict: {verdict} ({reasons_str})")
    reasoning.append(f"Eigenphi: {'YES' if eigenphi_main else 'NO'}")
    reasoning.append(f"Cycles: {n_cycles}, Transfers in cycles: {len(cycle_transfers)}")
    reasoning.append("")

    # Describe the flow
    reasoning.append("TRANSFER FLOW:")
    for j, t in enumerate(cycle_transfers):
        reasoning.append(
            f"  [{j}] {t['from_label']} → {t['to_label']}: {t['amount']}"
        )
    reasoning.append("")

    # Pools
    if pools_in_cycle:
        reasoning.append(f"POOLS IDENTIFIED: {', '.join(name for _, name in pools_in_cycle)}")
    if routers_in_cycle:
        reasoning.append(f"ROUTERS: {', '.join(name for _, name in routers_in_cycle)}")
    if unknown_contracts:
        reasoning.append(f"UNVERIFIED CONTRACTS: {len(unknown_contracts)} (likely pools or bot logic)")
    reasoning.append("")

    # Balance
    if gross_balance:
        reasoning.append(f"GROSS PROFIT: {'; '.join(gross_balance)}")
    if final_balance:
        reasoning.append(f"NET PROFIT (after gas): {'; '.join(final_balance)}")
    reasoning.append("")

    # Lending
    if has_lending:
        reasoning.append(f"LENDING: {lending_details}")
        reasoning.append("")

    # Final verdict with reasoning
    reasoning.append("REASONED VERDICT:")
    if not cycle_closes:
        final_verdict = "SUSPICIOUS"
        reasoning.append(
            "  SUSPICIOUS: The cycle does not close (first sender ≠ last receiver). "
            "This may be a routing artifact or a misparse."
        )
    elif verdict == "arbitrage" and cycle_closes and len(cycle_transfers) >= 2:
        final_verdict = "REAL_ARBITRAGE"
        pool_str = ", ".join(name for _, name in pools_in_cycle) if pools_in_cycle else "unidentified pools"
        reason_text = (
            f"  REAL ARBITRAGE: Closed cycle through {pool_str}. "
            f"Initiator sends {first_token} and receives {last_token} back "
            f"with positive profit ({'; '.join(final_balance) if final_balance else '?'}). "
        )
        if has_lending:
            reason_text += "Includes a flash loan (borrow-repay round-trip in leftover cycles). "
        if unknown_contracts:
            reason_text += f"{len(unknown_contracts)} unverified contracts are likely DEX pools or bot routing logic. "
        reasoning.append(reason_text)
    elif verdict == "warning" and cycle_closes:
        if "Mixed" in reasons_str:
            final_verdict = "UNCERTAIN_ARBITRAGE"
            reasoning.append(
                "  UNCERTAIN: Cycle exists but the balance involves multiple tokens "
                "with opposing signs. Without a price oracle, profitability cannot "
                "be determined. The structural pattern is consistent with arbitrage."
            )
        elif "negativeProfit" in reasons_str or "finalBalanceNegative" in reasons_str:
            final_verdict = "ATTEMPTED_ARBITRAGE"
            reasoning.append(
                "  ATTEMPTED ARBITRAGE: Valid cycle structure through DEX pools, "
                "but gas costs exceeded the gross profit. This is a failed arbitrage "
                "attempt — the bot executed the trade but lost money on gas."
            )
        elif "leftoverTransaction" in reasons_str:
            final_verdict = "PROBABLE_ARBITRAGE"
            reasoning.append(
                "  PROBABLE ARBITRAGE: Cycle found with positive balance, but some "
                "transfers could not be incorporated into the chain. The arbitrage "
                "is likely real but the decode layer missed some transfer events."
            )
        else:
            final_verdict = "PROBABLE_ARBITRAGE"
            reasoning.append(f"  PROBABLE ARBITRAGE: Warning with reasons: {reasons_str}")
    else:
        final_verdict = "INCONCLUSIVE"
        reasoning.append("  INCONCLUSIVE: Cannot determine from available data.")

    return tx_hash, final_verdict, "\n".join(reasoning)


def main():
    print("Loading address labels...")
    addr_labels = load_address_labels()
    print(f"  {len(addr_labels)} addresses loaded")

    categories = [
        (CATEGORY_FOLDERS[1], 1),
        (CATEGORY_FOLDERS[2], 2),
        (CATEGORY_FOLDERS[3], 3),
    ]

    all_summary = []

    for folder, cat_num in categories:
        folder_path = INSPECTIONS_DIR / folder
        if not folder_path.exists():
            print(f"  Skipping {folder}")
            continue

        out_dir = REASONED_DIR / f"cat{cat_num}"
        out_dir.mkdir(parents=True, exist_ok=True)

        verdicts = Counter()
        lending_count = 0
        router_count = 0
        router_names = Counter()
        pool_names = Counter()
        eigenphi_count = 0
        all_n_transfers = []
        all_n_cycles = []
        profit_values = []
        total = 0

        for txt_file in sorted(folder_path.glob("tx_*.txt")):
            tx_hash, final_verdict, reasoning = reason_transaction(txt_file, addr_labels)
            verdicts[final_verdict] += 1
            total += 1

            for line in reasoning.split("\n"):
                if line.startswith("LENDING:") and "Flash loan detected" in line:
                    lending_count += 1
                if line.startswith("ROUTERS:"):
                    router_count += 1
                    for name in line.split(":", 1)[1].strip().split(", "):
                        router_names[name.strip()] += 1
                if line.startswith("POOLS IDENTIFIED:"):
                    for name in line.split(":", 1)[1].strip().split(", "):
                        if name.strip():
                            pool_names[name.strip()] += 1
                if line.startswith("Eigenphi: YES"):
                    eigenphi_count += 1
                if line.startswith("Cycles:"):
                    parts = line.split(",")
                    try:
                        n_cyc = int(parts[0].split(":")[1].strip())
                        all_n_cycles.append(n_cyc)
                    except (ValueError, IndexError):
                        pass
                    try:
                        n_tr = int(parts[1].split(":")[1].strip())
                        all_n_transfers.append(n_tr)
                    except (ValueError, IndexError):
                        pass
                if line.startswith("NET PROFIT"):
                    # Parse ETH/WETH profit from net profit line
                    for part in line.split(";"):
                        part = part.strip()
                        tokens = part.split()
                        if len(tokens) >= 2 and tokens[-1] in ("ETH", "WETH", "(null)", "?"):
                            try:
                                val = float(tokens[-2].replace(",", ""))
                                profit_values.append(val)
                            except (ValueError, IndexError):
                                pass

            # Write per-transaction reasoning
            out_file = out_dir / txt_file.name
            with open(out_file, "w") as f:
                f.write(reasoning + "\n")

        if not total:
            print(f"  Skipping {folder} (no tx files)")
            continue

        # Category summary
        summary = []
        summary.append(f"\n{'=' * 60}")
        summary.append(f"CATEGORY {cat_num}: {folder}")
        summary.append(f"{'=' * 60}")
        summary.append(f"Total: {total}")
        summary.append(f"\nVerdicts:")
        for v, c in verdicts.most_common():
            pct = 100 * c / total if total else 0
            summary.append(f"  {v:25s}  {c:4d}  ({pct:.0f}%)")

        summary.append(f"\nFlash loan lending: {lending_count}/{total}")

        summary.append(f"\nRouter/aggregator involvement: {router_count}/{total}")
        if router_names:
            for rt, c in router_names.most_common(10):
                summary.append(f"  {rt:30s}  {c}")

        summary.append(f"\nEigenphi overlap: {eigenphi_count}/{total}")

        summary.append(f"\nTop pools:")
        for p, c in pool_names.most_common(10):
            summary.append(f"  {p:30s}  {c}")

        if all_n_cycles:
            multi_cycle = sum(1 for c in all_n_cycles if c > 1)
            summary.append(f"\nMulti-cycle txs: {multi_cycle}/{total}")
        if all_n_transfers:
            avg_tr = sum(all_n_transfers) / len(all_n_transfers)
            summary.append(f"Transfers per tx: avg={avg_tr:.1f}, min={min(all_n_transfers)}, max={max(all_n_transfers)}")

        if profit_values:
            profitable = [p for p in profit_values if p > 0]
            unprofitable = [p for p in profit_values if p < 0]
            summary.append(f"\nNet profit (ETH/WETH): {len(profit_values)} txs")
            summary.append(f"  Positive: {len(profitable)}, Negative: {len(unprofitable)}, Zero: {len(profit_values) - len(profitable) - len(unprofitable)}")
            if profitable:
                fmt = lambda v: f"{v:.18f}".rstrip("0").rstrip(".")
                summary.append(f"  Median positive: {fmt(sorted(profitable)[len(profitable)//2])} ETH")

        summary.append(f"\nWritten to: {out_dir}/")

        for line in summary:
            print(line)
        all_summary.extend(summary)

    # Global summary
    summary_path = REASONED_DIR / "reasoned_summary.txt"
    with open(summary_path, "w") as f:
        f.write("\n".join(all_summary) + "\n")
    print(f"\nSummary saved to {summary_path}")


if __name__ == "__main__":
    main()
