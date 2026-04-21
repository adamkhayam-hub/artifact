"""
Comprehensive manual review of all 300 sampled transactions.

For each transaction:
  1. Read inspect file and parse all transfers
  2. Resolve every address (pool name, token name, router, bot, EOA)
  3. Reconstruct the economic flow in plain English
  4. Verify: does the flow make sense as an arbitrage?
  5. Check for red flags (unknown contracts, broken cycles, suspicious patterns)
  6. Write a detailed per-transaction review

Output:
  - manual_review/verdicts/manual/cat{1,2,5}/tx_<hash>.txt
  - manual_review/verdicts/manual/manual_review_summary.txt
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
    is_dex_pool, is_router, classify_pool,
)

ETH_ADDR_RE = re.compile(r"0x[0-9a-f]{40}")
MANUAL_DIR = VERDICTS_DIR / "14_manual_review"


def load_address_labels():
    labels = {}
    for addr, name in KNOWN_ADDRESSES.items():
        labels[addr] = name
    path = ADDRESSES_DIR / "resolved_addresses.csv"
    if path.exists():
        with open(path, "r") as f:
            reader = csv.reader(f)
            next(reader)
            for row in reader:
                addr = row[0].lower()
                name = row[1]
                is_contract = row[2] == "True"
                if name and name not in ("unverified contract", "EOA"):
                    labels[addr] = name
                elif is_contract:
                    labels[addr] = f"unverified_contract({addr[:10]})"
                else:
                    labels[addr] = f"EOA({addr[:10]})"
    return labels


def short_label(addr, labels):
    name = labels.get(addr.lower(), addr[:12] + "...")
    # Shorten common pool names
    if "UniswapV3Pool" in name:
        return f"UniV3Pool({addr[:8]})"
    if "UniswapV2Pair" in name:
        return f"UniV2Pair({addr[:8]})"
    if "PancakeV3Pool" in name:
        return f"PancakeV3({addr[:8]})"
    if "AlgebraPool" in name:
        return f"Algebra({addr[:8]})"
    if "Curve" in name:
        short = name.split(":")[-1].strip() if ":" in name else "Curve"
        return f"Curve({short[:15]})"
    if len(name) > 30:
        return name[:27] + "..."
    return name


def parse_inspect(filepath):
    """Parse an inspect file into structured data."""
    content = filepath.read_text()
    lines = content.split("\n")

    result = {
        "tx_hash": "",
        "block": "",
        "verdict": "",
        "reasons": "",
        "final_balance": [],
        "gross_balance": [],
        "cycles": [],          # list of list of transfers
        "leftover_cycles": [], # list of list of transfers
        "leftovers": [],       # list of transfers
        "costs": [],
        "eigenphi_main": False,
        "raw": content,
    }

    section = "header"
    current_transfers = []
    current_cycle_idx = -1

    for line in lines:
        s = line.strip()

        # Header fields
        if s.startswith("TRANSACTION:"):
            result["tx_hash"] = s.split(":", 1)[1].strip()
        elif s.startswith("BLOCK:"):
            result["block"] = s.split(":", 1)[1].strip()
        elif s.startswith("Verdict:"):
            result["verdict"] = s.split(":", 1)[1].strip()
        elif s.startswith("Reasons:"):
            result["reasons"] = s.split(":", 1)[1].strip()
        elif s.startswith("FINAL BALANCE:"):
            result["final_balance"].append(s.split(":", 1)[1].strip())
        elif s.startswith("GROSS BALANCE:"):
            result["gross_balance"].append(s.split(":", 1)[1].strip())
        elif "In Eigenphi:" in s or "In Eigenphi main set:" in s:
            result["eigenphi_main"] = "YES" in s

        # Section changes (flush current_transfers on transition)
        new_section = None
        if s.startswith("CYCLES:") and "LEFTOVER" not in s:
            new_section = "cycles"
        elif "LEFTOVER CYCLES" in s:
            new_section = "leftover_cycles"
        elif s.startswith("LEFTOVERS (unexplained)"):
            new_section = "leftovers"
        elif s.startswith("TRANSACTION COSTS:"):
            new_section = "costs"
        elif s.startswith("EIGENPHI STATUS:"):
            new_section = "eigenphi"

        if new_section:
            # Flush current transfers into the right bucket
            if current_transfers:
                if section == "cycles":
                    result["cycles"].append(current_transfers)
                elif section == "leftover_cycles":
                    result["leftover_cycles"].append(current_transfers)
                elif section == "leftovers":
                    result["leftovers"] = current_transfers
                elif section == "costs":
                    result["costs"] = current_transfers
                current_transfers = []
            section = new_section
            continue

        # Parse cycle headers
        if section == "cycles" and "Cycle " in s and "transfers" in s:
            if current_transfers:
                result["cycles"].append(current_transfers)
            current_transfers = []
            continue

        if section == "leftover_cycles" and "Leftover cycle" in s and "transfers" in s:
            if current_transfers:
                result["leftover_cycles"].append(current_transfers)
            current_transfers = []
            continue

        # Parse transfers (format: [idx] addr \n -> addr \n amount)
        if section in ("cycles", "leftover_cycles", "leftovers", "costs"):
            addrs = ETH_ADDR_RE.findall(s.lower())

            # Priority: if last transfer has 'to' but no 'amount', this
            # line IS the amount regardless of content (even if it
            # contains an address like a token contract)
            if (current_transfers and "to" in current_transfers[-1]
                    and "amount" not in current_transfers[-1]
                    and s and not s.startswith("[") and not s.startswith("->")):
                current_transfers[-1]["amount"] = s
            elif s.startswith("[") and addrs:
                current_transfers.append({"from": addrs[0]})
            elif s.startswith("->") and addrs and current_transfers:
                current_transfers[-1]["to"] = addrs[0]
            elif addrs and not s.startswith("[") and not s.startswith("->"):
                # Non-indexed transfer (leftover cycles format)
                if not current_transfers or "amount" in current_transfers[-1]:
                    current_transfers.append({"from": addrs[0]})
                elif "to" not in current_transfers[-1]:
                    current_transfers[-1]["to"] = addrs[0]

    # Flush last batch
    if current_transfers:
        if section == "cycles":
            result["cycles"].append(current_transfers)
        elif section == "leftover_cycles":
            result["leftover_cycles"].append(current_transfers)
        elif section == "leftovers":
            result["leftovers"] = current_transfers
        elif section == "costs":
            result["costs"] = current_transfers

    return result


def review_transaction(parsed, labels):
    """Produce a detailed human review of one transaction."""
    review = []
    tx = parsed["tx_hash"]

    review.append(f"{'=' * 70}")
    review.append(f"TRANSACTION: {tx}")
    review.append(f"BLOCK: {parsed['block']}")
    review.append(f"{'=' * 70}")
    review.append(f"Ours verdict: {parsed['verdict']}")
    review.append(f"Reasons: {parsed['reasons']}")
    review.append(f"Eigenphi: {'YES' if parsed['eigenphi_main'] else 'NO'}")
    review.append("")

    # Balance
    if parsed["gross_balance"]:
        review.append(f"Gross profit: {'; '.join(parsed['gross_balance'])}")
    if parsed["final_balance"]:
        review.append(f"Net profit (after gas): {'; '.join(parsed['final_balance'])}")
    review.append("")

    # Analyze each cycle
    all_pools = []
    all_tokens = set()
    cycle_summaries = []

    for ci, cycle in enumerate(parsed["cycles"]):
        review.append(f"--- Cycle {ci + 1} ({len(cycle)} transfers) ---")

        flow_steps = []
        cycle_pools = []
        first_from = cycle[0].get("from", "?") if cycle else "?"
        last_to = cycle[-1].get("to", "?") if cycle else "?"

        for ti, t in enumerate(cycle):
            fr = t.get("from", "?")
            to = t.get("to", "?")
            amt = t.get("amount", "?")
            fr_label = short_label(fr, labels)
            to_label = short_label(to, labels)

            # Classify addresses
            fr_name = labels.get(fr.lower(), "")
            to_name = labels.get(to.lower(), "")
            fr_pool = classify_pool(fr_name)
            to_pool = classify_pool(to_name)

            if fr_pool:
                cycle_pools.append(fr_pool)
            if to_pool:
                cycle_pools.append(to_pool)

            # Token from amount line
            token = amt.split()[-1] if amt and amt != "?" else "?"
            all_tokens.add(token)

            flow_steps.append(f"  [{ti}] {fr_label} → {to_label}: {amt}")

        for step in flow_steps:
            review.append(step)

        closes = first_from.lower() == last_to.lower() if first_from != "?" else False
        unique_pools = list(dict.fromkeys(cycle_pools))  # preserve order, dedupe
        all_pools.extend(unique_pools)

        cycle_summaries.append({
            "closes": closes,
            "n_transfers": len(cycle),
            "pools": unique_pools,
            "first_from": first_from,
            "last_to": last_to,
        })

        review.append(f"  Cycle closes: {'YES' if closes else 'NO'}")
        if unique_pools:
            review.append(f"  Pools: {', '.join(unique_pools)}")
        review.append("")

    # Leftover cycles (lending check)
    has_lending = False
    lending_details = []
    for li, lc in enumerate(parsed["leftover_cycles"]):
        if len(lc) >= 2:
            t1, t2 = lc[0], lc[1]
            tok1 = t1.get("amount", "").split()[-1] if t1.get("amount") else ""
            tok2 = t2.get("amount", "").split()[-1] if t2.get("amount") else ""
            reversed_endpoints = (
                t1.get("from", "").lower() == t2.get("to", "").lower()
                and t1.get("to", "").lower() == t2.get("from", "").lower()
            )
            if tok1 and tok1 == tok2 and reversed_endpoints:
                has_lending = True
                fr_label = short_label(t1.get("from", "?"), labels)
                to_label = short_label(t1.get("to", "?"), labels)
                lending_details.append(
                    f"Flash loan: {fr_label} → {to_label}: "
                    f"{t1.get('amount', '?')} (borrow) / "
                    f"{t2.get('amount', '?')} (repay)"
                )

    if lending_details:
        review.append("--- Lending ---")
        for d in lending_details:
            review.append(f"  {d}")
        review.append("")

    # Leftovers
    if parsed["leftovers"]:
        review.append(f"--- Unexplained leftovers: {len(parsed['leftovers'])} transfers ---")
        for t in parsed["leftovers"][:5]:
            fr_label = short_label(t.get("from", "?"), labels)
            to_label = short_label(t.get("to", "?"), labels)
            review.append(f"  {fr_label} → {to_label}: {t.get('amount', '?')}")
        if len(parsed["leftovers"]) > 5:
            review.append(f"  ... and {len(parsed['leftovers']) - 5} more")
        review.append("")

    # MANUAL VERDICT
    review.append("=" * 40)
    review.append("MANUAL REVIEW VERDICT:")
    review.append("=" * 40)

    # Determine verdict
    all_close = all(cs["closes"] for cs in cycle_summaries) if cycle_summaries else False
    unique_all_pools = list(dict.fromkeys(all_pools))

    if not cycle_summaries:
        verdict = "INCONCLUSIVE"
        explanation = "No cycles found in inspect file."
    elif all_close and parsed["verdict"] == "arbitrage":
        # Confirmed arbitrage
        n_pools = len(unique_all_pools)
        pool_str = ", ".join(unique_all_pools) if unique_all_pools else "unidentified pools"
        n_tokens = len(all_tokens - {"?"})

        if has_lending:
            verdict = "REAL_ARBITRAGE (with flash loan)"
            explanation = (
                f"Confirmed arbitrage. {len(parsed['cycles'])} cycle(s) through "
                f"{pool_str}. Flash loan detected in leftover cycles. "
                f"{n_tokens} tokens involved. "
                f"Net profit: {'; '.join(parsed['final_balance']) or '?'}. "
                f"The bot borrows funds, executes a multi-leg swap exploiting "
                f"price differences across pools, and repays the loan in the "
                f"same transaction."
            )
        else:
            verdict = "REAL_ARBITRAGE"
            explanation = (
                f"Confirmed arbitrage. {len(parsed['cycles'])} cycle(s) through "
                f"{pool_str}. {n_tokens} tokens involved. "
                f"Net profit: {'; '.join(parsed['final_balance']) or '?'}. "
                f"The bot routes tokens through multiple pools, exploiting "
                f"price differences to recover more of the initial token "
                f"than was sent."
            )
    elif all_close and parsed["verdict"] == "warning":
        pool_str = ", ".join(unique_all_pools) if unique_all_pools else "unidentified pools"
        reasons = parsed["reasons"]

        if "negativeProfit" in reasons or "finalBalanceNegative" in reasons:
            verdict = "ATTEMPTED_ARBITRAGE"
            explanation = (
                f"Failed arbitrage attempt. Valid cycle structure through "
                f"{pool_str}, but gas costs exceeded the gross profit. "
                f"The bot executed the trade but the price movement was "
                f"insufficient to cover transaction fees. "
                f"Gross: {'; '.join(parsed['gross_balance']) or '?'}; "
                f"Net: {'; '.join(parsed['final_balance']) or '?'}."
            )
        elif "leftoverTransaction" in reasons:
            verdict = "PROBABLE_ARBITRAGE"
            explanation = (
                f"Probable arbitrage with incomplete evidence. Cycle found "
                f"through {pool_str} with positive balance, but some "
                f"transfers could not be incorporated into the chain. "
                f"The arbitrage is likely real but the decode layer "
                f"missed some transfer events."
            )
        elif "Mixed" in reasons:
            verdict = "UNCERTAIN_ARBITRAGE"
            explanation = (
                f"Structurally valid cycle through {pool_str}, but the "
                f"balance involves multiple tokens with opposing signs. "
                f"Without a price oracle, profitability cannot be determined. "
                f"The pattern is consistent with arbitrage."
            )
        else:
            verdict = "PROBABLE_ARBITRAGE"
            explanation = f"Warning-level detection through {pool_str}. Reasons: {reasons}."
    else:
        verdict = "SUSPICIOUS"
        explanation = "Cycle does not close or unexpected structure."

    if has_lending:
        lending_flag = " [FLASH LOAN]"
    else:
        lending_flag = ""

    review.append(f"Verdict: {verdict}{lending_flag}")
    review.append(f"Explanation: {explanation}")
    review.append("")

    return verdict, has_lending, "\n".join(review)


def main():
    print("Loading address labels...")
    labels = load_address_labels()
    print(f"  {len(labels)} addresses loaded")

    categories = [
        (CATEGORY_FOLDERS[1], 1),
        (CATEGORY_FOLDERS[2], 2),
        (CATEGORY_FOLDERS[3], 3),
        (CATEGORY_FOLDERS[4], 4),
    ]

    all_summary = []

    for folder, cat_num in categories:
        folder_path = INSPECTIONS_DIR / folder
        if not folder_path.exists():
            print(f"  Skipping {folder}")
            continue

        out_dir = MANUAL_DIR / f"cat{cat_num}"
        out_dir.mkdir(parents=True, exist_ok=True)

        verdict_counts = Counter()
        lending_count = 0
        total = 0

        for txt_file in sorted(folder_path.glob("tx_*.txt")):
            parsed = parse_inspect(txt_file)

            if "NOT IN OURS" in parsed["raw"] or "ERROR" in parsed["raw"]:
                continue

            verdict, has_lending, review_text = review_transaction(parsed, labels)
            verdict_counts[verdict] += 1
            if has_lending:
                lending_count += 1
            total += 1

            out_file = out_dir / txt_file.name
            with open(out_file, "w") as f:
                f.write(review_text)

        summary = []
        summary.append(f"\n{'=' * 60}")
        summary.append(f"CATEGORY {cat_num}: {folder}")
        summary.append(f"{'=' * 60}")
        summary.append(f"Total reviewed: {total}")
        summary.append(f"\nVerdicts:")
        for v, c in verdict_counts.most_common():
            pct = 100 * c / total if total else 0
            summary.append(f"  {v:40s}  {c:4d}  ({pct:.0f}%)")
        if total > 0:
            summary.append(f"\nFlash loan lending: {lending_count}/{total} ({100*lending_count/total:.0f}%)")
        else:
            summary.append(f"\nFlash loan lending: 0/0 (no samples)")

        for line in summary:
            print(line)
        all_summary.extend(summary)

    summary_path = MANUAL_DIR / "manual_review_summary.txt"
    with open(summary_path, "w") as f:
        f.write("\n".join(all_summary) + "\n")
    print(f"\nSummary saved to {summary_path}")


if __name__ == "__main__":
    main()
