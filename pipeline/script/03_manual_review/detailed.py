"""
Detailed manual review of cat1, cat2, cat5 transactions.

For each transaction:
  - Resolve addresses using resolved_addresses.csv
  - Build a human-readable flow narrative
  - Identify arbitrage type (triangular, multi-hop, lending, etc.)
  - Give a reasoned verdict
  - Flag lending involvement

Reads from:
  - data/manual_review/cat{1,2,5}_*/tx_*.txt (inspect files)
  - data/manual_review/resolved_addresses.csv
Writes to:
  - data/manual_review/detailed_review_cat{1,2,5}.csv
  - data/manual_review/detailed_review_summary.txt
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import re
from collections import Counter

from config import INSPECTIONS_DIR, ADDRESSES_DIR, VERDICTS_DIR, CATEGORY_FOLDERS, classify_pool

ETH_ADDR_RE = re.compile(r"0x[0-9a-f]{40}")


def load_address_labels():
    """Load resolved addresses into a dict."""
    labels = {}
    path = ADDRESSES_DIR / "resolved_addresses.csv"
    with open(path, "r") as f:
        reader = csv.reader(f)
        next(reader)
        for row in reader:
            addr = row[0].lower()
            name = row[1]
            is_contract = row[2] == "True"
            labels[addr] = name if name else ("contract" if is_contract else "EOA")
    return labels


def label(addr, labels_dict):
    """Return a full label for an address."""
    addr = addr.lower()
    name = labels_dict.get(addr, addr)
    if name == "unverified contract":
        return f"contract({addr})"
    if name == "EOA":
        return f"EOA({addr})"
    return name


    # classify_pool imported from config


def parse_inspect_file(filepath, addr_labels):
    """Parse an inspect file and return structured review data."""
    content = filepath.read_text()

    if "NOT IN ARGOS" in content:
        tx_match = re.search(r"TRANSACTION: (0x[0-9a-f]+)", content)
        return {
            "tx_hash": tx_match.group(1) if tx_match else "?",
            "verdict": "N/A",
            "reasons": "",
            "flow": "not in Argos dataset",
            "arb_type": "N/A",
            "involves_lending": False,
            "n_cycles": 0,
            "n_transfers": 0,
            "pools_used": [],
            "tokens_involved": [],
            "comment": "Transaction not in Argos dataset",
        }

    # Parse basic fields
    tx_hash = ""
    verdict = ""
    reasons = ""
    final_balance = []
    gross_balance = []

    lines = content.split("\n")
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("TRANSACTION:"):
            tx_hash = stripped.split(":", 1)[1].strip()
        elif stripped.startswith("Verdict:"):
            verdict = stripped.split(":", 1)[1].strip()
        elif stripped.startswith("Reasons:"):
            reasons = stripped.split(":", 1)[1].strip()
        elif stripped.startswith("FINAL BALANCE:"):
            final_balance.append(stripped.split(":", 1)[1].strip())
        elif stripped.startswith("GROSS BALANCE:"):
            gross_balance.append(stripped.split(":", 1)[1].strip())

    # Parse transfers in cycles
    transfers = []
    in_cycle_section = False
    in_leftover_section = False
    in_leftover_cycle_section = False
    current_transfer = {}

    for i, line in enumerate(lines):
        stripped = line.strip()

        if "CYCLES:" in stripped and not "LEFTOVER" in stripped:
            in_cycle_section = True
            in_leftover_section = False
            in_leftover_cycle_section = False
            continue
        elif "LEFTOVER CYCLES" in stripped:
            in_cycle_section = False
            in_leftover_cycle_section = True
            continue
        elif "LEFTOVERS (unexplained)" in stripped:
            in_cycle_section = False
            in_leftover_section = True
            in_leftover_cycle_section = False
            continue
        elif "TRANSACTION COSTS:" in stripped:
            in_cycle_section = False
            in_leftover_section = False
            in_leftover_cycle_section = False
            continue

        if not (in_cycle_section or in_leftover_cycle_section):
            continue

        # Look for address lines (contain 0x addresses)
        addrs = ETH_ADDR_RE.findall(stripped)
        if addrs and stripped.startswith("["):
            current_transfer = {"from": addrs[0], "section": "cycle"}
        elif addrs and stripped.startswith("->"):
            current_transfer["to"] = addrs[0]
        elif current_transfer.get("to") and not stripped.startswith("[") and not stripped.startswith("->") and stripped:
            # Amount line
            current_transfer["amount_line"] = stripped
            current_transfer["section"] = "leftover_cycle" if in_leftover_cycle_section else "cycle"
            transfers.append(current_transfer)
            current_transfer = {}
        elif addrs and not stripped.startswith("[") and not stripped.startswith("->"):
            # Leftover cycle format (no index)
            if "from" not in current_transfer:
                current_transfer = {"from": addrs[0], "section": "leftover_cycle"}
            elif "to" not in current_transfer:
                current_transfer["to"] = addrs[0]

    # Build flow narrative
    pools_used = []
    tokens_involved = set()
    flow_parts = []

    for t in transfers:
        fr_label = label(t.get("from", "?"), addr_labels)
        to_label = label(t.get("to", "?"), addr_labels)
        amount = t.get("amount_line", "")

        # Extract token from amount line
        parts = amount.split()
        token = parts[-1] if parts else "?"
        tokens_involved.add(token)

        # Identify pools
        fr_name = addr_labels.get(t.get("from", "").lower(), "")
        to_name = addr_labels.get(t.get("to", "").lower(), "")
        for name in [fr_name, to_name]:
            pool_type = classify_pool(name)
            if pool_type and pool_type not in pools_used:
                pools_used.append(pool_type)

        flow_parts.append(f"{fr_label} -[{amount}]-> {to_label}")

    flow = " | ".join(flow_parts) if flow_parts else "no transfers parsed"

    # Determine lending: a leftover cycle is lending only if it is a
    # 2-transfer same-token round-trip (borrow + repay with reversed endpoints).
    # Other leftover cycles are just orphan transfer groupings.
    leftover_cycle_transfers = [t for t in transfers if t.get("section") == "leftover_cycle"]
    has_lending = False
    # Group leftover transfers into pairs (they come in order from the inspect file)
    i = 0
    while i + 1 < len(leftover_cycle_transfers):
        t1 = leftover_cycle_transfers[i]
        t2 = leftover_cycle_transfers[i + 1]
        # Same token (last word of amount_line)
        tok1 = t1.get("amount_line", "").split()[-1] if t1.get("amount_line") else ""
        tok2 = t2.get("amount_line", "").split()[-1] if t2.get("amount_line") else ""
        # Reversed endpoints
        if (tok1 and tok1 == tok2
                and t1.get("from", "").lower() == t2.get("to", "").lower()
                and t1.get("to", "").lower() == t2.get("from", "").lower()):
            has_lending = True
            break
        i += 2
    n_cycles_match = re.search(r"CYCLES: (\d+)", content)
    n_cycles = int(n_cycles_match.group(1)) if n_cycles_match else 0

    if n_cycles == 0:
        arb_type = "no cycles"
    elif n_cycles == 1 and len(transfers) <= 4:
        arb_type = "simple triangular"
    elif n_cycles == 1 and len(transfers) <= 8:
        arb_type = "multi-hop"
    elif n_cycles == 1:
        arb_type = "complex single-cycle"
    elif n_cycles >= 2:
        arb_type = f"multi-cycle ({n_cycles})"

    if has_lending:
        arb_type += " + lending"

    # Build comment
    if verdict == "arbitrage":
        if has_lending:
            comment = f"Real arbitrage with lending component. Routes through {', '.join(pools_used) or 'unidentified pools'} involving {len(tokens_involved)} tokens."
        elif len(pools_used) > 0:
            comment = f"Real arbitrage routing through {', '.join(pools_used)} involving {len(tokens_involved)} tokens. Profit: {'; '.join(final_balance) or '?'}."
        else:
            comment = f"Real arbitrage with {len(transfers)} transfers involving {len(tokens_involved)} tokens."
    elif verdict == "warning":
        if "negativeProfit" in reasons or "finalBalanceNegative" in reasons:
            comment = f"Attempted arbitrage (unprofitable). Cycles exist through {', '.join(pools_used) or 'pools'} but gas costs exceed profit."
        elif "leftoverTransaction" in reasons:
            comment = f"Probable arbitrage with incomplete chain. Cycles found but some transfers unexplained."
        elif "Mixed" in reasons:
            comment = f"Uncertain: multi-token balance with opposing signs. Routes through {', '.join(pools_used) or 'pools'}."
        else:
            comment = f"Warning verdict: {reasons}."
    else:
        comment = f"Verdict: {verdict}"

    return {
        "tx_hash": tx_hash,
        "verdict": verdict,
        "reasons": reasons,
        "flow": flow,
        "arb_type": arb_type,
        "involves_lending": has_lending,
        "n_cycles": n_cycles,
        "n_transfers": len(transfers),
        "pools_used": pools_used,
        "tokens_involved": list(tokens_involved),
        "comment": comment,
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

        reviews = []
        for txt_file in sorted(folder_path.glob("tx_*.txt")):
            review = parse_inspect_file(txt_file, addr_labels)
            reviews.append(review)

        # Write detailed CSV
        out_dir = VERDICTS_DIR / "11_detailed_review"
        out_dir.mkdir(parents=True, exist_ok=True)
        out_path = out_dir / f"detailed_review_cat{cat_num}.csv"
        with open(out_path, "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow([
                "tx_hash", "verdict", "reasons", "arb_type",
                "n_cycles", "n_transfers", "involves_lending",
                "pools_used", "tokens", "comment",
            ])
            for r in reviews:
                writer.writerow([
                    r["tx_hash"], r["verdict"], r["reasons"],
                    r["arb_type"], r["n_cycles"], r["n_transfers"],
                    r["involves_lending"],
                    "|".join(r["pools_used"]),
                    "|".join(r["tokens_involved"][:5]),
                    r["comment"],
                ])

        # Aggregate stats
        verdict_counts = Counter(r["verdict"] for r in reviews)
        type_counts = Counter(r["arb_type"] for r in reviews)
        lending_count = sum(1 for r in reviews if r["involves_lending"])
        pool_counts = Counter()
        for r in reviews:
            for p in r["pools_used"]:
                pool_counts[p] += 1

        summary = []
        summary.append(f"\n{'=' * 60}")
        summary.append(f"CATEGORY {cat_num}: {folder}")
        summary.append(f"{'=' * 60}")
        summary.append(f"Total transactions: {len(reviews)}")
        summary.append(f"\nVerdicts:")
        for v, c in verdict_counts.most_common():
            summary.append(f"  {v:20s}  {c}")
        summary.append(f"\nArbitrage types:")
        for t, c in type_counts.most_common():
            summary.append(f"  {t:30s}  {c}")
        summary.append(f"\nLending involvement: {lending_count}/{len(reviews)}")
        summary.append(f"\nPools used:")
        for p, c in pool_counts.most_common():
            summary.append(f"  {p:20s}  {c}")
        summary.append(f"\nSaved to {out_path}")

        for line in summary:
            print(line)
        all_summaries.extend(summary)

    # Save summary
    summary_path = VERDICTS_DIR / "11_detailed_review" / "detailed_review_summary.txt"
    with open(summary_path, "w") as f:
        f.write("\n".join(all_summaries) + "\n")
    print(f"\nSummary saved to {summary_path}")


if __name__ == "__main__":
    main()
