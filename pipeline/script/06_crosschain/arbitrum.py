"""
19_arbitrum_summary.py — Summarize Arbitrum cross-chain validation results.

Reads:  data/arbitrum_1k/summary.csv
Writes: summaries/06_crosschain/arbitrum.txt
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import sys
from collections import Counter
from pathlib import Path

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
DATA_DIR = EVAL_DIR / "data" / "arbitrum_1k"
SUMMARIES_DIR = EVAL_DIR / "output" / "summaries"
SUMMARIES_DIR.mkdir(parents=True, exist_ok=True)

SUMMARY_CSV = DATA_DIR / "summary.csv"
OUT = SUMMARIES_DIR / "06_crosschain/arbitrum.txt"


def p(msg="", f=None):
    print(msg)
    if f:
        f.write(msg + "\n")


def main():
    if not SUMMARY_CSV.exists():
        print(f"ERROR: {SUMMARY_CSV} not found.")
        print("Run run_arbitrum_1k.sh first.")
        sys.exit(1)

    rows = []
    with open(SUMMARY_CSV) as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(row)

    verdicts = Counter(r["verdict"] for r in rows)
    blocks = set(r["block"] for r in rows)

    with open(OUT, "w") as out:
        p("=" * 60, out)
        p("ARBITRUM CROSS-CHAIN VALIDATION", out)
        p("=" * 60, out)
        p(f"Blocks: {len(blocks)}", out)
        p(f"Transactions: {len(rows)}", out)
        p("", out)

        p("Verdicts:", out)
        total = len(rows)
        for v in ["arbitrage", "warning", "none", "error"]:
            count = verdicts.get(v, 0)
            pct = count / total * 100 if total > 0 else 0
            p(f"  {v:12s}  {count:>6d}  ({pct:.1f}%)", out)

        flagged = verdicts.get("arbitrage", 0) + verdicts.get("warning", 0)
        p("", out)
        p(f"Flagged (arb + warn): {flagged} ({flagged/total*100:.1f}%)", out)

        # Cycle stats for flagged txs
        arb_rows = [r for r in rows if r["verdict"] == "arbitrage"]
        warn_rows = [r for r in rows if r["verdict"] == "warning"]

        if arb_rows:
            cycles = [int(r.get("num_cycles", 0)) for r in arb_rows]
            p("", out)
            p(f"Confirmed arbitrages: {len(arb_rows)}", out)
            p(f"  Avg cycles: {sum(cycles)/len(cycles):.1f}", out)
            p(f"  Max cycles: {max(cycles)}", out)

        if warn_rows:
            cycles = [int(r.get("num_cycles", 0)) for r in warn_rows]
            leftovers = [int(r.get("num_leftovers", 0)) for r in warn_rows]
            p("", out)
            p(f"Warnings: {len(warn_rows)}", out)
            p(f"  Avg cycles: {sum(cycles)/len(cycles):.1f}", out)
            p(f"  Avg leftovers: {sum(leftovers)/len(leftovers):.1f}", out)

        # Reason breakdown for warnings
        reason_counts = Counter()
        for r in warn_rows:
            reasons = r.get("reasons", "").split("|")
            for reason in reasons:
                if reason:
                    reason_counts[reason] += 1

        if reason_counts:
            p("", out)
            p("Warning reasons:", out)
            for reason, count in reason_counts.most_common():
                p(f"  {reason:30s}  {count:>5d}", out)

    print(f"Summary written to {OUT}")


if __name__ == "__main__":
    main()
