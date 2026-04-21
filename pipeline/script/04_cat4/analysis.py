"""
15_cat4_analysis.py — Analyze cat4 forensic results.

Reads: data/cat4_forensic/summary.csv + individual arbitrage.json
Writes: summaries/15_cat4_analysis_summary.txt

Applies the decision tree from METHODOLOGY.md:
  Q1: hasArbitrage? → Ours now detects it (was a bug fix)
  Q2: Closed loops exist?
  Q3: Any with τ_in = τ_out?
  Q4: Multi-hop token round trip?
  Q5: Classify cause (Eigenphi FP, decoder gap, algorithm edge case)
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import json
import sys
from pathlib import Path
from collections import Counter

csv.field_size_limit(sys.maxsize)

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
FORENSIC_DIR = EVAL_DIR / "output" / "cat4_forensic"
SUMMARIES_DIR = EVAL_DIR / "output" / "summaries"
SUMMARIES_DIR.mkdir(parents=True, exist_ok=True)

OUT = SUMMARIES_DIR / "15_cat4_analysis_summary.txt"


def p(msg=""):
    print(msg)
    with open(OUT, "a") as f:
        f.write(msg + "\n")


def classify_cat4(tx_hash, summary_row):
    """Apply the decision tree to a cat4 transaction."""
    has_arb = summary_row["has_arbitrage"] == "True"
    verdict = summary_row["verdict"]
    reasons = summary_row["reasons"].split("|") if summary_row["reasons"] else []
    num_cycles = int(summary_row["num_cycles"]) if summary_row["num_cycles"] else 0
    num_leftovers = int(summary_row["num_leftovers"]) if summary_row["num_leftovers"] else 0
    status = summary_row["status"]

    if status != "ok":
        return "exec_error", f"debug_graph failed: {status}"

    # Q1: Does Ours now detect it?
    if has_arb and verdict in ("arbitrage", "warning"):
        if verdict == "arbitrage":
            return "now_detected_confirmed", f"Bug fix: now confirmed arbitrage ({num_cycles} cycles)"
        else:
            return "now_detected_warning", f"Bug fix: now warning ({num_cycles} cycles, {num_leftovers} leftovers, {','.join(reasons)})"

    # Q2-Q3: Any cycles at all?
    if num_cycles > 0:
        return "has_cycles_not_arb", f"Cycles found but not arbitrage ({','.join(reasons)})"

    # No cycles — either decoder gap or Eigenphi FP
    if "noArbitrageCycles" in reasons:
        if "balanceNegative" in reasons or "finalBalanceNegative" in reasons:
            return "eigenphi_fp_negative", f"No cycles, negative balance — likely Eigenphi FP"
        elif "balancePositive" in reasons:
            return "decoder_or_algorithm", f"No cycles but positive balance — decoder gap or algorithm miss"
        else:
            return "eigenphi_fp_other", f"No cycles ({','.join(reasons)})"

    return "unknown", f"Unclassified ({verdict}, {','.join(reasons)})"


def main():
    # Clear output
    open(OUT, "w").close()

    summary_path = FORENSIC_DIR / "summary.csv"
    if not summary_path.exists():
        p("ERROR: Run run_cat4_forensic.sh first.")
        return

    p("=" * 70)
    p("CAT4 FORENSIC ANALYSIS")
    p("=" * 70)

    # Read summary
    rows = []
    with open(summary_path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(row)

    p(f"Total transactions: {len(rows)}")
    p()

    # Classify each
    classifications = Counter()
    details = {}
    for row in rows:
        tx = row["tx_hash"]
        cat, reason = classify_cat4(tx, row)
        classifications[cat] += 1
        details[tx] = (cat, reason)

    # Report
    p("Classification breakdown:")
    p("-" * 50)
    for cat, count in classifications.most_common():
        pct = count / len(rows) * 100
        p(f"  {cat:30s}: {count:4d} ({pct:5.1f}%)")

    p()
    p("=" * 70)
    p("INTERPRETATION")
    p("=" * 70)

    now_detected = classifications.get("now_detected_confirmed", 0) + \
                   classifications.get("now_detected_warning", 0)
    eigenphi_fp = classifications.get("eigenphi_fp_negative", 0) + \
                  classifications.get("eigenphi_fp_other", 0)
    decoder = classifications.get("decoder_or_algorithm", 0)
    has_cycles = classifications.get("has_cycles_not_arb", 0)
    errors = classifications.get("exec_error", 0)

    p(f"  Now detected (bug fix):     {now_detected:4d} ({now_detected/len(rows)*100:.1f}%)")
    p(f"  Eigenphi false positives:    {eigenphi_fp:4d} ({eigenphi_fp/len(rows)*100:.1f}%)")
    p(f"  Decoder/algorithm gaps:      {decoder:4d} ({decoder/len(rows)*100:.1f}%)")
    p(f"  Has cycles but not arb:      {has_cycles:4d} ({has_cycles/len(rows)*100:.1f}%)")
    p(f"  Execution errors:            {errors:4d} ({errors/len(rows)*100:.1f}%)")

    p()
    p("=" * 70)
    p("SAMPLE TRANSACTIONS BY CATEGORY")
    p("=" * 70)
    for cat in ["now_detected_confirmed", "now_detected_warning",
                "eigenphi_fp_negative", "decoder_or_algorithm",
                "has_cycles_not_arb"]:
        txs = [tx for tx, (c, _) in details.items() if c == cat]
        if txs:
            p(f"\n  {cat} (showing up to 5):")
            for tx in txs[:5]:
                _, reason = details[tx]
                p(f"    {tx[:20]}... — {reason}")


if __name__ == "__main__":
    main()
