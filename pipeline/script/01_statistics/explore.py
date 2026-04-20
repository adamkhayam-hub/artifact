"""
Explore the three evaluation datasets and print summary statistics.

Outputs: summaries/01_statistics/explore.txt

Reads from: data/system_compact.csv (run 00_preprocess.py first),
            data/eigenphi_arbis_txs_filtered.csv
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
from collections import Counter

from config import (
    DATA_DIR, SUMMARIES_DIR, EIGENPHI_FILTERED,
    normalize_hash, classify_by_reasons,
    load_compact,
)


def read_block_range(filepath, has_header=False, block_col=1):
    blocks = []
    with open(filepath, "r") as f:
        reader = csv.reader(f)
        if has_header:
            next(reader)
        for row in reader:
            blocks.append(int(row[block_col]))
    return min(blocks), max(blocks), len(blocks)


def main():
    out = []

    def p(s=""):
        out.append(s)
        print(s)

    p("=" * 60)
    p("BLOCK RANGES")
    p("=" * 60)

    rows = load_compact()

    all_blocks = [r["block"] for r in rows]
    system_min = min(all_blocks)
    system_max = max(all_blocks)
    system_count = len(rows)
    p(f"Argos:            {system_min:>10,} - {system_max:>10,}  ({system_count:,} txs)")

    eig_min, eig_max, eig_count = read_block_range(
        EIGENPHI_FILTERED, block_col=0
    )
    p(f"Eigenphi:         {eig_min:>10,} - {eig_max:>10,}  ({eig_count:,} txs)")

    overlap_min = max(system_min, eig_min)
    overlap_max = min(system_max, eig_max)
    p(f"\nOverlap range:    {overlap_min:>10,} - {overlap_max:>10,}")
    p(f"Argos blocks beyond Eigenphi: {system_max - eig_max}")

    # Eigenphi CSVs: col 0 = block_number, col 1 = tx_hash
    eig_in_range = 0
    eig_hashes_in_range = set()
    with open(EIGENPHI_FILTERED, "r") as f:
        reader = csv.reader(f)
        for row in reader:
            if int(row[0]) <= overlap_max:
                eig_in_range += 1
                eig_hashes_in_range.add(normalize_hash(row[1]))
    p(f"Eigenphi txs in overlap: {eig_in_range:,}")

    p("\n" + "=" * 60)
    p("ARGOS VERDICT DISTRIBUTION (normalized)")
    p("=" * 60)

    verdicts = Counter()
    reason_combos = Counter()
    has_cycles = Counter()
    has_leftovers = Counter()
    has_leftover_cycles = Counter()
    n_cycles_dist = Counter()
    total = len(rows)
    system_hash_verdict = {}

    for r in rows:
        h = r["tx_hash"]
        verdict = r["verdict"]
        reasons = r["reasons"]

        verdicts[verdict] += 1
        reason_combos[reasons] += 1
        system_hash_verdict[h] = (verdict, reasons)

        n_cycles_dist[r["num_cycles"]] += 1
        if r["num_cycles"] > 0:
            has_cycles[verdict] += 1
        if r["num_leftovers"] > 0:
            has_leftovers[verdict] += 1
            # num_leftovers tracks the "leftovers" field; used here as proxy
            # for transfersInLeftoversCycles (lending-related structures)
            has_leftover_cycles[verdict] += 1

    p(f"Total Argos results: {total:,}")
    p()

    for verdict, count in verdicts.most_common():
        pct = 100 * count / total
        p(f"  {str(verdict):12s}  {count:>10,}  ({pct:.1f}%)")

    p(f"\nWith cycles:")
    for verdict, count in has_cycles.most_common():
        p(f"  {str(verdict):12s}  {count:>10,}")

    p(f"\nWith leftovers:")
    for verdict, count in has_leftovers.most_common():
        p(f"  {str(verdict):12s}  {count:>10,}")

    p(f"\nWith leftover cycles (lending) [proxy: num_leftovers > 0]:")
    for verdict, count in has_leftover_cycles.most_common():
        p(f"  {str(verdict):12s}  {count:>10,}")

    # Fixpoint detection statistics
    p("\n" + "=" * 60)
    p("FIXPOINT DETECTION")
    p("=" * 60)
    fp_by_verdict = {}
    for r in rows:
        v = r["verdict"]
        fp = r.get("fixpoint_detected")
        if fp is None:
            continue
        if v not in fp_by_verdict:
            fp_by_verdict[v] = {"fixpoint": 0, "promoted": 0}
        if fp:
            fp_by_verdict[v]["fixpoint"] += 1
        else:
            fp_by_verdict[v]["promoted"] += 1

    total_fp = sum(d["fixpoint"] for d in fp_by_verdict.values())
    total_pr = sum(d["promoted"] for d in fp_by_verdict.values())
    total_det = total_fp + total_pr
    if total_det > 0:
        p(f"Total detected: {total_det:,}")
        p(f"  Fixpoint alone: {total_fp:>10,}  ({100*total_fp/total_det:.1f}%)")
        p(f"  Promoted:       {total_pr:>10,}  ({100*total_pr/total_det:.1f}%)")
        p()
        for v in ["arbitrage", "warning"]:
            if v in fp_by_verdict:
                d = fp_by_verdict[v]
                vt = d["fixpoint"] + d["promoted"]
                p(f"  {v:12s}  fixpoint={d['fixpoint']:>10,}  "
                  f"promoted={d['promoted']:>8,}  "
                  f"({100*d['promoted']/vt:.1f}% promoted)")
    else:
        p("  (fixpointDetected field not available)")

    p(f"\nTop 25 reason combinations:")
    for reasons, count in reason_combos.most_common(25):
        pct = 100 * count / total
        p(f"  {count:>10,}  ({pct:5.1f}%)  {reasons}")

    # Reason-based classification
    p("\n" + "=" * 60)
    p("REASON-BASED CLASSIFICATION")
    p("=" * 60)
    categories = Counter()
    for h, (verdict, reasons) in system_hash_verdict.items():
        categories[classify_by_reasons(verdict, reasons)] += 1
    p()
    for cat, count in categories.most_common():
        pct = 100 * count / total
        p(f"  {cat:30s}  {count:>10,}  ({pct:.1f}%)")

    # Overlap
    p("\n" + "=" * 60)
    p("OVERLAP ANALYSIS")
    p("=" * 60)
    system_hashes = set(system_hash_verdict.keys())
    both = system_hashes & eig_hashes_in_range
    system_only = system_hashes - eig_hashes_in_range
    eig_only = eig_hashes_in_range - system_hashes
    p(f"Argos total (unique hashes): {len(system_hashes):,}")
    p(f"Eigenphi in range (unique):  {len(eig_hashes_in_range):,}")
    p(f"Both (TP candidates):        {len(both):,}")
    p(f"Argos only (FP candidates):  {len(system_only):,}")
    p(f"Eigenphi only (FN cand.):    {len(eig_only):,}")

    output_path = SUMMARIES_DIR / "01_statistics/explore.txt"
    with open(output_path, "w") as f:
        f.write("\n".join(out) + "\n")
    print(f"\nOutput saved to {output_path}")


if __name__ == "__main__":
    main()
