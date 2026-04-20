"""
Detection accuracy: cross-reference Argos confidence tiers with Eigenphi.

For each Argos reason-based category, compute:
  - How many Eigenphi also flags (agreement)
  - How many Eigenphi does NOT flag (Argos-only)
  - How many are in Eigenphi-excluded (believed position changes)

Also compute:
  - Eigenphi-only txs (FN candidates): Eigenphi flags but Argos doesn't
  - P/R/F1 under different definitions of "positive"

Reads from: data/system_compact.csv (run 00_preprocess.py first),
            data/eigenphi_arbis_txs_filtered.csv
Writes to:  summaries/01_statistics/accuracy.txt
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
from collections import Counter

from config import (
    EIGENPHI_FILTERED,
    DATA_DIR, SUMMARIES_DIR,
    normalize_hash, classify_by_reasons,
    load_compact,
)


def main():
    out = []

    def p(s=""):
        out.append(s)
        print(s)

    # --- Determine overlap max block from compact CSV ---
    rows = load_compact()
    system_max = max(r["block"] for r in rows)

    eig_max = 0
    with open(EIGENPHI_FILTERED, "r") as f:
        reader = csv.reader(f)
        for row in reader:
            b = int(row[0])
            if b > eig_max:
                eig_max = b

    overlap_max = min(system_max, eig_max)

    eig_hashes = set()
    with open(EIGENPHI_FILTERED, "r") as f:
        reader = csv.reader(f)
        for row in reader:
            if int(row[0]) <= overlap_max:
                eig_hashes.add(normalize_hash(row[1]))

    p(f"Overlap max block: {overlap_max}")
    p(f"Eigenphi hashes in range: {len(eig_hashes):,}")

    # --- Load Argos results and classify ---
    system_data = {}  # hash -> (verdict, reasons, category)
    for r in rows:
        if r["block"] > overlap_max:
            continue
        h = r["tx_hash"]
        verdict = r["verdict"]
        reasons = r["reasons"]
        category = classify_by_reasons(verdict, reasons)
        system_data[h] = (verdict, reasons, category)

    system_hashes = set(system_data.keys())
    p(f"Argos hashes in range: {len(system_hashes):,}")

    # --- Cross-reference by category ---
    p("\n" + "=" * 70)
    p("CROSS-REFERENCE: ARGOS CATEGORIES vs EIGENPHI")
    p("=" * 70)

    categories = [
        "confirmed_arbitrage",
        "probable_arbitrage_incomplete",
        "attempted_arbitrage_unprofitable",
        "uncertain_mixed_balance",
        "warning_other",
    ]

    cat_counts = Counter()
    cat_in_eig = Counter()
    cat_not_in_eig = Counter()
    for h, (verdict, reasons, category) in system_data.items():
        cat_counts[category] += 1
        if h in eig_hashes:
            cat_in_eig[category] += 1
        else:
            cat_not_in_eig[category] += 1

    p(f"\n{'Category':<40s} {'Total':>10s} {'In Eig':>10s} {'%Eig':>7s} {'Argos-only':>12s}")
    p("-" * 82)
    for cat in categories:
        total = cat_counts[cat]
        in_eig = cat_in_eig[cat]
        not_eig = cat_not_in_eig[cat]
        pct_eig = 100 * in_eig / total if total > 0 else 0
        p(f"  {cat:<38s} {total:>10,} {in_eig:>10,} {pct_eig:>6.1f}% {not_eig:>12,}")

    total_all = sum(cat_counts.values())
    in_eig_all = sum(cat_in_eig.values())
    not_eig_all = sum(cat_not_in_eig.values())
    pct_all = 100 * in_eig_all / total_all if total_all > 0 else 0
    p("-" * 82)
    p(f"  {'TOTAL':<38s} {total_all:>10,} {in_eig_all:>10,} {pct_all:>6.1f}% {not_eig_all:>12,}")

    # --- Eigenphi-only (FN candidates) ---
    p("\n" + "=" * 70)
    p("EIGENPHI-ONLY (FN CANDIDATES)")
    p("=" * 70)

    eig_only = eig_hashes - system_hashes

    p(f"Eigenphi flags, Argos doesn't:   {len(eig_only):,}")

    # --- P/R/F1 under different definitions ---
    p("\n" + "=" * 70)
    p("PRECISION / RECALL / F1")
    p("=" * 70)
    p("(Eigenphi as ground truth, various Argos positive definitions)\n")

    definitions = [
        ("Argos: arbitrage only", lambda c: c == "confirmed_arbitrage"),
        ("Argos: arbitrage + probable", lambda c: c in ("confirmed_arbitrage", "probable_arbitrage_incomplete")),
        ("Argos: arbitrage + probable + attempted", lambda c: c in ("confirmed_arbitrage", "probable_arbitrage_incomplete", "attempted_arbitrage_unprofitable")),
        ("Argos: all (arbitrage + all warnings)", lambda c: True),
    ]

    for name, pred in definitions:
        system_pos = {h for h, (v, r, c) in system_data.items() if pred(c)}
        tp = len(system_pos & eig_hashes)
        fp = len(system_pos - eig_hashes)
        fn = len(eig_hashes - system_pos)

        precision = tp / (tp + fp) if (tp + fp) > 0 else 0
        recall = tp / (tp + fn) if (tp + fn) > 0 else 0
        f1 = 2 * precision * recall / (precision + recall) if (precision + recall) > 0 else 0

        p(f"  {name}")
        p(f"    TP: {tp:>10,}  FP: {fp:>10,}  FN: {fn:>10,}")
        p(f"    Precision: {precision:.4f}  Recall: {recall:.4f}  F1: {f1:.4f}")
        p()

    # --- Save ---
    output_path = SUMMARIES_DIR / "01_statistics/accuracy.txt"
    with open(output_path, "w") as f:
        f.write("\n".join(out) + "\n")
    p(f"\nOutput saved to {output_path}")


if __name__ == "__main__":
    main()
