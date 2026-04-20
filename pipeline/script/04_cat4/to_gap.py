"""
27_cat4_to_gap.py — Analyze cat4 (Eigenphi-only) transactions for
the to_ gap: arbitrage cycles detected by the fixpoint but not
surfaced by the classification layer.

Reads:
    data/cat4_forensic/summary.csv
    data/cat4_forensic/<tx_hash>/*.dot

Writes:
    summaries/04_cat4/to_gap.txt

Also generates PDFs from DOT files for all cat4 transactions.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import os
import subprocess
from pathlib import Path

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
SUMMARIES_DIR = EVAL_DIR / "output" / "summaries"
SUMMARIES_DIR.mkdir(parents=True, exist_ok=True)

CAT4_DIR = EVAL_DIR / "output" / "cat4_forensic"
SUMMARY_CSV = CAT4_DIR / "summary.csv"
OUT_TXT = SUMMARIES_DIR / "04_cat4/to_gap.txt"


def generate_pdfs(tx_dir):
    """Generate PDFs from all DOT files in a transaction directory."""
    generated = 0
    for f in sorted(os.listdir(tx_dir)):
        if f.endswith(".dot"):
            dot_path = os.path.join(tx_dir, f)
            pdf_path = os.path.join(tx_dir, f.replace(".dot", ".pdf"))
            result = subprocess.run(
                ["dot", "-Tpdf", dot_path, "-o", pdf_path],
                capture_output=True,
            )
            if result.returncode == 0:
                generated += 1
    return generated


def has_yellow_node(dot_path):
    """Check if a DOT file contains a yellow (arbitrage) node
    beyond the legend."""
    with open(dot_path) as f:
        content = f.read()
    # Legend always has one FFFF99 entry; a real yellow node adds more
    count = content.count("#FFFF99")
    return count > 1


def get_last_dot(tx_dir):
    """Return the path to the last (highest-numbered) DOT file."""
    dots = sorted(
        [f for f in os.listdir(tx_dir) if f.endswith(".dot")],
        key=lambda x: int(x.replace(".dot", "")),
    )
    if not dots:
        return None
    return os.path.join(tx_dir, dots[-1])


def main():
    if not SUMMARY_CSV.exists():
        print(f"ERROR: {SUMMARY_CSV} not found.")
        print("Run cat4 forensic first (step 13).")
        return

    out = []

    def p(s=""):
        out.append(s)
        print(s)

    p("=" * 60)
    p("CAT4 TO_ GAP ANALYSIS")
    p("=" * 60)

    yellow_txs = []
    cycles_no_yellow_txs = []
    no_cycles_txs = []
    missing_dir_txs = []
    total_pdfs = 0
    total = 0

    with open(SUMMARY_CSV) as f:
        reader = csv.DictReader(f)
        for row in reader:
            total += 1
            tx = row["tx_hash"]
            tx_dir = CAT4_DIR / tx

            if not tx_dir.is_dir():
                missing_dir_txs.append(tx)
                continue

            # Generate PDFs
            n_pdfs = generate_pdfs(str(tx_dir))
            total_pdfs += n_pdfs

            # Check last DOT for yellow node
            last_dot = get_last_dot(str(tx_dir))
            if last_dot is None:
                no_cycles_txs.append(tx)
                continue

            has_yellow = has_yellow_node(last_dot)
            num_cycles = int(row.get("num_cycles", 0))

            if has_yellow:
                yellow_txs.append(tx)
            elif num_cycles > 0:
                cycles_no_yellow_txs.append(tx)
            else:
                no_cycles_txs.append(tx)

    p(f"Total cat4 transactions: {total}")
    p(f"  With DOT files: {total - len(missing_dir_txs)}")
    p(f"  Missing directories: {len(missing_dir_txs)}")
    p(f"  PDFs generated: {total_pdfs}")
    p()
    p("-" * 60)
    p("CLASSIFICATION")
    p("-" * 60)

    classified = total - len(missing_dir_txs)
    if classified > 0:
        y_pct = 100 * len(yellow_txs) / classified
        c_pct = 100 * len(cycles_no_yellow_txs) / classified
        n_pct = 100 * len(no_cycles_txs) / classified
    else:
        y_pct = c_pct = n_pct = 0

    p(f"  Yellow node (to_ gap):      {len(yellow_txs):>4}"
      f"  ({y_pct:.1f}%)  — real arbitrage, fixpoint detects,"
      f" classification misses")
    p(f"  Cycles but no yellow:       {len(cycles_no_yellow_txs):>4}"
      f"  ({c_pct:.1f}%)  — structural cycles, not arbitrages"
      f" (cross-token)")
    p(f"  No cycles at all:           {len(no_cycles_txs):>4}"
      f"  ({n_pct:.1f}%)  — Eigenphi false positives")
    p()

    p("-" * 60)
    p("YELLOW NODE TRANSACTIONS (to_ gap)")
    p("-" * 60)
    for tx in yellow_txs:
        p(f"  0x{tx}")
    p()

    p("-" * 60)
    p("SUMMARY FOR PAPER")
    p("-" * 60)
    p(f"Of {classified} Eigenphi-only transactions reanalyzed via RPC:")
    p(f"  {n_pct:.0f}% are false positives (no cycles)")
    p(f"  {c_pct:.0f}% contain structural cycles but no"
      f" token-equivalent cycle")
    p(f"  {y_pct:.0f}% contain arbitrage cycles at inner contract"
      f" addresses")
    p(f"     not yet surfaced by the classification layer"
      f" (to_ limitation)")

    with open(OUT_TXT, "w") as f:
        f.write("\n".join(out) + "\n")
    print(f"\nOutput saved to {OUT_TXT}")


if __name__ == "__main__":
    main()
