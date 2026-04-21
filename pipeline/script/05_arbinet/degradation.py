"""
24_arbinet_degradation.py — ArbiNet temporal degradation curve.

For each 100-block window in the 1000-block range, plot ArbiNet's
detection count vs ours. Visualizes temporal stability.

Reads:  data/system_compact.csv
        data/eigenphi_arbis_txs_filtered.csv
        data/arbinet/arbinet1k.csv
Writes: summaries/05_arbinet/degradation.txt
        figures/fig_arbinet_degradation.pdf
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import sys
from collections import defaultdict
from pathlib import Path

csv.field_size_limit(sys.maxsize)

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
DATA_DIR = EVAL_DIR / "data"
SUMMARIES_DIR = EVAL_DIR / "output" / "summaries"
FIGURES_DIR = EVAL_DIR / "output" / "figures"
SUMMARIES_DIR.mkdir(parents=True, exist_ok=True)
FIGURES_DIR.mkdir(parents=True, exist_ok=True)

from config import load_compact, normalize_hash

ARBINET_CSV = DATA_DIR / "arbinet" / "arbinet1k.csv"
EIGENPHI_CSV = DATA_DIR / "eigenphi_arbis_txs.csv"  # full, covers 24.1M range
THREEWAY_CSV = DATA_DIR / "system_arbis_3wayeval.csv"

FIRST_BLOCK = 24_100_000
LAST_BLOCK = 24_100_999
WINDOW = 100

OUT_TXT = SUMMARIES_DIR / "05_arbinet/degradation.txt"
OUT_FIG = FIGURES_DIR / "fig_arbinet_degradation.pdf"


def p(msg="", f=None):
    print(msg)
    if f:
        f.write(msg + "\n")


def main():
    # Load Ours (3-way CSV for the ArbiNet block range)
    system_by_block = defaultdict(int)
    if THREEWAY_CSV.exists():
        with open(THREEWAY_CSV) as f:
            reader = csv.reader(f)
            for row in reader:
                if row[0].startswith("transaction"):
                    continue
                try:
                    block = int(row[1])
                    if FIRST_BLOCK <= block <= LAST_BLOCK:
                        system_by_block[block] += 1
                except (IndexError, ValueError):
                    pass
    else:
        # Fallback: compact CSV (only works if range overlaps)
        rows = load_compact()
        for r in rows:
            if FIRST_BLOCK <= r["block"] <= LAST_BLOCK:
                system_by_block[r["block"]] += 1

    # Load ArbiNet
    arbinet_by_block = defaultdict(int)
    if ARBINET_CSV.exists():
        with open(ARBINET_CSV) as f:
            reader = csv.DictReader(f)
            for row in reader:
                block = int(row["block"])
                if FIRST_BLOCK <= block <= LAST_BLOCK:
                    arbinet_by_block[block] += 1

    # Load Eigenphi
    eigenphi_by_block = defaultdict(int)
    with open(EIGENPHI_CSV) as f:
        reader = csv.reader(f)
        for row in reader:
            try:
                block = int(row[0])
                if FIRST_BLOCK <= block <= LAST_BLOCK:
                    eigenphi_by_block[block] += 1
            except (IndexError, ValueError):
                pass

    # Window aggregation
    windows = []
    for start in range(FIRST_BLOCK, LAST_BLOCK + 1, WINDOW):
        end = min(start + WINDOW - 1, LAST_BLOCK)
        a = sum(system_by_block.get(b, 0) for b in range(start, end + 1))
        n = sum(arbinet_by_block.get(b, 0) for b in range(start, end + 1))
        e = sum(eigenphi_by_block.get(b, 0) for b in range(start, end + 1))
        windows.append((start, end, a, n, e))

    with open(OUT_TXT, "w") as out:
        p("=" * 60, out)
        p(f"ARBINET TEMPORAL DEGRADATION ({WINDOW}-block windows)", out)
        p("=" * 60, out)
        p(f"Block range: {FIRST_BLOCK}-{LAST_BLOCK}", out)
        p(f"Windows: {len(windows)}", out)
        p("", out)

        p(f"{'Window':<20s} {'Ours':>8s} {'ArbiNet':>8s} {'Eigenphi':>8s}", out)
        p("-" * 48, out)
        for start, end, a, n, e in windows:
            p(f"  {start}-{end}  {a:>8d} {n:>8d} {e:>8d}", out)

        # Totals
        total_a = sum(w[2] for w in windows)
        total_n = sum(w[3] for w in windows)
        total_e = sum(w[4] for w in windows)
        p("-" * 48, out)
        p(f"  {'TOTAL':<17s}  {total_a:>8d} {total_n:>8d} {total_e:>8d}", out)

    print(f"Summary: {OUT_TXT}")

    # Figure
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        xs = range(len(windows))
        system_vals = [w[2] for w in windows]
        arbinet_vals = [w[3] for w in windows]
        eigenphi_vals = [w[4] for w in windows]

        fig, ax = plt.subplots(figsize=(8, 4))
        ax.plot(xs, system_vals, "o-", label="Ours", markersize=4, color="steelblue")
        ax.plot(xs, arbinet_vals, "s-", label="ArbiNet", markersize=4, color="orange")
        ax.plot(xs, eigenphi_vals, "^-", label="Eigenphi", markersize=4, color="green")
        ax.set_xlabel(f"Window ({WINDOW}-block)")
        ax.set_ylabel("Detections")
        ax.set_title("Detection rate per window: three-way comparison")
        ax.legend()
        plt.tight_layout()
        fig.savefig(OUT_FIG, dpi=150, bbox_inches="tight")
        plt.close()
        print(f"Figure: {OUT_FIG}")
    except ImportError:
        print("matplotlib not available; skipping figure.")


if __name__ == "__main__":
    main()
