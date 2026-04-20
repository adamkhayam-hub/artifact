"""
22_temporal_distribution.py — Detection rate over time.

Groups detections by block ranges and shows temporal trends.

Reads:  data/system_compact.csv
Writes: summaries/01_statistics/temporal.txt
        figures/fig_temporal.pdf
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import sys
import numpy as np
from collections import defaultdict
from config import SUMMARIES_DIR, FIGURES_DIR, load_compact

OUT_TXT = SUMMARIES_DIR / "01_statistics/temporal.txt"
OUT_FIG = FIGURES_DIR / "fig_temporal.pdf"

BUCKET_SIZE = 10_000  # blocks per bucket


def p(msg="", f=None):
    print(msg)
    if f:
        f.write(msg + "\n")


def main():
    rows = load_compact()

    buckets_confirmed = defaultdict(int)
    buckets_warning = defaultdict(int)
    buckets_total = defaultdict(int)

    for r in rows:
        block = r["block"]
        bucket = (block // BUCKET_SIZE) * BUCKET_SIZE
        verdict = r["verdict"]
        buckets_total[bucket] += 1
        if verdict == "arbitrage":
            buckets_confirmed[bucket] += 1
        else:
            buckets_warning[bucket] += 1

    all_buckets = sorted(set(buckets_total.keys()))

    with open(OUT_TXT, "w") as out:
        p("=" * 60, out)
        p(f"TEMPORAL DISTRIBUTION (per {BUCKET_SIZE:,} blocks)", out)
        p("=" * 60, out)
        p(f"Total buckets: {len(all_buckets)}", out)
        p(f"Total detections: {sum(buckets_total.values()):,}", out)
        p("", out)

        p(f"{'Block range':<25s} {'Confirmed':>10s} {'Warning':>10s} {'Total':>10s}", out)
        p("-" * 58, out)
        for b in all_buckets:
            c = buckets_confirmed.get(b, 0)
            w = buckets_warning.get(b, 0)
            t = buckets_total.get(b, 0)
            p(f"  {b:>10,}-{b+BUCKET_SIZE-1:>10,}  {c:>10,} {w:>10,} {t:>10,}", out)

        # Variance
        totals = [buckets_total[b] for b in all_buckets]
        p("", out)
        p(f"Detection rate per bucket:", out)
        p(f"  Mean:   {np.mean(totals):.0f}", out)
        p(f"  Std:    {np.std(totals):.0f}", out)
        p(f"  Min:    {np.min(totals)}", out)
        p(f"  Max:    {np.max(totals)}", out)

    print(f"Summary: {OUT_TXT}")

    # Figure
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        fig, ax = plt.subplots(figsize=(8, 4))
        xs = all_buckets
        cs = [buckets_confirmed.get(b, 0) for b in xs]
        ws = [buckets_warning.get(b, 0) for b in xs]

        ax.bar(range(len(xs)), cs, label="Confirmed", color="steelblue", alpha=0.8)
        ax.bar(range(len(xs)), ws, bottom=cs, label="Warning", color="orange", alpha=0.7)
        ax.set_xlabel(f"Block range (×{BUCKET_SIZE:,})")
        ax.set_ylabel("Detections")
        ax.set_title("Detection rate over time")
        ax.legend()

        # Sparse x-ticks
        tick_step = max(1, len(xs) // 10)
        ax.set_xticks(range(0, len(xs), tick_step))
        ax.set_xticklabels([f"{xs[i]//1_000_000:.1f}M" for i in range(0, len(xs), tick_step)],
                           rotation=45, fontsize=8)

        plt.tight_layout()
        fig.savefig(OUT_FIG, dpi=150, bbox_inches="tight")
        plt.close()
        print(f"Figure: {OUT_FIG}")
    except ImportError:
        print("matplotlib not available; skipping figure.")


if __name__ == "__main__":
    main()
