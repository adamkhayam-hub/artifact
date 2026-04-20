"""
17_performance.py — Analyze per-transaction execution time.

Reads: data/system_compact.csv (columns decode_ms, algo_ms)
       Run 00_preprocess.py first to generate this file.
Writes:
    summaries/01_statistics/performance.txt
    figures/fig_latency.pdf

The bench script (debug_arbi_bench.exe) writes decode and algo
timing per transaction into the CSV.  This script computes
aggregate statistics and produces a latency distribution figure.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import sys
import numpy as np

from config import SUMMARIES_DIR, FIGURES_DIR, load_compact

OUT_TXT = SUMMARIES_DIR / "01_statistics/performance.txt"
OUT_FIG = FIGURES_DIR / "fig_latency.pdf"


def p(msg="", f=None):
    print(msg)
    if f:
        f.write(msg + "\n")


def main():
    rows = load_compact()  # exits with clear error if compact CSV missing

    decode_times = []
    algo_times = []
    total_times = []
    skipped = 0

    print("Reading timing data from system_compact.csv...")
    for r in rows:
        decode_ms = r["decode_ms"]
        algo_ms = r["algo_ms"]
        if decode_ms is None or algo_ms is None:
            skipped += 1
            continue
        decode_times.append(decode_ms)
        algo_times.append(algo_ms)
        total_times.append(decode_ms + algo_ms)

    if not total_times:
        print("ERROR: No valid timing data found.")
        sys.exit(1)

    decode = np.array(decode_times)
    algo = np.array(algo_times)
    total = np.array(total_times)

    with open(OUT_TXT, "w") as out:
        p("=" * 60, out)
        p("PERFORMANCE ANALYSIS", out)
        p("=" * 60, out)
        p(f"Transactions with timing data: {len(total):,}", out)
        if skipped:
            p(f"Skipped (missing/invalid): {skipped:,}", out)
        p("", out)

        for name, arr in [("Decode", decode),
                          ("Algorithm", algo),
                          ("Total (decode+algo)", total)]:
            p(f"  {name}:", out)
            p(f"    Median:  {np.median(arr):.2f} ms", out)
            p(f"    Mean:    {np.mean(arr):.2f} ms", out)
            p(f"    P95:     {np.percentile(arr, 95):.2f} ms", out)
            p(f"    P99:     {np.percentile(arr, 99):.2f} ms", out)
            p(f"    Max:     {np.max(arr):.2f} ms", out)
            p("", out)

        # Outlier analysis
        p("-" * 60, out)
        p("OUTLIER ANALYSIS (total > 100ms)", out)
        p("-" * 60, out)
        outliers = total > 100
        n_outliers = np.sum(outliers)
        p(f"  Count: {n_outliers:,} ({n_outliers/len(total)*100:.3f}%)", out)
        if n_outliers > 0:
            p(f"  Median of outliers: {np.median(total[outliers]):.1f} ms", out)
            p(f"  Max of outliers: {np.max(total[outliers]):.1f} ms", out)

    print(f"Summary written to {OUT_TXT}")

    # Figure: latency distribution (log scale)
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        fig, ax = plt.subplots(figsize=(6, 3.5))

        # Histogram of total time (log scale x-axis)
        bins = np.logspace(np.log10(max(0.01, total.min())),
                           np.log10(total.max()), 80)
        ax.hist(total, bins=bins, color="steelblue", alpha=0.8,
                edgecolor="none")
        ax.set_xscale("log")
        ax.set_xlabel("Per-transaction latency (ms)")
        ax.set_ylabel("Count")
        ax.set_title("Detection latency distribution")

        # Vertical lines for percentiles
        for pct, label, color in [
            (50, "median", "green"),
            (95, "P95", "orange"),
            (99, "P99", "red"),
        ]:
            val = np.percentile(total, pct)
            ax.axvline(val, color=color, linestyle="--",
                       linewidth=1, alpha=0.8)
            ax.text(val * 1.1, ax.get_ylim()[1] * 0.85, label,
                    color=color, fontsize=8)

        plt.tight_layout()
        fig.savefig(OUT_FIG, dpi=150, bbox_inches="tight")
        plt.close()
        print(f"Figure written to {OUT_FIG}")
    except ImportError:
        print("matplotlib not available; skipping figure.")


if __name__ == "__main__":
    main()
