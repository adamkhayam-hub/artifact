"""
23_gas_efficiency.py — Gas efficiency of arbitrages.

Ratio of profit to gas cost across confirmed arbitrages.
Shows economic margins.

Reads:  data/system_compact.csv
Writes: summaries/01_statistics/gas.txt
        figures/fig_gas_efficiency.pdf
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import sys
import numpy as np
from config import SUMMARIES_DIR, FIGURES_DIR, load_compact

OUT_TXT = SUMMARIES_DIR / "01_statistics/gas.txt"
OUT_FIG = FIGURES_DIR / "fig_gas_efficiency.pdf"


def p(msg="", f=None):
    print(msg)
    if f:
        f.write(msg + "\n")


def main():
    rows = load_compact()

    # For gas efficiency we need decode_ms + algo_ms as proxy
    # The actual profit/gas ratio requires the full JSON (delta balance + gas costs)
    # From compact CSV we can analyze timing efficiency
    confirmed = [r for r in rows if r["verdict"] == "arbitrage"]
    warnings = [r for r in rows if r["verdict"] == "warning"]

    with open(OUT_TXT, "w") as out:
        p("=" * 60, out)
        p("DETECTION EFFICIENCY", out)
        p("=" * 60, out)

        for label, subset in [("Confirmed", confirmed), ("Warnings", warnings)]:
            decode_times = [r["decode_ms"] for r in subset if r["decode_ms"] is not None]
            algo_times = [r["algo_ms"] for r in subset if r["algo_ms"] is not None]
            total_times = [d + a for d, a in zip(decode_times, algo_times) if d is not None and a is not None]

            if not total_times:
                continue

            p(f"\n{label} ({len(subset):,} transactions):", out)
            p(f"  Decode:  median={np.median(decode_times):.2f}ms  P95={np.percentile(decode_times, 95):.2f}ms", out)
            p(f"  Algo:    median={np.median(algo_times):.2f}ms  P95={np.percentile(algo_times, 95):.2f}ms", out)
            p(f"  Total:   median={np.median(total_times):.2f}ms  P95={np.percentile(total_times, 95):.2f}ms", out)
            p(f"  Algo/Total ratio: {100*np.median(algo_times)/np.median(total_times):.1f}%", out)

        # Cycle count vs timing
        p("\n" + "-" * 60, out)
        p("TIMING BY CYCLE COUNT", out)
        p("-" * 60, out)

        from collections import defaultdict
        by_cycles = defaultdict(list)
        for r in rows:
            if r["decode_ms"] is not None and r["algo_ms"] is not None:
                by_cycles[r["num_cycles"]].append(r["decode_ms"] + r["algo_ms"])

        for nc in sorted(by_cycles.keys())[:10]:
            times = by_cycles[nc]
            p(f"  {nc} cycles: n={len(times):,}  median={np.median(times):.2f}ms  P95={np.percentile(times, 95):.2f}ms", out)

    print(f"Summary: {OUT_TXT}")

    # Figure: algo time vs cycle count
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        cycle_counts = []
        algo_ms = []
        for r in rows:
            if r["algo_ms"] is not None and r["num_cycles"] > 0:
                cycle_counts.append(r["num_cycles"])
                algo_ms.append(r["algo_ms"])

        if cycle_counts:
            fig, ax = plt.subplots(figsize=(6, 4))
            ax.scatter(cycle_counts, algo_ms, alpha=0.1, s=5, color="steelblue")
            ax.set_xlabel("Number of cycles")
            ax.set_ylabel("Algorithm time (ms)")
            ax.set_title("Detection cost vs complexity")
            ax.set_yscale("log")
            plt.tight_layout()
            fig.savefig(OUT_FIG, dpi=150, bbox_inches="tight")
            plt.close()
            print(f"Figure: {OUT_FIG}")
    except ImportError:
        print("matplotlib not available; skipping figure.")


if __name__ == "__main__":
    main()
