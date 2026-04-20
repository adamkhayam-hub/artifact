"""
20_attempted_competition.py — Attempted arbitrages as MEV competition signal.

Analyzes the ratio of attempted/confirmed per block. Blocks with many
attempted arbs and few confirmed ones suggest bot competition.

Reads:  data/system_compact.csv
Writes: summaries/01_statistics/attempted.txt
        figures/fig_attempted_ratio.pdf
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import sys
import numpy as np
from collections import Counter, defaultdict
from config import SUMMARIES_DIR, FIGURES_DIR, load_compact

OUT_TXT = SUMMARIES_DIR / "01_statistics/attempted.txt"
OUT_FIG = FIGURES_DIR / "fig_attempted_ratio.pdf"


def p(msg="", f=None):
    print(msg)
    if f:
        f.write(msg + "\n")


def main():
    rows = load_compact()

    # Classify each row
    confirmed = 0
    attempted = 0
    probable = 0
    uncertain = 0
    total = len(rows)

    blocks_confirmed = defaultdict(int)
    blocks_attempted = defaultdict(int)
    blocks_total = defaultdict(int)

    for r in rows:
        block = r["block"]
        reasons = r["reasons"]
        verdict = r["verdict"]
        blocks_total[block] += 1

        if verdict == "arbitrage":
            confirmed += 1
            blocks_confirmed[block] += 1
        elif "negativeProfit" in reasons or "finalBalanceNegative" in reasons:
            attempted += 1
            blocks_attempted[block] += 1
        elif "leftoverTransaction" in reasons and "negativeProfit" not in reasons:
            probable += 1
        else:
            uncertain += 1

    with open(OUT_TXT, "w") as out:
        p("=" * 60, out)
        p("ATTEMPTED ARBITRAGES AS COMPETITION SIGNAL", out)
        p("=" * 60, out)
        p(f"Total detections: {total:,}", out)
        p(f"  Confirmed:  {confirmed:>10,} ({100*confirmed/total:.1f}%)", out)
        p(f"  Attempted:  {attempted:>10,} ({100*attempted/total:.1f}%)", out)
        p(f"  Probable:   {probable:>10,} ({100*probable/total:.1f}%)", out)
        p(f"  Uncertain:  {uncertain:>10,} ({100*uncertain/total:.1f}%)", out)
        p("", out)

        # Per-block analysis
        all_blocks = set(blocks_confirmed.keys()) | set(blocks_attempted.keys())
        block_ratios = []
        for b in all_blocks:
            c = blocks_confirmed.get(b, 0)
            a = blocks_attempted.get(b, 0)
            if c + a > 0:
                block_ratios.append((b, c, a, a / (c + a)))

        if block_ratios:
            ratios = [r[3] for r in block_ratios]
            p(f"Blocks with any detection: {len(block_ratios):,}", out)
            p(f"Attempted / (attempted + confirmed) ratio:", out)
            p(f"  Mean:   {np.mean(ratios):.3f}", out)
            p(f"  Median: {np.median(ratios):.3f}", out)
            p(f"  Blocks with ratio > 0.8: {sum(1 for r in ratios if r > 0.8):,}", out)
            p(f"  Blocks with ratio = 0:   {sum(1 for r in ratios if r == 0):,}", out)

            # Correlation: more attempted → fewer confirmed?
            cs = [r[1] for r in block_ratios]
            ats = [r[2] for r in block_ratios]
            if len(cs) > 10:
                corr = np.corrcoef(cs, ats)[0, 1]
                p(f"\n  Correlation(confirmed, attempted): {corr:.3f}", out)

    print(f"Summary: {OUT_TXT}")

    # Figure: histogram of per-block attempted ratio
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        if block_ratios:
            ratios = [r[3] for r in block_ratios]

            fig, ax = plt.subplots(figsize=(5.5, 3.2))
            counts, edges, patches = ax.hist(
                ratios, bins=20, range=(0, 1),
                color="steelblue", edgecolor="white",
                linewidth=0.5)

            ax.set_xlabel(
                "Attempted / (attempted + confirmed) ratio",
                fontsize=9)
            ax.set_ylabel("Blocks (thousands)", fontsize=9)
            ax.set_yticklabels(
                [f"{int(y/1000)}" for y in ax.get_yticks()])
            ax.tick_params(labelsize=8)
            ax.axvline(
                np.median(ratios), color="red", linestyle="--",
                linewidth=1, label=f"median = {np.median(ratios):.2f}")
            ax.legend(fontsize=8, loc="upper right")
            ax.set_xlim(0, 1)
            plt.tight_layout()
            fig.savefig(OUT_FIG, dpi=300, bbox_inches="tight")
            plt.close()
            print(f"Figure: {OUT_FIG}")
    except ImportError:
        print("matplotlib not available; skipping figure.")


if __name__ == "__main__":
    main()
