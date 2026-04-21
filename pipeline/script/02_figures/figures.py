"""
Generate evaluation figures for the paper.

Outputs PDF figures to paper/evaluation/figures/:
  - fig_confidence_tiers.pdf: agreement with Eigenphi by confidence tier
  - fig_overlap.pdf: Ours vs Eigenphi detection overlap

Note: fig_cycle_lengths.pdf requires per-cycle transfer data from the
full system_arbis.csv (cycle lengths are not stored in system_compact.csv).

Reads from: data/system_compact.csv (run 00_preprocess.py first),
            data/eigenphi_arbis_txs_filtered.csv
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np

from config import (
    EIGENPHI_FILTERED,
    DATA_DIR, FIGURES_DIR, SUMMARIES_DIR,
    normalize_hash, classify_by_reasons,
    load_compact,
)

# --- Style ---
plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9,
    "axes.labelsize": 9,
    "xtick.labelsize": 8,
    "ytick.labelsize": 8,
    "legend.fontsize": 8,
    "figure.dpi": 300,
})


def load_data():
    """Load all datasets and return classified Ours data + Eigenphi hashes."""
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

    # Eigenphi hashes
    eig_hashes = set()
    with open(EIGENPHI_FILTERED, "r") as f:
        reader = csv.reader(f)
        for row in reader:
            if int(row[0]) <= overlap_max:
                eig_hashes.add(normalize_hash(row[1]))

    # Ours data filtered to overlap range
    system_data = {}
    for r in rows:
        if r["block"] > overlap_max:
            continue
        h = r["tx_hash"]
        verdict = r["verdict"]
        reasons = r["reasons"]
        category = classify_by_reasons(verdict, reasons)
        system_data[h] = (verdict, reasons, category)

    return system_data, eig_hashes


def fig_confidence_tiers(system_data, eig_hashes):
    """Stacked bar chart: each tier split into Eigenphi-agreed vs Ours-only."""
    categories = [
        ("Confirmed", "confirmed_arbitrage"),
        ("Probable", "probable_arbitrage_incomplete"),
        ("Attempted", "attempted_arbitrage_unprofitable"),
        ("Uncertain", "uncertain_mixed_balance"),
    ]

    labels = []
    agreed = []
    system_only = []

    for label, cat in categories:
        cat_hashes = {h for h, (v, r, c) in system_data.items() if c == cat}
        in_eig = len(cat_hashes & eig_hashes)
        not_eig = len(cat_hashes - eig_hashes)
        labels.append(label)
        agreed.append(in_eig)
        system_only.append(not_eig)

    fig, ax = plt.subplots(figsize=(3.4, 2.2))

    x = np.arange(len(labels))
    width = 0.55

    bars1 = ax.bar(x, agreed, width, label="Also in Eigenphi",
                   color="#4878A8", edgecolor="white", linewidth=0.3)
    bars2 = ax.bar(x, system_only, width, bottom=agreed,
                   label="Ours only", color="#E8A87C",
                   edgecolor="white", linewidth=0.3)

    # Build x-axis labels with percentage in Eigenphi color
    pcts = []
    for a, ao in zip(agreed, system_only):
        total = a + ao
        pcts.append(100 * a / total if total > 0 else 0)

    ax.set_xticks(x)
    tick_labels = [f"{lbl}\n{pct:.0f}% overlap"
                   for lbl, pct in zip(labels, pcts)]
    ax.set_xticklabels(tick_labels, rotation=0, fontsize=6)
    ax.set_ylabel("Transactions")
    ax.yaxis.set_major_formatter(mticker.FuncFormatter(
        lambda x, _: f"{x/1e6:.1f}M" if x >= 1e6 else f"{x/1e3:.0f}K"))
    ax.legend(loc="upper right", framealpha=0.9, fontsize=6,
              bbox_to_anchor=(1.0, 1.0))
    ax.set_title("Eigenphi agreement by confidence tier",
                 fontsize=8)
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)

    fig.tight_layout()
    path = FIGURES_DIR / "fig_confidence_tiers.pdf"
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {path}")


def fig_overlap(system_data, eig_hashes):
    """Three-column stacked bar: Eigenphi-only, Both, Ours-only,
    each broken down by Ours confidence tier."""
    system_hashes = set(system_data.keys())
    both_hashes = system_hashes & eig_hashes
    system_only_hashes = system_hashes - eig_hashes
    eig_only_count = len(eig_hashes - system_hashes)

    tiers = [
        ("Confirmed", "confirmed_arbitrage", "#4878A8"),
        ("Probable", "probable_arbitrage_incomplete", "#7BAE7F"),
        ("Attempted", "attempted_arbitrage_unprofitable", "#E8A87C"),
        ("Uncertain", "uncertain_mixed_balance", "#D4A5A5"),
    ]

    # Count tiers for "Both" and "Ours-only"
    from collections import Counter
    both_tier_counts = Counter()
    for h in both_hashes:
        _, _, cat = system_data[h]
        both_tier_counts[cat] += 1

    system_only_tier_counts = Counter()
    for h in system_only_hashes:
        _, _, cat = system_data[h]
        system_only_tier_counts[cat] += 1

    fig, ax = plt.subplots(figsize=(3.4, 2.4))

    columns = ["Eigenphi\nonly", "Both", "Ours\nonly"]
    x = np.arange(len(columns))
    width = 0.55

    # Eigenphi-only: single gray bar (no Ours tiers)
    # Both and Ours-only: stacked by tier
    for i, (tier_label, tier_key, color) in enumerate(tiers):
        both_val = both_tier_counts.get(tier_key, 0)
        system_val = system_only_tier_counts.get(tier_key, 0)

        # Compute bottoms
        both_bottom = sum(both_tier_counts.get(t[1], 0) for t in tiers[:i])
        system_bottom = sum(system_only_tier_counts.get(t[1], 0) for t in tiers[:i])

        # Both column (index 1)
        ax.bar(x[1], both_val, width, bottom=both_bottom,
               color=color, edgecolor="white", linewidth=0.3,
               label=tier_label if i < len(tiers) else None)
        # Ours-only column (index 2)
        ax.bar(x[2], system_val, width, bottom=system_bottom,
               color=color, edgecolor="white", linewidth=0.3)

    # Eigenphi-only column (index 0): single color, no tier breakdown
    ax.bar(x[0], eig_only_count, width, color="#888888",
           edgecolor="white", linewidth=0.3)

    # Total labels on top
    totals = [eig_only_count, len(both_hashes), len(system_only_hashes)]
    for i, total in enumerate(totals):
        label = f"{total/1e6:.1f}M" if total >= 1e6 else f"{total/1e3:.0f}K"
        ax.text(i, total + 30000, label,
                ha="center", va="bottom", fontsize=7, fontweight="bold")

    # Annotate the 295K confirmed in Ours-only
    confirmed_system_only = system_only_tier_counts.get("confirmed_arbitrage", 0)
    ax.annotate(f"{confirmed_system_only/1e3:.0f}K\nconfirmed",
                xy=(x[2], confirmed_system_only / 2),
                fontsize=6, ha="center", va="center",
                fontweight="bold", color="white")

    ax.set_xticks(x)
    ax.set_xticklabels(columns, fontsize=8)
    ax.set_ylabel("Transactions")
    ax.yaxis.set_major_formatter(mticker.FuncFormatter(
        lambda x, _: f"{x/1e6:.1f}M" if x >= 1e6 else f"{x/1e3:.0f}K"))
    ax.legend(loc="upper left", framealpha=0.9, fontsize=7)
    ax.set_title("Detection overlap by confidence tier")
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)

    fig.tight_layout()
    path = FIGURES_DIR / "fig_overlap.pdf"
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved {path}")


def main():
    print("Loading data...")
    system_data, eig_hashes = load_data()
    print(f"Loaded {len(system_data):,} Ours results, {len(eig_hashes):,} Eigenphi hashes")

    print("Generating figures...")
    fig_confidence_tiers(system_data, eig_hashes)
    fig_overlap(system_data, eig_hashes)

    print("Note: fig_cycle_lengths.pdf requires the full system_arbis.csv "
          "(cycle lengths are not stored in system_compact.csv).")

    # Save summary
    summary = [
        f"Figures generated: {FIGURES_DIR}",
        f"  fig_confidence_tiers.pdf",
        f"  fig_overlap.pdf",
        f"Ours results loaded: {len(system_data):,}",
        f"Eigenphi hashes loaded: {len(eig_hashes):,}",
    ]
    output_path = SUMMARIES_DIR / "02_figures/figures.txt"
    with open(output_path, "w") as f:
        f.write("\n".join(summary) + "\n")
    print(f"Summary saved to {output_path}")
    print("Done.")


if __name__ == "__main__":
    main()
