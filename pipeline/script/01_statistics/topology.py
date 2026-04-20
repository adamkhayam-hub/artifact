"""
Topology breakdown of detected arbitrages.

For each Argos result, extract:
  - Number of cycles (transfersInCycles)
  - Verdict (arbitrage vs warning)
  - Whether lending is involved (num_leftovers > 0 as proxy)

Note: per-cycle transfer details (cycle lengths, token counts) are not
available in the compact CSV and require the full system_arbis.csv.

Reads from: data/system_compact.csv (run 00_preprocess.py first)
Writes to:  summaries/01_statistics/topology.txt
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


from collections import Counter

from config import SUMMARIES_DIR, load_compact


def main():
    out = []

    def p(s=""):
        out.append(s)
        print(s)

    rows = load_compact()

    # --- Parse all Argos results ---
    cycle_count_dist = Counter()  # (verdict, n_cycles) -> count
    verdict_count = Counter()
    has_lending = Counter()  # verdict -> count
    total = len(rows)

    for r in rows:
        verdict = r["verdict"]
        n_cycles = r["num_cycles"]

        verdict_count[verdict] += 1
        cycle_count_dist[(verdict, n_cycles)] += 1

        # num_leftovers > 0 is used as a proxy for lending involvement
        # (transfersInLeftoversCycles is not stored in the compact CSV)
        if r["num_leftovers"] > 0:
            has_lending[verdict] += 1

    total_cycles = sum(
        n * count
        for (verdict, n), count in cycle_count_dist.items()
    )

    # --- Output ---
    p("=" * 60)
    p("TOPOLOGY BREAKDOWN")
    p("=" * 60)
    p(f"Total transactions: {total:,}")
    p(f"Total cycles across all txs: {total_cycles:,}")
    p()

    # Cycles per transaction
    p("CYCLES PER TRANSACTION (by verdict)")
    p("-" * 60)
    p(f"{'Cycles':>8s} {'Arbitrage':>12s} {'Warning':>12s} {'Total':>12s}")
    max_cycles_to_show = 10
    for n in range(1, max_cycles_to_show + 1):
        arb = cycle_count_dist.get(("arbitrage", n), 0)
        warn = cycle_count_dist.get(("warning", n), 0)
        p(f"  {n:>6d} {arb:>12,} {warn:>12,} {arb + warn:>12,}")
    # 11+
    arb_11 = sum(v for (vd, nc), v in cycle_count_dist.items() if vd == "arbitrage" and nc > max_cycles_to_show)
    warn_11 = sum(v for (vd, nc), v in cycle_count_dist.items() if vd == "warning" and nc > max_cycles_to_show)
    p(f"  {'11+':>6s} {arb_11:>12,} {warn_11:>12,} {arb_11 + warn_11:>12,}")

    # Lending involvement
    p(f"\nLENDING INVOLVEMENT [proxy: num_leftovers > 0]")
    p("-" * 60)
    for verdict in ["arbitrage", "warning"]:
        lending = has_lending.get(verdict, 0)
        total_v = verdict_count.get(verdict, 0)
        pct = 100 * lending / total_v if total_v > 0 else 0
        p(f"  {verdict:12s}  {lending:>10,} / {total_v:>10,}  ({pct:.1f}%)")

    p(f"\nNote: cycle lengths and token counts per cycle require the full")
    p(f"      system_arbis.csv (not available in compact CSV).")

    # --- Save ---
    output_path = SUMMARIES_DIR / "01_statistics/topology.txt"
    with open(output_path, "w") as f:
        f.write("\n".join(out) + "\n")
    p(f"\nOutput saved to {output_path}")


if __name__ == "__main__":
    main()
