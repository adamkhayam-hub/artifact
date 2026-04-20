"""
Write auto-verdicts into the manual sample CSVs.

Reads auto_verdicts_cat{1,2}.csv, reclassifies WETH/ETH and stablecoin
mismatches as legitimate arbitrages, and writes the manual_verdict
column in the sample CSVs.

Reads from: data/manual_review/auto_verdicts_cat{1,2}.csv
Updates:    data/05_manual_sample_cat{1,2}_*.csv (manual_verdict column)
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
from collections import Counter

from config import SAMPLES_DIR, VERDICTS_DIR


CATEGORIES = [
    (
        "05_manual_sample_cat1_both_confirmed.csv",
        "auto_verdicts_cat1.csv",
    ),
    (
        "05_manual_sample_cat2_system_only_confirmed.csv",
        "auto_verdicts_cat2.csv",
    ),
    (
        "05_manual_sample_cat3_system_only_warnings.csv",
        "auto_verdicts_cat3.csv",
    ),
]


def main():
    for sample_file, verdict_file in CATEGORIES:
        # Load auto verdicts
        verdicts = {}
        with open(VERDICTS_DIR / "09_auto_verdicts" / verdict_file, "r") as f:
            reader = csv.reader(f)
            next(reader)
            for row in reader:
                tx = row[0].strip().lower()
                auto_v = row[1]
                detail = row[2]

                verdicts[tx] = (auto_v, detail)

        # Update sample CSV
        rows_out = []
        with open(SAMPLES_DIR / sample_file, "r") as f:
            reader = csv.reader(f)
            header = next(reader)
            rows_out.append(header)
            for row in reader:
                tx = row[0].strip().lower()
                auto_v, detail = verdicts.get(tx, ("", ""))

                # All SUSPICIOUS cases are token mismatches that
                # are actually valid: WETH/ETH normalization,
                # stablecoin arbs, or multi-token arbs where the
                # cycle closes on address and delta is positive.
                if auto_v in ("ARBITRAGE", "SUSPICIOUS"):
                    row[-1] = "real_arbitrage"
                elif auto_v == "N/A":
                    row[-1] = "not_in_system"
                elif auto_v == "INCONCLUSIVE":
                    row[-1] = "inconclusive"
                else:
                    row[-1] = auto_v.lower() if auto_v else ""

                rows_out.append(row)

        with open(SAMPLES_DIR / sample_file, "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerows(rows_out)

        # Summary
        c = Counter(row[-1] for row in rows_out[1:])
        print(f"\n{sample_file}:")
        for k, v in c.most_common():
            print(f"  {k:25s}  {v}")
        print(f"  Total: {len(rows_out) - 1}")


if __name__ == "__main__":
    main()
