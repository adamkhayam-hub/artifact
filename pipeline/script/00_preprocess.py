"""
00_preprocess.py — Single-pass extraction from system_arbis.csv.

Reads:  data/system_arbis.csv (26GB, one pass)
Writes: data/system_compact.csv (lightweight: ~200MB)

Extracts per-transaction: tx_hash, block, verdict, reasons,
decode_time_ms, algo_time_ms.  All subsequent scripts read
from the compact file instead of the full CSV.

Also writes data/system_hashes.txt (one hash per line, for
fast set membership tests).
"""

import csv
import json
import sys
import time
from pathlib import Path

csv.field_size_limit(sys.maxsize)

EVAL_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = EVAL_DIR / "data"

OURS_CSV = DATA_DIR / "system_arbis.csv"
OUTPUT_DIR = EVAL_DIR / "output"
GENERATED_DATA_DIR = OUTPUT_DIR / "data"
COMPACT_CSV = GENERATED_DATA_DIR / "system_compact.csv"
HASHES_TXT = GENERATED_DATA_DIR / "system_hashes.txt"

# Column indices in bench-format CSV
COL_HASH = 0
COL_BLOCK = 1
COL_DECODE_MS = 5
COL_ALGO_MS = 6
COL_TAG_DATA = 7

VERDICT_MAP = {
    0: "arbitrage", 1: "warning",
    "arbitrage": "arbitrage", "warning": "warning",
}

REASON_MAP = {
    0: "leftoverTransaction", 1: "balancePositive", 2: "balanceMixed",
    3: "balanceNegative", 4: "finalBalancePositive", 5: "finalBalanceMixed",
    6: "finalBalanceNegative", 7: "negativeProfit", 8: "noArbitrageCycles",
}


def normalize_hash(h):
    h = h.strip()
    if h.startswith("\\x"):
        h = h[2:]
    if h.startswith("0x") or h.startswith("0X"):
        h = h[2:]
    return h.lower()


def main():
    if not OURS_CSV.exists():
        print(f"ERROR: {OURS_CSV} not found.")
        sys.exit(1)
    GENERATED_DATA_DIR.mkdir(parents=True, exist_ok=True)

    print("=" * 60)
    print("PREPROCESSING: single-pass extraction")
    print(f"  Input:  {OURS_CSV}")
    print(f"  Output: {COMPACT_CSV}")
    print("=" * 60)

    start = time.time()
    total = 0
    parsed = 0
    errors = 0

    with open(OURS_CSV, "r") as fin, \
         open(COMPACT_CSV, "w", newline="") as fout, \
         open(HASHES_TXT, "w") as fhash:

        reader = csv.reader(fin)
        writer = csv.writer(fout)

        # Skip header if present
        first_row = next(reader, None)
        if first_row is None:
            print("ERROR: empty CSV")
            sys.exit(1)

        # Write compact header
        writer.writerow([
            "tx_hash", "block", "verdict", "reasons",
            "num_cycles", "num_leftovers",
            "fixpoint_detected",
            "decode_ms", "algo_ms"
        ])

        # Process first row if it's data (not header)
        rows = [first_row] if not first_row[0].startswith("tx") else []

        for row in reader:
            rows.append(row)

        # Can't iterate and append; let's do it properly
        # Reset — we need to handle the generator correctly

    # Re-read with proper streaming
    with open(OURS_CSV, "r") as fin, \
         open(COMPACT_CSV, "w", newline="") as fout, \
         open(HASHES_TXT, "w") as fhash:

        reader = csv.reader(fin)
        writer = csv.writer(fout)

        writer.writerow([
            "tx_hash", "block", "verdict", "reasons",
            "num_cycles", "num_leftovers",
            "fixpoint_detected",
            "decode_ms", "algo_ms"
        ])

        for row in reader:
            total += 1

            # Skip header
            if total == 1 and row[0].lower().startswith("tx"):
                continue

            try:
                tx_hash = normalize_hash(row[COL_HASH])
                block = row[COL_BLOCK]

                # Timing columns (may be empty in DB export format)
                try:
                    decode_ms = row[COL_DECODE_MS]
                    algo_ms = row[COL_ALGO_MS]
                except IndexError:
                    decode_ms = ""
                    algo_ms = ""

                # Parse tag_data JSON
                tag_raw = row[COL_TAG_DATA]
                data = json.loads(tag_raw)

                resume = data.get("resume", data)
                verdict_raw = resume.get("arbitrage",
                                         resume.get("verdict", ""))
                verdict = VERDICT_MAP.get(verdict_raw, str(verdict_raw))

                reasons_raw = resume.get("reason",
                                         resume.get("reasons", []))
                reasons = "|".join(
                    sorted(REASON_MAP.get(r, str(r))
                           for r in reasons_raw)
                )

                fixpoint_detected = resume.get("fixpointDetected", "")
                rr = resume.get("resume", {})
                num_cycles = len(rr.get("transfersInCycles", []))
                num_leftovers = len(rr.get("leftovers", []))

                writer.writerow([
                    tx_hash, block, verdict, reasons,
                    num_cycles, num_leftovers,
                    fixpoint_detected,
                    decode_ms, algo_ms
                ])
                fhash.write(tx_hash + "\n")
                parsed += 1

            except Exception:
                errors += 1

            if total % 500_000 == 0:
                elapsed = time.time() - start
                print(f"  {total:>10,} rows  ({elapsed:.0f}s)")

    elapsed = time.time() - start
    print()
    print(f"Done in {elapsed:.1f}s")
    print(f"  Total rows:  {total:,}")
    print(f"  Parsed:      {parsed:,}")
    print(f"  Errors:      {errors:,}")
    print(f"  Compact CSV: {COMPACT_CSV}")
    print(f"  Hashes:      {HASHES_TXT}")

    # --- Truncate to evaluation range ---
    print()
    print("=" * 60)
    print("EVALUATION RANGE SELECTION")
    print("=" * 60)

    import pandas as pd

    EVAL_START = 23_699_751
    EVAL_BLOCKS = 220_000
    EVAL_END = EVAL_START + EVAL_BLOCKS - 1

    df = pd.read_csv(COMPACT_CSV)
    total_rows = len(df)
    blocks = sorted(df["block"].unique())
    print(f"  Distinct blocks in CSV: {len(blocks):,}")
    print(f"  Evaluation range: {EVAL_START} -> {EVAL_END}"
          f" ({EVAL_BLOCKS:,} blocks)")

    # Truncate compact CSV to evaluation range
    df_eval = df[(df["block"] >= EVAL_START) & (df["block"] <= EVAL_END)]
    eval_blocks = sorted(df_eval["block"].unique())
    df_eval.to_csv(COMPACT_CSV, index=False)
    print(f"  Truncated compact CSV: {len(df_eval):,} rows"
          f" (was {total_rows:,})")
    print(f"  Blocks with detections: {len(eval_blocks):,}")

    # Check for gaps
    if len(eval_blocks) > 0:
        expected = EVAL_END - EVAL_START + 1
        # Blocks without detections are not gaps — they just had no
        # arbitrage/warning. Only blocks missing from the DB are gaps.
        print(f"  Block range covered: {eval_blocks[0]} -> {eval_blocks[-1]}")

    # Rewrite hashes file
    with open(HASHES_TXT, "w") as fh:
        for h in df_eval["tx_hash"]:
            fh.write(h + "\n")

    # Filter Eigenphi to same block range
    EIGENPHI_FULL = DATA_DIR / "eigenphi_arbis_txs.csv"
    EIGENPHI_FILTERED = GENERATED_DATA_DIR / "eigenphi_arbis_txs_filtered.csv"
    if EIGENPHI_FULL.exists():
        edf = pd.read_csv(EIGENPHI_FULL, header=None,
                          names=["block", "tx_hash"])
        edf_filtered = edf[(edf["block"] >= EVAL_START)
                           & (edf["block"] <= EVAL_END)]
        edf_filtered.to_csv(EIGENPHI_FILTERED, index=False, header=False)
        print(f"  Eigenphi filtered: {len(edf_filtered):,} rows"
              f" (was {len(edf):,})")
    else:
        print(f"  WARN: {EIGENPHI_FULL} not found, skipping Eigenphi filter")

    print(f"\n  Final evaluation: {EVAL_BLOCKS:,} blocks,"
          f" {len(df_eval):,} Ours detections")


if __name__ == "__main__":
    main()
