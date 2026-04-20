"""
Parse ArbiNet raw output into CSV.

Reads:  data/arbinet/arbinet1k_raw.txt
Writes: data/arbinet/arbinet1k.csv

Format: tx_hash,block
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import re
from pathlib import Path

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
RAW = EVAL_DIR / "data" / "arbinet" / "arbinet1k_raw.txt"
OUT = EVAL_DIR / "data" / "arbinet" / "arbinet1k.csv"


def main():
    current_block = None
    rows = []

    with open(RAW) as f:
        for line in f:
            line = line.strip()
            m = re.match(r"Inspecting Block #(\d+)", line)
            if m:
                current_block = m.group(1)
                continue
            if line.startswith("-> "):
                tx_hash = line[3:].strip()
                rows.append((tx_hash, current_block))

    with open(OUT, "w") as f:
        f.write("tx_hash,block\n")
        for tx_hash, block in rows:
            f.write(f"{tx_hash},{block}\n")

    print(f"Parsed {len(rows)} arbitrages from {RAW.name}")
    print(f"Output: {OUT}")


if __name__ == "__main__":
    main()
