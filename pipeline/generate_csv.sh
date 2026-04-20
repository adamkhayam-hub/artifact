#!/bin/bash
set -e

PIPELINE_DIR="$(cd "$(dirname "$0")" && pwd)"

cat << 'USAGE'
============================================
  Generate system_arbis.csv
============================================

This script regenerates the main evaluation CSV
from scratch. Two modes are available:

  Offline (from pre-exported traces):
    ./generate_csv.sh offline /path/to/blockdb/evaluation

  RPC (from an archive node):
    ./generate_csv.sh rpc /path/to/config.json 23699751 23919750

The offline mode uses batch_analyse_offline on
pre-exported trace files. The RPC mode uses
batch_analyse to fetch traces from an archive
node via debug_traceTransaction.

USAGE

MODE="${1:?Usage: $0 <offline|rpc> [args...]}"

case "$MODE" in
  offline)
    TRACES_DIR="${2:?Usage: $0 offline <traces_dir>}"
    if [ ! -d "$TRACES_DIR" ]; then
      echo "ERROR: Traces directory not found: $TRACES_DIR"
      exit 1
    fi
    echo "Running batch_analyse_offline on: $TRACES_DIR"
    echo "Output: $PIPELINE_DIR/data/system_arbis.csv"
    echo ""
    docker run --rm \
      -v "$TRACES_DIR:/data:ro" \
      detect-api batch_analyse_offline --datadir /data \
      > "$PIPELINE_DIR/data/system_arbis.regenerated.csv"
    ;;

  rpc)
    CONFIG="${2:?Usage: $0 rpc <config.json> <block_first> <block_last>}"
    FIRST="${3:?Usage: $0 rpc <config.json> <block_first> <block_last>}"
    LAST="${4:?Usage: $0 rpc <config.json> <block_first> <block_last>}"
    if [ ! -f "$CONFIG" ]; then
      echo "ERROR: Config file not found: $CONFIG"
      exit 1
    fi
    echo "Running batch_analyse via RPC"
    echo "  Config: $CONFIG"
    echo "  Range:  $FIRST - $LAST"
    echo "  Output: $PIPELINE_DIR/data/system_arbis.csv"
    echo ""
    echo "This will take several hours for the full 220K range."
    echo ""
    docker run --rm \
      -v "$CONFIG:/tmp/config.json:ro" \
      detect-api batch_analyse \
        --block-first "$FIRST" \
        --block-last "$LAST" \
        --manifest /tmp/manifest.txt \
        --config /tmp/config.json \
        --concurrency 10 \
        --errors /tmp/errors.txt \
      > "$PIPELINE_DIR/data/system_arbis.regenerated.csv"
    ;;

  *)
    echo "ERROR: Unknown mode '$MODE'. Use 'offline' or 'rpc'."
    exit 1
    ;;
esac

LINES=$(wc -l < "$PIPELINE_DIR/data/system_arbis.regenerated.csv")
echo ""
echo "Generated: $PIPELINE_DIR/data/system_arbis.csv"
echo "Lines: $LINES"
echo ""
echo ""
echo "To use this CSV in the pipeline, replace system_arbis.csv:"
echo "  mv data/system_arbis.regenerated.csv data/system_arbis.csv"
echo "Then: python3 script/run_all.py --from 0"
