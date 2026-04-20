#!/bin/bash
set -e

PIPELINE_DIR="$(cd "$(dirname "$0")" && pwd)"

echo "============================================"
echo "  Evaluation Pipeline"
echo "============================================"
echo ""

# Check inputs exist
if [ ! -d "$PIPELINE_DIR/data" ]; then
    echo "ERROR: data/ directory not found."
    echo "Place the following files in pipeline/data/:"
    echo "  system_arbis.csv              (or use batch_analyse_offline to generate)"
    echo "  eigenphi_arbis_txs.csv       (Eigenphi baseline)"
    echo "  system_arbis_3wayeval.csv     (3-way comparison, optional)"
    echo "  arbinet/arbinet1k.csv        (ArbiNet results, optional)"
    exit 1
fi

# Step 0: Preprocess
echo "=== Step 0: Preprocess ==="
python3 "$PIPELINE_DIR/script/00_preprocess.py"

# Steps 1+: Run the full pipeline
echo "=== Running evaluation pipeline ==="
python3 "$PIPELINE_DIR/script/run_all.py" --from 1

echo ""
echo "============================================"
echo "  Pipeline complete."
echo "  Results in: $PIPELINE_DIR/output/"
echo "============================================"
