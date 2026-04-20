#!/bin/bash
# ============================================
#  Artifact Dependency Installer
# ============================================
#
# Installs everything needed to verify the artifact:
#   1. Python packages (numpy, matplotlib, pandas)
#   2. Rocq (for proof verification)
#   3. Loads the detect-api Docker image
#
# Requirements:
#   - Python 3.9+
#   - opam (OCaml package manager)
#   - Docker
#
# Usage:
#   ./install.sh

set -e

ARTIFACT_DIR="$(cd "$(dirname "$0")" && pwd)"

echo "============================================"
echo "  Installing artifact dependencies"
echo "============================================"

# --- 1. Python dependencies ---
echo ""
echo "[1/4] Installing Python packages into .venv..."
if ! command -v python3 >/dev/null 2>&1; then
  echo "ERROR: python3 not found. Install Python 3.9+ first."
  exit 1
fi
VENV="$ARTIFACT_DIR/.venv"
if [ ! -d "$VENV" ]; then
  python3 -m venv "$VENV"
fi
"$VENV/bin/pip" install --quiet --upgrade pip
"$VENV/bin/pip" install --quiet -r "$ARTIFACT_DIR/requirements.txt"
echo "Python OK (venv at $VENV)."

# --- 2. Rocq ---
echo ""
echo "[2/4] Installing Rocq..."
if ! command -v opam >/dev/null 2>&1; then
  echo "ERROR: opam not found. Install from https://opam.ocaml.org/"
  exit 1
fi
if ! opam list --installed 2>/dev/null | grep -q "^rocq-core "; then
  opam install -y rocq-core
fi
if ! opam list --installed 2>/dev/null | grep -q "^rocq-stdlib "; then
  opam install -y rocq-stdlib
fi
echo "Rocq OK ($(opam exec -- rocq --version 2>/dev/null | head -1 || echo 'installed'))."

# --- 3. Docker image ---
echo ""
echo "[3/4] Loading detect-api Docker image..."
if ! command -v docker >/dev/null 2>&1; then
  echo "ERROR: docker not found. Install Docker Desktop."
  exit 1
fi
if ! docker image inspect detect-api >/dev/null 2>&1; then
  if [ -f "$ARTIFACT_DIR/detect-api.tar.gz" ]; then
    docker load -i "$ARTIFACT_DIR/detect-api.tar.gz"
  else
    echo "WARNING: detect-api.tar.gz not found. Some pipeline steps will be skipped."
  fi
fi
echo "Docker OK."

# --- 4. Extract data archives ---
echo ""
echo "[4/4] Extracting data archives..."
if [ -f "$ARTIFACT_DIR/blockdb.tar.gz" ] && [ ! -d "$ARTIFACT_DIR/blockdb" ]; then
  tar -xzf "$ARTIFACT_DIR/blockdb.tar.gz" -C "$ARTIFACT_DIR"
  echo "  blockdb/ extracted."
fi
if [ -f "$ARTIFACT_DIR/pipeline/data.tar.gz" ] && [ ! -d "$ARTIFACT_DIR/pipeline/data" ]; then
  tar -xzf "$ARTIFACT_DIR/pipeline/data.tar.gz" -C "$ARTIFACT_DIR/pipeline"
  echo "  pipeline/data/ extracted."
fi
echo "Data OK."

echo ""
echo "============================================"
echo "  Installation complete."
echo ""
echo "  Next steps:"
echo "    1. Activate venv:  source .venv/bin/activate"
echo "    2. Compile Rocq:   cd rocq && opam exec -- rocq compile Arbitrage.v"
echo "    3. Run pipeline:   cd pipeline && python3 script/run_all.py --offline --from 0"
echo "============================================"
