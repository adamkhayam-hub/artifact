#!/bin/bash
# ============================================
#  Artifact Cleanup
# ============================================
#
# Removes everything install.sh produced, leaving only
# source files and the *_parts/ archives.
#
# Usage:
#   ./cleanup.sh

set -e

ARTIFACT_DIR="$(cd "$(dirname "$0")" && pwd)"

echo "============================================"
echo "  Cleaning artifact outputs"
echo "============================================"

rm -rf "$ARTIFACT_DIR/.venv"
echo "  .venv removed."

rm -rf "$ARTIFACT_DIR/.opam"
echo "  .opam (local opam root with Rocq) removed."

rm -rf "$ARTIFACT_DIR/blockdb"
rm -f  "$ARTIFACT_DIR/blockdb.tar.gz"
echo "  blockdb/ and blockdb.tar.gz removed."

rm -rf "$ARTIFACT_DIR/pipeline/data"
rm -f  "$ARTIFACT_DIR/pipeline/data.tar.gz"
echo "  pipeline/data/ and pipeline/data.tar.gz removed."

rm -rf "$ARTIFACT_DIR/pipeline/output"
echo "  pipeline/output/ removed."

rm -f "$ARTIFACT_DIR/detect-api.tar.gz"
echo "  detect-api.tar.gz removed."

if command -v docker >/dev/null 2>&1; then
  if docker image inspect detect-api >/dev/null 2>&1; then
    docker rmi detect-api >/dev/null 2>&1 || true
    echo "  detect-api Docker image removed."
  fi
fi

rm -rf "$ARTIFACT_DIR/rocq/.lia.cache" \
       "$ARTIFACT_DIR"/rocq/.*.aux \
       "$ARTIFACT_DIR"/rocq/*.glob \
       "$ARTIFACT_DIR"/rocq/*.vo \
       "$ARTIFACT_DIR"/rocq/*.vok \
       "$ARTIFACT_DIR"/rocq/*.vos 2>/dev/null || true
echo "  Rocq build artefacts removed."

echo ""
echo "============================================"
echo "  Cleanup complete. Run ./install.sh to rebuild."
echo "============================================"
