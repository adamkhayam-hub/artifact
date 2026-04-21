# Artifact: Protocol-Agnostic Arbitrage Detection with Decidable Structural Equivalence

## Overview

This artifact accompanies the paper "If It Walks Like an
Arbitrage: Protocol-Agnostic Detection with Decidable
Structural Equivalence." It enables verification of every
claim in the paper through four components:

1. **Rocq formalization** — machine-checked proofs of all
   five theorems
2. **Evaluation pipeline** — reproduces every number,
   figure, and table from the paper
3. **Detection tool** — a Docker image for inspecting
   arbitrary transactions, both offline and via RPC
4. **Pre-exported traces** — raw execution traces for
   offline verification without an archive node

## Requirements

Three system-level prerequisites. `install.sh` handles
Python packages, Rocq, and Docker image loading; you
only need to install the three underlying tools.

- **Docker** —
  [Install Docker Desktop](https://docs.docker.com/get-docker/)
- **opam** (OCaml package manager, for Rocq):
  ```bash
  bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
  opam init && eval $(opam env)
  ```
- **Python 3.9+** (with `pip`)
- **Graphviz** (optional, for DOT → PDF):
  ```bash
  brew install graphviz    # macOS
  apt install graphviz     # Ubuntu/Debian
  ```

## Quick start

Three commands to reproduce every claim in the paper:

```bash
# 1. Install artifact dependencies (~5 min, one-time)
#    Reassembles parts, loads detect-api, installs Python + Rocq
cd artifact && ./install.sh

# 2. Verify the 5 theorems (< 1 min)
#    Uses the sandboxed opam root at artifact/.opam
cd rocq && OPAMROOT="$PWD/../.opam" opam exec --switch=argos -- rocq compile Arbitrage.v

# 3. Reproduce the evaluation (5-30 min offline, hours online)
cd ../pipeline && python3 script/run_all.py --offline --from 0
```

To reset everything and start over: `./cleanup.sh`.

## Artifact layout (FYI)

The large payloads (Docker image, pre-exported traces, evaluation
CSVs) are shipped as <95 MB split parts so the repository fits within
standard git hosting limits. `install.sh` reassembles them; you do not
need to do anything manually.

- `detect-api_parts/` → `detect-api.tar.gz` (Docker image, kept for re-loads)
- `blockdb_parts/` → `blockdb.tar.gz` (pre-exported traces, deleted after extraction)
- `pipeline/data_parts/` → `pipeline/data.tar.gz` (CSVs, deleted after extraction)

### Sanity check after install

One-liner per component to confirm the install succeeded:

```bash
# Python
python3 -c "import numpy, matplotlib, pandas; print('Python OK')"

# Rocq
opam exec -- rocq --version

# Docker image
docker image inspect detect-api >/dev/null && echo "Docker OK"
```

### Inspect a single transaction

After install, try `tx_R` from the paper (a 3-arm
arbitrage through 6 pools that Eigenphi misses):

```bash
echo '["275f9642556a58802eafdd8289aa19a7275e9d40962056095bb9b5c51ac3d246"]' > /tmp/tx.json
echo '{"baseNode":"https://<YOUR_ARCHIVE_NODE>","baseBeacon":"","headers":[]}' > /tmp/config.json
mkdir -p /tmp/inspect_out
docker run \
  -v /tmp/tx.json:/tmp/tx.json:ro \
  -v /tmp/config.json:/tmp/config.json:ro \
  -v /tmp/inspect_out:/output \
  detect-api \
  inspect_tx --config /tmp/config.json --transaction /tmp/tx.json --outdir /output

# Verify
cat /tmp/inspect_out/275f9642*/arbitrage.json | python3 -c "import json,sys; d=json.load(sys.stdin); print('verdict:', d['resume']['arbitrage'])"
# Expected: verdict: arbitrage
```

No archive node? See the offline example in Section 3
(uses pre-exported traces from `blockdb/`, no network
needed).

---

## 1. Rocq Formalization

**Location:** `rocq/Arbitrage.v`

A single self-contained file (84 lemmas, 2,471 lines,
0 Admitted, 0 axioms) that mechanizes all five theorems
from the paper:

| Theorem | Rocq name | What it proves |
|---------|-----------|----------------|
| Thm 1 (Preservation) | `preservation` | No rewrite rule fabricates a transfer |
| Thm 2 (Termination) | `fixpoint_terminates` | Fixpoint converges in at most 3n-2 passes |
| Thm 3 (Soundness) | `soundness_full` | Arbitrage verdict implies Definition 5 |
| Thm 4 (Confluence) | `confluence` | Unique normal form |
| Thm 5 (Decidable equiv.) | `decidable_equivalence` | Word problem is decidable |

Each of the 15 rewriting rules from Table 1 is a named
constructor in the Rocq specification. The structural
predicates (`is_burn`, `is_mint`, `is_singleton_router`)
are abstract Parameters; all proofs proceed by case
analysis on the boolean value, making the formalization
valid for any EVM-compatible chain.

### How to verify

```bash
# Install Rocq if needed
opam install rocq-core

# Compile (takes ~30 seconds)
cd rocq
opam exec -- rocq compile Arbitrage.v
```

Expected output: no errors, no warnings. If the file
compiles, every theorem is machine-checked.

---

## 2. Evaluation Pipeline

**Location:** `pipeline/`

Reproduces every statistic, figure, and table from
Section 5 of the paper. The pipeline reads from
pre-computed CSV files and does not require network
access or an archive node.

### Requirements

- Python 3.9+
- Packages listed in `artifact/requirements.txt` (numpy, matplotlib, pandas):
  ```bash
  pip install -r ../requirements.txt
  ```

### How to run

```bash
cd pipeline

# Offline mode (uses pre-exported traces from blockdb/)
python3 script/run_all.py --offline --from 0

# Online mode (fetches traces from an archive node)
echo '{"baseNode":"https://<YOUR_NODE>","baseBeacon":"","headers":[]}' > /tmp/config.json
python3 script/run_all.py --online --config /tmp/config.json --from 0

# Auto-detect (uses blockdb/ if present, otherwise skips forensic steps)
python3 script/run_all.py --from 0
```

The pipeline has three modes for steps 19–20 and 24,
which run the detection tool on individual transactions:

- **`--offline`**: reads pre-exported traces from
  `blockdb/`. Samples only from available blocks.
- **`--online --config <path>`**: fetches traces via
  RPC from an archive node. Samples from the full
  220K range. Reproduces exact paper numbers.
- **Auto-detect** (no flag): uses `blockdb/` if
  present, otherwise skips forensic steps.

All other steps (0–18, 21–28) always run offline from
the pre-computed CSVs, regardless of the mode.

This executes 29 steps. Results appear in
`pipeline/output/`:
- `output/summaries/` — text summaries per step
- `output/figures/` — PDF figures
- `output/samples/` — sampled transactions for review
- `output/cat4_forensic/` — Category 4 forensic results
- `output/3way_gap/` — three-way gap analysis

### What each step produces

| Steps | What | Key output |
|-------|------|------------|
| 0 | Preprocess CSV | `output/data/system_compact.csv` |
| 1 | Exploration + fixpoint coverage | 98.7% fixpoint, 1.3% promotion |
| 2 | Accuracy (vs Eigenphi) | 83% overlap, 64,340 exclusive |
| 3 | Topology | 1,889,755 cycles, batching stats |
| 4 | Performance | P50=0.04ms algo, 0.19ms total |
| 5 | Attempted arbitrages | 437,409 (43%) |
| 6 | Bot concentration | Top-10 senders |
| 7-8 | Temporal + gas | Distribution plots |
| 9 | Figures | PDFs for the paper |
| 10-18 | Manual validation (see categories below) | 500 txs, zero false positives |
| 19-20 | Forensic analysis of baseline-exclusive txs | 63.5% at inner addresses, 8.5% baseline FP |
| 21-24 | ArbiNet three-way comparison | 81% overlap, gap analysis |
| 25-27 | Cross-chain | Arbitrum (50 confirmed), BSC (88 confirmed) |
| 28 | Master summary | All paper numbers in one file |

### Manual validation categories

The evaluation compares our system against Eigenphi
(a production MEV detection platform). The comparison
produces four categories of transactions:

- **Category 1 (Both confirmed)**: transactions that
  both our system and Eigenphi flag as arbitrage.
  These are high-confidence true positives. We sample
  100 and verify all are genuine arbitrages.

- **Category 2 (Ours-only confirmed)**: transactions
  our system flags as arbitrage but Eigenphi does not.
  These are our exclusive detections. We sample 100
  and verify all are genuine (63% involve flash loans,
  invisible to event-based detectors).

- **Category 3 (Ours-only warnings)**: transactions
  our system flags with a warning (structural cycle
  found but not confirmed as profitable). We sample
  100 and verify all contain real cyclic structures
  (76% are attempted arbitrages that lost money).

- **Category 4 (Eigenphi-only)**: transactions Eigenphi
  flags but our system does not classify. We sample 200
  and run our detection tool on each. The forensic
  analysis reveals that 63.5% contain cycles our
  fixpoint detects at inner contract addresses (not
  surfaced due to conservative classification scope),
  28% are cross-token routing (not arbitrages), and
  8.5% are Eigenphi false positives.

### Input data files

| File | Size | Description |
|------|------|-------------|
| `data/system_arbis.csv` | 8.7 GB | Full detection output for 220K blocks |
| `data/eigenphi_arbis_txs.csv` | 199 MB | Eigenphi labels (649,790 transactions) |
| `data/system_arbis_3wayeval.csv` | 28 MB | Detection output for the 1K ArbiNet range |
| `data/arbinet/arbinet1k.csv` | 134 KB | ArbiNet predictions on the same 1K range |
| `data/arbitrum_1k/summary.csv` | 3.4 MB | Arbitrum cross-chain results |
| `data/bsc_1k/summary.csv` | 5.6 MB | BSC cross-chain results |

### Regenerating the evaluation CSV (optional)

The provided `data/system_arbis.csv` was generated by
running our detection tool on 220K Ethereum blocks.
`generate_csv.sh` lets you reproduce it from scratch.
Output is written to `data/system_arbis.regenerated.csv`
so the provided file is never overwritten.

**Option A — Partial regeneration from pre-exported
traces (minutes, no network):**

```bash
cd pipeline
./generate_csv.sh offline ../blockdb/220k
# Output: data/system_arbis.regenerated.csv (1K blocks)
```

**Option B — Partial regeneration via RPC
(5-10 min, needs an archive node):**

```bash
./generate_csv.sh rpc /path/to/config.json 23699751 23699850
# Output: data/system_arbis.regenerated.csv (100 blocks)
```

**Option C — Full 220K regeneration via RPC
(6-12 hours, needs an archive node):**

```bash
./generate_csv.sh rpc /path/to/config.json 23699751 23919750
# Output: data/system_arbis.regenerated.csv (~8.7 GB)
```

To swap the regenerated CSV into the pipeline:

```bash
mv data/system_arbis.regenerated.csv data/system_arbis.csv
python3 script/run_all.py --from 0
```

### Offline vs RPC mode

Steps 19-20 (Cat4 forensic) and step 24 (gap analysis)
need to run the detection tool on individual transactions.
The pipeline automatically detects the mode:

- **Offline** (default): if `blockdb/` exists, the pipeline
  samples only transactions from available blocks and runs
  `inspect_tx_offline` via the Docker image
- **RPC**: if `inspect_tx_offline` is in the system PATH,
  the pipeline calls it directly; otherwise it uses
  `docker run detect-api inspect_tx_offline`

In offline mode with 1K blocks, the sample size for the
forensic analysis (steps 19-20, 24) is smaller because
only transactions from available blocks are sampled.
The core evaluation numbers (steps 0-9: overlap rates,
tier breakdown, topology, performance, attempted
arbitrages) are computed from the full 220K-block CSV
and reproduce the paper's numbers exactly. The
forensic percentages (63.5%, 8.5%, 37.7%) may differ
slightly in the offline sample, but the methodology
and the conclusions are identical.

---

## 3. Detection Tool (Docker)

**Location:** `detect-api_parts/` (reassembled into `detect-api.tar.gz`
and loaded by `install.sh`).

A Docker image containing five compiled binaries for
arbitrage detection. No source code, no build tools,
no API keys. The image includes a Postgres instance
with 2.6M event signatures for trace decoding.

### Load the image (manual)

`install.sh` does this for you. To reload manually:

```bash
cat detect-api_parts/detect-api.tar.gz.part-* > detect-api.tar.gz
docker load -i detect-api.tar.gz
```

### Available binaries

| Binary | Mode | Purpose |
|--------|------|---------|
| `inspect_tx` | RPC | Analyse a single transaction via an archive node |
| `inspect_tx_offline` | Offline | Analyse a single transaction from pre-exported JSON |
| `batch_analyse` | RPC | Analyse a block range, produce CSV |
| `batch_analyse_offline` | Offline | Produce CSV from pre-exported traces |
| `export_data` | RPC | Export raw traces for offline use |

### Example 1: Inspect a transaction via RPC

This analyses tx\_R from the paper (Section 3,
Figure 3), a three-arm arbitrage through six pools
that Eigenphi does not flag.

```bash
# Transaction hash (without 0x prefix)
echo '["275f9642556a58802eafdd8289aa19a7275e9d40962056095bb9b5c51ac3d246"]' > /tmp/tx.json

# RPC config (replace with your archive node URL)
echo '{"baseNode":"https://<YOUR_ARCHIVE_NODE>","baseBeacon":"","headers":[]}' > /tmp/config.json

# Run
mkdir -p output
docker run \
  -v /tmp/tx.json:/tmp/tx.json:ro \
  -v /tmp/config.json:/tmp/config.json:ro \
  -v $(pwd)/output:/output \
  detect-api \
  inspect_tx --config /tmp/config.json --transaction /tmp/tx.json --outdir /output

# View results
cat output/275f9642*/arbitrage.json | python3 -m json.tool | head -20
```

Expected: `"arbitrage": "arbitrage"` with positive
final balance (~0.0023 WETH profit).

### Example 2: Inspect a transaction offline

Using pre-exported traces from `blockdb/`. Pick any
transaction from the available blocks:

```bash
# Find a transaction
BLOCK=$(ls blockdb/220k/ | head -1)
TX=$(ls blockdb/220k/$BLOCK/*.trace.json | head -1 | xargs basename | sed 's/.trace.json//')
echo "Block: $BLOCK, TX: $TX"

# Run offline
mkdir -p output
docker run \
  -v $(pwd)/blockdb:/blockdb:ro \
  -v $(pwd)/output:/output \
  detect-api \
  inspect_tx_offline \
    --trace /blockdb/220k/$BLOCK/$TX.trace.json \
    --cft-input /blockdb/220k/$BLOCK/$TX.cft_input.json \
    --outdir /output

# View results
ls output/$TX/
```

Output directory contains:
- `0.dot` through `N.dot` — the AST at each
  transformation stage
- `arbitrage.json` — verdict with transfer chains,
  cycles, profit, and diagnostic reasons
- `trace.json` — the decoded execution trace

### Example 3: Batch analysis via RPC

Analyse two blocks and produce a CSV:

```bash
echo '{"baseNode":"https://<YOUR_ARCHIVE_NODE>","baseBeacon":"","headers":[]}' > /tmp/config.json

docker run \
  -v /tmp/config.json:/tmp/config.json:ro \
  detect-api \
  batch_analyse \
    --block-first 24100000 \
    --block-last 24100001 \
    --manifest /tmp/manifest.txt \
    --config /tmp/config.json \
    --concurrency 5 \
    --errors /tmp/errors.txt \
  > results.csv

wc -l results.csv
head -2 results.csv
```

The CSV has the same format as `system_arbis.csv`:
`transaction_id, block_number, tag, tag_data_id,
tag_log_index, decode_time_ms, algo_time_ms, tag_data`.

### Example 4: Batch analysis offline

Reproduce verdicts from pre-exported traces:

```bash
docker run \
  -v $(pwd)/blockdb/220k:/data:ro \
  detect-api \
  batch_analyse_offline --datadir /data \
  > offline_results.csv

wc -l offline_results.csv
```

### Example 5: Cross-chain (Arbitrum)

The same binary, same algorithm. Only the RPC URL and
the wrapped-token address change:

```bash
echo '["<arbitrum_tx_hash>"]' > /tmp/tx.json
echo '{"baseNode":"https://<ARBITRUM_RPC>","baseBeacon":"","headers":[]}' > /tmp/config.json

docker run \
  -e WETH_ADDRESS=82aF49447D8a07e3bd95BD0d56f35241523fBab1 \
  -v /tmp/tx.json:/tmp/tx.json:ro \
  -v /tmp/config.json:/tmp/config.json:ro \
  -v $(pwd)/output:/output \
  detect-api \
  inspect_tx --config /tmp/config.json --transaction /tmp/tx.json --outdir /output
```

Supported chains (set WETH\_ADDRESS accordingly):

| Chain | WETH_ADDRESS | Notes |
|-------|-------------|-------|
| Ethereum | `c02aaa39b223fe8d0a0e5c4f27ead9083c756cc2` | Default, no env var needed |
| Arbitrum | `82aF49447D8a07e3bd95BD0d56f35241523fBab1` | L2, same trace format |
| BSC | `bb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c` | Independent L1 |
| Optimism | `4200000000000000000000000000000000000006` | L2 |
| Base | `4200000000000000000000000000000000000006` | L2 |

---

## 4. Pre-exported Traces

**Location:** `blockdb_parts/` (extracted to `blockdb/` by `install.sh`).

Raw execution traces and fee metadata for offline
verification. Two block ranges are provided:

| Directory | Block range | Blocks | Purpose |
|-----------|-------------|--------|---------|
| `blockdb/220k/` | 23,699,751 – 23,700,750 | 1,000 | Subset of the 220K main evaluation |
| `blockdb/3way/` | 24,100,000 – 24,100,999 | 1,000 | Full ArbiNet three-way comparison range |

Each block directory contains pairs of files per
transaction:
- `<tx_hash>.trace.json` — raw execution trace
  (as returned by `debug_traceTransaction`)
- `<tx_hash>.cft_input.json` — block metadata
  (builder address, base fee, gas used)

### Why only 1K blocks?

The full 220K-block trace dataset exceeds 500 GB, which
is impractical for artifact hosting. The complete
evaluation CSV (`system_arbis.csv`, 8.7 GB) contains
verdicts for all 1M+ flagged transactions and is
sufficient to reproduce every paper statistic. The 1K
trace samples enable hands-on verification of individual
verdicts.

To reproduce the full trace dataset, use `export_data`:

```bash
echo '{"baseNode":"https://<YOUR_NODE>","baseBeacon":"","headers":[]}' > /tmp/config.json

docker run \
  -v /tmp/config.json:/tmp/config.json:ro \
  -v $(pwd)/exported:/export \
  detect-api \
  export_data \
    --block-first 23699751 \
    --block-last 23700750 \
    --manifest /export/manifest.txt \
    --config /tmp/config.json \
    --outdir /export/data \
    --concurrency 10 \
    --errors /export/errors.txt
```

---

## 5. Reading the DOT Visualizations

The detection tool exports the AST at each transformation
stage as a numbered DOT file. The sequence tells the story
of how the algorithm transforms a raw execution trace into
arbitrage cycles.

### File sequence

- `0.dot` — initial AST after construction and trimming.
  Shows the raw call hierarchy with individual transfers
  as leaf nodes.
- `1.dot` through `N-3.dot` — intermediate stages. Leaf
  manipulation (chaining adjacent transfers, lifting
  reduced subtrees) and node manipulation (merging
  parallel paths, connecting cycles).
- `N-2.dot` — AST after annotation. Closed chains are
  labeled as arbitrage (yellow) or cycle (pink).
- `N-1.dot` — AST after cycle connection. Complementary
  chains at the same level are merged.
- `N.dot` (last) — final reduced form after the fixpoint
  converges. This is the canonical form from which the
  verdict is derived.

### Node types

| Shape | Border | Meaning |
|-------|--------|---------|
| Rectangle | Single | Individual transfer (leaf) |
| Circle | Single | Call frame (contract invocation) |
| Octagon | Double | Transfer chain or cycle (result of rewriting) |

### Edge types

| Style | Meaning |
|-------|---------|
| Solid | Parent-child in the call hierarchy |
| Dotted | Internal structure of a chain (sub-transfers) |

### Colors

**Chain/cycle nodes (double-border octagon):**

| Color | Meaning | Rule |
|-------|---------|------|
| Yellow | Arbitrage cycle: closed, matching tokens, profitable | R13 |
| Pink | Cycle: closed, but sender is intermediary | R14 |
| Green | Merged chains: parallel paths combined | R7/R8 |
| Beige | Transfer chain: sequential transfers chained | R1/R6/R9 |
| Orange | Token mint: deposit or wrap | R3 |
| Purple | Token burn: withdrawal or unwrap | R2 |

**Transfer nodes (rectangle):**

| Color | Meaning |
|-------|---------|
| Light green | ERC-20 Transfer |
| Light purple | Burn (transfer to null address) |
| Light orange | Mint (transfer from null address) |
| White | Native ETH transfer |
| Grey | NFT transfer |

### Node labels

Transfer nodes display:
```
from: <source address or known name>
to: <destination address or known name>
sender: <σ, the CALL frame initiator>
origin: <transaction sender (EOA)>
amount: <value and token symbol>
desc: <Transfer | Mint | Burn | Withdrawal | Deposit | NativeTransfer>
contract: <ERC-20 | ERC-721 | ERC-1155 | Unknown>
```

Chain nodes display:
```
from: <chain origin>
middleman: <intermediary addresses>
to: <chain destination>
1st transfer: <entry amount and token>
amount0: <entry-side token amounts>
amount1: <exit-side token amounts>
strategy: <chaining | merging>
new_balance: <delta map per address>
```

### How to convert

```bash
# Single file
dot -Tpdf 0.dot -o 0.pdf

# All files in a transaction directory
for f in *.dot; do dot -Tpdf "$f" -o "${f%.dot}.pdf"; done
```

### Interpreting the final DOT

Open the last DOT file. If the transaction is an
arbitrage:
- At least one **yellow** node (arbitrage cycle) is
  present
- The delta map inside shows positive balance for
  the cycle origin
- The `arbitrage.json` file confirms with
  `"arbitrage": "arbitrage"`

If the transaction is a warning:
- **Pink** nodes indicate structural cycles that
  are not confirmed (negative profit, mixed balance,
  or sender traverses the path)
- The `arbitrage.json` has `"arbitrage": "warning"`
  with diagnostic reasons explaining why

If no yellow or pink nodes are present, the algorithm
found no cyclic structure (`"arbitrage": null`).

---

## Verification Summary

| Paper claim | How to verify | Expected result |
|-------------|---------------|-----------------|
| Five formal properties | `rocq compile Arbitrage.v` | Compiles with 0 errors |
| 457,841 confirmed arbitrages | Pipeline step 1 | `explore.txt`: confirmed = 457,841 |
| 83% Eigenphi overlap | Pipeline step 2 | `accuracy.txt`: 539,675 / 649,790 |
| 81% ArbiNet overlap | Pipeline step 22 | `comparison.txt`: 81% coverage |
| No FP in confirmed tier | Pipeline step 18 | `manual_review_summary.txt`: 0 FP in Cat 1 + Cat 2 |
| 64,340 exclusive confirmed | Pipeline step 2 | `accuracy.txt`: 64,340 exclusive |
| 437,409 attempted arbitrages | Pipeline step 5 | `attempted.txt`: 43.0% |
| 98.7% fixpoint coverage | Pipeline step 1 | `explore.txt`: 98.7% fixpoint |
| Three-chain portability | Cross-chain Docker commands | Same binary, different chains |
| Any individual transaction | `inspect_tx` or `inspect_tx_offline` | Verdict + DOTs + profit |

---

## Expected runtimes

| Step | Mode | Duration | Output size |
|------|------|----------|-------------|
| `install.sh` | — | ~5 min (first time) | — |
| `rocq compile Arbitrage.v` | — | ~30 s | `Arbitrage.vo` (~240 KB) |
| Pipeline steps 0-9 | offline | 5-10 min | `output/summaries/`, `output/figures/` |
| Pipeline full (29 steps) | offline | 15-30 min | Complete `output/` tree |
| Pipeline full (29 steps) | online | 1-3 hours | Same + accurate Cat 4 sample |
| `inspect_tx` single tx | RPC | 2-10 s per tx | DOT files + `arbitrage.json` |
| `generate_csv.sh` 1K blocks | offline | 1-3 min | ~30 MB CSV |
| `generate_csv.sh` 220K blocks | online | 6-12 hours | ~8.7 GB CSV |

---

## Troubleshooting

**`./install.sh: permission denied`**
```bash
chmod +x install.sh && ./install.sh
```

**`rocq: command not found` after install**

The install put Rocq inside an opam switch; use
`opam exec` to get the right PATH:
```bash
opam exec -- rocq compile Arbitrage.v
```

**`ModuleNotFoundError: No module named 'pandas'`**

Python packages didn't install into the Python that's
running. Reinstall with the same interpreter:
```bash
python3 -m pip install -r requirements.txt
```

**`docker: permission denied`** (Linux)
```bash
sudo usermod -aG docker $USER  # then log out and back in
```

**Pipeline step 0 fails with `ERROR: data/system_arbis.csv not found`**

The CSV is part of the artifact release (~8.7 GB) and
should be in `pipeline/data/`. If missing, regenerate
via `generate_csv.sh` (see Section 2, Regenerating the
evaluation CSV).

**Pipeline skips steps 19, 20, 24**

Those steps need transaction traces (RPC or blockdb).
Options:
- Add `--offline` to use `blockdb/` (1K-block sample,
  smaller forensic numbers)
- Add `--online --config cfg.json` to use an archive
  node (full 220K sample, matches paper exactly)

**`inspect_tx` returns `End_of_file` / `HTTPS error`**

Archive node URL is unreachable, or doesn't support
`debug_traceTransaction`. Verify the endpoint:
```bash
curl -X POST -H "Content-Type: application/json" \
  --data '{"jsonrpc":"2.0","method":"eth_blockNumber","params":[],"id":1}' \
  https://<YOUR_NODE>
```

**DOT files don't render**

Install Graphviz:
```bash
brew install graphviz        # macOS
apt install graphviz         # Ubuntu/Debian
```
