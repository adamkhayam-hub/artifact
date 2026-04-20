# Evaluation Pipeline

Reproduces every statistic, figure, and table from the
paper's evaluation section (Section 5). The pipeline
reads from pre-computed CSV data files and generates
all results in the `output/` directory.

## Requirements

- Python 3.9+
- Python packages (numpy, matplotlib, pandas):
  ```bash
  pip install -r ../requirements.txt
  ```
- Docker with the `detect-api` image loaded (only for
  steps 19-20 and 24, which run the detection tool on
  individual transactions). See the top-level
  `artifact/install.sh` for one-command setup.

## Quick start

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

This runs all 29 steps sequentially. Each step prints
its progress and writes results to `output/`. The full
pipeline takes 5-30 minutes depending on your machine.

To run a specific step or range:

```bash
# Run only step 2 (accuracy)
python3 script/run_all.py --from 2 --to 2

# Resume from step 10
python3 script/run_all.py --from 10
```

## Execution modes

Most of the pipeline (steps 0–18, 21–28) runs entirely
offline from the pre-computed CSVs. These steps always
reproduce the paper's exact numbers regardless of mode.

Steps 19–20 (Category 4 forensic) and step 24 (gap
analysis) are different: they need to run the detection
tool on individual transactions that the baselines flag
but our system does not classify. This is where the mode
matters.

### Offline mode (`--offline`)

```bash
python3 script/run_all.py --offline --from 0
```

Uses pre-exported traces from `blockdb/`. The sampling
step (step 10) automatically restricts to transactions
whose blocks are available in `blockdb/`. This means:

- Steps 0–9: **exact paper numbers** (read from full CSV)
- Steps 10–18: samples are drawn only from available
  blocks (fewer candidates, but methodology is identical)
- Steps 19–20: runs `inspect_tx_offline` via Docker on
  each sampled Category 4 transaction. No network needed.
- Step 24: runs `inspect_tx_offline` via Docker on gap
  transactions. The `blockdb/3way/` directory must
  contain the traces for this range.

The forensic percentages (63.5% at inner addresses,
8.5% baseline false positives) may differ slightly
because the sample is drawn from fewer blocks. The
methodology and the analysis logic are identical to
the paper.

### Online mode (`--online --config <path>`)

```bash
echo '{"baseNode":"https://<YOUR_NODE>","baseBeacon":"","headers":[]}' > /tmp/config.json
python3 script/run_all.py --online --config /tmp/config.json --from 0
```

Uses an archive node with `debug_traceTransaction` to
fetch traces on-demand. The sampling step draws from the
full 220K range with no restrictions. This reproduces the
paper's exact methodology including the forensic steps.

Requirements:
- The Docker image `detect-api` must be loaded
  (`docker load -i detect-api.tar.gz`)
- The config file must point to an archive node that
  supports `debug_traceTransaction`
- Steps 19–20 run `inspect_tx` (RPC mode) on up to 200
  transactions (each taking a few seconds)
- Step 24 runs `inspect_tx` on 468 gap transactions

This mode takes longer (network latency per transaction)
but produces the exact same numbers as the paper.

### Auto-detect mode (no flag)

```bash
python3 script/run_all.py --from 0
```

If `blockdb/` exists and contains data, behaves like
`--offline`. Otherwise, skips steps 19–20 and 24
entirely. All other steps still run and produce the
core evaluation numbers (overlap rates, tier breakdown,
topology, performance, attempted arbitrages, cross-chain).

This is the safest mode for a quick first run.

## Directory structure

```
pipeline/
  data/                        Input data (provided, do not modify)
    system_arbis.csv             Detection output for 220K blocks (8.7 GB)
    eigenphi_arbis_txs.csv       Eigenphi baseline labels (649,790 txs)
    system_arbis_3wayeval.csv    Detection output for 1K ArbiNet blocks
    arbinet/
      arbinet1k.csv              ArbiNet predictions on the same 1K blocks
    arbitrum_1k/
      summary.csv                Arbitrum cross-chain results (1K blocks)
    bsc_1k/
      summary.csv                BSC cross-chain results (1K blocks)

  script/                      Evaluation scripts (25 Python scripts)
    config.py                    Shared paths, constants, helper functions
    run_all.py                   Orchestrator (steps 0-28)
    00_preprocess.py             CSV extraction and range filtering
    01_statistics/               Exploration, accuracy, topology, performance,
                                 attempted, bots, temporal, gas
    02_figures/                  PDF figure generation
    03_manual_review/            Sampling, inspection, verdict resolution
    04_cat4/                     Forensic analysis of baseline-exclusive txs
    05_arbinet/                  ArbiNet three-way comparison and gap analysis
    06_crosschain/               Arbitrum and BSC cross-chain comparison
    99_master_summary.py         Consolidated summary of all numbers

  output/                      Generated results (empty before first run)
    data/                        Preprocessed compact CSV, filtered baselines
    summaries/                   Text summary per step (one .txt per step)
    figures/                     PDF figures
    samples/                     Sampled transactions for manual validation
    cat4_forensic/               Forensic results (DOTs, verdicts per tx)
    3way_gap/                    Three-way gap analysis results

  run.sh                       Shell wrapper for the pipeline
  generate_csv.sh              Regenerate the evaluation CSV from exported traces or RPC
```

## What each step does

### Step 0: Preprocessing

Reads the full detection CSV (`system_arbis.csv`, 8.7 GB)
in a single pass and produces:
- `output/data/system_compact.csv` — one row per flagged
  transaction with verdict, reasons, cycle count, and
  timing (used by all subsequent steps)
- `output/data/system_hashes.txt` — list of detected
  transaction hashes
- `output/data/eigenphi_arbis_txs_filtered.csv` — Eigenphi
  labels filtered to the same block range

### Steps 1-8: Statistics

Each step reads the compact CSV and produces a text
summary in `output/summaries/01_statistics/`.

| Step | Script | What it computes |
|------|--------|-----------------|
| 1 | `explore.py` | Total flagged (1,016,649), confirmed (457,841), fixpoint coverage (98.7%) |
| 2 | `accuracy.py` | Eigenphi overlap (83%), exclusive detections (64,340), tier breakdown |
| 3 | `topology.py` | Cycle count (1,889,755), batching rates, cycle lengths |
| 4 | `performance.py` | Algorithm latency (P50=0.04ms, P95=0.26ms) |
| 5 | `attempted.py` | Attempted arbitrages (437,409, 43%), per-block ratio |
| 6 | `bots.py` | Bot concentration (top-10 senders) |
| 7 | `temporal.py` | Temporal distribution across blocks |
| 8 | `gas.py` | Gas efficiency analysis |

### Step 9: Figures

Generates PDF figures in `output/figures/`:
- Confidence tier breakdown
- Attempted arbitrage ratio distribution
- Topology and cycle length histograms

### Steps 10-18: Manual validation

These steps implement the manual validation methodology:

| Step | Script | What it does |
|------|--------|-------------|
| 10 | `sample.py` | Sample 100 transactions from each of 4 categories (see below) |
| 11 | `inspect_all.py` | Extract transfer details for each sample |
| 12 | `resolve.py` | Resolve contract addresses via Blockscout |
| 13 | `auto_verdict.py` | Generate automatic preliminary verdicts |
| 14 | `write_verdicts.py` | Write verdict templates |
| 15 | `detailed.py` | Detailed structural review |
| 16 | `final.py` | Final verdict assignment |
| 17 | `reasoned.py` | Reasoned verdict with justification |
| 18 | `review.py` | Full manual review summary (500 txs, 0 FP in confirmed tier) |

**The four categories** (compared against Eigenphi):

1. **Both confirmed** (100 txs): transactions that both
   systems flag as arbitrage. Sanity check: are these
   real? Result: 100% genuine, 7% with flash loans.

2. **Ours-only confirmed** (100 txs): transactions only
   our system detects. Why does Eigenphi miss them?
   Result: 100% genuine, 63% involve flash loans that
   event-based detectors cannot see.

3. **Ours-only warnings** (100 txs): transactions our
   system flags with a warning but does not confirm.
   Are these noise? Result: 100% contain real cyclic
   structures (76% attempted with negative profit,
   14% mixed balance, 10% incomplete chains).

4. **Eigenphi-only** (200 txs): transactions Eigenphi
   flags but our system does not classify. What are
   we missing? Result: 63.5% contain cycles at inner
   addresses (our fixpoint detects them but the
   classification does not surface them), 28% are
   cross-token routing (not arbitrages), 8.5% are
   Eigenphi false positives.

In offline mode, step 10 automatically samples only
from transactions whose blocks are in `blockdb/`.
In online mode, it samples from the full range.

### Steps 19-20: Forensic analysis

These steps run the detection tool on Category 4
(Eigenphi-only) transactions to produce the forensic
breakdown:

| Step | Script | What it does |
|------|--------|-------------|
| 19 | `forensic.py` | Run `inspect_tx_offline` on each sampled tx, classify result |
| 20 | `to_gap.py` | Analyse the to\_ gap (cycles at inner addresses) |

In offline mode, the scripts use `inspect_tx_offline`
via Docker with `blockdb/` mounted. In online mode,
they use `inspect_tx` via Docker with the RPC config.

### Steps 21-24: ArbiNet comparison

| Step | Script | What it does |
|------|--------|-------------|
| 21 | `parse.py` | Parse raw ArbiNet output |
| 22 | `comparison.py` | Three-way comparison table (Ours × ArbiNet × Eigenphi) |
| 23 | `degradation.py` | Temporal degradation analysis |
| 24 | `gap.py` | Run detection on 468 gap transactions, check for cycles |

Step 24 follows the same pattern as step 19: it runs
the detection tool on transactions that baselines
flag but our system does not, and checks whether the
fixpoint detects cycles at inner addresses. The mode
(offline or online) is inherited from the pipeline flags.

### Steps 25-27: Cross-chain

| Step | Script | What it does |
|------|--------|-------------|
| 25 | `arbitrum.py` | Arbitrum summary (50 confirmed, 952 warnings) |
| 26 | `bsc.py` | BSC summary (88 confirmed, 922 warnings) |
| 27 | `comparison.py` | Side-by-side comparison across three chains |

These steps read from the pre-computed cross-chain
summary CSVs. No RPC access needed.

### Step 28: Master summary

Consolidates all numbers into a single file
(`output/summaries/99_master_summary.txt`) that
lists every key metric from the paper.

## Output files

After a full run, `output/` contains:

```
output/
  data/
    system_compact.csv           Compact per-transaction verdicts
    system_hashes.txt            All detected transaction hashes
    eigenphi_arbis_txs_filtered.csv   Eigenphi labels (filtered to range)
  summaries/
    01_statistics/
      explore.txt                Total counts, fixpoint coverage
      accuracy.txt               Overlap rates, exclusive detections
      topology.txt               Cycle counts, batching
      performance.txt            Latency percentiles
      attempted.txt              Attempted arbitrage analysis
      bots.txt                   Bot concentration
      temporal.txt               Temporal distribution
      gas.txt                    Gas efficiency
    02_figures/                  (empty, figures go to figures/)
    04_cat4/
      forensic.txt               Category 4 forensic breakdown
      to_gap.txt                 To_ gap analysis
    05_arbinet/
      comparison.txt             Three-way comparison
      degradation.txt            Temporal degradation
      gap.txt                    Gap analysis (468 txs)
    06_crosschain/
      arbitrum.txt               Arbitrum results
      bsc.txt                    BSC results
      comparison.txt             Cross-chain comparison
    99_master_summary.txt        All paper numbers
  figures/
    fig_confidence_tiers.pdf     Tier breakdown
    fig_attempted_ratio.pdf      Per-block attempted ratio
    ...
  samples/
    05_manual_sample_cat1_both_confirmed.csv
    05_manual_sample_cat2_system_only_confirmed.csv
    05_manual_sample_cat3_system_only_warnings.csv
    05_manual_sample_cat4_eigenphi_only.csv
  cat4_forensic/
    <tx_hash>/
      arbitrage.json             Detection verdict
      0.dot ... N.dot            AST transformation stages
  3way_gap/
    <tx_hash>/
      arbitrage.json
      0.dot ... N.dot

```

## Reproducing system_arbis.csv from scratch

The provided `data/system_arbis.csv` (8.7 GB) contains
the detection output for 220,000 blocks.
`generate_csv.sh` writes the regenerated CSV to
`data/system_arbis.regenerated.csv` so the provided
file is never overwritten.

### From pre-exported traces (offline)

```bash
# 1K-block sample (provided in blockdb/220k)
./generate_csv.sh offline ../blockdb/220k
```

This runs `batch_analyse_offline` on every trace in the
directory and produces the CSV.

### From an archive node (RPC)

```bash
# Create a config file with your archive node URL
echo '{"baseNode":"https://<YOUR_NODE>","baseBeacon":"","headers":[]}' > /tmp/config.json

# Small test range (a few minutes)
./generate_csv.sh rpc /tmp/config.json 23699751 23699850

# Full 220K evaluation range (takes 6-12 hours)
./generate_csv.sh rpc /tmp/config.json 23699751 23919750
```

This fetches execution traces via `debug_traceTransaction`
for each block, decodes them, runs the detection algorithm,
and outputs one CSV line per flagged transaction.

To swap the regenerated CSV into the pipeline:

```bash
mv data/system_arbis.regenerated.csv data/system_arbis.csv
python3 script/run_all.py --from 0
```

## Verifying paper numbers

After running the pipeline, check the key numbers:

```bash
# Total flagged transactions
grep "Total flagged" output/summaries/01_statistics/explore.txt

# Eigenphi overlap
grep "overlap" output/summaries/01_statistics/accuracy.txt

# Exclusive confirmed
grep "exclusive" output/summaries/01_statistics/accuracy.txt

# Attempted arbitrages
grep "attempted" output/summaries/01_statistics/attempted.txt

# False positives
grep "false positive" output/summaries/01_statistics/accuracy.txt

# All numbers at once
cat output/summaries/99_master_summary.txt
```
