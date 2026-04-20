"""
16_generate_forensic_reports.py — Generate forensic.md for each cat4 tx.

Reads: data/cat4_forensic/<tx_hash>/arbitrage.json + trace.json
Writes: data/cat4_forensic/<tx_hash>/forensic.md

Follows the Appendix B structure from the paper.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


import csv
import json
import re
import sys
from pathlib import Path
from collections import Counter, defaultdict

csv.field_size_limit(sys.maxsize)

EVAL_DIR = Path(__file__).resolve().parent.parent.parent
FORENSIC_DIR = EVAL_DIR / "data" / "cat4_forensic"

# Well-known addresses
KNOWN_TOKENS = {
    "0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2": "WETH",
    "0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48": "USDC",
    "0xdac17f958d2ee523a2206206994597c13d831ec7": "USDT",
    "0x6b175474e89094c44da98b954eedeac495271d0f": "DAI",
    "0x2260fac5e5542a773aa44fbcfedf7c193bc2c599": "WBTC",
    "0x7fc66500c84a76ad7e9c93437bfc5ac33e2ddae9": "AAVE",
    "0x1f573d6fb3f13d689ff844b4ce37794d79a7ff1c": "BNT",
    "0x0000000000000000000000000000000000000000": "ETH (null)",
    "0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee": "ETH (burn)",
}

KNOWN_CONTRACTS = {
    "0xba12222222228d8ba445958a75a0704d566bf2c8": "Balancer Vault",
    "0x000000000004444c5dc75cb358380d2e3de08a90": "Uniswap V4",
}


def sym_from_json(raw_json, addr):
    """Try to find symbol for an address in the raw JSON."""
    addr_lower = addr.lower()
    if addr_lower in KNOWN_TOKENS:
        return KNOWN_TOKENS[addr_lower]
    if addr_lower in KNOWN_CONTRACTS:
        return KNOWN_CONTRACTS[addr_lower]
    # Search in JSON for symbol near this address
    pattern = rf'"address"\s*:\s*"{re.escape(addr_lower)}".*?"symbol"\s*:\s*"([^"]+)"'
    m = re.search(pattern, raw_json, re.DOTALL)
    if m:
        return m.group(1)
    return addr[:10] + "..."


def extract_addr(v):
    """Extract address string from nested JSON value."""
    if isinstance(v, str):
        return v.lower()
    if isinstance(v, dict):
        if "address" in v:
            return v["address"].lower()
        if "value" in v:
            return extract_addr(v["value"])
    return str(v)[:42]


def find_erc20_transfers(trace_result):
    """Extract all ERC-20 Transfer events from trace."""
    logs = []
    for log in trace_result.get("logs", []):
        topics = log.get("topics", [])
        if topics and topics[0].startswith("0xddf252ad"):
            fr = "0x" + topics[1][26:] if len(topics) > 1 else "?"
            to = "0x" + topics[2][26:] if len(topics) > 2 else "?"
            amt = int(log.get("data", "0x0"), 16) if log.get("data", "0x") != "0x" else 0
            tok = log.get("address", "?").lower()
            logs.append({"from": fr.lower(), "to": to.lower(), "amount": amt, "token": tok})
    for c in trace_result.get("calls", []):
        logs.extend(find_erc20_transfers(c))
    return logs


def count_calls(trace_result, depth=0):
    """Count internal calls and max depth."""
    count = 1
    max_d = depth
    for c in trace_result.get("calls", []):
        sub_count, sub_depth = count_calls(c, depth + 1)
        count += sub_count
        max_d = max(max_d, sub_depth)
    return count, max_d


def generate_report(tx_hash, tx_dir, raw_arb_json):
    """Generate forensic.md for one transaction."""
    arb_data = json.loads(raw_arb_json)
    resume = arb_data["resume"]
    rr = resume["resume"]

    # Load trace
    trace_path = tx_dir / "trace.json"
    if trace_path.exists():
        with open(trace_path) as f:
            trace = json.load(f)
        trace_result = trace["result"]
        has_trace = True
    else:
        has_trace = False
        trace_result = {}

    lines = []
    def w(s=""):
        lines.append(s)

    w(f"# Forensic Analysis: 0x{tx_hash}")
    w()

    # --- Transaction profile ---
    w("## Transaction profile")
    if has_trace:
        from_addr = trace_result.get("from", "?")
        to_addr = trace_result.get("to", "?")
        n_calls, max_depth = count_calls(trace_result)
        self_call = from_addr.lower() == to_addr.lower()
        transfers = find_erc20_transfers(trace_result)
        tokens = set(t["token"] for t in transfers)

        w(f"- **From**: `{from_addr}`")
        w(f"- **To**: `{to_addr}`")
        w(f"- **Self-call**: {'Yes' if self_call else 'No'}")
        w(f"- **Internal calls**: {n_calls}, max depth {max_depth}")
        w(f"- **ERC-20 transfers**: {len(transfers)}")
        w(f"- **Distinct tokens**: {len(tokens)}")
        token_names = [sym_from_json(raw_arb_json, t) for t in tokens]
        w(f"- **Tokens**: {', '.join(sorted(token_names))}")
    else:
        w("- Trace not available")
        transfers = []
        from_addr = "?"
        to_addr = "?"
        self_call = False
    w()

    # --- AST reduction ---
    w("## AST reduction")
    has_arb = rr.get("hasArbitrage", False)
    verdict = resume.get("arbitrage", "none")
    reasons = resume.get("reason", [])
    cycles = rr.get("transfersInCycles", [])
    leftovers = rr.get("leftovers", [])
    leftover_cycles = rr.get("transfersInLeftoversCycles", [])

    n_dots = len(list(tx_dir.glob("*.dot")))
    w(f"- **Reduction steps**: {n_dots}")
    w(f"- **Cycles detected**: {len(cycles)}")
    w(f"- **Leftovers**: {len(leftovers)}")
    w(f"- **Leftover cycles (specular pairs)**: {len(leftover_cycles)}")
    w(f"- **hasArbitrage**: {has_arb}")
    w(f"- **Verdict**: {verdict}")
    w(f"- **Reasons**: {', '.join(reasons)}")
    w()

    # --- Closed-loop analysis ---
    w("## Closed-loop analysis")
    if cycles:
        w()
        w("| Cycle | Transfers | τ_in | τ_out | τ_in = τ_out? |")
        w("|-------|-----------|------|-------|---------------|")
        for i, c in enumerate(cycles):
            if len(c) > 0:
                first_asset = extract_addr(c[0].get("asset", {}).get("value", "?"))
                last_asset = extract_addr(c[-1].get("asset", {}).get("value", "?"))
                t_in = sym_from_json(raw_arb_json, first_asset)
                t_out = sym_from_json(raw_arb_json, last_asset)
                same = "Yes" if first_asset == last_asset else "No"
                w(f"| {i} | {len(c)} | {t_in} | {t_out} | {same} |")
        w()
    else:
        w("No cycles detected.")
        w()

    # --- Token flow analysis ---
    w("## Token flow analysis")
    if has_trace and transfers:
        # Determine central address (to_ or the most-connected)
        central = to_addr.lower()
        w(f"Central address: `{central}`")
        w()

        # Net balance per token at central address
        balances = defaultdict(int)
        for t in transfers:
            tok = sym_from_json(raw_arb_json, t["token"])
            if t["from"] == central:
                balances[tok] -= t["amount"]
            if t["to"] == central:
                balances[tok] += t["amount"]

        # Tokens that both enter and exit
        in_tokens = set()
        out_tokens = set()
        for t in transfers:
            tok = sym_from_json(raw_arb_json, t["token"])
            if t["to"] == central:
                in_tokens.add(tok)
            if t["from"] == central:
                out_tokens.add(tok)

        both = in_tokens & out_tokens
        if both:
            w(f"Tokens entering AND exiting central address: **{', '.join(sorted(both))}**")
            w()
            for tok in sorted(both):
                ins = [(t["from"], t["amount"]) for t in transfers
                       if t["to"] == central and sym_from_json(raw_arb_json, t["token"]) == tok]
                outs = [(t["to"], t["amount"]) for t in transfers
                        if t["from"] == central and sym_from_json(raw_arb_json, t["token"]) == tok]
                w(f"**{tok}**:")
                for addr, amt in ins:
                    w(f"  - IN:  {amt/1e18:.6f} from `{addr[:16]}...`")
                for addr, amt in outs:
                    w(f"  - OUT: {amt/1e18:.6f} to   `{addr[:16]}...`")
                # Is it cyclic or convergent?
                in_addrs = set(a for a, _ in ins)
                out_addrs = set(a for a, _ in outs)
                if in_addrs & out_addrs:
                    w(f"  - Pattern: **CYCLIC** (same address sends and receives)")
                else:
                    w(f"  - Pattern: **CONVERGENT** (different sources and sinks)")
                w()
        else:
            w("No token both enters and exits the central address.")
            w()
    else:
        w("Trace not available for flow analysis.")
        w()

    # --- Profit / Balance ---
    w("## Profit / Balance")
    delta = rr.get("deltaBalance", [])
    final = resume.get("finalBalance", [])
    costs = rr.get("txCosts", [])

    if delta:
        w("### Delta balance (gross)")
        for d in delta:
            amt = int(d["amount"]["value"])
            asset = extract_addr(d["asset"].get("value", d["asset"]))
            w(f"- {amt/1e18:+.18f} {sym_from_json(raw_arb_json, asset)}")
        w()

    if costs:
        total_cost = sum(int(c["amount"]["value"]) for c in costs)
        w(f"### Gas cost: {total_cost/1e18:.18f} ETH")
        w()

    if final:
        w("### Final balance (net)")
        for d in final:
            amt = int(d["amount"]["value"])
            asset = extract_addr(d["asset"].get("value", d["asset"]))
            w(f"- {amt/1e18:+.18f} {sym_from_json(raw_arb_json, asset)}")
        w()

    # --- Verdict ---
    w("## Verdict")
    w(f"- **Argos**: {verdict} ({', '.join(reasons)})")

    # Decision tree classification
    if has_arb and verdict in ("arbitrage", "warning"):
        if verdict == "arbitrage":
            dt = "now_detected_confirmed"
        else:
            dt = "now_detected_warning"
    elif len(cycles) > 0:
        dt = "has_cycles_not_arb"
    elif "noArbitrageCycles" in reasons:
        if "balanceNegative" in reasons or "finalBalanceNegative" in reasons:
            dt = "eigenphi_fp_negative"
        elif "balancePositive" in reasons:
            dt = "decoder_or_algorithm"
        else:
            dt = "eigenphi_fp_other"
    else:
        dt = "unknown"

    w(f"- **Decision tree**: {dt}")
    w(f"- **Human assessment**: TODO")
    w()

    # --- Notes ---
    w("## Notes")
    notes = []
    if self_call:
        notes.append("Self-calling contract (from == to)")
    if len(cycles) > 0 and not has_arb:
        notes.append(f"Has {len(cycles)} cycle(s) but none labeled arbitrage")
    if leftover_cycles:
        notes.append(f"{len(leftover_cycles)} specular pair(s) removed")
    if len(transfers) > 50:
        notes.append(f"High transfer count ({len(transfers)}) — possible airdrop/distribution")
    if not notes:
        notes.append("No notable patterns")
    for n in notes:
        w(f"- {n}")

    return "\n".join(lines)


def main():
    summary_path = FORENSIC_DIR / "summary.csv"
    if not summary_path.exists():
        print("ERROR: Run run_cat4_forensic.sh first.")
        return

    # Read summary to get list of OK transactions
    ok_txs = []
    with open(summary_path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["status"] == "ok":
                ok_txs.append(row["tx_hash"])

    print(f"Generating forensic reports for {len(ok_txs)} transactions...")

    generated = 0
    skipped = 0
    for tx_hash_full in ok_txs:
        tx_clean = tx_hash_full[2:] if tx_hash_full.startswith("0x") else tx_hash_full
        tx_dir = FORENSIC_DIR / tx_clean
        arb_path = tx_dir / "arbitrage.json"
        report_path = tx_dir / "forensic.md"

        if report_path.exists():
            skipped += 1
            continue

        if not arb_path.exists():
            continue

        with open(arb_path) as f:
            raw = f.read()

        report = generate_report(tx_clean, tx_dir, raw)
        with open(report_path, "w") as f:
            f.write(report)
        generated += 1

    print(f"Generated: {generated}, Skipped (already exists): {skipped}")


if __name__ == "__main__":
    main()
