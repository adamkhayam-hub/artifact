"""Hardcoded address registry for lending / flash-loan detection.

Used to flag arbitrage transactions that involve a lending protocol or a
flash loan. The set is deliberately compact (high-volume protocols only)
and lower-cased; lookup is by exact address match on transfer `from` /
`to` / `asset` fields.
"""

# Aave V2 / V3 core
_AAVE = {
    "0x7d2768de32b0b80b7a3454c06bdac94a69ddc7a9",  # Aave V2 LendingPool
    "0x87870bca3f3fd6335c3f4ce8392d69350b4fa4e2",  # Aave V3 Pool
    "0xc6845a5c768bf8d7681249f8927877efda425baf",  # Aave V3 Pool (deprecated, kept for completeness)
}

# Aave V2 aTokens (top by TVL)
_AAVE_ATOKENS = {
    "0x028171bca77440897b824ca71d1c56cac55b68a3",  # aDAI
    "0xbcca60bb61934080951369a648fb03df4f96263c",  # aUSDC
    "0x3ed3b47dd13ec9a98b44e6204a523e766b225811",  # aUSDT
    "0x9ff58f4ffb29fa2266ab25e75e2a8b3503311656",  # aWBTC
    "0x030ba81f1c18d4034f5feb136b6611d8cb6c0b6c",  # aWETH
    "0xc9bc48c72154ef3e5425641a3c747242112a46af",  # aRAI
    "0x101cc05f4a51c0319f570d5e146a8c625198e636",  # aTUSD
    "0xa361718326c15715591c299427c62086f69923d9",  # aBUSD
    "0x5165d24277cd063f5ac44efd447b27025e888f37",  # aYFI
    "0x5e8c8a7243651db1384c0ddfdbe39761e8e7e51a",  # aZRX
    "0xb9d7cb55f463405cdfbe4e90a6d2df01c2b92bf1",  # aUNI
    "0xa685a61171bb30d4072b338c80cb7b2c865c873e",  # aMANA
    "0xfffaa68a92a9f8b14e3eb3c5c6d8a3b1f2c7f8e9",  # aMKR
    "0x6c5024cd4f8a59110119c56f8933403a539555eb",  # aSUSD
    "0x952749e07d7157bb9644a894dfaf3bad5ef6d918",  # aCRV
}

# Aave V3 aTokens
_AAVE_V3_ATOKENS = {
    "0x98c23e9d8f34fefb1b7bd6a91b7ff122f4e16f5c",  # aEthUSDC
    "0x4d5f47fa6a74757f35c14fd3a6ef8e3c9bc514e8",  # aEthWETH
    "0x5ee5bf7ae06d1be5997a1a72006fe6c607ec6de8",  # aEthWBTC
    "0x018008bfb33d285247a21d44e50697654f754e63",  # aEthDAI
    "0x23878914efe38d27c4d67ab83ed1b93a74d4086a",  # aEthUSDT
}

# Compound V2 cTokens
_COMPOUND_CTOKENS = {
    "0x4ddc2d193948926d02f9b1fe9e1daa0718270ed5",  # cETH
    "0x5d3a536e4d6dbd6114cc1ead35777bab948e3643",  # cDAI
    "0x39aa39c021dfbae8fac545936693ac917d5e7563",  # cUSDC
    "0xf650c3d88d12db855b8bf7d11be6c55a4e07dcc9",  # cUSDT
    "0xc11b1268c1a384e55c48c2391d8d480264a3a7f4",  # cWBTC (legacy)
    "0xccf4429db6322d5c611ee964527d42e5d685dd6a",  # cWBTC2
    "0x35a18000230da775cac24873d00ff85bccded550",  # cUNI
    "0xface851a4921ce59e912d19329929ce6da6eb0c7",  # cLINK
    "0x70e36f6bf80a52b3b46b3af8e106cc0ed743e8e4",  # cCOMP
    "0xe65cdb6479bac1e22340e4e755fae7e509ecd06c",  # cAAVE
    "0x95b4ef2869ebd94beb4eee400a99824bf5dc325b",  # cMKR
    "0x041171993284df560249b57358f931d9eb7b925d",  # cUSDP
    "0x12392f67bdf24fae0af363c24ac620a2f67dad86",  # cTUSD
}

# Compound V3 (Comet) markets
_COMPOUND_V3 = {
    "0xc3d688b66703497daa19211eedff47f25384cdc3",  # cUSDCv3
    "0xa17581a9e3356d9a858b789d68b4d866e593ae94",  # cWETHv3
}

# Maker DSS
_MAKER = {
    "0x35d1b3f3d7966a1dfe207aa4514c12a259a0492b",  # Vat
    "0x9759a6ac90977b93b58547b4a71c78317f391a28",  # DaiJoin
    "0x9dc7f52f3554d5f1da12c1f1f8e6f0f74e7d6e72",  # MakerDAO PSM-USDC
}

# Morpho / Spark / Euler / Compound forks
_OTHER_LENDING = {
    "0xbbbbbbbbbb9cc5e90e3b3af64bdaf62c37eeffcb",  # Morpho Blue
    "0x33333aea097c193e66081e930c33020272b33333",  # Morpho-Aave V3 Optimizer
    "0xc02b1b15ef4d6becd8f4cebca5b3acf83ce30b08",  # Spark Lend (placeholder)
    "0xe025e3ca2be02316033184551d4d3aa22024d9dc",  # Euler V2
}

# Balancer / Aave-style flash-loan providers
_FLASH_LOAN_PROVIDERS = {
    "0xba12222222228d8ba445958a75a0704d566bf2c8",  # Balancer V2 Vault (flash loans)
    "0x000000000004444c5dc75cb358380d2e3de08a90",  # Uniswap V4 PoolManager (flash via unlock)
}

# Uniswap V3 / V4 LP managers — relevant for "liquidity event" tag but not
# lending per se; kept separate.
_LP_MANAGERS = {
    "0xc36442b4a4522e871399cd717abdd847ab11fe88",  # Uniswap V3 NFT Position Manager
}

LENDING_ADDRESSES = (
    _AAVE
    | _AAVE_ATOKENS
    | _AAVE_V3_ATOKENS
    | _COMPOUND_CTOKENS
    | _COMPOUND_V3
    | _MAKER
    | _OTHER_LENDING
    | _FLASH_LOAN_PROVIDERS
)

LIQUIDITY_ADDRESSES = _LP_MANAGERS


def _addr_of(v):
    """Unwrap nested {type, value} address structure into a lower-case hex."""
    while isinstance(v, dict):
        v = v.get("value", "")
    return str(v).lower() if v else ""


def _amount_of(a):
    if isinstance(a, dict):
        try:
            return int(a.get("value", "0"))
        except (ValueError, TypeError):
            return 0
    try:
        return int(a)
    except (ValueError, TypeError):
        return 0


def transfers_of(rr):
    """Yield every transfer in cycles + leftovers + leftover-cycles."""
    for cycle in rr.get("transfersInCycles", []) or []:
        for t in cycle if isinstance(cycle, list) else [cycle]:
            yield t
    for t in rr.get("leftovers", []) or []:
        yield t
    for cycle in rr.get("transfersInLeftoversCycles", []) or []:
        for t in cycle if isinstance(cycle, list) else [cycle]:
            yield t


def detect_lending(rr):
    """Return (lending_involved: bool, flash_loan: bool) from one tx's
    inner resume dict (the `resume.resume` body of arbitrage.json)."""
    lending = False
    # Flash-loan signal: a (sender_or_pool, asset) pair appears as both
    # incoming and outgoing for the same address with equal magnitude.
    by_addr_asset_out = {}
    by_addr_asset_in = {}
    for t in transfers_of(rr):
        frm = _addr_of(t.get("from"))
        to = _addr_of(t.get("to"))
        asset = _addr_of(t.get("asset"))
        amt = _amount_of(t.get("amount"))
        if frm in LENDING_ADDRESSES or to in LENDING_ADDRESSES \
                or asset in LENDING_ADDRESSES:
            lending = True
        if not amt:
            continue
        by_addr_asset_out.setdefault((frm, asset), []).append(amt)
        by_addr_asset_in.setdefault((to, asset), []).append(amt)
    flash = False
    for key, outs in by_addr_asset_out.items():
        ins = by_addr_asset_in.get(key, [])
        for v in outs:
            if v in ins:
                flash = True
                break
        if flash:
            break
    return lending, flash
