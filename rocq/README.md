# Rocq Formalization

## Verification

```bash
opam exec -- rocq compile Arbitrage.v
```

Expected: no errors, no warnings. Compilation takes
approximately 30 seconds.

## Overview

`Arbitrage.v` is a self-contained file (136 lemmas,
7 theorems, 3 corollaries, 4,738 lines, 0 Admitted,
0 axioms) that mechanizes all five theorems from
the paper. It requires only the Rocq standard
library.

## File structure

The file is organized in 15 sections, following the
paper's logical flow:

### Sections 1–4: Definitions

| Section | Content | Paper reference |
|---------|---------|----------------|
| 1. Basic Types | `address`, `token`, `amount`, `token_equiv` | §2 |
| 2. Transfer | Record with source, dest, amount, token, sender (σ); structural predicates (`is_burn`, `is_mint`, `is_singleton_router`, `is_token_contract`) | Definition 1 |
| 3. Cash Flow Tree | Inductive `cft` with `Leaf` and `Tree`; `chain_tree` as binary tree; `bal_cont`, `wrap_unwrap` | Definition 2 |
| 4. Walk and Cycle | `valid_walk`, `is_transfer_chain`, `is_cycle`, `validated_arbitrage` | Definitions 3–5 |

### Section 5: Rewrite rules

The 15 rewriting rules from Table 1, each encoded
as a named constructor of the `rewrite_step`
inductive (one constructor per rule, R1–R15):

| Constructor | Paper rule | What it does |
|-------------|-----------|--------------|
| `RS_swap_chain` | R1 | Chain two adjacent leaves with different tokens |
| `RS_burn_chain` | R2 | Chain a burn transfer with its predecessor |
| `RS_mint_chain` | R3 | Chain a mint transfer with its successor |
| `RS_pool_cycle` | R4 | Two opposite transfers forming a pool round-trip (σ-external) |
| `RS_router_chain` | R5 | Same-token leaves through a singleton router |
| `RS_chain_leaf` | R6 | Chain a leaf with an existing chain |
| `RS_merge_parallel` | R7 | Merge two parallel chains at matching endpoints |
| `RS_merge_closed_R8` | R8 | Merge two closed chains (token-match or `BalCont`) |
| `RS_merge_closed_R9` | R9 | Merge two closed chains at the same self-loop vertex |
| `RS_same_token_chain` | R10 | Chain two same-token leaves at node level (σ-external) |
| `RS_chain_chain` | R11 | Chain two sequential chains |
| `RS_merge_endpoint` | R12 | Merge chains sharing an endpoint vertex |
| `RS_lift` | R13 | Promote a fully-reduced subtree |
| `RS_annotate_arb` | R14 | Label closed chain as arbitrage (=\_τ token-in/out, ¬`WrapUnwrap`) |
| `RS_annotate_cyc` | R15 | Label closed chain as non-arbitrage cycle |

R16 (post-rewriting delta validation) is modeled by
the `validated_arbitrage` predicate.

### Sections 6–10: Classification, lemmas, main theorems

The `classify` function and its cascade of
diagnostic reasons (`NoCycles`, `Leftovers`,
`FinalNeg`, `FinalMixed`) maps to the verdict
cascade in §3.6. Helper lemmas develop
well-foundedness of the lexicographic order on
the termination measure
μ(T) = (`count_unlabeled`, `count_children`).

| Theorem | Rocq name | Technique |
|---------|-----------|-----------|
| Thm 1 (Preservation) | `preservation_step`, `preservation` | Case analysis on each rewrite rule |
| Thm 2 (Termination) | `fixpoint_terminates`, `termination_bound` | Well-founded induction on μ, bound 3n−2 |
| Thm 3 (Soundness) | `soundness_full`, `soundness_end_to_end_tree` | Verdict cascade discharged from Rocq-modeled pipeline |
| Thm 4 (Confluence) | `theorem_4_confluence`, `phase2_confluence` | DSE-ordered input lifted to a total step function |
| Cor 1 (Uniqueness) | `lfp_eq_gfp` | Termination + confluence |
| Thm 5 (Decidable equiv.) | `theorem_5_decidable_equivalence` | Convergence + decidable normal-form equality |

### Sections 11–13: Certified step function and confluence

The Phase-3 step `step_fn` and the Phase-2
combiner `try_combine_leaves` are defined as
computable Gallina functions. Determinism is not a
property of the rewrite relation — the rules
overlap and a relational view admits multiple
redexes. It is recovered structurally: the σ-CFT
input is DSE-ordered (Property prop:dse), so the
step lifts to a total function, and any two
derivations agree on the redex selected at each
step.

| Rocq function | Implementation |
|---------------|----------------|
| `annotate_all_fn` | `annotate_cycles` |
| `scan_and_merge` | `find_compatible_cycle` |
| `try_merge_children` | `connect_cycles_children` |
| `step_fn` | `annotate_and_reduce` |
| `try_combine_leaves` | leaf-pair priority cascade (§3.5) |

The concrete termination bound 3n−2 is derived
from `unlabeled_le_transfers` (u₀ ≤ n) and
`cc_plus2_le_twice_ct` (c₀ ≤ 2n−2).

### Section 14: Decidable equivalence

Two terms are joinable iff their normal forms
coincide. The proof uses termination (normal forms
exist) and confluence (normal forms are unique).

### Section 15: Extraction

The step function is computable Gallina, amenable
to Rocq's `Extraction` mechanism. The extraction
commands are commented at the end of the file. The
extracted code requires concrete instantiations of
the abstract parameters to run.

## Parameters

The development declares 9 `Parameter`s standing
for predicates the OCaml decoder instantiates at
run time. No `Axiom` is asserted: every theorem is
parametric in these realizers, so soundness,
confluence, and termination transfer to any
realizer choice.

| Parameter | Type | Purpose |
|-----------|------|---------|
| `address` | `Type` | Abstract address type |
| `address_eq_dec` | decidable equality | Address comparison |
| `token` | `Type` | Abstract token type |
| `token_eq_dec` | decidable equality | Token comparison |
| `token_equiv` | `token → token → bool` | Token equivalence =\_τ (e.g., ETH ≈ WETH) |
| `is_burn` | `transfer → bool` | Identifies burn transfers |
| `is_mint` | `transfer → bool` | Identifies mint transfers |
| `is_singleton_router` | `address → bool` | Identifies singleton-router addresses |
| `is_token_contract` | `address → token → bool` | Identifies leg-token contract addresses (guards `wrap_unwrap`) |

Well-formedness of `token_equiv` (reflexivity,
symmetry) is stated as a `Prop`
(`is_token_equiv_well_formed`), not as an axiom: a
deployer discharges it for the concrete
instantiation. Transitivity is deliberately not
required, since real-world equivalence is confined
to native/wrapped pairs and does not extend to
bridged or pegged tokens.

## Key design decisions

1. **DSE-ordered input, not deterministic rules.**
   The rewrite rules overlap; the relational view
   admits multiple redexes per term. Confluence is
   not a property of the rule set — it is recovered
   structurally by lifting the step to a total
   function over the DSE-ordered children list
   guaranteed by Property prop:dse on the input
   trace.

2. **List children, not multiset.** The `list cft`
   children in `Tree` is load-bearing. Property 1
   (DSE) is encoded structurally as ordered
   children, not declared as an `Axiom`. A
   multiset children type would force critical-pair
   analysis on the rewriting; the list does not.

3. **Binary chain tree.** The `chain_tree` type is
   a binary tree whose in-order traversal yields
   the transfer sequence. This makes merge
   well-defined and preserves construction history.

4. **Token equivalence as parameter.** The Rocq
   file does not hardcode ETH/WETH — it works for
   any chain's native/wrapped pair. Well-formedness
   (reflexivity, symmetry) is a `Prop`, discharged
   by the deployer; transitivity is not assumed.

5. **End-to-end soundness derived, not assumed.**
   `validate_deltas_sound` and
   `soundness_end_to_end_tree` discharge the
   "premises supplied externally" hypotheses of
   `soundness_end_to_end` from the Rocq-modeled
   `extract_arb_cycles` and `validate_deltas`,
   closing the loop without external assumptions.
