# Rocq Formalization

## Verification

```bash
opam exec -- rocq compile Arbitrage.v
```

Expected: no errors, no warnings.

To check that nothing is assumed beyond the declared
interface, add at the end of the file and recompile:

```coq
Print Assumptions theorem_1_preservation.
Print Assumptions theorem_2_termination.
Print Assumptions theorem_3_soundness.
Print Assumptions theorem_4_confluence.
Print Assumptions theorem_5_decidable_equivalence.
```

Each lists exactly the eleven `Parameter`s below and
nothing else: no `Admitted`, no added axiom.

## Overview

`Arbitrage.v` is a self-contained file (13,489 lines;
5 theorems, 432 lemmas, 13 corollaries, 1 example;
0 `Admitted`, 0 axioms, 11 `Parameter`s) that
mechanizes the five theorems of the paper. It requires
only the Rocq standard library.

Exactly five results are declared `Theorem`, and they
are the paper's five. Every other result is a `Lemma`,
a `Corollary`, or an `Example`, so the file's theorem
count is a claim count.

| Paper | Rocq |
|---|---|
| Thm 1, Preservation | `theorem_1_preservation` |
| Thm 2, Termination | `theorem_2_termination` |
| Thm 3, Soundness | `theorem_3_soundness` |
| Thm 4, Uniqueness | `theorem_4_confluence` |
| Thm 5, Decidability | `theorem_5_decidable_equivalence` |

## File structure

35 sections, grouped into six parts. A roadmap follows
the header comment at the top of the file.

**Part I — Model and rules (§1–7).** Basic types and the
eleven parameters; transfers (Def. 1); the σ-CFT
(Def. 2); walks and cycles (Def. 3–4); the rewrite rules;
the verdict function `classify` and its elementary
properties.

**Part II — Foundational invariants (§8–12).**
Well-foundedness of the lexicographic order; the measure
and its structural lemmas; preservation, including the
multiset-conservation form; walk correspondence, first
per rule and then for the multi-walk case.

**Part III — The deterministic kernel (§13–21).** The
computable step function `step_fn` and the leaf combiner
`try_combine_leaves`; determinism and confluence; the
relational characterization of `step_fn`; verified
`classify` properties; the concrete 3n−2 bound;
termination of the nondeterministic relation; phase-2
confluence; the phase-3 bridge back into `rewrite_star`.

**Part IV — Soundness into the transfer graph (§22–23).**
`rcft_invariant` and `refinement_of_transfer_graph_cycles`;
the structural soundness of `classify`, ending in
`graph_arbitrage` and its transfer-vocabulary form
`def5_witness`.

**Part V — The five theorems (§24).** Stated together, in
order, with the decidable-equality bundle they need.

**Part VI — Beyond the paper (§25–35).** The
redex-complete kernel `kfull_step` / `kfull_deep` (O0);
the canonical map `kappa` (O1) and its
associativity/commutativity laws (O2); linearity, which
discharges the distinctness side condition; local
confluence modulo `kappa` (O3); observable confluence
over δ-conservation; decidable structural equivalence.

## Rewrite rules

`rewrite_step` has 17 constructors: the 15 rules of
Table 1, plus `RS_lift` and `RS_under`.

| Constructor | Rule | What it does |
|-------------|------|--------------|
| `RS_swap_chain` | R1 | Chain two adjacent leaves with different tokens |
| `RS_burn_chain` | R2 | Chain a burn with an adjacent transfer (not a mint) |
| `RS_mint_chain` | R3 | Chain a transfer with an adjacent mint (not a burn) |
| `RS_pool_cycle` | R4 | Two opposite transfers through one address, σ external; builds a `Chaining` chain |
| `RS_router_chain` | R5 | Same-token leaves through a singleton router |
| `RS_leaf_chain` | R6 | Chain a leaf onto a chain (same call frame) |
| `RS_merge_endpoints` | R7 | Merge two chains sharing origin and destination, agreeing on τ_out and differing on τ_mid |
| `RS_merge_add` | R8 | Merge two closed chains (all three tokens agree, or `BalCont`) |
| `RS_merge_closed_R9` | R9 | Merge two closed chains agreeing on τ_in and τ_out |
| `RS_chain_seq` | R10 | Chain two sequential chains (token continuity or `BalCont`) |
| `RS_same_token_chain` | R11 | Same-token leaf pair across frames, σ external |
| `RS_node_leaf_chain` | R12 | Chain a leaf onto a chain across call frames |
| `RS_merge_node` | R13 | R7's premises with τ_in pinned as well |
| `RS_annotate_arb` | R14 | Label a closed chain `Arbitrage` (τ_in =_τ τ_out, ¬`WrapUnwrap`) |
| `RS_annotate_cyc` | R15 | Label a closed chain `Cycle` |
| `RS_lift` | — | A fully-reduced frame's children become siblings of the frame |
| `RS_under` | — | Single-hole congruence: a rule may fire in a nested subtree |

R16 (post-fixpoint delta validation) is not a rewrite
step; it is modeled by the `validated_arbitrage`
predicate and applied by `validate_deltas`.

## What the five theorems say

| Theorem | Content |
|---|---|
| `theorem_1_preservation` | Chains track walks in G; every transfer of a reachable tree is a transfer of T₀; the two carry the same multiset |
| `theorem_2_termination` | The kernel reaches a normal form; on `fully_lifted`, `non_empty` trees the bound is 3n−2 (`termination_bound`); `rewrite_step` is well-founded under any order (`rewrite_step_wf`) |
| `theorem_3_soundness` | An `Arbitrage` verdict on any reachable tree yields `def5_witness` over T₀'s own transfers: an address, a token, and a maximal bundle of walks that closes there and nets positive |
| `theorem_4_confluence` | The kernel's normal form is unique |
| `theorem_5_decidable_equivalence` | Joinable iff equal normal forms |

Supporting results the paper names:

| Result | Rocq |
|---|---|
| No fabricated transfers | `no_fabricated_transfers` |
| Reported profits are input balances | `reported_deltas_are_input_deltas` |
| A plain swap is not a Def. 5 witness | `plain_swap_not_def5` |
| Bundle size = 1 + parallel-merge junctions | `walk_decomposition_count` |
| Balances agree under every rule order | `observable_confluence_delta` |
| Local joinability up to reassociation | `local_confluent_mod_kappa_holds` |
| Decidable structural equivalence | `struct_equiv_dec` |

The 3n−2 bound is composed from `unlabeled_le_transfers`
(u₀ ≤ n) and `cc_plus2_le_twice_ct` (c₀ ≤ 2n−2, the
handshake, which is where `fully_lifted` is needed).

## Correspondence with the implementation

| Rocq | OCaml |
|---|---|
| `annotate_all_fn` | `Annotate.annotate_cycles` |
| `scan_and_merge` | `Merge.find_merge_partner` |
| `try_merge_children` | `Merge.connect_cycles_children` |
| `step_fn` | the annotate/merge fixpoint |
| `try_combine_leaves` | the leaf-pair priority cascade |
| `validate_deltas` | `Verdict.validate_arbitrage_deltas` |
| `classify` | `Verdict.infer_arbitrage_from_reasons` |

## Parameters

Eleven `Parameter`s, declared and never defined. Nothing
is assumed about them beyond their types, so every
result holds for every realizer.

| Parameter | Type | Purpose |
|-----------|------|---------|
| `address` | `Type` | Abstract address type |
| `address_eq_dec` | decidable equality | Address comparison |
| `token` | `Type` | Abstract token type |
| `token_eq_dec` | decidable equality | Token comparison |
| `token_equiv` | `token → token → bool` | Token equivalence =_τ (e.g. ETH ≈ WETH) |
| `is_burn` | `transfer → bool` | Identifies burn transfers |
| `is_mint` | `transfer → bool` | Identifies mint transfers |
| `is_singleton_router` | `address → bool` | Identifies singleton-router addresses (R5) |
| `is_token_contract` | `address → token → bool` | Leg-token contract membership (guards `wrap_unwrap`) |
| `net_positive` | `chain_tree → bool` | The deployment's cost model, case-split in `validate_deltas` |
| `trace_key` | `transfer → nat` | Trace-order key realizing Property 1; used by `kappa`. A deployment discharges it with the trace's own event indices |

Two well-formedness conditions are **stated but never
assumed**, so they are obligations on a deployment
rather than hypotheses of any theorem:

- `is_token_equiv_well_formed` — reflexivity and
  symmetry of `token_equiv`. Transitivity is
  deliberately not required: native/wrapped pairs do not
  chain to bridged or pegged tokens.
- `is_trace_key_wf` — injectivity of `trace_key`.

## Extraction

The extraction block sits at the end of the file,
commented, so that an ordinary compile does not write
generated files into the tree. Uncommenting it emits
`arbitrage_verified.ml` / `.mli`, carrying the kernel
(`step_fn`, `try_combine_leaves`), the verdict cascade
(`classify`), and the canonical map with its decidable
structural equivalence (`kappa`, `struct_equiv_dec`).

The emitted module has been checked to compile under
`ocamlc` against the realizers supplied there and to
run. Those realizers are placeholders for unit-testing
the extracted kernel, not the production configuration.
The extraction directives are erasure-level (`nat` as
OCaml `int`, native lists, products and options) and
carry no logical content.

Differential testing of the extracted kernel against the
production OCaml module at trace scale has not been
done; the paper states this explicitly.

## Key design decisions

1. **Determinism is structural, not a property of the
   rules.** The rules overlap, and the relational view
   admits several redexes per term. The kernel recovers
   a total step by scanning the DSE-ordered children
   list that Property 1 guarantees.

2. **List children, not multiset.** The `list` of
   children in `Tree` is load-bearing: Property 1 is
   encoded in the data structure rather than declared as
   an axiom. A multiset would force critical-pair
   analysis on the rewriting.

3. **Binary chain tree.** `chain_tree` is a binary tree
   whose in-order traversal is the transfer sequence,
   which makes merge well-defined and preserves the
   order of assembly.

4. **Token equivalence as a parameter.** Nothing
   hardcodes ETH/WETH; the development works for any
   chain's native/wrapped pair.

5. **Soundness lands in the transfer graph.**
   `theorem_3_soundness` concludes `def5_witness`, which
   is stated over T₀'s transfers in the vocabulary of
   transfers alone, naming neither the rewriting nor the
   normal form nor any label the reduction assigns.

6. **Openness is disclosed, not hidden.** Local
   confluence modulo `kappa` is proved on well-formed
   trees; whether it extends to a global statement is
   open. Every result the paper states uses the
   deterministic order and is unaffected either way.
