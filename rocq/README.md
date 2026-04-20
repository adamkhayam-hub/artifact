# Rocq Formalization

## Verification

```bash
opam exec -- rocq compile Arbitrage.v
```

Expected: no errors, no warnings. Compilation takes
approximately 30 seconds.

## Overview

`Arbitrage.v` is a self-contained file (84 lemmas,
2,471 lines, 0 Admitted) that mechanizes all five
theorems from the paper. It requires only the Rocq
standard library (no external dependencies beyond
`Classical`, used once for the termination proof).

## File structure

The file is organized in 15 sections, following the
paper's logical flow:

### Sections 1–4: Definitions

| Section | Content | Paper reference |
|---------|---------|----------------|
| 1. Basic Types | `address`, `token`, `amount`, structural predicates (`is_burn`, `is_mint`, `is_singleton_router`) | §2 |
| 2. Transfer | Record type with source, dest, amount, token, sender (σ) | Definition 1 |
| 3. Cash Flow Tree | Inductive `cft` with `Leaf` and `Tree` constructors; `chain_tree` as binary tree | Definition 2 |
| 4. Walk and Cycle | `valid_walk`, `is_transfer_chain`, `is_cycle` | Definitions 3–5 |

### Section 5: Rewrite rules

The 15 rewriting rules from Table 1, encoded as
named constructors of the `rewrite_step` inductive:

| Constructor | Paper rule | What it does |
|-------------|-----------|--------------|
| `RS_swap_chain` | R1 | Chain two leaves with different tokens |
| `RS_burn_chain` | R2 | Chain a burn transfer with adjacent transfer |
| `RS_mint_chain` | R3 | Chain a mint transfer with adjacent transfer |
| `RS_pool_cycle` | R4 | Chain two transfers in opposite directions (σ check) |
| `RS_router_chain` | R5 | Chain same-token transfers through a singleton router |
| `RS_leaf_chain` | R6, R11 | Chain a leaf with an existing chain |
| `RS_chain_seq` | R9 | Chain two sequential chains |
| `RS_same_token_chain` | R10 | Chain two same-token leaves (node level) |
| `RS_lift` | Lifting | Promote children of a reduced subtree |
| `RS_merge` | R7, R8, R12 | Merge chains with same endpoints |
| `RS_annotate` | R13, R14 | Label closed chain as arbitrage or cycle |

### Section 6: Classification

The `classify` function and its cascade of diagnostic
reasons (`NoCycles`, `Leftovers`, `FinalNeg`,
`FinalMixed`). Maps to Algorithm 4 in the paper.

### Sections 7–9: Helper lemmas

Properties of `has_reason`, `classify`, well-foundedness
of the lexicographic order, and the termination measure
`μ(T) = (count_unlabeled, count_children)`.

### Section 10: Main theorems

| Theorem | Rocq name | Technique |
|---------|-----------|-----------|
| Thm 1 (Preservation) | `preservation_step`, `preservation` | Case analysis on each rewrite rule |
| Thm 2 (Termination) | `fixpoint_terminates`, `termination_bound` | Well-founded induction on μ, bound 3n−2 |
| Thm 3 (Soundness) | `soundness_reasons`, `soundness_full` | Classification cascade |
| Thm 4 (Confluence) | `confluence` | Determinism of `step_fn` |
| Cor 1 (Uniqueness) | `lfp_eq_gfp` | Termination + confluence |
| Thm 5 (Decidable equiv.) | `decidable_equivalence` | Convergence + transitivity |

### Section 11: Certified step function

The step function `step_fn` is defined as a computable
Gallina function (not a relation), making determinism
immediate. It mirrors the implementation:

| Rocq function | Implementation |
|---------------|----------------|
| `annotate_all_fn` | `annotate_cycles` |
| `scan_and_merge` | `find_compatible_cycle` |
| `try_merge_children` | `connect_cycles_children` |
| `step_fn` | `annotate_and_reduce` |

### Sections 12–13: Confluence and termination bound

Confluence follows from determinism of `step_fn`.
The concrete bound 3n−2 is derived from
`unlabeled_le_transfers` (u₀ ≤ n) and
`cc_plus2_le_twice_ct` (c₀ ≤ 2n−2).

### Section 14: Decidable equivalence

Two terms are joinable iff their normal forms coincide.
The proof uses termination (normal forms exist) and
confluence (normal forms are unique).

### Section 15: Extraction

The step function is defined as a computable Gallina
function, making it amenable to Rocq's `Extraction`
mechanism. The extraction commands are commented out
at the end of the file. To produce a verified OCaml
implementation of the rewriting system:

```coq
(* Uncomment the last lines of Arbitrage.v: *)
Extraction Language OCaml.
Extraction "arbitrage_verified"
  classify has_reason
  is_labeled count_unlabeled count_children.
```

Then compile:

```bash
opam exec -- rocq compile Arbitrage.v
```

This produces `arbitrage_verified.ml` and
`arbitrage_verified.mli` — a verified reference
implementation of the step function, the classifier,
and the measure. The extracted code requires
concrete instantiations of the abstract parameters
(`address`, `token`, `token_equiv`, etc.) to run.

## Parameters

The development is parameterized over abstract types
and predicates. No axioms are assumed beyond the
parameters' types.

| Parameter | Type | Purpose |
|-----------|------|---------|
| `address` | `Type` | Abstract address type |
| `address_eq_dec` | decidable equality | Address comparison |
| `token` | `Type` | Abstract token type |
| `token_eq_dec` | decidable equality | Token comparison |
| `token_equiv` | `token → token → bool` | Token equivalence =\_τ (e.g., ETH ≈ WETH) |
| `token_equiv_refl` | reflexivity proof | =\_τ is reflexive |
| `token_equiv_sym` | symmetry proof | =\_τ is symmetric |
| `is_burn` | `transfer → bool` | Identifies burn transfers |
| `is_mint` | `transfer → bool` | Identifies mint transfers |
| `is_singleton_router` | `address → bool` | Identifies singleton router addresses |

The proofs hold for any instantiation of these
parameters. Transitivity of `token_equiv` is explicitly
not required. The structural predicates (`is_burn`,
`is_mint`, `is_singleton_router`) are handled by case
analysis on their boolean value — the proofs do not
depend on their semantics, only on their type.

## Key design decisions

1. **Step as function, not relation.** `step_fn` encodes
   the greedy left-to-right scan directly. Determinism
   is free. The relational formulation (`fixpoint_step_rel`)
   is kept for readability but is superseded by the
   functional version.

2. **`fold_to_sum` conversion.** Converts `fold_left`
   over lists to `list_sum (map f l)` so that `lia`
   can handle the arithmetic in the termination bound.

3. **`fully_lifted` predicate.** Every `RTree` has ≥2
   children after lifting. Required for the 2n−2
   bound on `count_children`.

4. **Binary chain tree.** The `chain_tree` type is a
   binary tree whose in-order traversal yields the
   transfer sequence. This makes merge well-defined
   and preserves construction history.

5. **Token equivalence as parameter.** The Rocq file
   does not hardcode ETH/WETH — it works for any
   chain's native/wrapped pair. Only reflexivity and
   symmetry are assumed.
