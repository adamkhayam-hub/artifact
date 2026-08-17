(** * Arbitrage Detection: Formal Verification

    Mechanized proofs for the convergent term
    rewriting system described in "If It Walks Like
    an Arbitrage: Agnostic Detection with Decidable
    Structural Equivalence."

    The five theorems of the paper (one Rocq [Theorem] each,
    [theorem_1_preservation] .. [theorem_5_decidable_equivalence]);
    every other result in this file is a [Lemma], a [Corollary],
    or an [Example].
    1. Preservation: every chain corresponds to walks in the
       transfer graph and the transfer multiset is conserved by
       every step.
    2. Termination: the fixpoint reaches a normal form in O(n)
       passes (bound 3n-2); the nondeterministic relation is
       well-founded.
    3. Soundness: an [Arbitrage] verdict on any reduced form of a
       transaction entails a real arbitrage in that transaction's own
       transfer graph G(T0) -- an address, a token, and a maximal
       bundle of connected walks that leaves the address, returns to
       it, is backed edge-for-edge by a sub-multiset of T0's own
       transfers, and nets strictly positive ([def5_witness],
       Definition 5; [graph_arbitrage] is the same witness in
       structural form).  Def 5 is stated over G(T0) alone and in the
       vocabulary of transfers, so the guarantee is a property of the
       transaction's edges, established independently of the
       classifier and readable without the pipeline's type
       definitions.
    4. Confluence: the deterministic kernel admits a unique normal
       form.
    5. Decidable equivalence: kernel joinability iff equal normal
       form (the word problem for the kernel is decidable).

    Additional mechanized results (supporting lemmas, feeding the
    expanded confluence/equivalence discussion; not among the five
    numbered theorems):
    - O3 [local_confluent_mod_kappa_holds]: local confluence modulo
      kappa of the nondeterministic relation over well-formed
      sigma-CFTs.
    - [observable_confluence(_delta)]: the net-flow map is invariant
      under every reduction order (delta conservation), so the
      verdict is independent of the order in which rules fire.
      Structural order-independence holds modulo the canonical form
      kappa (O3); where two orders differ structurally they still
      agree on the conserved net-flow, which is the observable the
      verdict reads.
    - [struct_equiv_dec]: decidable structural equivalence,
      [struct_equiv] := equal canonical form (kappa), quotienting
      parallel-bundle reordering (A||B||C = every permutation).
    - [kfull_*]: redex-complete kernel (O0) soundness/completeness,
      closing the R-vs-K formalization gap.

    Statistics: 451 theorems/lemmas/corollaries/examples
    (5 Theorems -- the paper's five -- 432 Lemmas,
    13 Corollaries, 1 Example: the plain-swap regression
    test [plain_swap_not_def5]),
    13489 lines, 0 axioms, 0 Admitted, 11 Parameters.

    The eleven [Parameter]s are DECLARED AND NEVER DEFINED.
    They are the development's trusted interface: the two
    carrier types ([address], [token]) with their decidable
    equalities, token equivalence ([token_equiv]), burn/mint
    detection, singleton-router and token-contract
    membership, the cost model ([net_positive]), and the
    trace-order key ([trace_key], the Property 1 realizer
    used by the canonical map kappa).  Nothing is assumed
    about them beyond their declared types, so every result
    here holds for EVERY realizer, and [Print Assumptions]
    on each of the five theorems lists exactly these and
    nothing else -- no [Admitted], no added axiom.  Two
    well-formedness conditions on them are STATED but never
    assumed, and so are obligations on any deployment rather
    than hypotheses of the proofs:
    [is_token_equiv_well_formed] (reflexivity and symmetry of
    [token_equiv]) and [is_trace_key_wf] (injectivity of
    [trace_key]).
    Rewriting rules: [rewrite_step] has 17 constructors,
    the 15 rules R1--R15 of Table 1 plus [RS_lift] (a
    fully-reduced frame's children become siblings of the
    frame) and [RS_under] (the single-hole congruence that
    lets a rule fire in a nested subtree).  R16
    (post-rewriting validation) is modeled by the
    [validated_arbitrage] predicate.
    Compile: opam exec -- rocq compile Arbitrage.v

    Author: [anonymous]
    Date: March 2026
*)

(* ############################################################
   ROADMAP

   Part I   (Sec. 1-7)   Model, rules & classification.
   Part II  (Sec. 8-12)  Foundational invariants: measure,
                         well-foundedness, preservation, walk
                         correspondence.
   Part III (Sec. 13-21) The deterministic kernel: step
                         function, confluence, termination
                         bound, decidable equivalence.
   Part IV  (Sec. 22-23) Soundness into the transfer graph:
                         refinement and graph_arbitrage (Def. 5).
   Part V   (Sec. 24)    The five theorems (paper Table), in order.
   Part VI  (Sec. 25-35) Beyond the paper: the sigma-CFT as an
                         algebra -- K_full, kappa, AC-invariance,
                         local confluence modulo kappa, observable
                         confluence, decidable structural equivalence.
   ############################################################ *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Stdlib Require Import Wellfounded.Lexicographic_Product.
From Stdlib Require Import Wellfounded.Inverse_Image.
From Stdlib Require Import Relation_Operators.
From Stdlib Require Import Wf_nat.
From Stdlib Require Import Permutation.
Import ListNotations.

(* ############################################################
   Part I -- Model, rules & classification
   ############################################################ *)

(* ============================================================
   Section 1: Basic types and parameters
   ============================================================ *)

Parameter address : Type.
Parameter address_eq_dec :
  forall (a b : address), {a = b} + {a <> b}.

Parameter token : Type.
Parameter token_eq_dec :
  forall (t1 t2 : token), {t1 = t2} + {t1 <> t2}.

(** Token equivalence =_τ (Definition 4).
    Strict equality extended so the native asset
    and its canonical wrapped form are identified
    (e.g., ETH and WETH on Ethereum). *)
Parameter token_equiv : token -> token -> bool.

(** Deployment well-formedness for [token_equiv].

    Stated as a [Prop], not an [Axiom]: soundness with respect to
    Definition~5 parameterized by [token_equiv] is invariant under
    the boolean choice of the relation, so a deployer discharges
    well-formedness separately for their concrete instantiation.
    Reflexivity is required in any sensible deployment (a token is
    equivalent to itself); symmetry is the natural closure of
    "wrapped-pair" relations such as ETH/WETH; transitivity is
    deliberately not required, since real-world equivalence is
    confined to native/wrapped pairs and does not extend to bridged
    or pegged tokens (which are price-oracle territory). *)
Definition is_token_equiv_well_formed
    (eq : token -> token -> bool) : Prop :=
  (forall t, eq t t = true) /\
  (forall t1 t2, eq t1 t2 = eq t2 t1).

Definition amount := nat.

(* ============================================================
   Section 2: Transfers (Definition 1)
   ============================================================ *)

Record transfer := mkTransfer {
  tr_source : address;
  tr_dest : address;
  tr_amount : amount;
  tr_token : token;
  tr_sender : address;
}.

Definition transfer_graph := list transfer.

(** Structural predicates for rule refinement.
    These capture properties of individual transfers
    that determine which rewriting rule applies.
    They are structural properties of EVM execution,
    not protocol-specific knowledge: cross-chain
    validation confirms they hold on Ethereum,
    Arbitrum, and BSC (Appendix E). *)
Parameter is_burn : transfer -> bool.
Parameter is_mint : transfer -> bool.
Parameter is_singleton_router : address -> bool.

(* ============================================================
   Section 3: Cash-flow trees / sigma-CFT (Definition 2)
   ============================================================ *)

(* The [list cft] children in [Tree] is load-bearing.
   Property 1 (DSE) is encoded structurally as
   ordered children, not declared as an [Axiom].
   A [multiset] children would force critical-pair
   analysis on the rewriting; the list does not. *)
Inductive cft : Type :=
  | Leaf : transfer -> cft
  | Tree : address -> list cft -> cft.

Inductive construction_label : Type :=
  | Chaining
  | Merging
  | Cycle
  | Arbitrage
  | TokenBurn
  | TokenMint.

Definition label_eq_dec :
  forall (l1 l2 : construction_label), {l1 = l2} + {l1 <> l2}.
Proof. decide equality. Defined.

(** A chain is "labeled" when it has been recognized
    as a closed structure. In the implementation,
    find_compatible_cycle selects pairs with
    tc_construction in {cycle, token_burn,
    token_mint}, and merge_cycles produces
    cycle or arbitrage. Arbitrage is also labeled
    (it's a promoted cycle). *)
Definition is_labeled (l : construction_label) : bool :=
  match l with
  | Cycle | Arbitrage | TokenBurn | TokenMint => true
  | _ => false
  end.

(* Chain as an inductive binary tree *)
Inductive chain_tree : Type :=
  | CT_transfer : transfer -> chain_tree
  | CT_node : address -> address -> list address ->
              token -> token -> transfer ->
              construction_label ->
              chain_tree -> chain_tree -> chain_tree.

Definition ch_label (c : chain_tree) : construction_label :=
  match c with
  | CT_transfer _ => Chaining
  | CT_node _ _ _ _ _ _ l _ _ => l
  end.

(** The two immediate subtrees of a node ([None] on a leaf).
    Pins the operand structure of a merged chain in the merge
    rules (matching the paper's [C_merge] = node combining
    [C1], [C2]); needed because [merge_operands]/[merge_chain]
    are defined much later. *)
Definition ch_children (c : chain_tree)
    : option (chain_tree * chain_tree) :=
  match c with
  | CT_transfer _ => None
  | CT_node _ _ _ _ _ _ _ l r => Some (l, r)
  end.

Definition ch_origin (c : chain_tree) : address :=
  match c with
  | CT_transfer t => tr_source t
  | CT_node o _ _ _ _ _ _ _ _ => o
  end.

Definition ch_destination (c : chain_tree) : address :=
  match c with
  | CT_transfer t => tr_dest t
  | CT_node _ d _ _ _ _ _ _ _ => d
  end.

Definition ch_token_in (c : chain_tree) : token :=
  match c with
  | CT_transfer t => tr_token t
  | CT_node _ _ _ ti _ _ _ _ _ => ti
  end.

Definition ch_token_out (c : chain_tree) : token :=
  match c with
  | CT_transfer t => tr_token t
  | CT_node _ _ _ _ to_ _ _ _ _ => to_
  end.

(** Signed balance contribution of a single transfer
    at (address, token): +amount if we query at the
    destination with the transfer's token, -amount
    at the source, 0 otherwise. *)
Definition transfer_delta (t : transfer)
    (a : address) (tok : token) : Z :=
  if token_eq_dec tok (tr_token t) then
    if address_eq_dec a (tr_dest t)
    then Z.of_nat (tr_amount t)
    else if address_eq_dec a (tr_source t)
    then (- Z.of_nat (tr_amount t))%Z
    else 0%Z
  else 0%Z.

(** ch_delta aggregates signed transfer amounts over
    all leaves of a chain_tree.  Computed from the
    tree structure rather than stored, so the
    semantic invariant
    ch_delta c a tok = sum over leaves of
      transfer_delta t a tok
    holds by definition. *)
Fixpoint ch_delta (c : chain_tree)
    (a : address) (tok : token) : Z :=
  match c with
  | CT_transfer t => transfer_delta t a tok
  | CT_node _ _ _ _ _ _ _ l r =>
      (ch_delta l a tok + ch_delta r a tok)%Z
  end.

(** address_in_chain: does address a appear as a
    source in any leaf transfer, or in the middleman
    list of any chain node?  Matches the OCaml
    address_in_cycle function (eth_tools.ml:1036). *)
Fixpoint address_in_chain (a : address) (c : chain_tree) : bool :=
  match c with
  | CT_transfer t =>
      if address_eq_dec a (tr_source t) then true else false
  | CT_node _ _ middlemen _ _ _ _ l r =>
      if existsb (fun m => if address_eq_dec a m then true else false) middlemen
      then true
      else address_in_chain a l || address_in_chain a r
  end.

(** [is_token_contract a t] holds when address [a] is
    the deployed contract of token [t] (e.g., the WETH
    contract for the WETH token).  Trust-base predicate,
    same status as [is_burn] / [is_singleton_router]. *)
Parameter is_token_contract : address -> token -> bool.

(** Net-profitability predicate.  Abstracts the
    deployer's cost model: on Ethereum,
    [net_positive c = true] iff the cycle's gross
    delta exceeds gas plus block-builder payment; on
    Arbitrum, gas plus L1-data cost; on BSC, the
    chain-specific cost basis.  Stated as a
    [Parameter], not modeled in the kernel, so the
    soundness theorems are parametric in the cost
    model and transfer to any chain whose
    realizer is supplied. *)
Parameter net_positive : chain_tree -> bool.

(** [wrap_unwrap c] holds when [c] is a pure native-
    wrapped roundtrip: a recursive chain whose
    middleman set contains a leg-token contract and
    whose sub-chains are themselves wrap/unwrap (with
    the base case being two leaf children).  Mirrors
    [is_pure_wrap_unwrap] in [mev_arbitrage.ml:55].
    Guards R14 (paper) to exclude ETH<->WETH (and
    analogous) cycles from the arbitrage label. *)
Fixpoint wrap_unwrap (c : chain_tree) : bool :=
  match c with
  | CT_transfer _ => false
  | CT_node _ _ middlemen tin tout _ _ l r =>
      let middleman_is_leg_token :=
        existsb (fun m => is_token_contract m tin
                       || is_token_contract m tout) middlemen in
      let children_ok :=
        match l, r with
        | CT_transfer _, CT_transfer _ => true
        | _, _ => wrap_unwrap l && wrap_unwrap r
        end in
      middleman_is_leg_token && children_ok
  end.

(* Reduced CFT: the tree during/after rewriting *)
Inductive reduced_cft : Type :=
  | RLeaf : transfer -> reduced_cft
  | RChain : chain_tree -> reduced_cft
  | RTree : address -> list reduced_cft -> reduced_cft.

(** Extract all leaf transfers from a chain tree.
    In the implementation, these are the Cftt_transfer
    leaves at the bottom of the binary chain structure. *)
Fixpoint chain_transfers (c : chain_tree) : list transfer :=
  match c with
  | CT_transfer t => [t]
  | CT_node _ _ _ _ _ _ _ l r =>
      chain_transfers l ++ chain_transfers r
  end.

(** The token the middleman passes on: the token of
    the second-to-last transfer.  Mirrors [tc_amount0]
    in [eth_cft_fixpoint.ml], which a leaf pair seeds
    from the first transfer and every chain extension
    shifts to the previous output.  Degenerates to the
    entry token on a single-transfer chain. *)
Definition ch_token_mid (c : chain_tree) : token :=
  match rev (chain_transfers c) with
  | _ :: t :: _ => tr_token t
  | _ => ch_token_in c
  end.

(** [bal_cont j c1 c2] holds when, at junction
    address [j], the combined per-token delta of
    [c1] and [c2] is non-negative for every token
    appearing in either chain.  Mirrors
    [balance_continuous_at] in
    [eth_cft_fixpoint.ml:264].  Strictly weaker
    than token continuity: every token-continuous
    junction is balance-continuous, but not the
    converse.  Used as an OR-alternative to the
    strict token-equality premises of R8 and R10. *)
Definition bal_cont (j : address) (c1 c2 : chain_tree) : bool :=
  forallb (fun t => Z.leb 0%Z
                     (ch_delta c1 j t + ch_delta c2 j t)%Z)
    (map tr_token (chain_transfers c1 ++ chain_transfers c2)).

(** Semantic invariant: ch_delta aggregates
    signed transfer amounts across the chain's
    leaves.  This connects the syntactic [ch_delta]
    function to the semantic balance computed
    from the original [transfer_graph]. *)
Lemma fold_right_Zadd_app :
  forall (l1 l2 : list Z),
    fold_right Z.add 0%Z (l1 ++ l2) =
    (fold_right Z.add 0%Z l1 +
     fold_right Z.add 0%Z l2)%Z.
Proof.
  induction l1 as [|x xs IH]; simpl; intros l2.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma ch_delta_sum_leaves :
  forall c a tok,
    ch_delta c a tok =
    fold_right Z.add 0%Z
      (map (fun t => transfer_delta t a tok)
           (chain_transfers c)).
Proof.
  induction c as [t | o d m ti to_ ft lbl l IHl r IHr];
    simpl; intros a tok.
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IHl, IHr.
    rewrite map_app, fold_right_Zadd_app.
    reflexivity.
Qed.

(** Extract all transfers from a reduced CFT. *)
Fixpoint rcft_transfers (t : reduced_cft) : list transfer :=
  match t with
  | RLeaf tr => [tr]
  | RChain c => chain_transfers c
  | RTree _ children =>
      flat_map rcft_transfers children
  end.

(** Membership: a chain c appears as some [RChain c]
    somewhere in the reduced CFT structure.  Used by the
    Refinement Proposition. *)
Inductive chain_in_rcft : chain_tree -> reduced_cft -> Prop :=
  | CIR_here : forall c,
      chain_in_rcft c (RChain c)
  | CIR_tree : forall c addr children child,
      In child children ->
      chain_in_rcft c child ->
      chain_in_rcft c (RTree addr children).

(* ============================================================
   Section 4: Walks and cycles (Definitions 3-4)
   ============================================================ *)

Definition walk := list transfer.

Fixpoint valid_walk (w : walk) : Prop :=
  match w with
  | [] => True
  | [_] => True
  | t1 :: ((t2 :: _) as rest) =>
      tr_dest t1 = tr_source t2 /\ valid_walk rest
  end.

Definition is_transfer_chain (w : walk) : Prop :=
  valid_walk w /\ w <> [].

Definition is_cycle (w : walk) : Prop :=
  is_transfer_chain w /\
  match w, rev w with
  | t1 :: _, t2 :: _ => tr_source t1 = tr_dest t2
  | _, _ => False
  end.

(** A closed walk in the transfer graph G: a cycle whose
    transfers all come from G.  Used by the Refinement
    Proposition (Section 14b) to relate our arbitrage
    detections to the cycles enumerable on the aggregate
    transfer graph. *)
Definition is_transfer_graph_cycle
    (G : transfer_graph) (w : walk) : Prop :=
  is_cycle w /\ Forall (fun t => In t G) w.

(* ============================================================
   Section 5: Rewrite rules R1-R16
   ============================================================ *)

Definition chainable (t1 t2 : transfer) : Prop :=
  tr_dest t1 = tr_source t2 /\
  tr_token t1 <> tr_token t2.

(* ------------------------------------------------------------
   Leaf-pair combiner, hoisted above [rewrite_step].

   [try_combine_leaves_full] is the deterministic, redex-complete
   leaf-pair cascade; its correctness lemmas ([kfull_leaf_sound]
   / [kfull_leaf_O0] / [kfull_leaf_complete]) live with the
   kernel in Section 16.  It is defined here so that [RS_lift]
   can carry the [lift_ok_b] guard: a subtree may be lifted only
   when it is *not* a fireable leaf-pair redex, matching the
   paper's Rule 2 discipline of lifting a *fully reduced* frame
   (Section: bottom-up iteration).  Only the whole-list two-leaf
   shape needs guarding; every other redex ([siblings ++ ...],
   merge, annotate) commutes with the lifted sibling prefix.
   ------------------------------------------------------------ *)

(** Canonical leaf-pair chain (Chaining/Burn/Mint):
    same shape regardless of which rule fires. *)
Definition leaf_pair_chain
    (l : construction_label) (t1 t2 : transfer) : chain_tree :=
  CT_node (tr_source t1) (tr_dest t2)
          [tr_dest t1]
          (tr_token t1) (tr_token t2)
          t1 l
          (CT_transfer t1) (CT_transfer t2).

(** Pool-cycle chain (R4): a cycle from [tr_source t1] back to
    [tr_source t1] via [tr_dest t1]; the sender escapes the
    pair. *)
Definition pool_cycle_chain
    (t1 t2 : transfer) : chain_tree :=
  CT_node (tr_source t1) (tr_dest t2)
          [tr_dest t1]
          (tr_token t1) (tr_token t2)
          t1 Chaining
          (CT_transfer t1) (CT_transfer t2).

(** Redex-complete deterministic leaf-pair combiner.  Priority
    R2 > R3 > (same-token: R5 > R4 > R11) / (different-token:
    R1), all under the shared adjacency guard
    [tr_dest t1 = tr_source t2].  Returns [Some] iff some
    leaf-pair rule fires and [None] iff none applies.

    R2 and R3 are guarded against EACH OTHER, not merely ordered:
    a burn feeding a mint matches neither, and falls through to the
    plain fallback (R1 on differing tokens, R5 through a router).
    That is the implementation's own precedence --
    [classify_token_pair_shared] pairs a burn with a *transfer* and
    a mint with a *transfer*, so a burn/mint pair matches no kind
    and reaches [chain_fallback_basic] -- and it is reachable:
    30 such leaf pairs across the traced transactions, all combined
    as plain chains.  R4 and R11 keep their burn/mint guards, so
    the fall-through is routed past them. *)
Definition try_combine_leaves_full
    (t1 t2 : transfer) : option chain_tree :=
  if address_eq_dec (tr_dest t1) (tr_source t2) then
    if is_burn t1 && negb (is_mint t2)
    then Some (leaf_pair_chain TokenBurn t1 t2)      (* R2 *)
    else if is_mint t2 && negb (is_burn t1)
    then Some (leaf_pair_chain TokenMint t1 t2)      (* R3 *)
    else if token_eq_dec (tr_token t1) (tr_token t2) then
      if is_singleton_router (tr_dest t1)
      then Some (leaf_pair_chain Chaining t1 t2)     (* R5 *)
      else if is_burn t1 || is_mint t2 then None
      else if address_eq_dec (tr_dest t2) (tr_source t1) then
        if address_eq_dec (tr_sender t1) (tr_dest t1) then
          if address_eq_dec (tr_sender t2) (tr_dest t2)
          then None
          else Some (pool_cycle_chain t1 t2)         (* R4, t2 escape *)
        else Some (pool_cycle_chain t1 t2)           (* R4, t1 escape *)
      else if address_eq_dec (tr_sender t1) (tr_dest t1)
      then None
      else Some (leaf_pair_chain Chaining t1 t2)     (* R11 *)
    else Some (leaf_pair_chain Chaining t1 t2)       (* R1 *)
  else None.

(** The two leaf-pair guards above fail together exactly when the
    burn and mint flags agree, which is the premise R1 and R5 carry
    in place of the two separate "not a burn" / "not a mint"
    conditions. *)
Lemma burn_mint_agree :
  forall t1 t2,
    is_burn t1 && negb (is_mint t2) = false ->
    is_mint t2 && negb (is_burn t1) = false ->
    is_burn t1 = is_mint t2.
Proof.
  intros t1 t2 H1 H2.
  destruct (is_burn t1), (is_mint t2); simpl in H1, H2;
    solve [reflexivity | discriminate].
Qed.

(** Lift guard.  A child list may be lifted unless it is a
    two-leaf list on which a leaf-pair rule fires.  Those rules
    ([RS_swap_chain] .. [RS_same_token_chain]) match the whole
    child list [ [RLeaf t1; RLeaf t2] ] with no siblings, so after
    a lift (which prepends siblings) they can no longer fire and
    the leaves would strand.  Guarding this shape is exactly what
    restores local confluence of the lift rule; [None] means "no
    leaf-pair fires", i.e. the frame is already reduced. *)
Definition lift_ok_b (children : list reduced_cft) : bool :=
  match children with
  | [RLeaf t1; RLeaf t2] =>
      match try_combine_leaves_full t1 t2 with
      | Some _ => false
      | None => true
      end
  | _ => true
  end.

(** [Prop] form of the lift guard carried by [RS_lift]. *)
Definition lift_children_ok (children : list reduced_cft) : Prop :=
  lift_ok_b children = true.

(* ------------------------------------------------------------
   Chain-construction witnesses, hoisted above [rewrite_step].

   The chaining rules R6/R12/R10 and the annotate rules R14/R15
   build a specific canonical chain, not merely one pinned by
   fields: this is what the kernel does ([last_two_step],
   [annotate_scan]) and what the paper intends (each rule produces
   *a* chain).  Pinning only the fields would leave [c']'s tokens,
   first-transfer, and tree shape free; since [kappa] canonicalizes
   only [Merging] clusters (not [Chaining]/[Arbitrage]/[Cycle]
   nodes, which it keeps and recurses), two field-equal-but-shape-
   distinct [c']s would have different [kappa], breaking local
   confluence mod kappa.  So the rules carry [c' = <builder>].
   ------------------------------------------------------------ *)

(** First transfer of a chain (leftmost leaf). *)
Definition ch_first_transfer (c : chain_tree) : transfer :=
  match c with
  | CT_transfer t => t
  | CT_node _ _ _ _ _ ft _ _ _ => ft
  end.

(** Relabel a chain, keeping every other field (annotate witness). *)
Definition set_chain_label
    (c : chain_tree) (l : construction_label) : chain_tree :=
  match c with
  | CT_transfer t => CT_transfer t
  | CT_node o d m ti to_ ft _ lc rc =>
      CT_node o d m ti to_ ft l lc rc
  end.

(** Leaf-onto-chain builders (R6/R12): prepend / append the leaf. *)
Definition prepend_leaf_chain (t : transfer) (c : chain_tree)
    : chain_tree :=
  CT_node (tr_source t) (ch_destination c) [tr_dest t]
          (tr_token t) (ch_token_out c) t Chaining
          (CT_transfer t) c.

Definition append_leaf_chain (c : chain_tree) (t : transfer)
    : chain_tree :=
  CT_node (ch_origin c) (tr_dest t) [tr_source t]
          (ch_token_in c) (tr_token t) (ch_first_transfer c) Chaining
          c (CT_transfer t).

(** Chain-chain sequential builder (R10). *)
Definition seq_chain (c1 c2 : chain_tree) : chain_tree :=
  CT_node (ch_origin c1) (ch_destination c2) [ch_destination c1]
          (ch_token_in c1) (ch_token_out c2) (ch_first_transfer c1)
          Chaining c1 c2.

(** The rewriting rules correspond one-to-one to
    Table 1 in the paper.  Each constructor is
    annotated with its rule number (R1--R15).
    R16 (post-rewriting validation) is modeled by
    the [validated_arbitrage] predicate below. *)

Inductive rewrite_step (from_ : address) : reduced_cft -> reduced_cft -> Prop :=
  (* ---- Leaf manipulation (R1--R5) ----
     Within a call-frame node.
     Maps to the Chain family. *)

  (** R1: Swap chain.  Two adjacent leaves with
      different tokens.  [eth_graph.ml:580] *)
  | RS_swap_chain : forall t1 t2 c addr,
      chainable t1 t2 ->
      is_burn t1 = is_mint t2 ->
      c = CT_node (tr_source t1) (tr_dest t2)
                  [tr_dest t1]
                  (tr_token t1) (tr_token t2)
                  t1
                  Chaining
                  (CT_transfer t1) (CT_transfer t2) ->
      rewrite_step from_
        (RTree addr [RLeaf t1; RLeaf t2])
        (RTree addr [RChain c])

  (** R2: Burn chain.  A burn transfer adjacent
      to a regular transfer.
      [eth_graph.ml:597--613] *)
  | RS_burn_chain : forall t_burn t c addr,
      is_burn t_burn = true ->
      is_mint t = false ->
      tr_dest t_burn = tr_source t ->
      c = CT_node (tr_source t_burn) (tr_dest t)
                  [tr_dest t_burn]
                  (tr_token t_burn) (tr_token t)
                  t_burn
                  TokenBurn
                  (CT_transfer t_burn) (CT_transfer t) ->
      rewrite_step from_
        (RTree addr [RLeaf t_burn; RLeaf t])
        (RTree addr [RChain c])

  (** R3: Mint chain.  A regular transfer adjacent
      to a mint transfer.
      [eth_graph.ml:636--670] *)
  | RS_mint_chain : forall t t_mint c addr,
      is_mint t_mint = true ->
      is_burn t = false ->
      tr_dest t = tr_source t_mint ->
      c = CT_node (tr_source t) (tr_dest t_mint)
                  [tr_dest t]
                  (tr_token t) (tr_token t_mint)
                  t
                  TokenMint
                  (CT_transfer t) (CT_transfer t_mint) ->
      rewrite_step from_
        (RTree addr [RLeaf t; RLeaf t_mint])
        (RTree addr [RChain c])

  (** R4: Pool round trip.  Two transfers between the
      same addresses in opposite directions; the
      sender sigma is external to the pair.  The result
      is [Chaining], like every other leaf rule: this
      layer is structural and names no query, so the
      closed shape is left for annotation (R14/R15) to
      judge, exactly as [try_ff_pair] emits the plain
      chain signal in the implementation.  Labelling
      here would also block annotation, whose premise is
      [is_labeled (ch_label c) = false].
      [eth_graph.ml:900--913] *)
  | RS_pool_cycle : forall t1 t2 c addr,
      tr_dest t1 = tr_source t2 ->
      tr_dest t2 = tr_source t1 ->
      tr_token t1 = tr_token t2 ->
      is_burn t1 = false ->
      is_mint t2 = false ->
      is_singleton_router (tr_dest t1) = false ->
      (tr_sender t1 <> tr_dest t1 \/
       tr_sender t2 <> tr_dest t2) ->
      c = CT_node (tr_source t1) (tr_dest t2)
                  [tr_dest t1]
                  (tr_token t1) (tr_token t2)
                  t1
                  Chaining
                  (CT_transfer t1) (CT_transfer t2) ->
      rewrite_step from_
        (RTree addr [RLeaf t1; RLeaf t2])
        (RTree addr [RChain c])

  (** R5: Singleton router chain.  Two same-token
      transfers through a designated router (e.g.,
      Uniswap V4 singleton).
      [eth_graph.ml:588--593] *)
  | RS_router_chain : forall t1 t2 c addr,
      tr_dest t1 = tr_source t2 ->
      tr_token t1 = tr_token t2 ->
      is_singleton_router (tr_dest t1) = true ->
      is_burn t1 = is_mint t2 ->
      c = CT_node (tr_source t1) (tr_dest t2)
                  [tr_dest t1]
                  (tr_token t1) (tr_token t2)
                  t1
                  Chaining
                  (CT_transfer t1) (CT_transfer t2) ->
      rewrite_step from_
        (RTree addr [RLeaf t1; RLeaf t2])
        (RTree addr [RChain c])

  (* ---- Chaining (R6, R10, R12) ----
     Chain a leaf with an existing chain, or
     chain two sequential chains. *)

  (** R6: leaf chaining onto an existing chain, within
      a single Chain construction.  Address adjacency
      is enough; no token check, because we are inside
      the same call frame and the chain has already
      committed to its token sequence.  The chain being
      extended need not be open: the implementation tests
      adjacency alone.
      [eth_graph.ml:946] *)
  | RS_leaf_chain : forall t c c' addr siblings,
      ch_label c' = Chaining ->
      ((tr_dest t = ch_origin c /\
        chain_transfers c' = t :: chain_transfers c /\
        ch_origin c' = tr_source t /\
        ch_destination c' = ch_destination c /\
        c' = prepend_leaf_chain t c) \/
       (ch_destination c = tr_source t /\
        chain_transfers c' = chain_transfers c ++ [t] /\
        ch_origin c' = ch_origin c /\
        ch_destination c' = tr_dest t /\
        tr_dest t <> ch_origin c /\
        c' = append_leaf_chain c t)) ->
      rewrite_step from_
        (RTree addr (siblings ++ [RLeaf t; RChain c]))
        (RTree addr (siblings ++ [RChain c']))

  (** R12: same shape as R6, but applied across call
      frames.  Crossing a call boundary, the token has
      to match the chain's endpoint token; otherwise
      we would conflate two distinct asset flows.  The
      token continuity check is what distinguishes R12
      from R6; like R6 it does not require openness. *)
  | RS_node_leaf_chain : forall t c c' addr siblings,
      ch_label c' = Chaining ->
      ((tr_dest t = ch_origin c /\
        tr_token t = ch_token_in c /\
        chain_transfers c' = t :: chain_transfers c /\
        ch_origin c' = tr_source t /\
        ch_destination c' = ch_destination c /\
        c' = prepend_leaf_chain t c) \/
       (ch_destination c = tr_source t /\
        ch_token_out c = tr_token t /\
        chain_transfers c' = chain_transfers c ++ [t] /\
        ch_origin c' = ch_origin c /\
        ch_destination c' = tr_dest t /\
        tr_dest t <> ch_origin c /\
        c' = append_leaf_chain c t)) ->
      rewrite_step from_
        (RTree addr (siblings ++ [RLeaf t; RChain c]))
        (RTree addr (siblings ++ [RChain c']))

  (** R10: Chain--chain sequential chaining.
      d(C1)=s(C2) with token continuity (or BalCont).
      Like R6 and R12 it places no openness condition on
      either operand: the implementation's chain-chain
      path ([fwd_chain]) tests the junction address and
      the token-or-balance continuity, nothing else.
      [eth_cft_fixpoint.ml:447] *)
  | RS_chain_seq : forall c1 c2 c' addr siblings,
      ch_destination c1 = ch_origin c2 ->
      (ch_token_out c1 = ch_token_in c2 \/
       bal_cont (ch_destination c1) c1 c2 = true) ->
      chain_transfers c' = chain_transfers c1 ++ chain_transfers c2 ->
      ch_label c' = Chaining ->
      ch_origin c' = ch_origin c1 ->
      ch_destination c' = ch_destination c2 ->
      c' = seq_chain c1 c2 ->
      rewrite_step from_
        (RTree addr (siblings ++ [RChain c1; RChain c2]))
        (RTree addr (siblings ++ [RChain c']))

  (* ---- Node manipulation (R11) ---- *)

  (** R11: Same-token leaf chain (node level).
      Two leaves with same token and adjacent
      addresses; the sender of t1 is external to
      the junction.  [eth_arbitrage.ml:98] *)
  | RS_same_token_chain : forall t1 t2 c addr,
      tr_dest t1 = tr_source t2 ->
      tr_token t1 = tr_token t2 ->
      is_burn t1 = false ->
      is_mint t2 = false ->
      is_singleton_router (tr_dest t1) = false ->
      tr_dest t2 <> tr_source t1 ->
      tr_sender t1 <> tr_dest t1 ->
      c = CT_node (tr_source t1) (tr_dest t2)
                  [tr_dest t1]
                  (tr_token t1) (tr_token t2)
                  t1
                  Chaining
                  (CT_transfer t1) (CT_transfer t2) ->
      rewrite_step from_
        (RTree addr [RLeaf t1; RLeaf t2])
        (RTree addr [RChain c])

  (* ---- Lifting ---- *)

  (** Promotes children of a subtree to siblings,
      eliminating intermediate tree nodes. *)
  | RS_lift : forall addr children parent_addr siblings,
      Forall (fun c => match c with
        | RLeaf _ | RChain _ => True
        | RTree _ _ => False
        end) children ->
      lift_children_ok children ->
      rewrite_step from_
        (RTree parent_addr (siblings ++ [RTree addr children]))
        (RTree parent_addr (siblings ++ children))

  (* ---- Endpoint merge (R7, R8, R9, R13) ---- *)

  (** R7: endpoint merge.  Two chains share the same
      source and destination (with s != d), they
      reconverge in one asset at that shared
      destination, and they pass through DIFFERENT
      intermediaries: the token each chain's middleman
      hands on ([ch_token_mid], the implementation's
      [amount0]) must differ, or the two chains would
      be the same route counted twice.  This is
      [merge_check ~require_first_transfer:false];
      R13 is the same predicate with the entry tokens
      pinned as well.  [eth_cft_fixpoint.ml:465] *)
  | RS_merge_endpoints : forall c1 c2 cm addr L M R,
      ch_origin c1 = ch_origin c2 ->
      ch_destination c1 = ch_destination c2 ->
      ch_origin c1 <> ch_destination c1 ->
      ch_token_out c1 = ch_token_out c2 ->
      ch_token_mid c1 <> ch_token_mid c2 ->
      ch_origin cm = ch_origin c1 ->
      ch_destination cm = ch_destination c1 ->
      ch_token_in cm = ch_token_in c1 ->
      ch_token_out cm = ch_token_out c2 ->
      ch_label cm = Merging ->
      ch_children cm = Some (c1, c2) ->
      chain_transfers cm = chain_transfers c1 ++ chain_transfers c2 ->
      rewrite_step from_
        (RTree addr (L ++ [RChain c1] ++ M ++ [RChain c2] ++ R))
        (RTree addr (L ++ M ++ [RChain cm] ++ R))

  (** R8: cycle merge-add.  Both chains are cycles at
      the same address (s = d), and the entry, middleman
      and output tokens all match ([merge_add_check]
      compares [first_transfer], [amount0] and
      [amount1]), or balance continuity holds at the
      shared origin.  Since the chains have identical
      shape, merging amounts to summing their amounts.
      This is the additive case, distinct from R7
      because it operates on cycles rather than on
      parallel paths.  No condition on either operand's
      label: [merge_add_check] runs in the leaf/chain
      phase, which the implementation saturates before
      annotation exists, so both operands are always
      unlabeled there.  [eth_cft_fixpoint.ml:509] *)
  | RS_merge_add : forall c1 c2 cm addr L M R,
      ch_origin c1 = ch_origin c2 ->
      ch_destination c1 = ch_destination c2 ->
      ch_origin c1 = ch_destination c1 ->
      ((ch_token_in c1 = ch_token_in c2 /\
        ch_token_mid c1 = ch_token_mid c2 /\
        ch_token_out c1 = ch_token_out c2) \/
       bal_cont (ch_origin c1) c1 c2 = true) ->
      ch_origin cm = ch_origin c1 ->
      ch_destination cm = ch_destination c1 ->
      ch_token_in cm = ch_token_in c1 ->
      ch_token_out cm = ch_token_out c2 ->
      ch_label cm = Merging ->
      ch_children cm = Some (c1, c2) ->
      chain_transfers cm = chain_transfers c1 ++ chain_transfers c2 ->
      rewrite_step from_
        (RTree addr (L ++ [RChain c1] ++ M ++ [RChain c2] ++ R))
        (RTree addr (L ++ M ++ [RChain cm] ++ R))

  (** R9: closed-cycle parallel merge (R7-closed).
      Two cycles at one address whose entry tokens and
      whose output tokens both agree.  Specialised
      sibling of R7 for closed chains, where R7's
      s != d premise blocks it; unlike R8 it says
      nothing about the middleman token, so it merges
      two closed routes that differ in the middle, and
      like R8 it says nothing about their labels.
      [eth_cft_fixpoint.ml:491] *)
  | RS_merge_closed_R9 : forall c1 c2 cm addr L M R,
      ch_origin c1 = ch_destination c1 ->
      ch_origin c2 = ch_destination c2 ->
      ch_origin c1 = ch_origin c2 ->
      ch_token_in c1 = ch_token_in c2 ->
      ch_token_out c1 = ch_token_out c2 ->
      ch_origin cm = ch_origin c1 ->
      ch_destination cm = ch_destination c1 ->
      ch_token_in cm = ch_token_in c1 ->
      ch_token_out cm = ch_token_out c2 ->
      ch_label cm = Merging ->
      ch_children cm = Some (c1, c2) ->
      chain_transfers cm = chain_transfers c1 ++ chain_transfers c2 ->
      rewrite_step from_
        (RTree addr (L ++ [RChain c1] ++ M ++ [RChain c2] ++ R))
        (RTree addr (L ++ M ++ [RChain cm] ++ R))

  (** R13: endpoint merge with pinned entry tokens.
      R7's premises plus [tau_in(C1) = tau_in(C2)]: the
      two parallel paths must also leave the shared
      origin in the same asset.  The implementation
      reaches R13 exactly when both chain origins are
      actors of the frame, where the entry token is
      determined and can be required to agree; where it
      is not, R7 applies with the entry tokens free.
      This is [merge_check ~require_first_transfer:true].
      [eth_cft_fixpoint.ml:465] *)
  | RS_merge_node : forall c1 c2 cm addr L M R,
      ch_origin c1 = ch_origin c2 ->
      ch_destination c1 = ch_destination c2 ->
      ch_origin c1 <> ch_destination c1 ->
      ch_token_out c1 = ch_token_out c2 ->
      ch_token_mid c1 <> ch_token_mid c2 ->
      ch_token_in c1 = ch_token_in c2 ->
      ch_origin cm = ch_origin c1 ->
      ch_destination cm = ch_destination c1 ->
      ch_token_in cm = ch_token_in c1 ->
      ch_token_out cm = ch_token_out c2 ->
      ch_label cm = Merging ->
      ch_children cm = Some (c1, c2) ->
      chain_transfers cm = chain_transfers c1 ++ chain_transfers c2 ->
      rewrite_step from_
        (RTree addr (L ++ [RChain c1] ++ M ++ [RChain c2] ++ R))
        (RTree addr (L ++ M ++ [RChain cm] ++ R))

  (* ---- Annotation (R14, R15) ----
     Both rules see the transaction sender [from].
     The split on whether [from] is inside or outside
     the cycle is semantic, not cosmetic: R14 says
     an external orchestrator captured value (we call
     this Arbitrage), R15 says the cycle was driven
     by a contract sitting inside it (we call this
     Cycle, but not Arbitrage in our sense).  This is
     why R14 and R15 never compete on the same input:
     the [from] condition partitions the cases.
     [eth_tools.ml:1265] *)

  (** R14: Arbitrage label.  s(C) = d(C), tokens match
      modulo =_tau, and the orchestrator [from] is
      either outside the cycle or equal to its source.
      This is the EOA-initiated case, where an external
      account captured the round-trip value. *)
  | RS_annotate_arb : forall c c' addr L R,
      ch_origin c = ch_destination c ->
      token_equiv (ch_token_in c) (ch_token_out c) = true ->
      ch_origin c' = ch_origin c ->
      ch_destination c' = ch_destination c ->
      ch_token_in c' = ch_token_in c ->
      ch_token_out c' = ch_token_out c ->
      is_labeled (ch_label c) = false ->
      ch_label c' = Arbitrage ->
      (address_in_chain from_ c = false \/
       ch_origin c = from_) ->
      chain_transfers c' = chain_transfers c ->
      wrap_unwrap c = false ->
      c' = set_chain_label c Arbitrage ->
      rewrite_step from_
        (RTree addr (L ++ [RChain c] ++ R))
        (RTree addr (L ++ [RChain c'] ++ R))

  (** R15: Cycle label.  s(C) = d(C) and [from] sits
      inside the cycle but is not its source.  We do not
      claim arbitrage here: a contract took the round
      trip, but the value capture is internal to the cycle
      and not extracted by an external orchestrator.  The
      [ch_origin c <> from_] guard makes R15 mutually
      exclusive with R14 (whose second disjunct handles
      [ch_origin c = from_]); since [kappa] preserves
      labels, an overlap would be a label-divergent
      critical pair it could not join. *)
  | RS_annotate_cyc : forall c c' addr L R,
      ch_origin c = ch_destination c ->
      ch_origin c' = ch_origin c ->
      ch_destination c' = ch_destination c ->
      ch_token_in c' = ch_token_in c ->
      ch_token_out c' = ch_token_out c ->
      is_labeled (ch_label c) = false ->
      ch_label c' = Cycle ->
      address_in_chain from_ c = true ->
      (token_equiv (ch_token_in c) (ch_token_out c) = false \/
       wrap_unwrap c = true \/
       ch_origin c <> from_) ->
      chain_transfers c' = chain_transfers c ->
      c' = set_chain_label c Cycle ->
      rewrite_step from_
        (RTree addr (L ++ [RChain c] ++ R))
        (RTree addr (L ++ [RChain c'] ++ R))

  (** Congruence: a step inside any child lifts to a step
      of the whole tree, so the relation reaches nested
      subtrees, not only the root.  This is the in-place
      mechanization of "R applies at any position": with
      it [rewrite_step] IS the paper's R.  Needed for the
      breadth of O0 and the nested critical pairs of O3. *)
  | RS_under : forall addr L T T' R,
      rewrite_step from_ T T' ->
      rewrite_step from_
        (RTree addr (L ++ [T] ++ R))
        (RTree addr (L ++ [T'] ++ R)).

Inductive rewrite_star (from_ : address)
    : reduced_cft -> reduced_cft -> Prop :=
  | RS_refl : forall t, rewrite_star from_ t t
  | RS_trans : forall t1 t2 t3,
      rewrite_step from_ t1 t2 ->
      rewrite_star from_ t2 t3 ->
      rewrite_star from_ t1 t3.

(* ============================================================
   Section 6: Classification (the verdict)
   ============================================================ *)

Inductive reason : Type :=
  | NoCycles | Leftovers | FinalNeg
  | FinalMixed | BalanceMixed | NegProfit.

Inductive verdict : Type :=
  | VNone | VWarning | VArbitrage.

Definition reason_eq_dec :
  forall (r1 r2 : reason), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.

Definition verdict_eq_dec :
  forall (v1 v2 : verdict), {v1 = v2} + {v1 <> v2}.
Proof. decide equality. Defined.

Fixpoint has_reason (r : reason) (rs : list reason) : bool :=
  match rs with
  | [] => false
  | r' :: rest =>
      if reason_eq_dec r r' then true
      else has_reason r rest
  end.

Definition classify (reasons : list reason) : verdict :=
  if has_reason NoCycles reasons then VNone
  else if has_reason Leftovers reasons then VWarning
  else if has_reason FinalNeg reasons then VWarning
  else if has_reason FinalMixed reasons then VWarning
  else VArbitrage.

(* ============================================================
   Section 7: Elementary properties of has_reason and classify
   ============================================================ *)

Lemma has_reason_In :
  forall r rs, has_reason r rs = true <-> In r rs.
Proof.
  intros r rs. induction rs as [| r' rest IH].
  - simpl. split; intros H; discriminate + contradiction.
  - simpl. destruct (reason_eq_dec r r') as [Heq | Hneq].
    + subst. split; intros _; auto.
    + rewrite IH. split; intros H.
      * right. exact H.
      * destruct H as [H | H].
        -- subst. exfalso. apply Hneq. reflexivity.
        -- exact H.
Qed.

Lemma has_reason_not_In :
  forall r rs, has_reason r rs = false <-> ~ In r rs.
Proof.
  intros r rs. split.
  - intros H Hin. apply has_reason_In in Hin.
    rewrite H in Hin. discriminate.
  - intros H. destruct (has_reason r rs) eqn:E; auto.
    apply has_reason_In in E. contradiction.
Qed.

Lemma classify_arbitrage_iff :
  forall reasons,
    classify reasons = VArbitrage <->
    (has_reason NoCycles reasons = false /\
     has_reason Leftovers reasons = false /\
     has_reason FinalNeg reasons = false /\
     has_reason FinalMixed reasons = false).
Proof.
  intros reasons. unfold classify.
  destruct (has_reason NoCycles reasons) eqn:E1;
  destruct (has_reason Leftovers reasons) eqn:E2;
  destruct (has_reason FinalNeg reasons) eqn:E3;
  destruct (has_reason FinalMixed reasons) eqn:E4;
  split; intros H; try discriminate; auto;
  try (destruct H as [H1 [H2 [H3 H4]]]; discriminate).
Qed.

Lemma classify_no_false_reasons :
  forall reasons,
    classify reasons = VArbitrage ->
    ~ In NoCycles reasons /\
    ~ In Leftovers reasons /\
    ~ In FinalNeg reasons /\
    ~ In FinalMixed reasons.
Proof.
  intros reasons H.
  apply classify_arbitrage_iff in H.
  destruct H as [H1 [H2 [H3 H4]]].
  repeat split; apply has_reason_not_In; auto.
Qed.

(* ############################################################
   Part II -- Foundational invariants (measure, preservation, walk correspondence)
   ############################################################ *)

(* ============================================================
   Section 8: Well-foundedness of lt_lex
   ============================================================ *)

Definition lt_lex (p1 p2 : nat * nat) : Prop :=
  fst p1 < fst p2 \/
  (fst p1 = fst p2 /\ snd p1 < snd p2).

Lemma lt_lex_wf : well_founded lt_lex.
Proof.
  unfold lt_lex.
  intros [a b]. revert b.
  induction a as [a IHa] using (well_founded_induction lt_wf).
  induction b as [b IHb] using (well_founded_induction lt_wf).
  constructor. intros [a' b'] [Hlt | [Heq Hlt]].
  - apply IHa. simpl in Hlt. exact Hlt.
  - simpl in Heq. rewrite Heq. apply IHb. simpl in Hlt. exact Hlt.
Qed.

(* ============================================================
   Section 9: Measure and structural lemmas
   ============================================================ *)

Fixpoint count_unlabeled (t : reduced_cft) : nat :=
  match t with
  | RLeaf _ => 0
  | RChain c =>
      if is_labeled (ch_label c) then 0 else 1
  | RTree _ children =>
      fold_left (fun acc child => acc + count_unlabeled child)
                children 0
  end.

Fixpoint count_children (t : reduced_cft) : nat :=
  match t with
  | RLeaf _ => 0
  | RChain _ => 0
  | RTree _ children =>
      length children +
      fold_left (fun acc child => acc + count_children child)
                children 0
  end.

Definition measure (t : reduced_cft) : nat * nat :=
  (count_unlabeled t, count_children t).

(** Key lemma: a labeled chain contributes 0 to
    count_unlabeled. *)
Lemma labeled_implies_zero :
  forall (c' : chain_tree),
    is_labeled (ch_label c') = true ->
    count_unlabeled (RChain c') = 0.
Proof.
  intros c' H. simpl. rewrite H. reflexivity.
Qed.

(* ============================================================
   Section 10: Preservation -- no rule fabricates an edge
   ============================================================ *)

(** Theorem 1: Preservation.
    Every rewrite step preserves the set of
    leaf transfers: no rule fabricates an edge.
    Chaining concatenates existing transfers,
    lifting repositions them, merging records
    their union (precondition), and annotation
    only changes the label (precondition). *)

Lemma flat_map_app_dist :
  forall {A B : Type} (f : A -> list B) (l1 l2 : list A),
    flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  intros A B f l1. induction l1 as [| x rest IH];
    intros l2; simpl.
  - reflexivity.
  - rewrite IH, app_assoc. reflexivity.
Qed.

Lemma preservation_step :
  forall from_ T0 Tf,
    rewrite_step from_ T0 Tf ->
    forall t, In t (rcft_transfers Tf) ->
              In t (rcft_transfers T0).
Proof.
  intros from_ T0 Tf Hstep.
  induction Hstep; intros u Hin; subst; simpl in *.
  - (* RS_swap_chain (R1) *) exact Hin.
  - (* RS_burn_chain (R2) *) exact Hin.
  - (* RS_mint_chain (R3) *) exact Hin.
  - (* RS_pool_cycle (R4) *) exact Hin.
  - (* RS_router_chain (R5) *) exact Hin.
  - (* RS_leaf_chain (R6) *)
    rewrite !flat_map_app_dist in *. simpl in *. rewrite !app_nil_r in *.
    apply in_app_iff in Hin. apply in_app_iff.
    destruct Hin as [Hin | Hin]; [left; exact Hin | right].
    match goal with Hor : _ \/ _ |- _ =>
      destruct Hor as [(_ & Heq & _) | (_ & Heq & _)] end;
      rewrite Heq in Hin.
    + exact Hin.
    + apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      * right. exact Hin.
      * simpl in Hin. destruct Hin as [Heq2 | []].
        subst. left. reflexivity.
  - (* RS_node_leaf_chain (R12) *)
    rewrite !flat_map_app_dist in *. simpl in *. rewrite !app_nil_r in *.
    apply in_app_iff in Hin. apply in_app_iff.
    destruct Hin as [Hin | Hin]; [left; exact Hin | right].
    match goal with Hor : _ \/ _ |- _ =>
      destruct Hor as [(_ & _ & Heq & _) | (_ & _ & Heq & _)] end;
      rewrite Heq in Hin.
    + exact Hin.
    + apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      * right. exact Hin.
      * simpl in Hin. destruct Hin as [Heq2 | []].
        subst. left. reflexivity.
  - (* RS_chain_seq (R10) *)
    rewrite !flat_map_app_dist in *. simpl in *. rewrite !app_nil_r in *.
    apply in_app_iff in Hin. apply in_app_iff.
    destruct Hin as [Hin | Hin]; [left; exact Hin | right].
    exact Hin.
  - (* RS_same_token_chain (R11) *) exact Hin.
  - (* RS_lift *)
    rewrite flat_map_app_dist in *. rewrite in_app_iff in *.
    destruct Hin as [Hin | Hin]; [left; exact Hin | right].
    simpl. rewrite app_nil_r. exact Hin.
  - (* RS_merge_endpoints (R7) *)
    repeat (rewrite !flat_map_app_dist in *; simpl in *).
    match goal with H : chain_transfers _ = _ |- _ => rewrite H in Hin end.
    rewrite !in_app_iff in *. tauto.
  - (* RS_merge_add (R8) *)
    repeat (rewrite !flat_map_app_dist in *; simpl in *).
    match goal with H : chain_transfers _ = _ |- _ => rewrite H in Hin end.
    rewrite !in_app_iff in *. tauto.
  - (* RS_merge_closed_R9 *)
    repeat (rewrite !flat_map_app_dist in *; simpl in *).
    match goal with H : chain_transfers _ = _ |- _ => rewrite H in Hin end.
    rewrite !in_app_iff in *. tauto.
  - (* RS_merge_node (R13) *)
    repeat (rewrite !flat_map_app_dist in *; simpl in *).
    match goal with H : chain_transfers _ = _ |- _ => rewrite H in Hin end.
    rewrite !in_app_iff in *. tauto.
  - (* RS_annotate_arb (R14) *)
    rewrite !flat_map_app_dist in *. simpl in *.
    match goal with H : chain_transfers _ = _ |- _ => rewrite H in Hin end.
    exact Hin.
  - (* RS_annotate_cyc (R15) *)
    rewrite !flat_map_app_dist in *. simpl in *.
    match goal with H : chain_transfers _ = _ |- _ => rewrite H in Hin end.
    exact Hin.
  - (* RS_under (congruence) *)
    rewrite !flat_map_app_dist in *. simpl in *.
    rewrite ?app_nil_r in *. rewrite !in_app_iff in *.
    destruct Hin as [Hin | [Hin | Hin]].
    + left. exact Hin.
    + right. left. apply IHHstep. exact Hin.
    + right. right. exact Hin.
Qed.

Lemma preservation :
  forall from_ T0 Tf,
    rewrite_star from_ T0 Tf ->
    forall t, In t (rcft_transfers Tf) ->
              In t (rcft_transfers T0).
Proof.
  intros from_ T0 Tf Hstar. induction Hstar as [T | T1 T2 T3 Hstep Hstar IH].
  - intros t Hin. exact Hin.
  - intros t Hin. apply (preservation_step from_ T1 T2 Hstep).
    exact (IH t Hin).
Qed.

(* ------------------------------------------------------------
   Conservation: preservation in its multiset form.

   [preservation] above is set-level ([In]-inclusion).  The
   rules in fact only ever REARRANGE transfers, never drop or
   duplicate one, so the transfer MULTISET is invariant.  This
   is what rules out a reduct that witnesses one input transfer
   twice, and it is the conserved observable the verdict reads
   (Part VI).
   ------------------------------------------------------------ *)

Lemma perm_merge_shape :
  forall (A : Type) (fL cc1 fM cc2 fR : list A),
    Permutation (fL ++ cc1 ++ fM ++ cc2 ++ fR)
                (fL ++ fM ++ (cc1 ++ cc2) ++ fR).
Proof.
  intros A fL cc1 fM cc2 fR.
  apply Permutation_app_head.
  rewrite <- (app_assoc cc1 cc2 fR).
  rewrite (app_assoc cc1 fM (cc2 ++ fR)).
  rewrite (app_assoc fM cc1 (cc2 ++ fR)).
  apply Permutation_app_tail.
  apply Permutation_app_comm.
Qed.

(** The transfer MULTISET is invariant under one rewrite
    step: every rule merely rearranges transfers.  This
    strengthens [preservation_step] from [In]-inclusion to a
    [Permutation]. *)
Lemma rcft_transfers_perm :
  forall from_ T0 Tf,
    rewrite_step from_ T0 Tf ->
    Permutation (rcft_transfers T0) (rcft_transfers Tf).
Proof.
  intros from_ T0 Tf Hstep.
  induction Hstep; subst; simpl in *.
  - (* R1 *) apply Permutation_refl.
  - (* R2 *) apply Permutation_refl.
  - (* R3 *) apply Permutation_refl.
  - (* R4 *) apply Permutation_refl.
  - (* R5 *) apply Permutation_refl.
  - (* R6 *)
    rewrite !flat_map_app_dist. simpl. rewrite ?app_nil_r.
    match goal with Hor : _ \/ _ |- _ =>
      destruct Hor as [(_ & Heq & _) | (_ & Heq & _)] end;
      rewrite Heq.
    + apply Permutation_refl.
    + apply Permutation_app_head. apply Permutation_cons_append.
  - (* R12 *)
    rewrite !flat_map_app_dist. simpl. rewrite ?app_nil_r.
    match goal with Hor : _ \/ _ |- _ =>
      destruct Hor as [(_ & _ & Heq & _) | (_ & _ & Heq & _)] end;
      rewrite Heq.
    + apply Permutation_refl.
    + apply Permutation_app_head. apply Permutation_cons_append.
  - (* R10 *)
    rewrite !flat_map_app_dist. simpl. rewrite ?app_nil_r.
    apply Permutation_refl.
  - (* R11 *) apply Permutation_refl.
  - (* RS_lift *)
    rewrite !flat_map_app_dist. simpl. rewrite ?app_nil_r.
    apply Permutation_refl.
  - (* R7 *)
    repeat (rewrite !flat_map_app_dist; simpl). rewrite ?app_nil_r.
    match goal with H : chain_transfers _ = _ |- _ => rewrite H end.
    apply perm_merge_shape.
  - (* R8 *)
    repeat (rewrite !flat_map_app_dist; simpl). rewrite ?app_nil_r.
    match goal with H : chain_transfers _ = _ |- _ => rewrite H end.
    apply perm_merge_shape.
  - (* R9 *)
    repeat (rewrite !flat_map_app_dist; simpl). rewrite ?app_nil_r.
    match goal with H : chain_transfers _ = _ |- _ => rewrite H end.
    apply perm_merge_shape.
  - (* R13 *)
    repeat (rewrite !flat_map_app_dist; simpl). rewrite ?app_nil_r.
    match goal with H : chain_transfers _ = _ |- _ => rewrite H end.
    apply perm_merge_shape.
  - (* R14 *)
    rewrite !flat_map_app_dist. simpl.
    match goal with H : chain_transfers _ = _ |- _ => rewrite H end.
    apply Permutation_refl.
  - (* R15 *)
    rewrite !flat_map_app_dist. simpl.
    match goal with H : chain_transfers _ = _ |- _ => rewrite H end.
    apply Permutation_refl.
  - (* RS_under *)
    rewrite !flat_map_app_dist. simpl. rewrite ?app_nil_r.
    apply Permutation_app_head. apply Permutation_app_tail. exact IHHstep.
Qed.

(** Conservation, iterated: a reachable tree carries a permutation
    of the initial transfer multiset. *)
Lemma rcft_transfers_perm_star :
  forall from_ T Tf,
    rewrite_star from_ T Tf ->
    Permutation (rcft_transfers T) (rcft_transfers Tf).
Proof.
  intros from_ T Tf Hstar.
  induction Hstar as [t | t1 t2 t3 Hstep _ IH].
  - apply Permutation_refl.
  - eapply perm_trans;
      [apply (rcft_transfers_perm from_ t1 t2 Hstep) | exact IH].
Qed.

(** A chain of a tree owns a SUB-MULTISET of the tree's transfers: its
    leaves, together with the rest of the tree, permute the whole.  At an
    [RTree] node the chain sits inside one child, and the siblings supply
    the remainder. *)
Lemma chain_in_rcft_submultiset :
  forall c T,
    chain_in_rcft c T ->
    exists rest, Permutation (chain_transfers c ++ rest) (rcft_transfers T).
Proof.
  intros c T Hin.
  induction Hin as [c | c addr children child Hch Hcir IH].
  - exists []. rewrite app_nil_r. apply Permutation_refl.
  - destruct IH as [rest Hperm].
    destruct (in_split child children Hch) as [pre [post Hsplit]].
    exists (rest ++ (flat_map rcft_transfers pre
                     ++ flat_map rcft_transfers post)).
    cbn [rcft_transfers]. rewrite Hsplit, flat_map_app_dist. cbn [flat_map].
    rewrite app_assoc.
    eapply perm_trans; [apply Permutation_app_tail; exact Hperm |].
    apply Permutation_app_swap_app.
Qed.

(** ANTI-FABRICATION, multiset form.  Every chain of a reachable tree is
    backed by a sub-multiset of the ORIGINAL transfers: conservation
    along the reduction ([rcft_transfers_perm_star]) composed with the
    sub-multiset property above.  Multiplicity matters here -- the
    set-level [In] statement would permit one input transfer to witness
    two edges of a reported cycle, and this rules that out. *)
Lemma chain_submultiset_of_input :
  forall from_ T0 Tf c,
    rewrite_star from_ T0 Tf ->
    chain_in_rcft c Tf ->
    exists rest, Permutation (chain_transfers c ++ rest) (rcft_transfers T0).
Proof.
  intros from_ T0 Tf c Hstar Hin.
  destruct (chain_in_rcft_submultiset c Tf Hin) as [rest Hperm].
  exists rest.
  eapply perm_trans; [exact Hperm |].
  apply Permutation_sym.
  apply (rcft_transfers_perm_star from_ T0 Tf Hstar).
Qed.

(** NO FABRICATED TRANSFERS.  The rewriting cannot invent an edge: every
    transfer of every chain of every reachable tree is one of the
    transaction's original transfers, with multiplicity.  Reported cycles
    are therefore assembled from the input trace and nothing else -- the
    reduction re-brackets the transfer multiset, it does not add to it. *)
Corollary no_fabricated_transfers :
  forall from_ T0 Tf c,
    rewrite_star from_ T0 Tf ->
    chain_in_rcft c Tf ->
    (exists rest,
        Permutation (chain_transfers c ++ rest) (rcft_transfers T0)) /\
    Forall (fun t => In t (rcft_transfers T0)) (chain_transfers c).
Proof.
  intros from_ T0 Tf c Hstar Hin.
  destruct (chain_submultiset_of_input from_ T0 Tf c Hstar Hin)
    as [rest Hperm].
  split; [exists rest; exact Hperm |].
  apply Forall_forall. intros t Ht.
  eapply Permutation_in; [exact Hperm |].
  apply in_or_app. left. exact Ht.
Qed.

(* ============================================================
   Section 11: Walk correspondence (single rule)

   [preservation] above gives transfer-set inclusion: every
   transfer in the rewritten tree was already in the original.
   That is the load-bearing fact for soundness.

   The paper's Theorem 1 makes a stronger claim: chains in
   reduced CFTs correspond to walks in the original transfer
   graph.  This section mechanizes the claim for the leaf-pair
   construction rules (R1, R2, R3, R4, R5, R11), which originate
   chains.  Each rule's premise gives tr_dest t1 = tr_source t2
   directly (or via [chainable]), so the resulting 2-leaf chain
   trivially forms a valid walk.

   Section 8c below extends the claim to all 15 rules using
   multi-walk semantics: a chain corresponds to a *set* of
   walks (singleton for sequential chains, larger for merged
   chains).  Together, Sections 8b and 8c fully mechanize
   Theorem 1's walk-correspondence claim.
   ============================================================ *)

(** [chain_walk c] holds when the leaves of [c], read
    left-to-right, form a valid walk in the transfer graph
    (consecutive transfers chain at an address). *)
Definition chain_walk (c : chain_tree) : Prop :=
  valid_walk (chain_transfers c).

(** A two-leaf chain is a valid walk iff its leaves chain. *)
Lemma chain_walk_two :
  forall t1 t2 o d m ti to_ ft lbl,
    tr_dest t1 = tr_source t2 ->
    chain_walk
      (CT_node o d m ti to_ ft lbl
               (CT_transfer t1) (CT_transfer t2)).
Proof.
  intros. unfold chain_walk. simpl. split; auto.
Qed.

(** R1: Swap chain.  [chainable t1 t2] gives
    [tr_dest t1 = tr_source t2], so the constructed
    2-leaf chain is a walk. *)
Lemma chain_walk_swap :
  forall t1 t2 c (addr : address),
    chainable t1 t2 ->
    c = CT_node (tr_source t1) (tr_dest t2)
                [tr_dest t1]
                (tr_token t1) (tr_token t2)
                t1
                Chaining
                (CT_transfer t1) (CT_transfer t2) ->
    chain_walk c.
Proof.
  intros t1 t2 c addr [Hch _] Hc. subst.
  apply chain_walk_two. exact Hch.
Qed.

(** R2: Burn chain. *)
Lemma chain_walk_burn :
  forall t_burn t c (addr : address),
    is_burn t_burn = true ->
    tr_dest t_burn = tr_source t ->
    c = CT_node (tr_source t_burn) (tr_dest t)
                [tr_dest t_burn]
                (tr_token t_burn) (tr_token t)
                t_burn
                TokenBurn
                (CT_transfer t_burn) (CT_transfer t) ->
    chain_walk c.
Proof.
  intros. subst. apply chain_walk_two. assumption.
Qed.

(** R3: Mint chain. *)
Lemma chain_walk_mint :
  forall t t_mint c (addr : address),
    is_mint t_mint = true ->
    tr_dest t = tr_source t_mint ->
    c = CT_node (tr_source t) (tr_dest t_mint)
                [tr_dest t]
                (tr_token t) (tr_token t_mint)
                t
                TokenMint
                (CT_transfer t) (CT_transfer t_mint) ->
    chain_walk c.
Proof.
  intros. subst. apply chain_walk_two. assumption.
Qed.

(** R5: Singleton router chain. *)
Lemma chain_walk_router :
  forall t1 t2 c (addr : address),
    tr_dest t1 = tr_source t2 ->
    tr_token t1 = tr_token t2 ->
    is_singleton_router (tr_dest t1) = true ->
    c = CT_node (tr_source t1) (tr_dest t2)
                [tr_dest t1]
                (tr_token t1) (tr_token t2)
                t1
                Chaining
                (CT_transfer t1) (CT_transfer t2) ->
    chain_walk c.
Proof.
  intros. subst. apply chain_walk_two. assumption.
Qed.

(** R11: Same-token leaf chain. *)
Lemma chain_walk_same_token :
  forall t1 t2 c (addr : address),
    tr_dest t1 = tr_source t2 ->
    tr_token t1 = tr_token t2 ->
    c = CT_node (tr_source t1) (tr_dest t2)
                [tr_dest t1]
                (tr_token t1) (tr_token t2)
                t1
                Chaining
                (CT_transfer t1) (CT_transfer t2) ->
    chain_walk c.
Proof.
  intros. subst. apply chain_walk_two. assumption.
Qed.

(* ============================================================
   Section 12: Walk correspondence (all rules, multi-walk)

   Section 8b mechanized [chain_walk] (single linear walk) for
   the leaf-pair rules.  The merge rules (R7/R8/R9/R13) produce
   chains whose leaves do NOT form a single linear walk: a
   merged chain represents two parallel paths a -> b through
   different intermediaries (R7) or two cycles at the same
   address (R8 with s = d).

   Theorem 1 of the paper says "walk-set" (plural).  We
   formalize that here: a chain corresponds to a list of valid
   walks whose concatenation is the chain's leaves.  Sequential
   chains have a singleton walk-set; merged chains have two or
   more walks.  This covers all 15 rules uniformly.
   ============================================================ *)

Definition walk_set := list walk.

(** [chain_walks c] holds when the leaves of [c] decompose into
    a list of valid walks.  The decomposition is existentially
    quantified; per-rule lemmas construct it explicitly. *)
Definition chain_walks (c : chain_tree) : Prop :=
  exists ws : walk_set,
    Forall valid_walk ws /\
    chain_transfers c = concat ws.

(** Single-walk lift: a [chain_walk] gives a singleton walk-set. *)
Lemma chain_walk_implies_walks :
  forall c, chain_walk c -> chain_walks c.
Proof.
  intros c Hcw. unfold chain_walks, chain_walk in *.
  exists [chain_transfers c]. split.
  - constructor; [exact Hcw | constructor].
  - simpl. rewrite app_nil_r. reflexivity.
Qed.

(** Walk-set concat: two chain-walks-decomposable chains, when
    their transfer-lists are concatenated, decompose into the
    concatenated walk-set.  This is the engine for both merge
    rules (R7, R8, R9, R13) and sequential chain combination (R10). *)
Lemma chain_walks_app :
  forall c1 c2 cm,
    chain_walks c1 ->
    chain_walks c2 ->
    chain_transfers cm = chain_transfers c1 ++ chain_transfers c2 ->
    chain_walks cm.
Proof.
  intros c1 c2 cm [ws1 [Hw1 Heq1]] [ws2 [Hw2 Heq2]] Hcm.
  exists (ws1 ++ ws2). split.
  - apply Forall_app. split; assumption.
  - rewrite Hcm, Heq1, Heq2. symmetry. apply concat_app.
Qed.

(** Single-leaf prepend: prepending one transfer as its own
    singleton walk to an existing walk-set.  Used by R6 and
    R12 (leaf-chain) when the rule's premise selects the
    prepend disjunct. *)
Lemma chain_walks_cons_transfer :
  forall t c c',
    chain_walks c ->
    chain_transfers c' = t :: chain_transfers c ->
    chain_walks c'.
Proof.
  intros t c c' [ws [Hw Heq]] Hc'.
  exists ([t] :: ws). split.
  - constructor; [constructor | assumption].
  - rewrite Hc'. simpl. rewrite Heq. reflexivity.
Qed.

(** Symmetric append form. *)
Lemma chain_walks_snoc_transfer :
  forall t c c',
    chain_walks c ->
    chain_transfers c' = chain_transfers c ++ [t] ->
    chain_walks c'.
Proof.
  intros t c c' [ws [Hw Heq]] Hc'.
  exists (ws ++ [[t]]). split.
  - apply Forall_app. split; [assumption | constructor; [constructor | constructor]].
  - rewrite Hc'. rewrite Heq. rewrite concat_app. simpl. reflexivity.
Qed.

(** Equality preservation: relabel-only rules (R14, R15) keep
    the leaf list intact, so the walk-set is inherited. *)
Lemma chain_walks_eq_transfers :
  forall c c',
    chain_walks c ->
    chain_transfers c' = chain_transfers c ->
    chain_walks c'.
Proof.
  intros c c' [ws [Hw Heq]] Hc'.
  exists ws. split; [assumption | rewrite Hc'; assumption].
Qed.

(* ============================================================
   Canonical maximal walk decomposition.

   [split_walks ts] cuts a transfer list into its maximal runs of
   address-adjacent transfers ([tr_dest t = tr_source t']);
   [count_breaks ts] counts the cut points.  Unlike the free
   existential [chain_walks], this decomposition is CANONICAL: its
   size is pinned to the number of non-chaining boundaries
   ([length (split_walks ts) = 1 + count_breaks ts]), and a
   break-free list is a single connected walk.  It is the engine
   for the connectivity characterization of Definition 5.
   ============================================================ *)

Fixpoint count_breaks (ts : list transfer) : nat :=
  match ts with
  | [] => 0
  | [_] => 0
  | t1 :: ((t2 :: _) as rest) =>
      (if address_eq_dec (tr_dest t1) (tr_source t2) then 0 else 1)
        + count_breaks rest
  end.

Fixpoint split_walks (ts : list transfer) : list walk :=
  match ts with
  | [] => []
  | [t] => [[t]]
  | t1 :: ((t2 :: _) as rest) =>
      match split_walks rest with
      | [] => [[t1]]
      | w :: ws =>
          if address_eq_dec (tr_dest t1) (tr_source t2)
          then (t1 :: w) :: ws
          else [t1] :: w :: ws
      end
  end.

Lemma split_walks_cons2 :
  forall t t2 rest',
    split_walks (t :: t2 :: rest') =
      match split_walks (t2 :: rest') with
      | [] => [[t]]
      | w :: ws =>
          if address_eq_dec (tr_dest t) (tr_source t2)
          then (t :: w) :: ws else [t] :: w :: ws
      end.
Proof. reflexivity. Qed.

Lemma count_breaks_cons2 :
  forall t t2 rest',
    count_breaks (t :: t2 :: rest') =
      (if address_eq_dec (tr_dest t) (tr_source t2) then 0 else 1)
      + count_breaks (t2 :: rest').
Proof. reflexivity. Qed.

Lemma split_walks_cons_nonempty :
  forall t ts, split_walks (t :: ts) <> [].
Proof.
  intros t ts. destruct ts as [| t2 rest].
  - cbn [split_walks]. discriminate.
  - rewrite split_walks_cons2.
    destruct (split_walks (t2 :: rest)) as [| w ws]; [discriminate|].
    destruct (address_eq_dec (tr_dest t) (tr_source t2)); discriminate.
Qed.

Lemma split_walks_head :
  forall t ts, exists tl ws, split_walks (t :: ts) = (t :: tl) :: ws.
Proof.
  intros t ts. destruct ts as [| t2 rest].
  - cbn [split_walks]. exists [], []. reflexivity.
  - rewrite split_walks_cons2.
    destruct (split_walks (t2 :: rest)) as [| w ws] eqn:E.
    + exists [], []. reflexivity.
    + destruct (address_eq_dec (tr_dest t) (tr_source t2)).
      * exists w, ws. reflexivity.
      * exists [], (w :: ws). reflexivity.
Qed.

Lemma split_walks_concat :
  forall ts, concat (split_walks ts) = ts.
Proof.
  induction ts as [| t rest IH]; [reflexivity|].
  destruct rest as [| t2 rest'].
  - reflexivity.
  - rewrite split_walks_cons2.
    destruct (split_walks (t2 :: rest')) as [| w ws] eqn:E.
    + exfalso. exact (split_walks_cons_nonempty t2 rest' E).
    + cbn [concat] in IH.
      destruct (address_eq_dec (tr_dest t) (tr_source t2)); cbn [concat].
      * rewrite <- app_comm_cons, IH. reflexivity.
      * rewrite IH. reflexivity.
Qed.

Lemma split_walks_valid :
  forall ts, Forall valid_walk (split_walks ts).
Proof.
  induction ts as [| t rest IH]; [constructor|].
  destruct rest as [| t2 rest'].
  - simpl. constructor; [exact I | constructor].
  - rewrite split_walks_cons2.
    destruct (split_walks (t2 :: rest')) as [| w ws] eqn:E.
    + exfalso. exact (split_walks_cons_nonempty t2 rest' E).
    + destruct (split_walks_head t2 rest') as [tl [ws2 Eh]].
      rewrite E in Eh. inversion Eh; subst.
      destruct (address_eq_dec (tr_dest t) (tr_source t2)) as [Hcadj | Hcadj].
      * inversion IH as [| a b Hvw Hvws Heq]; subst.
        constructor;
          [cbn [valid_walk]; split; [exact Hcadj | exact Hvw] | exact Hvws].
      * constructor; [exact I | exact IH].
Qed.

Lemma split_walks_length :
  forall ts, ts <> [] -> length (split_walks ts) = S (count_breaks ts).
Proof.
  induction ts as [| t rest IH]; [intros H; contradiction|].
  intros _. destruct rest as [| t2 rest'].
  - reflexivity.
  - assert (IHr : length (split_walks (t2 :: rest'))
                  = S (count_breaks (t2 :: rest')))
      by (apply IH; discriminate).
    rewrite split_walks_cons2, count_breaks_cons2.
    destruct (split_walks (t2 :: rest')) as [| w ws] eqn:E.
    + exfalso. exact (split_walks_cons_nonempty t2 rest' E).
    + cbn [length] in IHr.
      destruct (address_eq_dec (tr_dest t) (tr_source t2)); cbn [length]; lia.
Qed.

(** A break-free transfer list is a single connected walk. *)
Lemma count_breaks_zero_valid :
  forall ts, count_breaks ts = 0 -> valid_walk ts.
Proof.
  induction ts as [| t rest IH]; [intros; exact I|].
  destruct rest as [| t2 rest'].
  - intros _. exact I.
  - cbn [count_breaks]. intros H.
    destruct (address_eq_dec (tr_dest t) (tr_source t2)) as [Hcadj | Hcadj].
    + cbn [valid_walk]. split; [exact Hcadj | apply IH; exact H].
    + cbn in H. discriminate H.
Qed.

(** [rcft_chains T] extracts every chain in [T] (each chain
    appears once for each [RChain] occurrence).  Uses
    [flat_map] over children, which Rocq's guard checker
    accepts (same idiom as [rcft_transfers]). *)
Fixpoint rcft_chains (T : reduced_cft) : list chain_tree :=
  match T with
  | RLeaf _ => []
  | RChain c => [c]
  | RTree _ children => flat_map rcft_chains children
  end.

(** [walks_in_rcft T] lifts [chain_walks] to a reduced CFT:
    every chain in [T] decomposes into a walk-set.  Defined
    via [rcft_chains] to keep the recursion separate from
    the property. *)
Definition walks_in_rcft (T : reduced_cft) : Prop :=
  Forall chain_walks (rcft_chains T).

(** Walk-set preservation under one rewrite step: chains in the
    rewritten tree continue to decompose into walk-sets in the
    original transfer graph.  Each rule contributes a
    construction:
    - R1-R5, R11: build a 2-leaf single-walk chain.
    - R6, R12: prepend or append a single transfer; either as a
      new singleton walk in the walk-set or, when the OCaml
      premise on chained endpoints holds, extending an existing
      walk.  We use the splitting form here.
    - R10: concatenate walk-sets of two chains.
    - R7, R8, R9, R13: walk-set union (multi-walk: each input
      chain contributes its walks).
    - R14, R15: relabel only; walk-set unchanged.
    - RS_lift: structural; chains are unchanged. *)
(** Helper: extracting chains from a list of [reduced_cft]
    distributes over [++]. *)
Lemma flat_map_rcft_chains_app :
  forall l1 l2,
    flat_map rcft_chains (l1 ++ l2) =
    flat_map rcft_chains l1 ++ flat_map rcft_chains l2.
Proof. intros. apply flat_map_app. Qed.

Lemma walk_correspondence_step :
  forall from_ T0 Tf,
    rewrite_step from_ T0 Tf ->
    walks_in_rcft T0 ->
    walks_in_rcft Tf.
Proof.
  intros from_ T0 Tf Hstep.
  induction Hstep; intros Hwalks; subst; unfold walks_in_rcft in *;
    simpl in *;
    repeat rewrite flat_map_rcft_chains_app in *;
    repeat rewrite Forall_app in *; simpl in *;
    repeat rewrite app_nil_r in *.
  - (* RS_swap_chain (R1) *)
    constructor; [|constructor].
    apply chain_walk_implies_walks. eapply chain_walk_swap; eauto.
  - (* RS_burn_chain (R2) *)
    constructor; [|constructor].
    apply chain_walk_implies_walks. eapply chain_walk_burn; eauto.
  - (* RS_mint_chain (R3) *)
    constructor; [|constructor].
    apply chain_walk_implies_walks. eapply chain_walk_mint; eauto.
  - (* RS_pool_cycle (R4) *)
    constructor; [|constructor].
    apply chain_walk_implies_walks.
    apply chain_walk_two. assumption.
  - (* RS_router_chain (R5) *)
    constructor; [|constructor].
    apply chain_walk_implies_walks. eapply chain_walk_router; eauto.
  - (* RS_leaf_chain (R6) *)
    destruct Hwalks as [Hsibs Hc].
    inversion Hc as [|? ? Hcw _]; subst.
    split; [exact Hsibs |].
    constructor; [|constructor].
    match goal with Hor : _ \/ _ |- _ =>
      destruct Hor as [(_ & Heq & _) | (_ & Heq & _)] end.
    + eapply chain_walks_cons_transfer; [exact Hcw | exact Heq].
    + eapply chain_walks_snoc_transfer; [exact Hcw | exact Heq].
  - (* RS_node_leaf_chain (R12) *)
    destruct Hwalks as [Hsibs Hc].
    inversion Hc as [|? ? Hcw _]; subst.
    split; [exact Hsibs |].
    constructor; [|constructor].
    match goal with Hor : _ \/ _ |- _ =>
      destruct Hor as [(_ & _ & Heq & _) | (_ & _ & Heq & _)] end.
    + eapply chain_walks_cons_transfer; [exact Hcw | exact Heq].
    + eapply chain_walks_snoc_transfer; [exact Hcw | exact Heq].
  - (* RS_chain_seq (R10) *)
    destruct Hwalks as [Hsibs Hcs].
    inversion Hcs as [|? ? Hc1' Hrest]; subst.
    inversion Hrest as [|? ? Hc2' _]; subst.
    split; [exact Hsibs |].
    constructor; [|constructor].
    eapply chain_walks_app; [exact Hc1' | exact Hc2' | reflexivity].
  - (* RS_same_token_chain (R11) *)
    constructor; [|constructor].
    apply chain_walk_implies_walks. eapply chain_walk_same_token; eauto.
  - (* RS_lift: lifted children inherit. *)
    destruct Hwalks as [Hsibs Hinner].
    split; [exact Hsibs | exact Hinner].
  - (* RS_merge_endpoints (R7) *)
    destruct Hwalks as [Hsibs Hcs].
    inversion Hcs as [|? ? Hc1' Hrest]; subst.
    rewrite flat_map_app in Hrest. simpl in Hrest.
    apply Forall_app in Hrest as [HM Htail].
    inversion Htail as [|? ? Hc2' Hr]; subst.
    split; [exact Hsibs |].
    split; [exact HM |].
    constructor; [|exact Hr].
    eapply chain_walks_app; [exact Hc1' | exact Hc2' | match goal with H : chain_transfers _ = _ |- _ => exact H end].
  - (* RS_merge_add (R8) *)
    destruct Hwalks as [Hsibs Hcs].
    inversion Hcs as [|? ? Hc1' Hrest]; subst.
    rewrite flat_map_app in Hrest. simpl in Hrest.
    apply Forall_app in Hrest as [HM Htail].
    inversion Htail as [|? ? Hc2' Hr]; subst.
    split; [exact Hsibs |].
    split; [exact HM |].
    constructor; [|exact Hr].
    eapply chain_walks_app; [exact Hc1' | exact Hc2' | match goal with H : chain_transfers _ = _ |- _ => exact H end].
  - (* RS_merge_closed_R9 *)
    destruct Hwalks as [Hsibs Hcs].
    inversion Hcs as [|? ? Hc1' Hrest]; subst.
    rewrite flat_map_app in Hrest. simpl in Hrest.
    apply Forall_app in Hrest as [HM Htail].
    inversion Htail as [|? ? Hc2' Hr]; subst.
    split; [exact Hsibs |].
    split; [exact HM |].
    constructor; [|exact Hr].
    eapply chain_walks_app; [exact Hc1' | exact Hc2' | match goal with H : chain_transfers _ = _ |- _ => exact H end].
  - (* RS_merge_node (R13) *)
    destruct Hwalks as [Hsibs Hcs].
    inversion Hcs as [|? ? Hc1' Hrest]; subst.
    rewrite flat_map_app in Hrest. simpl in Hrest.
    apply Forall_app in Hrest as [HM Htail].
    inversion Htail as [|? ? Hc2' Hr]; subst.
    split; [exact Hsibs |].
    split; [exact HM |].
    constructor; [|exact Hr].
    eapply chain_walks_app; [exact Hc1' | exact Hc2' | match goal with H : chain_transfers _ = _ |- _ => exact H end].
  - (* RS_annotate_arb (R14) *)
    destruct Hwalks as [Hsibs Hctail].
    inversion Hctail as [|? ? Hcw Hr]; subst.
    split; [exact Hsibs |].
    constructor; [|exact Hr].
    eapply chain_walks_eq_transfers; [exact Hcw | match goal with H : chain_transfers _ = _ |- _ => exact H end].
  - (* RS_annotate_cyc (R15) *)
    destruct Hwalks as [Hsibs Hctail].
    inversion Hctail as [|? ? Hcw Hr]; subst.
    split; [exact Hsibs |].
    constructor; [|exact Hr].
    eapply chain_walks_eq_transfers; [exact Hcw | match goal with H : chain_transfers _ = _ |- _ => exact H end].
  - (* RS_under (congruence) *)
    destruct Hwalks as [HL HTR].
    rewrite Forall_app in HTR. destruct HTR as [HT HR].
    split; [exact HL |].
    rewrite Forall_app. split; [apply IHHstep; exact HT | exact HR].
Qed.

(** Reflexive--transitive closure: walk-set decomposition is
    preserved by any number of rewriting steps. *)
Lemma walk_correspondence :
  forall from_ T0 Tf,
    rewrite_star from_ T0 Tf ->
    walks_in_rcft T0 ->
    walks_in_rcft Tf.
Proof.
  intros from_ T0 Tf Hstar. induction Hstar as [T | T1 T2 T3 Hstep _ IH].
  - intros; assumption.
  - intros Hwalks. apply IH.
    apply (walk_correspondence_step from_ T1 T2 Hstep Hwalks).
Qed.

(** [fixpoint_terminates] below covers the Phase-3
    fixpoint (annotate + merge); see Section 13b
    for [rewrite_step_terminating], the Phase-2
    counterpart added in revision.

    We first define the helper functions that
    construct the result of each step, then define
    the fixpoint steps using these functions. *)

(** [set_chain_label] and [ch_first_transfer] are defined in Section 5
    (hoisted above [rewrite_step] for the R14/R15 and R6/R10 witnesses). *)

(** Decide annotation label: Arbitrage or Cycle. *)
Definition annotate_label
    (from_ : address) (c : chain_tree) : construction_label :=
  if negb (address_in_chain from_ c) then Arbitrage
  else if address_eq_dec (ch_origin c) from_
       then Arbitrage
       else Cycle.

(** Construct the merged chain from two operands. *)
Definition merge_two_chains
    (from_ : address) (c1 c2 : chain_tree) : chain_tree :=
  let l := if negb (address_in_chain from_ c1
                    || address_in_chain from_ c2)
           then Arbitrage
           else if address_eq_dec (ch_origin c1) from_
                then Arbitrage
                else Cycle in
  CT_node (ch_origin c1) (ch_destination c2)
          []
          (ch_token_in c1) (ch_token_out c2)
          (ch_first_transfer c1)
          l c1 c2.

(** annotate_label always produces a labeled result. *)
Lemma annotate_label_is_labeled :
  forall from_ c,
    is_labeled (annotate_label from_ c) = true.
Proof.
  intros from_ c. unfold annotate_label.
  destruct (negb (address_in_chain from_ c));
    [ reflexivity |].
  destruct (address_eq_dec (ch_origin c) from_);
    reflexivity.
Qed.

(** merge_two_chains produces a labeled result. *)
Lemma merge_two_chains_is_labeled :
  forall from_ c1 c2,
    is_labeled (ch_label (merge_two_chains from_ c1 c2)) = true.
Proof.
  intros. unfold merge_two_chains. simpl.
  destruct (negb (address_in_chain from_ c1
                  || address_in_chain from_ c2));
    [| destruct (address_eq_dec (ch_origin c1) from_)];
    reflexivity.
Qed.

Inductive fixpoint_step_rel (from_ : address) :
  reduced_cft -> reduced_cft -> Prop :=
  | FS_merge : forall c1 c2 addr siblings,
      is_labeled (ch_label c1) = true ->
      is_labeled (ch_label c2) = true ->
      ch_origin c1 = ch_origin c2 ->
      ch_destination c1 = ch_destination c2 ->
      fixpoint_step_rel from_
        (RTree addr (siblings ++ [RChain c1; RChain c2]))
        (RTree addr (siblings ++ [RChain (merge_two_chains from_ c1 c2)]))

  (** Merge two unlabeled Chaining chains.  This is
      a structural merge (no token check); the token
      equivalence =_τ is checked at annotation time
      by [FS_annotate] / [annotate_all_fn]. *)
  | FS_merge_unlabeled : forall c1 c2 addr siblings,
      ch_label c1 = Chaining ->
      ch_label c2 = Chaining ->
      fixpoint_step_rel from_
        (RTree addr (siblings ++ [RChain c1; RChain c2]))
        (RTree addr (siblings ++ [RChain (merge_two_chains from_ c1 c2)]))

  (** R13: Arbitrage annotation.
      from notin C or s(C) = from.
      Uses [token_equiv] (=_τ, Definition 4). *)
  | FS_annotate_arb : forall c addr siblings,
      (match c with CT_node _ _ _ _ _ _ _ _ _ => True
                  | CT_transfer _ => False end) ->
      ch_origin c = ch_destination c ->
      token_equiv (ch_token_in c) (ch_token_out c) = true ->
      is_labeled (ch_label c) = false ->
      annotate_label from_ c = Arbitrage ->
      fixpoint_step_rel from_
        (RTree addr (siblings ++ [RChain c]))
        (RTree addr (siblings ++ [RChain (set_chain_label c Arbitrage)]))

  (** R14: Cycle annotation.
      from in C and s(C) != from. *)
  | FS_annotate_cycle : forall c addr siblings,
      (match c with CT_node _ _ _ _ _ _ _ _ _ => True
                  | CT_transfer _ => False end) ->
      ch_origin c = ch_destination c ->
      token_equiv (ch_token_in c) (ch_token_out c) = true ->
      is_labeled (ch_label c) = false ->
      annotate_label from_ c = Cycle ->
      fixpoint_step_rel from_
        (RTree addr (siblings ++ [RChain c]))
        (RTree addr (siblings ++ [RChain (set_chain_label c Cycle)])).

(** Helper: fold_left distributes over app. *)
Lemma fold_left_app :
  forall {A : Type} (f : nat -> A -> nat) l1 l2 init,
    fold_left f (l1 ++ l2) init =
    fold_left f l2 (fold_left f l1 init).
Proof.
  intros A f l1. induction l1 as [| x rest IH];
    intros l2 init; simpl; auto.
Qed.

(** count_unlabeled over a singleton list. *)
Lemma count_unlabeled_singleton :
  forall (x : reduced_cft),
    fold_left (fun acc child => acc + count_unlabeled child)
              [x] 0 = count_unlabeled x.
Proof. intros x. simpl. lia. Qed.

(** count_unlabeled of RChain. *)
Lemma count_unlabeled_chain :
  forall c,
    count_unlabeled (RChain c) =
    if is_labeled (ch_label c) then 0 else 1.
Proof. intros c. reflexivity. Qed.

(** count_children of RChain is 0. *)
Lemma count_children_chain :
  forall c, count_children (RChain c) = 0.
Proof. reflexivity. Qed.

(** Helper: fold_left of + is monotone in last element. *)
Lemma fold_left_add_last_lt :
  forall (f : reduced_cft -> nat) l (x y : reduced_cft),
    f x < f y ->
    fold_left (fun acc c => acc + f c) (l ++ [x]) 0 <
    fold_left (fun acc c => acc + f c) (l ++ [y]) 0.
Proof.
  intros f l x y Hlt.
  rewrite !fold_left_app. simpl. lia.
Qed.

Lemma fold_left_add_last_le :
  forall (f : reduced_cft -> nat) l (x y : reduced_cft),
    f x <= f y ->
    fold_left (fun acc c => acc + f c) (l ++ [x]) 0 <=
    fold_left (fun acc c => acc + f c) (l ++ [y]) 0.
Proof.
  intros f l x y Hle.
  rewrite !fold_left_app. simpl. lia.
Qed.

(** Unlabeled count of a chain depends on its label. *)
(** A labeled chain contributes 0 to count_unlabeled. *)
Lemma labeled_count_zero : forall c,
  is_labeled (ch_label c) = true ->
  count_unlabeled (RChain c) = 0.
Proof.
  intros c H. simpl.
  destruct (ch_label c); simpl in H;
    try discriminate; reflexivity.
Qed.

(** Helper for merge: replacing [x;y] with [z] in a
    suffix decreases fold_left when f(z) <= f(x)+f(y). *)
Lemma fold_left_replace_two_with_one :
  forall (f : reduced_cft -> nat) l x y z,
    f z <= f x + f y ->
    fold_left (fun acc c => acc + f c) (l ++ [z]) 0 <=
    fold_left (fun acc c => acc + f c) (l ++ [x; y]) 0.
Proof.
  intros f l x y z Hle.
  rewrite !fold_left_app. simpl. lia.
Qed.

(** Key: FS_merge decreases count_children. *)
Lemma fs_merge_decreases_children :
  forall c1 c2 cm (siblings : list reduced_cft),
    length (siblings ++ [RChain cm]) <
    length (siblings ++ [RChain c1; RChain c2]).
Proof.
  intros. rewrite !length_app. simpl. lia.
Qed.

(** Key: FS_merge does not increase count_unlabeled
    when the merged result is labeled. *)
Lemma fs_merge_unlabeled_nonincrease :
  forall c1 c2 cm (siblings : list reduced_cft),
    is_labeled (ch_label cm) = true ->
    fold_left (fun acc child => acc + count_unlabeled child)
      (siblings ++ [RChain cm]) 0 <=
    fold_left (fun acc child => acc + count_unlabeled child)
      (siblings ++ [RChain c1; RChain c2]) 0.
Proof.
  intros c1 c2 cm siblings Hlab.
  apply fold_left_replace_two_with_one.
  rewrite labeled_count_zero by exact Hlab. lia.
Qed.

(** MAIN THEOREM: each fixpoint step strictly
    decreases the lexicographic measure. *)
Lemma fixpoint_step_decreases :
  forall from_ T T',
    fixpoint_step_rel from_ T T' ->
    lt_lex (measure T') (measure T).
Proof.
  intros from_ T T' Hstep.
  inversion Hstep; subst; unfold lt_lex, measure; simpl.
  - (* FS_merge *)
    right. split.
    + rewrite !fold_left_app. simpl.
      rewrite H, H0.
      destruct (negb (address_in_chain from_ c1
                      || address_in_chain from_ c2));
        [| destruct (address_eq_dec (ch_origin c1) from_)];
        simpl; lia.
    + rewrite !fold_left_app. simpl.
      rewrite !length_app. simpl. lia.
  - (* FS_merge_unlabeled *)
    left.
    rewrite !fold_left_app. simpl.
    rewrite H, H0. simpl.
    destruct (negb (address_in_chain from_ c1
                    || address_in_chain from_ c2));
      [| destruct (address_eq_dec (ch_origin c1) from_)];
      simpl; lia.
  - (* FS_annotate_arb (R13) *)
    left.
    apply fold_left_add_last_lt.
    destruct c as [t | o d m ti to_ ft lbl lc rc];
      [ contradiction | ].
    simpl in H2 |- *.
    rewrite H2. simpl. lia.
  - (* FS_annotate_cycle (R14) *)
    left.
    apply fold_left_add_last_lt.
    destruct c as [t | o d m ti to_ ft lbl lc rc];
      [ contradiction | ].
    simpl in H2 |- *.
    rewrite H2. simpl. lia.
Qed.

(** Theorem 3: Soundness.
    The classify function returning VArbitrage implies
    the absence of verdict-determining reasons. *)
Lemma soundness_reasons :
  forall reasons,
    classify reasons = VArbitrage ->
    ~ In NoCycles reasons /\
    ~ In Leftovers reasons /\
    ~ In FinalNeg reasons /\
    ~ In FinalMixed reasons.
Proof.
  exact classify_no_false_reasons.
Qed.

(** Validate-Deltas: downgrades arbitrage-labeled
    chains whose gross delta is non-positive to
    cycle.  After validation, every surviving
    arbitrage chain has delta > 0.

    In the implementation
    (remove_arbitrage_cycles_with_no_balance,
    eth_arbitrage.ml:784), this checks:
    - delta[to_] exists and
    - first_transfer.amount <= amount1 for same token.

    We model this as a predicate on chain_tree:
    the gross delta at the origin is positive. *)
Definition validated_arbitrage (c : chain_tree) : Prop :=
  ch_label c = Arbitrage /\
  (ch_delta c (ch_origin c) (ch_token_in c) > 0)%Z /\
  net_positive c = true.

(** [VArbitrage] implies both the cascade
    conditions AND the existence of at least one
    validated arbitrage cycle, connecting the
    syntactic [classify] verdict to the semantic
    Definition 4. *)
Lemma soundness_full :
  forall reasons cycles,
    classify reasons = VArbitrage ->
    (* NoCycles not in R means cycles is nonempty *)
    (~ In NoCycles reasons -> cycles <> []) ->
    (* Every cycle in the list was validated *)
    (forall c, In c cycles -> validated_arbitrage c) ->
    (* Then: the cascade conditions hold AND
       there exists a validated cycle *)
    (~ In NoCycles reasons /\
     ~ In Leftovers reasons /\
     ~ In FinalNeg reasons /\
     ~ In FinalMixed reasons) /\
    exists c, In c cycles /\ validated_arbitrage c.
Proof.
  intros reasons cycles Hclass Hnonempty Hvalid.
  split.
  - exact (classify_no_false_reasons reasons Hclass).
  - assert (Hnc : ~ In NoCycles reasons)
      by (apply classify_no_false_reasons in Hclass;
          tauto).
    specialize (Hnonempty Hnc).
    destruct cycles as [| c rest].
    + contradiction.
    + exists c. split.
      * left. reflexivity.
      * apply Hvalid. left. reflexivity.
Qed.

(* ############################################################
   Part III -- The deterministic kernel (confluence, termination, decidable equivalence)
   ############################################################ *)

(* ============================================================
   Section 13: Leftover modeling
   ============================================================ *)

(** has_leftovers: does the reduced CFT contain any
    RLeaf nodes (transfers not consumed into a chain)?
    Matches the implementation's Extract-and-Recover
    which separates cycles from leftover leaves.
    In eval_semantics_arbitrage_analysis, leftovers
    present => Cftar_leftover_transaction added. *)
Fixpoint has_leftovers (t : reduced_cft) : bool :=
  match t with
  | RLeaf _ => true
  | RChain _ => false
  | RTree _ children =>
      existsb has_leftovers children
  end.

(** has_arb_cycles: does the reduced CFT contain at
    least one chain labeled arbitrage?
    Matches the has_cycles check in
    eval_semantics_arbitrage_analysis. *)
Fixpoint has_arb_cycles (t : reduced_cft) : bool :=
  match t with
  | RLeaf _ => false
  | RChain c =>
      match ch_label c with
      | Arbitrage => true
      | _ => false
      end
  | RTree _ children =>
      existsb has_arb_cycles children
  end.

(** Extract every Arbitrage-labeled chain from a
    reduced CFT.  Mirrors the OCaml
    Extract-and-Recover step that pulls cycles from
    the tree before passing them to Validate-Deltas. *)
Fixpoint extract_arb_cycles (t : reduced_cft)
    : list chain_tree :=
  match t with
  | RLeaf _ => []
  | RChain c =>
      match ch_label c with
      | Arbitrage => [c]
      | _ => []
      end
  | RTree _ children =>
      (fix loop (ts : list reduced_cft) : list chain_tree :=
         match ts with
         | [] => []
         | t :: rest => extract_arb_cycles t ++ loop rest
         end) children
  end.

(** Validate-Deltas modeled in Rocq: filter the
    extracted cycles by positive gross delta at
    the origin/token-in pair.  This is the exact
    boolean predicate the OCaml
    [remove_arbitrage_cycles_with_no_balance]
    implements (eth_arbitrage.ml:784). *)
Definition validate_deltas
    (cs : list chain_tree) : list chain_tree :=
  filter (fun c =>
    Z.gtb (ch_delta c (ch_origin c) (ch_token_in c)) 0
    && net_positive c)
    cs.

(** Cons-step reduction for [extract_arb_cycles] over an
    [RTree]: holds definitionally because the inline
    fix-helper unfolds the same way. *)
Lemma extract_arb_cycles_RTree_cons :
  forall a t rest,
    extract_arb_cycles (RTree a (t :: rest)) =
    extract_arb_cycles t ++ extract_arb_cycles (RTree a rest).
Proof. reflexivity. Qed.

(** Every chain in [extract_arb_cycles t] is labeled
    Arbitrage by construction. *)
Lemma extract_arb_cycles_labeled :
  forall t c, In c (extract_arb_cycles t) ->
              ch_label c = Arbitrage.
Proof.
  fix IH 1. intros t c.
  destruct t as [tr | c0 | addr children].
  - intros Hin. simpl in Hin. contradiction.
  - intros Hin. simpl in Hin.
    destruct (ch_label c0) eqn:Elab; simpl in Hin;
      try contradiction.
    destruct Hin as [Heq | Hin]; [|contradiction].
    subst c. exact Elab.
  - revert c.
    induction children as [| ch rest IHrest];
      intros c Hin.
    + simpl in Hin. contradiction.
    + rewrite extract_arb_cycles_RTree_cons in Hin.
      apply in_app_iff in Hin.
      destruct Hin as [Hin | Hin].
      * exact (IH ch c Hin).
      * exact (IHrest c Hin).
Qed.

(** Every chain that survives [validate_deltas] has
    strictly positive gross delta at its origin. *)
Lemma validate_deltas_positive :
  forall cs c, In c (validate_deltas cs) ->
    (ch_delta c (ch_origin c) (ch_token_in c) > 0)%Z.
Proof.
  intros cs c Hin.
  unfold validate_deltas in Hin.
  apply filter_In in Hin as [_ Hgt].
  apply andb_true_iff in Hgt as [Hgt _].
  apply Z.gtb_lt in Hgt. apply Z.lt_gt. exact Hgt.
Qed.

(** Every chain that survives [validate_deltas] is
    net-profitable under the deployer's cost model. *)
Lemma validate_deltas_net_positive :
  forall cs c, In c (validate_deltas cs) ->
    net_positive c = true.
Proof.
  intros cs c Hin.
  unfold validate_deltas in Hin.
  apply filter_In in Hin as [_ Hgt].
  apply andb_true_iff in Hgt as [_ Hnp]. exact Hnp.
Qed.

(** Validate-Deltas is conservative: filtering
    cannot introduce new chains. *)
Lemma validate_deltas_subset :
  forall cs c, In c (validate_deltas cs) -> In c cs.
Proof.
  intros cs c Hin.
  unfold validate_deltas in Hin.
  apply filter_In in Hin as [Hin _]. exact Hin.
Qed.

(** The Extract-and-Recover composed with
    Validate-Deltas produces a list of cycles each
    satisfying [validated_arbitrage].  The [Forall
    validated_arbitrage] hypothesis used in
    [soundness_end_to_end] is derivable from the
    Rocq-modeled pipeline. *)
Lemma validate_deltas_sound :
  forall t,
    Forall validated_arbitrage
           (validate_deltas (extract_arb_cycles t)).
Proof.
  intros t.
  apply Forall_forall.
  intros c Hin.
  unfold validated_arbitrage. repeat split.
  - apply (extract_arb_cycles_labeled t c).
    apply (validate_deltas_subset _ c Hin).
  - apply (validate_deltas_positive _ c Hin).
  - apply (validate_deltas_net_positive _ c Hin).
Qed.

(** Attempted-arbitrage characterization: a closed,
    structurally-Def-5 cycle whose [net_positive]
    realizer returns false is, by construction, not
    a validated arbitrage.  This is the formal
    counterpart of the OCaml classifier emitting the
    Warning verdict for cycles whose gross delta
    exceeds gas + builder payment yields net <= 0. *)
Corollary attempted_arbitrage_characterization :
  forall c,
    ch_label c = Arbitrage ->
    (ch_delta c (ch_origin c) (ch_token_in c) > 0)%Z ->
    net_positive c = false ->
    ~ validated_arbitrage c.
Proof.
  intros c Hlbl Hpos Hnp [_ [_ Habs]].
  rewrite Hnp in Habs. discriminate.
Qed.

(** compute_reasons: produces the reason list from
    the reduced AST state, mirroring
    eval_semantics_arbitrage_analysis in the
    implementation.  We model the four
    verdict-determining reasons. *)
Definition compute_reasons
    (has_cyc : bool) (has_left : bool)
    (final_neg : bool) (final_mixed : bool)
    : list reason :=
  (if has_cyc then [] else [NoCycles]) ++
  (if has_left then [Leftovers] else []) ++
  (if final_neg then [FinalNeg] else []) ++
  (if final_mixed then [FinalMixed] else []).

(** Key connection: when the AST has leftovers,
    the Leftovers reason is in the list, which
    prevents VArbitrage. *)
Lemma leftovers_in_reasons :
  forall has_cyc final_neg final_mixed,
    In Leftovers
      (compute_reasons has_cyc true final_neg final_mixed).
Proof.
  intros. unfold compute_reasons.
  destruct has_cyc; simpl;
    [ left; reflexivity
    | right; left; reflexivity ].
Qed.

(** When the AST has no leftovers and cycles exist,
    the NoCycles and Leftovers reasons are absent. *)
Lemma no_leftovers_no_nocycles :
  forall final_neg final_mixed,
    ~ In NoCycles
      (compute_reasons true false final_neg final_mixed) /\
    ~ In Leftovers
      (compute_reasons true false final_neg final_mixed).
Proof.
  intros. unfold compute_reasons. simpl.
  split; intros H;
    destruct final_neg; destruct final_mixed;
    simpl in H; intuition discriminate.
Qed.

(** Complete leftover soundness: if the reduced AST
    has leftovers, the verdict cannot be Arbitrage.
    This matches the implementation: leftovers =>
    Cftar_leftover_transaction => Warning. *)
Lemma leftovers_prevent_arbitrage :
  forall has_cyc final_neg final_mixed,
    classify
      (compute_reasons has_cyc true final_neg final_mixed)
    <> VArbitrage.
Proof.
  intros has_cyc final_neg final_mixed Habs.
  apply classify_no_false_reasons in Habs.
  destruct Habs as [_ [Hl _]].
  apply Hl. unfold compute_reasons.
  destruct has_cyc, final_neg, final_mixed;
    simpl; auto.
Qed.

(** Converse: VArbitrage implies no leftovers in
    the reduced AST (when reasons are computed
    from the AST state). *)
Lemma arbitrage_implies_no_leftovers :
  forall has_cyc has_left final_neg final_mixed,
    classify
      (compute_reasons has_cyc has_left
         final_neg final_mixed) = VArbitrage ->
    has_left = false.
Proof.
  intros has_cyc has_left final_neg final_mixed H.
  destruct has_left eqn:E; auto.
  exfalso.
  exact (leftovers_prevent_arbitrage
    has_cyc final_neg final_mixed H).
Qed.

(** Full connection: VArbitrage from compute_reasons
    implies cycles exist AND no leftovers AND
    final balance is not negative or mixed. *)
Lemma arbitrage_implies_clean_ast :
  forall has_cyc has_left final_neg final_mixed,
    classify
      (compute_reasons has_cyc has_left
         final_neg final_mixed) = VArbitrage ->
    has_cyc = true /\
    has_left = false /\
    final_neg = false /\
    final_mixed = false.
Proof.
  intros hc hl fn fm Hclass.
  assert (Hno := classify_no_false_reasons _ Hclass).
  destruct Hno as [Hnc [Hleft [Hfn Hfm]]].
  (* If any flag is wrong, the corresponding reason
     is in the list, contradicting Hno. *)
  destruct hc eqn:Ec; [ | exfalso; apply Hnc;
    unfold compute_reasons; simpl; auto ].
  destruct hl eqn:El; [ exfalso; apply Hleft;
    unfold compute_reasons; simpl; auto | ].
  destruct fn eqn:Efn; [ exfalso; apply Hfn;
    unfold compute_reasons; simpl; auto | ].
  destruct fm eqn:Efm; [ exfalso; apply Hfm;
    unfold compute_reasons; simpl; auto | ].
  auto.
Qed.

(** End-to-end soundness: if the pipeline declares
    VArbitrage from the reduced AST state, and the
    pipeline's Validate-Deltas step has stamped every
    extracted cycle with validated_arbitrage, then
    (a) the reduced AST has the expected shape
        (cycles present, no leftovers, no negative
         or mixed final balance), and
    (b) at least one cycle in the extracted list
        satisfies Definition 4 (the economic
        predicate: ch_label = Arbitrage and
        ch_delta > 0 at the origin).

    The premises [cycles <> []] and
    [forall c, In c cycles -> validated_arbitrage c]
    are stated here as explicit hypotheses so this
    corollary can be applied at any pipeline stage.
    They are discharged in
    [soundness_end_to_end_tree] below from the
    Rocq-modeled [extract_arb_cycles] and
    [validate_deltas], closing the loop end-to-end.
    The flag cascade half is discharged by
    [arbitrage_implies_clean_ast]; the existential
    half composes [soundness_full] with that fact. *)
Corollary soundness_end_to_end :
  forall has_cyc has_left final_neg final_mixed cycles,
    classify
      (compute_reasons has_cyc has_left
         final_neg final_mixed) = VArbitrage ->
    cycles <> [] ->
    (forall c, In c cycles -> validated_arbitrage c) ->
    (has_cyc = true /\ has_left = false /\
     final_neg = false /\ final_mixed = false) /\
    exists c, In c cycles /\ validated_arbitrage c.
Proof.
  intros hc hl fn fm cycles Hclass Hnonempty Hvalid.
  split.
  - exact (arbitrage_implies_clean_ast hc hl fn fm Hclass).
  - pose proof
      (soundness_full
         (compute_reasons hc hl fn fm) cycles
         Hclass (fun _ => Hnonempty) Hvalid)
      as [_ Hex].
    exact Hex.
Qed.

(** End-to-end soundness over a tree, with the
    pipeline's filtered cycle list derived from
    [extract_arb_cycles] and [validate_deltas].
    When [classify] declares VArbitrage and the
    tree contains at least one arbitrage cycle
    that survives delta validation, that cycle
    satisfies Definition 4 ([validated_arbitrage]). *)
Corollary soundness_end_to_end_tree :
  forall t has_left final_neg final_mixed,
    classify
      (compute_reasons (has_arb_cycles t) has_left
         final_neg final_mixed) = VArbitrage ->
    validate_deltas (extract_arb_cycles t) <> [] ->
    (has_arb_cycles t = true /\ has_left = false /\
     final_neg = false /\ final_mixed = false) /\
    exists c, In c (validate_deltas (extract_arb_cycles t))
              /\ validated_arbitrage c.
Proof.
  intros t hl fn fm Hclass Hnonempty.
  pose proof (validate_deltas_sound t) as Hall.
  split.
  - exact (arbitrage_implies_clean_ast _ _ _ _ Hclass).
  - destruct (validate_deltas (extract_arb_cycles t))
      as [| c rest] eqn:Eq;
      [contradiction|].
    exists c. split.
    + left; reflexivity.
    + rewrite Forall_forall in Hall.
      apply Hall. left; reflexivity.
Qed.

(** The implementation's annotate_and_reduce is a
    deterministic function.

    Note: connect_cycles has its own inner fixpoint
    (it recurses until children stabilize), so a
    single "pass" in the implementation may perform
    multiple FS_merge steps.  This does not affect
    correctness: the outer fixpoint catches any
    remaining work, and the measure still decreases
    on each FS_merge application regardless of
    whether it occurs in the inner or outer loop.

      let rec annotate_and_reduce from_ to_ cft =
        let reduced = annotate_cycles ... cft in
        let reduced = connect_cycles ... reduced in
        match cft = reduced with
        | true  -> reduced
        | false -> annotate_and_reduce from_ to_ reduced

    annotate_cycles is a pure structural map (List.map
    over children). connect_cycles uses
    find_compatible_cycle which does a greedy
    left-to-right scan. Both are deterministic.

    The step function below encodes the greedy
    left-to-right scan directly as a computable
    function, making determinism immediate. *)

(* ============================================================
   Section 14: Certified step function (the kernel)

   The step is defined as a computable function
   (greedy left-to-right scan), so determinism is
   immediate.

   Correspondence with the OCaml implementation:
   - annotate_all_fn   ↔ annotate_cycles
   - scan_and_merge     ↔ find_compatible_cycle
   - try_merge_children ↔ connect_cycles_children
   - step_fn            ↔ annotate_and_reduce

   Termination follows from three observations:
   1. Each merge replaces 2 children with 1
      → count_children strictly decreases
   2. count_children(RChain _) = 0 always
      → the fold sum is preserved across merges
   3. Annotation only relabels, no structural change
      → count_children preserved by annotation
   ============================================================ *)

(** Annotate all chains in the reduced CFT.
    For each unlabeled chain forming a closed cycle
    (same origin/destination, token_equiv holds),
    assign Arbitrage or Cycle.
    Mirrors annotate_cycles. *)
Fixpoint annotate_all_fn
    (from_ : address) (t : reduced_cft) : reduced_cft :=
  match t with
  | RLeaf tr => RLeaf tr
  | RChain c =>
      if negb (is_labeled (ch_label c))
         && (if address_eq_dec (ch_origin c) (ch_destination c)
             then true else false)
         && token_equiv (ch_token_in c) (ch_token_out c)
      then
        match annotate_label from_ c with
        | Arbitrage =>
            if wrap_unwrap c then RChain c
            else RChain (set_chain_label c Arbitrage)
        | lbl => RChain (set_chain_label c lbl)
        end
      else RChain c
  | RTree addr children =>
      RTree addr (map (annotate_all_fn from_) children)
  end.

(** Two labeled chains that share origin and
    destination are compatible for merging.
    Mirrorscft_trees_compatible_for_merge. *)
(** [chains_mergeable c1 c2] holds when the kernel
    may merge [c1] and [c2].  Enforces the structural
    invariant required for the Phase-3 bridge: both
    chains labeled, endpoints aligned, closure
    (origin = destination), input-token match (R9
    shape), and token closure on the merged chain. *)
Definition chains_mergeable (c1 c2 : chain_tree) : bool :=
  is_labeled (ch_label c1)
  && is_labeled (ch_label c2)
  && (if address_eq_dec (ch_origin c1) (ch_origin c2)
      then true else false)
  && (if address_eq_dec (ch_destination c1) (ch_destination c2)
      then true else false)
  && (if address_eq_dec (ch_origin c1) (ch_destination c1)
      then true else false)
  && (if token_eq_dec (ch_token_in c1) (ch_token_in c2)
      then true else false)
  && (if token_eq_dec (ch_token_out c1) (ch_token_out c2)
      then true else false)
  && token_equiv (ch_token_in c1) (ch_token_out c2).

(** Structural merge for unlabeled Chaining chains.
    This handles the case where two adjacent chains
    have not yet been annotated (both still labeled
    Chaining). In the implementation, this covers
    same-token relay patterns and native/wrapped
    asset pairs. The token equivalence check
    (=_τ) is applied at annotation time, not here;
    this rule only requires structural adjacency. *)
Definition chains_unlabeled_mergeable (c1 c2 : chain_tree) : bool :=
  negb (is_labeled (ch_label c1))
  && negb (is_labeled (ch_label c2))
  && (if label_eq_dec (ch_label c1) Chaining then true else false)
  && (if label_eq_dec (ch_label c2) Chaining then true else false)
  && (if address_eq_dec (ch_destination c1) (ch_origin c2)
      then true else false)
  && (if token_eq_dec (ch_token_out c1) (ch_token_in c2)
      then true else false).

(** Scan the sibling list for a chain compatible
    with c1 and merge them.
    Mirrors find_compatible_cycle. *)
Fixpoint scan_and_merge
    (c1 : chain_tree)
    (from_ : address)
    (prefix : list reduced_cft)
    (before : list reduced_cft)
    (after : list reduced_cft)
    : option (list reduced_cft) :=
  match after with
  | [] => None
  | (RChain c2) :: after' =>
      if chains_mergeable c1 c2
         || chains_unlabeled_mergeable c1 c2
      then
        let cm := merge_two_chains from_ c1 c2 in
        Some (prefix ++ before ++ [RChain cm] ++ after')
      else
        scan_and_merge c1 from_ prefix
          (before ++ [RChain c2]) after'
  | x :: after' =>
      scan_and_merge c1 from_ prefix
        (before ++ [x]) after'
  end.

Definition find_and_merge
    (from_ : address)
    (prefix : list reduced_cft)
    (child : reduced_cft)
    (rest : list reduced_cft)
    : option (list reduced_cft) :=
  match child with
  | RChain c1 =>
      scan_and_merge c1 from_ prefix [] rest
  | _ => None
  end.

(** Try to merge one pair in a child list.
    Scans left-to-right for the first child that
    has a compatible partner.
    Matches the greedy scan in
    connect_cycles_children. *)
Fixpoint try_merge_children
    (from_ : address)
    (prefix : list reduced_cft)
    (suffix : list reduced_cft)
    : option (list reduced_cft) :=
  match suffix with
  | [] => None
  | child :: rest =>
      match find_and_merge from_ prefix child rest with
      | Some new_children => Some new_children
      | None =>
          try_merge_children from_ (prefix ++ [child]) rest
      end
  end.

(** Phase-3 step: annotate all closed chains, then
    perform one merge.  Returns [None] when the tree
    is in normal form (fixpoint reached).  This is
    one pass of [annotate_and_reduce]; the outer loop
    (repeated application until [None]) terminates
    because each step strictly decreases the lex
    measure. *)
Definition step_fn
    (from_ : address) (t : reduced_cft) : option reduced_cft :=
  let t' := annotate_all_fn from_ t in
  match t' with
  | RTree addr children =>
      match try_merge_children from_ [] children with
      | Some new_children => Some (RTree addr new_children)
      | None => None
      end
  | _ => None
  end.

(** Key properties of set_chain_label. *)
Lemma set_chain_label_origin :
  forall c l, ch_origin (set_chain_label c l) = ch_origin c.
Proof. intros [|]; reflexivity. Qed.

Lemma set_chain_label_destination :
  forall c l, ch_destination (set_chain_label c l) = ch_destination c.
Proof. intros [|]; reflexivity. Qed.

Lemma set_chain_label_token_in :
  forall c l, ch_token_in (set_chain_label c l) = ch_token_in c.
Proof. intros [|]; reflexivity. Qed.

Lemma set_chain_label_token_out :
  forall c l, ch_token_out (set_chain_label c l) = ch_token_out c.
Proof. intros [|]; reflexivity. Qed.

Lemma set_chain_label_label :
  forall c l,
    match c with
    | CT_transfer _ => ch_label (set_chain_label c l) = Chaining
    | CT_node _ _ _ _ _ _ _ _ _ => ch_label (set_chain_label c l) = l
    end.
Proof. intros [|]; reflexivity. Qed.

Lemma set_chain_label_transfers :
  forall c l,
    chain_transfers (set_chain_label c l) = chain_transfers c.
Proof. intros [|]; reflexivity. Qed.

(** Key lemma: suffix of a fixed length uniquely
    determines the prefix. *)
Lemma app_inv_tail :
  forall {A : Type} (s1 s2 : list A) (r1 r2 : list A),
    s1 ++ r1 = s2 ++ r2 ->
    length r1 = length r2 ->
    s1 = s2 /\ r1 = r2.
Proof.
  intros A s1. induction s1 as [| a rest IH];
    intros s2 r1 r2 H Hlen.
  - simpl in H. destruct s2 as [| b rest2].
    + auto.
    + exfalso.
      apply (f_equal (@length A)) in H.
      rewrite length_app in H. simpl in H. lia.
  - destruct s2 as [| b rest2].
    + exfalso.
      apply (f_equal (@length A)) in H.
      simpl in H. rewrite length_app in H. lia.
    + simpl in H. injection H. intros Hrest Ha.
      subst. destruct (IH rest2 r1 r2 Hrest Hlen).
      subst. auto.
Qed.

(** Helper: every [fixpoint_step_rel] step from an
    [RTree] produces an [RTree].  By inversion on
    the relation -- all four constructors yield
    [RTree addr (siblings ++ [...])]. *)
Lemma fixpoint_step_same_tree :
  forall from_ addr children T',
    fixpoint_step_rel from_ (RTree addr children) T' ->
    exists addr', exists children',
      T' = RTree addr' children'.
Proof.
  intros from_ addr children T' H.
  inversion H; subst; eexists; eexists; reflexivity.
Qed.

(** Tactic: solve a determinism subgoal after
    double inversion, given that the children
    lists are equal. *)
Ltac solve_det :=
  match goal with
  | [ H : ?s1 ++ ?r1 = ?s2 ++ ?r2 |- _ ] =>
      first
        [ let Hs := fresh in
          assert (Hs := app_inv_tail s1 s2 r1 r2 H
            ltac:(simpl; reflexivity));
          destruct Hs; subst;
          match goal with
          | [ Ht : _ :: _ = _ :: _ |- _ ] =>
              injection Ht; intros; subst; reflexivity
          | _ => reflexivity
          end
        | exfalso;
          apply (f_equal (@length _)) in H;
          rewrite !length_app in H;
          simpl in H; lia ]
  end.

Ltac solve_det_sym :=
  match goal with
  | [ H : ?s1 ++ ?r1 = ?s2 ++ ?r2 |- _ ] =>
      first
        [ let Hs := fresh in
          assert (Hs := app_inv_tail s1 s2 r1 r2 H
            ltac:(simpl; reflexivity));
          destruct Hs; subst; reflexivity
        | let Hs := fresh in
          symmetry in H;
          assert (Hs := app_inv_tail s2 s1 r2 r1 H
            ltac:(simpl; reflexivity));
          destruct Hs; subst; reflexivity
        | exfalso;
          apply (f_equal (@length _)) in H;
          rewrite !length_app in H;
          simpl in H; lia ]
  end.

Ltac solve_same_length :=
  match goal with
  | [ H : ?s1 ++ ?r1 = ?s2 ++ ?r2 |- _ ] =>
      apply app_inv_tail in H;
        [ destruct H; subst;
          match goal with
          | [ Ht : _ :: _ = _ :: _ |- _ ] =>
              injection Ht; intros; subst; reflexivity
          | _ => reflexivity
          end
        | reflexivity ]
  end.

Ltac solve_diff_length :=
  match goal with
  | [ H : ?s1 ++ ?r1 = ?s2 ++ ?r2 |- _ ] =>
      exfalso;
      let Hlen := fresh in
      assert (Hlen := f_equal (@length _) H);
      repeat rewrite length_app in Hlen;
      simpl in Hlen; lia
  end.

(* ============================================================
   Section 15: Deterministic step and confluence
   ============================================================ *)

(** The deterministic step is defined directly from
    the computable step_fn.  Determinism is not a
    property of the rewrite relation -- the rules
    overlap and a relational view admits multiple
    redexes.  It is recovered structurally: the
    σ-CFT input is DSE-ordered (Property prop:dse),
    so step_fn is a total function, and any two
    derivations agree on the redex selected at each
    step. *)

Definition fixpoint_step_det
    (from_ : address) (T T' : reduced_cft) : Prop :=
  step_fn from_ T = Some T'.

Lemma fixpoint_step_det_deterministic :
  forall from_ T T1 T2,
    fixpoint_step_det from_ T T1 ->
    fixpoint_step_det from_ T T2 ->
    T1 = T2.
Proof.
  intros from_ T T1 T2 H1 H2.
  unfold fixpoint_step_det in *.
  rewrite H1 in H2. injection H2. auto.
Qed.

(** Every deterministic step is also a valid
    relational step (or sequence of steps).
    This bridges the two formulations.
    We state soundness: step_fn only constructs
    valid merges and annotations. *)
(** The following lemmas establish that the
    deterministic step decreases the measure.
    Key properties proved below:
    - annotate_all_fn preserves count_children
      (only relabels, no structural change)
    - annotate_all_fn does not increase
      count_unlabeled (labels go from false to true)
    - try_merge_children replaces two children with
      one, strictly decreasing list length *)
(** Helper: fold_left over map with a function
    that preserves values. *)
Lemma fold_left_map_eq :
  forall (f : reduced_cft -> nat) (g : reduced_cft -> reduced_cft)
         (l : list reduced_cft),
    (forall x, f (g x) = f x) ->
    forall init,
    fold_left (fun a c => a + f c) (map g l) init =
    fold_left (fun a c => a + f c) l init.
Proof.
  intros f g l Hfg. induction l as [| h rest IH];
    intros init; simpl; auto.
  rewrite Hfg. exact (IH (init + f h)).
Qed.

(** fold_left of addition is monotone in init. *)
Lemma fold_left_add_mono_init :
  forall (f : reduced_cft -> nat) (l : list reduced_cft) i1 i2,
    i1 <= i2 ->
    fold_left (fun a c => a + f c) l i1 <=
    fold_left (fun a c => a + f c) l i2.
Proof.
  intros f l. induction l as [| h rest IH];
    intros i1 i2 Hle; simpl; auto.
  apply IH. lia.
Qed.

Lemma fold_left_map_le :
  forall (f : reduced_cft -> nat) (g : reduced_cft -> reduced_cft)
         (l : list reduced_cft),
    (forall x, f (g x) <= f x) ->
    forall init,
    fold_left (fun a c => a + f c) (map g l) init <=
    fold_left (fun a c => a + f c) l init.
Proof.
  intros f g l Hfg.
  induction l as [| h rest IH]; intros init; simpl; auto.
  (* Goal: fold ... (map g rest) (init + f(g h))
           <= fold ... rest (init + f h) *)
  transitivity
    (fold_left (fun a c => a + f c) (map g rest) (init + f h)).
  - apply fold_left_add_mono_init.
    specialize (Hfg h). lia.
  - apply IH.
Qed.

(** Annotation only relabels chains. count_children
    is preserved exactly.

    Technical note: we use [fix IH 1] (manual fixpoint
    on the first argument) instead of [induction]
    because [reduced_cft] is not an inductive type
    that Rocq's [induction] tactic handles directly:
    the recursive occurrence is inside a [list].
    [fix IH 1] gives us an induction hypothesis on
    any structurally smaller [reduced_cft], which we
    then combine with list induction on [children].
    This idiom appears throughout the file. *)
Lemma annotate_preserves_children :
  forall from_ t,
    count_children (annotate_all_fn from_ t) =
    count_children t.
Proof.
  intros from_.
  fix IH 1. destruct t as [tr | c | addr children].
  - simpl. reflexivity.
  - simpl. destruct (_ && _ && _); [|reflexivity].
    destruct (annotate_label from_ c) eqn:Hlab;
      try reflexivity.
    destruct (wrap_unwrap c); reflexivity.
  - simpl. rewrite length_map. f_equal.
    assert (Hfold : forall init,
      fold_left (fun a c => a + count_children c)
        (map (annotate_all_fn from_) children) init =
      fold_left (fun a c => a + count_children c)
        children init).
    { induction children as [| h rest IHl];
        intros init; simpl; auto.
      rewrite (IH h).
      exact (IHl (init + count_children h)). }
    exact (Hfold 0).
Qed.

(** Annotation only relabels chains. count_unlabeled
    can only decrease (a chain might become labeled,
    never the reverse). *)
Lemma annotate_unlabeled_nonincrease :
  forall from_ t,
    count_unlabeled (annotate_all_fn from_ t) <=
    count_unlabeled t.
Proof.
  intros from_.
  fix IH 1. destruct t as [tr | c | addr children].
  - simpl. lia.
  - simpl. destruct (_ && _ && _) eqn:Econd; [|simpl; lia].
    destruct (annotate_label from_ c) eqn:Hlab; simpl.
    + destruct (is_labeled (ch_label (set_chain_label c Chaining)));
        destruct (is_labeled (ch_label c)); lia.
    + destruct (is_labeled (ch_label (set_chain_label c Merging)));
        destruct (is_labeled (ch_label c)); lia.
    + destruct (is_labeled (ch_label (set_chain_label c Cycle)));
        destruct (is_labeled (ch_label c)); lia.
    + destruct (wrap_unwrap c).
      * simpl. destruct (is_labeled (ch_label c)); lia.
      * simpl.
        destruct (is_labeled (ch_label (set_chain_label c Arbitrage)));
          destruct (is_labeled (ch_label c)); lia.
    + destruct (is_labeled (ch_label (set_chain_label c TokenBurn)));
        destruct (is_labeled (ch_label c)); lia.
    + destruct (is_labeled (ch_label (set_chain_label c TokenMint)));
        destruct (is_labeled (ch_label c)); lia.
  - simpl.
    assert (Hfold : forall init,
      fold_left (fun a c => a + count_unlabeled c)
        (map (annotate_all_fn from_) children) init <=
      fold_left (fun a c => a + count_unlabeled c)
        children init).
    { induction children as [| h rest IHl];
        intros init; simpl; [lia|].
      specialize (IH h).
      transitivity (fold_left (fun a c => a + count_unlabeled c)
        (map (annotate_all_fn from_) rest)
        (init + count_unlabeled h)).
      - apply fold_left_add_mono_init. lia.
      - exact (IHl (init + count_unlabeled h)). }
    exact (Hfold 0).
Qed.

(** Property 3: try_merge_children replaces two
    children with one.  We prove the generalized
    version with accumulator. *)
(** The inner scan of find_and_merge preserves a
    length invariant: |before| + |after| = |rest|
    at each step. When it succeeds, the result has
    length |prefix| + |before| + 1 + |after'|
    where before ++ [matched] ++ after' = rest,
    giving |result| = |prefix| + |rest|. *)
(** The scan replaces two children (c1 from the
    caller, c2 from after) with one merged child.
    So the result has length |prefix| + |before| +
    1 + |after'| where before ++ [c2] ++ after' is
    a partition of `after`. Since |before| + 1 +
    |after'| = |after|, we get
    |result| + 1 = |prefix| + |before| + 2 + |after'|
                 = |prefix| + |after| + 1. *)
Lemma scan_and_merge_length :
  forall c1 from_ prefix before after result,
    scan_and_merge c1 from_ prefix before after =
      Some result ->
    length result + 1 =
    length prefix + length before + length after + 1.
Proof.
  intros c1 from_ prefix before after.
  revert before.
  induction after as [| hd tl IH];
    intros before result H.
  - discriminate.
  - destruct hd as [t | c2 | a l]; simpl in H.
    + (* RLeaf *)
      specialize (IH (before ++ [RLeaf t]) result H).
      rewrite length_app in IH. simpl in IH. simpl. lia.
    + (* RChain *)
      destruct (_ || _) eqn:Econd.
      * injection H; intros; subst.
        repeat rewrite length_app. simpl. lia.
      * specialize (IH (before ++ [RChain c2]) result H).
        rewrite length_app in IH. simpl in IH. simpl. lia.
    + (* RTree *)
      specialize (IH (before ++ [RTree a l]) result H).
      rewrite length_app in IH. simpl in IH. simpl. lia.
Qed.

Lemma find_and_merge_length :
  forall from_ prefix child rest result,
    find_and_merge from_ prefix child rest = Some result ->
    length result + 1 = length prefix + length rest + 1.
Proof.
  intros from_ prefix child rest result H.
  unfold find_and_merge in H.
  destruct child; try discriminate.
  apply scan_and_merge_length in H. simpl in H. lia.
Qed.

Lemma try_merge_length :
  forall from_ prefix suffix result,
    try_merge_children from_ prefix suffix = Some result ->
    length result < length prefix + length suffix.
Proof.
  intros from_ prefix suffix.
  revert prefix.
  induction suffix as [| child rest IH];
    intros prefix result H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (find_and_merge from_ prefix child rest) eqn:Hfm.
    + injection H; intros; subst.
      apply find_and_merge_length in Hfm.
      simpl. lia.
    + apply IH in H.
      rewrite length_app in H. simpl in H. simpl. lia.
Qed.

(** The merge preserves the count_children fold sum.
    count_children(RChain _) = 0 for ALL chains
    regardless of internal structure.  So swapping
    RChain c2 for RChain cm changes nothing: both
    contribute 0. *)
Lemma scan_and_merge_fold_cc :
  forall c1 from_ prefix before after result init,
    scan_and_merge c1 from_ prefix before after =
      Some result ->
    fold_left (fun a c => a + count_children c)
      result init =
    fold_left (fun a c => a + count_children c)
      (prefix ++ before ++ after) init.
Proof.
  intros c1 from_ prefix before after.
  revert before.
  induction after as [| hd tl IH];
    intros before result init H.
  - discriminate.
  - destruct hd as [t | c2 | a l]; simpl in H.
    + specialize (IH (before ++ [RLeaf t]) result init H).
      rewrite IH. repeat rewrite <- app_assoc. reflexivity.
    + destruct (_ || _) eqn:Econd.
      * injection H; intros; subst.
        repeat (rewrite fold_left_app; simpl). lia.
      * specialize (IH (before ++ [RChain c2]) result init H).
        rewrite IH. repeat rewrite <- app_assoc. reflexivity.
    + specialize (IH (before ++ [RTree a l]) result init H).
      rewrite IH. repeat rewrite <- app_assoc. reflexivity.
Qed.

(** Inserting an element with count_children = 0
    does not change the fold sum. *)
Lemma fold_cc_skip_zero :
  forall x l1 l2 init,
    count_children x = 0 ->
    fold_left (fun a c => a + count_children c)
      (l1 ++ x :: l2) init =
    fold_left (fun a c => a + count_children c)
      (l1 ++ l2) init.
Proof.
  intros x l1 l2 init Hx.
  rewrite !fold_left_app. simpl. rewrite Hx.
  rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma try_merge_fold_cc :
  forall from_ prefix suffix result init,
    try_merge_children from_ prefix suffix = Some result ->
    fold_left (fun a c => a + count_children c)
      result init =
    fold_left (fun a c => a + count_children c)
      (prefix ++ suffix) init.
Proof.
  intros from_ prefix suffix.
  revert prefix.
  induction suffix as [| child rest IH];
    intros prefix result init H.
  - discriminate.
  - simpl in H.
    destruct (find_and_merge from_ prefix child rest) eqn:Hfm.
    + injection H; intros; subst.
      unfold find_and_merge in Hfm.
      destruct child as [|c|]; try discriminate.
      pose proof (scan_and_merge_fold_cc
        c from_ prefix [] rest result init Hfm) as Hscan.
      simpl in Hscan.
      rewrite fold_cc_skip_zero with (x := RChain c)
        by reflexivity.
      exact Hscan.
    + specialize (IH (prefix ++ [child]) result init H).
      rewrite IH.
      rewrite <- app_assoc. reflexivity.
Qed.

(** Replacing one element with a smaller one in a
    fold_left sum gives a smaller result. *)
Lemma fold_replace_le :
  forall (f : reduced_cft -> nat) x y l1 l2 init,
    f x <= f y ->
    fold_left (fun a c => a + f c) (l1 ++ x :: l2) init <=
    fold_left (fun a c => a + f c) (l1 ++ y :: l2) init.
Proof.
  intros. rewrite !fold_left_app. simpl.
  apply fold_left_add_mono_init. lia.
Qed.

(** Removing an element from a fold_left sum gives
    a smaller or equal result. *)
Lemma fold_remove_le :
  forall (f : reduced_cft -> nat) x l1 l2 init,
    fold_left (fun a c => a + f c) (l1 ++ l2) init <=
    fold_left (fun a c => a + f c) (l1 ++ x :: l2) init.
Proof.
  intros. rewrite !fold_left_app. simpl.
  apply fold_left_add_mono_init. lia.
Qed.

(** The merge result has count_unlabeled = 0
    because merge_two_chains is always labeled. *)
Lemma merge_cu_zero :
  forall from_ c1 c2,
    count_unlabeled
      (RChain (merge_two_chains from_ c1 c2)) = 0.
Proof.
  intros. simpl.
  destruct (negb (address_in_chain from_ c1
                  || address_in_chain from_ c2));
    [| destruct (address_eq_dec (ch_origin c1) from_)];
    reflexivity.
Qed.

(** The merge does not increase count_unlabeled.
    My merge result is always labeled (Arbitrage
    or Cycle), so count_unlabeled = 0.  The
    replaced chain c2 had count_unlabeled >= 0.
    The sum can only decrease or stay equal. *)
Lemma scan_and_merge_fold_cu :
  forall c1 from_ prefix before after result init,
    scan_and_merge c1 from_ prefix before after =
      Some result ->
    fold_left (fun a c => a + count_unlabeled c)
      result init <=
    fold_left (fun a c => a + count_unlabeled c)
      (prefix ++ before ++ after) init.
Proof.
  intros c1 from_ prefix before after.
  revert before.
  induction after as [| hd tl IH];
    intros before result init H.
  - discriminate.
  - destruct hd as [t | c2 | a l]; simpl in H.
    + specialize (IH (before ++ [RLeaf t]) result init H).
      rewrite <- !app_assoc in IH. exact IH.
    + destruct (_ || _) eqn:Econd.
      * injection H; intros; subst.
        rewrite !fold_left_app. simpl.
        destruct (negb (address_in_chain from_ c1
                        || address_in_chain from_ c2));
          [| destruct (address_eq_dec (ch_origin c1) from_)];
          simpl; apply fold_left_add_mono_init; lia.
      * specialize (IH (before ++ [RChain c2]) result init H).
        rewrite <- !app_assoc in IH. exact IH.
    + specialize (IH (before ++ [RTree a l]) result init H).
      rewrite <- !app_assoc in IH. exact IH.
Qed.

Lemma try_merge_fold_cu :
  forall from_ prefix suffix result init,
    try_merge_children from_ prefix suffix = Some result ->
    fold_left (fun a c => a + count_unlabeled c)
      result init <=
    fold_left (fun a c => a + count_unlabeled c)
      (prefix ++ suffix) init.
Proof.
  intros from_ prefix suffix.
  revert prefix.
  induction suffix as [| child rest IH];
    intros prefix result init H.
  - discriminate.
  - simpl in H.
    destruct (find_and_merge from_ prefix child rest) eqn:Hfm.
    + injection H; intros; subst.
      unfold find_and_merge in Hfm.
      destruct child as [|c|]; try discriminate.
      pose proof (scan_and_merge_fold_cu
        c from_ prefix [] rest result init Hfm) as Hscan.
      simpl in Hscan.
      transitivity
        (fold_left (fun a c0 => a + count_unlabeled c0)
          (prefix ++ rest) init); [exact Hscan|].
      rewrite !fold_left_app. simpl.
      apply fold_left_add_mono_init. lia.
    + specialize (IH (prefix ++ [child]) result init H).
      rewrite <- app_assoc in IH. exact IH.
Qed.

(** Each step strictly decreases the lexicographic
    measure (count_unlabeled, count_children).
    The merge replaces 2 children with 1, so
    count_children drops.  The fold sum is preserved
    because all RChain nodes contribute 0 to it.
    count_unlabeled doesn't increase because the
    merged result is always labeled. *)
Lemma fixpoint_step_det_decreases :
  forall from_ T T',
    fixpoint_step_det from_ T T' ->
    lt_lex (measure T') (measure T).
Proof.
  intros from_ T T' H.
  unfold fixpoint_step_det, step_fn in H.
  destruct (annotate_all_fn from_ T) as [| | addr children] eqn:Hann;
    try discriminate.
  destruct (try_merge_children from_ [] children) as [nc|] eqn:Hmerge;
    try discriminate.
  injection H; intros; subst.
  unfold lt_lex, measure. simpl.
  (* count_children strictly decreased *)
  assert (Hlen := try_merge_length from_ [] children nc Hmerge).
  simpl in Hlen.
  (* fold_left sum preserved by merge *)
  assert (Hfold := try_merge_fold_cc from_ [] children nc 0 Hmerge).
  simpl in Hfold.
  (* count_unlabeled: annotation didn't increase it *)
  assert (Hu := annotate_unlabeled_nonincrease from_ T).
  rewrite Hann in Hu. simpl in Hu.
  (* count_children: annotation preserved it *)
  assert (Hc := annotate_preserves_children from_ T).
  rewrite Hann in Hc. simpl in Hc.
  (* count_unlabeled: merge doesn't increase it *)
  assert (Hfu := try_merge_fold_cu from_ [] children nc 0 Hmerge).
  simpl in Hfu.
  (* Case split on whether count_unlabeled decreased *)
  destruct (Nat.eq_dec
    (count_unlabeled (RTree addr nc))
    (count_unlabeled T)) as [Heq|Hneq].
  - (* Equal: use right disjunct *)
    right. split; [exact Heq|].
    rewrite Hfold. lia.
  - (* Strict decrease: use left disjunct *)
    left. simpl in *. lia.
Qed.

(** Reflexive-transitive closure of the
    deterministic step. *)
Inductive fixpoint_star_det (from_ : address) :
  reduced_cft -> reduced_cft -> Prop :=
  | FSD_refl : forall t, fixpoint_star_det from_ t t
  | FSD_step : forall t1 t2 t3,
      fixpoint_step_det from_ t1 t2 ->
      fixpoint_star_det from_ t2 t3 ->
      fixpoint_star_det from_ t1 t3.

(** Well-foundedness of the deterministic step. *)
Lemma fixpoint_step_det_wf :
  forall from_,
  well_founded (fun T' T => fixpoint_step_det from_ T T').
Proof.
  intro from_. intro T.
  remember (measure T) as m eqn:Hm.
  revert T Hm.
  induction m as [m IH] using (well_founded_induction lt_lex_wf).
  intros T Hm. constructor. intros T' Hstep.
  apply (IH (measure T')).
  - subst. exact (fixpoint_step_det_decreases from_ T T' Hstep).
  - reflexivity.
Qed.

(** Termination of the deterministic fixpoint.
    Constructive proof by case analysis on the
    option result of [step_fn]. *)
Lemma fixpoint_terminates :
  forall from_ (T0 : reduced_cft),
    exists Tf, fixpoint_star_det from_ T0 Tf /\
               (forall T', ~ fixpoint_step_det from_ Tf T').
Proof.
  intros from_ T0.
  induction T0 as [T0 IH]
    using (well_founded_ind (fixpoint_step_det_wf from_)).
  remember (step_fn from_ T0) as st eqn:Hst.
  destruct st as [T1 |].
  - assert (Hstep : fixpoint_step_det from_ T0 T1).
    { unfold fixpoint_step_det. rewrite <- Hst. reflexivity. }
    destruct (IH T1 Hstep) as [Tf [Hstar Hnf]].
    exists Tf. split.
    + eapply FSD_step; eassumption.
    + exact Hnf.
  - exists T0. split.
    + apply FSD_refl.
    + intros T' Hstep.
      unfold fixpoint_step_det in Hstep.
      rewrite <- Hst in Hstep. discriminate.
Qed.

(** Confluence.  The rewrite rules themselves are
    non-deterministic (multiple rules may apply to
    overlapping redexes), but the input, a trace
    with the sequential ordering guaranteed by
    Property prop:dse, is deterministic.  We
    exploit this by realizing the step as a total
    computable function over ordered children, so
    the resulting rewriting is convergent: any two
    reduction sequences from the same starting tree
    produce the same normal form.  Critical pairs
    (R6/R10, R7/R9) that would arise absent
    Property prop:dse are discussed in the proofs
    companion. *)
Lemma fixpoint_star_det_deterministic :
  forall from_ T T1 T2,
    fixpoint_star_det from_ T T1 ->
    fixpoint_star_det from_ T T2 ->
    (forall T', ~ fixpoint_step_det from_ T1 T') ->
    (forall T', ~ fixpoint_step_det from_ T2 T') ->
    T1 = T2.
Proof.
  intros from_ T T1 T2 Hstar1.
  revert T2.
  induction Hstar1 as [T | T Tmid T1 Hstep1 Hstar1 IH].
  - intros T2 Hstar2 Hnf1 Hnf2.
    inversion Hstar2; subst.
    + reflexivity.
    + exfalso. exact (Hnf1 t2 H).
  - intros T2 Hstar2 Hnf1 Hnf2.
    inversion Hstar2; subst.
    + exfalso. exact (Hnf2 Tmid Hstep1).
    + assert (Tmid = t2) as Heq
        by exact (fixpoint_step_det_deterministic
                    from_ T Tmid t2 Hstep1 H).
      subst. exact (IH T2 H0 Hnf1 Hnf2).
Qed.

Lemma confluence :
  forall from_ (T0 Tf1 Tf2 : reduced_cft),
    fixpoint_star_det from_ T0 Tf1 ->
    fixpoint_star_det from_ T0 Tf2 ->
    (forall T', ~ fixpoint_step_det from_ Tf1 T') ->
    (forall T', ~ fixpoint_step_det from_ Tf2 T') ->
    Tf1 = Tf2.
Proof.
  intros from_.
  exact (fixpoint_star_det_deterministic from_).
Qed.

(** Corollary: the fixpoint is unique. *)
Corollary lfp_eq_gfp :
  forall from_ (T0 : reduced_cft),
    exists! Tf, fixpoint_star_det from_ T0 Tf /\
                (forall T', ~ fixpoint_step_det from_ Tf T').
Proof.
  intros from_ T0.
  destruct (fixpoint_terminates from_ T0) as [Tf [Hstar Hnf]].
  exists Tf. split.
  - exact (conj Hstar Hnf).
  - intros Tf' [Hstar' Hnf'].
    symmetry.
    exact (confluence from_ T0 Tf' Tf Hstar' Hstar Hnf' Hnf).
Qed.

(* ============================================================
   Section 16: step_fn relational characterization

   Bridge between the declarative spec [rewrite_step]
   and the computable [step_fn]: an explicit relation
   [step_fn_rel] decomposing one [step_fn] call into
   its two phases (annotation + one merge), with
   proofs that [step_fn] refines it and preserves the
   same invariants (transfer-set inclusion + lex
   measure decrease).
   ============================================================ *)

(** Relabeling preserves the chain's transfer list. *)
Lemma set_chain_label_chain_transfers :
  forall c l, chain_transfers (set_chain_label c l) = chain_transfers c.
Proof. intros [|]; reflexivity. Qed.

(** Merging two chains concatenates their transfers. *)
Lemma merge_two_chains_chain_transfers :
  forall from_ c1 c2,
    chain_transfers (merge_two_chains from_ c1 c2) =
    chain_transfers c1 ++ chain_transfers c2.
Proof. intros. reflexivity. Qed.

(** Annotation pass preserves the transfer multiset
    of the entire reduced CFT.  Since [set_chain_label]
    only touches the label slot and [annotate_all_fn]
    is structural recursion, transfers are unchanged
    everywhere. *)
Lemma annotate_all_fn_preserves_transfers :
  forall from_ t,
    rcft_transfers (annotate_all_fn from_ t) =
    rcft_transfers t.
Proof.
  intros from_.
  fix IH 1. destruct t as [tr | c | addr children].
  - reflexivity.
  - simpl. destruct (_ && _ && _); [|reflexivity].
    destruct (annotate_label from_ c) eqn:Hlab; simpl;
      try apply set_chain_label_chain_transfers.
    destruct (wrap_unwrap c); simpl;
      [reflexivity | apply set_chain_label_chain_transfers].
  - simpl.
    induction children as [| h rest IHl].
    + reflexivity.
    + simpl. rewrite (IH h). f_equal. exact IHl.
Qed.

(** scan_and_merge subset: every transfer present in
    the merged child list was present in the original
    [prefix ++ [RChain c1] ++ before ++ after]
    arrangement.  The merge concatenates c1's and
    c2's transfers into the new chain; the rest of
    the children are unchanged in content. *)
Lemma scan_and_merge_subset_transfers :
  forall c1 from_ prefix before after result,
    scan_and_merge c1 from_ prefix before after = Some result ->
    forall t,
      In t (flat_map rcft_transfers result) ->
      In t (flat_map rcft_transfers
              (prefix ++ [RChain c1] ++ before ++ after)).
Proof.
  intros c1 from_ prefix before after.
  revert before.
  induction after as [| hd tl IH]; intros before result H t Hin.
  - discriminate.
  - destruct hd as [tr | c2 | a children]; simpl in H.
    + (* RLeaf: scan recurses with before ++ [RLeaf tr] *)
      specialize (IH (before ++ [RLeaf tr]) result H t Hin).
      rewrite <- !app_assoc in IH. simpl in IH. exact IH.
    + (* RChain c2 *)
      destruct (chains_mergeable c1 c2
                || chains_unlabeled_mergeable c1 c2) eqn:Emerge.
      * (* merge fires *)
        injection H; intros; subst result.
        rewrite !flat_map_app in *. simpl in *.
        rewrite !app_nil_r in *.
        (* Hin contains chain_transfers (merge_two_chains ...);
           merge_two_chains_chain_transfers expands it to
           chain_transfers c1 ++ chain_transfers c2.
           Try the rewrite; if simpl already unfolded it,
           continue without. *)
        try rewrite merge_two_chains_chain_transfers in Hin.
        repeat rewrite in_app_iff in *.
        tauto.
      * (* not mergeable: recurse *)
        specialize (IH (before ++ [RChain c2]) result H t Hin).
        rewrite <- !app_assoc in IH. simpl in IH. exact IH.
    + (* RTree: scan recurses with before ++ [RTree _ _] *)
      specialize (IH (before ++ [RTree a children]) result H t Hin).
      rewrite <- !app_assoc in IH. simpl in IH. exact IH.
Qed.

(** try_merge_children subset: any transfer in the
    merged result was in the original [prefix ++ suffix].
    Either find_and_merge fires (delegate to
    scan_and_merge_subset_transfers) or it fails and
    we recurse on the tail with prefix extended. *)
Lemma try_merge_children_subset_transfers :
  forall from_ prefix suffix result,
    try_merge_children from_ prefix suffix = Some result ->
    forall t,
      In t (flat_map rcft_transfers result) ->
      In t (flat_map rcft_transfers (prefix ++ suffix)).
Proof.
  intros from_ prefix suffix.
  revert prefix.
  induction suffix as [| child rest IH]; intros prefix result H t Hin.
  - discriminate.
  - simpl in H.
    destruct (find_and_merge from_ prefix child rest) eqn:Hfm.
    + (* find_and_merge fires *)
      injection H; intros; subst result.
      unfold find_and_merge in Hfm.
      destruct child as [|c|]; try discriminate.
      pose proof (scan_and_merge_subset_transfers
                    c from_ prefix [] rest l Hfm t Hin) as Hscan.
      simpl in Hscan. exact Hscan.
    + (* find_and_merge fails: recurse with prefix ++ [child] *)
      specialize (IH (prefix ++ [child]) result H t Hin).
      rewrite <- app_assoc in IH. simpl in IH. exact IH.
Qed.

(** The relational form of step_fn.  A step decomposes
    into the annotation pass producing some
    [RTree addr children] state, and a successful
    merge producing the new children list.  This
    inductive is constructed so that
    [step_fn_rel from_ T T' <-> step_fn from_ T = Some T']
    by inspection. *)
Inductive step_fn_rel (from_ : address) :
  reduced_cft -> reduced_cft -> Prop :=
| SFR : forall T addr children new_children,
    annotate_all_fn from_ T = RTree addr children ->
    try_merge_children from_ [] children = Some new_children ->
    step_fn_rel from_ T (RTree addr new_children).

(** Soundness of the computable step w.r.t. its
    relational form: every successful [step_fn] call
    produces a result captured by [step_fn_rel].
    Together with [step_fn_rel_decreases] and
    [step_fn_rel_preserves_transfers] this closes the
    bridge from the executable kernel to the
    declarative semantics. *)
Lemma step_fn_sound :
  forall from_ T T',
    step_fn from_ T = Some T' ->
    step_fn_rel from_ T T'.
Proof.
  intros from_ T T' Hsfn.
  unfold step_fn in Hsfn.
  destruct (annotate_all_fn from_ T) as [tr | c | addr children] eqn:Hann;
    try discriminate.
  destruct (try_merge_children from_ [] children) as [nc|] eqn:Hmerge;
    try discriminate.
  injection Hsfn; intros; subst.
  econstructor; eassumption.
Qed.

(** step_fn_rel decreases the lexicographic measure.
    Inherits from the existing fixpoint_step_det
    decrease lemma by unfolding step_fn. *)
Lemma step_fn_rel_decreases :
  forall from_ T T',
    step_fn_rel from_ T T' ->
    lt_lex (measure T') (measure T).
Proof.
  intros from_ T T' Hrel.
  inversion Hrel as
    [T0 addr children new_children Hann Hmerge Heq1 Heq2]; subst.
  apply (fixpoint_step_det_decreases from_).
  unfold fixpoint_step_det, step_fn.
  rewrite Hann, Hmerge. reflexivity.
Qed.

(** step_fn_rel preserves the transfer multiset
    (subset direction): every transfer in the result
    was already in the input.  This is the same
    invariant proved for the declarative rewrite_step
    by [preservation_step]; the bridge from the
    computable step_fn to that invariant is now
    mechanized rather than by inspection. *)
Lemma step_fn_rel_preserves_transfers :
  forall from_ T T',
    step_fn_rel from_ T T' ->
    forall t, In t (rcft_transfers T') ->
              In t (rcft_transfers T).
Proof.
  intros from_ T T' Hrel t Hin.
  inversion Hrel as
    [T0 addr children new_children Hann Hmerge Heq1 Heq2]; subst.
  (* Hin : In t (rcft_transfers (RTree addr new_children))
     Goal: In t (rcft_transfers T)
     Path: rcft_transfers T = rcft_transfers (annotate_all_fn from_ T)
                          (by annotate_all_fn_preserves_transfers, sym)
         = rcft_transfers (RTree addr children)            (by Hann)
         = flat_map rcft_transfers children
         ⊇ flat_map rcft_transfers new_children            (by try_merge subset)
         = rcft_transfers (RTree addr new_children) ∋ t. *)
  rewrite <- (annotate_all_fn_preserves_transfers from_ T).
  rewrite Hann. simpl.
  pose proof (try_merge_children_subset_transfers
                from_ [] children new_children Hmerge t)
       as Hsub.
  simpl in Hsub. simpl in Hin. exact (Hsub Hin).
Qed.

(* ============================================================
   Section 17: Verified classify properties
   ============================================================ *)

(** classify never returns VArbitrage when NoCycles is present. *)
Lemma classify_nocycles :
  forall reasons,
    In NoCycles reasons ->
    classify reasons = VNone.
Proof.
  intros reasons H. unfold classify.
  apply has_reason_In in H. rewrite H. reflexivity.
Qed.

(** classify never returns VArbitrage when Leftovers is present. *)
Lemma classify_leftovers :
  forall reasons,
    ~ In NoCycles reasons ->
    In Leftovers reasons ->
    classify reasons = VWarning.
Proof.
  intros reasons Hnc Hl. unfold classify.
  apply has_reason_not_In in Hnc. rewrite Hnc.
  apply has_reason_In in Hl. rewrite Hl. reflexivity.
Qed.

(** classify never returns VArbitrage when FinalNeg is present. *)
Lemma classify_finalneg :
  forall reasons,
    ~ In NoCycles reasons ->
    ~ In Leftovers reasons ->
    In FinalNeg reasons ->
    classify reasons = VWarning.
Proof.
  intros reasons Hnc Hl Hfn. unfold classify.
  apply has_reason_not_In in Hnc. rewrite Hnc.
  apply has_reason_not_In in Hl. rewrite Hl.
  apply has_reason_In in Hfn. rewrite Hfn. reflexivity.
Qed.

(** classify never returns VArbitrage when FinalMixed present. *)
Lemma classify_finalmixed :
  forall reasons,
    ~ In NoCycles reasons ->
    ~ In Leftovers reasons ->
    ~ In FinalNeg reasons ->
    In FinalMixed reasons ->
    classify reasons = VWarning.
Proof.
  intros reasons Hnc Hl Hfn Hfm. unfold classify.
  apply has_reason_not_In in Hnc. rewrite Hnc.
  apply has_reason_not_In in Hl. rewrite Hl.
  apply has_reason_not_In in Hfn. rewrite Hfn.
  apply has_reason_In in Hfm. rewrite Hfm. reflexivity.
Qed.

(** The classify cascade is complete: these are the
    only four reasons that prevent VArbitrage. *)
Lemma classify_complete :
  forall reasons,
    classify reasons <> VArbitrage ->
    In NoCycles reasons \/
    In Leftovers reasons \/
    In FinalNeg reasons \/
    In FinalMixed reasons.
Proof.
  intros reasons H.
  unfold classify in H.
  destruct (has_reason NoCycles reasons) eqn:E1.
  - left. apply has_reason_In. auto.
  - destruct (has_reason Leftovers reasons) eqn:E2.
    + right. left. apply has_reason_In. auto.
    + destruct (has_reason FinalNeg reasons) eqn:E3.
      * right. right. left. apply has_reason_In. auto.
      * destruct (has_reason FinalMixed reasons) eqn:E4.
        -- right. right. right. apply has_reason_In. auto.
        -- exfalso. apply H. reflexivity.
Qed.

(* ============================================================
   Section 18: Concrete termination bound (3n-2)

   My measure μ(T) = (u, c) where:
     u = count_unlabeled (number of unlabeled chains)
     c = count_children (total children across all Tree nodes)

   For the initial CFT with n transfers:
     u₀ ≤ n    (each transfer → at most one chain)
     c₀ ≤ 2n-2 (binary tree with n leaves has ≤ 2n-1 nodes,
                 minus the root → 2n-2 children)

   Total passes ≤ u₀ + c₀ ≤ n + (2n-2) = 3n - 2.
   ============================================================ *)

(** Count leaf transfers in a chain tree. *)
Fixpoint count_chain_transfers (c : chain_tree) : nat :=
  match c with
  | CT_transfer _ => 1
  | CT_node _ _ _ _ _ _ _ l r =>
      count_chain_transfers l + count_chain_transfers r
  end.

(** Count leaf transfers in a reduced CFT. *)
Fixpoint count_transfers (t : reduced_cft) : nat :=
  match t with
  | RLeaf _ => 1
  | RChain c => count_chain_transfers c
  | RTree _ children =>
      fold_left (fun acc child => acc + count_transfers child)
                children 0
  end.

(** Every chain has at least one transfer. *)
Lemma chain_transfers_ge_1 :
  forall c, count_chain_transfers c >= 1.
Proof.
  induction c as [?|? ? ? ? ? ? ? lc ? rc ?]; simpl; lia.
Qed.

(** Every RLeaf contributes 1 to count_unlabeled and
    1 to count_transfers.  Every RChain contributes
    0 or 1 to count_unlabeled and ≥1 to count_transfers.
    So count_unlabeled ≤ count_transfers. *)
Lemma unlabeled_le_transfers :
  forall t, count_unlabeled t <= count_transfers t.
Proof.
  fix IH 1. destruct t as [tr | c | addr children].
  - (* RLeaf: both are 1 *)
    simpl. lia.
  - (* RChain: unlabeled is 0 or 1, transfers ≥ 1 *)
    simpl. destruct c as [t0|o d m ti to_ ft lbl lc rc]; simpl.
    + (* CT_transfer: both 1 *) lia.
    + (* CT_node: unlabeled ≤ 1, transfers ≥ 2 *)
      pose proof (chain_transfers_ge_1 lc) as Hlc.
      pose proof (chain_transfers_ge_1 rc) as Hrc.
      destruct (is_labeled lbl); simpl; lia.
  - (* RTree: sum over children *)
    simpl.
    assert (Haux : forall l iu it,
      iu <= it ->
      fold_left (fun a c => a + count_unlabeled c) l iu <=
      fold_left (fun a c => a + count_transfers c) l it).
    { induction l as [|x rest IHl]; intros iu it Hle;
        simpl; [lia|].
      specialize (IH x). apply IHl. lia. }
    exact (Haux children 0 0 (Nat.le_refl _)).
Qed.

(** The bound c₀ ≤ 2n-2 comes from standard tree
    theory: a tree with n leaves and no unary
    branching has at most n-1 internal nodes and
    2n-2 edges (= count_children).  In the CFT, the
    lifting rule (RS_lift) eliminates unary branching,
    so this holds for any post-lift tree.

    Formalizing this requires a well-formedness
    predicate (every RTree has ≥2 children).  I
    state it as an assumption and derive the bound
    from it. *)

(** A tree where every internal node has ≥2 children
    satisfies count_children ≤ 2 * count_transfers - 2.
    This is the standard bound for trees without
    unary branching. *)
(** Every non-empty reduced_cft has ≥1 transfer.
    RLeaf and RChain always have ≥1; RTree has ≥1
    if it has ≥1 child. *)
Lemma transfers_ge_1_leaf :
  forall tr, count_transfers (RLeaf tr) >= 1.
Proof. simpl. lia. Qed.

Lemma transfers_ge_1_chain :
  forall c, count_transfers (RChain c) >= 1.
Proof. intro. simpl. pose proof (chain_transfers_ge_1 c). lia. Qed.

(** By construction, my reduced CFTs never contain
    empty tree nodes: every call frame in the EVM
    trace has ≥1 transfer or sub-call, and the
    lifting rule collapses single-child intermediaries.
    I encode this as a non_empty predicate. *)
Fixpoint non_empty (t : reduced_cft) : bool :=
  match t with
  | RLeaf _ => true
  | RChain _ => true
  | RTree _ children =>
      match children with
      | [] => false
      | _ => forallb non_empty children
      end
  end.

(** Helpers for the fold_left-based non_empty check. *)

(** fold_left of && starting from false stays false. *)
Lemma fold_andb_false :
  forall {A : Type} (f : A -> bool) l,
    fold_left (fun acc c => acc && f c) l false = false.
Proof.
  induction l as [|h rest IH]; simpl; auto.
Qed.

(** fold_left of addition shifts linearly in init. *)
Lemma fold_left_add_shift :
  forall (f : reduced_cft -> nat) l init k,
    fold_left (fun a c => a + f c) l (init + k) =
    fold_left (fun a c => a + f c) l init + k.
Proof.
  induction l as [|h rest IH]; intros init k; simpl; [lia|].
  replace (init + k + f h) with (init + f h + k) by lia.
  exact (IH (init + f h) k).
Qed.

(** fold_left of addition is ≥ init. *)
Lemma fold_left_add_ge_init :
  forall (f : reduced_cft -> nat) l init,
    fold_left (fun a c => a + f c) l init >= init.
Proof.
  induction l as [|h rest IH]; intro init; simpl; [lia|].
  specialize (IH (init + f h)). lia.
Qed.

(** Splitting the fold_left && into head and tail. *)
Lemma fold_andb_cons :
  forall {A : Type} (f : A -> bool) h rest,
    fold_left (fun acc c => acc && f c) (h :: rest) true = true ->
    f h = true /\
    fold_left (fun acc c => acc && f c) rest true = true.
Proof.
  intros A f h rest H. simpl in H.
  destruct (f h) eqn:Efh; simpl in H.
  - split; [reflexivity | exact H].
  - rewrite fold_andb_false in H. discriminate.
Qed.

(** Non-empty subtrees have ≥1 transfer. *)
Lemma non_empty_transfers_ge_1 :
  forall t, non_empty t = true ->
    count_transfers t >= 1.
Proof.
  fix IH 1.
  destruct t as [tr | c | addr [|h rest]].
  - simpl. lia.
  - simpl. intro. pose proof (chain_transfers_ge_1 c). lia.
  - discriminate.
  - intros Hne. simpl in Hne. simpl.
    apply andb_true_iff in Hne.
    destruct Hne as [Hh _].
    specialize (IH h Hh).
    pose proof (fold_left_add_ge_init
      count_transfers rest (count_transfers h)).
    lia.
Qed.

(** After lifting, every RTree has ≥2 children.
    I keep lifting until every Tree node has a
    sibling, which is the fully_lifted invariant.
    Using forallb (not fold_left) for clean
    destructing in proofs. *)
Fixpoint fully_lifted (t : reduced_cft) : bool :=
  match t with
  | RLeaf _ => true
  | RChain _ => true
  | RTree _ children =>
      (2 <=? length children) &&
      forallb fully_lifted children
  end.

(** The bound cc + 2 ≤ 2*ct holds for all fully
    lifted, non-empty trees.  The per-element bound
    gives cc(x) + 2 ≤ 2*ct(x) for every subtree,
    and the list sum absorbs the +2 into the 2*ct
    budget via fold_left_add_shift.

    The Coq proof requires careful fold_left
    accumulator management.  I state it and use it
    for the 3n bound; the list induction is the
    standard Handshaking Lemma for trees. *)
(** [lia] chokes on [fold_left]; convert to
    [list_sum (map f l)] so it can see arithmetic.
    Used throughout this file. *)
Lemma fold_to_sum :
  forall (f : reduced_cft -> nat) l init,
    fold_left (fun a c => a + f c) l init =
    init + list_sum (map f l).
Proof.
  induction l as [|h rest IH]; intro init; simpl; [lia|].
  rewrite IH. lia.
Qed.

(** The per-element bound cc+2 ≤ 2*ct summed over
    a list gives sum_cc + 2*length ≤ 2*sum_ct. *)
Lemma sum_cc_le :
  forall l,
    (forall x, In x l ->
       count_children x + 2 <= 2 * count_transfers x) ->
    list_sum (map count_children l) + 2 * length l <=
    2 * list_sum (map count_transfers l).
Proof.
  induction l as [|h rest IH]; intros Hall; simpl; [lia|].
  assert (Hh := Hall h (or_introl eq_refl)).
  specialize (IH (fun x Hx => Hall x (or_intror Hx))).
  lia.
Qed.

Lemma cc_plus2_le_twice_ct :
  forall t,
    fully_lifted t = true ->
    non_empty t = true ->
    count_children t + 2 <= 2 * count_transfers t.
Proof.
  fix IH 1.
  destruct t as [tr | c | addr [|h rest]].
  - simpl. lia.
  - simpl. destruct c as [?|? ? ? ? ? ? ? cl cr]; simpl.
    + lia.
    + intros _ _. pose proof (chain_transfers_ge_1 cl).
      pose proof (chain_transfers_ge_1 cr). lia.
  - intros _ Habs. discriminate.
  - intros Hfl Hne. simpl.
    rewrite !fold_to_sum. simpl.
    assert (Hfl2 := Hfl). simpl in Hfl2.
    apply andb_true_iff in Hfl2 as [Hlen Hfl_all].
    simpl in Hne. apply andb_true_iff in Hne as [Hne_h Hne_rest].
    apply andb_true_iff in Hfl_all as [Hfl_h Hfl_rest].
    (* Build per-element bound from IH on h, then
       recurse into rest via the fix. The key: we
       call IH only on h (structurally smaller) and
       on elements of rest (also structurally smaller
       since they're subterms of the original tree).
       But Coq's guard checker needs to see this
       directly, not through In. So we build Hall
       by induction on the children list. *)
    assert (Hall : forall x, In x (h :: rest) ->
      count_children x + 2 <= 2 * count_transfers x).
    { assert (IHh := IH h Hfl_h Hne_h).
      (* For rest elements, use a list scan *)
      assert (IHrest : forall x, In x rest ->
        count_children x + 2 <= 2 * count_transfers x).
      { clear IHh Hlen Hfl_h Hne_h Hfl.
        induction rest as [|r rs IHrs]; intros x Hin;
          [destruct Hin|].
        simpl in Hfl_rest, Hne_rest.
        apply andb_true_iff in Hfl_rest as [Hfl_r Hfl_rs].
        apply andb_true_iff in Hne_rest as [Hne_r Hne_rs].
        destruct Hin as [<- | Hin].
        - exact (IH r Hfl_r Hne_r).
        - exact (IHrs Hne_rs Hfl_rs x Hin). }
      intros x [<- | Hin]; [exact IHh | exact (IHrest x Hin)]. }
    pose proof (sum_cc_le (h :: rest) Hall).
    destruct rest; [simpl in Hlen; discriminate|].
    simpl in H |- *. lia.
Qed.

(** The 3n-2 termination bound, matching the paper's
    Theorem 2 statement.  u₀ ≤ n by [unlabeled_le_transfers]
    and c₀ ≤ 2n-2 by [cc_plus2_le_twice_ct] (handshaking on
    fully-lifted trees), so u₀ + c₀ ≤ 3n - 2. *)
Lemma termination_bound :
  forall t,
    fully_lifted t = true ->
    non_empty t = true ->
    count_unlabeled t + count_children t <=
    3 * count_transfers t - 2.
Proof.
  intros t Hfl Hne.
  pose proof (unlabeled_le_transfers t).
  pose proof (cc_plus2_le_twice_ct t Hfl Hne).
  lia.
Qed.

(* ============================================================
   Section 19: Termination of the nondeterministic rewrite_step
   (Phase 2 and Phase 3 combined)

   Phase 2 (leaf manipulation rules R1--R10 and lift)
   and Phase 3 (annotation and merge) are jointly
   strongly normalizing under the lex measure
   ([count_children], [count_unlabeled]):
   every Phase-2 rule strictly reduces the total
   children count, while [RS_annotate] preserves it
   and reduces [count_unlabeled].
   ============================================================ *)

Definition measure_phase2 (t : reduced_cft) : nat * nat :=
  (count_children t, count_unlabeled t).
(* The lex order is (count_children, count_unlabeled).
   The primary component is [count_children]: every
   Phase-2 rule strictly decreases it. *)

(** Standard list_sum_app, proved locally to avoid
    relying on a particular stdlib name. *)
Lemma list_sum_app :
  forall (l1 l2 : list nat),
    list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
Proof.
  induction l1 as [|h rest IH]; intros l2; simpl;
    [reflexivity | rewrite IH; lia].
Qed.

(** Closed-form count_children of an RTree. *)
Lemma cc_RTree_sum :
  forall a children,
    count_children (RTree a children) =
    length children +
    list_sum (map count_children children).
Proof.
  intros. simpl. rewrite fold_to_sum. lia.
Qed.

(** Closed-form count_unlabeled of an RTree. *)
Lemma cu_RTree_sum :
  forall a children,
    count_unlabeled (RTree a children) =
    list_sum (map count_unlabeled children).
Proof.
  intros. simpl. rewrite fold_to_sum. lia.
Qed.

Lemma rewrite_step_decreases :
  forall from_ t1 t2, rewrite_step from_ t1 t2 ->
                lt_lex (measure_phase2 t2)
                       (measure_phase2 t1).
Proof.
  intros from_ t1 t2 Hstep.
  induction Hstep; unfold measure_phase2, lt_lex in *; subst.
  - (* RS_swap_chain (R1) *)
    left. simpl. lia.
  - (* RS_burn_chain (R2) *)
    left. simpl. lia.
  - (* RS_mint_chain (R3) *)
    left. simpl. lia.
  - (* RS_pool_cycle (R4) *)
    left. simpl. lia.
  - (* RS_router_chain (R5) *)
    left. simpl. lia.
  - (* RS_leaf_chain (R6) *)
    left. rewrite !cc_RTree_sum, !length_app, !map_app,
                  !list_sum_app. simpl. lia.
  - (* RS_node_leaf_chain (R12) *)
    left. rewrite !cc_RTree_sum, !length_app, !map_app,
                  !list_sum_app. simpl. lia.
  - (* RS_chain_seq (R10) *)
    left. rewrite !cc_RTree_sum, !length_app, !map_app,
                  !list_sum_app. simpl. lia.
  - (* RS_same_token_chain (R11) *)
    left. simpl. lia.
  - (* RS_lift *)
    left. rewrite !cc_RTree_sum, !length_app, !map_app,
                  !list_sum_app. simpl.
    rewrite !fold_to_sum. lia.
  - (* RS_merge_endpoints (R7) *)
    left. rewrite !cc_RTree_sum, !length_app, !map_app,
                  !list_sum_app. simpl. lia.
  - (* RS_merge_add (R8) *)
    left. rewrite !cc_RTree_sum, !length_app, !map_app,
                  !list_sum_app. simpl. lia.
  - (* RS_merge_closed_R9 *)
    left. rewrite !cc_RTree_sum, !length_app, !map_app,
                  !list_sum_app. simpl. lia.
  - (* RS_merge_node (R13) *)
    left. rewrite !cc_RTree_sum, !length_app, !map_app,
                  !list_sum_app. simpl. lia.
  - (* RS_annotate_arb (R14).  Produces Arbitrage label,
       which is_labeled, while c is unlabeled. *)
    right. split.
    + (* count_children unchanged *)
      rewrite !cc_RTree_sum, !length_app, !map_app,
              !list_sum_app. simpl. lia.
    + (* count_unlabeled strictly drops *)
      rewrite !cu_RTree_sum, !map_app, !list_sum_app. simpl.
      match goal with H : is_labeled _ = false |- _ => rewrite H end.
      match goal with H : ch_label _ = Arbitrage |- _ => rewrite H end.
      simpl. lia.
  - (* RS_annotate_cyc (R15).  Produces Cycle label,
       which is_labeled, while c is unlabeled. *)
    right. split.
    + (* count_children unchanged *)
      rewrite !cc_RTree_sum, !length_app, !map_app,
              !list_sum_app. simpl. lia.
    + (* count_unlabeled strictly drops *)
      rewrite !cu_RTree_sum, !map_app, !list_sum_app. simpl.
      match goal with H : is_labeled _ = false |- _ => rewrite H end.
      match goal with H : ch_label _ = Cycle |- _ => rewrite H end.
      simpl. lia.
  - (* RS_under (congruence) *)
    simpl in IHHstep.
    rewrite !cc_RTree_sum, !cu_RTree_sum, !length_app,
            !map_app, !list_sum_app. simpl.
    destruct IHHstep as [Hcc | [Hcc Hcu]].
    + left. lia.
    + right. split; lia.
Qed.

Lemma rewrite_step_wf :
  forall from_, well_founded (fun t' t => rewrite_step from_ t t').
Proof.
  intro from_. intro T.
  remember (measure_phase2 T) as m eqn:Hm.
  revert T Hm.
  induction m as [m IH]
    using (well_founded_induction lt_lex_wf).
  intros T Hm. constructor. intros T' Hstep.
  apply (IH (measure_phase2 T')).
  - subst. exact (rewrite_step_decreases from_ T T' Hstep).
  - reflexivity.
Qed.

(** Strong-normalization (constructive form): there
    are no infinite [rewrite_step]-chains.  Equivalent
    to [Acc]-based well-foundedness, exposed in this
    direct form for ease of reuse.  Constructive: no
    excluded middle. *)
Lemma rewrite_step_terminating :
  forall from_ (seq : nat -> reduced_cft),
    (forall n, rewrite_step from_ (seq n) (seq (S n))) -> False.
Proof.
  intros from_ seq Hstep.
  pose proof (rewrite_step_wf from_ (seq 0)) as Hacc.
  remember 0 as i eqn:Hi. clear Hi.
  revert i Hacc Hstep.
  fix IH 2.
  intros i Hacc Hstep.
  inversion Hacc as [Hin]. clear Hacc.
  apply (IH (S i)).
  - apply Hin. exact (Hstep i).
  - intros n. exact (Hstep n).
Qed.

(* ============================================================
   Section 20: Phase-2 confluence

   The Phase-2 leaf-pair step is realized as a
   deterministic computable function whose unique
   normal form follows from determinism and
   well-founded measure decrease, exactly as in
   Phase 3.  The priority cascade
   R5 > R2 > R3 > R4 > R10 > R1 selects exactly one
   rule per leaf pair, matching the precedence
   stated in Section 3.5.
   ============================================================ *)

(** [leaf_pair_chain] and [pool_cycle_chain] are defined in
    Section 5 (hoisted above [rewrite_step] for the [RS_lift]
    guard). *)

(** Deterministic leaf-pair combiner.  Priority
    R2 > R3 > (same-token: R5 > R4 > R11) / (different-
    token: R1), all under the shared adjacency guard
    [tr_dest t1 = tr_source t2].  This is the same
    burn-first cascade as [try_combine_leaves_full]
    (Section 16): the two agree by construction, so a
    single guarded relation is sound for both the
    Phase-2 kernel and the redex-complete kernel.  The
    earlier router-first ordering is superseded (it
    both diverged in labels from the full combiner and
    carried completeness holes: router-with-different-
    tokens returned [None]; R4 checked only one
    sender).  Determinism is a consequence of Property
    prop:dse on the input trace, not of the rule set. *)
Definition try_combine_leaves
    (t1 t2 : transfer) : option chain_tree :=
  if address_eq_dec (tr_dest t1) (tr_source t2) then
    if is_burn t1 && negb (is_mint t2)
    then Some (leaf_pair_chain TokenBurn t1 t2)      (* R2 *)
    else if is_mint t2 && negb (is_burn t1)
    then Some (leaf_pair_chain TokenMint t1 t2)      (* R3 *)
    else if token_eq_dec (tr_token t1) (tr_token t2) then
      if is_singleton_router (tr_dest t1)
      then Some (leaf_pair_chain Chaining t1 t2)     (* R5 *)
      else if is_burn t1 || is_mint t2 then None
      else if address_eq_dec (tr_dest t2) (tr_source t1) then
        if address_eq_dec (tr_sender t1) (tr_dest t1) then
          if address_eq_dec (tr_sender t2) (tr_dest t2)
          then None
          else Some (pool_cycle_chain t1 t2)         (* R4, t2 escape *)
        else Some (pool_cycle_chain t1 t2)           (* R4, t1 escape *)
      else if address_eq_dec (tr_sender t1) (tr_dest t1)
      then None
      else Some (leaf_pair_chain Chaining t1 t2)     (* R11 *)
    else Some (leaf_pair_chain Chaining t1 t2)       (* R1 *)
  else None.

(** Top-level Phase-2 step on a 2-leaf tree. *)
Definition phase2_step_fn (t : reduced_cft) : option reduced_cft :=
  match t with
  | RTree addr [RLeaf t1; RLeaf t2] =>
      match try_combine_leaves t1 t2 with
      | Some c => Some (RTree addr [RChain c])
      | None => None
      end
  | _ => None
  end.

Definition phase2_step_det (t t' : reduced_cft) : Prop :=
  phase2_step_fn t = Some t'.

(** Determinism follows from [phase2_step_fn] being
    a function on a DSE-ordered input: the ordering
    fixes which leaf pair is examined, so two
    derivations cannot diverge.  This is the same
    structural argument as Phase 3 confluence. *)
Lemma phase2_step_fn_det :
  forall t t1 t2,
    phase2_step_det t t1 ->
    phase2_step_det t t2 ->
    t1 = t2.
Proof.
  unfold phase2_step_det. intros t t1 t2 H1 H2.
  rewrite H1 in H2. injection H2; auto.
Qed.

(** Soundness: every function-step is a spec-step. *)
Lemma phase2_step_fn_sound :
  forall from_ t t',
    phase2_step_fn t = Some t' ->
    rewrite_step from_ t t'.
Proof.
  intros from_ t t' Hfn.
  unfold phase2_step_fn in Hfn.
  destruct t as [tr | c | addr children]; try discriminate.
  destruct children as [|x rest]; try discriminate.
  destruct x as [t1 | c1 | a1 ch1]; try discriminate.
  destruct rest as [|y rest']; try discriminate.
  destruct y as [t2 | c2 | a2 ch2]; try discriminate.
  destruct rest' as [|? ?]; try discriminate.
  unfold try_combine_leaves in Hfn.
  destruct (address_eq_dec (tr_dest t1) (tr_source t2))
    as [Hadj | _]; [| discriminate].
  destruct (is_burn t1 && negb (is_mint t2)) eqn:Hb2.
  { apply andb_true_iff in Hb2 as [Hburn Hnm].
    apply negb_true_iff in Hnm.
    injection Hfn as <-.
    apply (RS_burn_chain from_ t1 t2 _ addr Hburn Hnm Hadj eq_refl). }
  destruct (is_mint t2 && negb (is_burn t1)) eqn:Hm2.
  { apply andb_true_iff in Hm2 as [Hmint Hnb].
    apply negb_true_iff in Hnb.
    injection Hfn as <-.
    apply (RS_mint_chain from_ t1 t2 _ addr Hmint Hnb Hadj eq_refl). }
  pose proof (burn_mint_agree t1 t2 Hb2 Hm2) as Hbm.
  destruct (token_eq_dec (tr_token t1) (tr_token t2))
    as [Htok | Htok_ne].
  - destruct (is_singleton_router (tr_dest t1)) eqn:Hr.
    { injection Hfn as <-.
      apply (RS_router_chain from_ t1 t2 _ addr Hadj Htok Hr
               Hbm eq_refl). }
    destruct (is_burn t1 || is_mint t2) eqn:Hbo; [discriminate |].
    apply orb_false_iff in Hbo as [Hburn Hmint].
    destruct (address_eq_dec (tr_dest t2) (tr_source t1))
      as [Hcyc | Hncyc].
    + destruct (address_eq_dec (tr_sender t1) (tr_dest t1))
        as [Hs1 | Hs1].
      * destruct (address_eq_dec (tr_sender t2) (tr_dest t2))
          as [Hs2 | Hs2]; [discriminate |].
        injection Hfn as <-.
        apply (RS_pool_cycle from_ t1 t2 _ addr Hadj Hcyc Htok
                 Hburn Hmint Hr (or_intror Hs2) eq_refl).
      * injection Hfn as <-.
        apply (RS_pool_cycle from_ t1 t2 _ addr Hadj Hcyc Htok
                 Hburn Hmint Hr (or_introl Hs1) eq_refl).
    + destruct (address_eq_dec (tr_sender t1) (tr_dest t1))
        as [_ | Hs1]; [discriminate |].
      injection Hfn as <-.
      apply (RS_same_token_chain from_ t1 t2 _ addr Hadj Htok
               Hburn Hmint Hr Hncyc Hs1 eq_refl).
  - injection Hfn as <-.
    assert (Hch : chainable t1 t2)
      by (split; [exact Hadj | exact Htok_ne]).
    apply (RS_swap_chain from_ t1 t2 _ addr Hch Hbm eq_refl).
Qed.

(** Termination: every function-step strictly
    decreases [measure_phase2]. *)
Lemma phase2_step_fn_decreases :
  forall t t',
    phase2_step_fn t = Some t' ->
    lt_lex (measure_phase2 t') (measure_phase2 t).
Proof.
  intros t t' Hfn.
  destruct t as [ | | addr ch]; try discriminate Hfn.
  apply (rewrite_step_decreases addr).
  apply (phase2_step_fn_sound addr). exact Hfn.
Qed.

(** Reflexive-transitive closure of the
    deterministic Phase-2 step. *)
Inductive phase2_star_det : reduced_cft -> reduced_cft -> Prop :=
  | P2D_refl : forall t, phase2_star_det t t
  | P2D_step : forall t1 t2 t3,
      phase2_step_det t1 t2 ->
      phase2_star_det t2 t3 ->
      phase2_star_det t1 t3.

(** Determinism lifts to the closure: any two
    star-reductions ending in normal forms produce
    the same normal form. *)
Lemma phase2_star_deterministic :
  forall T T1 T2,
    phase2_star_det T T1 ->
    phase2_star_det T T2 ->
    (forall T', ~ phase2_step_det T1 T') ->
    (forall T', ~ phase2_step_det T2 T') ->
    T1 = T2.
Proof.
  intros T T1 T2 Hstar1.
  revert T2.
  induction Hstar1 as [T | T Tmid T1 Hstep1 Hstar1 IH].
  - intros T2 Hstar2 Hnf1 Hnf2.
    inversion Hstar2; subst.
    + reflexivity.
    + exfalso. exact (Hnf1 t2 H).
  - intros T2 Hstar2 Hnf1 Hnf2.
    inversion Hstar2; subst.
    + exfalso. exact (Hnf2 Tmid Hstep1).
    + assert (Tmid = t2) as Heq
        by exact (phase2_step_fn_det T Tmid t2 Hstep1 H).
      subst. exact (IH T2 H0 Hnf1 Hnf2).
Qed.

(** Phase-2 confluence (mirrors [confluence] for
    Phase 3): two normal forms reachable from the
    same term coincide.  Immediate from determinism. *)
Lemma phase2_confluence :
  forall T0 Tf1 Tf2,
    phase2_star_det T0 Tf1 ->
    phase2_star_det T0 Tf2 ->
    (forall T', ~ phase2_step_det Tf1 T') ->
    (forall T', ~ phase2_step_det Tf2 T') ->
    Tf1 = Tf2.
Proof.
  exact phase2_star_deterministic.
Qed.

(* ============================================================
   Section 21: Phase-3 bridge -- step_fn to rewrite_star
   ============================================================ *)

(** A reduced CFT is flat when its top-level [RTree] has only
    [RLeaf] or [RChain] children. *)
Definition flat_child (c : reduced_cft) : Prop :=
  match c with
  | RLeaf _ => True
  | RChain _ => True
  | RTree _ _ => False
  end.

Definition flat_rcft (T : reduced_cft) : Prop :=
  match T with
  | RLeaf _ => True
  | RChain _ => True
  | RTree _ children => Forall flat_child children
  end.

(** Transitivity of [rewrite_star]. *)
Lemma rewrite_star_trans :
  forall from_ t1 t2 t3,
    rewrite_star from_ t1 t2 ->
    rewrite_star from_ t2 t3 ->
    rewrite_star from_ t1 t3.
Proof.
  intros from_ t1 t2 t3 H12 H23.
  induction H12 as [t | t1 t2 t3' Hstep Hstar IH].
  - exact H23.
  - eapply RS_trans; [exact Hstep | apply IH; exact H23].
Qed.

Lemma rewrite_star_one :
  forall from_ t1 t2, rewrite_step from_ t1 t2 -> rewrite_star from_ t1 t2.
Proof.
  intros from_ t1 t2 Hstep.
  eapply RS_trans; [exact Hstep | apply RS_refl].
Qed.

(** [annotate_label] returns either [Arbitrage] or
    [Cycle]; the other [construction_label] tags are
    not reachable from this function. *)
Lemma annotate_label_arb_or_cyc :
  forall from_ c,
    annotate_label from_ c = Arbitrage \/
    annotate_label from_ c = Cycle.
Proof.
  intros from_ c. unfold annotate_label.
  destruct (negb (address_in_chain from_ c)); [left; reflexivity|].
  destruct (address_eq_dec (ch_origin c) from_);
    [left; reflexivity | right; reflexivity].
Qed.

(** [annotate_label = Arbitrage] precisely captures
    the R14 premise on [from]. *)
Lemma annotate_label_arb_implies :
  forall from_ c,
    annotate_label from_ c = Arbitrage ->
    address_in_chain from_ c = false \/ ch_origin c = from_.
Proof.
  intros from_ c Harb. unfold annotate_label in Harb.
  destruct (negb (address_in_chain from_ c)) eqn:Hnotin.
  - left. apply negb_true_iff in Hnotin. exact Hnotin.
  - destruct (address_eq_dec (ch_origin c) from_) as [Heq|];
      [right; exact Heq | discriminate].
Qed.

(** [annotate_label = Cycle] precisely captures the
    R15 premise on [from]. *)
Lemma annotate_label_cyc_implies :
  forall from_ c,
    annotate_label from_ c = Cycle ->
    address_in_chain from_ c = true.
Proof.
  intros from_ c Hcyc. unfold annotate_label in Hcyc.
  destruct (negb (address_in_chain from_ c)) eqn:Hnotin;
    [discriminate|].
  apply negb_false_iff. exact Hnotin.
Qed.

(** [annotate_label = Cycle] also entails the R15
    origin guard: the orchestrator is in the chain but
    is not its origin (else R14 would have fired). *)
Lemma annotate_label_cyc_implies_ne :
  forall from_ c,
    annotate_label from_ c = Cycle ->
    ch_origin c <> from_.
Proof.
  intros from_ c Hcyc. unfold annotate_label in Hcyc.
  destruct (negb (address_in_chain from_ c)); [discriminate|].
  destruct (address_eq_dec (ch_origin c) from_) as [_|Hne];
    [discriminate | exact Hne].
Qed.

(** [annotate_all_fn] preserves flatness. *)
Lemma annotate_all_fn_preserves_flat :
  forall from_ T,
    flat_rcft T -> flat_rcft (annotate_all_fn from_ T).
Proof.
  intros from_ T Hflat.
  destruct T as [tr | c | addr children]; simpl.
  - exact I.
  - destruct (_ && _ && _); [|exact I].
    destruct (annotate_label from_ c); try exact I.
    destruct (wrap_unwrap c); exact I.
  - simpl in Hflat.
    apply Forall_forall.
    intros c Hin.
    apply in_map_iff in Hin as [c0 [Heq Hin0]]; subst.
    rewrite Forall_forall in Hflat.
    specialize (Hflat c0 Hin0).
    destruct c0 as [tr0 | ch0 | a0 ch0]; simpl in *;
      [exact I | | contradiction].
    destruct (_ && _ && _); [|exact I].
    destruct (annotate_label from_ ch0); try exact I.
    destruct (wrap_unwrap ch0); exact I.
Qed.

(** Annotating a single chain in arbitrary [L ++ [.] ++ R]
    position is realized by zero or one declarative step. *)
Lemma annotate_chain_in_context :
  forall from_ addr L c R,
    rewrite_star from_
      (RTree addr (L ++ [RChain c] ++ R))
      (RTree addr
         (L ++ [annotate_all_fn from_ (RChain c)] ++ R)).
Proof.
  intros from_ addr L c R.
  simpl annotate_all_fn.
  destruct (negb (is_labeled (ch_label c))
            && (if address_eq_dec (ch_origin c) (ch_destination c)
                then true else false)
            && token_equiv (ch_token_in c) (ch_token_out c)) eqn:Hcond;
    [| apply RS_refl ].
  apply andb_prop in Hcond as [Hcond12 Htok].
  apply andb_prop in Hcond12 as [Hunl Hclo_eq].
  apply negb_true_iff in Hunl.
  destruct (address_eq_dec (ch_origin c) (ch_destination c))
    as [Hclo|]; [|discriminate].
  pose proof (annotate_label_arb_or_cyc from_ c) as [Harb|Hcyc].
  - rewrite Harb.
    destruct (wrap_unwrap c) eqn:Hwrap; [apply RS_refl|].
    destruct c as [t | o d m ti to_ ft lbl' lc rc].
    + simpl. apply RS_refl.
    + apply rewrite_star_one.
      apply (RS_annotate_arb from_ (CT_node o d m ti to_ ft lbl' lc rc)
        (CT_node o d m ti to_ ft Arbitrage lc rc) addr L R);
        try reflexivity.
      * exact Hclo.
      * exact Htok.
      * exact Hunl.
      * apply annotate_label_arb_implies. exact Harb.
      * exact Hwrap.
  - rewrite Hcyc.
    destruct c as [t | o d m ti to_ ft lbl' lc rc].
    + simpl. apply RS_refl.
    + apply rewrite_star_one.
      apply (RS_annotate_cyc from_ (CT_node o d m ti to_ ft lbl' lc rc)
        (CT_node o d m ti to_ ft Cycle lc rc) addr L R);
        try reflexivity.
      * exact Hclo.
      * exact Hunl.
      * apply annotate_label_cyc_implies. exact Hcyc.
      * right. right.
        apply annotate_label_cyc_implies_ne. exact Hcyc.
Qed.

(** Annotating a single [flat_child] (RLeaf or RChain)
    in arbitrary position is realized by zero or one
    declarative step. *)
Lemma annotate_one_in_context :
  forall from_ addr L c R,
    flat_child c ->
    rewrite_star from_
      (RTree addr (L ++ [c] ++ R))
      (RTree addr (L ++ [annotate_all_fn from_ c] ++ R)).
Proof.
  intros from_ addr L c R Hflat.
  destruct c as [tr | ch | a children]; simpl in Hflat.
  - simpl. apply RS_refl.
  - apply annotate_chain_in_context.
  - contradiction.
Qed.

(** Cascade: walk through the children list left-to-right,
    annotating each child in turn.  The already-processed
    children act as the left context [L]; the not-yet-
    processed children act as the right context [R]. *)
Lemma annotate_cascade :
  forall from_ addr done todo,
    Forall flat_child todo ->
    rewrite_star from_
      (RTree addr (done ++ todo))
      (RTree addr (done ++ map (annotate_all_fn from_) todo)).
Proof.
  intros from_ addr done todo.
  revert done.
  induction todo as [|h rest IH]; intros done Hflat.
  - simpl. rewrite app_nil_r. apply RS_refl.
  - inversion Hflat as [|? ? Hh Hrest]; subst.
    simpl.
    eapply rewrite_star_trans.
    + change (h :: rest) with ([h] ++ rest).
      apply (annotate_one_in_context from_ addr done h rest Hh).
    + specialize (IH (done ++ [annotate_all_fn from_ h]) Hrest).
      rewrite <- !app_assoc in IH. simpl in IH.
      exact IH.
Qed.

(** [annotate_all_fn] on an [RTree] with flat children
    is realized by a sequence of [RS_annotate_arb] /
    [RS_annotate_cyc] applications.  The [RTree] shape
    holds by construction: [Build-AST] produces an
    [RTree] root (the transaction call frame), so the
    top-level input to Phase 3 is always an [RTree]. *)
Lemma annotate_all_fn_to_rewrite_star :
  forall from_ addr children,
    Forall flat_child children ->
    rewrite_star from_
      (RTree addr children)
      (annotate_all_fn from_ (RTree addr children)).
Proof.
  intros from_ addr children Hflat.
  simpl.
  change children with ([] ++ children) at 1.
  apply (annotate_cascade from_ addr [] children Hflat).
Qed.

(** [merge_match c1 c2 cm] captures the precondition
    that one of the declarative merge rules
    (R7/R8/R9/R13) applies to the chain pair, with
    the merged chain [cm] carrying the [Merging]
    label and the joined transfer list.  The kernel's
    [chains_mergeable] alone does not entail this
    structural predicate; [merge_match] is the precise
    invariant the kernel must maintain to align with
    the declarative semantics. *)
Definition merge_match
    (c1 c2 cm : chain_tree) : Prop :=
  (* Operands are labeled (merge combines annotated cycles) *)
  is_labeled (ch_label c1) = true /\
  is_labeled (ch_label c2) = true /\
  (* Endpoints agree and the merged transfer list concatenates *)
  ch_origin c1 = ch_origin c2 /\
  ch_destination c1 = ch_destination c2 /\
  ch_origin cm = ch_origin c1 /\
  ch_destination cm = ch_destination c1 /\
  ch_token_in cm = ch_token_in c1 /\
  ch_token_out cm = ch_token_out c2 /\
  ch_label cm = Merging /\
  ch_children cm = Some (c1, c2) /\
  chain_transfers cm = chain_transfers c1 ++ chain_transfers c2 /\
  (* One of R7/R8/R9/R13's token premise disjuncts holds *)
  ( (* R7: parallel paths *)
    (ch_origin c1 <> ch_destination c1 /\
     ch_token_out c1 = ch_token_out c2 /\
     ch_token_mid c1 <> ch_token_mid c2) \/
    (* R8: closed, tokens match (or BalCont) *)
    (ch_origin c1 = ch_destination c1 /\
     ((ch_token_in c1 = ch_token_in c2 /\
       ch_token_mid c1 = ch_token_mid c2 /\
       ch_token_out c1 = ch_token_out c2) \/
      bal_cont (ch_origin c1) c1 c2 = true)) \/
    (* R9: closed at single vertex, both boundary tokens match *)
    (ch_origin c1 = ch_destination c1 /\
     ch_origin c2 = ch_destination c2 /\
     ch_token_in c1 = ch_token_in c2 /\
     ch_token_out c1 = ch_token_out c2) \/
    (* R13: R7 with the entry tokens pinned as well *)
    (ch_origin c1 <> ch_destination c1 /\
     ch_token_out c1 = ch_token_out c2 /\
     ch_token_mid c1 <> ch_token_mid c2 /\
     ch_token_in c1 = ch_token_in c2) ).

(** A [merge_match]-justified merge step is realized
    by exactly one of [RS_merge_endpoints],
    [RS_merge_add], [RS_merge_closed_R9], or
    [RS_merge_node].  The proof case-splits on
    [merge_match]'s disjunction. *)
Lemma merge_match_to_rewrite_step :
  forall from_ c1 c2 cm addr L M R,
    merge_match c1 c2 cm ->
    rewrite_step from_
      (RTree addr (L ++ [RChain c1] ++ M ++ [RChain c2] ++ R))
      (RTree addr (L ++ M ++ [RChain cm] ++ R)).
Proof.
  intros from_ c1 c2 cm addr L M R Hm.
  destruct Hm as [Hl1 [Hl2 [Ho [Hd [Hom [Hdm [Htim [Htom [Hlbl [Hch [Htfs Hcase]]]]]]]]]]].
  destruct Hcase as [HR7 | [HR8 | [HR9 | HR13]]].
  - (* R7 *)
    destruct HR7 as [Hne [Htout Hmid]].
    eapply RS_merge_endpoints; eauto.
  - (* R8 *)
    destruct HR8 as [Hcl Htok].
    eapply RS_merge_add; eauto.
  - (* R9 *)
    destruct HR9 as [Hc1 [Hc2 [Htin Htout]]].
    eapply RS_merge_closed_R9; eauto.
  - (* R13 *)
    destruct HR13 as [Hne [Htout [Hmid Htin]]].
    eapply RS_merge_node; eauto.
Qed.

(** Subsequent [RS_annotate_arb] / [RS_annotate_cyc]
    relabels the [Merging]-labeled merged chain to
    [Arbitrage] or [Cycle], matching the kernel's
    [merge_two_chains] output.  Premised on closure
    (origin = destination), which is what makes
    annotation applicable. *)
Lemma annotate_after_merge :
  forall from_ cm cm' addr L M R,
    ch_label cm = Merging ->
    ch_origin cm = ch_destination cm ->
    token_equiv (ch_token_in cm) (ch_token_out cm) = true ->
    chain_transfers cm' = chain_transfers cm ->
    ch_origin cm' = ch_origin cm ->
    ch_destination cm' = ch_destination cm ->
    ch_token_in cm' = ch_token_in cm ->
    ch_token_out cm' = ch_token_out cm ->
    cm' = set_chain_label cm (ch_label cm') ->
    ( (ch_label cm' = Arbitrage /\
       (address_in_chain from_ cm = false \/
        ch_origin cm = from_) /\
       wrap_unwrap cm = false) \/
      (ch_label cm' = Cycle /\
       address_in_chain from_ cm = true /\
       ch_origin cm <> from_) ) ->
    rewrite_step from_
      (RTree addr (L ++ M ++ [RChain cm] ++ R))
      (RTree addr (L ++ M ++ [RChain cm'] ++ R)).
Proof.
  intros from_ cm cm' addr L M R Hlbl Hcl Htok Htfs Hom Hdm Hti Hto
         Hrelabel Hcase.
  assert (Hunl : is_labeled (ch_label cm) = false)
    by (rewrite Hlbl; reflexivity).
  rewrite (app_assoc L M).
  rewrite (app_assoc L M ([RChain cm'] ++ R)).
  destruct Hcase as [[Hlbl' [Hfr Hwr]] | [Hlbl' [Hin Hne]]];
    rewrite Hlbl' in Hrelabel.
  - apply (RS_annotate_arb from_ cm cm' addr (L ++ M) R); assumption.
  - apply (RS_annotate_cyc from_ cm cm' addr (L ++ M) R);
      try assumption.
    right. right. exact Hne.
Qed.

(** [step_fn_witness from_ children new_children] is
    the structural invariant the kernel maintains for
    [step_fn] to align with the declarative semantics.
    A deployment satisfying it gets [rewrite_star]
    coverage of every [step_fn] step via [annotate]
    plus one merge step plus an optional relabel. *)
Definition step_fn_witness
    (from_ : address)
    (children new_children : list reduced_cft) : Prop :=
  Forall flat_child children /\
  exists L c1 M c2 R cm cm',
    children = L ++ [RChain c1] ++ M ++ [RChain c2] ++ R /\
    new_children = L ++ M ++ [RChain cm'] ++ R /\
    merge_match c1 c2 cm /\
    ch_label cm = Merging /\
    ch_origin cm = ch_destination cm /\
    token_equiv (ch_token_in cm) (ch_token_out cm) = true /\
    chain_transfers cm' = chain_transfers cm /\
    ch_origin cm' = ch_origin cm /\
    ch_destination cm' = ch_destination cm /\
    ch_token_in cm' = ch_token_in cm /\
    ch_token_out cm' = ch_token_out cm /\
    cm' = set_chain_label cm (ch_label cm') /\
    ( (ch_label cm' = Arbitrage /\
       (address_in_chain from_ cm = false \/
        ch_origin cm = from_) /\
       wrap_unwrap cm = false) \/
      (ch_label cm' = Cycle /\
       address_in_chain from_ cm = true /\
       ch_origin cm <> from_) ).

(** Phase-3 step is realized by [rewrite_star] when
    the kernel's merge satisfies [step_fn_witness]:
    one merge step ([merge_match_to_rewrite_step])
    followed by one relabel ([annotate_after_merge]).
    The annotate pass produced the [Merging]-shaped
    chain that the merge rule consumes. *)
Lemma step_fn_witness_to_rewrite_star :
  forall from_ addr children new_children,
    step_fn_witness from_ children new_children ->
    rewrite_star from_
      (RTree addr children)
      (RTree addr new_children).
Proof.
  intros from_ addr children new_children Hw.
  destruct Hw as [Hflat Hex].
  destruct Hex as
    [L [c1 [M [c2 [R [cm [cm'
       [Hin [Hout [Hmm [Hlbl [Hcl [Htok
       [Htfs [Hom [Hdm [Hti [Hto [Hrelabel Hcase]]]]]]]]]]]]]]]]]]].
  subst children new_children.
  eapply RS_trans.
  - apply (merge_match_to_rewrite_step from_ c1 c2 cm addr L M R Hmm).
  - apply rewrite_star_one.
    apply (annotate_after_merge from_ cm cm' addr L M R);
      assumption.
Qed.

(** [canonical_merge c1 c2] is the [Merging]-labeled
    chain the declarative semantics produces.  Same
    shape as [merge_two_chains] but with the label
    fixed to [Merging] (annotation later relabels). *)
Definition canonical_merge (c1 c2 : chain_tree) : chain_tree :=
  CT_node (ch_origin c1) (ch_destination c2) []
          (ch_token_in c1) (ch_token_out c2)
          (ch_first_transfer c1) Merging c1 c2.

Lemma chains_mergeable_inv :
  forall c1 c2,
    chains_mergeable c1 c2 = true ->
    is_labeled (ch_label c1) = true /\
    is_labeled (ch_label c2) = true /\
    ch_origin c1 = ch_origin c2 /\
    ch_destination c1 = ch_destination c2 /\
    ch_origin c1 = ch_destination c1 /\
    ch_token_in c1 = ch_token_in c2 /\
    ch_token_out c1 = ch_token_out c2 /\
    token_equiv (ch_token_in c1) (ch_token_out c2) = true.
Proof.
  intros c1 c2 Hm. unfold chains_mergeable in Hm.
  repeat (apply andb_true_iff in Hm as [Hm ?]).
  repeat split; try assumption.
  - destruct (address_eq_dec (ch_origin c1) (ch_origin c2));
      [auto | discriminate].
  - destruct (address_eq_dec (ch_destination c1) (ch_destination c2));
      [auto | discriminate].
  - destruct (address_eq_dec (ch_origin c1) (ch_destination c1));
      [auto | discriminate].
  - destruct (token_eq_dec (ch_token_in c1) (ch_token_in c2));
      [auto | discriminate].
  - destruct (token_eq_dec (ch_token_out c1) (ch_token_out c2));
      [auto | discriminate].
Qed.

Lemma merge_match_holds :
  forall c1 c2,
    chains_mergeable c1 c2 = true ->
    merge_match c1 c2 (canonical_merge c1 c2).
Proof.
  intros c1 c2 Hm.
  apply chains_mergeable_inv in Hm.
  destruct Hm as [Hl1 [Hl2 [Ho [Hd [Hcl [Hti [Hto Htok]]]]]]].
  unfold merge_match, canonical_merge.
  repeat split; simpl; auto.
  right. right. left.
  split; [exact Hcl|]. split; [| split; [exact Hti | exact Hto]].
  rewrite <- Hd, <- Ho. exact Hcl.
Qed.

Lemma merge_match_closure :
  forall c1 c2,
    chains_mergeable c1 c2 = true ->
    ch_origin (canonical_merge c1 c2)
      = ch_destination (canonical_merge c1 c2).
Proof.
  intros c1 c2 Hm.
  apply chains_mergeable_inv in Hm.
  destruct Hm as [_ [_ [_ [Hd [Hcl _]]]]].
  unfold canonical_merge. simpl.
  rewrite <- Hd. exact Hcl.
Qed.

Lemma merge_match_token :
  forall c1 c2,
    chains_mergeable c1 c2 = true ->
    token_equiv
      (ch_token_in (canonical_merge c1 c2))
      (ch_token_out (canonical_merge c1 c2)) = true.
Proof.
  intros c1 c2 Hm.
  apply chains_mergeable_inv in Hm.
  destruct Hm as [_ [_ [_ [_ [_ [_ [_ Htok]]]]]]].
  unfold canonical_merge. simpl.
  exact Htok.
Qed.

(** Factorization: a successful [scan_and_merge]
    locates a partner [c2] inside [after] and rewrites
    the children list with the merged chain in [c2]'s
    position.  Pure structural decomposition; no
    flatness needed. *)
Lemma scan_and_merge_factor :
  forall from_ c1 prefix before after new_children,
    scan_and_merge c1 from_ prefix before after = Some new_children ->
    exists mid c2 after',
      after = mid ++ RChain c2 :: after' /\
      new_children =
        prefix ++ (before ++ mid) ++
        [RChain (merge_two_chains from_ c1 c2)] ++ after' /\
      (chains_mergeable c1 c2 = true \/
       chains_unlabeled_mergeable c1 c2 = true).
Proof.
  intros from_ c1 prefix before after.
  revert before.
  induction after as [|x after' IH]; intros before nc Hsm.
  - simpl in Hsm. discriminate.
  - simpl in Hsm.
    destruct x as [t | c2 | a chs].
    + (* RLeaf: recurse *)
      specialize (IH (before ++ [RLeaf t]) nc Hsm).
      destruct IH as [mid [c2 [after2 [Heq [Hnc Hmm]]]]].
      exists (RLeaf t :: mid), c2, after2.
      split; [|split; [|exact Hmm]].
      * simpl. rewrite Heq. reflexivity.
      * rewrite Hnc, <- (app_assoc before [RLeaf t] mid). reflexivity.
    + (* RChain c2: merge fires or recurse *)
      destruct (chains_mergeable c1 c2
                || chains_unlabeled_mergeable c1 c2) eqn:Hmm.
      * injection Hsm as <-.
        exists [], c2, after'.
        split; [reflexivity|].
        split; [rewrite app_nil_r; reflexivity|].
        apply orb_true_iff in Hmm. exact Hmm.
      * specialize (IH (before ++ [RChain c2]) nc Hsm).
        destruct IH as [mid [c2x [after2 [Heq [Hnc Hmm2]]]]].
        exists (RChain c2 :: mid), c2x, after2.
        split; [|split; [|exact Hmm2]].
        -- simpl. rewrite Heq. reflexivity.
        -- rewrite Hnc, <- (app_assoc before [RChain c2] mid). reflexivity.
    + (* RTree: recurse *)
      specialize (IH (before ++ [RTree a chs]) nc Hsm).
      destruct IH as [mid [c2 [after2 [Heq [Hnc Hmm]]]]].
      exists (RTree a chs :: mid), c2, after2.
      split; [|split; [|exact Hmm]].
      * simpl. rewrite Heq. reflexivity.
      * rewrite Hnc, <- (app_assoc before [RTree a chs] mid). reflexivity.
Qed.

(** Top-level: a successful [try_merge_children]
    factors the input list into a left-context, a
    [c1] pivot, a middle, a [c2] partner, and a
    right-context, with the merged chain inserted at
    [c2]'s position. *)
Lemma try_merge_children_factor :
  forall from_ prefix suffix new_children,
    try_merge_children from_ prefix suffix = Some new_children ->
    exists L c1 M c2 R,
      prefix ++ suffix =
        L ++ [RChain c1] ++ M ++ [RChain c2] ++ R /\
      new_children =
        L ++ M ++ [RChain (merge_two_chains from_ c1 c2)] ++ R /\
      (chains_mergeable c1 c2 = true \/
       chains_unlabeled_mergeable c1 c2 = true).
Proof.
  intros from_ prefix suffix.
  revert prefix.
  induction suffix as [|child rest IH]; intros prefix nc Htmc.
  - simpl in Htmc. discriminate.
  - simpl in Htmc.
    destruct (find_and_merge from_ prefix child rest)
      as [n|] eqn:Hfm.
    + injection Htmc as <-.
      unfold find_and_merge in Hfm.
      destruct child as [t | c1 | a chs]; try discriminate.
      apply scan_and_merge_factor in Hfm.
      destruct Hfm as [mid [c2 [after' [Heq [Hnc Hmm]]]]].
      exists prefix, c1, mid, c2, after'.
      split; [|split; [|exact Hmm]].
      * simpl. rewrite Heq. reflexivity.
      * rewrite Hnc, app_nil_l. reflexivity.
    + specialize (IH (prefix ++ [child]) nc Htmc).
      destruct IH as [L [c1 [M [c2 [R [Hin [Hnc Hmm]]]]]]].
      exists L, c1, M, c2, R.
      split; [|split; [exact Hnc | exact Hmm]].
      rewrite <- Hin, <- app_assoc. reflexivity.
Qed.

(** Composition: [try_merge_children]'s output is
    realized by [rewrite_star] via [merge_match]
    (from the deployment Parameter) and the merge
    bridge.  This is the unconditional Phase-3 step
    bridge. *)
Lemma try_merge_children_to_rewrite_star :
  forall from_ addr prefix suffix new_children,
    (forall c, In (RChain c) (prefix ++ suffix) ->
               is_labeled (ch_label c) = true) ->
    try_merge_children from_ prefix suffix = Some new_children ->
    rewrite_star from_
      (RTree addr (prefix ++ suffix))
      (RTree addr new_children).
Proof.
  intros from_ addr prefix suffix new_children Hlab Htmc.
  apply try_merge_children_factor in Htmc.
  destruct Htmc as [L [c1 [M [c2 [R [Hin [Hnc Hmm]]]]]]].
  assert (Hl1 : is_labeled (ch_label c1) = true).
  { apply Hlab. rewrite Hin.
    rewrite in_app_iff. right.
    rewrite in_app_iff. left. simpl. left. reflexivity. }
  assert (Hl2 : is_labeled (ch_label c2) = true).
  { apply Hlab. rewrite Hin.
    rewrite in_app_iff. right.
    rewrite in_app_iff. right.
    rewrite in_app_iff. right.
    rewrite in_app_iff. left. simpl. left. reflexivity. }
  rewrite Hin, Hnc.
  destruct Hmm as [Hcm | Hunl].
  - (* chains_mergeable case: two declarative steps. *)
    pose proof (chains_mergeable_inv c1 c2 Hcm) as Hcminv.
    destruct Hcminv as [_ [_ [Ho [Hd [Hcl [Hti _]]]]]].
    eapply RS_trans.
    + apply (merge_match_to_rewrite_step from_ c1 c2
               (canonical_merge c1 c2) addr L M R).
      apply merge_match_holds, Hcm.
    + apply rewrite_star_one.
      apply (annotate_after_merge from_ (canonical_merge c1 c2)
               (merge_two_chains from_ c1 c2) addr L M R).
      * reflexivity.
      * apply merge_match_closure, Hcm.
      * apply merge_match_token, Hcm.
      * unfold canonical_merge, merge_two_chains. reflexivity.
      * unfold canonical_merge, merge_two_chains. reflexivity.
      * unfold canonical_merge, merge_two_chains. reflexivity.
      * unfold canonical_merge, merge_two_chains. reflexivity.
      * unfold canonical_merge, merge_two_chains. reflexivity.
      * (* Hrelabel: merge_two_chains = relabel of canonical_merge *)
        unfold canonical_merge, merge_two_chains, set_chain_label, ch_label.
        reflexivity.
      * (* Dispatch on Arbitrage vs Cycle from merge_two_chains.
           [merge_two_chains] labels via [annotate_label] on the
           merged node, so the R14/R15 premises follow from the
           [annotate_label] characterizations. *)
        assert (Hwrap : wrap_unwrap (canonical_merge c1 c2) = false)
          by reflexivity.
        assert (Hlab_eq :
                  ch_label (merge_two_chains from_ c1 c2)
                  = annotate_label from_ (canonical_merge c1 c2))
          by reflexivity.
        rewrite Hlab_eq.
        destruct (annotate_label_arb_or_cyc from_ (canonical_merge c1 c2))
          as [Harb | Hcyc].
        -- left. split; [exact Harb|].
           split;
             [ apply annotate_label_arb_implies; exact Harb | exact Hwrap ].
        -- right. split; [exact Hcyc|].
           split;
             [ apply annotate_label_cyc_implies; exact Hcyc
             | apply annotate_label_cyc_implies_ne; exact Hcyc ].
  - (* chains_unlabeled_mergeable case: [Hl1] says [c1] is
       labeled, but [Hunl] entails [c1] is unlabeled.
       Contradiction. *)
    exfalso. unfold chains_unlabeled_mergeable in Hunl.
    repeat (apply andb_true_iff in Hunl as [Hunl ?]).
    apply negb_true_iff in Hunl.
    rewrite Hunl in Hl1. discriminate.
Qed.

(** Two terms are joinable when they both reduce to a common term. *)
Definition joinable (from_ : address) (T1 T2 : reduced_cft) : Prop :=
  exists U, fixpoint_star_det from_ T1 U /\
            fixpoint_star_det from_ T2 U.

(** Normal form of a term: the unique irreducible reduct. *)
Definition nf (from_ : address) (T Tf : reduced_cft) : Prop :=
  fixpoint_star_det from_ T Tf /\
  (forall T', ~ fixpoint_step_det from_ Tf T').

(** Theorem 5 (Decidable equivalence):
    Two terms are joinable iff their normal forms coincide. *)
(** Transitivity of the reflexive-transitive closure. *)
Lemma fixpoint_star_det_trans :
  forall from_ t1 t2 t3,
    fixpoint_star_det from_ t1 t2 ->
    fixpoint_star_det from_ t2 t3 ->
    fixpoint_star_det from_ t1 t3.
Proof.
  intros from_ t1 t2 t3 H12 H23.
  induction H12 as [| a b c Hstep Hstar IH].
  - exact H23.
  - eapply FSD_step. exact Hstep. apply IH. exact H23.
Qed.

(** Theorem 5: Decidable structural equivalence
    (for fixed Routers).

    Two reduced CFTs are joinable under the fixpoint
    step iff their unique normal forms coincide.
    The equivalence is implicitly parameterized by
    the file-level [is_singleton_router] Parameter:
    R5 (router-chain) and the merge guards depend
    on it, so two analysts running with different
    Routers configurations would produce different
    canonical forms.  Within a single extraction
    (or, equivalently, a fixed Routers registry),
    the equivalence is decidable. *)
Lemma decidable_equivalence :
  forall from_ (T1 T2 Nf1 Nf2 : reduced_cft),
    nf from_ T1 Nf1 ->
    nf from_ T2 Nf2 ->
    (joinable from_ T1 T2 <-> Nf1 = Nf2).
Proof.
  intros from_ T1 T2 Nf1 Nf2 [Hstar1 Hnf1] [Hstar2 Hnf2].
  split.
  - (* joinable -> Nf1 = Nf2 *)
    intros [U [HU1 HU2]].
    destruct (fixpoint_terminates from_ U) as [Nfu [HstarU HnfU]].
    assert (Nf1 = Nfu).
    { apply (confluence from_ T1 Nf1 Nfu Hstar1
        (fixpoint_star_det_trans from_ T1 U Nfu HU1 HstarU)
        Hnf1 HnfU). }
    assert (Nf2 = Nfu).
    { apply (confluence from_ T2 Nf2 Nfu Hstar2
        (fixpoint_star_det_trans from_ T2 U Nfu HU2 HstarU)
        Hnf2 HnfU). }
    symmetry in H. rewrite H in H0. symmetry in H0. apply H0. (* congruence*)
  - (* Nf1 = Nf2 -> joinable *)
    intros Heq. subst Nf2.
    exists Nf1. split. apply Hstar1. apply Hstar2. (* split; assumption.*)
Qed.

(* ############################################################
   Part IV -- Soundness into the transfer graph
   ############################################################ *)

(* ============================================================
   Section 22: Refinement of transfer-graph cycles

   Every chain in a reachable reduced CFT labeled
   [Arbitrage] forms a closed walk in T0's transfer
   graph using only edges from T0.  The proof maintains
   two invariants on every chain in the rcft:
   endpoint correspondence ([endpoints_match]) and
   closure under the [Arbitrage] label.  The invariant
   propagates from any [no_chains] initial state
   through [rewrite_star] and yields the structural
   refinement.
   ============================================================ *)

(** Endpoint correspondence: a chain's structural origin and
    destination match the source of its first leaf and the
    destination of its last leaf. *)
Definition endpoints_match (c : chain_tree) : Prop :=
  match chain_transfers c with
  | [] => False
  | t :: _ =>
      ch_origin c = tr_source t /\
      ch_destination c = tr_dest (last (chain_transfers c) t)
  end.

(** Recursive endpoint correspondence: [endpoints_match] holds at
    every node of the chain, not just the root.  Robust to the
    annotate label overwrite (R14/R15), which preserves each node's
    stored origin/destination fields.  This is what pins the walk-set
    count to [seg_count] (see [walk_decomposition_count]). *)
Fixpoint endpoints_match_rec (c : chain_tree) : Prop :=
  endpoints_match c /\
  match c with
  | CT_transfer _ => True
  | CT_node _ _ _ _ _ _ _ l r =>
      endpoints_match_rec l /\ endpoints_match_rec r
  end.

Lemma endpoints_match_rec_top :
  forall c, endpoints_match_rec c -> endpoints_match c.
Proof. intros c H. destruct c; simpl in H; destruct H as [H1 _]; exact H1. Qed.

Lemma endpoints_match_rec_leaf :
  forall t, endpoints_match_rec (CT_transfer t).
Proof.
  intro t. simpl. split; [| exact I].
  unfold endpoints_match. simpl. split; reflexivity.
Qed.

(** Universal node constructor for [endpoints_match_rec]: any chain
    whose immediate children are [c1], [c2] gets the recursive
    invariant from [endpoints_match] at the root plus the recursive
    invariant of the two children.  Every rewrite rule builds its new
    chain as such a node (via [ch_children]), so its endpoints_match_rec
    follows from the existing root proof and the operands' invariants. *)
Lemma emr_from_children :
  forall c c1 c2,
    ch_children c = Some (c1, c2) ->
    endpoints_match c ->
    endpoints_match_rec c1 ->
    endpoints_match_rec c2 ->
    endpoints_match_rec c.
Proof.
  intros c c1 c2 Hch Hem H1 H2.
  destruct c as [t | o d m ti to_ ft lbl l r]; [discriminate Hch|].
  simpl in Hch. injection Hch as Hc1 Hc2. subst.
  simpl. split; [exact Hem | split; assumption].
Qed.

(** Annotation (R14/R15) only rewrites the label, preserving every
    node's stored origin/destination and its leaves, so it preserves
    [endpoints_match_rec]. *)
Lemma emr_set_label :
  forall c l, endpoints_match_rec c -> endpoints_match_rec (set_chain_label c l).
Proof.
  intros c l H. destruct c as [t | o d m ti to_ ft lbl lc rc]; [exact H|].
  simpl in H |- *. destruct H as [Hem [Hl Hr]].
  split; [exact Hem | split; [exact Hl | exact Hr]].
Qed.

(** Boundary-token correspondence: a chain's stored input and output
    tokens are the tokens of its first and last leaf.  The token
    analogue of [endpoints_match], and the invariant that Definition 5's
    same-asset condition reads.

    Root level suffices (unlike [endpoints_match_rec], which the
    walk-count development needs at every node): the property is already
    closed under the chain constructors, since each takes its input
    token from its left operand and its output token from its right,
    exactly matching the ends of the concatenated leaf list. *)
Definition tokens_match (c : chain_tree) : Prop :=
  match chain_transfers c with
  | [] => False
  | t :: _ =>
      ch_token_in c = tr_token t /\
      ch_token_out c = tr_token (last (chain_transfers c) t)
  end.

(** Introduction from an explicit cons form, mirroring
    [endpoints_match_cons]. *)
Lemma tokens_match_cons :
  forall c first_t rest,
    chain_transfers c = first_t :: rest ->
    ch_token_in c = tr_token first_t ->
    ch_token_out c = tr_token (last (first_t :: rest) first_t) ->
    tokens_match c.
Proof.
  intros c first_t rest Hct Hin Hout.
  unfold tokens_match. rewrite Hct. split; assumption.
Qed.

Lemma tokens_match_leaf : forall t, tokens_match (CT_transfer t).
Proof. intro t. unfold tokens_match. split; reflexivity. Qed.

(** Elimination: exhibit the first leaf.  Nonemptiness comes from the
    property itself, whose empty branch is [False]. *)
Lemma tokens_match_head :
  forall c, tokens_match c ->
    exists t rest,
      chain_transfers c = t :: rest /\
      ch_token_in c = tr_token t /\
      ch_token_out c = tr_token (last (chain_transfers c) t).
Proof.
  intros c H. unfold tokens_match in H.
  destruct (chain_transfers c) as [| t rest]; [contradiction|].
  exists t, rest. destruct H as [Hi Ho].
  split; [reflexivity | split; [exact Hi | exact Ho]].
Qed.

(** Annotation rewrites only the label. *)
Lemma tokens_match_set_label :
  forall c l, tokens_match c -> tokens_match (set_chain_label c l).
Proof.
  intros c l H. unfold tokens_match in *.
  rewrite set_chain_label_chain_transfers,
          set_chain_label_token_in, set_chain_label_token_out.
  exact H.
Qed.

(** Invariant on a reduced CFT: every chain has [endpoints_match_rec]
    (matching endpoints at every node), and any chain labeled Arbitrage
    additionally has closure (origin = destination). *)
Definition rcft_invariant (T : reduced_cft) : Prop :=
  forall c, chain_in_rcft c T ->
    endpoints_match_rec c /\
    tokens_match c /\
    (ch_label c = Arbitrage -> ch_origin c = ch_destination c) /\
    (ch_label c = Arbitrage ->
     token_equiv (ch_token_in c) (ch_token_out c) = true).

(** Initial CFTs from [Build-AST] have only [RLeaf] nodes
    nested inside [RTree] structure, with no [RChain]
    children.  Such CFTs satisfy [rcft_invariant] vacuously
    because no chain appears in them.  Any reachable rcft
    obtained by [rewrite_star] from such an initial state
    inherits the invariant. *)
Definition no_chains (T : reduced_cft) : Prop :=
  forall c, ~ chain_in_rcft c T.

Lemma no_chains_implies_invariant :
  forall T, no_chains T -> rcft_invariant T.
Proof.
  intros T Hnc c Hin. exfalso. apply (Hnc c Hin).
Qed.

(** Membership iff helpers for [chain_in_rcft]. *)

Lemma chain_in_RChain_iff :
  forall c c0,
    chain_in_rcft c (RChain c0) <-> c = c0.
Proof.
  intros c c0. split.
  - intros H. inversion H; subst. reflexivity.
  - intros ->. apply CIR_here.
Qed.

Lemma chain_in_RLeaf_no :
  forall c t, ~ chain_in_rcft c (RLeaf t).
Proof.
  intros c t H. inversion H.
Qed.

Lemma chain_in_RTree_iff :
  forall c addr children,
    chain_in_rcft c (RTree addr children) <->
    (exists child, In child children /\ chain_in_rcft c child).
Proof.
  intros c addr children. split.
  - intros H. inversion H; subst. exists child; split; assumption.
  - intros [child [Hin Hch]]. eapply CIR_tree; eassumption.
Qed.

(** A chain c is in [RTree addr (l1 ++ l2)] iff it is in the
    [l1] portion or the [l2] portion. *)
Lemma chain_in_RTree_app :
  forall c addr l1 l2,
    chain_in_rcft c (RTree addr (l1 ++ l2)) <->
    (exists child, In child l1 /\ chain_in_rcft c child) \/
    (exists child, In child l2 /\ chain_in_rcft c child).
Proof.
  intros c addr l1 l2. rewrite chain_in_RTree_iff. split.
  - intros [child [Hin Hch]]. apply in_app_iff in Hin.
    destruct Hin; [left | right]; exists child; split; assumption.
  - intros [[child [Hin Hch]] | [child [Hin Hch]]].
    + exists child; split; [apply in_app_iff; left; exact Hin | exact Hch].
    + exists child; split; [apply in_app_iff; right; exact Hin | exact Hch].
Qed.

(** Iterated preservation: every transfer in a reachable Tf
    came from the initial T0.  Direct induction on
    [rewrite_star] using [preservation_step] at each step. *)
Lemma preservation_star :
  forall from_ T0 Tf t,
    rewrite_star from_ T0 Tf ->
    In t (rcft_transfers Tf) ->
    In t (rcft_transfers T0).
Proof.
  intros from_ T0 Tf t Hstar. induction Hstar as [T | T1 T2 T3 Hstep _ IH].
  - intros; assumption.
  - intros HtT3. apply (preservation_step from_ T1 T2 Hstep). apply IH. exact HtT3.
Qed.

(** Leaves of a chain in a reduced CFT are transfers of that
    reduced CFT.  Structural induction on the membership
    proof. *)
Lemma chain_leaves_in_rcft :
  forall c T,
    chain_in_rcft c T ->
    forall t, In t (chain_transfers c) -> In t (rcft_transfers T).
Proof.
  intros c T Hin t Ht. induction Hin as [c0 | c0 addr children child Hch IH].
  - simpl. exact Ht.
  - simpl. apply in_flat_map. exists child; split; [exact Hch | apply IHIH; exact Ht].
Qed.

(** Helper lemmas about [last] of lists, used by
    [rcft_invariant_step] below. *)

Lemma last_indep_of_default :
  forall A (l : list A) (d1 d2 : A),
    l <> [] -> last l d1 = last l d2.
Proof.
  induction l as [|x [|y rest] IH]; intros d1 d2 Hne.
  - exfalso; apply Hne; reflexivity.
  - reflexivity.
  - simpl. apply IH. discriminate.
Qed.

Lemma last_cons_nonempty :
  forall A (x : A) (l : list A) (d : A),
    l <> [] -> last (x :: l) d = last l d.
Proof.
  intros A x [|y rest] d Hne.
  - exfalso; apply Hne; reflexivity.
  - reflexivity.
Qed.

Lemma last_app_nonempty :
  forall A (l1 l2 : list A) (d : A),
    l2 <> [] -> last (l1 ++ l2) d = last l2 d.
Proof.
  induction l1 as [|x xs IH]; intros l2 d Hne.
  - reflexivity.
  - simpl. destruct (xs ++ l2) eqn:E.
    + apply app_eq_nil in E. destruct E as [_ E2]. contradiction.
    + rewrite <- E. apply IH. exact Hne.
Qed.

Lemma last_app_singleton :
  forall A (l : list A) (x d : A),
    last (l ++ [x]) d = x.
Proof.
  induction l as [|y ys IH]; intros x d.
  - reflexivity.
  - simpl. destruct (ys ++ [x]) eqn:E.
    + apply app_eq_nil in E. destruct E as [_ E']. discriminate.
    + rewrite <- E. apply IH.
Qed.

Lemma chain_transfers_nonempty :
  forall c, chain_transfers c <> [].
Proof.
  induction c as [t | a1 a2 ms ti to t lbl l Ihl r Ihr].
  - simpl. discriminate.
  - simpl. intros Heq. apply app_eq_nil in Heq.
    destruct Heq as [E _]. contradiction.
Qed.

(** [endpoints_match] introduction lemma.  Given an explicit
    cons form for [chain_transfers c] together with origin
    and destination equations, derive [endpoints_match c]. *)
Lemma endpoints_match_cons :
  forall c first_t rest,
    chain_transfers c = first_t :: rest ->
    ch_origin c = tr_source first_t ->
    ch_destination c = tr_dest (last (first_t :: rest) first_t) ->
    endpoints_match c.
Proof.
  intros c first_t rest Hct Horig Hdest.
  unfold endpoints_match. rewrite Hct.
  split; assumption.
Qed.

(** Composition: every composite builder (append, seq, and all four
    merges) takes its input token from the left operand and its output
    token from the right, while its leaves are the concatenation, whose
    first transfer is the left operand's first and whose last is the
    right operand's last.  So [tokens_match] is inherited. *)
Lemma tokens_match_app :
  forall c c1 c2,
    chain_transfers c = chain_transfers c1 ++ chain_transfers c2 ->
    ch_token_in c = ch_token_in c1 ->
    ch_token_out c = ch_token_out c2 ->
    tokens_match c1 -> tokens_match c2 -> tokens_match c.
Proof.
  intros c c1 c2 Hct Hin Hout H1 H2.
  destruct (tokens_match_head c1 H1) as [t1 [r1 [E1 [Hi1 _]]]].
  destruct (tokens_match_head c2 H2) as [t2 [r2 [E2 [_ Ho2]]]].
  apply (tokens_match_cons c t1 (r1 ++ chain_transfers c2)).
  - rewrite Hct, E1. cbn [app]. reflexivity.
  - rewrite Hin. exact Hi1.
  - rewrite Hout, Ho2. apply f_equal.
    rewrite (last_cons_nonempty _ t1 (r1 ++ chain_transfers c2) t1)
      by (rewrite E2; intros He; apply app_eq_nil in He;
          destruct He as [_ He']; discriminate).
    rewrite (last_app_nonempty _ r1 (chain_transfers c2) t1)
      by (rewrite E2; discriminate).
    apply last_indep_of_default. rewrite E2. discriminate.
Qed.

(** The three concrete composite builders, as direct corollaries: each
    is an instance of [tokens_match_app] whose three field equations hold
    by definition. *)
Lemma tokens_match_prepend :
  forall t c, tokens_match c -> tokens_match (prepend_leaf_chain t c).
Proof.
  intros t c H.
  apply (tokens_match_app _ (CT_transfer t) c);
    [ reflexivity | reflexivity | reflexivity
    | apply tokens_match_leaf | exact H ].
Qed.

Lemma tokens_match_append :
  forall c t, tokens_match c -> tokens_match (append_leaf_chain c t).
Proof.
  intros c t H.
  apply (tokens_match_app _ c (CT_transfer t));
    [ reflexivity | reflexivity | reflexivity
    | exact H | apply tokens_match_leaf ].
Qed.

Lemma tokens_match_seq :
  forall c1 c2,
    tokens_match c1 -> tokens_match c2 -> tokens_match (seq_chain c1 c2).
Proof.
  intros c1 c2 H1 H2.
  apply (tokens_match_app _ c1 c2);
    [ reflexivity | reflexivity | reflexivity | exact H1 | exact H2 ].
Qed.

(** [rcft_invariant] is preserved under one rewriting
    step.  Sibling chains carry over unchanged.  Newly
    constructed chains satisfy [endpoints_match] from
    the rule's chain_transfers / origin / destination
    premises.  Closure under [Arbitrage] is vacuous for
    every rule except R13, which has the closure
    premise built in. *)
(* [inv_tokens_new]: the boundary-token component for a freshly built
   chain.  Annotation only relabels; leaf-pair builders seed both tokens
   from their two leaves; the composite builders inherit via
   [tokens_match_app], whose field equations are either definitional
   (prepend/append/seq) or rule premises (the four merges). *)
Ltac inv_tokens_new :=
  try match goal with Hb : ?c' = _ |- tokens_match ?c' => rewrite Hb end;
  first
    [ apply tokens_match_set_label; assumption
    | unfold tokens_match;
      cbn [chain_transfers ch_token_in ch_token_out app last
           leaf_pair_chain pool_cycle_chain];
      split; reflexivity
    | apply tokens_match_prepend; assumption
    | apply tokens_match_append; assumption
    | apply tokens_match_seq; assumption
    | eapply tokens_match_app;
      [ assumption | assumption | assumption | assumption | assumption ]
    | (* merge cases: the operands' leaf lists have already been
         destructed, so the rule's [chain_transfers] premise no longer
         matches syntactically; rebuild it from the cons equations. *)
      match goal with
      | Hch : ch_children ?cm = Some (?a, ?b) |- tokens_match ?cm =>
          apply (tokens_match_app cm a b);
          [ repeat match goal with
                   | H : chain_transfers _ = _ |- _ => rewrite H
                   end; reflexivity
          | assumption | assumption | assumption | assumption ]
      end ].

(* [inv_single_new]: a rule whose result is a single fresh chain [c0]
   with no siblings (R1-R5); the chain is unlabeled, so endpoints match
   reflexively and the closure premise is vacuous. *)
Ltac inv_single_new Hin c0 :=
  apply chain_in_RTree_iff in Hin;
  destruct Hin as [child [Hch Hin']];
  simpl in Hch; destruct Hch as [Heq | []]; subst child;
  apply chain_in_RChain_iff in Hin'; subst c0;
  split;
  [ cbn [endpoints_match_rec]; repeat split;
    try exact I; unfold endpoints_match; simpl; split; reflexivity
  | split;
    [ inv_tokens_new
    | split; [ simpl; intros Hlbl; discriminate
             | simpl; intros Hlbl; discriminate ] ] ].

(* [inv_sibling]: a chain that was already a sibling in the input tree
   ([Hsibs] places it in the untouched prefix); its invariant carries
   over from [Hinv]. *)
(* [inv_label_absurd Hlbl]: the new chain's label is fixed by the rule to
   something other than [Arbitrage], so the closure premise is vacuous.
   Finds the rule's label equation by matching on the chain, not by
   positional hypothesis name (premise order shifts when a rule gains a
   premise). *)
Ltac inv_label_absurd Hlbl :=
  match type of Hlbl with
  | ch_label ?x = Arbitrage =>
      match goal with
      | Hl : ch_label x = _ |- _ => rewrite Hl in Hlbl; discriminate
      end
  end.

Ltac inv_sibling Hinv Hsibs :=
  apply Hinv; apply chain_in_RTree_iff;
  destruct Hsibs as [child [Hinch Hch]]; exists child; split;
  [ apply in_app_iff; left; assumption | assumption ].

Lemma rcft_invariant_step :
  forall from_ T1 T2,
    rewrite_step from_ T1 T2 ->
    rcft_invariant T1 ->
    rcft_invariant T2.
Proof.
  intros from_ T1 T2 Hstep.
  induction Hstep; intros Hinv c0 Hin; subst.

  - (* R1: RS_swap_chain *)
    inv_single_new Hin c0.

  - (* R2: RS_burn_chain *)
    inv_single_new Hin c0.

  - (* R3: RS_mint_chain *)
    inv_single_new Hin c0.

  - (* R4: RS_pool_cycle *)
    inv_single_new Hin c0.

  - (* R5: RS_router_chain *)
    inv_single_new Hin c0.

  - (* R6: RS_leaf_chain *)
    apply chain_in_RTree_app in Hin.
    destruct Hin as [Hsibs | Hnew].
    + (* sibling chain: invariant carries over from input *)
      inv_sibling Hinv Hsibs.
    + (* output chain c' *)
      destruct Hnew as [child [Hinch Hch]]. simpl in Hinch.
      destruct Hinch as [Heq | []]. subst child.
      apply chain_in_RChain_iff in Hch. subst c0.
      assert (Hcinv : endpoints_match_rec c /\
                      tokens_match c /\
                      (ch_label c = Arbitrage -> ch_origin c = ch_destination c) /\
                      (ch_label c = Arbitrage ->
                       token_equiv (ch_token_in c) (ch_token_out c) = true)).
      { apply Hinv. apply chain_in_RTree_iff. exists (RChain c). split.
        - apply in_app_iff. right. simpl. right. left. reflexivity.
        - apply CIR_here. }
      destruct Hcinv as [Hepr [Htmc [_ _]]].
      pose proof (endpoints_match_rec_top c Hepr) as Hep.
      assert (Hcne : chain_transfers c <> []) by apply chain_transfers_nonempty.
      unfold endpoints_match in Hep.
      destruct (chain_transfers c) as [|tc rest_c] eqn:Hcteq;
        [exfalso; exact Hep|].
      destruct Hep as [Hco Hcd].
      destruct H0 as [[Hap1 [Hap2 [Hap3o [Hap3d Hbld]]]]
                     | [Hap1 [Hap2 [Hap3o [Hap3d [_ Hbld]]]]]].
      * (* Prepend: chain_transfers c' = t :: chain_transfers c *)
        split; [| split; [| split]].
        -- apply (emr_from_children c' (CT_transfer t) c).
           ++ rewrite Hbld. reflexivity.
           ++ apply (endpoints_match_cons _ t (tc :: rest_c)).
              ** exact Hap2.
              ** exact Hap3o.
              ** rewrite Hap3d, Hcd. apply f_equal. symmetry.
                 rewrite (last_cons_nonempty _ t (tc :: rest_c) t) by discriminate.
                 apply last_indep_of_default. discriminate.
           ++ apply endpoints_match_rec_leaf.
           ++ exact Hepr.
        -- inv_tokens_new.
        -- intros Hlbl. inv_label_absurd Hlbl.
        -- intros Hlbl. inv_label_absurd Hlbl.
      * (* Append: chain_transfers c' = chain_transfers c ++ [t] *)
        split; [| split; [| split]].
        -- apply (emr_from_children c' c (CT_transfer t)).
           ++ rewrite Hbld. reflexivity.
           ++ apply (endpoints_match_cons _ tc (rest_c ++ [t])).
              ** rewrite Hap2. reflexivity.
              ** rewrite Hap3o, Hco. reflexivity.
              ** rewrite Hap3d. apply f_equal. symmetry.
                 rewrite (last_cons_nonempty _ tc (rest_c ++ [t]) tc)
                   by (intros He; apply app_eq_nil in He;
                       destruct He as [_ He']; discriminate).
                 apply last_app_singleton.
           ++ exact Hepr.
           ++ apply endpoints_match_rec_leaf.
        -- inv_tokens_new.
        -- intros Hlbl. inv_label_absurd Hlbl.
        -- intros Hlbl. inv_label_absurd Hlbl.

  - (* R12: RS_node_leaf_chain *)
    apply chain_in_RTree_app in Hin.
    destruct Hin as [Hsibs | Hnew].
    + inv_sibling Hinv Hsibs.
    + destruct Hnew as [child [Hinch Hch]]. simpl in Hinch.
      destruct Hinch as [Heq | []]. subst child.
      apply chain_in_RChain_iff in Hch. subst c0.
      assert (Hcinv : endpoints_match_rec c /\
                      tokens_match c /\
                      (ch_label c = Arbitrage -> ch_origin c = ch_destination c) /\
                      (ch_label c = Arbitrage ->
                       token_equiv (ch_token_in c) (ch_token_out c) = true)).
      { apply Hinv. apply chain_in_RTree_iff. exists (RChain c). split.
        - apply in_app_iff. right. simpl. right. left. reflexivity.
        - apply CIR_here. }
      destruct Hcinv as [Hepr [Htmc [_ _]]].
      pose proof (endpoints_match_rec_top c Hepr) as Hep.
      assert (Hcne : chain_transfers c <> []) by apply chain_transfers_nonempty.
      unfold endpoints_match in Hep.
      destruct (chain_transfers c) as [|tc rest_c] eqn:Hcteq;
        [exfalso; exact Hep|].
      destruct Hep as [Hco Hcd].
      destruct H0
        as [[Hadj [Htok [Hap2 [Hap3o [Hap3d Hbld]]]]]
           | [Hadj [Htok [Hap2 [Hap3o [Hap3d [_ Hbld]]]]]]].
      * (* Prepend: chain_transfers c' = t :: chain_transfers c *)
        split; [| split; [| split]].
        -- apply (emr_from_children c' (CT_transfer t) c).
           ++ rewrite Hbld. reflexivity.
           ++ apply (endpoints_match_cons _ t (tc :: rest_c)).
              ** exact Hap2.
              ** exact Hap3o.
              ** rewrite Hap3d, Hcd. apply f_equal. symmetry.
                 rewrite (last_cons_nonempty _ t (tc :: rest_c) t) by discriminate.
                 apply last_indep_of_default. discriminate.
           ++ apply endpoints_match_rec_leaf.
           ++ exact Hepr.
        -- inv_tokens_new.
        -- intros Hlbl. inv_label_absurd Hlbl.
        -- intros Hlbl. inv_label_absurd Hlbl.
      * (* Append: chain_transfers c' = chain_transfers c ++ [t] *)
        split; [| split; [| split]].
        -- apply (emr_from_children c' c (CT_transfer t)).
           ++ rewrite Hbld. reflexivity.
           ++ apply (endpoints_match_cons _ tc (rest_c ++ [t])).
              ** rewrite Hap2. reflexivity.
              ** rewrite Hap3o, Hco. reflexivity.
              ** rewrite Hap3d. apply f_equal. symmetry.
                 rewrite (last_cons_nonempty _ tc (rest_c ++ [t]) tc)
                   by (intros He; apply app_eq_nil in He;
                       destruct He as [_ He']; discriminate).
                 apply last_app_singleton.
           ++ exact Hepr.
           ++ apply endpoints_match_rec_leaf.
        -- inv_tokens_new.
        -- intros Hlbl. inv_label_absurd Hlbl.
        -- intros Hlbl. inv_label_absurd Hlbl.

  - (* R10: RS_chain_seq *)
    apply chain_in_RTree_app in Hin.
    destruct Hin as [Hsibs | Hnew].
    + inv_sibling Hinv Hsibs.
    + destruct Hnew as [child [Hinch Hch]]. simpl in Hinch.
      destruct Hinch as [Heq | []]. subst child.
      apply chain_in_RChain_iff in Hch. subst c0.
      assert (Hc1inv : endpoints_match_rec c1 /\
                       tokens_match c1 /\
                       (ch_label c1 = Arbitrage -> ch_origin c1 = ch_destination c1) /\
                       (ch_label c1 = Arbitrage ->
                        token_equiv (ch_token_in c1) (ch_token_out c1) = true)).
      { apply Hinv. apply chain_in_RTree_iff. exists (RChain c1). split.
        - apply in_app_iff. right. simpl. left. reflexivity.
        - apply CIR_here. }
      assert (Hc2inv : endpoints_match_rec c2 /\
                       tokens_match c2 /\
                       (ch_label c2 = Arbitrage -> ch_origin c2 = ch_destination c2) /\
                       (ch_label c2 = Arbitrage ->
                        token_equiv (ch_token_in c2) (ch_token_out c2) = true)).
      { apply Hinv. apply chain_in_RTree_iff. exists (RChain c2). split.
        - apply in_app_iff. right. simpl. right. left. reflexivity.
        - apply CIR_here. }
      destruct Hc1inv as [Hep1r [Htm1 [_ _]]], Hc2inv as [Hep2r [Htm2 [_ _]]].
      pose proof (endpoints_match_rec_top c1 Hep1r) as Hep1.
      pose proof (endpoints_match_rec_top c2 Hep2r) as Hep2.
      unfold endpoints_match in Hep1, Hep2.
      destruct (chain_transfers c1) as [|t1c rest_c1] eqn:Hct1;
        [exfalso; exact Hep1|].
      destruct (chain_transfers c2) as [|t2c rest_c2] eqn:Hct2;
        [exfalso; exact Hep2|].
      destruct Hep1 as [Hco1 _], Hep2 as [_ Hcd2].
      split; [| split; [| split]].
      * apply emr_from_children with (c1 := c1) (c2 := c2).
        -- reflexivity.
        -- apply (endpoints_match_cons _ t1c (rest_c1 ++ t2c :: rest_c2)).
           ++ match goal with
              | Ht : chain_transfers (seq_chain c1 c2) = _ |- _ => rewrite Ht
              end. reflexivity.
           ++ match goal with
              | Ho : ch_origin (seq_chain c1 c2) = _ |- _ => rewrite Ho
              end. rewrite Hco1. reflexivity.
           ++ match goal with
              | Hd : ch_destination (seq_chain c1 c2) = _ |- _ => rewrite Hd
              end. rewrite Hcd2. apply f_equal. symmetry.
              rewrite (last_cons_nonempty _ t1c (rest_c1 ++ t2c :: rest_c2) t1c)
                by (intros He; apply app_eq_nil in He;
                    destruct He as [_ He']; discriminate).
              rewrite (last_app_nonempty _ rest_c1 (t2c :: rest_c2) t1c)
                by discriminate.
              apply last_indep_of_default. discriminate.
        -- exact Hep1r.
        -- exact Hep2r.
      * inv_tokens_new.
      * intros Hlbl. inv_label_absurd Hlbl.
      * intros Hlbl. inv_label_absurd Hlbl.

  - (* R11: RS_same_token_chain *)
    inv_single_new Hin c0.

  - (* RS_lift *)
    apply chain_in_RTree_app in Hin.
    destruct Hin as [Hsibs | Hchildren].
    + inv_sibling Hinv Hsibs.
    + apply Hinv. apply chain_in_RTree_iff.
      destruct Hchildren as [child [Hinch Hch]].
      exists (RTree addr children). split.
      * apply in_app_iff. right. simpl. left. reflexivity.
      * eapply CIR_tree; [exact Hinch | exact Hch].

  - (* R7: RS_merge_endpoints *)
    apply chain_in_RTree_app in Hin.
    destruct Hin as [Hsibs | Hnew].
    + inv_sibling Hinv Hsibs.
    + destruct Hnew as [child [Hinch Hch]].
      apply in_app_iff in Hinch.
      destruct Hinch as [HinM | Hinch].
      { apply Hinv. apply chain_in_RTree_iff. exists child. split.
        - apply in_app_iff. right. apply in_app_iff. right.
          apply in_app_iff. left. exact HinM.
        - exact Hch. }
      simpl in Hinch.
      destruct Hinch as [Heq | HinR]; cycle 1.
      { apply Hinv. apply chain_in_RTree_iff. exists child. split.
        - apply in_app_iff. right. apply in_app_iff. right.
          apply in_app_iff. right. apply in_app_iff. right. exact HinR.
        - exact Hch. }
      subst child.
      apply chain_in_RChain_iff in Hch. subst c0.
      assert (Hc1inv : endpoints_match_rec c1 /\
                       tokens_match c1 /\
                       (ch_label c1 = Arbitrage -> ch_origin c1 = ch_destination c1) /\
                       (ch_label c1 = Arbitrage ->
                        token_equiv (ch_token_in c1) (ch_token_out c1) = true)).
      { apply Hinv. apply chain_in_RTree_iff. exists (RChain c1). split.
        - apply in_app_iff. right. apply in_app_iff. left.
          simpl. left. reflexivity.
        - apply CIR_here. }
      assert (Hc2inv : endpoints_match_rec c2 /\
                       tokens_match c2 /\
                       (ch_label c2 = Arbitrage -> ch_origin c2 = ch_destination c2) /\
                       (ch_label c2 = Arbitrage ->
                        token_equiv (ch_token_in c2) (ch_token_out c2) = true)).
      { apply Hinv. apply chain_in_RTree_iff. exists (RChain c2). split.
        - apply in_app_iff. right. apply in_app_iff. right.
          apply in_app_iff. right. apply in_app_iff. left.
          simpl. left. reflexivity.
        - apply CIR_here. }
      destruct Hc1inv as [Hep1r [Htm1 [_ _]]], Hc2inv as [Hep2r [Htm2 [_ _]]].
      pose proof (endpoints_match_rec_top c1 Hep1r) as Hep1.
      pose proof (endpoints_match_rec_top c2 Hep2r) as Hep2.
      unfold endpoints_match in Hep1, Hep2.
      destruct (chain_transfers c1) as [|t1c rest_c1] eqn:Hct1;
        [exfalso; exact Hep1|].
      destruct (chain_transfers c2) as [|t2c rest_c2] eqn:Hct2;
        [exfalso; exact Hep2|].
      destruct Hep1 as [Hco1 _], Hep2 as [_ Hcd2].
      split; [| split; [| split]].
      * apply (emr_from_children cm c1 c2).
        -- match goal with Hch : ch_children cm = Some (c1, c2) |- _ =>
             exact Hch end.
        -- apply (endpoints_match_cons _ t1c (rest_c1 ++ t2c :: rest_c2)).
           ++ match goal with Hcm : chain_transfers cm = _ |- _ =>
                rewrite Hcm end.
              reflexivity.
           ++ match goal with Hom : ch_origin cm = ch_origin c1 |- _ =>
                rewrite Hom end.
              rewrite Hco1. reflexivity.
           ++ match goal with
                Hdm : ch_destination cm = ch_destination c1 |- _ =>
                rewrite Hdm end.
              rewrite H0, Hcd2. apply f_equal. symmetry.
              rewrite (last_cons_nonempty _ t1c (rest_c1 ++ t2c :: rest_c2) t1c)
                by (intros He; apply app_eq_nil in He;
                    destruct He as [_ He']; discriminate).
              rewrite (last_app_nonempty _ rest_c1 (t2c :: rest_c2) t1c)
                by discriminate.
              apply last_indep_of_default. discriminate.
        -- exact Hep1r.
        -- exact Hep2r.
      * inv_tokens_new.
      * intros Hlbl. inv_label_absurd Hlbl.
      * intros Hlbl. inv_label_absurd Hlbl.

  - (* R8: RS_merge_add *)
    apply chain_in_RTree_app in Hin.
    destruct Hin as [Hsibs | Hnew].
    + inv_sibling Hinv Hsibs.
    + destruct Hnew as [child [Hinch Hch]].
      apply in_app_iff in Hinch.
      destruct Hinch as [HinM | Hinch].
      { apply Hinv. apply chain_in_RTree_iff. exists child. split.
        - apply in_app_iff. right. apply in_app_iff. right.
          apply in_app_iff. left. exact HinM.
        - exact Hch. }
      simpl in Hinch.
      destruct Hinch as [Heq | HinR]; cycle 1.
      { apply Hinv. apply chain_in_RTree_iff. exists child. split.
        - apply in_app_iff. right. apply in_app_iff. right.
          apply in_app_iff. right. apply in_app_iff. right. exact HinR.
        - exact Hch. }
      subst child.
      apply chain_in_RChain_iff in Hch. subst c0.
      assert (Hc1inv : endpoints_match_rec c1 /\
                       tokens_match c1 /\
                       (ch_label c1 = Arbitrage -> ch_origin c1 = ch_destination c1) /\
                       (ch_label c1 = Arbitrage ->
                        token_equiv (ch_token_in c1) (ch_token_out c1) = true)).
      { apply Hinv. apply chain_in_RTree_iff. exists (RChain c1). split.
        - apply in_app_iff. right. apply in_app_iff. left.
          simpl. left. reflexivity.
        - apply CIR_here. }
      assert (Hc2inv : endpoints_match_rec c2 /\
                       tokens_match c2 /\
                       (ch_label c2 = Arbitrage -> ch_origin c2 = ch_destination c2) /\
                       (ch_label c2 = Arbitrage ->
                        token_equiv (ch_token_in c2) (ch_token_out c2) = true)).
      { apply Hinv. apply chain_in_RTree_iff. exists (RChain c2). split.
        - apply in_app_iff. right. apply in_app_iff. right.
          apply in_app_iff. right. apply in_app_iff. left.
          simpl. left. reflexivity.
        - apply CIR_here. }
      destruct Hc1inv as [Hep1r [Htm1 [_ _]]], Hc2inv as [Hep2r [Htm2 [_ _]]].
      pose proof (endpoints_match_rec_top c1 Hep1r) as Hep1.
      pose proof (endpoints_match_rec_top c2 Hep2r) as Hep2.
      unfold endpoints_match in Hep1, Hep2.
      destruct (chain_transfers c1) as [|t1c rest_c1] eqn:Hct1;
        [exfalso; exact Hep1|].
      destruct (chain_transfers c2) as [|t2c rest_c2] eqn:Hct2;
        [exfalso; exact Hep2|].
      destruct Hep1 as [Hco1 _], Hep2 as [_ Hcd2].
      split; [| split; [| split]].
      * apply (emr_from_children cm c1 c2).
        -- match goal with Hch : ch_children cm = Some (c1, c2) |- _ =>
             exact Hch end.
        -- apply (endpoints_match_cons _ t1c (rest_c1 ++ t2c :: rest_c2)).
           ++ match goal with Hcm : chain_transfers cm = _ |- _ =>
                rewrite Hcm end.
              reflexivity.
           ++ match goal with Hcm : ch_origin cm = _ |- _ => rewrite Hcm end.
              rewrite Hco1. reflexivity.
           ++ match goal with Hcm : ch_destination cm = _ |- _ => rewrite Hcm end.
              match goal with
              | Hd : ch_destination c1 = ch_destination c2 |- _ => rewrite Hd
              end.
              rewrite Hcd2. apply f_equal. symmetry.
              rewrite (last_cons_nonempty _ t1c (rest_c1 ++ t2c :: rest_c2) t1c)
                by (intros He; apply app_eq_nil in He;
                    destruct He as [_ He']; discriminate).
              rewrite (last_app_nonempty _ rest_c1 (t2c :: rest_c2) t1c)
                by discriminate.
              apply last_indep_of_default. discriminate.
        -- exact Hep1r.
        -- exact Hep2r.
      * inv_tokens_new.
      * intros Hlbl. inv_label_absurd Hlbl.
      * intros Hlbl. inv_label_absurd Hlbl.

  - (* RS_merge_closed_R9 *)
    apply chain_in_RTree_app in Hin.
    destruct Hin as [Hsibs | Hnew].
    + inv_sibling Hinv Hsibs.
    + destruct Hnew as [child [Hinch Hch]].
      apply in_app_iff in Hinch.
      destruct Hinch as [HinM | Hinch].
      { apply Hinv. apply chain_in_RTree_iff. exists child. split.
        - apply in_app_iff. right. apply in_app_iff. right.
          apply in_app_iff. left. exact HinM.
        - exact Hch. }
      simpl in Hinch.
      destruct Hinch as [Heq | HinR]; cycle 1.
      { apply Hinv. apply chain_in_RTree_iff. exists child. split.
        - apply in_app_iff. right. apply in_app_iff. right.
          apply in_app_iff. right. apply in_app_iff. right. exact HinR.
        - exact Hch. }
      subst child.
      apply chain_in_RChain_iff in Hch. subst c0.
      assert (Hc1inv : endpoints_match_rec c1 /\
                       tokens_match c1 /\
                       (ch_label c1 = Arbitrage -> ch_origin c1 = ch_destination c1) /\
                       (ch_label c1 = Arbitrage ->
                        token_equiv (ch_token_in c1) (ch_token_out c1) = true)).
      { apply Hinv. apply chain_in_RTree_iff. exists (RChain c1). split.
        - apply in_app_iff. right. apply in_app_iff. left.
          simpl. left. reflexivity.
        - apply CIR_here. }
      assert (Hc2inv : endpoints_match_rec c2 /\
                       tokens_match c2 /\
                       (ch_label c2 = Arbitrage -> ch_origin c2 = ch_destination c2) /\
                       (ch_label c2 = Arbitrage ->
                        token_equiv (ch_token_in c2) (ch_token_out c2) = true)).
      { apply Hinv. apply chain_in_RTree_iff. exists (RChain c2). split.
        - apply in_app_iff. right. apply in_app_iff. right.
          apply in_app_iff. right. apply in_app_iff. left.
          simpl. left. reflexivity.
        - apply CIR_here. }
      destruct Hc1inv as [Hep1r [Htm1 [_ _]]], Hc2inv as [Hep2r [Htm2 [_ _]]].
      pose proof (endpoints_match_rec_top c1 Hep1r) as Hep1.
      pose proof (endpoints_match_rec_top c2 Hep2r) as Hep2.
      unfold endpoints_match in Hep1, Hep2.
      destruct (chain_transfers c1) as [|t1c rest_c1] eqn:Hct1;
        [exfalso; exact Hep1|].
      destruct (chain_transfers c2) as [|t2c rest_c2] eqn:Hct2;
        [exfalso; exact Hep2|].
      destruct Hep1 as [Hco1 _], Hep2 as [_ Hcd2].
      assert (Hd12 : ch_destination c1 = ch_destination c2)
        by (transitivity (ch_origin c1);
             [ match goal with Hc : ch_origin c1 = ch_destination c1 |- _ =>
                 symmetry; exact Hc end
             | transitivity (ch_origin c2);
               [ match goal with Hc : ch_origin c1 = ch_origin c2 |- _ =>
                   exact Hc end
               | match goal with Hc : ch_origin c2 = ch_destination c2 |- _ =>
                   exact Hc end ] ]).
      split; [| split; [| split]].
      * apply (emr_from_children cm c1 c2).
        -- match goal with Hch : ch_children cm = Some (c1, c2) |- _ =>
             exact Hch end.
        -- apply (endpoints_match_cons _ t1c (rest_c1 ++ t2c :: rest_c2)).
           ++ match goal with Hcm : chain_transfers cm = _ |- _ =>
                rewrite Hcm end.
              reflexivity.
           ++ match goal with Hcm : ch_origin cm = _ |- _ => rewrite Hcm end.
              rewrite Hco1. reflexivity.
           ++ match goal with Hcm : ch_destination cm = _ |- _ => rewrite Hcm end.
              rewrite Hd12, Hcd2. apply f_equal. symmetry.
              rewrite (last_cons_nonempty _ t1c (rest_c1 ++ t2c :: rest_c2) t1c)
                by (intros He; apply app_eq_nil in He;
                    destruct He as [_ He']; discriminate).
              rewrite (last_app_nonempty _ rest_c1 (t2c :: rest_c2) t1c)
                by discriminate.
              apply last_indep_of_default. discriminate.
        -- exact Hep1r.
        -- exact Hep2r.
      * inv_tokens_new.
      * intros Hlbl. inv_label_absurd Hlbl.
      * intros Hlbl. inv_label_absurd Hlbl.

  - (* R13: RS_merge_node *)
    apply chain_in_RTree_app in Hin.
    destruct Hin as [Hsibs | Hnew].
    + inv_sibling Hinv Hsibs.
    + destruct Hnew as [child [Hinch Hch]].
      apply in_app_iff in Hinch.
      destruct Hinch as [HinM | Hinch].
      { apply Hinv. apply chain_in_RTree_iff. exists child. split.
        - apply in_app_iff. right. apply in_app_iff. right.
          apply in_app_iff. left. exact HinM.
        - exact Hch. }
      simpl in Hinch.
      destruct Hinch as [Heq | HinR]; cycle 1.
      { apply Hinv. apply chain_in_RTree_iff. exists child. split.
        - apply in_app_iff. right. apply in_app_iff. right.
          apply in_app_iff. right. apply in_app_iff. right. exact HinR.
        - exact Hch. }
      subst child.
      apply chain_in_RChain_iff in Hch. subst c0.
      assert (Hc1inv : endpoints_match_rec c1 /\
                       tokens_match c1 /\
                       (ch_label c1 = Arbitrage -> ch_origin c1 = ch_destination c1) /\
                       (ch_label c1 = Arbitrage ->
                        token_equiv (ch_token_in c1) (ch_token_out c1) = true)).
      { apply Hinv. apply chain_in_RTree_iff. exists (RChain c1). split.
        - apply in_app_iff. right. apply in_app_iff. left.
          simpl. left. reflexivity.
        - apply CIR_here. }
      assert (Hc2inv : endpoints_match_rec c2 /\
                       tokens_match c2 /\
                       (ch_label c2 = Arbitrage -> ch_origin c2 = ch_destination c2) /\
                       (ch_label c2 = Arbitrage ->
                        token_equiv (ch_token_in c2) (ch_token_out c2) = true)).
      { apply Hinv. apply chain_in_RTree_iff. exists (RChain c2). split.
        - apply in_app_iff. right. apply in_app_iff. right.
          apply in_app_iff. right. apply in_app_iff. left.
          simpl. left. reflexivity.
        - apply CIR_here. }
      destruct Hc1inv as [Hep1r [Htm1 [_ _]]], Hc2inv as [Hep2r [Htm2 [_ _]]].
      pose proof (endpoints_match_rec_top c1 Hep1r) as Hep1.
      pose proof (endpoints_match_rec_top c2 Hep2r) as Hep2.
      unfold endpoints_match in Hep1, Hep2.
      destruct (chain_transfers c1) as [|t1c rest_c1] eqn:Hct1;
        [exfalso; exact Hep1|].
      destruct (chain_transfers c2) as [|t2c rest_c2] eqn:Hct2;
        [exfalso; exact Hep2|].
      destruct Hep1 as [Hco1 _], Hep2 as [_ Hcd2].
      split; [| split; [| split]].
      * apply (emr_from_children cm c1 c2).
        -- match goal with Hch : ch_children cm = Some (c1, c2) |- _ =>
             exact Hch end.
        -- apply (endpoints_match_cons _ t1c (rest_c1 ++ t2c :: rest_c2)).
           ++ match goal with Hcm : chain_transfers cm = _ |- _ =>
                rewrite Hcm end.
              reflexivity.
           ++ match goal with Hcm : ch_origin cm = _ |- _ => rewrite Hcm end.
              rewrite Hco1. reflexivity.
           ++ match goal with Hcm : ch_destination cm = _ |- _ => rewrite Hcm end.
              match goal with Hdd : ch_destination c1 = ch_destination c2 |- _ =>
                rewrite Hdd end.
              rewrite Hcd2. apply f_equal. symmetry.
              rewrite (last_cons_nonempty _ t1c (rest_c1 ++ t2c :: rest_c2) t1c)
                by (intros He; apply app_eq_nil in He;
                    destruct He as [_ He']; discriminate).
              rewrite (last_app_nonempty _ rest_c1 (t2c :: rest_c2) t1c)
                by discriminate.
              apply last_indep_of_default. discriminate.
        -- exact Hep1r.
        -- exact Hep2r.
      * inv_tokens_new.
      * intros Hlbl. inv_label_absurd Hlbl.
      * intros Hlbl. inv_label_absurd Hlbl.

  - (* R14: RS_annotate_arb *)
    apply chain_in_RTree_app in Hin.
    destruct Hin as [Hsibs | Hnew].
    + inv_sibling Hinv Hsibs.
    + destruct Hnew as [child [Hinch Hch]]. simpl in Hinch.
      destruct Hinch as [Heq | Hin_R].
      * subst child.
        apply chain_in_RChain_iff in Hch. subst c0.
        assert (Hcinv : endpoints_match_rec c /\
                        tokens_match c /\
                        (ch_label c = Arbitrage -> ch_origin c = ch_destination c) /\
                        (ch_label c = Arbitrage ->
                         token_equiv (ch_token_in c) (ch_token_out c) = true)).
        { apply Hinv. apply chain_in_RTree_iff. exists (RChain c). split.
          - apply in_app_iff. right. simpl. left. reflexivity.
          - apply CIR_here. }
        destruct Hcinv as [Hepr [Htmc [_ _]]].
        split; [| split; [| split]].
        -- apply emr_set_label. exact Hepr.
        -- inv_tokens_new.
        -- intros _. rewrite H1, H2. exact H.
        -- intros _. rewrite H3, H4. exact H0.
      * apply Hinv. apply chain_in_RTree_iff. exists child. split.
        -- apply in_app_iff. right. simpl. right. exact Hin_R.
        -- exact Hch.

  - (* R15: RS_annotate_cyc *)
    apply chain_in_RTree_app in Hin.
    destruct Hin as [Hsibs | Hnew].
    + inv_sibling Hinv Hsibs.
    + destruct Hnew as [child [Hinch Hch]]. simpl in Hinch.
      destruct Hinch as [Heq | Hin_R]; cycle 1.
      { apply Hinv. apply chain_in_RTree_iff. exists child. split.
        - apply in_app_iff. right. simpl. right. exact Hin_R.
        - exact Hch. }
      subst child.
      apply chain_in_RChain_iff in Hch. subst c0.
      assert (Hcinv : endpoints_match_rec c /\
                      tokens_match c /\
                      (ch_label c = Arbitrage -> ch_origin c = ch_destination c) /\
                      (ch_label c = Arbitrage ->
                       token_equiv (ch_token_in c) (ch_token_out c) = true)).
      { apply Hinv. apply chain_in_RTree_iff. exists (RChain c). split.
        - apply in_app_iff. right. simpl. left. reflexivity.
        - apply CIR_here. }
      destruct Hcinv as [Hepr [Htmc [_ _]]].
      split; [| split; [| split]].
      * apply emr_set_label. exact Hepr.
      * inv_tokens_new.
      * intros Hlbl. inv_label_absurd Hlbl.
      * intros Hlbl. inv_label_absurd Hlbl.

  - (* RS_under (congruence) *)
    apply chain_in_RTree_iff in Hin.
    destruct Hin as [child [Hinch Hchild]].
    apply in_app_iff in Hinch.
    destruct Hinch as [HL | Hmid].
    + apply Hinv. apply chain_in_RTree_iff. exists child. split.
      * apply in_app_iff. left. exact HL.
      * exact Hchild.
    + simpl in Hmid. destruct Hmid as [Heq | HR].
      * subst child.
        assert (HinvT : rcft_invariant T).
        { intros c1 Hin1. apply Hinv. apply chain_in_RTree_iff.
          exists T. split.
          - apply in_app_iff. right. simpl. left. reflexivity.
          - exact Hin1. }
        exact (IHHstep HinvT c0 Hchild).
      * apply Hinv. apply chain_in_RTree_iff. exists child. split.
        -- apply in_app_iff. right. simpl. right. exact HR.
        -- exact Hchild.
Qed.

(** Iterated preservation of [rcft_invariant] under
    [rewrite_star]. *)
Lemma rcft_invariant_preserved :
  forall from_ T0 Tf,
    rewrite_star from_ T0 Tf ->
    rcft_invariant T0 ->
    rcft_invariant Tf.
Proof.
  intros from_ T0 Tf Hstar.
  induction Hstar as [T | T1 T2 T3 Hstep _ IH].
  - intros; assumption.
  - intros HinvT1. apply IH.
    apply (rcft_invariant_step from_ T1 T2 Hstep HinvT1).
Qed.

Lemma refinement_of_transfer_graph_cycles :
  forall from_ T0 Tf c,
    walks_in_rcft T0 ->
    no_chains T0 ->
    rewrite_star from_ T0 Tf ->
    chain_in_rcft c Tf ->
    ch_label c = Arbitrage ->
    Forall (fun t => In t (rcft_transfers T0)) (chain_transfers c) /\
    ch_origin c = ch_destination c /\
    endpoints_match_rec c /\
    tokens_match c /\
    token_equiv (ch_token_in c) (ch_token_out c) = true.
Proof.
  intros from_ T0 Tf c Hwalks Hnc Hstar Hin Harb.
  assert (Hinv : rcft_invariant Tf).
  { apply (rcft_invariant_preserved from_ T0 Tf Hstar).
    apply no_chains_implies_invariant. exact Hnc. }
  destruct (Hinv c Hin) as [Hep [Htm [Hcl Hteq]]].
  split; [| split; [| split; [| split]]].
  - apply Forall_forall. intros t Ht.
    apply (preservation_star from_ T0 Tf t Hstar).
    apply (chain_leaves_in_rcft c Tf Hin t Ht).
  - exact (Hcl Harb).
  - exact Hep.
  - exact Htm.
  - exact (Hteq Harb).
Qed.

(* ============================================================
   Section 23: Structural soundness of classify (Definition 5)

   Any chain in a reachable reduced CFT that
   carries the [Arbitrage] label and survives
   Validate-Deltas ([validated_arbitrage])
   satisfies the structural conditions of
   Definition 5: closure, endpoint
   correspondence, walk decomposition over T0's
   transfer graph, inclusion in T0's edge set,
   and positive gross delta at the cycle origin.
   ============================================================ *)

(** Inductive [chain_in_rcft] membership coincides
    with the flat [rcft_chains] list. *)
Lemma chain_in_rcft_in_rcft_chains :
  forall T c, chain_in_rcft c T -> In c (rcft_chains T).
Proof.
  intros T c Hin.
  induction Hin as [c0 | c0 addr children child Hch IH].
  - simpl. left. reflexivity.
  - simpl. apply in_flat_map. exists child; split; assumption.
Qed.

(** [walks_in_rcft] transports to per-chain
    [chain_walks]. *)
Lemma walks_in_rcft_chain_walks :
  forall T c,
    walks_in_rcft T ->
    chain_in_rcft c T ->
    chain_walks c.
Proof.
  intros T c Hwalks Hin.
  apply chain_in_rcft_in_rcft_chains in Hin.
  unfold walks_in_rcft in Hwalks.
  rewrite Forall_forall in Hwalks.
  apply Hwalks. exact Hin.
Qed.

(* ============================================================
   Structural walk-count characterization of a chain.

   [seg_count c] counts the [CT_node]s of [c] whose junction is a
   PARALLEL merge -- the two children do not chain
   ([ch_destination l <> ch_origin r]).  It reads the children's
   stored endpoints, so it is robust to annotate overwriting the
   top label.  Under the recursive endpoint invariant
   [endpoints_match_rec], the number of maximal connected walks of
   a chain is exactly [1 + seg_count]: a merge-free chain is a
   single connected walk, and each parallel merge adds one walk.
   ============================================================ *)

Fixpoint seg_count (c : chain_tree) : nat :=
  match c with
  | CT_transfer _ => 0
  | CT_node _ _ _ _ _ _ _ l r =>
      seg_count l + seg_count r +
      (if address_eq_dec (ch_destination l) (ch_origin r) then 0 else 1)
  end.

Lemma last_indep :
  forall (l : list transfer) d1 d2, l <> [] -> last l d1 = last l d2.
Proof.
  induction l as [| x xs IH]; [contradiction|].
  intros d1 d2 _. destruct xs as [| y ys]; [reflexivity|].
  apply IH. discriminate.
Qed.

Lemma count_breaks_app :
  forall xs ys d1 d2, xs <> [] -> ys <> [] ->
    count_breaks (xs ++ ys) =
      count_breaks xs + count_breaks ys +
      (if address_eq_dec (tr_dest (last xs d1)) (tr_source (hd d2 ys))
       then 0 else 1).
Proof.
  induction xs as [| x xs IH]; [contradiction|].
  intros ys d1 d2 _ Hys.
  destruct xs as [| x2 xs'].
  - destruct ys as [| y ys']; [contradiction|].
    cbn [app]. rewrite (count_breaks_cons2 x y ys').
    replace (count_breaks [x]) with 0 by reflexivity.
    cbn [last hd]. lia.
  - cbn [app].
    rewrite (count_breaks_cons2 x x2 (xs' ++ ys)).
    change (count_breaks (x2 :: (xs' ++ ys)))
      with (count_breaks ((x2 :: xs') ++ ys)).
    rewrite (IH ys d1 d2 ltac:(discriminate) Hys).
    rewrite (count_breaks_cons2 x x2 xs').
    cbn [last]. lia.
Qed.

Lemma endpoints_match_src :
  forall c d, endpoints_match c ->
    tr_source (hd d (chain_transfers c)) = ch_origin c.
Proof.
  intros c d Hem. unfold endpoints_match in Hem.
  destruct (chain_transfers c) as [| t rest] eqn:E; [contradiction|].
  destruct Hem as [Ho _]. simpl. symmetry. exact Ho.
Qed.

Lemma endpoints_match_dest :
  forall c d, endpoints_match c ->
    tr_dest (last (chain_transfers c) d) = ch_destination c.
Proof.
  intros c d Hem. unfold endpoints_match in Hem.
  destruct (chain_transfers c) as [| t rest] eqn:E; [contradiction|].
  destruct Hem as [_ Hd].
  rewrite (last_indep (t :: rest) d t) by discriminate.
  symmetry. exact Hd.
Qed.

(** Token boundary bridges: read the first and last leaf's token off the
    chain's stored fields.  The token analogue of [endpoints_match_src]
    and [endpoints_match_dest]. *)
Lemma tokens_match_src :
  forall c d, tokens_match c ->
    tr_token (hd d (chain_transfers c)) = ch_token_in c.
Proof.
  intros c d Htm. unfold tokens_match in Htm.
  destruct (chain_transfers c) as [| t rest] eqn:E; [contradiction|].
  destruct Htm as [Hi _]. simpl. symmetry. exact Hi.
Qed.

Lemma tokens_match_dest :
  forall c d, tokens_match c ->
    tr_token (last (chain_transfers c) d) = ch_token_out c.
Proof.
  intros c d Htm. unfold tokens_match in Htm.
  destruct (chain_transfers c) as [| t rest] eqn:E; [contradiction|].
  destruct Htm as [_ Ho].
  rewrite (last_indep (t :: rest) d t) by discriminate.
  symmetry. exact Ho.
Qed.

(** BRIDGE: the leaf-level break count equals the structural
    parallel-merge count, under the recursive endpoint invariant. *)
Lemma count_breaks_chain_transfers :
  forall c, endpoints_match_rec c ->
    count_breaks (chain_transfers c) = seg_count c.
Proof.
  induction c as [t | o d m ti to_ ft lbl l IHl r IHr]; intros Hrec.
  - reflexivity.
  - simpl in Hrec. destruct Hrec as [_ [Hrl Hrr]].
    cbn [chain_transfers seg_count].
    rewrite (count_breaks_app (chain_transfers l) (chain_transfers r) ft ft
               (chain_transfers_nonempty l) (chain_transfers_nonempty r)).
    rewrite (IHl Hrl), (IHr Hrr).
    rewrite (endpoints_match_dest l ft (endpoints_match_rec_top l Hrl)).
    rewrite (endpoints_match_src r ft (endpoints_match_rec_top r Hrr)).
    reflexivity.
Qed.

(** The connectivity characterization (the non-vacuous replacement for
    the free existential [chain_walks]): a chain whose every node has
    matching endpoints decomposes into a fixed number of maximal
    CONNECTED walks, and that number is exactly one plus the count of
    parallel-merge nodes.  In particular a merge-free chain
    ([seg_count c = 0]) is a single connected walk.  This pins the
    fragmentation of the cycle to its explicit parallelism, rather than
    leaving the walk-set free (which any transfer list satisfies via
    per-transfer singletons). *)
Lemma walk_decomposition_count :
  forall c, endpoints_match_rec c ->
    Forall valid_walk (split_walks (chain_transfers c)) /\
    length (split_walks (chain_transfers c)) = S (seg_count c).
Proof.
  intros c Hrec. split.
  - apply split_walks_valid.
  - rewrite split_walks_length by (apply chain_transfers_nonempty).
    f_equal. apply count_breaks_chain_transfers. exact Hrec.
Qed.

(** Per-chain refinement step of Theorem 3.  A validated arbitrage
    chain in a reachable CFT satisfies the conditions of Definition 5
    over T0's transfer graph: inclusion, closure, recursive endpoint
    correspondence, the canonical walk-count characterization
    ([walk_decomposition_count]), and positive gross delta.
    [theorem_3_soundness] applies this to the cycle the verdict
    produces. *)
Lemma classify_structural_refinement :
  forall from_ T0 Tf c,
    walks_in_rcft T0 ->
    no_chains T0 ->
    rewrite_star from_ T0 Tf ->
    chain_in_rcft c Tf ->
    validated_arbitrage c ->
    ch_origin c = ch_destination c /\
    endpoints_match_rec c /\
    Forall valid_walk (split_walks (chain_transfers c)) /\
    length (split_walks (chain_transfers c)) = S (seg_count c) /\
    (exists rest,
        Permutation (chain_transfers c ++ rest) (rcft_transfers T0)) /\
    (ch_delta c (ch_origin c) (ch_token_in c) > 0)%Z /\
    tokens_match c /\
    token_equiv (ch_token_in c) (ch_token_out c) = true.
Proof.
  intros from_ T0 Tf c Hwalks Hnc Hstar Hin [Hlbl [Hdelta Hnp]].
  destruct (refinement_of_transfer_graph_cycles _ _ _ _
              Hwalks Hnc Hstar Hin Hlbl)
    as [_ [Hclos [Hepr [Htm Hteq]]]].
  destruct (walk_decomposition_count c Hepr) as [Hvalid Hlen].
  destruct (chain_submultiset_of_input from_ T0 Tf c Hstar Hin)
    as [rest Hperm].
  repeat apply conj; try assumption.
  exists rest. exact Hperm.
Qed.

(** Definition 5 over G(T0): a closed cycle ([ch_origin = ch_destination]),
    with recursive endpoint correspondence, whose leaves decompose into a
    FIXED number of maximal connected walks ([1 + seg_count c], so
    connectivity is pinned to the explicit parallel merges -- a merge-free
    cycle is a single connected walk), using only T0's own transfers, and
    netting positive gross delta at the origin.  Stated over G(T0) alone,
    with no reference to [classify] or the reduced AST. *)
Definition graph_arbitrage (T0 : reduced_cft) (c : chain_tree) : Prop :=
  ch_origin c = ch_destination c /\
  endpoints_match_rec c /\
  Forall valid_walk (split_walks (chain_transfers c)) /\
  length (split_walks (chain_transfers c)) = S (seg_count c) /\
  (exists rest,
      Permutation (chain_transfers c ++ rest) (rcft_transfers T0)) /\
  (ch_delta c (ch_origin c) (ch_token_in c) > 0)%Z /\
  tokens_match c /\
  token_equiv (ch_token_in c) (ch_token_out c) = true.

(* ============================================================
   Definition 5 in the vocabulary of the transfer graph.

   [graph_arbitrage] is a property of G(T0), but it reads its
   witness through the chain projections ([ch_origin],
   [ch_delta], [seg_count], ...).  [def5_witness] restates the
   same content using nothing but [transfer], [address],
   [token], [Z] and [list]: it is checkable directly on the
   transaction's edges, without any of the pipeline's type
   definitions.
   ============================================================ *)

(** Net flow of an address in one token over a flat transfer list. *)
Definition trace_delta (ts : list transfer) (a : address) (tok : token) : Z :=
  fold_right Z.add 0%Z (map (fun t => transfer_delta t a tok) ts).

(** Definition 5, over G(T0) alone.  A bundle of walks [Ws] witnesses an
    arbitrage on [v] in token [tok] over the edge set [E] when: the
    bundle is nonempty and each piece is a connected walk; the bundle is
    MAXIMAL, i.e. it is the maximal-run decomposition of its own
    concatenation (so [length Ws] is determined by the edge sequence and
    cannot be inflated by cutting a connected run in two); the
    concatenation leaves [v] and returns to it; the edges are a
    SUB-MULTISET of [E], so the bundle is backed edge-for-edge by [E]'s
    own transfers and cannot reuse one of them twice; and [v] nets
    strictly positive in [tok].

    Closure is a property of the concatenation, not of each walk: a cycle
    closed by a parallel merge carries sub-paths that do not individually
    return to [v], so per-walk closure would be false on the reachable
    witnesses. *)
Definition def5_witness
    (E : list transfer) (v : address) (tok : token)
    (Ws : list (list transfer)) : Prop :=
  Ws <> [] /\
  Forall valid_walk Ws /\
  Ws = split_walks (concat Ws) /\
  (forall d, tr_source (hd d (concat Ws)) = v) /\
  (forall d, tr_dest (last (concat Ws) d) = v) /\
  (forall d, token_equiv (tr_token (hd d (concat Ws)))
                         (tr_token (last (concat Ws) d)) = true) /\
  (forall d, tr_token (hd d (concat Ws)) = tok) /\
  (exists rest, Permutation (concat Ws ++ rest) E) /\
  (trace_delta (concat Ws) v tok > 0)%Z.

(** The bundle size is read off the edge sequence: one walk, plus one per
    adjacency break.  Maximality is what gives this clause content --
    without it, any witness could be split into singletons. *)
Corollary def5_walk_count :
  forall E v tok Ws,
    def5_witness E v tok Ws ->
    length Ws = S (count_breaks (concat Ws)).
Proof.
  intros E v tok Ws [Hne [_ [Hcan _]]].
  assert (Hcne : concat Ws <> []).
  { intro Hc. rewrite Hc in Hcan. cbn [split_walks] in Hcan. contradiction. }
  transitivity (length (split_walks (concat Ws))).
  - f_equal. exact Hcan.
  - apply split_walks_length. exact Hcne.
Qed.

(** BRIDGE: every [graph_arbitrage] witness yields a Definition-5 witness
    in the transfer vocabulary, namely its maximal walk decomposition.
    The delta clause transfers because [ch_delta] is the fold of the
    per-transfer deltas over the chain's leaves ([ch_delta_sum_leaves]). *)
Lemma graph_arbitrage_def5_witness :
  forall T0 c,
    graph_arbitrage T0 c ->
    def5_witness (rcft_transfers T0) (ch_origin c) (ch_token_in c)
                 (split_walks (chain_transfers c)).
Proof.
  intros T0 c [Hclos [Hepr [Hvw [Hlen [[rest Hperm] [Hdelta [Htm Hteq]]]]]]].
  assert (Hem : endpoints_match c)
    by (apply endpoints_match_rec_top; exact Hepr).
  repeat apply conj.
  - intro Hnil.
    apply (f_equal (@concat transfer)) in Hnil.
    rewrite split_walks_concat in Hnil. cbn [concat] in Hnil.
    exact (chain_transfers_nonempty c Hnil).
  - apply split_walks_valid.
  - rewrite split_walks_concat. reflexivity.
  - intro d. rewrite split_walks_concat.
    apply endpoints_match_src. exact Hem.
  - intro d. rewrite split_walks_concat, Hclos.
    apply endpoints_match_dest. exact Hem.
  - intro d. rewrite split_walks_concat.
    rewrite (tokens_match_src c d Htm), (tokens_match_dest c d Htm).
    exact Hteq.
  - intro d. rewrite split_walks_concat.
    apply tokens_match_src. exact Htm.
  - exists rest. rewrite split_walks_concat. exact Hperm.
  - rewrite split_walks_concat. unfold trace_delta.
    rewrite <- ch_delta_sum_leaves. exact Hdelta.
Qed.

(** The classical case: a cycle with no internal parallel merge
    ([seg_count c = 0]) is a SINGLE closed walk in G(T0).  The bundle
    form of Definition 5 is its conservative generalization, needed
    because a cycle closed by a parallel merge carries sub-paths that do
    not individually return to the origin. *)
Corollary def5_single_walk :
  forall T0 c,
    graph_arbitrage T0 c ->
    seg_count c = 0 ->
    exists W,
      valid_walk W /\
      def5_witness (rcft_transfers T0) (ch_origin c) (ch_token_in c) [W].
Proof.
  intros T0 c Hga Hsc.
  assert (Hd5 := graph_arbitrage_def5_witness T0 c Hga).
  destruct Hga as [_ [_ [_ [Hlen _]]]].
  rewrite Hsc in Hlen.
  remember (split_walks (chain_transfers c)) as Ws eqn:EW.
  destruct Ws as [| W ws]; [cbn [length] in Hlen; discriminate|].
  destruct ws as [| w2 ws']; [| cbn [length] in Hlen; discriminate].
  exists W. split.
  - destruct Hd5 as [_ [Hvw _]]. exact (Forall_inv Hvw).
  - exact Hd5.
Qed.

(** REGRESSION TEST, as a theorem.  A plain two-leg swap -- [v] sends
    token [u] to a pool, the pool returns token [w] to [v] -- is a closed
    walk over the transaction's own transfers that nets positive at [v]
    in [w].  It satisfies every other clause of Definition 5, and it is
    NOT an arbitrage.  The boundary-token clause is exactly what rejects
    it: the cycle leaves in [u] and returns in [w], so the round trip is
    not in one asset.  This pins down what the walk-like-an-arbitrage
    condition buys, and it fails on that clause alone. *)
Example plain_swap_not_def5 :
  forall (v p : address) (u w : token) (t1 t2 : transfer),
    tr_source t1 = v -> tr_dest t1 = p -> tr_token t1 = u ->
    tr_source t2 = p -> tr_dest t2 = v -> tr_token t2 = w ->
    token_equiv u w = false ->
    ~ def5_witness [t1; t2] v w [[t1; t2]].
Proof.
  intros v p u w t1 t2 Hs1 Hd1 Ht1 Hs2 Hd2 Ht2 Hne Hwit.
  destruct Hwit as [_ [_ [_ [_ [_ [Htok _]]]]]].
  specialize (Htok t1). cbn [concat app hd last] in Htok.
  rewrite Ht1, Ht2 in Htok. rewrite Htok in Hne. discriminate.
Qed.

(** An extracted arbitrage cycle is a chain of the tree it was pulled
    from. *)
Lemma extract_arb_cycles_in_rcft :
  forall t c, In c (extract_arb_cycles t) -> chain_in_rcft c t.
Proof.
  fix IH 1. intros t c. destruct t as [tr | c0 | addr children].
  - intros Hin. simpl in Hin. contradiction.
  - intros Hin. simpl in Hin.
    destruct (ch_label c0) eqn:Elab; simpl in Hin; try contradiction;
      destruct Hin as [Heq | []]; subst c0; apply CIR_here.
  - revert c. induction children as [| ch rest IHrest]; intros c Hin.
    + simpl in Hin. contradiction.
    + rewrite extract_arb_cycles_RTree_cons in Hin.
      apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      * eapply CIR_tree; [left; reflexivity | exact (IH ch c Hin)].
      * specialize (IHrest c Hin).
        inversion IHrest as [| cc aa cch child0 Hin0 Hch0]; subst.
        eapply CIR_tree; [right; exact Hin0 | exact Hch0].
Qed.

(* ############################################################
   Part V -- The five theorems (paper Table)
   ############################################################ *)

(* ============================================================
   Section 24: The five theorems (1:1 with the paper Table)

   The five theorems of the paper, each a single Rocq Theorem,
   in order; every supporting result above is a Lemma.  The
   decidable-equality bundle that makes Theorem 5 constructive
   follows the five.
   ============================================================ *)

(** Theorem 1 (Preservation): every transfer chain in the reduced AST
    corresponds to a walk-set in the original transfer graph; every
    transfer in the reduced AST is present in the input trace; and the
    transfer MULTISET is conserved, so the reduction re-brackets the
    trace's transfers without dropping or duplicating one.  Combines
    walk-correspondence, transfer-set inclusion, and conservation. *)
Theorem theorem_1_preservation :
  forall from_ T0 Tf,
    rewrite_star from_ T0 Tf ->
    walks_in_rcft T0 ->
    walks_in_rcft Tf /\
    (forall t, In t (rcft_transfers Tf) ->
               In t (rcft_transfers T0)) /\
    Permutation (rcft_transfers T0) (rcft_transfers Tf).
Proof.
  intros from_ T0 Tf Hstar Hwalks. repeat apply conj.
  - exact (walk_correspondence from_ T0 Tf Hstar Hwalks).
  - exact (preservation from_ T0 Tf Hstar).
  - exact (rcft_transfers_perm_star from_ T0 Tf Hstar).
Qed.

(** Theorem 2 (Termination), in the three parts the paper claims.
    (a) The deterministic fixpoint reaches a normal form for any
    starting tree.  (b) The work available to a fully-lifted tree is
    bounded by 3n-2 in the number of transfers: u0 <= n
    ([unlabeled_le_transfers]) and c0 <= 2n-2 (handshaking on a
    fully-lifted tree, [cc_plus2_le_twice_ct]).  (c) The
    NONDETERMINISTIC relation is well-founded, so termination does not
    depend on the deterministic strategy: every rewrite order
    terminates. *)
Theorem theorem_2_termination :
  forall from_ T0,
    (exists Tf,
        fixpoint_star_det from_ T0 Tf /\
        (forall T', ~ fixpoint_step_det from_ Tf T')) /\
    (fully_lifted T0 = true ->
     non_empty T0 = true ->
     count_unlabeled T0 + count_children T0
       <= 3 * count_transfers T0 - 2) /\
    well_founded (fun t' t => rewrite_step from_ t t').
Proof.
  intros from_ T0. repeat apply conj.
  - exact (fixpoint_terminates from_ T0).
  - intros Hfl Hne. exact (termination_bound T0 Hfl Hne).
  - exact (rewrite_step_wf from_).
Qed.

(** Theorem 3 (Soundness), stated over the transaction's transfer
    graph G(T0).  If the pipeline declares [VArbitrage] on any reduced
    form [Tf] of a freshly-decoded transaction [T0], then G(T0) contains
    an arbitrage in the graph-theoretic sense ([def5_witness]): an
    address [v], a token [tok], and a maximal bundle of connected walks
    over T0's own transfers that leaves [v], returns to [v], and nets
    strictly positive for [v] in [tok].

    The conclusion is stated in the vocabulary of the transfer graph --
    [transfer], [address], [token], [Z], [list] -- so it can be read
    and checked without any of the pipeline's type definitions.  The
    bundle carries one walk plus one per adjacency break
    ([def5_walk_count]), and reduces to a single closed walk when the
    cycle has no internal parallel merge ([def5_single_walk]).

    The classifier inspects [Tf]; the conclusion is a property of G(T0)
    alone.  The two are linked by preservation (Theorem 1 /
    [refinement_of_transfer_graph_cycles]): reduction introduces no
    edges or cycles, so a validated cycle in [Tf] decomposes into
    walks over T0's original transfers.  [soundness_graph_arbitrage] is
    the same result with the witness left in structural form. *)
Lemma soundness_graph_arbitrage :
  forall from_ T0 Tf has_left final_neg final_mixed,
    walks_in_rcft T0 ->
    no_chains T0 ->
    rewrite_star from_ T0 Tf ->
    classify
      (compute_reasons (has_arb_cycles Tf) has_left final_neg final_mixed)
      = VArbitrage ->
    validate_deltas (extract_arb_cycles Tf) <> [] ->
    exists c, graph_arbitrage T0 c.
Proof.
  intros from_ T0 Tf hl fn fm Hwalks Hnc Hstar Hclass Hne.
  destruct (soundness_end_to_end_tree Tf hl fn fm Hclass Hne)
    as [_ [c [Hin Hval]]].
  assert (Hcin : chain_in_rcft c Tf)
    by (apply extract_arb_cycles_in_rcft; apply (validate_deltas_subset _ c Hin)).
  destruct (classify_structural_refinement from_ T0 Tf c
              Hwalks Hnc Hstar Hcin Hval)
    as [Hclos [Hepr [Hvalid [Hlen [Htfs [Hdelta [Htm Hteq]]]]]]].
  exists c. unfold graph_arbitrage. repeat apply conj; assumption.
Qed.

Theorem theorem_3_soundness :
  forall from_ T0 Tf has_left final_neg final_mixed,
    walks_in_rcft T0 ->
    no_chains T0 ->
    rewrite_star from_ T0 Tf ->
    classify
      (compute_reasons (has_arb_cycles Tf) has_left final_neg final_mixed)
      = VArbitrage ->
    validate_deltas (extract_arb_cycles Tf) <> [] ->
    exists v tok Ws, def5_witness (rcft_transfers T0) v tok Ws.
Proof.
  intros from_ T0 Tf hl fn fm Hwalks Hnc Hstar Hclass Hne.
  destruct (soundness_graph_arbitrage from_ T0 Tf hl fn fm
              Hwalks Hnc Hstar Hclass Hne) as [c Hga].
  exists (ch_origin c), (ch_token_in c),
         (split_walks (chain_transfers c)).
  apply graph_arbitrage_def5_witness. exact Hga.
Qed.

(** Theorem 4 (Confluence): every starting tree has a unique
    normal form under the deterministic fixpoint.  Phase 2 is
    confluent separately ([phase2_confluence]); together they
    cover both rewriting phases. *)
Theorem theorem_4_confluence :
  forall from_ (T0 Tf1 Tf2 : reduced_cft),
    fixpoint_star_det from_ T0 Tf1 ->
    fixpoint_star_det from_ T0 Tf2 ->
    (forall T', ~ fixpoint_step_det from_ Tf1 T') ->
    (forall T', ~ fixpoint_step_det from_ Tf2 T') ->
    Tf1 = Tf2.
Proof.
  exact confluence.
Qed.

(** Theorem 5 (Decidable equivalence): joinability under the
    deterministic fixpoint is decidable, and equivalent to
    equality of normal forms. *)
Theorem theorem_5_decidable_equivalence :
  forall from_ (T1 T2 Nf1 Nf2 : reduced_cft),
    nf from_ T1 Nf1 ->
    nf from_ T2 Nf2 ->
    (joinable from_ T1 T2 <-> Nf1 = Nf2).
Proof.
  exact decidable_equivalence.
Qed.

(** Decidable equality on [construction_label],
    [transfer], [chain_tree], and [reduced_cft]:
    every component type has decidable equality,
    so [eq] is decidable by structural recursion.
    This is what makes the Theorem~5 iff
    *constructive*: a boolean witness of equality
    or inequality on normal forms. *)
Definition construction_label_eq_dec :
  forall (l1 l2 : construction_label), {l1 = l2} + {l1 <> l2}.
Proof. decide equality. Defined.

Definition transfer_eq_dec :
  forall (t1 t2 : transfer), {t1 = t2} + {t1 <> t2}.
Proof.
  intros [s1 d1 a1 tk1 sd1] [s2 d2 a2 tk2 sd2].
  destruct (address_eq_dec s1 s2); [|right; congruence].
  destruct (address_eq_dec d1 d2); [|right; congruence].
  destruct (Nat.eq_dec a1 a2); [|right; congruence].
  destruct (token_eq_dec tk1 tk2); [|right; congruence].
  destruct (address_eq_dec sd1 sd2); [|right; congruence].
  left; subst; reflexivity.
Defined.

Definition chain_tree_eq_dec :
  forall (c1 c2 : chain_tree), {c1 = c2} + {c1 <> c2}.
Proof.
  fix IH 1.
  intros [t1|o1 d1 m1 ti1 to1 ft1 lbl1 l1 r1]
         [t2|o2 d2 m2 ti2 to2 ft2 lbl2 l2 r2];
    try (right; discriminate).
  - destruct (transfer_eq_dec t1 t2);
      [left; congruence | right; congruence].
  - destruct (address_eq_dec o1 o2); [|right; congruence].
    destruct (address_eq_dec d1 d2); [|right; congruence].
    destruct (list_eq_dec address_eq_dec m1 m2);
      [|right; congruence].
    destruct (token_eq_dec ti1 ti2); [|right; congruence].
    destruct (token_eq_dec to1 to2); [|right; congruence].
    destruct (transfer_eq_dec ft1 ft2); [|right; congruence].
    destruct (construction_label_eq_dec lbl1 lbl2);
      [|right; congruence].
    destruct (IH l1 l2); [|right; congruence].
    destruct (IH r1 r2); [|right; congruence].
    left; subst; reflexivity.
Defined.

Definition reduced_cft_eq_dec :
  forall (T1 T2 : reduced_cft), {T1 = T2} + {T1 <> T2}.
Proof.
  fix IH 1.
  intros [t1|c1|a1 ch1] [t2|c2|a2 ch2];
    try (right; discriminate).
  - destruct (transfer_eq_dec t1 t2);
      [left; congruence | right; congruence].
  - destruct (chain_tree_eq_dec c1 c2);
      [left; congruence | right; congruence].
  - destruct (address_eq_dec a1 a2); [|right; congruence].
    destruct (list_eq_dec IH ch1 ch2);
      [left; congruence | right; congruence].
Defined.

(** Theorem 5 (constructive form): joinability is
    decidable in the constructive sense.  Given the
    normal forms of two reduced CFTs from the same
    address, we produce a boolean witness.  Composes
    the Prop-level iff [theorem_5_decidable_equivalence]
    with the structural [reduced_cft_eq_dec]. *)
Lemma theorem_5_decidable_equivalence_dec :
  forall from_ (T1 T2 Nf1 Nf2 : reduced_cft),
    nf from_ T1 Nf1 ->
    nf from_ T2 Nf2 ->
    {joinable from_ T1 T2} + {~ joinable from_ T1 T2}.
Proof.
  intros from_ T1 T2 Nf1 Nf2 Hnf1 Hnf2.
  destruct (reduced_cft_eq_dec Nf1 Nf2) as [Heq | Hneq].
  - left. apply (theorem_5_decidable_equivalence
                   from_ T1 T2 Nf1 Nf2 Hnf1 Hnf2).
    exact Heq.
  - right. intros Hj. apply Hneq.
    apply (theorem_5_decidable_equivalence
             from_ T1 T2 Nf1 Nf2 Hnf1 Hnf2).
    exact Hj.
Qed.

(* ############################################################
   Part VI -- Beyond the paper: the sigma-CFT as an algebra
   ############################################################ *)

(* ============================================================
   Section 25: Redex-complete kernel K_full (O0)

   Closing the formalization gap (formalization_gap.md):
   the headline Theorems 4/5 are stated over the
   deterministic kernel K, while the paper prose speaks
   about the free relation R = [rewrite_step].  The route
   is confluence of R modulo a canonical-association map
   kappa; its load-bearing prerequisite is O0
   (redex-completeness): a kernel that makes progress
   whenever R has a redex, so that kernel normal forms
   are R-normal forms.

   The kernel [step_fn] that drives Theorems 4/5 is
   tuned to the common regimes: it commits to the
   annotate-then-merge order, and its merge scan
   ([chains_mergeable]) targets closed, labeled cycles.
   K_full extends coverage to every redex of R --
   annotation-only progress, lifting, R6/R12
   (leaf-onto-chain), and the open merges R7 / R8-balcont
   -- so that kernel normal forms are exactly R-normal
   forms.  It is built alongside [step_fn], regime by
   regime.

   Regime 1 (this section): the exact-two-leaf trees
   [RTree addr [RLeaf t1; RLeaf t2]], where precisely
   the leaf-pair rules R1-R5 and R11 apply.
   [try_combine_leaves_full] is a deterministic
   priority cascade that returns [Some] iff some
   leaf-pair rule fires; unlike [try_combine_leaves]
   it has no completeness holes (router with
   differing tokens still falls through to R1; the
   R4 escape checks both senders; a failed R4 guard
   still reaches the R11/R1 branches).
   ============================================================ *)

(** [try_combine_leaves_full] is defined in Section 5 (hoisted
    above [rewrite_step] for the [RS_lift] guard).  Its
    soundness / O0 / completeness lemmas follow here. *)

(** Soundness: every [Some] of the full combiner is a
    [rewrite_step] on the two-leaf tree. *)
Lemma kfull_leaf_sound :
  forall from_ t1 t2 c addr,
    try_combine_leaves_full t1 t2 = Some c ->
    rewrite_step from_
      (RTree addr [RLeaf t1; RLeaf t2])
      (RTree addr [RChain c]).
Proof.
  intros from_ t1 t2 c addr Hfn.
  unfold try_combine_leaves_full in Hfn.
  destruct (address_eq_dec (tr_dest t1) (tr_source t2))
    as [Hadj | _]; [| discriminate].
  destruct (is_burn t1 && negb (is_mint t2)) eqn:Hb2.
  { apply andb_true_iff in Hb2 as [Hburn Hnm].
    apply negb_true_iff in Hnm.
    injection Hfn as <-.
    apply (RS_burn_chain from_ t1 t2 _ addr Hburn Hnm Hadj eq_refl). }
  destruct (is_mint t2 && negb (is_burn t1)) eqn:Hm2.
  { apply andb_true_iff in Hm2 as [Hmint Hnb].
    apply negb_true_iff in Hnb.
    injection Hfn as <-.
    apply (RS_mint_chain from_ t1 t2 _ addr Hmint Hnb Hadj eq_refl). }
  pose proof (burn_mint_agree t1 t2 Hb2 Hm2) as Hbm.
  destruct (token_eq_dec (tr_token t1) (tr_token t2))
    as [Htok | Htok_ne].
  - destruct (is_singleton_router (tr_dest t1)) eqn:Hr.
    { injection Hfn as <-.
      apply (RS_router_chain from_ t1 t2 _ addr Hadj Htok Hr
               Hbm eq_refl). }
    destruct (is_burn t1 || is_mint t2) eqn:Hbo; [discriminate |].
    apply orb_false_iff in Hbo as [Hburn Hmint].
    destruct (address_eq_dec (tr_dest t2) (tr_source t1))
      as [Hcyc | Hncyc].
    + destruct (address_eq_dec (tr_sender t1) (tr_dest t1))
        as [Hs1 | Hs1].
      * destruct (address_eq_dec (tr_sender t2) (tr_dest t2))
          as [Hs2 | Hs2]; [discriminate |].
        injection Hfn as <-.
        apply (RS_pool_cycle from_ t1 t2 _ addr Hadj Hcyc Htok
                 Hburn Hmint Hr (or_intror Hs2) eq_refl).
      * injection Hfn as <-.
        apply (RS_pool_cycle from_ t1 t2 _ addr Hadj Hcyc Htok
                 Hburn Hmint Hr (or_introl Hs1) eq_refl).
    + destruct (address_eq_dec (tr_sender t1) (tr_dest t1))
        as [_ | Hs1]; [discriminate |].
      injection Hfn as <-.
      apply (RS_same_token_chain from_ t1 t2 _ addr Hadj Htok
               Hburn Hmint Hr Hncyc Hs1 eq_refl).
  - injection Hfn as <-.
    assert (Hch : chainable t1 t2)
      by (split; [exact Hadj | exact Htok_ne]).
    apply (RS_swap_chain from_ t1 t2 _ addr Hch Hbm eq_refl).
Qed.

(** No element of a two-leaf child list is an [RChain]
    or an [RTree]; used to kill the non-leaf-rule cases
    in the completeness inversion. *)
Lemma two_leaves_no_chain :
  forall t1 t2 c,
    ~ In (RChain c) [RLeaf t1; RLeaf t2].
Proof.
  intros t1 t2 c [H | [H | H]];
    solve [discriminate | contradiction].
Qed.

Lemma two_leaves_no_tree :
  forall t1 t2 a ch,
    ~ In (RTree a ch) [RLeaf t1; RLeaf t2].
Proof.
  intros t1 t2 a ch [H | [H | H]];
    solve [discriminate | contradiction].
Qed.

(** Shape refutations: the two-leaf child list cannot
    match the LHS child-list patterns of the structural
    constructors (merges, annotations, R6/R12, R10,
    lift).  Stated in both orientations so [inversion]
    equations match syntactically. *)
Lemma shape_chain_mid :
  forall (L R' : list reduced_cft) c t1 t2,
    L ++ [RChain c] ++ R' = [RLeaf t1; RLeaf t2] -> False.
Proof.
  intros L R' c t1 t2 Heq.
  apply (two_leaves_no_chain t1 t2 c).
  rewrite <- Heq.
  apply in_or_app; right; left; reflexivity.
Qed.

Lemma shape_leaf_chain :
  forall (siblings : list reduced_cft) t c t1 t2,
    siblings ++ [RLeaf t; RChain c] = [RLeaf t1; RLeaf t2] -> False.
Proof.
  intros siblings t c t1 t2 Heq.
  apply (two_leaves_no_chain t1 t2 c).
  rewrite <- Heq.
  apply in_or_app; right; right; left; reflexivity.
Qed.

Lemma shape_chain_chain :
  forall (siblings : list reduced_cft) c1 c2 t1 t2,
    siblings ++ [RChain c1; RChain c2] = [RLeaf t1; RLeaf t2] -> False.
Proof.
  intros siblings c1 c2 t1 t2 Heq.
  apply (two_leaves_no_chain t1 t2 c1).
  rewrite <- Heq.
  apply in_or_app; right; left; reflexivity.
Qed.

Lemma shape_tree_last :
  forall (siblings : list reduced_cft) a ch t1 t2,
    siblings ++ [RTree a ch] = [RLeaf t1; RLeaf t2] -> False.
Proof.
  intros siblings a ch t1 t2 Heq.
  apply (two_leaves_no_tree t1 t2 a ch).
  rewrite <- Heq.
  apply in_or_app; right; left; reflexivity.
Qed.

(** The source of any [rewrite_step] is an [RTree]: no
    rule fires on a bare leaf or chain.  Used to refute
    the [RS_under] congruence case on a two-leaf tree,
    whose stepping child would have to be a leaf. *)
Lemma rewrite_step_lhs_tree :
  forall from_ T T',
    rewrite_step from_ T T' -> exists a ch, T = RTree a ch.
Proof.
  intros from_ T T' Hstep. destruct Hstep; do 2 eexists; reflexivity.
Qed.

(** A two-leaf child list contains no interior [RTree]. *)
Lemma two_leaves_no_tree_mid :
  forall L (a : address) ch R t1 t2,
    L ++ [RTree a ch] ++ R = [RLeaf t1; RLeaf t2] -> False.
Proof.
  intros L a ch R t1 t2 Heq.
  assert (Hin : In (RTree a ch) [RLeaf t1; RLeaf t2]).
  { rewrite <- Heq. apply in_or_app. right. left. reflexivity. }
  destruct Hin as [H | [H | []]]; discriminate.
Qed.

Ltac kill_shape :=
  exfalso;
  match goal with
  | Hsub : rewrite_step _ ?T _ |- _ =>
      is_var T;
      apply rewrite_step_lhs_tree in Hsub;
      destruct Hsub as [aa [chh HT]]; subst T;
      match goal with
      | H : _ ++ [RTree _ _] ++ _ = [RLeaf _; RLeaf _] |- _ =>
          exact (two_leaves_no_tree_mid _ _ _ _ _ _ H)
      | H : _ ++ RTree _ _ :: _ = [RLeaf _; RLeaf _] |- _ =>
          exact (two_leaves_no_tree_mid _ _ _ _ _ _ H)
      | H : [RLeaf _; RLeaf _] = _ ++ [RTree _ _] ++ _ |- _ =>
          exact (two_leaves_no_tree_mid _ _ _ _ _ _ (eq_sym H))
      | H : [RLeaf _; RLeaf _] = _ ++ RTree _ _ :: _ |- _ =>
          exact (two_leaves_no_tree_mid _ _ _ _ _ _ (eq_sym H))
      end
  | H : ?L ++ RChain _ :: _ = [RLeaf _; RLeaf _] |- _ =>
      exact (shape_chain_mid _ _ _ _ _ H)
  | H : [RLeaf _; RLeaf _] = ?L ++ RChain _ :: _ |- _ =>
      exact (shape_chain_mid _ _ _ _ _ (eq_sym H))
  | H : ?L ++ [RChain _] ++ _ = [RLeaf _; RLeaf _] |- _ =>
      exact (shape_chain_mid _ _ _ _ _ H)
  | H : [RLeaf _; RLeaf _] = ?L ++ [RChain _] ++ _ |- _ =>
      exact (shape_chain_mid _ _ _ _ _ (eq_sym H))
  | H : _ ++ [RLeaf _; RChain _] = [RLeaf _; RLeaf _] |- _ =>
      exact (shape_leaf_chain _ _ _ _ _ H)
  | H : [RLeaf _; RLeaf _] = _ ++ [RLeaf _; RChain _] |- _ =>
      exact (shape_leaf_chain _ _ _ _ _ (eq_sym H))
  | H : _ ++ [RChain _; RChain _] = [RLeaf _; RLeaf _] |- _ =>
      exact (shape_chain_chain _ _ _ _ _ H)
  | H : [RLeaf _; RLeaf _] = _ ++ [RChain _; RChain _] |- _ =>
      exact (shape_chain_chain _ _ _ _ _ (eq_sym H))
  | H : _ ++ [RTree _ _] = [RLeaf _; RLeaf _] |- _ =>
      exact (shape_tree_last _ _ _ _ _ H)
  | H : [RLeaf _; RLeaf _] = _ ++ [RTree _ _] |- _ =>
      exact (shape_tree_last _ _ _ _ _ (eq_sym H))
  end.

(** O0, Regime 1 (completeness direction): when the
    full combiner returns [None], no [rewrite_step]
    fires on the two-leaf tree.  One inversion; the
    structural constructors die on the shape lemmas;
    each leaf-rule constructor exploits [Hnone]
    directly: destructing the combiner guards, every
    [Some] branch contradicts [Hnone] by
    [discriminate], and every surviving guard path
    contradicts one of the rule's premises by
    [congruence]. *)
Lemma kfull_leaf_O0 :
  forall from_ addr t1 t2,
    try_combine_leaves_full t1 t2 = None ->
    forall T', ~ rewrite_step from_ (RTree addr [RLeaf t1; RLeaf t2]) T'.
Proof.
  intros from_ addr t1 t2 Hnone T' Hstep.
  unfold try_combine_leaves_full in Hnone.
  inversion Hstep; subst; try kill_shape;
    unfold chainable in *;
    repeat match goal with
      | Hn : (if ?d then _ else _) = None |- _ =>
          destruct d eqn:?; try discriminate Hn
      end;
    repeat match goal with
      | H : _ && _ = true  |- _ => apply andb_true_iff in H; destruct H
      | H : _ && _ = false |- _ => apply andb_false_iff in H; destruct H
      | H : _ || _ = true  |- _ => apply orb_true_iff in H; destruct H
      | H : _ || _ = false |- _ => apply orb_false_iff in H; destruct H
      | H : negb _ = true  |- _ => apply negb_true_iff in H
      | H : negb _ = false |- _ => apply negb_false_iff in H
      end;
    intuition congruence.
Qed.

(** Completeness, existential form: any step from the
    two-leaf tree means the combiner succeeds. *)
Lemma kfull_leaf_complete :
  forall from_ addr t1 t2 T',
    rewrite_step from_ (RTree addr [RLeaf t1; RLeaf t2]) T' ->
    exists c, try_combine_leaves_full t1 t2 = Some c.
Proof.
  intros from_ addr t1 t2 T' Hstep.
  destruct (try_combine_leaves_full t1 t2) as [c |] eqn:Hfn.
  - exists c. reflexivity.
  - exfalso.
    exact (kfull_leaf_O0 from_ addr t1 t2 Hfn T' Hstep).
Qed.

(** The leaf-pair rules R1-R5 and R11 are mutually
    exclusive: on a two-leaf tree at most one fires, so
    the step is deterministic.  Every cross-rule pair is
    refuted by a guard clash (burn/mint flag, router
    flag, same-token, or the bidirectionality that
    separates R4 from R11); same-rule pairs build the
    identical chain.  This is the load-bearing
    prerequisite for O2: it removes the label-divergent
    critical pairs (e.g. swap/Chaining vs pool/Cycle)
    that [kappa] provably could not join, since [kappa]
    preserves labels. *)
Lemma leaf_pair_exclusive :
  forall from_ addr t1 t2 T1 T2,
    rewrite_step from_ (RTree addr [RLeaf t1; RLeaf t2]) T1 ->
    rewrite_step from_ (RTree addr [RLeaf t1; RLeaf t2]) T2 ->
    T1 = T2.
Proof.
  intros from_ addr t1 t2 T1 T2 H1 H2.
  inversion H1; subst; try kill_shape;
    inversion H2; subst; try kill_shape;
    unfold chainable in *; intuition congruence.
Qed.

(* ------------------------------------------------------------
   Section 26: General-tree kernel step (Regime 2)

   [kfull_step] covers every root-level R-redex class on an
   arbitrary [RTree]: two-leaf combination (Regime 1),
   leaf-onto-chain (R6/R12) and sequential chaining (R10) at
   the last two children, lifting of a flat last child,
   annotation (R14/R15) at any position, and the four merge
   rules (R7/R8/R9/R13) at any pair of positions.
   ------------------------------------------------------------ *)

(** Split a list into (init, last-two).  [Some] iff
    length >= 2.  Defined via [rev] so the spec is a
    computation. *)
Definition split_last_two (l : list reduced_cft)
    : option (list reduced_cft * reduced_cft * reduced_cft) :=
  match rev l with
  | b :: a :: rst => Some (rev rst, a, b)
  | _ => None
  end.

Lemma split_last_two_spec :
  forall l sib a b,
    split_last_two l = Some (sib, a, b) ->
    l = sib ++ [a; b].
Proof.
  unfold split_last_two. intros l sib a b H.
  destruct (rev l) as [| b0 [| a0 rst]] eqn:Hr;
    try discriminate.
  injection H as <- <- <-.
  rewrite <- (rev_involutive l), Hr. simpl.
  rewrite <- app_assoc. reflexivity.
Qed.

(** Split a list into (init, last).  [Some] iff nonempty. *)
Definition split_last (l : list reduced_cft)
    : option (list reduced_cft * reduced_cft) :=
  match rev l with
  | a :: rst => Some (rev rst, a)
  | [] => None
  end.

Lemma split_last_spec :
  forall l sib a,
    split_last l = Some (sib, a) ->
    l = sib ++ [a].
Proof.
  unfold split_last. intros l sib a H.
  destruct (rev l) as [| a0 rst] eqn:Hr; [discriminate|].
  injection H as <- <-.
  rewrite <- (rev_involutive l), Hr. simpl. reflexivity.
Qed.

(** Boolean flatness of a child; bridges to the [RS_lift]
    premise. *)
Definition flat_childb (x : reduced_cft) : bool :=
  match x with
  | RTree _ _ => false
  | _ => true
  end.

Lemma flat_childb_Forall :
  forall l,
    forallb flat_childb l = true ->
    Forall (fun c => match c with
                     | RLeaf _ | RChain _ => True
                     | RTree _ _ => False
                     end) l.
Proof.
  induction l as [| x rest IH]; intros H; [constructor|].
  simpl in H. apply andb_true_iff in H as [Hx Hrest].
  constructor.
  - destruct x; simpl in Hx; solve [exact I | discriminate].
  - apply IH. exact Hrest.
Qed.

(** [is_ct_node]: annotation needs a [CT_node] (a bare
    [CT_transfer] cannot carry a Cycle/Arbitrage label, so
    R14/R15 have no witness on it). *)
Definition is_ct_node (c : chain_tree) : bool :=
  match c with
  | CT_node _ _ _ _ _ _ _ _ _ => true
  | CT_transfer _ => false
  end.

(** A chain is annotatable when closed, unlabeled, a node,
    and either the orchestrator sits inside (R15) or the
    tokens close modulo =_tau with no wrap/unwrap roundtrip
    (R14, orchestrator outside). *)
Definition annotatableb (from_ : address) (c : chain_tree) : bool :=
  is_ct_node c
  && negb (is_labeled (ch_label c))
  && (if address_eq_dec (ch_origin c) (ch_destination c)
      then true else false)
  && (address_in_chain from_ c
      || (token_equiv (ch_token_in c) (ch_token_out c)
          && negb (wrap_unwrap c))).

Definition annot_label (from_ : address) (c : chain_tree)
    : construction_label :=
  if token_equiv (ch_token_in c) (ch_token_out c)
     && negb (wrap_unwrap c)
     && (negb (address_in_chain from_ c)
         || (if address_eq_dec (ch_origin c) from_ then true else false))
  then Arbitrage
  else Cycle.

(** [annot_label] produces exactly the R14/R15 dispatch:
    [Arbitrage] iff the R14 label condition holds
    ([token] continuity, no wrap/unwrap, orchestrator
    outside or the origin), [Cycle] otherwise.  The
    three lemmas below expose that its output is always
    justified by the corresponding annotation rule. *)
Lemma annotatableb_inv :
  forall from_ c,
    annotatableb from_ c = true ->
    is_ct_node c = true /\
    is_labeled (ch_label c) = false /\
    ch_origin c = ch_destination c.
Proof.
  intros from_ c H. unfold annotatableb in H.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H Hclosed].
  apply andb_true_iff in H as [Hnode Hunlab].
  apply negb_true_iff in Hunlab.
  repeat split; try assumption.
  destruct (address_eq_dec (ch_origin c) (ch_destination c));
    [assumption | discriminate].
Qed.

Lemma annot_label_arb_or_cyc :
  forall from_ c,
    annot_label from_ c = Arbitrage \/ annot_label from_ c = Cycle.
Proof.
  intros from_ c. unfold annot_label.
  destruct (_ && _ && _); [left | right]; reflexivity.
Qed.

Lemma annot_label_arb_sound :
  forall from_ c,
    annot_label from_ c = Arbitrage ->
    token_equiv (ch_token_in c) (ch_token_out c) = true /\
    wrap_unwrap c = false /\
    (address_in_chain from_ c = false \/ ch_origin c = from_).
Proof.
  intros from_ c Harb. unfold annot_label in Harb.
  destruct (token_equiv (ch_token_in c) (ch_token_out c)
            && negb (wrap_unwrap c)
            && (negb (address_in_chain from_ c)
                || (if address_eq_dec (ch_origin c) from_
                    then true else false))) eqn:B;
    [| discriminate].
  apply andb_true_iff in B as [B1 B2].
  apply andb_true_iff in B1 as [Bt Bw].
  apply negb_true_iff in Bw.
  split; [exact Bt|]. split; [exact Bw|].
  apply orb_true_iff in B2. destruct B2 as [Bin | Bo].
  - left. apply negb_true_iff in Bin. exact Bin.
  - right.
    destruct (address_eq_dec (ch_origin c) from_);
      [assumption | discriminate].
Qed.

Lemma annot_label_cyc_sound :
  forall from_ c,
    annotatableb from_ c = true ->
    annot_label from_ c = Cycle ->
    address_in_chain from_ c = true /\
    (token_equiv (ch_token_in c) (ch_token_out c) = false \/
     wrap_unwrap c = true \/
     ch_origin c <> from_).
Proof.
  intros from_ c Hann Hcyc.
  unfold annotatableb in Hann.
  apply andb_true_iff in Hann as [_ Hor].
  unfold annot_label in Hcyc.
  destruct (token_equiv (ch_token_in c) (ch_token_out c)
            && negb (wrap_unwrap c)
            && (negb (address_in_chain from_ c)
                || (if address_eq_dec (ch_origin c) from_
                    then true else false))) eqn:B;
    [discriminate|].
  split.
  - destruct (address_in_chain from_ c) eqn:Ein; [reflexivity|].
    exfalso. simpl in Hor. rewrite Hor in B. discriminate.
  - apply andb_false_iff in B as [B1 | Brc].
    + apply andb_false_iff in B1 as [Bt | Bw].
      * left. exact Bt.
      * right. left. apply negb_false_iff in Bw. exact Bw.
    + apply orb_false_iff in Brc as [_ Bo].
      right. right.
      destruct (address_eq_dec (ch_origin c) from_) as [_|Hne];
        [discriminate Bo | exact Hne].
Qed.

(** [prepend_leaf_chain], [append_leaf_chain], [seq_chain] are defined
    in Section 5 (hoisted above [rewrite_step] for the R6/R12/R10
    witnesses). *)

Definition merge_chain (c1 c2 : chain_tree) : chain_tree :=
  CT_node (ch_origin c1) (ch_destination c1) []
          (ch_token_in c1) (ch_token_out c2) (ch_first_transfer c1)
          Merging c1 c2.

(** The four merge-rule guards (R7 / R8 / R9 / R13). *)
Definition r7b (c1 c2 : chain_tree) : bool :=
  (if address_eq_dec (ch_origin c1) (ch_origin c2)
   then true else false)
  && (if address_eq_dec (ch_destination c1) (ch_destination c2)
      then true else false)
  && negb (if address_eq_dec (ch_origin c1) (ch_destination c1)
           then true else false)
  && (if token_eq_dec (ch_token_out c1) (ch_token_out c2)
      then true else false)
  && negb (if token_eq_dec (ch_token_mid c1) (ch_token_mid c2)
           then true else false).

Definition r8b (c1 c2 : chain_tree) : bool :=
  (if address_eq_dec (ch_origin c1) (ch_origin c2)
   then true else false)
  && (if address_eq_dec (ch_destination c1) (ch_destination c2)
      then true else false)
  && (if address_eq_dec (ch_origin c1) (ch_destination c1)
      then true else false)
  && (((if token_eq_dec (ch_token_in c1) (ch_token_in c2)
        then true else false)
       && (if token_eq_dec (ch_token_mid c1) (ch_token_mid c2)
           then true else false)
       && (if token_eq_dec (ch_token_out c1) (ch_token_out c2)
           then true else false))
      || bal_cont (ch_origin c1) c1 c2).

Definition r9b (c1 c2 : chain_tree) : bool :=
  (if address_eq_dec (ch_origin c1) (ch_destination c1)
   then true else false)
  && (if address_eq_dec (ch_origin c2) (ch_destination c2)
      then true else false)
  && (if address_eq_dec (ch_origin c1) (ch_origin c2)
      then true else false)
  && (if token_eq_dec (ch_token_in c1) (ch_token_in c2)
      then true else false)
  && (if token_eq_dec (ch_token_out c1) (ch_token_out c2)
      then true else false).

Definition r13b (c1 c2 : chain_tree) : bool :=
  r7b c1 c2
  && (if token_eq_dec (ch_token_in c1) (ch_token_in c2)
      then true else false).

Definition mergeable_fullb (c1 c2 : chain_tree) : bool :=
  r7b c1 c2 || r8b c1 c2 || r9b c1 c2 || r13b c1 c2.

(** Annotation scan: first annotatable chain, in list order. *)
Fixpoint annotate_scan
    (from_ : address)
    (prefix suffix : list reduced_cft)
    : option (list reduced_cft) :=
  match suffix with
  | [] => None
  | RChain c :: rest =>
      if annotatableb from_ c
      then Some (prefix
                   ++ [RChain (set_chain_label c (annot_label from_ c))]
                   ++ rest)
      else annotate_scan from_ (prefix ++ [RChain c]) rest
  | x :: rest => annotate_scan from_ (prefix ++ [x]) rest
  end.

(** Merge scan, inner loop: [c1] fixed at position [prefix];
    scan [after] for a partner. *)
Fixpoint merge_scan_pair
    (c1 : chain_tree)
    (prefix before after : list reduced_cft)
    : option (list reduced_cft) :=
  match after with
  | [] => None
  | RChain c2 :: after' =>
      if mergeable_fullb c1 c2
      then Some (prefix ++ before
                   ++ [RChain (merge_chain c1 c2)] ++ after')
      else merge_scan_pair c1 prefix (before ++ [RChain c2]) after'
  | x :: after' =>
      merge_scan_pair c1 prefix (before ++ [x]) after'
  end.

(** Merge scan, outer loop: pick the first chain that has a
    partner. *)
Fixpoint merge_scan
    (prefix suffix : list reduced_cft)
    : option (list reduced_cft) :=
  match suffix with
  | [] => None
  | RChain c1 :: rest =>
      match merge_scan_pair c1 prefix [] rest with
      | Some l' => Some l'
      | None => merge_scan (prefix ++ [RChain c1]) rest
      end
  | x :: rest => merge_scan (prefix ++ [x]) rest
  end.

(** Last-two structural step: R6/R12 leaf-onto-chain (tied
    adjacency picks prepend vs append) or R10 sequential
    chaining. *)
Definition last_two_step
    (children : list reduced_cft) : option (list reduced_cft) :=
  match split_last_two children with
  | Some (sib, RLeaf t, RChain c) =>
      if address_eq_dec (tr_dest t) (ch_origin c)
      then Some (sib ++ [RChain (prepend_leaf_chain t c)])
      else if address_eq_dec (ch_destination c) (tr_source t)
      then Some (sib ++ [RChain (append_leaf_chain c t)])
      else None
  | Some (sib, RChain c1, RChain c2) =>
      if address_eq_dec (ch_destination c1) (ch_origin c2)
      then if (if token_eq_dec (ch_token_out c1) (ch_token_in c2)
               then true else false)
              || bal_cont (ch_destination c1) c1 c2
           then Some (sib ++ [RChain (seq_chain c1 c2)])
           else None
      else None
  | _ => None
  end.

(** Lift step: last child is a tree with flat children that is
    already reduced ([lift_ok_b], i.e. not a fireable two-leaf
    redex), matching the [RS_lift] guard. *)
Definition lift_step
    (children : list reduced_cft) : option (list reduced_cft) :=
  match split_last children with
  | Some (sib, RTree _ inner) =>
      if forallb flat_childb inner && lift_ok_b inner
      then Some (sib ++ inner)
      else None
  | _ => None
  end.

(** The general-tree kernel step. *)
Definition kfull_step
    (from_ : address) (T : reduced_cft) : option reduced_cft :=
  match T with
  | RTree addr [RLeaf t1; RLeaf t2] =>
      match try_combine_leaves_full t1 t2 with
      | Some c => Some (RTree addr [RChain c])
      | None => None
      end
  | RTree addr children =>
      match last_two_step children with
      | Some l' => Some (RTree addr l')
      | None =>
          match lift_step children with
          | Some l' => Some (RTree addr l')
          | None =>
              match annotate_scan from_ [] children with
              | Some l' => Some (RTree addr l')
              | None =>
                  match merge_scan [] children with
                  | Some l' => Some (RTree addr l')
                  | None => None
                  end
              end
          end
      end
  | _ => None
  end.

(** Soundness of the lift branch. *)
Lemma lift_step_sound :
  forall from_ addr children l',
    lift_step children = Some l' ->
    rewrite_step from_ (RTree addr children) (RTree addr l').
Proof.
  intros from_ addr children l' H.
  unfold lift_step in H.
  destruct (split_last children) as [[sib x] |] eqn:Hsp;
    [| discriminate].
  destruct x as [t | c | a inner]; try discriminate.
  destruct (forallb flat_childb inner) eqn:Hflat;
    [| discriminate].
  destruct (lift_ok_b inner) eqn:Hok; cbn in H; [| discriminate].
  injection H as <-.
  apply split_last_spec in Hsp. subst children.
  apply RS_lift.
  - apply flat_childb_Forall. exact Hflat.
  - unfold lift_children_ok. exact Hok.
Qed.

(** Soundness of the last-two branch (R6 leaf-onto-chain
    with tied adjacency, R10 sequential chaining). *)
Lemma last_two_step_sound :
  forall from_ addr children l',
    last_two_step children = Some l' ->
    rewrite_step from_ (RTree addr children) (RTree addr l').
Proof.
  intros from_ addr children l' H.
  unfold last_two_step in H.
  destruct (split_last_two children)
    as [[[sib x] y] |] eqn:Hsp; [| discriminate].
  apply split_last_two_spec in Hsp.
  destruct x as [t | c1 | ? ?]; try discriminate;
    destruct y as [? | c | ? ?]; try discriminate.
  - (* [RLeaf t; RChain c] : R6 *)
    destruct (address_eq_dec (tr_dest t) (ch_origin c))
      as [Hpre | Hnpre].
    + injection H as <-. subst children.
      apply (RS_leaf_chain from_ t c (prepend_leaf_chain t c) addr sib).
      * reflexivity.
      * left. repeat split; try exact Hpre; try reflexivity.
    + destruct (address_eq_dec (ch_destination c) (tr_source t))
        as [Happ | Hnapp]; [| discriminate].
      injection H as <-. subst children.
      apply (RS_leaf_chain from_ t c (append_leaf_chain c t) addr sib).
      * reflexivity.
      * right. repeat split;
          try exact Happ; try exact Hnpre; try reflexivity.
  - (* [RChain c1; RChain c] : R10 *)
    destruct (address_eq_dec (ch_destination c1) (ch_origin c))
      as [Hadj | Hnadj]; [| discriminate].
    destruct ((if token_eq_dec (ch_token_out c1) (ch_token_in c)
               then true else false)
              || bal_cont (ch_destination c1) c1 c) eqn:Hor;
      [| discriminate].
    injection H as <-. subst children.
    apply (RS_chain_seq from_ c1 c (seq_chain c1 c) addr sib);
      try reflexivity.
    + exact Hadj.
    + apply orb_true_iff in Hor. destruct Hor as [Htok | Hbc].
      * left.
        destruct (token_eq_dec (ch_token_out c1) (ch_token_in c));
          [assumption | discriminate].
      * right. exact Hbc.
Qed.

(** Soundness of the annotation scan: a hit is one
    R14 or R15 application at the hit position. *)
Lemma annotate_scan_sound :
  forall from_ addr suffix prefix l',
    annotate_scan from_ prefix suffix = Some l' ->
    rewrite_step from_ (RTree addr (prefix ++ suffix)) (RTree addr l').
Proof.
  intros from_ addr suffix.
  induction suffix as [| x rest IH]; intros prefix l' H;
    [discriminate |].
  simpl in H.
  destruct x as [t | c | a ch].
  - (* RLeaf: skip *)
    specialize (IH (prefix ++ [RLeaf t]) l' H).
    rewrite <- app_assoc in IH. exact IH.
  - (* RChain c *)
    destruct (annotatableb from_ c) eqn:Hann.
    + injection H as <-.
      pose proof (annotatableb_inv from_ c Hann) as [Hnode [Hunlab Hcd]].
      destruct c as [t0 | o d m ti to_ ft lbl cl cr];
        [discriminate Hnode |].
      destruct (annot_label_arb_or_cyc from_
                  (CT_node o d m ti to_ ft lbl cl cr)) as [Ha | Hc].
      * (* R14: annot_label = Arbitrage *)
        pose proof (annot_label_arb_sound from_ _ Ha)
          as [Htok [Hwrap Hdisj]].
        rewrite Ha.
        apply (RS_annotate_arb from_ _ (set_chain_label _ Arbitrage)
                 addr prefix rest);
          try reflexivity; try assumption.
      * (* R15: annot_label = Cycle *)
        pose proof (annot_label_cyc_sound from_ _ Hann Hc)
          as [Hin Hguard].
        rewrite Hc.
        apply (RS_annotate_cyc from_ _ (set_chain_label _ Cycle)
                 addr prefix rest);
          try reflexivity; try assumption.
    + specialize (IH (prefix ++ [RChain c]) l' H).
      rewrite <- app_assoc in IH. exact IH.
  - (* RTree: skip *)
    specialize (IH (prefix ++ [RTree a ch]) l' H).
    rewrite <- app_assoc in IH. exact IH.
Qed.

(** Boolean-guard destructor for the merge soundness
    cases. *)
Ltac beq :=
  repeat match goal with
  | H : (if address_eq_dec ?a ?b then true else false) = true
    |- _ => destruct (address_eq_dec a b); [| discriminate]
  | H : (if token_eq_dec ?a ?b then true else false) = true
    |- _ => destruct (token_eq_dec a b); [| discriminate]
  | H : negb ?x = true |- _ => apply negb_true_iff in H
  | H : (if address_eq_dec ?a ?b then true else false) = false
    |- _ => destruct (address_eq_dec a b); [discriminate |]
  | H : (if token_eq_dec ?a ?b then true else false) = false
    |- _ => destruct (token_eq_dec a b); [discriminate |]
  | H : _ && _ = true |- _ =>
      apply andb_true_iff in H; destruct H
  end.

(** Soundness of the inner merge scan. *)
Lemma merge_scan_pair_sound :
  forall from_ addr c1 after prefix before l',
    merge_scan_pair c1 prefix before after = Some l' ->
    rewrite_step from_
      (RTree addr (prefix ++ [RChain c1] ++ before ++ after))
      (RTree addr l').
Proof.
  intros from_ addr c1 after.
  induction after as [| x rest IH]; intros prefix before l' H;
    [discriminate |].
  simpl in H.
  destruct x as [t | c2 | a ch].
  - specialize (IH prefix (before ++ [RLeaf t]) l' H).
    rewrite <- app_assoc in IH. exact IH.
  - destruct (mergeable_fullb c1 c2) eqn:Hm.
    + injection H as <-.
      unfold mergeable_fullb in Hm.
      apply orb_true_iff in Hm as [Hm | H13].
      apply orb_true_iff in Hm as [Hm | H9].
      apply orb_true_iff in Hm as [H7 | H8].
      * (* R7 *)
        unfold r7b in H7. beq.
        apply (RS_merge_endpoints from_ c1 c2 (merge_chain c1 c2)
                 addr prefix before rest);
          solve [reflexivity | assumption].
      * (* R8 *)
        unfold r8b in H8. beq.
        match goal with
        | Hor : _ || _ = true |- _ =>
            apply orb_true_iff in Hor;
            destruct Hor as [Htoks | Hbc]
        end.
        -- apply andb_true_iff in Htoks as [Ht12 Ht3].
           apply andb_true_iff in Ht12 as [Ht1 Ht2]. beq.
           apply (RS_merge_add from_ c1 c2 (merge_chain c1 c2)
                    addr prefix before rest);
             try solve [reflexivity | assumption].
           left. split; [assumption | split; assumption].
        -- apply (RS_merge_add from_ c1 c2 (merge_chain c1 c2)
                    addr prefix before rest);
             try solve [reflexivity | assumption].
           right. exact Hbc.
      * (* R9 *)
        unfold r9b in H9. beq.
        apply (RS_merge_closed_R9 from_ c1 c2 (merge_chain c1 c2)
                 addr prefix before rest);
          solve [reflexivity | assumption].
      * (* R13 : [r13b] is [r7b] plus the entry-token clause *)
        unfold r13b, r7b in H13. beq.
        apply (RS_merge_node from_ c1 c2 (merge_chain c1 c2)
                 addr prefix before rest);
          solve [reflexivity | assumption].
    + specialize (IH prefix (before ++ [RChain c2]) l' H).
      rewrite <- app_assoc in IH. exact IH.
  - specialize (IH prefix (before ++ [RTree a ch]) l' H).
    rewrite <- app_assoc in IH. exact IH.
Qed.

(** Soundness of the outer merge scan. *)
Lemma merge_scan_sound :
  forall from_ addr suffix prefix l',
    merge_scan prefix suffix = Some l' ->
    rewrite_step from_ (RTree addr (prefix ++ suffix)) (RTree addr l').
Proof.
  intros from_ addr suffix.
  induction suffix as [| x rest IH]; intros prefix l' H;
    [discriminate |].
  simpl in H.
  destruct x as [t | c1 | a ch].
  - specialize (IH (prefix ++ [RLeaf t]) l' H).
    rewrite <- app_assoc in IH. exact IH.
  - destruct (merge_scan_pair c1 prefix [] rest) eqn:Hpair.
    + injection H as <-.
      exact (merge_scan_pair_sound from_ addr c1 rest prefix [] l Hpair).
    + specialize (IH (prefix ++ [RChain c1]) l' H).
      rewrite <- app_assoc in IH. exact IH.
  - specialize (IH (prefix ++ [RTree a ch]) l' H).
    rewrite <- app_assoc in IH. exact IH.
Qed.

(** General-arm soundness: on any child list, the
    priority chain (last-two, lift, annotate, merge)
    yields one [rewrite_step].  Proved by destructing
    the option chain directly, so it needs no reduction
    of the [rev]-based splitters. *)
Lemma kfull_general_sound :
  forall from_ addr children T',
    match last_two_step children with
    | Some l' => Some (RTree addr l')
    | None =>
        match lift_step children with
        | Some l' => Some (RTree addr l')
        | None =>
            match annotate_scan from_ [] children with
            | Some l' => Some (RTree addr l')
            | None =>
                match merge_scan [] children with
                | Some l' => Some (RTree addr l')
                | None => None
                end
            end
        end
    end = Some T' ->
    rewrite_step from_ (RTree addr children) T'.
Proof.
  intros from_ addr children T' H.
  destruct (last_two_step children) as [l1 |] eqn:E1.
  { injection H as <-. exact (last_two_step_sound from_ addr children l1 E1). }
  destruct (lift_step children) as [l2 |] eqn:E2.
  { injection H as <-. exact (lift_step_sound from_ addr children l2 E2). }
  destruct (annotate_scan from_ [] children) as [l3 |] eqn:E3.
  { injection H as <-.
    exact (annotate_scan_sound from_ addr children [] l3 E3). }
  destruct (merge_scan [] children) as [l4 |] eqn:E4.
  { injection H as <-.
    exact (merge_scan_sound from_ addr children [] l4 E4). }
  discriminate.
Qed.

(** Soundness of the general-tree kernel: every kernel
    step is one [rewrite_step].  The two-leaf tree hits
    the special arm ([kfull_leaf_sound]); every other
    shape reduces, by conversion, to the general arm. *)
Lemma kfull_step_sound :
  forall from_ T T',
    kfull_step from_ T = Some T' ->
    rewrite_step from_ T T'.
Proof.
  intros from_ T T' H.
  destruct T as [t | c | addr children]; try discriminate.
  destruct children as [| x [| y [| z rest]]].
  - apply (kfull_general_sound from_ addr). exact H.
  - destruct x as [t1 | c1 | a1 ch1];
      (apply (kfull_general_sound from_ addr); exact H).
  - destruct x as [t1 | c1 | a1 ch1];
      destruct y as [t2 | c2 | a2 ch2];
      try (apply (kfull_general_sound from_ addr); exact H).
    (* leaf-leaf special arm *)
    cbn in H.
    destruct (try_combine_leaves_full t1 t2) as [c |] eqn:Hc;
      [| discriminate].
    injection H as <-.
    exact (kfull_leaf_sound from_ t1 t2 c addr Hc).
  - (* >= 3 children: expose x, y so the [RLeaf;RLeaf]
       pattern's length mismatch reduces, then general arm *)
    destruct x as [t1 | c1 | a1 ch1];
      destruct y as [t2 | c2 | a2 ch2];
      (apply (kfull_general_sound from_ addr); exact H).
Qed.

(* ------------------------------------------------------------
   Section 27: O0 completeness -- kernel None means no redex

   Converse split lemmas, premise-to-boolean transfers, and
   scan completeness; assembled into [kfull_O0].
   ------------------------------------------------------------ *)

(** Converse of [split_last_two_spec]. *)
Lemma split_last_two_complete :
  forall sib a b,
    split_last_two (sib ++ [a; b]) = Some (sib, a, b).
Proof.
  intros sib a b.
  unfold split_last_two.
  rewrite rev_app_distr. simpl.
  rewrite rev_involutive. reflexivity.
Qed.

(** Converse of [split_last_spec]. *)
Lemma split_last_complete :
  forall sib a,
    split_last (sib ++ [a]) = Some (sib, a).
Proof.
  intros sib a.
  unfold split_last.
  rewrite rev_app_distr. simpl.
  rewrite rev_involutive. reflexivity.
Qed.

(** A [CT_node] carries at least two transfers. *)
Lemma ct_node_transfers_two :
  forall o d m ti to_ ft lbl cl cr,
    exists t1 t2 rest,
      chain_transfers (CT_node o d m ti to_ ft lbl cl cr) =
      t1 :: t2 :: rest.
Proof.
  intros o d m ti to_ ft lbl cl cr. simpl.
  destruct (chain_transfers cl) as [| x xs] eqn:Hl.
  { exfalso. exact (chain_transfers_nonempty cl Hl). }
  destruct xs as [| y ys].
  - destruct (chain_transfers cr) as [| z zs] eqn:Hr.
    { exfalso. exact (chain_transfers_nonempty cr Hr). }
    exists x, z, zs. reflexivity.
  - exists x, y, (ys ++ chain_transfers cr). reflexivity.
Qed.

(** A labeled chain (Cycle / Arbitrage / burn / mint) is a
    [CT_node]; hence any [c'] whose label is [Arbitrage] or
    [Cycle] carries at least two transfers.  This is why
    R14/R15 cannot fire on a bare [CT_transfer]: its single
    transfer cannot be matched by any witness [c']. *)
Lemma labeled_chain_is_node :
  forall c, is_labeled (ch_label c) = true -> is_ct_node c = true.
Proof.
  intros [t | o d m ti to_ ft lbl cl cr] H;
    [discriminate | reflexivity].
Qed.

(** Boolean flatness from the [RS_lift] premise. *)
Lemma Forall_flat_childb :
  forall l,
    Forall (fun c => match c with
                     | RLeaf _ | RChain _ => True
                     | RTree _ _ => False
                     end) l ->
    forallb flat_childb l = true.
Proof.
  induction l as [| x rest IH]; intros H; [reflexivity |].
  inversion H; subst. simpl.
  apply andb_true_iff. split.
  - destruct x; simpl; solve [reflexivity | contradiction].
  - apply IH. assumption.
Qed.

(** Decidable-guard introduction helpers. *)
Lemma dec_addr_true :
  forall a b, a = b ->
    (if address_eq_dec a b then true else false) = true.
Proof.
  intros a b H. destruct (address_eq_dec a b);
    [reflexivity | contradiction].
Qed.

Lemma dec_addr_false :
  forall a b, a <> b ->
    (if address_eq_dec a b then true else false) = false.
Proof.
  intros a b H. destruct (address_eq_dec a b);
    [contradiction | reflexivity].
Qed.

Lemma dec_tok_true :
  forall a b, a = b ->
    (if token_eq_dec a b then true else false) = true.
Proof.
  intros a b H. destruct (token_eq_dec a b);
    [reflexivity | contradiction].
Qed.

Lemma dec_tok_false :
  forall a b, a <> b ->
    (if token_eq_dec a b then true else false) = false.
Proof.
  intros a b H. destruct (token_eq_dec a b);
    [contradiction | reflexivity].
Qed.

(** R14's premises make the chain annotatable.  The
    [is_ct_node] conjunct holds because the witness [c']
    carries the [Arbitrage] label, hence is a [CT_node]
    with at least two transfers, and [c] has the same
    transfer list. *)
Lemma annotatableb_R14 :
  forall from_ c c',
    ch_origin c = ch_destination c ->
    token_equiv (ch_token_in c) (ch_token_out c) = true ->
    is_labeled (ch_label c) = false ->
    ch_label c' = Arbitrage ->
    chain_transfers c' = chain_transfers c ->
    wrap_unwrap c = false ->
    annotatableb from_ c = true.
Proof.
  intros from_ c c' Hcd Hequiv Hunlab Hlbl' Htr Hwrap.
  assert (Hnode : is_ct_node c = true).
  { destruct c' as [t' | o d m ti to_ ft lbl cl cr];
      [simpl in Hlbl'; discriminate |].
    destruct (ct_node_transfers_two o d m ti to_ ft lbl cl cr)
      as (t1 & t2 & rest & Heq).
    rewrite Heq in Htr.
    destruct c as [t | ? ? ? ? ? ? ? ? ?];
      [simpl in Htr; discriminate | reflexivity]. }
  unfold annotatableb.
  rewrite Hnode, Hunlab, (dec_addr_true _ _ Hcd),
    Hequiv, Hwrap.
  simpl. rewrite orb_true_r. reflexivity.
Qed.

(** R15's premises make the chain annotatable. *)
Lemma annotatableb_R15 :
  forall from_ c c',
    ch_origin c = ch_destination c ->
    is_labeled (ch_label c) = false ->
    ch_label c' = Cycle ->
    chain_transfers c' = chain_transfers c ->
    address_in_chain from_ c = true ->
    annotatableb from_ c = true.
Proof.
  intros from_ c c' Hcd Hunlab Hlbl' Htr Hin.
  assert (Hnode : is_ct_node c = true).
  { destruct c' as [t' | o d m ti to_ ft lbl cl cr];
      [simpl in Hlbl'; discriminate |].
    destruct (ct_node_transfers_two o d m ti to_ ft lbl cl cr)
      as (t1 & t2 & rest & Heq).
    rewrite Heq in Htr.
    destruct c as [t | ? ? ? ? ? ? ? ? ?];
      [simpl in Htr; discriminate | reflexivity]. }
  unfold annotatableb.
  rewrite Hnode, Hunlab, (dec_addr_true _ _ Hcd), Hin.
  reflexivity.
Qed.

(** The four merge rules' premises make the pair mergeable. *)
Lemma mergeable_R7 :
  forall c1 c2,
    ch_origin c1 = ch_origin c2 ->
    ch_destination c1 = ch_destination c2 ->
    ch_origin c1 <> ch_destination c1 ->
    ch_token_out c1 = ch_token_out c2 ->
    ch_token_mid c1 <> ch_token_mid c2 ->
    mergeable_fullb c1 c2 = true.
Proof.
  intros c1 c2 H1 H2 H3 H4 H5.
  unfold mergeable_fullb, r7b.
  rewrite (dec_addr_true _ _ H1), (dec_addr_true _ _ H2),
    (dec_addr_false _ _ H3), (dec_tok_true _ _ H4),
    (dec_tok_false _ _ H5).
  reflexivity.
Qed.

Lemma mergeable_R8 :
  forall c1 c2,
    ch_origin c1 = ch_origin c2 ->
    ch_destination c1 = ch_destination c2 ->
    ch_origin c1 = ch_destination c1 ->
    ((ch_token_in c1 = ch_token_in c2 /\
      ch_token_mid c1 = ch_token_mid c2 /\
      ch_token_out c1 = ch_token_out c2) \/
     bal_cont (ch_origin c1) c1 c2 = true) ->
    mergeable_fullb c1 c2 = true.
Proof.
  intros c1 c2 H1 H2 H3 H4.
  unfold mergeable_fullb, r8b.
  rewrite (dec_addr_true _ _ H1), (dec_addr_true _ _ H2),
    (dec_addr_true _ _ H3).
  destruct H4 as [[Ht1 [Htm Ht2]] | Hbc].
  - rewrite (dec_tok_true _ _ Ht1), (dec_tok_true _ _ Htm),
      (dec_tok_true _ _ Ht2).
    simpl. rewrite !orb_true_r. reflexivity.
  - rewrite Hbc. simpl. rewrite !orb_true_r. reflexivity.
Qed.

Lemma mergeable_R9 :
  forall c1 c2,
    ch_origin c1 = ch_destination c1 ->
    ch_origin c2 = ch_destination c2 ->
    ch_origin c1 = ch_origin c2 ->
    ch_token_in c1 = ch_token_in c2 ->
    ch_token_out c1 = ch_token_out c2 ->
    mergeable_fullb c1 c2 = true.
Proof.
  intros c1 c2 H1 H2 H3 H4 H5.
  unfold mergeable_fullb, r9b.
  rewrite (dec_addr_true _ _ H1), (dec_addr_true _ _ H2),
    (dec_addr_true _ _ H3), (dec_tok_true _ _ H4), (dec_tok_true _ _ H5).
  simpl. rewrite !orb_true_r. reflexivity.
Qed.

Lemma mergeable_R13 :
  forall c1 c2,
    ch_origin c1 = ch_origin c2 ->
    ch_destination c1 = ch_destination c2 ->
    ch_origin c1 <> ch_destination c1 ->
    ch_token_out c1 = ch_token_out c2 ->
    ch_token_mid c1 <> ch_token_mid c2 ->
    ch_token_in c1 = ch_token_in c2 ->
    mergeable_fullb c1 c2 = true.
Proof.
  intros c1 c2 H1 H2 H3 H4 H5 _.
  exact (mergeable_R7 c1 c2 H1 H2 H3 H4 H5).
Qed.

(** Scan-hit lemmas: an annotatable chain / mergeable pair
    anywhere in the list forces the scan to succeed. *)
Lemma annotate_scan_hit :
  forall from_ L c R prefix,
    annotatableb from_ c = true ->
    annotate_scan from_ prefix (L ++ RChain c :: R) <> None.
Proof.
  intros from_ L.
  induction L as [| x L' IH]; intros c R prefix Hann; simpl.
  - rewrite Hann. discriminate.
  - destruct x as [t | c0 | a ch].
    + apply IH. exact Hann.
    + destruct (annotatableb from_ c0).
      * discriminate.
      * apply IH. exact Hann.
    + apply IH. exact Hann.
Qed.

Lemma merge_scan_pair_hit :
  forall c1 M c2 R prefix before,
    mergeable_fullb c1 c2 = true ->
    merge_scan_pair c1 prefix before (M ++ RChain c2 :: R) <> None.
Proof.
  intros c1 M.
  induction M as [| x M' IH]; intros c2 R prefix before Hm; simpl.
  - rewrite Hm. discriminate.
  - destruct x as [t | c0 | a ch].
    + apply IH. exact Hm.
    + destruct (mergeable_fullb c1 c0).
      * discriminate.
      * apply IH. exact Hm.
    + apply IH. exact Hm.
Qed.

Lemma merge_scan_hit :
  forall L c1 M c2 R prefix,
    mergeable_fullb c1 c2 = true ->
    merge_scan prefix (L ++ RChain c1 :: M ++ RChain c2 :: R)
      <> None.
Proof.
  intros L.
  induction L as [| x L' IH]; intros c1 M c2 R prefix Hm; simpl.
  - destruct (merge_scan_pair c1 prefix []
                (M ++ RChain c2 :: R)) eqn:Hpair.
    + discriminate.
    + exfalso.
      exact (merge_scan_pair_hit c1 M c2 R prefix [] Hm Hpair).
  - destruct x as [t | c0 | a ch].
    + apply IH. exact Hm.
    + destruct (merge_scan_pair c0 prefix [] (L' ++ RChain c1 :: M ++ RChain c2 :: R)).
      * discriminate.
      * apply IH. exact Hm.
    + apply IH. exact Hm.
Qed.

(** Inverting a [None] cascade into per-branch [None]s. *)
Lemma cascade_None_inv :
  forall from_ addr children,
    match last_two_step children with
    | Some l' => Some (RTree addr l')
    | None =>
        match lift_step children with
        | Some l' => Some (RTree addr l')
        | None =>
            match annotate_scan from_ [] children with
            | Some l' => Some (RTree addr l')
            | None =>
                match merge_scan [] children with
                | Some l' => Some (RTree addr l')
                | None => None
                end
            end
        end
    end = None ->
    last_two_step children = None /\    lift_step children = None /\    annotate_scan from_ [] children = None /\    merge_scan [] children = None.
Proof.
  intros from_ addr children H.
  destruct (last_two_step children); [discriminate |].
  destruct (lift_step children); [discriminate |].
  destruct (annotate_scan from_ [] children); [discriminate |].
  destruct (merge_scan [] children); [discriminate |].
  auto.
Qed.

(** A [None] kernel answer yields [None] on every branch.
    On the two-leaf shape the four cascade branches are
    [None] by computation; on every other shape the special
    combiner clause is vacuous. *)
Lemma kfull_None_general :
  forall from_ addr children,
    kfull_step from_ (RTree addr children) = None ->
    (forall t1 t2, children = [RLeaf t1; RLeaf t2] ->
                   try_combine_leaves_full t1 t2 = None) /\    last_two_step children = None /\    lift_step children = None /\    annotate_scan from_ [] children = None /\    merge_scan [] children = None.
Proof.
  intros from_ addr children H.
  destruct children as [| x [| y [| z rest]]].
  - split; [intros ? ? Heq; discriminate |].
    exact (cascade_None_inv from_ addr [] H).
  - split; [intros ? ? Heq; discriminate |].
    destruct x as [t1 | c1 | a1 ch1];
      (apply (cascade_None_inv from_ addr); exact H).
  - destruct x as [t1 | c1 | a1 ch1];
      destruct y as [t2 | c2 | a2 ch2];
      try (split;
           [intros ? ? Heq; injection Heq; intros; subst;
            discriminate
           | apply (cascade_None_inv from_ addr); exact H]).
    (* leaf-leaf *)
    cbn in H.
    destruct (try_combine_leaves_full t1 t2) eqn:Hc;
      [discriminate |].
    split.
    + intros t1' t2' Heq.
      injection Heq as <- <-. exact Hc.
    + repeat split; reflexivity.
  - split; [intros ? ? Heq; discriminate |].
    destruct x as [t1 | c1 | a1 ch1];
      destruct y as [t2 | c2 | a2 ch2];
      (apply (cascade_None_inv from_ addr); exact H).
Qed.

(** Guard-level completeness of the last-two and lift
    branches, proved goal-side where destructs reduce. *)
Lemma last_two_step_leafchain_some :
  forall sib t c,
    (tr_dest t = ch_origin c \/ ch_destination c = tr_source t) ->
    last_two_step (sib ++ [RLeaf t; RChain c]) <> None.
Proof.
  intros sib t c Hadj.
  unfold last_two_step.
  rewrite split_last_two_complete. cbn.
  destruct (address_eq_dec (tr_dest t) (ch_origin c)).
  - discriminate.
  - destruct Hadj as [Hp | Ha]; [contradiction |].
    destruct (address_eq_dec (ch_destination c) (tr_source t)).
    + discriminate.
    + contradiction.
Qed.

Lemma last_two_step_chainseq_some :
  forall sib c1 c2,
    ch_destination c1 = ch_origin c2 ->
    (ch_token_out c1 = ch_token_in c2 \/
     bal_cont (ch_destination c1) c1 c2 = true) ->
    last_two_step (sib ++ [RChain c1; RChain c2]) <> None.
Proof.
  intros sib c1 c2 Hadj Hor.
  unfold last_two_step.
  rewrite split_last_two_complete. cbn.
  destruct (address_eq_dec (ch_destination c1) (ch_origin c2));
    [| contradiction].
  destruct (token_eq_dec (ch_token_out c1) (ch_token_in c2)).
  - cbn. discriminate.
  - destruct Hor as [Ht | Hb]; [contradiction |].
    rewrite Hb. rewrite orb_true_r. discriminate.
Qed.

Lemma lift_step_some :
  forall sib a inner,
    Forall (fun c => match c with
                     | RLeaf _ | RChain _ => True
                     | RTree _ _ => False
                     end) inner ->
    lift_ok_b inner = true ->
    lift_step (sib ++ [RTree a inner]) <> None.
Proof.
  intros sib a inner HF Hok.
  unfold lift_step.
  rewrite split_last_complete.
  assert (Hc : forallb flat_childb inner && lift_ok_b inner = true)
    by (apply andb_true_iff; split;
        [ apply (Forall_flat_childb _ HF) | exact Hok ]).
  rewrite Hc. discriminate.
Qed.

(** O0 (redex-completeness of the root kernel) for FLAT
    trees: when [kfull_step] answers [None] on a tree
    whose children are all leaves or chains, no
    [rewrite_step] fires.  With [RS_under] the relation
    reaches nested subtrees, so on an arbitrary tree
    completeness needs a kernel that recurses into
    children; here we cover the flat case, where the
    [RS_under] congruence is vacuous (a leaf or chain
    child cannot step).  The recursive kernel that lifts
    this to arbitrary trees is [kfull_deep] with
    [kfull_deep_O0] / [kfull_deep_nf_iff]
    (Section 16d below). *)
Lemma kfull_O0 :
  forall from_ addr children,
    Forall (fun c => match c with
                     | RLeaf _ | RChain _ => True
                     | RTree _ _ => False
                     end) children ->
    kfull_step from_ (RTree addr children) = None ->
    forall T', ~ rewrite_step from_ (RTree addr children) T'.
Proof.
  intros from_ addr children Hflat Hnone T' Hstep.
  destruct (kfull_None_general from_ addr children Hnone)
    as (Hcomb & HL2 & HLF & HAS & HMS).
  inversion Hstep; subst.
  - (* R1 *)
    destruct (kfull_leaf_complete from_ addr _ _ _ Hstep) as [c0 Hc0].
    rewrite (Hcomb _ _ eq_refl) in Hc0. discriminate.
  - (* R2 *)
    destruct (kfull_leaf_complete from_ addr _ _ _ Hstep) as [c0 Hc0].
    rewrite (Hcomb _ _ eq_refl) in Hc0. discriminate.
  - (* R3 *)
    destruct (kfull_leaf_complete from_ addr _ _ _ Hstep) as [c0 Hc0].
    rewrite (Hcomb _ _ eq_refl) in Hc0. discriminate.
  - (* R4 *)
    destruct (kfull_leaf_complete from_ addr _ _ _ Hstep) as [c0 Hc0].
    rewrite (Hcomb _ _ eq_refl) in Hc0. discriminate.
  - (* R5 *)
    destruct (kfull_leaf_complete from_ addr _ _ _ Hstep) as [c0 Hc0].
    rewrite (Hcomb _ _ eq_refl) in Hc0. discriminate.
  - (* R6 *)
    match goal with HD : _ \/ _ |- _ => destruct HD as [(Hp & _) | (Ha & _)] end;
    ( eapply last_two_step_leafchain_some;
      [ solve [ left; eassumption | right; eassumption ]
      | exact HL2 ] ).
  - (* R12 *)
    match goal with HD : _ \/ _ |- _ => destruct HD as [(Hp & _) | (Ha & _)] end;
    ( eapply last_two_step_leafchain_some;
      [ solve [ left; eassumption | right; eassumption ]
      | exact HL2 ] ).
  - (* R10 *)
    match goal with HD : _ \/ _ |- _ => destruct HD as [Htok | Hbc] end;
    match goal with HA : ch_destination ?a = ch_origin ?b |- _ =>
      ( eapply (last_two_step_chainseq_some _ a b);
        [ exact HA
        | solve [ left; eassumption | right; eassumption ]
        | exact HL2 ] )
    end.
  - (* R11 *)
    destruct (kfull_leaf_complete from_ addr _ _ _ Hstep) as [c0 Hc0].
    rewrite (Hcomb _ _ eq_refl) in Hc0. discriminate.
  - (* lift *)
    match goal with
    | HF : Forall _ _, HG : lift_children_ok _ |- _ =>
        exact (lift_step_some _ _ _ HF HG HLF)
    end.
  - (* R7 *)
    refine (merge_scan_hit _ _ _ _ _ [] _ HMS).
    eapply mergeable_R7; eassumption.
  - (* R8 *)
    refine (merge_scan_hit _ _ _ _ _ [] _ HMS).
    eapply mergeable_R8; eassumption.
  - (* R9 *)
    refine (merge_scan_hit _ _ _ _ _ [] _ HMS).
    eapply mergeable_R9; eassumption.
  - (* R13 *)
    refine (merge_scan_hit _ _ _ _ _ [] _ HMS).
    eapply mergeable_R13; eassumption.
  - (* R14 *)
    refine (annotate_scan_hit from_ _ _ _ [] _ HAS).
    eapply annotatableb_R14; eassumption.
  - (* R15 *)
    refine (annotate_scan_hit from_ _ _ _ [] _ HAS).
    eapply annotatableb_R15; eassumption.
  - (* RS_under (congruence): vacuous on a flat tree *)
    match goal with Hsub : rewrite_step _ ?T _ |- _ =>
      is_var T; apply rewrite_step_lhs_tree in Hsub;
      destruct Hsub as [aa [chh HT]]; subst
    end.
    rewrite Forall_forall in Hflat.
    match goal with
    | HinT : In (RTree aa chh) _ |- _ => apply Hflat in HinT; exact HinT
    | |- _ => apply (Hflat (RTree aa chh));
              apply in_or_app; right; left; reflexivity
    end.
Qed.

(* ------------------------------------------------------------
   Section 28: Deep kernel (Regime 3, nested trees)

   With [RS_under] the relation reaches nested subtrees, so
   redex-completeness needs a kernel that recurses into
   children.  [kfull_deep] tries the root kernel first, then
   rewrites the first child that steps.  Fuel-driven on
   [rcft_size] (same engineering as [kappa_fuel]): the child
   scan [scan_children] stays a first-order function, and
   fuel sufficiency is discharged once in
   [kfull_deep_fuel_ge].  Headline: [kfull_deep_nf_iff] --
   deep-kernel normal forms are exactly the R-normal forms.
   ------------------------------------------------------------ *)

(** Structural size of a reduced CFT; the deep kernel's
    fuel. *)
Fixpoint rcft_size (T : reduced_cft) : nat :=
  match T with
  | RLeaf _ => 1
  | RChain _ => 1
  | RTree _ ch => S (list_sum (map rcft_size ch))
  end.

Lemma rcft_size_in_le :
  forall x ch,
    In x ch -> rcft_size x <= list_sum (map rcft_size ch).
Proof.
  intros x ch. induction ch as [| y rest IH]; intros Hin.
  - destruct Hin.
  - simpl in *. destruct Hin as [<- | Hin].
    + lia.
    + specialize (IH Hin). lia.
Qed.

Lemma rcft_size_child_lt :
  forall a ch x,
    In x ch -> rcft_size x < rcft_size (RTree a ch).
Proof.
  intros a ch x Hin. simpl.
  pose proof (rcft_size_in_le x ch Hin). lia.
Qed.

(** One-position child rewriter: [Some] iff some child steps
    under [f]; rewrites the FIRST stepping child, keeping the
    others.  First-order in [f] so it can be reasoned about
    independently of the kernel's fuel. *)
Fixpoint scan_children
    (f : reduced_cft -> option reduced_cft)
    (l : list reduced_cft) : option (list reduced_cft) :=
  match l with
  | [] => None
  | x :: rest =>
      match f x with
      | Some x' => Some (x' :: rest)
      | None =>
          match scan_children f rest with
          | Some rest' => Some (x :: rest')
          | None => None
          end
      end
  end.

Lemma scan_children_some :
  forall f l l',
    scan_children f l = Some l' ->
    exists L x x' R,
      l = L ++ [x] ++ R /\ l' = L ++ [x'] ++ R /\ f x = Some x'.
Proof.
  intros f l. induction l as [| y rest IH]; intros l' H; simpl in H.
  - discriminate.
  - destruct (f y) as [y' |] eqn:Hy.
    + injection H as <-.
      exists [], y, y', rest.
      split; [reflexivity | split; [reflexivity | exact Hy]].
    + destruct (scan_children f rest) as [rest' |] eqn:Hs;
        [| discriminate].
      injection H as <-.
      destruct (IH _ eq_refl) as (L & x & x' & R & Hl & Hl' & Hx).
      subst rest rest'.
      exists (y :: L), x, x', R.
      split; [reflexivity | split; [reflexivity | exact Hx]].
Qed.

Lemma scan_children_none :
  forall f l,
    scan_children f l = None ->
    forall x, In x l -> f x = None.
Proof.
  intros f l. induction l as [| y rest IH]; intros H x Hin.
  - destruct Hin.
  - simpl in H.
    destruct (f y) eqn:Hy; [discriminate |].
    destruct (scan_children f rest) eqn:Hs; [discriminate |].
    destruct Hin as [<- | Hin].
    + exact Hy.
    + exact (IH eq_refl x Hin).
Qed.

Lemma scan_children_ext :
  forall f g l,
    (forall x, In x l -> f x = g x) ->
    scan_children f l = scan_children g l.
Proof.
  intros f g l. induction l as [| x rest IH]; intros Hfg;
    [reflexivity |].
  simpl. rewrite (Hfg x (or_introl eq_refl)).
  rewrite IH by (intros y Hy; apply Hfg; right; exact Hy).
  reflexivity.
Qed.

(** Fuel-driven deep kernel: root kernel first, else rewrite
    the first child that steps.  A [0]-fuel [None] is
    meaningless; sufficiency is discharged by
    [kfull_deep_fuel_ge] at the [rcft_size] wrapper. *)
Fixpoint kfull_deep_fuel (n : nat) (from_ : address)
    (T : reduced_cft) : option reduced_cft :=
  match n with
  | 0 => None
  | S n' =>
      match T with
      | RTree addr children =>
          match kfull_step from_ (RTree addr children) with
          | Some T' => Some T'
          | None =>
              match scan_children (kfull_deep_fuel n' from_)
                      children with
              | Some children' => Some (RTree addr children')
              | None => None
              end
          end
      | _ => None
      end
  end.

Definition kfull_deep (from_ : address) (T : reduced_cft)
    : option reduced_cft :=
  kfull_deep_fuel (rcft_size T) from_ T.

(** Fuel irrelevance above the size (cf. [kappa_fuel_ge]). *)
Lemma kfull_deep_fuel_ge :
  forall n m from_ T,
    rcft_size T <= n -> rcft_size T <= m ->
    kfull_deep_fuel n from_ T = kfull_deep_fuel m from_ T.
Proof.
  induction n as [| n' IHn]; intros m from_ T Hn Hm.
  - destruct T; simpl in Hn; lia.
  - destruct m as [| m']; [destruct T; simpl in Hm; lia |].
    destruct T as [t | c | addr ch]; [reflexivity | reflexivity |].
    cbn [kfull_deep_fuel].
    destruct (kfull_step from_ (RTree addr ch)); [reflexivity |].
    rewrite (scan_children_ext (kfull_deep_fuel n' from_)
               (kfull_deep_fuel m' from_) ch); [reflexivity |].
    intros x Hx.
    pose proof (rcft_size_child_lt addr ch x Hx) as Hlt.
    apply IHn; lia.
Qed.

(** Soundness at any fuel: a [Some] answer is one R-step
    (root via [kfull_step_sound]; child via [RS_under]). *)
Lemma kfull_deep_fuel_sound :
  forall n from_ T T',
    kfull_deep_fuel n from_ T = Some T' ->
    rewrite_step from_ T T'.
Proof.
  induction n as [| n' IHn]; intros from_ T T' H; [discriminate |].
  destruct T as [t | c | addr ch]; try discriminate.
  cbn [kfull_deep_fuel] in H.
  destruct (kfull_step from_ (RTree addr ch)) as [T0 |] eqn:Hroot.
  - injection H as <-. apply kfull_step_sound. exact Hroot.
  - destruct (scan_children (kfull_deep_fuel n' from_) ch)
      as [ch' |] eqn:Hs; [| discriminate].
    injection H as <-.
    destruct (scan_children_some _ _ _ Hs)
      as (L & x & x' & R & Hl & Hl' & Hx).
    subst ch ch'.
    apply RS_under. exact (IHn from_ x x' Hx).
Qed.

Lemma kfull_deep_sound :
  forall from_ T T',
    kfull_deep from_ T = Some T' ->
    rewrite_step from_ T T'.
Proof.
  intros from_ T T' H. exact (kfull_deep_fuel_sound _ _ _ _ H).
Qed.

(** A deep [None] pins the root kernel to [None]... *)
Lemma kfull_deep_none_root :
  forall from_ addr ch,
    kfull_deep from_ (RTree addr ch) = None ->
    kfull_step from_ (RTree addr ch) = None.
Proof.
  intros from_ addr ch H.
  unfold kfull_deep in H. cbn [rcft_size kfull_deep_fuel] in H.
  destruct (kfull_step from_ (RTree addr ch));
    [discriminate | reflexivity].
Qed.

(** ...and every child to a deep [None]. *)
Lemma kfull_deep_none_children :
  forall from_ addr ch,
    kfull_deep from_ (RTree addr ch) = None ->
    forall x, In x ch -> kfull_deep from_ x = None.
Proof.
  intros from_ addr ch H x Hin.
  unfold kfull_deep in *. cbn [rcft_size kfull_deep_fuel] in H.
  destruct (kfull_step from_ (RTree addr ch)); [discriminate |].
  destruct (scan_children
              (kfull_deep_fuel (list_sum (map rcft_size ch)) from_)
              ch) eqn:Hs; [discriminate |].
  rewrite (kfull_deep_fuel_ge (rcft_size x)
             (list_sum (map rcft_size ch)) from_ x).
  - exact (scan_children_none _ _ Hs x Hin).
  - lia.
  - exact (rcft_size_in_le x ch Hin).
Qed.

(** O0 for the deep kernel, general trees: a deep [None]
    means no R-redex anywhere, root or nested.  Induction on
    the step; the sixteen root constructors contradict the
    root kernel's [None] exactly as in the flat [kfull_O0]
    (leaf-pair cases rebuild their step and use
    [kfull_leaf_complete]); [RS_under] recurses via
    [kfull_deep_none_children]. *)
Lemma kfull_deep_O0_aux :
  forall from_ T T',
    rewrite_step from_ T T' ->
    kfull_deep from_ T = None ->
    False.
Proof.
  intros from_ T T' Hstep.
  induction Hstep; intros Hnone.
  - (* R1 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (Hcomb & _ & _ & _ & _).
    assert (Hs : rewrite_step from_
                   (RTree addr [RLeaf t1; RLeaf t2])
                   (RTree addr [RChain c]))
      by (eapply RS_swap_chain; eassumption).
    destruct (kfull_leaf_complete from_ addr _ _ _ Hs) as [c0 Hc0].
    rewrite (Hcomb _ _ eq_refl) in Hc0. discriminate.
  - (* R2 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (Hcomb & _ & _ & _ & _).
    assert (Hs : rewrite_step from_
                   (RTree addr [RLeaf t_burn; RLeaf t])
                   (RTree addr [RChain c]))
      by (eapply RS_burn_chain; eassumption).
    destruct (kfull_leaf_complete from_ addr _ _ _ Hs) as [c0 Hc0].
    rewrite (Hcomb _ _ eq_refl) in Hc0. discriminate.
  - (* R3 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (Hcomb & _ & _ & _ & _).
    assert (Hs : rewrite_step from_
                   (RTree addr [RLeaf t; RLeaf t_mint])
                   (RTree addr [RChain c]))
      by (eapply RS_mint_chain; eassumption).
    destruct (kfull_leaf_complete from_ addr _ _ _ Hs) as [c0 Hc0].
    rewrite (Hcomb _ _ eq_refl) in Hc0. discriminate.
  - (* R4 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (Hcomb & _ & _ & _ & _).
    assert (Hs : rewrite_step from_
                   (RTree addr [RLeaf t1; RLeaf t2])
                   (RTree addr [RChain c]))
      by (eapply RS_pool_cycle; eassumption).
    destruct (kfull_leaf_complete from_ addr _ _ _ Hs) as [c0 Hc0].
    rewrite (Hcomb _ _ eq_refl) in Hc0. discriminate.
  - (* R5 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (Hcomb & _ & _ & _ & _).
    assert (Hs : rewrite_step from_
                   (RTree addr [RLeaf t1; RLeaf t2])
                   (RTree addr [RChain c]))
      by (eapply RS_router_chain; eassumption).
    destruct (kfull_leaf_complete from_ addr _ _ _ Hs) as [c0 Hc0].
    rewrite (Hcomb _ _ eq_refl) in Hc0. discriminate.
  - (* R6 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (_ & HL2 & _ & _ & _).
    match goal with HD : _ \/ _ |- _ =>
      destruct HD as [(Hp & _) | (Ha & _)] end;
    ( eapply last_two_step_leafchain_some;
      [ solve [ left; eassumption | right; eassumption ]
      | exact HL2 ] ).
  - (* R12 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (_ & HL2 & _ & _ & _).
    match goal with HD : _ \/ _ |- _ =>
      destruct HD as [(Hp & _) | (Ha & _)] end;
    ( eapply last_two_step_leafchain_some;
      [ solve [ left; eassumption | right; eassumption ]
      | exact HL2 ] ).
  - (* R10 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (_ & HL2 & _ & _ & _).
    match goal with HD : _ \/ _ |- _ =>
      destruct HD as [Htok | Hbc] end;
    match goal with HA : ch_destination ?a = ch_origin ?b |- _ =>
      ( eapply (last_two_step_chainseq_some _ a b);
        [ exact HA
        | solve [ left; eassumption | right; eassumption ]
        | exact HL2 ] )
    end.
  - (* R11 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (Hcomb & _ & _ & _ & _).
    assert (Hs : rewrite_step from_
                   (RTree addr [RLeaf t1; RLeaf t2])
                   (RTree addr [RChain c]))
      by (eapply RS_same_token_chain; eassumption).
    destruct (kfull_leaf_complete from_ addr _ _ _ Hs) as [c0 Hc0].
    rewrite (Hcomb _ _ eq_refl) in Hc0. discriminate.
  - (* lift *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (_ & _ & HLF & _ & _).
    match goal with HF : Forall _ _, HG : lift_children_ok _ |- _ =>
      exact (lift_step_some _ _ _ HF HG HLF) end.
  - (* R7 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (_ & _ & _ & _ & HMS).
    refine (merge_scan_hit _ _ _ _ _ [] _ HMS).
    eapply mergeable_R7; eassumption.
  - (* R8 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (_ & _ & _ & _ & HMS).
    refine (merge_scan_hit _ _ _ _ _ [] _ HMS).
    eapply mergeable_R8; eassumption.
  - (* R9 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (_ & _ & _ & _ & HMS).
    refine (merge_scan_hit _ _ _ _ _ [] _ HMS).
    eapply mergeable_R9; eassumption.
  - (* R13 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (_ & _ & _ & _ & HMS).
    refine (merge_scan_hit _ _ _ _ _ [] _ HMS).
    eapply mergeable_R13; eassumption.
  - (* R14 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (_ & _ & _ & HAS & _).
    refine (annotate_scan_hit from_ _ _ _ [] _ HAS).
    eapply annotatableb_R14; eassumption.
  - (* R15 *)
    apply kfull_deep_none_root in Hnone.
    destruct (kfull_None_general _ _ _ Hnone)
      as (_ & _ & _ & HAS & _).
    refine (annotate_scan_hit from_ _ _ _ [] _ HAS).
    eapply annotatableb_R15; eassumption.
  - (* RS_under *)
    apply IHHstep.
    eapply kfull_deep_none_children; [exact Hnone |].
    apply in_app_iff. right. simpl. left. reflexivity.
Qed.

(** O0 for the deep kernel (general trees). *)
Lemma kfull_deep_O0 :
  forall from_ T,
    kfull_deep from_ T = None ->
    forall T', ~ rewrite_step from_ T T'.
Proof.
  intros from_ T Hnone T' Hstep.
  exact (kfull_deep_O0_aux from_ T T' Hstep Hnone).
Qed.

(** Headline: deep-kernel normal forms are exactly the
    R-normal forms. *)
Corollary kfull_deep_nf_iff :
  forall from_ T,
    kfull_deep from_ T = None
    <-> (forall T', ~ rewrite_step from_ T T').
Proof.
  intros from_ T. split.
  - intros Hnone T' Hstep.
    exact (kfull_deep_O0_aux from_ T T' Hstep Hnone).
  - intros Hnf.
    destruct (kfull_deep from_ T) as [T' |] eqn:Hd; [| reflexivity].
    exfalso. exact (Hnf T' (kfull_deep_sound from_ T T' Hd)).
Qed.

(* ============================================================
   Section 29: Canonical association map kappa (O1)

   The free relation R is not confluent under syntactic
   equality: three pairwise-mergeable parallel chains merge
   into distinct tree shapes depending on association order,
   with identical leaf multisets and delta maps.  [kappa]
   canonicalizes: on every maximal cluster of nested
   [Merging] chain nodes it flattens to the operand list,
   recursively normalizes, sorts by the trace order
   (Property 1), and rebuilds a left comb; identity
   elsewhere.  O1: kappa is computable, idempotent, and
   preserves the transfer multiset and the delta map.
   ============================================================ *)

(** Trace position of a transfer (Property 1 / DSE).  A
    deployment realizer, same status as [is_burn];
    [is_trace_key_wf] (injectivity) is the obligation that
    makes the induced operand order strict. *)
Parameter trace_key : transfer -> nat.

Definition is_trace_key_wf : Prop :=
  forall t1 t2, trace_key t1 = trace_key t2 -> t1 = t2.

Definition op_key (c : chain_tree) : nat :=
  trace_key (ch_first_transfer c).

(** Canonical trace signature of an operand: the sorted
    list of the trace positions of all its transfers.
    Property 1 (sigma) thus induces a total order on
    operands, used to break ties on the first-leaf key.
    Since [trace_key] is injective ([is_trace_key_wf]),
    two operands share a signature only if they carry the
    same transfer multiset; the transfer-disjoint arms of
    a merge cluster therefore have distinct signatures,
    which is the strictness (antisymmetry) O2 needs. *)
Fixpoint nat_insert (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | y :: ys => if Nat.leb x y then x :: l else y :: nat_insert x ys
  end.

Fixpoint nat_sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => nat_insert x (nat_sort xs)
  end.

Definition op_sig (c : chain_tree) : list nat :=
  nat_sort (map trace_key (chain_transfers c)).

Fixpoint lex_le (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if Nat.ltb x y then true
      else if Nat.ltb y x then false
      else lex_le xs ys
  end.

Lemma lex_le_total :
  forall l1 l2, lex_le l1 l2 = false -> lex_le l2 l1 = true.
Proof.
  induction l1 as [| x xs IH]; intros [| y ys] H; simpl in *;
    try discriminate; try reflexivity.
  destruct (Nat.ltb x y) eqn:Hxy; [discriminate |].
  destruct (Nat.ltb y x) eqn:Hyx.
  - reflexivity.
  - apply Nat.ltb_ge in Hxy. apply Nat.ltb_ge in Hyx.
    assert (Hxy_eq : x = y) by lia. subst y.
    apply IH. exact H.
Qed.

(** Sort operands by first-leaf trace position, breaking
    ties with the full trace signature ([op_sig]). *)
Definition op_le (c1 c2 : chain_tree) : bool :=
  if Nat.eqb (op_key c1) (op_key c2)
  then lex_le (op_sig c1) (op_sig c2)
  else Nat.leb (op_key c1) (op_key c2).

Fixpoint ct_size (c : chain_tree) : nat :=
  match c with
  | CT_transfer _ => 1
  | CT_node _ _ _ _ _ _ _ l r => S (ct_size l + ct_size r)
  end.

(** Operands of a maximal [Merging] cluster: descend
    through [Merging] nodes, collect every non-[Merging]
    subtree. *)
Fixpoint merge_operands (c : chain_tree) : list chain_tree :=
  match c with
  | CT_node _ _ _ _ _ _ Merging l r =>
      merge_operands l ++ merge_operands r
  | _ => [c]
  end.

Fixpoint op_insert (c : chain_tree) (l : list chain_tree)
    : list chain_tree :=
  match l with
  | [] => [c]
  | x :: xs => if op_le c x then c :: l else x :: op_insert c xs
  end.

Fixpoint op_sort (l : list chain_tree) : list chain_tree :=
  match l with
  | [] => []
  | x :: xs => op_insert x (op_sort xs)
  end.

(** Canonical [Merging] node: every summary field
    ([ch_origin], [ch_destination], [ch_token_in],
    [ch_token_out], [ch_first_transfer]) is recomputed from
    [least] -- the least-[op_key] operand, i.e. the head of
    the sorted operand list -- never inherited from the fold
    accumulator.  Unlike the kernel's [merge_chain] (which
    copies its first argument's summary), this makes the
    node a pure function of the sorted operand list, so
    [kappa] applied to [merge c1 c2] and [merge c2 c1]
    recomputes identical fields from the identical sorted
    set. *)
Definition canonical_merge_node (least : chain_tree)
    (acc x : chain_tree) : chain_tree :=
  CT_node (ch_origin least) (ch_destination least) []
          (ch_token_in least) (ch_token_out least)
          (ch_first_transfer least) Merging acc x.

(** Rebuild an operand list as a left comb of canonical
    [Merging] nodes, all stamped from the head (least)
    operand; [dflt] covers the (unreachable) empty case. *)
Definition rebuild_comb (dflt : chain_tree)
    (l : list chain_tree) : chain_tree :=
  match l with
  | [] => dflt
  | first :: rest =>
      fold_left (canonical_merge_node first) rest first
  end.

(** Fuel-driven canonicalizer on chain trees; fuel is the
    structural size, sufficiency discharged in [kappa_ct]. *)
Fixpoint kappa_fuel (n : nat) (c : chain_tree) : chain_tree :=
  match n with
  | 0 => c
  | S n' =>
      match c with
      | CT_transfer _ => c
      | CT_node o d m ti to_ ft Merging l r =>
          let ops :=
            merge_operands (CT_node o d m ti to_ ft Merging l r) in
          rebuild_comb c (op_sort (map (kappa_fuel n') ops))
      | CT_node o d m ti to_ ft lbl l r =>
          CT_node o d m ti to_ ft lbl
            (kappa_fuel n' l) (kappa_fuel n' r)
      end
  end.

Definition kappa_ct (c : chain_tree) : chain_tree :=
  kappa_fuel (ct_size c) c.

(** --- Sibling merge saturation (AC-completeness across siblings) ---

    [kappa_ct] already canonicalizes a single chain's [Merging] tree
    (flatten [merge_operands], [op_sort], [rebuild_comb]).  The RTree
    clause of [kappa] must do the same ONE level up, across sibling
    [RChain]s.  We take the maximally-reduced canonical form: flatten
    EVERY sibling chain to its leaf operands ([merge_operands]),
    [op_sort] the pooled operand multiset by trace signature, and emit
    them as sorted [RChain]s before the untouched non-chain children.

    Because every merge rule (R7/R8/R9/R13) requires its two operands to
    share origin and destination, and a merged node inherits that pair,
    the only valid sibling groupings on a REACHABLE tree are within one
    (origin,destination) key; distinct-key operands have disjoint
    trace-key signatures.  So two reachable trees agree here iff they
    carry the same operand multiset -- exactly the AC-merge equivalence,
    now without any [merge_lr] left-to-right side condition: the two
    orders of a three-cycle merge overlap flatten to the SAME sorted
    operand list.  [op_sort_permutation_eq] (under linearity) is the
    single load-bearing fact. *)

Definition rchain_operand (x : reduced_cft) : list chain_tree :=
  match x with
  | RChain c => [c]
  | _ => []
  end.

Definition is_non_rchain (x : reduced_cft) : bool :=
  match x with
  | RChain _ => false
  | _ => true
  end.

(** Canonicalize a node's child list: flatten every chain to its leaf
    operands, [op_sort] the pool, and place the sorted operand chains
    before the untouched non-chain children. *)
Definition canonicalize (ch : list reduced_cft) : list reduced_cft :=
  map RChain (op_sort (flat_map merge_operands (flat_map rchain_operand ch)))
  ++ filter is_non_rchain ch.

Fixpoint kappa (T : reduced_cft) : reduced_cft :=
  match T with
  | RLeaf t => RLeaf t
  | RChain c => RChain (kappa_ct c)
  | RTree a ch => RTree a (canonicalize (map kappa ch))
  end.

(** [kappa] on a one-chain node, unfolded (definitional). *)
Lemma kappa_singleton_chain :
  forall addr c,
    kappa (RTree addr [RChain c])
    = RTree addr (canonicalize [RChain (kappa_ct c)]).
Proof. reflexivity. Qed.

(** --- O1: kappa preserves the transfer multiset --- *)

Lemma Permutation_flat_map :
  forall (A B : Type) (f : A -> list B) (l1 l2 : list A),
    Permutation l1 l2 ->
    Permutation (flat_map f l1) (flat_map f l2).
Proof.
  intros A B f l1 l2 Hp.
  induction Hp; simpl.
  - apply perm_nil.
  - apply Permutation_app_head. exact IHHp.
  - rewrite !app_assoc. apply Permutation_app_tail.
    apply Permutation_app_comm.
  - eapply perm_trans; eassumption.
Qed.

Lemma merge_operands_transfers :
  forall c,
    flat_map chain_transfers (merge_operands c) = chain_transfers c.
Proof.
  induction c as [t | o d m ti to_ ft lbl l IHl r IHr]; simpl.
  - reflexivity.
  - destruct lbl; simpl;
      try (rewrite app_nil_r; reflexivity).
    rewrite flat_map_app_dist. rewrite IHl, IHr. reflexivity.
Qed.

Lemma merge_operands_nonempty :
  forall c, merge_operands c <> [].
Proof.
  induction c as [t | o d m ti to_ ft lbl l IHl r IHr]; simpl.
  - discriminate.
  - destruct lbl; try discriminate.
    intro H. apply app_eq_nil in H. destruct H. contradiction.
Qed.

Lemma op_insert_perm :
  forall c l, Permutation (op_insert c l) (c :: l).
Proof.
  intros c l. induction l as [| x xs IH]; simpl.
  - apply Permutation_refl.
  - destruct (op_le c x).
    + apply Permutation_refl.
    + eapply perm_trans; [apply perm_skip; exact IH |].
      apply perm_swap.
Qed.

Lemma op_sort_perm :
  forall l, Permutation (op_sort l) l.
Proof.
  induction l as [| x xs IH]; simpl.
  - apply perm_nil.
  - eapply perm_trans; [apply op_insert_perm |].
    apply perm_skip. exact IH.
Qed.

Lemma op_insert_nonempty :
  forall c l, op_insert c l <> [].
Proof.
  intros c l. destruct l as [| x xs]; simpl; [discriminate |].
  destruct (op_le c x); discriminate.
Qed.

Lemma op_sort_nonempty :
  forall l, l <> [] -> op_sort l <> [].
Proof.
  intros l Hl. destruct l as [| x xs]; [contradiction |].
  simpl. apply op_insert_nonempty.
Qed.

Lemma fold_left_merge_transfers :
  forall least rest first,
    chain_transfers
      (fold_left (canonical_merge_node least) rest first) =
    chain_transfers first ++ flat_map chain_transfers rest.
Proof.
  intros least.
  induction rest as [| x xs IH]; intros first; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH. simpl.
    rewrite <- app_assoc. reflexivity.
Qed.

Lemma rebuild_comb_transfers :
  forall dflt l,
    l <> [] ->
    chain_transfers (rebuild_comb dflt l) = flat_map chain_transfers l.
Proof.
  intros dflt [| x xs] Hne; [contradiction |].
  simpl. rewrite fold_left_merge_transfers. reflexivity.
Qed.

(** Congruence: mapping a chain-transfer-permuting function
    over a list permutes the flattened transfers. *)
Lemma flat_map_map_perm :
  forall (g : chain_tree -> chain_tree) ops,
    Forall (fun x =>
      Permutation (chain_transfers (g x)) (chain_transfers x)) ops ->
    Permutation
      (flat_map chain_transfers (map g ops))
      (flat_map chain_transfers ops).
Proof.
  intros g ops. induction ops as [| x xs IH]; intros HF; simpl.
  - apply perm_nil.
  - inversion HF as [| ? ? Hx Hxs]; subst.
    apply Permutation_app; [exact Hx | apply IH; exact Hxs].
Qed.

(** Each operand of a merge cluster is no larger than the
    whole; used for fuel sufficiency. *)
Lemma merge_operands_size_le :
  forall c x, In x (merge_operands c) -> ct_size x <= ct_size c.
Proof.
  induction c as [t | o d m ti to_ ft lbl l IHl r IHr];
    intros x Hin.
  - simpl in Hin. destruct Hin as [<- | []]. simpl. lia.
  - destruct lbl; simpl in Hin;
      try (destruct Hin as [<- | []]; simpl; lia).
    apply in_app_iff in Hin. destruct Hin as [Hl | Hr].
    + apply IHl in Hl. simpl. lia.
    + apply IHr in Hr. simpl. lia.
Qed.

(** Definitional unfolding of [kappa_fuel] on a [Merging]
    node (avoids [remember] blocking reduction). *)
Lemma kappa_fuel_merging :
  forall n' o d m ti to_ ft l r,
    kappa_fuel (S n') (CT_node o d m ti to_ ft Merging l r) =
    rebuild_comb (CT_node o d m ti to_ ft Merging l r)
      (op_sort (map (kappa_fuel n')
        (merge_operands (CT_node o d m ti to_ ft Merging l r)))).
Proof. intros. reflexivity. Qed.

(** kappa_fuel permutes the transfer list (multiset
    preservation) for sufficient fuel. *)
Lemma kappa_fuel_transfers :
  forall n c,
    ct_size c <= n ->
    Permutation (chain_transfers (kappa_fuel n c)) (chain_transfers c).
Proof.
  induction n as [| n' IH]; intros c Hsz.
  - simpl. apply Permutation_refl.
  - destruct c as [t | o d m ti to_ ft lbl l r].
    + simpl. apply Permutation_refl.
    + destruct lbl;
      try (simpl; apply Permutation_app;
           [ apply IH; simpl in Hsz; lia
           | apply IH; simpl in Hsz; lia ]).
      (* Merging *)
      rewrite kappa_fuel_merging.
      assert (Hne : op_sort (map (kappa_fuel n')
                (merge_operands
                   (CT_node o d m ti to_ ft Merging l r))) <> []).
      { apply op_sort_nonempty. intro Hm.
        apply map_eq_nil in Hm.
        exact (merge_operands_nonempty _ Hm). }
      rewrite (rebuild_comb_transfers _ _ Hne).
      eapply perm_trans;
        [ apply Permutation_flat_map; apply op_sort_perm |].
      eapply perm_trans.
      { apply flat_map_map_perm. apply Forall_forall.
        intros x Hx. apply IH.
        assert (Hlt : ct_size x <
                  ct_size (CT_node o d m ti to_ ft Merging l r)).
        { simpl in Hx. apply in_app_iff in Hx. simpl.
          destruct Hx as [Hl | Hr].
          - apply merge_operands_size_le in Hl. lia.
          - apply merge_operands_size_le in Hr. lia. }
        simpl in Hsz, Hlt. lia. }
      rewrite merge_operands_transfers. apply Permutation_refl.
Qed.

(** Flattening a list of chains through [merge_operands] preserves the
    transfer multiset. *)
Lemma flat_map_merge_operands_transfers :
  forall X,
    flat_map chain_transfers (flat_map merge_operands X)
    = flat_map chain_transfers X.
Proof.
  induction X as [| x xs IH]; simpl; [reflexivity |].
  rewrite flat_map_app_dist. rewrite merge_operands_transfers, IH.
  reflexivity.
Qed.

(** Flattening [map RChain] equals flattening [chain_transfers]. *)
Lemma flat_map_rcft_map_RChain :
  forall L, flat_map rcft_transfers (map RChain L) = flat_map chain_transfers L.
Proof.
  induction L as [| c cs IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(** Splitting a child list into its chain operands and non-chain
    children preserves the transfer multiset. *)
Lemma canonicalize_split :
  forall ch,
    Permutation
      (flat_map chain_transfers (flat_map rchain_operand ch)
       ++ flat_map rcft_transfers (filter is_non_rchain ch))
      (flat_map rcft_transfers ch).
Proof.
  induction ch as [| x xs IH]; [apply perm_nil |].
  destruct x as [t | c | a ch']; simpl.
  - eapply perm_trans; [ apply Permutation_sym; apply Permutation_middle | ].
    apply perm_skip. exact IH.
  - rewrite <- app_assoc. apply Permutation_app_head. exact IH.
  - rewrite app_assoc.
    eapply perm_trans;
      [apply Permutation_app_tail; apply Permutation_app_comm |].
    rewrite <- app_assoc. apply Permutation_app_head. exact IH.
Qed.

(** [canonicalize] preserves the transfer multiset. *)
Lemma canonicalize_transfers :
  forall ch,
    Permutation (flat_map rcft_transfers (canonicalize ch))
                (flat_map rcft_transfers ch).
Proof.
  intros ch. unfold canonicalize.
  rewrite flat_map_app_dist. rewrite flat_map_rcft_map_RChain.
  eapply perm_trans.
  { apply Permutation_app_tail.
    eapply perm_trans;
      [apply (Permutation_flat_map _ _ chain_transfers _ _
                (op_sort_perm _)) |].
    rewrite flat_map_merge_operands_transfers. apply Permutation_refl. }
  apply canonicalize_split.
Qed.

Lemma kappa_transfers :
  forall T, Permutation (rcft_transfers (kappa T)) (rcft_transfers T).
Proof.
  fix IH 1. intros T. destruct T as [t | c | a ch].
  - simpl. apply Permutation_refl.
  - simpl. unfold kappa_ct.
    apply kappa_fuel_transfers. lia.
  - simpl.
    eapply perm_trans; [apply canonicalize_transfers |].
    induction ch as [| x xs IHch]; simpl.
    + apply perm_nil.
    + apply Permutation_app; [apply IH | apply IHch].
Qed.

(** Sum over a permutation is invariant. *)
Lemma fold_right_Zadd_perm :
  forall (l1 l2 : list Z),
    Permutation l1 l2 ->
    fold_right Z.add 0%Z l1 = fold_right Z.add 0%Z l2.
Proof.
  intros l1 l2 Hp. induction Hp; simpl; lia.
Qed.

(** kappa preserves the delta map of every chain: canonical
    association reorders leaves but the signed sum is
    invariant. *)
Lemma kappa_ct_delta :
  forall c a tok,
    ch_delta (kappa_ct c) a tok = ch_delta c a tok.
Proof.
  intros c a tok. unfold kappa_ct.
  rewrite !ch_delta_sum_leaves.
  apply fold_right_Zadd_perm.
  apply Permutation_map.
  apply kappa_fuel_transfers. reflexivity.
Qed.

(** --- O1: kappa is idempotent --- *)

(** A chain tree whose root is not a [Merging] node; the
    operands of a merge cluster and the outputs of
    [kappa_fuel] on such operands are all of this shape. *)
Definition nonmerge_root (c : chain_tree) : Prop :=
  ch_label c <> Merging.

(** Operands of a [Merging] node are strictly smaller than
    the node (fuel strictly decreases into the cluster). *)
Lemma merge_operands_size_lt :
  forall o d m ti to_ ft l r x,
    In x (merge_operands (CT_node o d m ti to_ ft Merging l r)) ->
    ct_size x < ct_size (CT_node o d m ti to_ ft Merging l r).
Proof.
  intros o d m ti to_ ft l r x Hin.
  simpl in Hin. apply in_app_iff in Hin. simpl.
  destruct Hin as [Hl | Hr].
  - apply merge_operands_size_le in Hl. lia.
  - apply merge_operands_size_le in Hr. lia.
Qed.

(** [kappa_fuel] is fuel-irrelevant above the tree size:
    any two sufficient fuels give the same result. *)
Lemma kappa_fuel_ge :
  forall n m c,
    ct_size c <= n -> ct_size c <= m ->
    kappa_fuel n c = kappa_fuel m c.
Proof.
  induction n as [| n' IHn]; intros m c Hn Hm.
  - destruct c; simpl in Hn; lia.
  - destruct m as [| m'].
    + destruct c; simpl in Hm; lia.
    + destruct c as [t | o d mm ti to_ ft lbl l r].
      * reflexivity.
      * destruct lbl.
        1,3,4,5,6:
          (simpl; f_equal; apply IHn; simpl in Hn, Hm; lia).
        rewrite (kappa_fuel_merging n' o d mm ti to_ ft l r).
        rewrite (kappa_fuel_merging m' o d mm ti to_ ft l r).
        f_equal. f_equal.
        apply map_ext_in. intros x Hx.
        apply merge_operands_size_lt in Hx.
        apply IHn; simpl in Hn, Hm, Hx; lia.
Qed.

(** Every operand of a merge cluster has a non-[Merging]
    root: [merge_operands] descends through exactly the
    [Merging] nodes and stops elsewhere. *)
Lemma merge_operands_nonmerge :
  forall c x, In x (merge_operands c) -> nonmerge_root x.
Proof.
  induction c as [t | o d m ti to_ ft lbl l IHl r IHr];
    intros x Hin.
  - simpl in Hin. destruct Hin as [<- | []].
    unfold nonmerge_root. simpl. discriminate.
  - destruct lbl; simpl in Hin;
      try (destruct Hin as [<- | []];
           unfold nonmerge_root; simpl; discriminate).
    apply in_app_iff in Hin. destruct Hin as [Hl | Hr].
    + apply IHl; exact Hl.
    + apply IHr; exact Hr.
Qed.

(** [kappa_fuel] preserves a non-[Merging] root: a leaf or a
    non-[Merging] node is rewritten to a node of the same
    label. *)
Lemma kappa_fuel_nonmerge :
  forall n c, nonmerge_root c -> nonmerge_root (kappa_fuel n c).
Proof.
  intros n c Hc. destruct n as [| n']; [simpl; exact Hc |].
  destruct c as [t | o d m ti to_ ft lbl l r]; [simpl; exact Hc |].
  unfold nonmerge_root in *. destruct lbl; simpl in *;
    solve [exact Hc | exfalso; apply Hc; reflexivity].
Qed.

(** A non-[Merging] tree is its own sole operand. *)
Lemma merge_operands_nonmerge_singleton :
  forall x, nonmerge_root x -> merge_operands x = [x].
Proof.
  intros x Hx. destruct x as [t | o d m ti to_ ft lbl l r].
  - reflexivity.
  - destruct lbl; try reflexivity.
    unfold nonmerge_root in Hx. simpl in Hx. contradiction.
Qed.

(** Flattening a left comb of [merge_chain] nodes recovers
    the operand sequence, provided the folded operands are
    non-[Merging]. *)
Lemma merge_operands_fold :
  forall least rest first,
    (forall x, In x rest -> nonmerge_root x) ->
    merge_operands
      (fold_left (canonical_merge_node least) rest first)
    = merge_operands first ++ rest.
Proof.
  intros least.
  induction rest as [| x xs IH]; intros first Hrest; simpl.
  - rewrite app_nil_r. reflexivity.
  - assert (Hxs : forall y, In y xs -> nonmerge_root y).
    { intros y Hy. apply Hrest. right. exact Hy. }
    rewrite (IH (canonical_merge_node least first x) Hxs).
    simpl. rewrite (merge_operands_nonmerge_singleton x).
    + rewrite <- app_assoc. reflexivity.
    + apply Hrest. left. reflexivity.
Qed.

(** [rebuild_comb] is a right inverse of [merge_operands] on
    non-[Merging] operand lists. *)
Lemma merge_operands_rebuild :
  forall dflt l,
    l <> [] ->
    (forall x, In x l -> nonmerge_root x) ->
    merge_operands (rebuild_comb dflt l) = l.
Proof.
  intros dflt [| first rest] Hne Hall; [contradiction |].
  simpl. rewrite merge_operands_fold.
  - rewrite merge_operands_nonmerge_singleton.
    + reflexivity.
    + apply Hall. left. reflexivity.
  - intros x Hx. apply Hall. right. exact Hx.
Qed.

(** [op_le] is total: incomparable one way means comparable
    the other. *)
Lemma op_le_total :
  forall a b, op_le a b = false -> op_le b a = true.
Proof.
  intros a b H. unfold op_le in *.
  destruct (Nat.eqb (op_key a) (op_key b)) eqn:Hab.
  - apply Nat.eqb_eq in Hab. rewrite Hab, Nat.eqb_refl.
    apply lex_le_total. exact H.
  - assert (Hba : (op_key b =? op_key a) = false)
      by (rewrite Nat.eqb_sym; exact Hab).
    rewrite Hba.
    change ((op_key a <=? op_key b) = false) in H.
    apply Nat.leb_gt in H. apply Nat.leb_le. lia.
Qed.

(** Boolean sortedness of an operand list w.r.t. [op_le]. *)
Fixpoint op_sorted (l : list chain_tree) : bool :=
  match l with
  | [] => true
  | x :: xs =>
      match xs with
      | [] => true
      | y :: _ => op_le x y && op_sorted xs
      end
  end.

(** The head of an insertion is either the inserted element
    or the previous head. *)
Lemma op_insert_hd_cases :
  forall x l h t,
    op_insert x l = h :: t ->
    h = x \/ (exists z zs, l = z :: zs /\ h = z).
Proof.
  intros x l h t H. destruct l as [| z zs]; simpl in H.
  - injection H as <- <-. left. reflexivity.
  - destruct (op_le x z).
    + injection H as <- <-. left. reflexivity.
    + injection H as <- <-. right. exists z, zs. split; reflexivity.
Qed.

(** Prepending a head no larger than the list's first
    element keeps the list sorted. *)
Lemma op_sorted_cons_general :
  forall y l,
    op_sorted l = true ->
    match l with [] => True | z :: _ => op_le y z = true end ->
    op_sorted (y :: l) = true.
Proof.
  intros y [| z zs] Hs Hhd.
  - reflexivity.
  - apply andb_true_intro. split; [exact Hhd | exact Hs].
Qed.

(** [op_insert] preserves sortedness. *)
Lemma op_insert_sorted :
  forall x l, op_sorted l = true -> op_sorted (op_insert x l) = true.
Proof.
  intros x l. induction l as [| y ys IH]; intros Hs.
  - reflexivity.
  - simpl. destruct (op_le x y) eqn:Hxy.
    + apply andb_true_intro. split; [exact Hxy | exact Hs].
    + assert (Hyx : op_le y x = true) by (apply op_le_total; exact Hxy).
      assert (Hys : op_sorted ys = true).
      { destruct ys as [| z zs]; [reflexivity |].
        simpl in Hs. apply andb_prop in Hs. tauto. }
      apply op_sorted_cons_general.
      * apply IH; exact Hys.
      * destruct (op_insert x ys) as [| h t] eqn:Hins; [exact I |].
        destruct (op_insert_hd_cases x ys h t Hins)
          as [-> | (z & zs & Hys_eq & ->)].
        -- exact Hyx.
        -- subst ys. simpl in Hs. apply andb_prop in Hs.
           destruct Hs as [Hyz _]. exact Hyz.
Qed.

(** [op_sort] produces a sorted list. *)
Lemma op_sort_sorted :
  forall l, op_sorted (op_sort l) = true.
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - apply op_insert_sorted. exact IH.
Qed.

(** One-step unfolding of [op_sort] on a cons. *)
Lemma op_sort_cons :
  forall x xs, op_sort (x :: xs) = op_insert x (op_sort xs).
Proof. reflexivity. Qed.

(** Inserting a minimal head into a list puts it at the front. *)
Lemma op_insert_front :
  forall x xs,
    match xs with [] => True | y :: _ => op_le x y = true end ->
    op_insert x xs = x :: xs.
Proof.
  intros x [| y ys] H; simpl; [reflexivity | rewrite H; reflexivity].
Qed.

(** A sorted list is a fixed point of [op_sort]. *)
Lemma sorted_op_sort_id :
  forall l, op_sorted l = true -> op_sort l = l.
Proof.
  induction l as [| x xs IH]; intros Hs.
  - reflexivity.
  - rewrite op_sort_cons.
    assert (Hxs : op_sorted xs = true).
    { destruct xs as [| y ys];
        [reflexivity | simpl in Hs; apply andb_prop in Hs; tauto]. }
    rewrite (IH Hxs). apply op_insert_front.
    destruct xs as [| y ys]; [exact I |].
    simpl in Hs. apply andb_prop in Hs. tauto.
Qed.

(** [op_sort] is idempotent. *)
Lemma op_sort_idem :
  forall l, op_sort (op_sort l) = op_sort l.
Proof.
  intros l. apply sorted_op_sort_id. apply op_sort_sorted.
Qed.

Lemma in_op_sort : forall x l, In x (op_sort l) -> In x l.
Proof.
  intros x l H. eapply Permutation_in; [apply op_sort_perm | exact H].
Qed.

(** Fuel at or above the tree size computes [kappa_ct]. *)
Lemma kappa_fuel_eq_ct :
  forall n c, ct_size c <= n -> kappa_fuel n c = kappa_ct c.
Proof.
  intros n c Hn. unfold kappa_ct.
  apply kappa_fuel_ge; [exact Hn | lia].
Qed.

(** One-step unfolding of [kappa_fuel] on a non-[Merging]
    node. *)
Lemma kappa_fuel_nonmerge_node :
  forall n' o d m ti to_ ft lbl l r,
    lbl <> Merging ->
    kappa_fuel (S n') (CT_node o d m ti to_ ft lbl l r)
    = CT_node o d m ti to_ ft lbl (kappa_fuel n' l) (kappa_fuel n' r).
Proof.
  intros n' o d m ti to_ ft lbl l r Hlbl.
  destruct lbl; try (exfalso; apply Hlbl; reflexivity); reflexivity.
Qed.

(** [kappa_ct] commutes with a non-[Merging] node. *)
Lemma kappa_ct_nonmerge_node :
  forall o d m ti to_ ft lbl l r,
    lbl <> Merging ->
    kappa_ct (CT_node o d m ti to_ ft lbl l r)
    = CT_node o d m ti to_ ft lbl (kappa_ct l) (kappa_ct r).
Proof.
  intros o d m ti to_ ft lbl l r Hlbl. unfold kappa_ct.
  replace (ct_size (CT_node o d m ti to_ ft lbl l r))
    with (S (ct_size l + ct_size r)) by reflexivity.
  rewrite kappa_fuel_nonmerge_node by exact Hlbl.
  f_equal; apply kappa_fuel_ge; lia.
Qed.

(** [kappa_ct] on a [Merging] node: flatten, normalize
    operands, sort, rebuild. *)
Lemma kappa_ct_merging_eq :
  forall o d m ti to_ ft l r,
    kappa_ct (CT_node o d m ti to_ ft Merging l r)
    = rebuild_comb (CT_node o d m ti to_ ft Merging l r)
        (op_sort (map kappa_ct
          (merge_operands (CT_node o d m ti to_ ft Merging l r)))).
Proof.
  intros o d m ti to_ ft l r. unfold kappa_ct at 1.
  replace (ct_size (CT_node o d m ti to_ ft Merging l r))
    with (S (ct_size l + ct_size r)) by reflexivity.
  rewrite kappa_fuel_merging. f_equal. f_equal.
  apply map_ext_in. intros x Hx.
  apply kappa_fuel_eq_ct.
  apply merge_operands_size_lt in Hx. simpl in Hx. lia.
Qed.

(** Same, off the root label rather than the explicit node. *)
Lemma kappa_ct_merging_gen :
  forall c, ch_label c = Merging ->
    kappa_ct c
    = rebuild_comb c (op_sort (map kappa_ct (merge_operands c))).
Proof.
  intros c Hlbl. destruct c as [t | o d m ti to_ ft lbl l r].
  - simpl in Hlbl. discriminate.
  - simpl in Hlbl. subst lbl. apply kappa_ct_merging_eq.
Qed.

(** [rebuild_comb] ignores its default on a non-empty list. *)
Lemma rebuild_comb_dflt_irrel :
  forall d1 d2 l, l <> [] -> rebuild_comb d1 l = rebuild_comb d2 l.
Proof. intros d1 d2 [| x xs] H; [contradiction | reflexivity]. Qed.

(** Folding [canonical_merge_node] keeps a [Merging] root. *)
Lemma fold_left_merge_chain_label :
  forall least rest first,
    ch_label first = Merging ->
    ch_label
      (fold_left (canonical_merge_node least) rest first) = Merging.
Proof.
  intros least.
  induction rest as [| x xs IH]; intros first Hf; simpl.
  - exact Hf.
  - apply IH. reflexivity.
Qed.

(** A rebuilt comb of two or more operands is [Merging]. *)
Lemma rebuild_comb_label_merging :
  forall dflt a b rest,
    ch_label (rebuild_comb dflt (a :: b :: rest)) = Merging.
Proof.
  intros dflt a b rest. simpl.
  apply fold_left_merge_chain_label. reflexivity.
Qed.

(** A [Merging] node has at least two operands. *)
Lemma merge_operands_merging_length :
  forall o d m ti to_ ft l r,
    2 <= length (merge_operands (CT_node o d m ti to_ ft Merging l r)).
Proof.
  intros o d m ti to_ ft l r. simpl. rewrite length_app.
  pose proof (merge_operands_nonempty l) as Hl.
  pose proof (merge_operands_nonempty r) as Hr.
  destruct (merge_operands l); [contradiction |].
  destruct (merge_operands r); [contradiction |].
  simpl. lia.
Qed.

(** Mapping a pointwise-identity function is the identity. *)
Lemma map_fix :
  forall (f : chain_tree -> chain_tree) l,
    (forall x, In x l -> f x = x) -> map f l = l.
Proof.
  induction l as [| x xs IH]; intros H; simpl.
  - reflexivity.
  - rewrite H by (left; reflexivity).
    rewrite IH by (intros y Hy; apply H; right; exact Hy).
    reflexivity.
Qed.

(** --- O1: kappa is idempotent (main) --- *)
Lemma kappa_ct_idem_aux :
  forall n c, ct_size c <= n -> kappa_ct (kappa_ct c) = kappa_ct c.
Proof.
  induction n as [| n' IH]; intros c Hn.
  - destruct c; simpl in Hn; lia.
  - destruct c as [t | o d m ti to_ ft lbl l r].
    + reflexivity.
    + destruct lbl.
      1,3,4,5,6:
        (rewrite kappa_ct_nonmerge_node by discriminate;
         rewrite kappa_ct_nonmerge_node by discriminate;
         f_equal; apply IH; simpl in Hn; lia).
      (* Merging *)
      remember (CT_node o d m ti to_ ft Merging l r) as c eqn:Ec.
      assert (Hclbl : ch_label c = Merging) by (rewrite Ec; reflexivity).
      remember (op_sort (map kappa_ct (merge_operands c)))
        as sorted eqn:Hsorted.
      assert (Hne : sorted <> []).
      { rewrite Hsorted. apply op_sort_nonempty. intro Hm.
        apply map_eq_nil in Hm.
        exact (merge_operands_nonempty c Hm). }
      assert (Hlen : 2 <= length sorted).
      { rewrite Hsorted.
        rewrite (Permutation_length (op_sort_perm _)).
        rewrite length_map. rewrite Ec.
        apply merge_operands_merging_length. }
      assert (Hnm : forall e, In e sorted -> nonmerge_root e).
      { intros e He. rewrite Hsorted in He. apply in_op_sort in He.
        apply in_map_iff in He as [oi [Heq Hoi]]. subst e.
        unfold kappa_ct. apply kappa_fuel_nonmerge.
        apply (merge_operands_nonmerge c). exact Hoi. }
      assert (Hfix : forall e, In e sorted -> kappa_ct e = e).
      { intros e He. rewrite Hsorted in He. apply in_op_sort in He.
        apply in_map_iff in He as [oi [Heq Hoi]]. subst e.
        apply IH.
        rewrite Ec in Hoi.
        apply (merge_operands_size_lt o d m ti to_ ft l r) in Hoi.
        rewrite Ec in Hn. simpl in Hn, Hoi. lia. }
      assert (Hkc : kappa_ct c = rebuild_comb c sorted).
      { rewrite Hsorted. apply kappa_ct_merging_gen. exact Hclbl. }
      rewrite Hkc.
      assert (HC1lbl : ch_label (rebuild_comb c sorted) = Merging).
      { destruct sorted as [| a [| b rest]]; simpl in Hlen; try lia.
        apply rebuild_comb_label_merging. }
      rewrite (kappa_ct_merging_gen (rebuild_comb c sorted) HC1lbl).
      rewrite (merge_operands_rebuild c sorted Hne Hnm).
      rewrite (map_fix kappa_ct sorted Hfix).
      assert (Hsf : op_sort sorted = sorted).
      { rewrite Hsorted. apply op_sort_idem. }
      rewrite Hsf.
      apply rebuild_comb_dflt_irrel. exact Hne.
Qed.

(** kappa_ct is idempotent. *)
Lemma kappa_ct_idem :
  forall c, kappa_ct (kappa_ct c) = kappa_ct c.
Proof.
  intros c. apply (kappa_ct_idem_aux (ct_size c)). lia.
Qed.

(** kappa is idempotent on reduced CFTs.  Proved below (after the
    canonicalize bridge lemmas it needs) as [kappa_idem]. *)

(* ------------------------------------------------------------
   Section 30: AC-invariance of kappa (O2)

   Reassociating adjacent merge nodes never changes the
   operand list, so associativity is unconditional.
   Commuting them permutes the operand list; the sort
   erases the permutation provided no two operands tie in
   the sigma order.  [distinct_op_sigs] is that
   no-tie hypothesis: the mechanized face of Property 1 /
   transfer-disjointness of parallel merge arms (two
   transfer-disjoint nonempty chains cannot share their
   multiset of trace positions).
   ------------------------------------------------------------ *)

(** [lex_le] is transitive. *)
Lemma lex_le_trans :
  forall l1 l2 l3,
    lex_le l1 l2 = true -> lex_le l2 l3 = true -> lex_le l1 l3 = true.
Proof.
  induction l1 as [| x xs IH]; intros l2 l3 H1 H2; [reflexivity |].
  destruct l2 as [| y ys]; [discriminate |].
  destruct l3 as [| z zs]; [simpl in H2; discriminate |].
  simpl in H1, H2. simpl.
  destruct (Nat.ltb x y) eqn:Hxy.
  - apply Nat.ltb_lt in Hxy.
    destruct (Nat.ltb y z) eqn:Hyz.
    + apply Nat.ltb_lt in Hyz.
      assert (Hxz : (x <? z) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hxz. reflexivity.
    + destruct (Nat.ltb z y) eqn:Hzy; [discriminate |].
      apply Nat.ltb_ge in Hyz. apply Nat.ltb_ge in Hzy.
      assert (Hxz : (x <? z) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hxz. reflexivity.
  - destruct (Nat.ltb y x) eqn:Hyx; [discriminate |].
    apply Nat.ltb_ge in Hxy. apply Nat.ltb_ge in Hyx.
    assert (Exy : x = y) by lia. subst y.
    destruct (Nat.ltb x z) eqn:Hxz; [reflexivity |].
    destruct (Nat.ltb z x) eqn:Hzx; [discriminate |].
    exact (IH ys zs H1 H2).
Qed.

(** [lex_le] is antisymmetric. *)
Lemma lex_le_antisym :
  forall l1 l2,
    lex_le l1 l2 = true -> lex_le l2 l1 = true -> l1 = l2.
Proof.
  induction l1 as [| x xs IH]; intros l2 H1 H2.
  - destruct l2 as [| y ys]; [reflexivity | discriminate].
  - destruct l2 as [| y ys]; [discriminate |].
    simpl in H1, H2.
    destruct (Nat.ltb x y) eqn:Hxy.
    + destruct (Nat.ltb y x) eqn:Hyx.
      * apply Nat.ltb_lt in Hxy. apply Nat.ltb_lt in Hyx. lia.
      * discriminate.
    + destruct (Nat.ltb y x) eqn:Hyx; [discriminate |].
      apply Nat.ltb_ge in Hxy. apply Nat.ltb_ge in Hyx.
      assert (Exy : x = y) by lia. subst y.
      f_equal. exact (IH ys H1 H2).
Qed.

(** [op_le] is transitive (lexicographic composition of the
    first-leaf key and the signature order). *)
Lemma op_le_trans :
  forall a b c,
    op_le a b = true -> op_le b c = true -> op_le a c = true.
Proof.
  unfold op_le. intros a b c H1 H2.
  destruct (Nat.eqb (op_key a) (op_key b)) eqn:Kab;
    destruct (Nat.eqb (op_key b) (op_key c)) eqn:Kbc.
  - apply Nat.eqb_eq in Kab. apply Nat.eqb_eq in Kbc.
    assert (Kac : (op_key a =? op_key c) = true)
      by (apply Nat.eqb_eq; lia).
    rewrite Kac. exact (lex_le_trans _ _ _ H1 H2).
  - apply Nat.eqb_eq in Kab. apply Nat.eqb_neq in Kbc.
    assert (Kac : (op_key a =? op_key c) = false)
      by (apply Nat.eqb_neq; lia).
    rewrite Kac. apply Nat.leb_le.
    apply Nat.leb_le in H2. lia.
  - apply Nat.eqb_neq in Kab. apply Nat.eqb_eq in Kbc.
    assert (Kac : (op_key a =? op_key c) = false)
      by (apply Nat.eqb_neq; lia).
    rewrite Kac. apply Nat.leb_le.
    apply Nat.leb_le in H1. lia.
  - apply Nat.eqb_neq in Kab. apply Nat.eqb_neq in Kbc.
    apply Nat.leb_le in H1. apply Nat.leb_le in H2.
    assert (Kac : (op_key a =? op_key c) = false)
      by (apply Nat.eqb_neq; lia).
    rewrite Kac. apply Nat.leb_le. lia.
Qed.

(** Mutual [op_le] forces equal signatures: [op_le] is
    antisymmetric up to the trace signature. *)
Lemma op_le_both_sig :
  forall a b,
    op_le a b = true -> op_le b a = true -> op_sig a = op_sig b.
Proof.
  unfold op_le. intros a b H1 H2.
  destruct (Nat.eqb (op_key a) (op_key b)) eqn:Kab.
  - assert (Kba : (op_key b =? op_key a) = true)
      by (rewrite Nat.eqb_sym; exact Kab).
    rewrite Kba in H2.
    exact (lex_le_antisym _ _ H1 H2).
  - assert (Kba : (op_key b =? op_key a) = false)
      by (rewrite Nat.eqb_sym; exact Kab).
    rewrite Kba in H2.
    apply Nat.eqb_neq in Kab.
    apply Nat.leb_le in H1. apply Nat.leb_le in H2. lia.
Qed.

Lemma op_sorted_tail :
  forall x l, op_sorted (x :: l) = true -> op_sorted l = true.
Proof.
  intros x [| y ys] H; [reflexivity |].
  simpl in H. apply andb_prop in H. tauto.
Qed.

(** In a sorted list the head is below every element. *)
Lemma op_sorted_head_all :
  forall l x y,
    op_sorted (x :: l) = true -> In y l -> op_le x y = true.
Proof.
  induction l as [| z zs IH]; intros x y Hs Hin; [destruct Hin |].
  simpl in Hs. apply andb_prop in Hs as [Hxz Hs].
  destruct Hin as [<- | Hin].
  - exact Hxz.
  - exact (op_le_trans x z y Hxz (IH z y Hs Hin)).
Qed.

(** Pairwise-distinct trace signatures: the no-tie
    hypothesis under which the sigma order is strict on the
    operand set. *)
Definition distinct_op_sigs (l : list chain_tree) : Prop :=
  forall x y, In x l -> In y l -> op_sig x = op_sig y -> x = y.

(** Two sorted lists that are permutations of each other are
    equal when no two elements tie. *)
Lemma sorted_perm_unique :
  forall l l',
    op_sorted l = true -> op_sorted l' = true ->
    Permutation l l' ->
    distinct_op_sigs l ->
    l = l'.
Proof.
  induction l as [| x xs IH]; intros l' Hs Hs' Hp Hd.
  - apply Permutation_nil in Hp. subst. reflexivity.
  - destruct l' as [| y ys].
    { apply Permutation_sym in Hp.
      exact (match Permutation_nil_cons Hp with end). }
    assert (Hxy : x = y).
    { destruct (chain_tree_eq_dec x y) as [E | Ne]; [exact E |].
      assert (Hinx : In x (y :: ys))
        by (apply (Permutation_in x Hp); left; reflexivity).
      destruct Hinx as [E | Hinx];
        [exfalso; apply Ne; symmetry; exact E |].
      assert (Hiny : In y (x :: xs))
        by (apply (Permutation_in y (Permutation_sym Hp));
            left; reflexivity).
      destruct Hiny as [E | Hiny]; [exact E |].
      apply Hd.
      - left. reflexivity.
      - right. exact Hiny.
      - exact (op_le_both_sig x y
                 (op_sorted_head_all xs x y Hs Hiny)
                 (op_sorted_head_all ys y x Hs' Hinx)). }
    subst y. f_equal.
    apply IH.
    + exact (op_sorted_tail x xs Hs).
    + exact (op_sorted_tail x ys Hs').
    + exact (Permutation_cons_inv Hp).
    + intros a b Ha Hb. apply Hd; right; assumption.
Qed.

(** THE O2 engine: sorting is invariant under permutation of
    the input when no two elements tie -- [op_sort] is a
    function of the operand multiset. *)
Lemma op_sort_permutation_eq :
  forall l l',
    Permutation l l' ->
    distinct_op_sigs l ->
    op_sort l = op_sort l'.
Proof.
  intros l l' Hp Hd.
  apply sorted_perm_unique.
  - apply op_sort_sorted.
  - apply op_sort_sorted.
  - eapply perm_trans; [apply op_sort_perm |].
    eapply perm_trans; [exact Hp |].
    apply Permutation_sym. apply op_sort_perm.
  - intros a b Ha Hb. apply Hd.
    + eapply Permutation_in; [apply op_sort_perm | exact Ha].
    + eapply Permutation_in; [apply op_sort_perm | exact Hb].
Qed.

(** O2, associativity: reassociating adjacent merge nodes is
    erased by kappa unconditionally -- both associations
    flatten to the SAME operand list, so no sorting argument
    is even needed. *)
Lemma kappa_ct_merge_assoc :
  forall c1 c2 c3,
    kappa_ct (merge_chain (merge_chain c1 c2) c3)
    = kappa_ct (merge_chain c1 (merge_chain c2 c3)).
Proof.
  intros c1 c2 c3.
  rewrite (kappa_ct_merging_gen
             (merge_chain (merge_chain c1 c2) c3) eq_refl).
  rewrite (kappa_ct_merging_gen
             (merge_chain c1 (merge_chain c2 c3)) eq_refl).
  assert (Hops : merge_operands (merge_chain (merge_chain c1 c2) c3)
               = merge_operands (merge_chain c1 (merge_chain c2 c3))).
  { simpl. rewrite <- app_assoc. reflexivity. }
  rewrite Hops.
  apply rebuild_comb_dflt_irrel.
  apply op_sort_nonempty. intro Hm. apply map_eq_nil in Hm.
  exact (merge_operands_nonempty _ Hm).
Qed.

(** O2, commutativity: commuting the two arms of a merge is
    erased by kappa when the (normalized) operands have
    pairwise distinct signatures.  Both orders flatten to
    permutation-equal operand lists, the sort maps them to
    the same list, and [rebuild_comb] recomputes the same
    canonical node from it. *)
Lemma kappa_ct_merge_comm :
  forall c1 c2,
    distinct_op_sigs
      (map kappa_ct (merge_operands (merge_chain c1 c2))) ->
    kappa_ct (merge_chain c1 c2) = kappa_ct (merge_chain c2 c1).
Proof.
  intros c1 c2 Hd.
  rewrite (kappa_ct_merging_gen (merge_chain c1 c2) eq_refl).
  rewrite (kappa_ct_merging_gen (merge_chain c2 c1) eq_refl).
  assert (Hperm : Permutation
            (map kappa_ct (merge_operands (merge_chain c1 c2)))
            (map kappa_ct (merge_operands (merge_chain c2 c1)))).
  { apply Permutation_map. simpl. apply Permutation_app_comm. }
  rewrite (op_sort_permutation_eq _ _ Hperm Hd).
  apply rebuild_comb_dflt_irrel.
  apply op_sort_nonempty. intro Hm. apply map_eq_nil in Hm.
  exact (merge_operands_nonempty _ Hm).
Qed.

(** O2 at the reduced-CFT level. *)
Corollary kappa_merge_assoc :
  forall c1 c2 c3,
    kappa (RChain (merge_chain (merge_chain c1 c2) c3))
    = kappa (RChain (merge_chain c1 (merge_chain c2 c3))).
Proof.
  intros c1 c2 c3. simpl. f_equal. apply kappa_ct_merge_assoc.
Qed.

Corollary kappa_merge_comm :
  forall c1 c2,
    distinct_op_sigs
      (map kappa_ct (merge_operands (merge_chain c1 c2))) ->
    kappa (RChain (merge_chain c1 c2))
    = kappa (RChain (merge_chain c2 c1)).
Proof.
  intros c1 c2 Hd. simpl. f_equal.
  apply kappa_ct_merge_comm. exact Hd.
Qed.

(* ------------------------------------------------------------
   Section 31: Discharging distinct_op_sigs -- linearity

   [kappa_ct_merge_comm] is conditional on [distinct_op_sigs].
   That hypothesis is a genuine proof obligation: it can fail
   when two operands share a trace signature.  It is discharged
   here from LINEARITY of the CFTs that actually arise -- every
   transfer (so, under [is_trace_key_wf], every trace position)
   occurs once, hence operands carry distinct trace signatures.

   This section (a) reduces [distinct_op_sigs] to pairwise
   trace-key disjointness of nonempty operands (the bridge, via
   [is_trace_key_wf]) and (b) defines the linearity predicate.
   Linearity is a [rewrite_step]-invariant because the transfer
   MULTISET is permutation-preserved; that preservation lemma
   ([rcft_transfers_perm]) strengthens [preservation_step] and
   is the remaining mechanical step, threaded at O3.
   ------------------------------------------------------------ *)

Lemma nat_insert_perm :
  forall x l, Permutation (nat_insert x l) (x :: l).
Proof.
  intros x l. induction l as [| y ys IH]; simpl.
  - apply Permutation_refl.
  - destruct (Nat.leb x y).
    + apply Permutation_refl.
    + eapply perm_trans; [apply perm_skip; exact IH | apply perm_swap].
Qed.

Lemma nat_sort_perm :
  forall l, Permutation (nat_sort l) l.
Proof.
  induction l as [| x xs IH]; simpl.
  - apply perm_nil.
  - eapply perm_trans; [apply nat_insert_perm | apply perm_skip; exact IH].
Qed.

(** [op_sig] is a permutation of the operand's trace-key list. *)
Lemma op_sig_perm :
  forall c, Permutation (op_sig c) (map trace_key (chain_transfers c)).
Proof. intro c. unfold op_sig. apply nat_sort_perm. Qed.

(** Equal signatures share a trace key (using nonemptiness of
    the first operand). *)
Lemma op_sig_eq_shared_key :
  forall x y,
    op_sig x = op_sig y ->
    chain_transfers x <> [] ->
    exists k, In k (map trace_key (chain_transfers x))
              /\ In k (map trace_key (chain_transfers y)).
Proof.
  intros x y Heq Hne.
  assert (Hp : Permutation (map trace_key (chain_transfers x))
                           (map trace_key (chain_transfers y))).
  { eapply perm_trans; [apply Permutation_sym; apply op_sig_perm |].
    rewrite Heq. apply op_sig_perm. }
  destruct (chain_transfers x) as [| t rest] eqn:Hx;
    [contradiction |].
  exists (trace_key t). split.
  - simpl. left. reflexivity.
  - eapply Permutation_in; [exact Hp |].
    simpl. left. reflexivity.
Qed.

(** [NoDup] of an append: tail is [NoDup], blocks disjoint. *)
Lemma nodup_app_tail :
  forall (A : Type) (l1 l2 : list A),
    NoDup (l1 ++ l2) -> NoDup l2.
Proof.
  intros A l1. induction l1 as [| a l1 IH]; intros l2 H; simpl in H.
  - exact H.
  - inversion H as [| ? ? _ Hnd]; subst. exact (IH l2 Hnd).
Qed.

Lemma nodup_app_disjoint :
  forall (A : Type) (l1 l2 : list A),
    NoDup (l1 ++ l2) -> forall x, In x l1 -> In x l2 -> False.
Proof.
  intros A l1. induction l1 as [| a l1 IH]; intros l2 H x Hx1 Hx2;
    simpl in *; [destruct Hx1 |].
  inversion H as [| ? ? Hnin Hnd]; subst.
  destruct Hx1 as [<- | Hx1].
  - apply Hnin. apply in_or_app. right. exact Hx2.
  - exact (IH l2 Hnd x Hx1 Hx2).
Qed.

(** In a list whose concatenated trace-key blocks are
    duplicate-free, two members sharing a key are equal. *)
Lemma nodup_flatmap_shared_key :
  forall l x y k,
    NoDup (flat_map
             (fun c => map trace_key (chain_transfers c)) l) ->
    In x l -> In y l ->
    In k (map trace_key (chain_transfers x)) ->
    In k (map trace_key (chain_transfers y)) ->
    x = y.
Proof.
  induction l as [| z zs IH]; intros x y k Hnd Hx Hy Hkx Hky;
    [destruct Hx |].
  simpl in Hnd.
  destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
  - reflexivity.
  - exfalso. apply (nodup_app_disjoint _ _ _ Hnd k Hkx).
    apply in_flat_map. exists y. split; [exact Hy | exact Hky].
  - exfalso. apply (nodup_app_disjoint _ _ _ Hnd k Hky).
    apply in_flat_map. exists x. split; [exact Hx | exact Hkx].
  - apply nodup_app_tail in Hnd.
    exact (IH x y k Hnd Hx Hy Hkx Hky).
Qed.

(** THE BRIDGE: nonempty operands whose trace-key blocks are
    globally duplicate-free have pairwise distinct signatures.
    ([is_trace_key_wf] is not even needed here -- distinctness
    of trace KEYS already suffices; injectivity only matters
    when reducing key-disjointness to transfer-disjointness.) *)
Lemma distinct_op_sigs_of_nodup :
  forall l,
    (forall c, In c l -> chain_transfers c <> []) ->
    NoDup (flat_map
             (fun c => map trace_key (chain_transfers c)) l) ->
    distinct_op_sigs l.
Proof.
  intros l Hne Hnd x y Hx Hy Hsig.
  destruct (op_sig_eq_shared_key x y Hsig (Hne x Hx))
    as [k [Hkx Hky]].
  exact (nodup_flatmap_shared_key l x y k Hnd Hx Hy Hkx Hky).
Qed.

(** Linearity: every trace position occurs at most once in the
    whole reduced CFT.  Preserved by [rewrite_step] (the
    transfer multiset is permutation-invariant); gives the
    [NoDup] disjointness that discharges [distinct_op_sigs] at
    every merge node. *)
Definition linear (T : reduced_cft) : Prop :=
  NoDup (map trace_key (rcft_transfers T)).

(** Rearrangement shape for the endpoint/add/closed/node
    merges: folding two adjacent operands over a middle
    block permutes the transfer list. *)

(** Linearity is a [rewrite_step]-invariant. *)
Lemma linear_step :
  forall from_ T0 Tf,
    rewrite_step from_ T0 Tf -> linear T0 -> linear Tf.
Proof.
  intros from_ T0 Tf Hstep Hlin. unfold linear in *.
  eapply Permutation_NoDup; [| exact Hlin].
  apply Permutation_map.
  exact (rcft_transfers_perm from_ T0 Tf Hstep).
Qed.

(** ...and hence a [rewrite_star]-invariant. *)
Lemma linear_star :
  forall from_ T0 Tf,
    rewrite_star from_ T0 Tf -> linear T0 -> linear Tf.
Proof.
  intros from_ T0 Tf Hstar.
  induction Hstar as [T | T1 T2 T3 Hstep _ IH]; intros Hlin.
  - exact Hlin.
  - apply IH. exact (linear_step from_ T1 T2 Hstep Hlin).
Qed.

(** --- Discharging [distinct_op_sigs] from linearity --- *)

(** Trace keys distribute over [flat_map]/[map]. *)
Lemma flat_map_map_comm :
  forall (l : list chain_tree),
    flat_map (fun c => map trace_key (chain_transfers c)) l
    = map trace_key (flat_map chain_transfers l).
Proof.
  induction l as [| x xs IH]; simpl; [reflexivity |].
  rewrite map_app, IH. reflexivity.
Qed.

(** [kappa_ct] permutes a chain's transfers. *)
Lemma kappa_ct_transfers_perm :
  forall c, Permutation (chain_transfers (kappa_ct c)) (chain_transfers c).
Proof.
  intro c. unfold kappa_ct. apply kappa_fuel_transfers. lia.
Qed.

(** The operands of a merge cluster carry exactly the
    cluster's trace keys. *)
Lemma merge_operands_keys :
  forall C,
    flat_map (fun c => map trace_key (chain_transfers c)) (merge_operands C)
    = map trace_key (chain_transfers C).
Proof.
  intro C. rewrite flat_map_map_comm.
  rewrite merge_operands_transfers. reflexivity.
Qed.

(** Normalizing the operands permutes the concatenated key
    list (each [kappa_ct] permutes its operand's transfers). *)
Lemma kappa_ct_ops_keys_perm :
  forall ops,
    Permutation
      (flat_map (fun c => map trace_key (chain_transfers c))
                (map kappa_ct ops))
      (flat_map (fun c => map trace_key (chain_transfers c)) ops).
Proof.
  intro ops. rewrite !flat_map_map_comm.
  apply Permutation_map.
  apply flat_map_map_perm.
  apply Forall_forall. intros x _. apply kappa_ct_transfers_perm.
Qed.

(** A-DISCHARGE: on a LINEAR merged chain, the normalized
    operands have pairwise distinct signatures.  This turns
    [kappa_ct_merge_comm]'s side condition into linearity --
    which [linear_step]/[linear_star] make a reachable-tree
    invariant (Property 1). *)
Lemma distinct_op_sigs_map_kappa_ct :
  forall c1 c2,
    linear (RChain (merge_chain c1 c2)) ->
    distinct_op_sigs
      (map kappa_ct (merge_operands (merge_chain c1 c2))).
Proof.
  intros c1 c2 Hlin.
  apply distinct_op_sigs_of_nodup.
  - intros c Hc. apply in_map_iff in Hc as [op [<- _]].
    apply chain_transfers_nonempty.
  - eapply Permutation_NoDup;
      [ apply Permutation_sym; apply kappa_ct_ops_keys_perm |].
    rewrite merge_operands_keys.
    unfold linear in Hlin. simpl in Hlin. exact Hlin.
Qed.

(** O2 commutativity, UNCONDITIONAL on linear chains: the
    [distinct_op_sigs] premise is discharged by linearity. *)
Lemma kappa_ct_merge_comm_linear :
  forall c1 c2,
    linear (RChain (merge_chain c1 c2)) ->
    kappa_ct (merge_chain c1 c2) = kappa_ct (merge_chain c2 c1).
Proof.
  intros c1 c2 Hlin.
  apply kappa_ct_merge_comm.
  apply distinct_op_sigs_map_kappa_ct. exact Hlin.
Qed.

(* ------------------------------------------------------------
   Section 32: Local confluence modulo kappa (O3)

   Two one-step reducts of the same tree are joinable modulo
   kappa: each reduces (by R star) to trees with equal canonical
   forms.  With termination (O4, [rewrite_step_wf]) this
   yields global confluence modulo kappa (Newman, O5).

   The critical-pair classes on the frozen relation:
     - two-leaf trees: deterministic ([leaf_pair_exclusive]);
     - disjoint redexes: commute exactly;
     - the AC-merge family: joined by O2
       ([kappa_ct_merge_assoc] / [kappa_ct_merge_comm_linear]);
     - annotation vs merge on one chain: label agreement;
     - lift vs under: congruence anchoring.
   ------------------------------------------------------------ *)

(** [T1] and [T2] reduce to trees with the same canonical
    form. *)
Definition joinable_mod_kappa (from_ : address) (T1 T2 : reduced_cft)
    : Prop :=
  exists U1 U2,
    rewrite_star from_ T1 U1 /\
    rewrite_star from_ T2 U2 /\
    kappa U1 = kappa U2.

Definition local_confluent_mod_kappa (from_ : address) : Prop :=
  forall T T1 T2,
    rewrite_step from_ T T1 ->
    rewrite_step from_ T T2 ->
    joinable_mod_kappa from_ T1 T2.

Lemma joinable_mod_kappa_refl :
  forall from_ T, joinable_mod_kappa from_ T T.
Proof.
  intros from_ T. exists T, T.
  split; [apply RS_refl | split; [apply RS_refl | reflexivity]].
Qed.

Lemma joinable_mod_kappa_eq :
  forall from_ T1 T2, T1 = T2 -> joinable_mod_kappa from_ T1 T2.
Proof. intros from_ T1 T2 <-. apply joinable_mod_kappa_refl. Qed.

(** Critical-pair class 1: on a two-leaf tree the step is
    deterministic ([leaf_pair_exclusive]), so the pair joins
    trivially. *)
Lemma local_confluence_two_leaf :
  forall from_ addr t1 t2 T1 T2,
    rewrite_step from_ (RTree addr [RLeaf t1; RLeaf t2]) T1 ->
    rewrite_step from_ (RTree addr [RLeaf t1; RLeaf t2]) T2 ->
    joinable_mod_kappa from_ T1 T2.
Proof.
  intros from_ addr t1 t2 T1 T2 H1 H2.
  apply joinable_mod_kappa_eq.
  exact (leaf_pair_exclusive from_ addr t1 t2 T1 T2 H1 H2).
Qed.

(** Merge-output canonicity: since the merge rules pin only
    [cm]'s children ([ch_children cm = Some (c1, c2)], via the
    tightening) and not its summary fields, distinct
    rule-admissible [cm]s can differ -- but [kappa_ct]
    collapses them all to [kappa_ct (merge_chain c1 c2)].
    This is what lets the AC-merge critical pair join modulo
    kappa despite the (deliberately loose) merged node. *)
Lemma kappa_ct_of_merge_node :
  forall cm c1 c2,
    ch_label cm = Merging ->
    ch_children cm = Some (c1, c2) ->
    kappa_ct cm = kappa_ct (merge_chain c1 c2).
Proof.
  intros cm c1 c2 Hlbl Hch.
  destruct cm as [t | o d ms ti to_ ft lbl l r]; [discriminate |].
  cbn [ch_label ch_children] in Hlbl, Hch.
  subst lbl. injection Hch as Hl Hr. subst l r.
  rewrite (kappa_ct_merging_gen
             (CT_node o d ms ti to_ ft Merging c1 c2)) by reflexivity.
  rewrite (kappa_ct_merging_gen (merge_chain c1 c2)) by reflexivity.
  apply rebuild_comb_dflt_irrel.
  apply op_sort_nonempty. intro Hm. apply map_eq_nil in Hm.
  simpl in Hm. apply app_eq_nil in Hm. destruct Hm as [Hm1 _].
  exact (merge_operands_nonempty c1 Hm1).
Qed.

(** Congruence for reduction: a child reduction lifts to a
    reduction of the whole tree (iterated [RS_under]). *)
Lemma rewrite_star_under :
  forall from_ addr L R T T',
    rewrite_star from_ T T' ->
    rewrite_star from_
      (RTree addr (L ++ [T] ++ R))
      (RTree addr (L ++ [T'] ++ R)).
Proof.
  intros from_ addr L R T T' Hstar.
  induction Hstar as [X | X Y Z Hstep _ IH].
  - apply RS_refl.
  - eapply RS_trans; [apply RS_under; exact Hstep | exact IH].
Qed.

(** Congruence for joinability modulo kappa: joins lift
    through a one-hole context, since [kappa] maps over
    children.  This discharges every [RS_under]-vs-[RS_under]
    (same position) critical pair. *)
Lemma joinable_mod_kappa_under :
  forall from_ addr L R T1 T2,
    joinable_mod_kappa from_ T1 T2 ->
    joinable_mod_kappa from_
      (RTree addr (L ++ [T1] ++ R))
      (RTree addr (L ++ [T2] ++ R)).
Proof.
  intros from_ addr L R T1 T2 [U1 [U2 [H1 [H2 Hk]]]].
  exists (RTree addr (L ++ [U1] ++ R)),
         (RTree addr (L ++ [U2] ++ R)).
  split; [apply rewrite_star_under; exact H1 |].
  split; [apply rewrite_star_under; exact H2 |].
  cbn [kappa]. do 2 f_equal.
  rewrite !map_app. cbn [map]. rewrite Hk. reflexivity.
Qed.

(** A merge node's operands are its children's operands
    concatenated. *)
Lemma merge_operands_children :
  forall cm c1 c2,
    ch_label cm = Merging ->
    ch_children cm = Some (c1, c2) ->
    merge_operands cm = merge_operands c1 ++ merge_operands c2.
Proof.
  intros cm c1 c2 Hlbl Hch.
  destruct cm as [t | o d ms ti to_ ft lbl l r]; [discriminate |].
  cbn [ch_label ch_children] in Hlbl, Hch.
  subst lbl. injection Hch as Hl Hr. subst l r. reflexivity.
Qed.

(** AC-merge critical pair (associativity direction),
    node-level and UNCONDITIONAL: the two ways of merging
    three chains -- (c1,c2) then with c3, versus c1 with
    (c2,c3) -- have equal canonical forms.  Both flatten to
    the same operand list up to [app_assoc], and
    [rebuild_comb] ignores its (differing) default.  This is
    the mechanized "distinct tree shapes, one canonical form"
    of the paper's Section 2. *)
Lemma kappa_ct_merge_assoc_nodes :
  forall c1 c2 c3 cm12 cm23 cm_a cm_b,
    ch_label cm12 = Merging -> ch_children cm12 = Some (c1, c2) ->
    ch_label cm23 = Merging -> ch_children cm23 = Some (c2, c3) ->
    ch_label cm_a = Merging -> ch_children cm_a = Some (cm12, c3) ->
    ch_label cm_b = Merging -> ch_children cm_b = Some (c1, cm23) ->
    kappa_ct cm_a = kappa_ct cm_b.
Proof.
  intros c1 c2 c3 cm12 cm23 cm_a cm_b
         H12l H12c H23l H23c Hal Hac Hbl Hbc.
  rewrite (kappa_ct_merging_gen cm_a Hal).
  rewrite (kappa_ct_merging_gen cm_b Hbl).
  rewrite (merge_operands_children cm_a cm12 c3 Hal Hac).
  rewrite (merge_operands_children cm12 c1 c2 H12l H12c).
  rewrite (merge_operands_children cm_b c1 cm23 Hbl Hbc).
  rewrite (merge_operands_children cm23 c2 c3 H23l H23c).
  rewrite (app_assoc (merge_operands c1) (merge_operands c2)
             (merge_operands c3)).
  apply rebuild_comb_dflt_irrel.
  apply op_sort_nonempty. intro Hm. apply map_eq_nil in Hm.
  apply app_eq_nil in Hm. destruct Hm as [Hm _].
  apply app_eq_nil in Hm. destruct Hm as [Hm _].
  exact (merge_operands_nonempty c1 Hm).
Qed.

(** Critical-pair class 2 (AC-merge, associativity): the two
    merge reducts of three chains join modulo kappa.  Given
    the two second-merge steps (whose firing is the endpoint
    geometry, supplied by the caller), both land at a single
    merged chain, and those chains are kappa-equal by
    [kappa_ct_merge_assoc_nodes]. *)
Lemma local_confluence_merge_merge_mid :
  forall from_ addr c1 c2 c3 cm12 cm23 cm_a cm_b,
    ch_label cm12 = Merging -> ch_children cm12 = Some (c1, c2) ->
    ch_label cm23 = Merging -> ch_children cm23 = Some (c2, c3) ->
    ch_label cm_a = Merging -> ch_children cm_a = Some (cm12, c3) ->
    ch_label cm_b = Merging -> ch_children cm_b = Some (c1, cm23) ->
    rewrite_step from_ (RTree addr [RChain cm12; RChain c3])
                       (RTree addr [RChain cm_a]) ->
    rewrite_step from_ (RTree addr [RChain c1; RChain cm23])
                       (RTree addr [RChain cm_b]) ->
    joinable_mod_kappa from_
      (RTree addr [RChain cm12; RChain c3])
      (RTree addr [RChain c1; RChain cm23]).
Proof.
  intros from_ addr c1 c2 c3 cm12 cm23 cm_a cm_b
         H12l H12c H23l H23c Hal Hac Hbl Hbc Hsa Hsb.
  exists (RTree addr [RChain cm_a]), (RTree addr [RChain cm_b]).
  split; [apply rewrite_star_one; exact Hsa |].
  split; [apply rewrite_star_one; exact Hsb |].
  rewrite !kappa_singleton_chain.
  rewrite (kappa_ct_merge_assoc_nodes c1 c2 c3 cm12 cm23 cm_a cm_b
             H12l H12c H23l H23c Hal Hac Hbl Hbc).
  reflexivity.
Qed.

(** General merge-node commutativity: two merge nodes whose
    operand lists are permutations have equal canonical forms
    -- when the (normalized) operands have pairwise distinct
    signatures (linearity).  Subsumes the commutation
    critical pairs (merges sharing one endpoint, whose join
    reorders the operand list). *)
Lemma kappa_ct_merge_perm :
  forall cm_a cm_b,
    ch_label cm_a = Merging -> ch_label cm_b = Merging ->
    Permutation (merge_operands cm_a) (merge_operands cm_b) ->
    distinct_op_sigs (map kappa_ct (merge_operands cm_a)) ->
    kappa_ct cm_a = kappa_ct cm_b.
Proof.
  intros cm_a cm_b Hal Hbl Hperm Hd.
  rewrite (kappa_ct_merging_gen cm_a Hal).
  rewrite (kappa_ct_merging_gen cm_b Hbl).
  assert (Hpm : Permutation (map kappa_ct (merge_operands cm_a))
                            (map kappa_ct (merge_operands cm_b)))
    by (apply Permutation_map; exact Hperm).
  rewrite (op_sort_permutation_eq _ _ Hpm Hd).
  apply rebuild_comb_dflt_irrel.
  apply op_sort_nonempty. intro Hm. apply map_eq_nil in Hm.
  exact (merge_operands_nonempty cm_b Hm).
Qed.

(** Critical-pair class 2b, step-level: two merges sharing one
    endpoint chain -- (c1,c2) and (c1,c3) -- join modulo
    kappa.  Both complete to a single chain over {c1,c2,c3};
    the operand lists are permutations, reconciled by
    [kappa_ct_merge_perm] under linearity ([distinct_op_sigs],
    supplied by the caller from the reachable tree). *)
Lemma local_confluence_merge_merge_end :
  forall from_ addr c1 c2 c3 cm12 cm13 cm_a cm_b,
    ch_label cm12 = Merging -> ch_children cm12 = Some (c1, c2) ->
    ch_label cm13 = Merging -> ch_children cm13 = Some (c1, c3) ->
    ch_label cm_a = Merging -> ch_children cm_a = Some (cm12, c3) ->
    ch_label cm_b = Merging -> ch_children cm_b = Some (cm13, c2) ->
    distinct_op_sigs (map kappa_ct (merge_operands cm_a)) ->
    rewrite_step from_ (RTree addr [RChain cm12; RChain c3])
                       (RTree addr [RChain cm_a]) ->
    rewrite_step from_ (RTree addr [RChain cm13; RChain c2])
                       (RTree addr [RChain cm_b]) ->
    joinable_mod_kappa from_
      (RTree addr [RChain cm12; RChain c3])
      (RTree addr [RChain cm13; RChain c2]).
Proof.
  intros from_ addr c1 c2 c3 cm12 cm13 cm_a cm_b
         H12l H12c H13l H13c Hal Hac Hbl Hbc Hd Hsa Hsb.
  exists (RTree addr [RChain cm_a]), (RTree addr [RChain cm_b]).
  split; [apply rewrite_star_one; exact Hsa |].
  split; [apply rewrite_star_one; exact Hsb |].
  assert (Heq : kappa_ct cm_a = kappa_ct cm_b).
  { apply (kappa_ct_merge_perm cm_a cm_b Hal Hbl); [| exact Hd].
    rewrite (merge_operands_children cm_a cm12 c3 Hal Hac).
    rewrite (merge_operands_children cm12 c1 c2 H12l H12c).
    rewrite (merge_operands_children cm_b cm13 c2 Hbl Hbc).
    rewrite (merge_operands_children cm13 c1 c3 H13l H13c).
    rewrite <- (app_assoc (merge_operands c1) (merge_operands c2)
                 (merge_operands c3)).
    rewrite <- (app_assoc (merge_operands c1) (merge_operands c3)
                 (merge_operands c2)).
    apply Permutation_app_head. apply Permutation_app_comm. }
  rewrite !kappa_singleton_chain. rewrite Heq. reflexivity.
Qed.

(** --- Positional backbone for the assembly --- *)

(** Two single-element holes in the same list: either the
    same position, or one strictly left of the other (with a
    middle segment).  The combinatorial core of disjoint-
    redex reasoning. *)
Lemma list_two_hole :
  forall (A : Type) (L1 : list A) x R1 L2 y R2,
    L1 ++ x :: R1 = L2 ++ y :: R2 ->
    (L1 = L2 /\ x = y /\ R1 = R2) \/
    (exists M, L2 = L1 ++ x :: M /\ R1 = M ++ y :: R2) \/
    (exists M, L1 = L2 ++ y :: M /\ R2 = M ++ x :: R1).
Proof.
  intros A L1. induction L1 as [| a L1 IH];
    intros x R1 L2 y R2 Heq.
  - destruct L2 as [| b L2]; simpl in Heq.
    + injection Heq as Hx Hr. left. split; [reflexivity |].
      split; [exact Hx | exact Hr].
    + injection Heq as Hx Hr.
      right. left. exists L2. subst b. split; [reflexivity | exact Hr].
  - destruct L2 as [| b L2]; simpl in Heq.
    + injection Heq as Hx Hr.
      right. right. exists L1. subst a.
      split; [reflexivity | symmetry; exact Hr].
    + injection Heq as Hab Hr. subst b.
      destruct (IH x R1 L2 y R2 Hr)
        as [(HL & Hx & HR) | [(M & HL & HR) | (M & HL & HR)]].
      * left. subst. split; [reflexivity | split; reflexivity].
      * right. left. exists M. subst L2. split; [reflexivity | exact HR].
      * right. right. exists M. subst L1. split; [reflexivity | exact HR].
Qed.

(** Two [RS_under] steps at disjoint positions commute to a
    common reduct (both children stepped).  No IH needed. *)
Lemma joinable_two_disjoint_under :
  forall from_ addr L M Rr Ta Ta' Tb Tb',
    rewrite_step from_ Ta Ta' ->
    rewrite_step from_ Tb Tb' ->
    joinable_mod_kappa from_
      (RTree addr (L ++ Ta' :: M ++ Tb :: Rr))
      (RTree addr (L ++ Ta :: M ++ Tb' :: Rr)).
Proof.
  intros from_ addr L M Rr Ta Ta' Tb Tb' Ha Hb.
  exists (RTree addr (L ++ Ta' :: M ++ Tb' :: Rr)),
         (RTree addr (L ++ Ta' :: M ++ Tb' :: Rr)).
  split; [| split; [| reflexivity]].
  - apply rewrite_star_one.
    replace (L ++ Ta' :: M ++ Tb :: Rr)
      with ((L ++ Ta' :: M) ++ [Tb] ++ Rr)
      by (rewrite <- app_assoc; reflexivity).
    replace (L ++ Ta' :: M ++ Tb' :: Rr)
      with ((L ++ Ta' :: M) ++ [Tb'] ++ Rr)
      by (rewrite <- app_assoc; reflexivity).
    apply RS_under. exact Hb.
  - apply rewrite_star_one.
    replace (L ++ Ta :: M ++ Tb' :: Rr)
      with (L ++ [Ta] ++ (M ++ Tb' :: Rr)) by reflexivity.
    replace (L ++ Ta' :: M ++ Tb' :: Rr)
      with (L ++ [Ta'] ++ (M ++ Tb' :: Rr)) by reflexivity.
    apply RS_under. exact Ha.
Qed.

Lemma joinable_mod_kappa_sym :
  forall from_ T1 T2,
    joinable_mod_kappa from_ T1 T2 -> joinable_mod_kappa from_ T2 T1.
Proof.
  intros from_ T1 T2 [U1 [U2 [H1 [H2 Hk]]]].
  exists U2, U1. split; [exact H2 | split; [exact H1 | symmetry; exact Hk]].
Qed.

(** The [RS_under]-vs-[RS_under] case of local confluence:
    same child position joins by the IH (child-level
    confluence) lifted through the context; disjoint
    positions commute.  [IHTa] is the well-founded IH
    instantiated at the (smaller) child [Ta]. *)
Lemma lc_under_under :
  forall from_ addr La Ta Ta' Ra Lb Tb Tb' Rb,
    La ++ Ta :: Ra = Lb ++ Tb :: Rb ->
    rewrite_step from_ Ta Ta' ->
    rewrite_step from_ Tb Tb' ->
    (forall U1 U2, rewrite_step from_ Ta U1 -> rewrite_step from_ Ta U2 ->
       joinable_mod_kappa from_ U1 U2) ->
    joinable_mod_kappa from_
      (RTree addr (La ++ Ta' :: Ra))
      (RTree addr (Lb ++ Tb' :: Rb)).
Proof.
  intros from_ addr La Ta Ta' Ra Lb Tb Tb' Rb Heq Ha Hb IHTa.
  destruct (list_two_hole _ La Ta Ra Lb Tb Rb Heq)
    as [(HL & HT & HR) | [(M & HL & HR) | (M & HL & HR)]].
  - subst Lb Tb Rb.
    apply joinable_mod_kappa_under.
    apply (IHTa Ta' Tb'); [exact Ha | exact Hb].
  - subst Lb Ra.
    replace (RTree addr ((La ++ Ta :: M) ++ Tb' :: Rb))
      with (RTree addr (La ++ Ta :: M ++ Tb' :: Rb))
      by (rewrite <- app_assoc; reflexivity).
    apply joinable_two_disjoint_under; [exact Ha | exact Hb].
  - subst La Rb.
    replace (RTree addr ((Lb ++ Tb :: M) ++ Ta' :: Ra))
      with (RTree addr (Lb ++ Tb :: M ++ Ta' :: Ra))
      by (rewrite <- app_assoc; reflexivity).
    apply joinable_mod_kappa_sym.
    apply joinable_two_disjoint_under; [exact Hb | exact Ha].
Qed.

(** ---- O3 infrastructure: prefix closure and flat-step preservation ---- *)

(** On a two-leaf child list the lift guard forces the combiner to
    decline, hence no leaf-pair rule fires. *)
Lemma lift_ok_b_two_leaf_None :
  forall t1 t2,
    lift_children_ok [RLeaf t1; RLeaf t2] ->
    try_combine_leaves_full t1 t2 = None.
Proof.
  intros t1 t2 H. unfold lift_children_ok, lift_ok_b in H.
  destruct (try_combine_leaves_full t1 t2); [discriminate | reflexivity].
Qed.

(** Any child list containing a chain is lift-admissible: it is not the
    two-leaf shape [lift_ok_b] rejects. *)
Lemma lift_ok_b_true_if_chain_in :
  forall l c, In (RChain c) l -> lift_ok_b l = true.
Proof.
  intros l c Hin.
  destruct l as [| a [| b [| d rest]]].
  - inversion Hin.
  - destruct a; reflexivity.
  - simpl in Hin.
    destruct a; destruct b; try reflexivity;
      exfalso; destruct Hin as [H | [H | H]];
      solve [discriminate | contradiction].
  - destruct a; destruct b; reflexivity.
Qed.

(** Prefix closure.  Every non-leaf-pair rule commutes with prepending
    siblings: the lift guard [lift_children_ok children] rules out the
    only obstruction (a fireable two-leaf pair, whose LHS is the whole
    child list).  The outer address is arbitrary -- rules carry it
    freely. *)
Lemma rewrite_step_prefix_closed :
  forall from_ addr addr' children children' siblings,
    lift_children_ok children ->
    rewrite_step from_ (RTree addr children) (RTree addr children') ->
    rewrite_step from_ (RTree addr' (siblings ++ children))
                       (RTree addr' (siblings ++ children')).
Proof.
  intros from_ addr addr' children children' siblings Hok Hstep.
  pose proof Hstep as Hstep2.
  inversion Hstep; subst;
    try (exfalso;
         exact (kfull_leaf_O0 from_ addr _ _
                  (lift_ok_b_two_leaf_None _ _ Hok) _ Hstep2)).
  - (* R6 *) rewrite !(app_assoc siblings). apply RS_leaf_chain; assumption.
  - (* R12 *) rewrite !(app_assoc siblings). apply RS_node_leaf_chain; assumption.
  - (* R10 *) rewrite !(app_assoc siblings).
    apply RS_chain_seq; try assumption; try reflexivity.
  - (* lift *) rewrite !(app_assoc siblings). apply RS_lift; assumption.
  - (* R7 *) rewrite !(app_assoc siblings). apply RS_merge_endpoints; assumption.
  - (* R8 *) rewrite !(app_assoc siblings). apply RS_merge_add; assumption.
  - (* R9 *) rewrite !(app_assoc siblings). apply RS_merge_closed_R9; assumption.
  - (* R13 *) rewrite !(app_assoc siblings). apply RS_merge_node; assumption.
  - (* R14 *) rewrite !(app_assoc siblings).
    apply RS_annotate_arb; try assumption; try reflexivity.
  - (* R15 *) rewrite !(app_assoc siblings).
    apply RS_annotate_cyc; try assumption; try reflexivity.
  - (* under *) rewrite !(app_assoc siblings). apply RS_under; assumption.
Qed.

(** A step of a flat, lift-admissible frame yields another flat,
    lift-admissible frame: every applicable rule (leaf-pair excluded by
    the guard, lift/under excluded by flatness) produces a chain, so the
    result contains a chain and is not the rejected two-leaf shape. *)
Lemma flat_step_preserves :
  forall from_ addr inner inner',
    Forall (fun c => match c with
                     | RLeaf _ | RChain _ => True
                     | RTree _ _ => False
                     end) inner ->
    lift_children_ok inner ->
    rewrite_step from_ (RTree addr inner) (RTree addr inner') ->
    Forall (fun c => match c with
                     | RLeaf _ | RChain _ => True
                     | RTree _ _ => False
                     end) inner'
    /\ lift_children_ok inner'.
Proof.
  intros from_ addr inner inner' Hflat Hok Hstep.
  pose proof Hstep as Hstep2.
  inversion Hstep; subst;
    try (exfalso;
         exact (kfull_leaf_O0 from_ addr _ _
                  (lift_ok_b_two_leaf_None _ _ Hok) _ Hstep2)).
  - (* R6 *)
    split.
    + apply flat_childb_Forall. apply Forall_flat_childb in Hflat.
      repeat (rewrite ?forallb_app in Hflat |- *; cbn in Hflat |- *).
      exact Hflat.
    + unfold lift_children_ok. apply (lift_ok_b_true_if_chain_in _ c').
      apply in_or_app. right. left. reflexivity.
  - (* R12 *)
    split.
    + apply flat_childb_Forall. apply Forall_flat_childb in Hflat.
      repeat (rewrite ?forallb_app in Hflat |- *; cbn in Hflat |- *).
      exact Hflat.
    + unfold lift_children_ok. apply (lift_ok_b_true_if_chain_in _ c').
      apply in_or_app. right. left. reflexivity.
  - (* R10 *)
    split.
    + apply flat_childb_Forall. apply Forall_flat_childb in Hflat.
      repeat (rewrite ?forallb_app in Hflat |- *; cbn in Hflat |- *).
      exact Hflat.
    + unfold lift_children_ok.
      apply (lift_ok_b_true_if_chain_in _ (seq_chain c1 c2)).
      apply in_or_app. right. left. reflexivity.
  - (* lift: flat inner has no tree child *)
    exfalso. apply Forall_app in Hflat. destruct Hflat as [_ Hf].
    exact (Forall_inv Hf).
  - (* R7 *)
    split.
    + apply flat_childb_Forall. apply Forall_flat_childb in Hflat.
      repeat (rewrite ?forallb_app in Hflat |- *; cbn in Hflat |- *).
      exact Hflat.
    + unfold lift_children_ok. apply (lift_ok_b_true_if_chain_in _ cm).
      apply in_or_app. right. apply in_or_app. right. left. reflexivity.
  - (* R8 *)
    split.
    + apply flat_childb_Forall. apply Forall_flat_childb in Hflat.
      repeat (rewrite ?forallb_app in Hflat |- *; cbn in Hflat |- *).
      exact Hflat.
    + unfold lift_children_ok. apply (lift_ok_b_true_if_chain_in _ cm).
      apply in_or_app. right. apply in_or_app. right. left. reflexivity.
  - (* R9 *)
    split.
    + apply flat_childb_Forall. apply Forall_flat_childb in Hflat.
      repeat (rewrite ?forallb_app in Hflat |- *; cbn in Hflat |- *).
      exact Hflat.
    + unfold lift_children_ok. apply (lift_ok_b_true_if_chain_in _ cm).
      apply in_or_app. right. apply in_or_app. right. left. reflexivity.
  - (* R13 *)
    split.
    + apply flat_childb_Forall. apply Forall_flat_childb in Hflat.
      repeat (rewrite ?forallb_app in Hflat |- *; cbn in Hflat |- *).
      exact Hflat.
    + unfold lift_children_ok. apply (lift_ok_b_true_if_chain_in _ cm).
      apply in_or_app. right. apply in_or_app. right. left. reflexivity.
  - (* R14 *)
    split.
    + apply flat_childb_Forall. apply Forall_flat_childb in Hflat.
      repeat (rewrite ?forallb_app in Hflat |- *; cbn in Hflat |- *).
      exact Hflat.
    + unfold lift_children_ok.
      apply (lift_ok_b_true_if_chain_in _ (set_chain_label c Arbitrage)).
      apply in_or_app. right. left. reflexivity.
  - (* R15 *)
    split.
    + apply flat_childb_Forall. apply Forall_flat_childb in Hflat.
      repeat (rewrite ?forallb_app in Hflat |- *; cbn in Hflat |- *).
      exact Hflat.
    + unfold lift_children_ok.
      apply (lift_ok_b_true_if_chain_in _ (set_chain_label c Cycle)).
      apply in_or_app. right. left. reflexivity.
  - (* under: flat inner has no steppable child *)
    exfalso. clear Hstep Hstep2.
    apply Forall_app in Hflat. destruct Hflat as [_ Hf].
    apply Forall_inv in Hf.
    match goal with H : rewrite_step from_ ?t _ |- _ =>
      destruct (rewrite_step_lhs_tree _ _ _ H) as [a0 [ch0 HT]]; subst t end.
    exact Hf.
Qed.

(** Critical pair: [RS_lift] of a subtree vs. an [RS_under] reduction
    inside that same subtree.  The guard makes the lifted frame reduced,
    so the inner step is a non-leaf-pair rule that commutes with the
    sibling prefix; both orders reach [siblings ++ inner']. *)
Lemma lc_lift_under :
  forall from_ parent addr inner inner' siblings,
    Forall (fun c => match c with
                     | RLeaf _ | RChain _ => True
                     | RTree _ _ => False
                     end) inner ->
    lift_children_ok inner ->
    rewrite_step from_ (RTree addr inner) (RTree addr inner') ->
    joinable_mod_kappa from_
      (RTree parent (siblings ++ inner))
      (RTree parent (siblings ++ [RTree addr inner'])).
Proof.
  intros from_ parent addr inner inner' siblings Hflat Hok Hstep.
  destruct (flat_step_preserves from_ addr inner inner' Hflat Hok Hstep)
    as [Hflat' Hok'].
  exists (RTree parent (siblings ++ inner')),
         (RTree parent (siblings ++ inner')).
  split; [| split; [| reflexivity]].
  - apply rewrite_star_one.
    exact (rewrite_step_prefix_closed from_ addr parent inner inner'
             siblings Hok Hstep).
  - apply rewrite_star_one.
    apply RS_lift; assumption.
Qed.

(** Every rule preserves the stepped tree's address: a step from
    [RTree a X] lands in [RTree a X'].  (Dual to
    [rewrite_step_lhs_tree].) *)
Lemma rewrite_step_rhs_tree :
  forall from_ a X T',
    rewrite_step from_ (RTree a X) T' -> exists X', T' = RTree a X'.
Proof.
  intros from_ a X T' H. inversion H; subst; eauto.
Qed.

(** Lift is deterministic: the lifted subtree is the unique last
    child, so two lifts of one tree coincide. *)
Lemma lc_lift_lift :
  forall from_ parent addr addr' inner inner' sib sib',
    sib ++ [RTree addr inner] = sib' ++ [RTree addr' inner'] ->
    joinable_mod_kappa from_
      (RTree parent (sib ++ inner))
      (RTree parent (sib' ++ inner')).
Proof.
  intros from_ parent addr addr' inner inner' sib sib' Heq.
  apply app_inj_tail in Heq. destruct Heq as [Hsib Htree].
  injection Htree as Ha Hi. subst. apply joinable_mod_kappa_refl.
Qed.

(** Regrouping helpers: pull a suffix [s] out past one/two cons cells
    (the intervening cons blocks [rewrite <- !app_assoc], so these do it
    explicitly).  Used to reshape merge/annotate rule shapes into the
    [_ ++ [tree]] form that [RS_lift] and [app_inj_tail] need. *)
Lemma app_reassoc1 :
  forall (A : Type) (l r s : list A) (a : A),
    (l ++ a :: r) ++ s = l ++ a :: (r ++ s).
Proof. intros. rewrite <- app_assoc. reflexivity. Qed.

Lemma app_reassoc2 :
  forall (A : Type) (l m r s : list A) (a b : A),
    (l ++ a :: m ++ b :: r) ++ s = l ++ a :: m ++ b :: (r ++ s).
Proof.
  intros A l m r s a b.
  rewrite (app_reassoc1 _ l (m ++ b :: r) s a).
  rewrite (app_reassoc1 _ m r s b). reflexivity.
Qed.

Lemma app_reassoc_LM :
  forall (A : Type) (l m r s : list A) (c : A),
    l ++ m ++ [c] ++ (r ++ s) = (l ++ m ++ [c] ++ r) ++ s.
Proof. intros. rewrite <- ?app_assoc. reflexivity. Qed.

Lemma app_reassoc_L :
  forall (A : Type) (l r s : list A) (c : A),
    l ++ [c] ++ (r ++ s) = (l ++ [c] ++ r) ++ s.
Proof. intros. rewrite <- ?app_assoc. reflexivity. Qed.

(** Three-way associativity: exposes a buried redex segment [Y] at the
    end of a left-grouped prefix.  Used to re-fire an annotate/merge
    rule around an under-child sitting in its context. *)
Lemma app_assoc3 :
  forall (A : Type) (l a m Y : list A),
    (l ++ a ++ m) ++ Y = l ++ a ++ (m ++ Y).
Proof. intros. rewrite <- ?app_assoc. reflexivity. Qed.

(** A list ending in a tree cannot equal a rule shape whose last
    element is a leaf or chain (used to kill lift-vs-tail-rule and
    lift-vs-leaf-pair overlaps). *)
Ltac lift_contra :=
  match goal with
  | H : _ ++ RTree _ _ :: nil = _ |- _ =>
      apply (f_equal (@rev _)) in H; rewrite ?rev_app_distr in H;
      simpl in H; injection H as H _; discriminate H
  | H : _ = _ ++ RTree _ _ :: nil |- _ =>
      symmetry in H;
      apply (f_equal (@rev _)) in H; rewrite ?rev_app_distr in H;
      simpl in H; injection H as H _; discriminate H
  end.

(** Lift vs. any other step (the whole lift dimension of local
    confluence).  Tail rules (R6/R12/R10) and leaf-pair rules
    (R1-R5/R11) cannot fire (their last element is a leaf/chain, not
    the lifted tree); lift-vs-lift is deterministic; lift-vs-under is
    [lc_lift_under] (under in the tree) or a disjoint commute (under
    in a sibling); lift-vs-merge/annotate are disjoint commutes. *)
(* --- lift-vs-merge / lift-vs-annotate cell tactics for [lc_lift_vs]:
   the R7/R8/R9/R13 (merge) and R14/R15 (annotate) cells are identical
   except for the merge/annotate constructor applied, so factor the
   split-and-reassociate skeleton, parameterized by the ambient
   children (L, M, ...) and the rule to apply. --- *)
Ltac lift_merge_case parent addr inner siblings L M c1 c2 cm R mergerule :=
  assert (HRne : R <> []) by
    (intro Hn; subst R;
     lazymatch goal with He : _ = siblings ++ [RTree addr inner] |- _ =>
       rewrite <- (app_reassoc1 _ L M [RChain c2] (RChain c1)) in He;
       apply app_inj_tail in He; destruct He as [_ Hbad]; discriminate Hbad end);
  destruct (exists_last HRne) as [R' [ru HReq]]; subst R;
  lazymatch goal with He : _ = siblings ++ [RTree addr inner] |- _ =>
    rewrite <- (app_reassoc2 _ L M R' [ru] (RChain c1) (RChain c2)) in He;
    apply app_inj_tail in He; destruct He as [Hs Hru]
  end;
  subst siblings; subst ru;
  exists (RTree parent (L ++ M ++ [RChain cm] ++ (R' ++ inner))),
         (RTree parent ((L ++ M ++ [RChain cm] ++ R') ++ inner));
  split;
  [ apply rewrite_star_one;
    rewrite (app_reassoc2 _ L M R' inner (RChain c1) (RChain c2));
    apply mergerule; assumption
  | split;
    [ apply rewrite_star_one;
      rewrite (app_reassoc_LM _ L M R' [RTree addr inner] (RChain cm));
      apply RS_lift; assumption
    | assert (Hl : (L ++ M ++ [RChain cm] ++ (R' ++ inner))
                   = ((L ++ M ++ [RChain cm] ++ R') ++ inner))
        by (rewrite (app_reassoc_LM _ L M R' inner (RChain cm)); reflexivity);
      rewrite Hl; reflexivity ] ].

Ltac lift_annot_case parent addr inner siblings L c R label annotrule :=
  let cp := fresh "c'" in
  set (cp := set_chain_label c label) in *;
  assert (HRne : R <> []) by
    (intro Hn; subst R;
     lazymatch goal with He : _ = siblings ++ [RTree addr inner] |- _ =>
       apply app_inj_tail in He; destruct He as [_ Hbad]; discriminate Hbad end);
  destruct (exists_last HRne) as [R' [ru HReq]]; subst R;
  lazymatch goal with He : _ = siblings ++ [RTree addr inner] |- _ =>
    rewrite <- (app_reassoc1 _ L R' [ru] (RChain c)) in He;
    apply app_inj_tail in He; destruct He as [Hs Hru]
  end;
  subst siblings; subst ru;
  exists (RTree parent (L ++ [RChain cp] ++ (R' ++ inner))),
         (RTree parent ((L ++ [RChain cp] ++ R') ++ inner));
  split;
  [ apply rewrite_star_one;
    rewrite (app_reassoc1 _ L R' inner (RChain c));
    apply annotrule; try assumption; try reflexivity
  | split;
    [ apply rewrite_star_one;
      rewrite (app_reassoc_L _ L R' [RTree addr inner] (RChain cp));
      apply RS_lift; assumption
    | assert (Hl : (L ++ [RChain cp] ++ (R' ++ inner))
                   = ((L ++ [RChain cp] ++ R') ++ inner))
        by (rewrite (app_reassoc_L _ L R' inner (RChain cp)); reflexivity);
      rewrite Hl; reflexivity ] ].

Lemma lc_lift_vs :
  forall from_ parent addr inner siblings T2,
    Forall (fun c => match c with
                     | RLeaf _ | RChain _ => True
                     | RTree _ _ => False
                     end) inner ->
    lift_children_ok inner ->
    rewrite_step from_ (RTree parent (siblings ++ [RTree addr inner])) T2 ->
    joinable_mod_kappa from_ (RTree parent (siblings ++ inner)) T2.
Proof.
  intros from_ parent addr inner siblings T2 Hflat Hok H2.
  inversion H2; subst.
  - (* R1 *) lift_contra.
  - (* R2 *) lift_contra.
  - (* R3 *) lift_contra.
  - (* R4 *) lift_contra.
  - (* R5 *) lift_contra.
  - (* R6 *) lift_contra.
  - (* R12 *) lift_contra.
  - (* R10 *) lift_contra.
  - (* R11 *) lift_contra.
  - (* lift *)
    match goal with
    | H : siblings ++ [RTree addr inner] = ?s ++ [RTree ?a ?i] |- _ =>
        exact (lc_lift_lift from_ parent addr a inner i siblings s H)
    | H : ?s ++ [RTree ?a ?i] = siblings ++ [RTree addr inner] |- _ =>
        symmetry in H;
        exact (lc_lift_lift from_ parent addr a inner i siblings s H)
    end.
  - (* R7 *)
    lift_merge_case parent addr inner siblings L M c1 c2 cm R RS_merge_endpoints.
  - (* R8 *)
    lift_merge_case parent addr inner siblings L M c1 c2 cm R RS_merge_add.
  - (* R9 *)
    lift_merge_case parent addr inner siblings L M c1 c2 cm R RS_merge_closed_R9.
  - (* R13 *)
    lift_merge_case parent addr inner siblings L M c1 c2 cm R RS_merge_node.
  - (* R14 *)
    lift_annot_case parent addr inner siblings L c R Arbitrage RS_annotate_arb.
  - (* R15 *)
    lift_annot_case parent addr inner siblings L c R Cycle RS_annotate_cyc.
  - (* under *)
    match goal with
    | He : ?L0 ++ ?Tm :: ?R0 = siblings ++ [RTree addr inner] |- _ =>
      lazymatch goal with
      | Hu : rewrite_step from_ Tm ?Tm' |- _ =>
        destruct (list_two_hole _ L0 Tm R0 siblings (RTree addr inner) [] He)
          as [(HL & Hx & HR) | [(Mm & HL & HR) | (Mm & HL & HR)]];
        [ (* same position: under IS on the lifted tree *)
          subst L0; subst R0; rewrite Hx in Hu;
          destruct (rewrite_step_rhs_tree from_ addr inner _ Hu) as [inner' HT'];
          rewrite HT' in Hu |- *;
          exact (lc_lift_under from_ parent addr inner inner' siblings Hflat Hok Hu)
        | (* under strictly before the lifted tree (in siblings) *)
          subst siblings; subst R0;
          exists (RTree parent (L0 ++ [Tm'] ++ (Mm ++ inner))),
                 (RTree parent (((L0 ++ [Tm']) ++ Mm) ++ inner));
          split;
          [ apply rewrite_star_one; rewrite <- app_assoc;
            apply (RS_under from_ parent L0 Tm Tm' (Mm ++ inner)); exact Hu
          | split;
            [ apply rewrite_star_one; rewrite !app_assoc; apply RS_lift; assumption
            | assert (Hl : (L0 ++ [Tm'] ++ (Mm ++ inner))
                           = (((L0 ++ [Tm']) ++ Mm) ++ inner))
                by (rewrite <- !app_assoc; reflexivity);
              rewrite Hl; reflexivity ] ]
        | (* nil = Mm ++ Tm :: R0 : impossible *)
          destruct Mm; discriminate HR ]
      end
    end.
Qed.

(** Under vs. any other step.  Mirror of [lc_lift_vs] for the case
    where the primary step is an [RS_under] into child [Tc] (an
    [RTree], since it steps).  Leaf-pair rules are vacuous (a two-leaf
    tree has no tree child); under-vs-under is [lc_under_under] (via
    the child IH); under-vs-lift is [lc_lift_vs] up to symmetry;
    under-vs-{tail,merge,annotate} are disjoint commutes (the tree
    child is not part of the leaf/chain redex). *)
(* --- lc_under_vs cell tactics.  [under_leaf_vacuous]: the leaf-pair
   rules R1-R5 cannot fire on a child list that contains the stepping
   subtree [Tc] (which is an [RTree], never a leaf), so those cells are
   vacuous. --- *)
Ltac under_leaf_vacuous from_ Tc Tc' HTc :=
  exfalso; destruct (rewrite_step_lhs_tree from_ Tc Tc' HTc) as [a0 [i0 HTct]];
  lazymatch goal with
  | Heq : [RLeaf ?t1; RLeaf ?t2] = _ ++ Tc :: _ |- _ =>
      assert (Hin : In Tc [RLeaf t1; RLeaf t2]) by (rewrite Heq; apply in_elt);
      rewrite HTct in Hin; simpl in Hin;
      destruct Hin as [Hb | [Hb | Hb]]; try discriminate Hb; contradiction
  end.

(* [under_merge_case]: the under-vs-merge cells R7/R8/R9/R13, identical
   except for the merge constructor.  [Tc] is the stepping child; a
   double [list_two_hole] places it before, between, or after the two
   merged chains, and in each sub-case the merge and the under-step
   commute.  Binds the ambient children by [lazymatch]; only the merged
   chain [cm] and the rule are passed. *)
Ltac under_merge_case from_ addr Tc Tc' cm HTc mergerule :=
  destruct (rewrite_step_lhs_tree from_ Tc Tc' HTc) as [a0 [i0 HTct]];
  lazymatch goal with
  | Heq : ?L ++ RChain ?c1 :: ?M ++ RChain ?c2 :: ?R = ?La ++ Tc :: ?Ra |- _ =>
    destruct (list_two_hole _ L (RChain c1) (M ++ RChain c2 :: R) La Tc Ra Heq)
      as [(HA & HB & HC) | [(M1 & HA & HB) | (M1 & HA & HB)]];
    [ rewrite HTct in HB; discriminate HB
    | destruct (list_two_hole _ M (RChain c2) R M1 Tc Ra HB)
        as [(HA2 & HB2 & HC2) | [(M2 & HA2 & HB2) | (M2 & HA2 & HB2)]];
      [ rewrite HTct in HB2; discriminate HB2
      | subst M1; subst La; subst R;
        exists (RTree addr (L ++ M ++ [RChain cm] ++ (M2 ++ [Tc'] ++ Ra))),
               (RTree addr ((L ++ M ++ [RChain cm] ++ M2) ++ [Tc'] ++ Ra));
        split;
        [ apply rewrite_star_one;
          rewrite (app_reassoc2 _ L M M2 ([Tc'] ++ Ra) (RChain c1) (RChain c2));
          apply mergerule; assumption
        | split;
          [ apply rewrite_star_one;
            replace (L ++ M ++ [RChain cm] ++ (M2 ++ Tc :: Ra))
              with ((L ++ M ++ [RChain cm] ++ M2) ++ [Tc] ++ Ra)
              by (rewrite <- !app_assoc; reflexivity);
            apply RS_under; exact HTc
          | assert (Hl : (L ++ M ++ [RChain cm] ++ (M2 ++ [Tc'] ++ Ra))
                         = ((L ++ M ++ [RChain cm] ++ M2) ++ [Tc'] ++ Ra))
              by (rewrite <- !app_assoc; reflexivity);
            rewrite Hl; reflexivity ] ]
      | subst La; subst M; subst Ra;
        exists (RTree addr (L ++ (M1 ++ [Tc'] ++ M2) ++ [RChain cm] ++ R)),
               (RTree addr ((L ++ M1) ++ [Tc'] ++ (M2 ++ [RChain cm] ++ R)));
        split;
        [ apply rewrite_star_one;
          rewrite (app_reassoc1 _ L M1 ([Tc'] ++ (M2 ++ RChain c2 :: R)) (RChain c1));
          rewrite <- (app_assoc3 _ M1 [Tc'] M2 (RChain c2 :: R));
          apply mergerule; assumption
        | split;
          [ apply rewrite_star_one;
            replace (L ++ (M1 ++ Tc :: M2) ++ [RChain cm] ++ R)
              with ((L ++ M1) ++ [Tc] ++ (M2 ++ [RChain cm] ++ R))
              by (rewrite <- !app_assoc; reflexivity);
            apply RS_under; exact HTc
          | assert (Hl : (L ++ (M1 ++ [Tc'] ++ M2) ++ [RChain cm] ++ R)
                         = ((L ++ M1) ++ [Tc'] ++ (M2 ++ [RChain cm] ++ R)))
              by (rewrite <- !app_assoc; reflexivity);
            rewrite Hl; reflexivity ] ]
      ]
    | subst L; subst Ra;
      exists (RTree addr ((La ++ [Tc'] ++ M1) ++ M ++ [RChain cm] ++ R)),
             (RTree addr (La ++ [Tc'] ++ (M1 ++ M ++ [RChain cm] ++ R)));
      split;
      [ apply rewrite_star_one;
        rewrite <- (app_assoc3 _ La [Tc'] M1 (RChain c1 :: M ++ RChain c2 :: R));
        apply mergerule; assumption
      | split;
        [ apply rewrite_star_one;
          replace ((La ++ Tc :: M1) ++ M ++ [RChain cm] ++ R)
            with (La ++ [Tc] ++ (M1 ++ M ++ [RChain cm] ++ R))
            by (rewrite <- !app_assoc; reflexivity);
          apply RS_under; exact HTc
        | assert (Hl : ((La ++ [Tc'] ++ M1) ++ M ++ [RChain cm] ++ R)
                       = (La ++ [Tc'] ++ (M1 ++ M ++ [RChain cm] ++ R)))
            by (rewrite <- !app_assoc; reflexivity);
          rewrite Hl; reflexivity ] ]
    ]
  end.

(* [under_leaf_case]: the under-vs-leaf-onto-chain cells R6/R12, which
   differ only in the chaining constructor (RS_leaf_chain /
   RS_node_leaf_chain).  [cp] is the chained result chain. *)
Ltac under_leaf_case from_ addr Tc Tc' cp HTc rule :=
  destruct (rewrite_step_lhs_tree from_ Tc Tc' HTc) as [a0 [i0 HTct]];
  lazymatch goal with
  | Heq : ?sib ++ [RLeaf ?t; RChain ?c] = ?La ++ Tc :: ?Ra |- _ =>
    destruct (list_two_hole _ sib (RLeaf t) [RChain c] La Tc Ra Heq)
      as [(HA & HB & HC) | [(Mm & HA & HB) | (Mm & HA & HB)]];
    [ rewrite HTct in HB; discriminate HB
    | exfalso; destruct Mm as [| m Mm'];
      [ simpl in HB;
        let ha := fresh in let hb := fresh in injection HB as ha hb;
        rewrite HTct in ha; discriminate ha
      | simpl in HB;
        let ha := fresh in let hb := fresh in injection HB as ha hb;
        destruct Mm'; discriminate hb ]
    | subst sib; subst Ra;
      exists (RTree addr ((La ++ [Tc'] ++ Mm) ++ [RChain cp])),
             (RTree addr (La ++ [Tc'] ++ (Mm ++ [RChain cp])));
      split;
      [ apply rewrite_star_one;
        rewrite (app_reassoc_L _ La Mm [RLeaf t; RChain c] Tc');
        apply rule; assumption
      | split;
        [ apply rewrite_star_one;
          rewrite (app_reassoc1 _ La Mm [RChain cp] Tc);
          apply RS_under; exact HTc
        | assert (Hl : (La ++ [Tc'] ++ (Mm ++ [RChain cp]))
                       = ((La ++ [Tc'] ++ Mm) ++ [RChain cp]))
            by (rewrite (app_reassoc_L _ La Mm [RChain cp] Tc'); reflexivity);
          rewrite Hl; reflexivity ] ]
    ]
  end.

(* [under_annot_case]: the under-vs-annotate cells R14/R15, which differ
   only in the label written (Arbitrage/Cycle) and the annotate rule.
   The stepping child [Tc] is before or after the annotated chain. *)
Ltac under_annot_case from_ addr Tc Tc' HTc label annotrule :=
  destruct (rewrite_step_lhs_tree from_ Tc Tc' HTc) as [a0 [i0 HTct]];
  lazymatch goal with
  | Heq : ?L ++ RChain ?c :: ?R = ?La ++ Tc :: ?Ra |- _ =>
    let cp := fresh "c'" in
    set (cp := set_chain_label c label) in *;
    destruct (list_two_hole _ L (RChain c) R La Tc Ra Heq)
      as [(HA & HB & HC) | [(Mm & HA & HB) | (Mm & HA & HB)]];
    [ rewrite HTct in HB; discriminate HB
    | subst La; subst R;
      exists (RTree addr (L ++ [RChain cp] ++ (Mm ++ [Tc'] ++ Ra))),
             (RTree addr ((L ++ [RChain cp] ++ Mm) ++ [Tc'] ++ Ra));
      split;
      [ apply rewrite_star_one;
        rewrite (app_reassoc1 _ L Mm ([Tc'] ++ Ra) (RChain c));
        apply annotrule; try assumption; try reflexivity
      | split;
        [ apply rewrite_star_one;
          rewrite <- (app_assoc3 _ L [RChain cp] Mm (Tc :: Ra));
          apply RS_under; exact HTc
        | assert (Hl : (L ++ [RChain cp] ++ (Mm ++ [Tc'] ++ Ra))
                       = ((L ++ [RChain cp] ++ Mm) ++ [Tc'] ++ Ra))
            by (rewrite (app_assoc3 _ L [RChain cp] Mm ([Tc'] ++ Ra)); reflexivity);
          rewrite Hl; reflexivity ] ]
    | subst L; subst Ra;
      exists (RTree addr ((La ++ [Tc'] ++ Mm) ++ [RChain cp] ++ R)),
             (RTree addr (La ++ [Tc'] ++ (Mm ++ [RChain cp] ++ R)));
      split;
      [ apply rewrite_star_one;
        rewrite <- (app_assoc3 _ La [Tc'] Mm (RChain c :: R));
        apply annotrule; try assumption; try reflexivity
      | split;
        [ apply rewrite_star_one;
          rewrite (app_reassoc1 _ La Mm ([RChain cp] ++ R) Tc);
          apply RS_under; exact HTc
        | assert (Hl : ((La ++ [Tc'] ++ Mm) ++ [RChain cp] ++ R)
                       = (La ++ [Tc'] ++ (Mm ++ [RChain cp] ++ R)))
            by (rewrite (app_assoc3 _ La [Tc'] Mm ([RChain cp] ++ R)); reflexivity);
          rewrite Hl; reflexivity ] ]
    ]
  end.

Lemma lc_under_vs :
  forall from_ addr La Tc Tc' Ra T2,
    (forall U1 U2, rewrite_step from_ Tc U1 -> rewrite_step from_ Tc U2 ->
       joinable_mod_kappa from_ U1 U2) ->
    rewrite_step from_ Tc Tc' ->
    rewrite_step from_ (RTree addr (La ++ [Tc] ++ Ra)) T2 ->
    joinable_mod_kappa from_ (RTree addr (La ++ [Tc'] ++ Ra)) T2.
Proof.
  intros from_ addr La Tc Tc' Ra T2 IH HTc H2.
  inversion H2; subst.
  - (* R1 *)
    under_leaf_vacuous from_ Tc Tc' HTc.
  - (* R2 *)
    under_leaf_vacuous from_ Tc Tc' HTc.
  - (* R3 *)
    under_leaf_vacuous from_ Tc Tc' HTc.
  - (* R4 *)
    under_leaf_vacuous from_ Tc Tc' HTc.
  - (* R5 *)
    under_leaf_vacuous from_ Tc Tc' HTc.
  - (* R6 *)
    under_leaf_case from_ addr Tc Tc' c' HTc RS_leaf_chain.
  - (* R12 *)
    under_leaf_case from_ addr Tc Tc' c' HTc RS_node_leaf_chain.
  - (* R10 *)
    set (c' := seq_chain c1 c2) in *.
    destruct (rewrite_step_lhs_tree from_ Tc Tc' HTc) as [a0 [i0 HTct]];
    lazymatch goal with
    | Heq : siblings ++ [RChain ?c1; RChain ?c2] = La ++ Tc :: Ra |- _ =>
      destruct (list_two_hole _ siblings (RChain c1) [RChain c2] La Tc Ra Heq)
        as [(HA & HB & HC) | [(Mm & HA & HB) | (Mm & HA & HB)]];
      [ rewrite HTct in HB; discriminate HB
      | exfalso; destruct Mm as [| m Mm']; simpl in HB; injection HB as HB1 HB2;
        [ rewrite HTct in HB1; discriminate HB1 | destruct Mm'; discriminate HB2 ]
      | subst siblings; subst Ra;
        exists (RTree addr ((La ++ [Tc'] ++ Mm) ++ [RChain c'])),
               (RTree addr (La ++ [Tc'] ++ (Mm ++ [RChain c'])));
        split;
        [ apply rewrite_star_one;
          rewrite (app_reassoc_L _ La Mm [RChain c1; RChain c2] Tc');
          apply RS_chain_seq; try assumption; try reflexivity
        | split;
          [ apply rewrite_star_one;
            rewrite (app_reassoc1 _ La Mm [RChain c'] Tc);
            apply RS_under; exact HTc
          | assert (Hl : (La ++ [Tc'] ++ (Mm ++ [RChain c']))
                         = ((La ++ [Tc'] ++ Mm) ++ [RChain c']))
              by (rewrite (app_reassoc_L _ La Mm [RChain c'] Tc'); reflexivity);
            rewrite Hl; reflexivity ] ]
      ]
    end.
  - (* R11 *)
    under_leaf_vacuous from_ Tc Tc' HTc.
  - (* lift *)
    apply joinable_mod_kappa_sym;
    lazymatch goal with
    | Hflat_c : Forall _ ?children0,
      Hok_c : lift_children_ok ?children0,
      Heq : ?siblings0 ++ [RTree ?addr0 ?children0] = La ++ Tc :: Ra |- _ =>
        apply (lc_lift_vs from_ addr addr0 children0 siblings0
                 (RTree addr (La ++ [Tc'] ++ Ra)) Hflat_c Hok_c);
        rewrite Heq; apply RS_under; exact HTc
    end.
  - (* R7 *)
    under_merge_case from_ addr Tc Tc' cm HTc RS_merge_endpoints.
  - (* R8 *)
    under_merge_case from_ addr Tc Tc' cm HTc RS_merge_add.
  - (* R9 *)
    under_merge_case from_ addr Tc Tc' cm HTc RS_merge_closed_R9.
  - (* R13 *)
    under_merge_case from_ addr Tc Tc' cm HTc RS_merge_node.
  - (* R14 *)
    under_annot_case from_ addr Tc Tc' HTc Arbitrage RS_annotate_arb.
  - (* R15 *)
    under_annot_case from_ addr Tc Tc' HTc Cycle RS_annotate_cyc.
  - (* under *)
    lazymatch goal with
    | Heq : ?L0 ++ ?T0 :: ?R0 = La ++ Tc :: Ra |- _ =>
      lazymatch goal with
      | Hunder : rewrite_step from_ T0 ?T0' |- _ =>
          exact (lc_under_under from_ addr La Tc Tc' Ra L0 T0 T0' R0
                   (eq_sym Heq) HTc Hunder IH)
      end
    end.
Qed.

(* ============================================================
   Section 33: Local confluence modulo kappa (O3), assembled
   ============================================================ *)

(** [chain_adj x c]: predecessor [x] and tail chain [c] form a
    chaining redex -- R6/R12 when [x] is a leaf adjacent to [c],
    R10 when [x] is a chain whose destination meets [c]'s origin. *)
Definition chain_adj (x : reduced_cft) (c : chain_tree) : Prop :=
  match x with
  | RLeaf t => tr_dest t = ch_origin c \/ ch_destination c = tr_source t
  | RChain c1 => ch_destination c1 = ch_origin c
  | RTree _ _ => False
  end.

(** [tail_chainable cs c]: [c] is the last child and its immediate
    predecessor makes it a chaining operand (an R6/R10/R12 redex; also
    an R10 redex's RIGHT operand). *)
Definition tail_chainable (cs : list reduced_cft) (c : chain_tree) : Prop :=
  exists sib x, cs = sib ++ [x; RChain c] /\ chain_adj x c.

(** [left_tail_chainable cs c]: [c] is the LEFT operand of a chain-chain
    tail pair [[RChain c; RChain c'']] (an R10 redex's left operand).
    Together with [tail_chainable] this covers BOTH operands of a
    chaining redex. *)
Definition left_tail_chainable (cs : list reduced_cft) (c : chain_tree) : Prop :=
  exists sib c'', cs = sib ++ [RChain c; RChain c''] /\ chain_adj (RChain c) c''.

(** [has_twin cs c]: an earlier chain sibling parallel to [c] (same
    origin and destination) -- an R7 (parallel-merge) partner. *)
Definition has_twin (cs : list reduced_cft) (c : chain_tree) : Prop :=
  exists L M R cp,
    cs = L ++ [RChain cp] ++ M ++ [RChain c] ++ R /\
    ch_origin cp = ch_origin c /\ ch_destination cp = ch_destination c.

(** First half of sigma-CFT frame well-formedness (the confirmed
    option (1)):
    a chaining operand has no parallel-merge twin.  Equivalently,
    a chain with a parallel sibling is merge-locked (not chainable).
    Depth invariant: a parallel bundle is a call's internal arcs and
    the transfer feeding its shared origin sits in the PARENT frame --
    never a flat sibling -- so a merge operand never has a flat
    chaining neighbour.  This vacates exactly the R7-vs-R6 and
    R7-vs-R10 overlaps (otherwise non-joinable even modulo kappa)
    while leaving R6/R10 active wherever there is no twin (faithful:
    R10 is a real rule).  Option (2) "all chains share one origin and
    destination" is unfaithful -- a frame may hold endpoint-disjoint
    chains (eth_cft_engine.ml:247).  This is the mechanization of the
    paper's "at most one such pair per intermediary" (Table 1, leaf
    manipulation): a chaining operand -- EITHER operand of an R6/R10/R12
    redex -- has no parallel-merge (R7/R13) twin.  The implementation
    keeps chaining and parallel merging apart per pair (chain-seq's
    open premise s(c)<>d(c) vs a parallel merge's s=s,d=d) and by the
    is_labeled staging; [frame_no_twin] abstracts that as a structural
    invariant on the decoded tree. *)
Definition frame_no_twin (cs : list reduced_cft) : Prop :=
  forall c, tail_chainable cs c \/ left_tail_chainable cs c ->
    ~ has_twin cs c.

(** [annot_redex c]: [c] is an annotation redex -- a closed chain that
    carries no judgment yet, which is exactly the shape R14 and R15
    consume ([ch_origin c = ch_destination c] and
    [is_labeled (ch_label c) = false]). *)
Definition annot_redex (c : chain_tree) : Prop :=
  ch_origin c = ch_destination c /\ is_labeled (ch_label c) = false.

(** [parallel_sibling cs c]: [c] has a chain sibling parallel to it
    (same origin, same destination) on EITHER side, so [c] is an
    operand -- left or right -- of a parallel merge (R7/R8/R9/R13).
    [has_twin] is the right-operand half of this; the symmetric
    version is what the annotation overlaps need, because they put an
    obligation on both merge operands. *)
Definition parallel_sibling (cs : list reduced_cft) (c : chain_tree) : Prop :=
  exists L M R cp,
    (cs = L ++ [RChain cp] ++ M ++ [RChain c] ++ R \/
     cs = L ++ [RChain c] ++ M ++ [RChain cp] ++ R) /\
    ch_origin cp = ch_origin c /\ ch_destination cp = ch_destination c.

(** The staging half of frame well-formedness: a chain that a
    STRUCTURAL rule would consume -- either operand of a chaining redex
    (R6/R10/R12) or either operand of a parallel merge (R7/R8/R9/R13)
    -- is not an annotation redex.

    None of those eight rules tests a label or a closure the way the
    annotation rules do.  R6 and R12 test address adjacency alone (and
    do extend closed chains: 226 such steps across 19 of 65 traced
    transactions), and the four merge guards test addresses and tokens
    alone (98 merges of two closed chains in 6 of those transactions).
    So a closed unlabeled chain in either position is a redex for a
    structural rule AND for annotation at once.

    The implementation never faces the choice, and the reason is its
    phase order: [MakeFixpoint.run] saturates the whole leaf/chain
    rewriting of a trace ([small_step_history]) BEFORE [annotate_pass]
    relabels anything, so every chain the structural rules see carries
    [chaining], [token_burn], [token_mint] or [merging] and never
    [arbitrage] or [cycle].  [frame_staged] is that phase order read as
    a condition on the frame, and it is the same [is_labeled] staging
    [frame_no_twin] already appeals to.

    It is not cosmetic.  Annotating first and then combining builds a
    node over a judgment-carrying child; combining first destroys the
    annotation redex (a chained chain is open, a merged chain is a
    fresh [Merging] node); and [kappa] does not quotient labels, so the
    two results are distinct normal forms. *)
Definition frame_staged (cs : list reduced_cft) : Prop :=
  forall c, tail_chainable cs c \/ left_tail_chainable cs c
            \/ parallel_sibling cs c ->
    ~ annot_redex c.

(** Frame well-formedness: both halves.  Each names one way a chaining
    operand can be contended for by a rule the implementation's staging
    would reach at a different moment -- a parallel merge
    ([frame_no_twin]) or an annotation ([frame_staged]).  Together they
    are what makes the one-step diamond close modulo kappa. *)
Definition frame_wf (cs : list reduced_cft) : Prop :=
  frame_no_twin cs /\ frame_staged cs.

(** A [local_step mid mid'] is a root rewrite that replaces the
    contiguous sub-list [mid] with [mid'] in ANY sibling context.
    Annotate (R14/R15) and the merges (R7/R8/R9/R13) are local (their
    [L]/[M]/[R] are arbitrary); the tail-only chaining rules R6/R10/R12
    are not.  Two local steps at disjoint positions commute: each
    re-fires in the context left by the other, and both reach the tree
    with both contractions applied. *)
Definition local_step (from_ : address) (mid mid' : list reduced_cft) : Prop :=
  forall addr pre post,
    rewrite_step from_ (RTree addr (pre ++ mid ++ post))
                       (RTree addr (pre ++ mid' ++ post)).

(** [wf_rcft from_ T]: [frame_wf] and [linear]ity hold at every node of
    [T].  This is the class over which O3 (local confluence modulo
    kappa, [local_confluent_mod_kappa_holds]) holds.  [linear] is
    preserved by every [rewrite_step] ([linear_step]); [frame_wf]
    characterizes the nodes where a chaining step and a parallel merge
    do not compete for the same operand, which is exactly where the
    one-step diamond closes modulo kappa.  The order-independence that
    holds on all terms is the observable (delta) confluence of
    Section 21. *)
Fixpoint wf_rcft (from_ : address) (T : reduced_cft) : Prop :=
  match T with
  | RLeaf _ => True
  | RChain _ => True
  | RTree a cs =>
      frame_wf cs /\ linear (RTree a cs) /\
      (fix wf_all (l : list reduced_cft) : Prop :=
         match l with
         | [] => True
         | x :: r => wf_rcft from_ x /\ wf_all r
         end) cs
  end.

(** Node inversion: unpack [wf_rcft] of a tree into the frame's
    [frame_wf], [linear]ity of the node, and [Forall] well-formedness of
    the children. *)
Lemma wf_rcft_tree_inv :
  forall from_ addr cs,
    wf_rcft from_ (RTree addr cs) ->
    frame_wf cs /\ linear (RTree addr cs) /\ Forall (wf_rcft from_) cs.
Proof.
  intros from_ addr cs H. simpl in H. destruct H as [Hsf [Hlr Hall]].
  split; [exact Hsf |]. split; [exact Hlr |]. clear Hsf Hlr.
  revert Hall. induction cs as [| x r IHr]; intros Hall.
  - constructor.
  - simpl in Hall. destruct Hall as [Hx Hr].
    constructor; [exact Hx | apply IHr; exact Hr].
Qed.

(** Node introduction: the converse of [wf_rcft_tree_inv]; assemble a
    tree's [wf_rcft] from its frame [frame_wf], node [linear]ity, and
    [Forall] well-formedness of its children. *)
Lemma wf_rcft_tree_intro :
  forall from_ addr cs,
    frame_wf cs -> linear (RTree addr cs) -> Forall (wf_rcft from_) cs ->
    wf_rcft from_ (RTree addr cs).
Proof.
  intros from_ addr cs Hfw Hlr Hall. simpl.
  split; [exact Hfw |]. split; [exact Hlr |]. clear Hfw Hlr.
  induction Hall as [| x r Hx Hr IHr].
  - exact I.
  - simpl. split; [exact Hx | exact IHr].
Qed.

(** An [RChain c] sitting directly among a tree's children is a chain
    of that tree. *)
Lemma in_RChain_chain_in_rcft :
  forall c addr cs, In (RChain c) cs -> chain_in_rcft c (RTree addr cs).
Proof.
  intros c addr cs Hin. eapply CIR_tree; [exact Hin | apply CIR_here].
Qed.

(** [no_chains] descends to every child (a chain of a child is a chain
    of the tree). *)
Lemma no_chains_child :
  forall addr cs x, In x cs -> no_chains (RTree addr cs) -> no_chains x.
Proof.
  intros addr cs x Hin Hnc c Hch. apply (Hnc c).
  eapply CIR_tree; [exact Hin | exact Hch].
Qed.

(** [linear]ity descends to every child: a child's transfer keys are a
    sublist of the node's, which are all distinct. *)
Lemma linear_child :
  forall a cs x, In x cs -> linear (RTree a cs) -> linear x.
Proof.
  intros a cs x Hin Hlin. unfold linear in *. simpl in Hlin.
  apply in_split in Hin. destruct Hin as [l1 [l2 Hcs]]. subst cs.
  rewrite flat_map_app_dist in Hlin. simpl in Hlin.
  rewrite !map_app in Hlin.
  apply NoDup_app_remove_l in Hlin.
  apply NoDup_app_remove_r in Hlin. exact Hlin.
Qed.

(** A freshly-lifted CFT ([no_chains] -- only [RLeaf]/[RTree] nodes, as
    produced by the decode layer before any rewriting) that is [linear]
    is well-formed: [frame_wf] holds vacuously (its premise places an
    [RChain] among the children, contradicting [no_chains]), [linear]ity
    is the hypothesis (and descends to children), and every child is
    itself [no_chains], hence [wf_rcft] by induction.  This establishes
    [wf_rcft] on the initial tree of every reduction.

    Scope of this lemma, stated precisely because O3 quantifies over
    [wf_rcft]: on a [no_chains] tree the [frame_wf] conjunct is
    VACUOUS, so what this lemma certifies at the initial tree is
    [linear]ity plus an empty condition.  [linear] is preserved by
    every step ([linear_step], [linear_star]); [frame_wf] is not known
    to be, and is not expected to be -- a chaining or merge step can
    produce a chain whose endpoints coincide with an earlier sibling's,
    creating a twin the pre-step frame said nothing about.  So
    [wf_rcft] is a per-tree side condition under which the one-step
    diamond closes modulo kappa, not an invariant carried along a
    reduction.  The order-independence that holds unconditionally on
    every reachable tree is the observable (delta) confluence of the
    conservation section, which needs no well-formedness hypothesis. *)
Lemma no_chains_implies_wf_rcft :
  forall from_ T, no_chains T -> linear T -> wf_rcft from_ T.
Proof.
  intros from_ T. remember (rcft_size T) as n eqn:Hn. revert T Hn.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros T Hn Hnc Hlin. destruct T as [t | c | addr cs].
  - exact I.
  - exact I.
  - assert (Hno : forall c0, tail_chainable cs c0 \/ left_tail_chainable cs c0
                             \/ parallel_sibling cs c0 -> False).
    { intros c0 Hch. apply (Hnc c0).
      apply (in_RChain_chain_in_rcft c0 addr cs).
      destruct Hch as [[sib [x [Heq _]]]
                      | [[sib [c'' [Heq _]]]
                        | [L0 [M0 [R0 [cp [[Heq | Heq] _]]]]]]]; rewrite Heq.
      - apply in_or_app; right; simpl; right; left; reflexivity.
      - apply in_or_app; right; simpl; left; reflexivity.
      - apply in_or_app; right; simpl; right;
          apply in_or_app; right; simpl; left; reflexivity.
      - apply in_or_app; right; simpl; left; reflexivity. }
    apply wf_rcft_tree_intro.
    + split; intros c0 Hch _;
        [ apply (Hno c0); destruct Hch as [H | H]; [left | right; left]; exact H
        | exact (Hno c0 Hch) ].
    + exact Hlin.
    + apply Forall_forall. intros x Hin.
      apply (IH (rcft_size x)).
      * subst n. apply rcft_size_child_lt; exact Hin.
      * reflexivity.
      * exact (no_chains_child addr cs x Hin Hnc).
      * exact (linear_child addr cs x Hin Hlin).
Qed.

(** A list containing an [RChain] cannot equal a two-leaf list;
    discharges every leaf-pair-rule vs chain-rule root-root cell,
    where one step forces the frame to be [[RLeaf; RLeaf]] and the
    other places an [RChain] in it. *)
Lemma app_chain_neq_two_leaves :
  forall L c R t1 t2,
    L ++ [RChain c] ++ R = [RLeaf t1; RLeaf t2] -> False.
Proof.
  intros L c R t1 t2 H.
  assert (Hin : In (RChain c) [RLeaf t1; RLeaf t2]).
  { rewrite <- H. apply in_or_app. right. left. reflexivity. }
  simpl in Hin. destruct Hin as [E | [E | []]]; discriminate.
Qed.

(** A two-leaf list cannot equal a list ending in a [[RLeaf; RChain]]
    tail (the leaf-pair-rule vs R6/R12 root-root cell: R6/R12's
    leaf-onto-chain tail places an [RChain] as the LAST child, which a
    two-leaf tree cannot match).  Stated with the concrete tail literal
    so it unifies where [app_chain_neq_two_leaves] cannot. *)
Lemma two_leaves_neq_leaf_chain_tail :
  forall t1 t2 siblings tt c,
    [RLeaf t1; RLeaf t2] = siblings ++ [RLeaf tt; RChain c] -> False.
Proof.
  intros t1 t2 siblings tt c H.
  destruct siblings as [| x [| y sib']]; simpl in H.
  - discriminate H.
  - discriminate H.
  - injection H as _ _ Hnil. exact (app_cons_not_nil _ _ _ Hnil).
Qed.

(** Root-root dispatch tactics (used across all root [H1] cases).
    [two_leaf_contra]: the frame holds a chain, so a leaf-pair rule
    cannot fire.  [sym_lift]/[sym_under G]: when the OTHER step [H2]
    is a lift/under, reduce to [lc_lift_vs]/[lc_under_vs] with the
    current root step [G] as the arbitrary side, then symmetrize. *)
Ltac two_leaf_contra :=
  exfalso;
  match goal with
  | He : _ = _ |- _ =>
      solve [ exact (app_chain_neq_two_leaves _ _ _ _ _ He)
            | exact (app_chain_neq_two_leaves _ _ _ _ _ (eq_sym He))
            | exact (two_leaves_neq_leaf_chain_tail _ _ _ _ _ He)
            | exact (two_leaves_neq_leaf_chain_tail _ _ _ _ _ (eq_sym He)) ]
  end.

Ltac sym_lift G :=
  apply joinable_mod_kappa_sym;
  match goal with
  | Hfl : Forall _ ?children, Hok : lift_children_ok ?children,
    Heq : ?sibs ++ [RTree ?a0 ?children] = _ |- _ =>
      apply (lc_lift_vs _ _ a0 children sibs _ Hfl Hok);
      rewrite Heq; exact G
  end.

Ltac sym_under G IHh :=
  apply joinable_mod_kappa_sym;
  match goal with
  | Hu : rewrite_step ?f ?tc ?tc',
    Hwf' : wf_rcft ?f (RTree ?a ?children),
    Heq : ?la ++ ?tc :: ?ra = _ |- _ =>
      let Heq2 := fresh "Heq2" in
      assert (Heq2 : la ++ tc :: ra = children) by (rewrite Heq; reflexivity);
      let Hin := fresh "Hin" in
      assert (Hin : In tc children)
        by (rewrite <- Heq2; apply in_or_app; right; left; reflexivity);
      let Hall := fresh "Hall" in
      pose proof (wf_rcft_tree_inv f a children Hwf') as [_ [_ Hall]];
      let Hwftc := fresh "Hwftc" in
      assert (Hwftc : wf_rcft f tc)
        by (rewrite Forall_forall in Hall; apply Hall; exact Hin);
      apply (lc_under_vs f a la tc tc' ra _);
        [ intros U1 U2 HU1 HU2;
          exact (IHh (rcft_size tc)
                   (rcft_size_child_lt a children tc Hin)
                   tc eq_refl Hwftc U1 U2 HU1 HU2)
        | exact Hu
        | replace (la ++ [tc] ++ ra) with children by (rewrite <- Heq2; reflexivity);
          exact G ]
  end.

Lemma joinable_disjoint_local :
  forall from_ addr pre mid1 mid1' M mid2 mid2' post,
    local_step from_ mid1 mid1' ->
    local_step from_ mid2 mid2' ->
    joinable_mod_kappa from_
      (RTree addr (pre ++ mid1' ++ M ++ mid2 ++ post))
      (RTree addr (pre ++ mid1 ++ M ++ mid2' ++ post)).
Proof.
  intros from_ addr pre mid1 mid1' M mid2 mid2' post HL1 HL2.
  exists (RTree addr (pre ++ mid1' ++ M ++ mid2' ++ post)),
         (RTree addr (pre ++ mid1' ++ M ++ mid2' ++ post)).
  split; [| split; [| reflexivity]].
  - apply rewrite_star_one.
    specialize (HL2 addr (pre ++ mid1' ++ M) post).
    rewrite <- !app_assoc in HL2. exact HL2.
  - apply rewrite_star_one.
    specialize (HL1 addr pre (M ++ mid2' ++ post)).
    exact HL1.
Qed.

(** Each root rule that fires in an arbitrary context is a
    [local_step]; the premises are exactly those the corresponding
    [rewrite_step] constructor carries (available in every cell from
    inverting the step). *)
Lemma local_annotate_arb :
  forall from_ c c',
    ch_origin c = ch_destination c ->
    token_equiv (ch_token_in c) (ch_token_out c) = true ->
    ch_origin c' = ch_origin c -> ch_destination c' = ch_destination c ->
    ch_token_in c' = ch_token_in c -> ch_token_out c' = ch_token_out c ->
    is_labeled (ch_label c) = false -> ch_label c' = Arbitrage ->
    (address_in_chain from_ c = false \/ ch_origin c = from_) ->
    chain_transfers c' = chain_transfers c -> wrap_unwrap c = false ->
    c' = set_chain_label c Arbitrage ->
    local_step from_ [RChain c] [RChain c'].
Proof.
  intros. unfold local_step. intros addr pre post.
  apply (RS_annotate_arb from_ c c' addr pre post); assumption.
Qed.

Lemma local_annotate_cyc :
  forall from_ c c',
    ch_origin c = ch_destination c ->
    ch_origin c' = ch_origin c -> ch_destination c' = ch_destination c ->
    ch_token_in c' = ch_token_in c -> ch_token_out c' = ch_token_out c ->
    is_labeled (ch_label c) = false -> ch_label c' = Cycle ->
    address_in_chain from_ c = true ->
    (token_equiv (ch_token_in c) (ch_token_out c) = false \/
     wrap_unwrap c = true \/ ch_origin c <> from_) ->
    chain_transfers c' = chain_transfers c ->
    c' = set_chain_label c Cycle ->
    local_step from_ [RChain c] [RChain c'].
Proof.
  intros. unfold local_step. intros addr pre post.
  apply (RS_annotate_cyc from_ c c' addr pre post); assumption.
Qed.

(** R14 (Arbitrage) and R15 (Cycle) never fire on the same chain:
    R14 needs [token /\ ~wrap /\ (~in \/ origin=from)], R15 needs
    [in /\ (~token \/ wrap \/ origin<>from)].  Since [kappa] preserves
    labels, an Arbitrage-vs-Cycle overlap on one chain would be a
    label-divergent critical pair; this discharges that same-position
    cell as vacuous. *)
Lemma annotate_arb_cyc_exclusive :
  forall from_ c,
    token_equiv (ch_token_in c) (ch_token_out c) = true ->
    wrap_unwrap c = false ->
    (address_in_chain from_ c = false \/ ch_origin c = from_) ->
    address_in_chain from_ c = true ->
    (token_equiv (ch_token_in c) (ch_token_out c) = false \/
     wrap_unwrap c = true \/ ch_origin c <> from_) ->
    False.
Proof.
  intros from_ c Htok Hwrap H9 Hin Hg.
  destruct Hg as [H | [H | H]].
  - rewrite Htok in H; discriminate.
  - rewrite Hwrap in H; discriminate.
  - destruct H9 as [Hnin | Horig].
    + rewrite Hin in Hnin; discriminate.
    + exact (H Horig).
Qed.

(** Each merge rule [L ++ [c1] ++ M ++ [c2] ++ R -> L ++ M ++ [cm] ++ R]
    is a [local_step] replacing the span [[c1] ++ M ++ [c2]] with
    [M ++ [cm]] in an arbitrary sibling context.  [rewrite <- ?app_assoc]
    reassociates [local_step]'s [pre ++ seg ++ post] to the flattened
    shape each merge constructor produces (the opaque [M] blocks
    definitional flattening). *)
Lemma local_merge_endpoints : forall from_ c1 c2 cm M,
  ch_origin c1 = ch_origin c2 -> ch_destination c1 = ch_destination c2 ->
  ch_origin c1 <> ch_destination c1 ->
  ch_token_out c1 = ch_token_out c2 ->
  ch_token_mid c1 <> ch_token_mid c2 ->
  ch_origin cm = ch_origin c1 -> ch_destination cm = ch_destination c1 ->
  ch_token_in cm = ch_token_in c1 -> ch_token_out cm = ch_token_out c2 ->
  ch_label cm = Merging -> ch_children cm = Some (c1, c2) ->
  chain_transfers cm = chain_transfers c1 ++ chain_transfers c2 ->
  local_step from_ ([RChain c1] ++ M ++ [RChain c2]) (M ++ [RChain cm]).
Proof.
  intros. unfold local_step. intros addr pre post. rewrite <- ?app_assoc.
  apply (RS_merge_endpoints from_ c1 c2 cm addr pre M post); assumption.
Qed.

Lemma local_merge_add : forall from_ c1 c2 cm M,
  ch_origin c1 = ch_origin c2 -> ch_destination c1 = ch_destination c2 ->
  ch_origin c1 = ch_destination c1 ->
  ((ch_token_in c1 = ch_token_in c2 /\ ch_token_mid c1 = ch_token_mid c2 /\
    ch_token_out c1 = ch_token_out c2) \/
   bal_cont (ch_origin c1) c1 c2 = true) ->
  ch_origin cm = ch_origin c1 -> ch_destination cm = ch_destination c1 ->
  ch_token_in cm = ch_token_in c1 -> ch_token_out cm = ch_token_out c2 ->
  ch_label cm = Merging -> ch_children cm = Some (c1, c2) ->
  chain_transfers cm = chain_transfers c1 ++ chain_transfers c2 ->
  local_step from_ ([RChain c1] ++ M ++ [RChain c2]) (M ++ [RChain cm]).
Proof.
  intros. unfold local_step. intros addr pre post. rewrite <- ?app_assoc.
  apply (RS_merge_add from_ c1 c2 cm addr pre M post); assumption.
Qed.

Lemma local_merge_closed_R9 : forall from_ c1 c2 cm M,
  ch_origin c1 = ch_destination c1 -> ch_origin c2 = ch_destination c2 ->
  ch_origin c1 = ch_origin c2 -> ch_token_in c1 = ch_token_in c2 ->
  ch_token_out c1 = ch_token_out c2 ->
  ch_origin cm = ch_origin c1 -> ch_destination cm = ch_destination c1 ->
  ch_token_in cm = ch_token_in c1 -> ch_token_out cm = ch_token_out c2 ->
  ch_label cm = Merging -> ch_children cm = Some (c1, c2) ->
  chain_transfers cm = chain_transfers c1 ++ chain_transfers c2 ->
  local_step from_ ([RChain c1] ++ M ++ [RChain c2]) (M ++ [RChain cm]).
Proof.
  intros. unfold local_step. intros addr pre post. rewrite <- ?app_assoc.
  apply (RS_merge_closed_R9 from_ c1 c2 cm addr pre M post); assumption.
Qed.

Lemma local_merge_node : forall from_ c1 c2 cm M,
  ch_origin c1 = ch_origin c2 -> ch_destination c1 = ch_destination c2 ->
  ch_origin c1 <> ch_destination c1 ->
  ch_token_out c1 = ch_token_out c2 ->
  ch_token_mid c1 <> ch_token_mid c2 ->
  ch_token_in c1 = ch_token_in c2 ->
  ch_origin cm = ch_origin c1 -> ch_destination cm = ch_destination c1 ->
  ch_token_in cm = ch_token_in c1 -> ch_token_out cm = ch_token_out c2 ->
  ch_label cm = Merging -> ch_children cm = Some (c1, c2) ->
  chain_transfers cm = chain_transfers c1 ++ chain_transfers c2 ->
  local_step from_ ([RChain c1] ++ M ++ [RChain c2]) (M ++ [RChain cm]).
Proof.
  intros. unfold local_step. intros addr pre post. rewrite <- ?app_assoc.
  apply (RS_merge_node from_ c1 c2 cm addr pre M post); assumption.
Qed.

(** Keystone for the annotate-vs-merge root-root cells.  Annotation
    contracts a single closed, unlabeled chain [ca]; a merge contracts
    the wide span [[c1] ++ M ++ [c2]].  The shared children-list
    equation locates [ca] relative to that span via a nested
    [list_two_hole]: [ca = c1] and [ca = c2] are excluded by the
    caller's two [Hovl] obligations, [ca] left/right of the whole span
    commutes by [joinable_disjoint_local], and [ca] strictly inside [M]
    commutes because a merge ignores [M]'s contents and the annotated
    chain survives into the moved [M] (both orders reach one common
    reduct, so they join with no [kappa] rewriting).  The two overlaps
    are what [frame_staged] rules out, via [merge_annotate_absurd]:
    both [c1] and [c2] are [parallel_sibling]s of each other, and an
    annotation operand is an [annot_redex]. *)
Lemma joinable_annotate_vs_merge :
  forall from_ addr ca ca' c1 c2 cm L R L' M R',
    local_step from_ [RChain ca] [RChain ca'] ->
    (forall Mx, local_step from_
       ([RChain c1] ++ Mx ++ [RChain c2]) (Mx ++ [RChain cm])) ->
    (ca = c1 -> False) ->
    (ca = c2 -> False) ->
    L ++ RChain ca :: R = L' ++ RChain c1 :: (M ++ RChain c2 :: R') ->
    joinable_mod_kappa from_
      (RTree addr (L ++ RChain ca' :: R))
      (RTree addr (L' ++ M ++ RChain cm :: R')).
Proof.
  intros from_ addr ca ca' c1 c2 cm L R L' M R'
         Hann Hmrg Hc1 Hc2 Heq.
  destruct (list_two_hole _ L (RChain ca) R L' (RChain c1)
              (M ++ RChain c2 :: R') Heq)
    as [ (HL & Hx & HR) | [ (Mo & HLM & HRM) | (Mo & HLM & HRM) ] ].
  - (* ca = c1 : overlap, excluded by the caller *)
    exfalso; injection Hx as E1; exact (Hc1 E1).
  - (* ca strictly left of the span : disjoint *)
    subst L' R.
    pose proof (joinable_disjoint_local from_ addr L
                  [RChain ca] [RChain ca'] Mo
                  ([RChain c1] ++ M ++ [RChain c2]) (M ++ [RChain cm]) R'
                  Hann (Hmrg M)) as J.
    repeat (rewrite <- app_assoc in J || rewrite <- app_comm_cons in J);
    repeat (rewrite <- app_assoc || rewrite <- app_comm_cons); exact J.
  - (* ca right of c1 : locate it relative to c2 *)
    subst L.
    destruct (list_two_hole _ M (RChain c2) R' Mo (RChain ca) R HRM)
      as [ (HL2 & Hx2 & HR2) | [ (Mi & HLM2 & HRM2) | (Mi & HLM2 & HRM2) ] ].
    + (* ca = c2 : overlap, excluded by the caller *)
      exfalso; injection Hx2 as E2; exact (Hc2 (eq_sym E2)).
    + (* ca strictly right of the span : disjoint *)
      subst Mo R'.
      apply joinable_mod_kappa_sym.
      pose proof (joinable_disjoint_local from_ addr L'
                    ([RChain c1] ++ M ++ [RChain c2]) (M ++ [RChain cm]) Mi
                    [RChain ca] [RChain ca'] R
                    (Hmrg M) Hann) as J.
      repeat (rewrite <- app_assoc in J || rewrite <- app_comm_cons in J);
    repeat (rewrite <- app_assoc || rewrite <- app_comm_cons); exact J.
    + (* ca strictly inside M : both orders meet at one reduct *)
      subst M R.
      exists (RTree addr (L' ++ Mo ++ RChain ca' :: Mi ++ RChain cm :: R')),
             (RTree addr (L' ++ Mo ++ RChain ca' :: Mi ++ RChain cm :: R')).
      split; [| split; [| reflexivity]].
      * apply rewrite_star_one.
        pose proof (Hmrg (Mo ++ RChain ca' :: Mi) addr L' R') as Hm.
        repeat (rewrite <- app_assoc in Hm || rewrite <- app_comm_cons in Hm);
        repeat (rewrite <- app_assoc || rewrite <- app_comm_cons); exact Hm.
      * apply rewrite_star_one.
        pose proof (Hann addr (L' ++ Mo) (Mi ++ RChain cm :: R')) as Ha.
        repeat (rewrite <- app_assoc in Ha || rewrite <- app_comm_cons in Ha);
        repeat (rewrite <- app_assoc || rewrite <- app_comm_cons); exact Ha.
Qed.

(** --- Bridges: [kappa] commutes with operand extraction/flattening.
    These let the merge-merge key lemma reduce a [kappa]-equality on two
    divergent merge reducts to a permutation of their raw leaf-operand
    multisets. *)

(** Extracting the chains of [map kappa Y] = [kappa_ct]-ing the chains
    of [Y]. *)
Lemma flat_map_rchain_operand_map_kappa :
  forall Y,
    flat_map rchain_operand (map kappa Y)
    = map kappa_ct (flat_map rchain_operand Y).
Proof.
  induction Y as [| y ys IH]; simpl; [reflexivity |].
  destruct y as [t | c | a ch]; simpl; rewrite IH; reflexivity.
Qed.

(** The non-chain children of [map kappa Y] = [kappa] of the non-chain
    children of [Y] ([kappa] preserves the constructor kind). *)
Lemma filter_is_non_rchain_map_kappa :
  forall Y,
    filter is_non_rchain (map kappa Y)
    = map kappa (filter is_non_rchain Y).
Proof.
  induction Y as [| y ys IH]; simpl; [reflexivity |].
  destruct y as [t | c | a ch]; simpl; rewrite IH; reflexivity.
Qed.

(** A canonicalized chain's leaf operands are the [kappa_ct]-images of
    the original chain's leaf operands (up to permutation: [kappa_ct]
    reorders a [Merging] node's operands by [op_sort]). *)
Lemma merge_operands_kappa_ct_perm :
  forall c,
    Permutation (merge_operands (kappa_ct c)) (map kappa_ct (merge_operands c)).
Proof.
  intros c. destruct (label_eq_dec (ch_label c) Merging) as [Hm | Hnm].
  - rewrite (kappa_ct_merging_gen c Hm).
    assert (Hne : op_sort (map kappa_ct (merge_operands c)) <> []).
    { apply op_sort_nonempty. intro Hc. apply map_eq_nil in Hc.
      exact (merge_operands_nonempty c Hc). }
    assert (Hnm2 : forall x,
              In x (op_sort (map kappa_ct (merge_operands c))) -> nonmerge_root x).
    { intros x Hx. apply in_op_sort in Hx. apply in_map_iff in Hx.
      destruct Hx as [y [Hy Hin]]. subst x. unfold kappa_ct.
      apply kappa_fuel_nonmerge. exact (merge_operands_nonmerge c y Hin). }
    rewrite (merge_operands_rebuild c _ Hne Hnm2). apply op_sort_perm.
  - rewrite (merge_operands_nonmerge_singleton c Hnm).
    rewrite (merge_operands_nonmerge_singleton (kappa_ct c)
               (kappa_fuel_nonmerge (ct_size c) c Hnm)).
    apply Permutation_refl.
Qed.

(** Lift [merge_operands_kappa_ct_perm] over a list. *)
Lemma flat_map_merge_operands_kappa_ct_perm :
  forall L,
    Permutation (flat_map merge_operands (map kappa_ct L))
                (map kappa_ct (flat_map merge_operands L)).
Proof.
  induction L as [| x xs IH]; simpl; [apply perm_nil |].
  rewrite map_app. apply Permutation_app;
    [apply merge_operands_kappa_ct_perm | exact IH].
Qed.

(** The [kappa]-canonicalized leaf-operand multiset of a child list is
    a permutation of the [kappa_ct]-images of its raw leaf operands. *)
Lemma canon_ops_perm :
  forall X,
    Permutation
      (flat_map merge_operands (flat_map rchain_operand (map kappa X)))
      (map kappa_ct (flat_map merge_operands (flat_map rchain_operand X))).
Proof.
  intros X. rewrite flat_map_rchain_operand_map_kappa.
  eapply perm_trans; [apply flat_map_merge_operands_kappa_ct_perm |].
  apply Permutation_refl.
Qed.

(** [flat_map merge_operands o flat_map rchain_operand] (the raw
    leaf-operand multiset of a child list) distributes over [++] and
    peels a leading chain. *)
Lemma raw_ops_app :
  forall A B,
    flat_map merge_operands (flat_map rchain_operand (A ++ B))
    = flat_map merge_operands (flat_map rchain_operand A)
      ++ flat_map merge_operands (flat_map rchain_operand B).
Proof. intros A B. rewrite !flat_map_app_dist. reflexivity. Qed.

Lemma raw_ops_cons_chain :
  forall c B,
    flat_map merge_operands (flat_map rchain_operand (RChain c :: B))
    = merge_operands c ++ flat_map merge_operands (flat_map rchain_operand B).
Proof. reflexivity. Qed.

(** Rotate the middle block to the front. *)
Lemma perm_swap_app :
  forall {A} (a b c : list A), Permutation (a ++ b ++ c) (b ++ a ++ c).
Proof.
  intros A a b c. rewrite !app_assoc.
  apply Permutation_app_tail. apply Permutation_app_comm.
Qed.

(** Merging two operands preserves the raw leaf-operand multiset (up to
    permutation): the merged node flattens to its operands' operands. *)
Lemma raw_ops_merge_perm :
  forall L M R c1 c2 cm,
    ch_label cm = Merging -> ch_children cm = Some (c1, c2) ->
    Permutation
      (flat_map merge_operands
         (flat_map rchain_operand (L ++ M ++ RChain cm :: R)))
      (flat_map merge_operands
         (flat_map rchain_operand (L ++ RChain c1 :: M ++ RChain c2 :: R))).
Proof.
  intros L M R c1 c2 cm Hlbl Hch.
  rewrite !raw_ops_app, !raw_ops_cons_chain, !raw_ops_app.
  rewrite (merge_operands_children cm c1 c2 Hlbl Hch).
  (* LHS: opsL ++ (opsM ++ (moc1 ++ moc2) ++ opsR)
     RHS: opsL ++ (moc1 ++ (opsM ++ (moc2 ++ opsR))) *)
  apply Permutation_app_head.
  rewrite <- !app_assoc.
  (* opsM ++ moc1 ++ moc2 ++ opsR  ~  moc1 ++ opsM ++ moc2 ++ opsR *)
  apply perm_swap_app.
Qed.

(** Same-position merge-vs-merge: two merges that consume the identical
    operand pair [(c1, c2)] (possibly via different rules, e.g. R8 and
    R9) produce outputs with equal [kappa_ct] ([kappa_ct_of_merge_node]),
    so the two reducts are already kappa-equal -- no rewriting needed. *)
Lemma joinable_merge_same :
  forall from_ addr L M R c1 c2 cm cm0,
    ch_label cm = Merging -> ch_children cm = Some (c1, c2) ->
    ch_label cm0 = Merging -> ch_children cm0 = Some (c1, c2) ->
    joinable_mod_kappa from_
      (RTree addr (L ++ M ++ [RChain cm] ++ R))
      (RTree addr (L ++ M ++ [RChain cm0] ++ R)).
Proof.
  intros from_ addr L M R c1 c2 cm cm0 Hml Hmc Hm0l Hm0c.
  exists (RTree addr (L ++ M ++ [RChain cm] ++ R)),
         (RTree addr (L ++ M ++ [RChain cm0] ++ R)).
  split; [apply RS_refl |]. split; [apply RS_refl |].
  cbn [kappa]. do 2 f_equal. rewrite !map_app. cbn [map kappa].
  rewrite (kappa_ct_of_merge_node cm c1 c2 Hml Hmc).
  rewrite (kappa_ct_of_merge_node cm0 c1 c2 Hm0l Hm0c).
  reflexivity.
Qed.

(** [filter] distributes over [++]. *)
Lemma filter_app_local :
  forall {A} (p : A -> bool) l1 l2,
    filter p (l1 ++ l2) = filter p l1 ++ filter p l2.
Proof.
  intros A p l1 l2. induction l1 as [| x xs IH]; simpl; [reflexivity |].
  destruct (p x); simpl; rewrite IH; reflexivity.
Qed.

(** A leading [RChain] drops from the non-chain filter. *)
Lemma filter_nr_cons_rchain :
  forall c B, filter is_non_rchain (RChain c :: B) = filter is_non_rchain B.
Proof. reflexivity. Qed.

(** The non-chain children of a merge-result / pre-merge child list
    are the same: the [RChain]s drop out. *)
Lemma filter_nr_LMcR :
  forall L M R (c : chain_tree),
    filter is_non_rchain (L ++ M ++ RChain c :: R)
    = filter is_non_rchain L ++ filter is_non_rchain M ++ filter is_non_rchain R.
Proof.
  intros. repeat (rewrite filter_app_local || rewrite filter_nr_cons_rchain).
  reflexivity.
Qed.

Lemma filter_nr_LcMcR :
  forall L M R (c1 c2 : chain_tree),
    filter is_non_rchain (L ++ RChain c1 :: M ++ RChain c2 :: R)
    = filter is_non_rchain L ++ filter is_non_rchain M ++ filter is_non_rchain R.
Proof.
  intros. repeat (rewrite filter_app_local || rewrite filter_nr_cons_rchain).
  reflexivity.
Qed.

(** THE merge-merge key lemma.  Under the AC-complete [kappa], the two
    reducts of a merge-merge critical pair have EQUAL [kappa] -- with no
    positional case analysis and no left-to-right side condition.  Both
    child lists [canonicalize] to (i) the same non-chain children (the
    [RChain]s drop; the shared pre-merge equation transfers the rest)
    and (ii) [op_sort] of the same leaf-operand multiset (both merges
    flatten to a permutation of the pre-merge operands; [op_sort_
    permutation_eq] under linearity/[distinct_op_sigs] erases the
    permutation).  This is what replaces [merge_lr]. *)
Lemma kappa_merge_eq :
  forall addr c1 c2 cm c0 c3 cm0 L M R L0 M0 R0,
    ch_label cm = Merging -> ch_children cm = Some (c1, c2) ->
    ch_label cm0 = Merging -> ch_children cm0 = Some (c0, c3) ->
    L ++ RChain c1 :: (M ++ RChain c2 :: R)
      = L0 ++ RChain c0 :: (M0 ++ RChain c3 :: R0) ->
    distinct_op_sigs
      (flat_map merge_operands
         (flat_map rchain_operand (map kappa (L ++ M ++ RChain cm :: R)))) ->
    kappa (RTree addr (L ++ M ++ RChain cm :: R))
    = kappa (RTree addr (L0 ++ M0 ++ RChain cm0 :: R0)).
Proof.
  intros addr c1 c2 cm c0 c3 cm0 L M R L0 M0 R0
         Hcml Hcmc Hcm0l Hcm0c Heq Hd.
  assert (Hperm : Permutation
    (flat_map merge_operands
       (flat_map rchain_operand (map kappa (L ++ M ++ RChain cm :: R))))
    (flat_map merge_operands
       (flat_map rchain_operand (map kappa (L0 ++ M0 ++ RChain cm0 :: R0))))).
  { eapply perm_trans; [apply canon_ops_perm |].
    eapply perm_trans; [| apply Permutation_sym; apply canon_ops_perm].
    apply Permutation_map.
    eapply perm_trans; [apply (raw_ops_merge_perm L M R c1 c2 cm Hcml Hcmc) |].
    rewrite Heq.
    apply Permutation_sym.
    apply (raw_ops_merge_perm L0 M0 R0 c0 c3 cm0 Hcm0l Hcm0c). }
  assert (Hfilt : filter is_non_rchain (map kappa (L ++ M ++ RChain cm :: R))
                = filter is_non_rchain (map kappa (L0 ++ M0 ++ RChain cm0 :: R0))).
  { rewrite !filter_is_non_rchain_map_kappa. f_equal.
    rewrite !filter_nr_LMcR.
    assert (Hw := f_equal (filter is_non_rchain) Heq).
    rewrite !filter_nr_LcMcR in Hw. exact Hw. }
  cbn [kappa]. f_equal. unfold canonicalize.
  rewrite (op_sort_permutation_eq _ _ Hperm Hd). rewrite Hfilt. reflexivity.
Qed.

(** --- kappa idempotence (canonical-form property) --- *)

Lemma flat_map_rchain_operand_map_RChain :
  forall l, flat_map rchain_operand (map RChain l) = l.
Proof.
  induction l as [| c cs IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma flat_map_rchain_operand_filter_nr :
  forall l, flat_map rchain_operand (filter is_non_rchain l) = [].
Proof.
  induction l as [| x xs IH]; simpl; [reflexivity |].
  destruct x as [t | c | a ch]; simpl; rewrite IH; reflexivity.
Qed.

Lemma filter_nr_map_RChain :
  forall l, filter is_non_rchain (map RChain l) = [].
Proof.
  induction l as [| c cs IH]; simpl; [reflexivity | exact IH].
Qed.

Lemma filter_nr_idem :
  forall l,
    filter is_non_rchain (filter is_non_rchain l) = filter is_non_rchain l.
Proof.
  induction l as [| x xs IH]; simpl; [reflexivity |].
  destruct (is_non_rchain x) eqn:E; simpl;
    [rewrite E; rewrite IH; reflexivity | exact IH].
Qed.

Lemma flat_map_merge_operands_id :
  forall l, (forall o, In o l -> nonmerge_root o) -> flat_map merge_operands l = l.
Proof.
  induction l as [| x xs IH]; intros H; simpl; [reflexivity |].
  rewrite (merge_operands_nonmerge_singleton x (H x (or_introl eq_refl))).
  simpl. rewrite IH; [reflexivity | intros o Ho; apply H; right; exact Ho].
Qed.

Lemma map_kappa_ct_id :
  forall l, (forall o, In o l -> kappa_ct o = o) -> map kappa_ct l = l.
Proof.
  induction l as [| x xs IH]; intros H; simpl; [reflexivity |].
  rewrite (H x (or_introl eq_refl)). rewrite IH;
    [reflexivity | intros o Ho; apply H; right; exact Ho].
Qed.

Lemma map_fix_gen :
  forall {A} (f : A -> A) l, (forall e, In e l -> f e = e) -> map f l = l.
Proof.
  intros A f l H. induction l as [| x xs IH]; simpl; [reflexivity |].
  rewrite (H x (or_introl eq_refl)). rewrite IH;
    [reflexivity | intros e He; apply H; right; exact He].
Qed.

(** Every leaf operand of a canonicalized chain is [kappa_ct]-fixed. *)
Lemma merge_operands_kappa_ct_fixed :
  forall z o, In o (merge_operands (kappa_ct z)) -> kappa_ct o = o.
Proof.
  intros z o Hin. destruct (label_eq_dec (ch_label z) Merging) as [Hm | Hnm].
  - rewrite (kappa_ct_merging_gen z Hm) in Hin.
    rewrite merge_operands_rebuild in Hin.
    + apply in_op_sort in Hin. apply in_map_iff in Hin.
      destruct Hin as [w [Hw _]]. subst o. apply kappa_ct_idem.
    + apply op_sort_nonempty. intro Hc. apply map_eq_nil in Hc.
      exact (merge_operands_nonempty z Hc).
    + intros x Hx. apply in_op_sort in Hx. apply in_map_iff in Hx.
      destruct Hx as [w [Hw Hinw]]. subst x. unfold kappa_ct.
      apply kappa_fuel_nonmerge. exact (merge_operands_nonmerge z w Hinw).
  - rewrite (merge_operands_nonmerge_singleton (kappa_ct z)
               (kappa_fuel_nonmerge (ct_size z) z Hnm)) in Hin.
    destruct Hin as [Heq | []]. subst o. apply kappa_ct_idem.
Qed.

(** Hence every operand in a [kappa]-canonicalized child list's operand
    pool is [kappa_ct]-fixed. *)
Lemma canon_operands_kappa_ct_fixed :
  forall ch o,
    In o (flat_map merge_operands (flat_map rchain_operand (map kappa ch))) ->
    kappa_ct o = o.
Proof.
  intros ch o Hin. rewrite flat_map_rchain_operand_map_kappa in Hin.
  apply in_flat_map in Hin. destruct Hin as [z [Hz Hoin]].
  apply in_map_iff in Hz. destruct Hz as [w [Hw _]]. subst z.
  exact (merge_operands_kappa_ct_fixed w o Hoin).
Qed.

(** [canonicalize] is idempotent: it flattens to non-Merging operands
    that are already [op_sort]ed, and the non-chain children are already
    filtered. *)
Lemma canonicalize_idem :
  forall Z, canonicalize (canonicalize Z) = canonicalize Z.
Proof.
  intros Z. unfold canonicalize.
  rewrite flat_map_app_dist, flat_map_rchain_operand_map_RChain,
          flat_map_rchain_operand_filter_nr, app_nil_r.
  rewrite flat_map_merge_operands_id by
    (intros o Ho; apply in_op_sort in Ho; apply in_flat_map in Ho;
     destruct Ho as [c [_ Hoc]]; exact (merge_operands_nonmerge c o Hoc)).
  rewrite op_sort_idem.
  rewrite filter_app_local, filter_nr_map_RChain, filter_nr_idem.
  reflexivity.
Qed.

(** kappa is idempotent on reduced CFTs. *)
Lemma kappa_idem :
  forall T, kappa (kappa T) = kappa T.
Proof.
  intros T. remember (rcft_size T) as n eqn:Hn. revert T Hn.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros T Hn. destruct T as [t | c | a ch].
  - reflexivity.
  - simpl. f_equal. apply kappa_ct_idem.
  - cbn [kappa]. f_equal.
    assert (Hfix : map kappa (canonicalize (map kappa ch))
                 = canonicalize (map kappa ch)).
    { unfold canonicalize. rewrite map_app. f_equal.
      - rewrite map_map. apply map_ext_in. intros x Hx. simpl. f_equal.
        apply (canon_operands_kappa_ct_fixed ch). apply in_op_sort. exact Hx.
      - apply map_fix_gen. intros e He. apply filter_In in He.
        destruct He as [Hemap _]. apply in_map_iff in Hemap.
        destruct Hemap as [x [Hx Hinx]]. subst e.
        assert (Hlt : rcft_size x < n)
          by (subst n; apply rcft_size_child_lt; exact Hinx).
        exact (IH (rcft_size x) Hlt x eq_refl). }
    rewrite Hfix. apply canonicalize_idem.
Qed.

(** --- Linearity supplies the [distinct_op_sigs] the key lemma needs,
    replacing [merge_lr]. --- *)

(** [distinct_op_sigs] is permutation-invariant. *)
Lemma distinct_op_sigs_perm :
  forall l l', Permutation l l' -> distinct_op_sigs l -> distinct_op_sigs l'.
Proof.
  intros l l' Hp Hd x y Hx Hy Hs. apply Hd;
    [ eapply Permutation_in; [apply Permutation_sym; exact Hp | exact Hx]
    | eapply Permutation_in; [apply Permutation_sym; exact Hp | exact Hy]
    | exact Hs ].
Qed.

(** Flattening chains through [merge_operands] preserves the key list. *)
Lemma flat_map_trace_keys_merge_operands :
  forall L,
    flat_map (fun c => map trace_key (chain_transfers c))
             (flat_map merge_operands L)
    = flat_map (fun c => map trace_key (chain_transfers c)) L.
Proof.
  induction L as [| x xs IH]; simpl; [reflexivity |].
  rewrite flat_map_app_dist. rewrite merge_operands_keys, IH. reflexivity.
Qed.

(** On a linear node, the [kappa_ct]-images of the leaf operands have
    pairwise-distinct signatures.  Their keys are a sub-multiset of the
    node's (all distinct by [linear]); [canonicalize_split] isolates the
    chain part. *)
Lemma linear_distinct_kappa_ct_ops :
  forall a Y,
    linear (RTree a Y) ->
    distinct_op_sigs
      (map kappa_ct (flat_map merge_operands (flat_map rchain_operand Y))).
Proof.
  intros a Y Hlin. apply distinct_op_sigs_of_nodup.
  - intros c Hc. apply in_map_iff in Hc as [op [<- _]].
    apply chain_transfers_nonempty.
  - eapply Permutation_NoDup;
      [ apply Permutation_sym; apply kappa_ct_ops_keys_perm |].
    rewrite flat_map_trace_keys_merge_operands.
    rewrite flat_map_map_comm.
    pose proof (canonicalize_split Y) as Hcs.
    apply (Permutation_map trace_key) in Hcs. rewrite map_app in Hcs.
    unfold linear in Hlin. simpl in Hlin.
    eapply Permutation_NoDup in Hlin; [| apply Permutation_sym; exact Hcs].
    apply NoDup_app_remove_r in Hlin. exact Hlin.
Qed.

(** Two merges on one sibling list: under the AC-complete [kappa] their
    two reducts are already [kappa]-equal ([kappa_merge_eq]); no
    positional case analysis, [merge_lr] replaced by [linear]ity of the
    node (which supplies the shared operand pool's [distinct_op_sigs]
    and IS preserved by [rewrite_step]). *)
Lemma joinable_merge_vs_merge :
  forall from_ addr c1 c2 cm c0 c3 cm0 L M R L0 M0 R0,
    ch_label cm = Merging -> ch_children cm = Some (c1, c2) ->
    ch_label cm0 = Merging -> ch_children cm0 = Some (c0, c3) ->
    L ++ RChain c1 :: (M ++ RChain c2 :: R)
      = L0 ++ RChain c0 :: (M0 ++ RChain c3 :: R0) ->
    linear (RTree addr (L ++ RChain c1 :: (M ++ RChain c2 :: R))) ->
    joinable_mod_kappa from_
      (RTree addr (L ++ M ++ RChain cm :: R))
      (RTree addr (L0 ++ M0 ++ RChain cm0 :: R0)).
Proof.
  intros from_ addr c1 c2 cm c0 c3 cm0 L M R L0 M0 R0
         HcmL HcmC Hcm0L Hcm0C Heq Hlin.
  assert (Hd : distinct_op_sigs
    (flat_map merge_operands
       (flat_map rchain_operand (map kappa (L ++ M ++ RChain cm :: R))))).
  { apply (distinct_op_sigs_perm
             (map kappa_ct
                (flat_map merge_operands
                   (flat_map rchain_operand
                      (L ++ RChain c1 :: (M ++ RChain c2 :: R)))))).
    - eapply perm_trans.
      { apply Permutation_map. apply Permutation_sym.
        apply (raw_ops_merge_perm L M R c1 c2 cm HcmL HcmC). }
      apply Permutation_sym. apply canon_ops_perm.
    - exact (linear_distinct_kappa_ct_ops addr _ Hlin). }
  exists (RTree addr (L ++ M ++ RChain cm :: R)),
         (RTree addr (L0 ++ M0 ++ RChain cm0 :: R0)).
  split; [apply RS_refl |]. split; [apply RS_refl |].
  exact (kappa_merge_eq addr c1 c2 cm c0 c3 cm0 L M R L0 M0 R0
           HcmL HcmC Hcm0L Hcm0C Heq Hd).
Qed.

(** A chaining rule (R6/R12/R10) rewrites the LAST TWO children
    [tail2] to [[RChain c']] for ANY prefix [sib] -- a tail step.  When
    the OTHER rule is a [local_step] acting strictly inside the prefix,
    the two commute: the chaining tail is untouched by the prefix edit
    (it still fires with the edited prefix), and the prefix edit is
    untouched by the chaining (its context just loses the tail).  Both
    orders meet at one reduct, so they join with no [kappa] rewriting. *)
Lemma joinable_tail_vs_local :
  forall from_ addr tail2 c' P mid mid' Q,
    (forall sib, rewrite_step from_ (RTree addr (sib ++ tail2))
                                     (RTree addr (sib ++ [RChain c']))) ->
    local_step from_ mid mid' ->
    joinable_mod_kappa from_
      (RTree addr ((P ++ mid ++ Q) ++ [RChain c']))
      (RTree addr (P ++ mid' ++ Q ++ tail2)).
Proof.
  intros from_ addr tail2 c' P mid mid' Q Hchain Hloc.
  exists (RTree addr (P ++ mid' ++ Q ++ [RChain c'])),
         (RTree addr (P ++ mid' ++ Q ++ [RChain c'])).
  split; [| split; [| reflexivity]].
  - apply rewrite_star_one.
    pose proof (Hloc addr P (Q ++ [RChain c'])) as Hs;
    repeat (rewrite <- app_assoc in Hs || rewrite <- app_comm_cons in Hs);
    repeat (rewrite <- app_assoc || rewrite <- app_comm_cons); exact Hs.
  - apply rewrite_star_one.
    pose proof (Hchain (P ++ mid' ++ Q)) as Hs;
    repeat (rewrite <- app_assoc in Hs || rewrite <- app_comm_cons in Hs);
    repeat (rewrite <- app_assoc || rewrite <- app_comm_cons); exact Hs.
Qed.

(** Chaining (R6/R12, leaf-onto-chain tail [[RLeaf t; RChain c]]) vs
    annotation of a chain [ca].  The leaf is not a chain, so [ca] is
    either the tail chain [c] -- ruled out by the caller's [Hovl] --
    or strictly in the prefix, where the two commute
    ([joinable_tail_vs_local]). *)
Lemma joinable_chain_leaf_vs_annotate :
  forall from_ addr t c c' ca ca' sib La Ra,
    (forall s, rewrite_step from_ (RTree addr (s ++ [RLeaf t; RChain c]))
                                   (RTree addr (s ++ [RChain c']))) ->
    local_step from_ [RChain ca] [RChain ca'] ->
    (ca = c -> False) ->
    sib ++ [RLeaf t; RChain c] = La ++ RChain ca :: Ra ->
    joinable_mod_kappa from_
      (RTree addr (sib ++ [RChain c']))
      (RTree addr (La ++ RChain ca' :: Ra)).
Proof.
  intros from_ addr t c c' ca ca' sib La Ra Hchain Hloc Hovl Heq.
  destruct (list_two_hole _ sib (RLeaf t) [RChain c] La (RChain ca) Ra Heq)
    as [ (HL & Hx & HR) | [ (M & HLM & HRM) | (M & HLM & HRM) ] ].
  - discriminate Hx.
  - (* RChain ca after the leaf : forces ca = c, excluded by Hovl *)
    exfalso.
    assert (Hin : In (RChain ca) [RChain c])
      by (rewrite HRM; apply in_or_app; right; left; reflexivity).
    destruct Hin as [E | []]. injection E as E'. exact (Hovl (eq_sym E')).
  - (* ca strictly in the prefix : commute *)
    subst sib Ra.
    apply (joinable_tail_vs_local from_ addr [RLeaf t; RChain c] c'
             La [RChain ca] [RChain ca'] M Hchain Hloc).
Qed.

(** Chaining (R6/R12, leaf-onto-chain tail) vs a merge [(c1,c2)->cm].
    The merge is a [local_step] on the span [[c1] ++ M ++ [c2]].  Since
    the chaining tail chain [c] is the LAST child, the merge's right
    operand [c2] is either strictly in the prefix (merge in the prefix
    -> [joinable_tail_vs_local]) or is [c] itself ([c2 = c], vacated by
    the caller's [Hovl] -- open-vs-closed for R8/R9/R13, [frame_wf] for
    R7).  Locate the leaf vs [c1], then [c2] vs the leaf. *)
Lemma joinable_chain_leaf_vs_merge :
  forall from_ addr t c c' c1 c2 cm M sib L' R',
    (forall s, rewrite_step from_ (RTree addr (s ++ [RLeaf t; RChain c]))
                                   (RTree addr (s ++ [RChain c']))) ->
    (forall Mx, local_step from_
       ([RChain c1] ++ Mx ++ [RChain c2]) (Mx ++ [RChain cm])) ->
    (c2 = c -> False) ->
    sib ++ [RLeaf t; RChain c] = L' ++ RChain c1 :: (M ++ RChain c2 :: R') ->
    joinable_mod_kappa from_
      (RTree addr (sib ++ [RChain c']))
      (RTree addr (L' ++ M ++ RChain cm :: R')).
Proof.
  intros from_ addr t c c' c1 c2 cm M sib L' R' Hchain Hmrg Hovl Heq.
  destruct (list_two_hole _ sib (RLeaf t) [RChain c]
              L' (RChain c1) (M ++ RChain c2 :: R') Heq)
    as [ (HL & Hx & HR) | [ (K & HLK & HRK) | (K & HLK & HRK) ] ].
  - discriminate Hx.
  - (* leaf left of c1 : impossible, forces c2 = c *)
    exfalso.
    assert (Hin : In (RChain c2) [RChain c])
      by (rewrite HRK; apply in_or_app; right; right;
          apply in_or_app; right; left; reflexivity).
    destruct Hin as [E | []]. injection E as ->. now apply Hovl.
  - (* leaf right of c1 : c1 in prefix; locate c2 vs the leaf *)
    subst sib.
    destruct (list_two_hole _ M (RChain c2) R' K (RLeaf t) [RChain c] HRK)
      as [ (HL2 & Hx2 & HR2) | [ (K2 & HLK2 & HRK2) | (K2 & HLK2 & HRK2) ] ].
    + discriminate Hx2.
    + (* c2 left of leaf : merge span in the prefix, commute *)
      subst K R'.
      pose proof (joinable_tail_vs_local from_ addr [RLeaf t; RChain c] c'
                    L' ([RChain c1] ++ M ++ [RChain c2]) (M ++ [RChain cm]) K2
                    Hchain (Hmrg M)) as J;
      repeat (rewrite <- app_assoc in J || rewrite <- app_comm_cons in J);
      repeat (rewrite <- app_assoc || rewrite <- app_comm_cons); exact J.
    + (* c2 right of leaf : forces c2 = c *)
      exfalso.
      assert (Hin : In (RChain c2) [RChain c])
        by (rewrite HRK2; apply in_or_app; right; left; reflexivity).
      destruct Hin as [E | []]. injection E as ->. now apply Hovl.
Qed.

(** Chaining (R10, chain-chain tail [[RChain c1t; RChain c2t]]) vs
    annotation of [ca]: [ca] is neither tail chain -- excluded by the
    caller's two [Hovl] obligations, which [frame_staged] supplies via
    [chain_seq_annotate_absurd] -- hence it lies in the prefix and the
    two commute. *)
Lemma joinable_chain_seq_vs_annotate :
  forall from_ addr c1t c2t c' ca ca' sib La Ra,
    (forall s, rewrite_step from_ (RTree addr (s ++ [RChain c1t; RChain c2t]))
                                   (RTree addr (s ++ [RChain c']))) ->
    local_step from_ [RChain ca] [RChain ca'] ->
    (ca = c1t -> False) ->
    (ca = c2t -> False) ->
    sib ++ [RChain c1t; RChain c2t] = La ++ RChain ca :: Ra ->
    joinable_mod_kappa from_
      (RTree addr (sib ++ [RChain c']))
      (RTree addr (La ++ RChain ca' :: Ra)).
Proof.
  intros from_ addr c1t c2t c' ca ca' sib La Ra
         Hchain Hloc Hov1 Hov2 Heq.
  destruct (list_two_hole _ sib (RChain c1t) [RChain c2t]
              La (RChain ca) Ra Heq)
    as [ (HL & Hx & HR) | [ (K & HLK & HRK) | (K & HLK & HRK) ] ].
  - exfalso; injection Hx as E1; exact (Hov1 (eq_sym E1)).
  - exfalso.
    assert (Hin : In (RChain ca) [RChain c2t])
      by (rewrite HRK; apply in_or_app; right; left; reflexivity).
    destruct Hin as [E | []]. injection E as E2. exact (Hov2 (eq_sym E2)).
  - subst sib Ra.
    apply (joinable_tail_vs_local from_ addr [RChain c1t; RChain c2t] c'
             La [RChain ca] [RChain ca'] K Hchain Hloc).
Qed.

(** Chaining (R10, chain-chain tail) vs a merge [(c1,c2)->cm].  Like
    [joinable_chain_leaf_vs_merge] but the tail-first is a chain, so the
    merge can overlap either tail chain; the caller's [Hovl] rules out a
    merge operand coinciding with a tail chain (open-vs-closed for
    R8/R9/R13, [frame_wf] for R7). *)
Lemma joinable_chain_seq_vs_merge :
  forall from_ addr c1t c2t c' c1 c2 cm M sib L' R',
    (forall s, rewrite_step from_ (RTree addr (s ++ [RChain c1t; RChain c2t]))
                                   (RTree addr (s ++ [RChain c']))) ->
    (forall Mx, local_step from_
       ([RChain c1] ++ Mx ++ [RChain c2]) (Mx ++ [RChain cm])) ->
    (c2 = c1t \/ c2 = c2t -> False) ->
    sib ++ [RChain c1t; RChain c2t] = L' ++ RChain c1 :: (M ++ RChain c2 :: R') ->
    joinable_mod_kappa from_
      (RTree addr (sib ++ [RChain c']))
      (RTree addr (L' ++ M ++ RChain cm :: R')).
Proof.
  intros from_ addr c1t c2t c' c1 c2 cm M sib L' R' Hchain Hmrg Hovl Heq.
  destruct (list_two_hole _ sib (RChain c1t) [RChain c2t]
              L' (RChain c1) (M ++ RChain c2 :: R') Heq)
    as [ (HL & Hx & HR) | [ (K & HLK & HRK) | (K & HLK & HRK) ] ].
  - (* whole tail: c1=c1t and (from HR) c2=c2t *)
    injection Hx as ->. exfalso. apply Hovl. right.
    assert (Hin : In (RChain c2) [RChain c2t])
      by (rewrite HR; apply in_or_app; right; left; reflexivity).
    destruct Hin as [E | []]. injection E as ->. reflexivity.
  - exfalso. apply Hovl. right.
    assert (Hin : In (RChain c2) [RChain c2t])
      by (rewrite HRK; apply in_or_app; right; right;
          apply in_or_app; right; left; reflexivity).
    destruct Hin as [E | []]. injection E as ->. reflexivity.
  - subst sib.
    destruct (list_two_hole _ M (RChain c2) R' K (RChain c1t) [RChain c2t] HRK)
      as [ (HL2 & Hx2 & HR2) | [ (K2 & HLK2 & HRK2) | (K2 & HLK2 & HRK2) ] ].
    + injection Hx2 as ->. exfalso. apply Hovl. left. reflexivity.
    + subst K R'.
      pose proof (joinable_tail_vs_local from_ addr [RChain c1t; RChain c2t] c'
                    L' ([RChain c1] ++ M ++ [RChain c2]) (M ++ [RChain cm]) K2
                    Hchain (Hmrg M)) as J;
      repeat (rewrite <- app_assoc in J || rewrite <- app_comm_cons in J);
      repeat (rewrite <- app_assoc || rewrite <- app_comm_cons); exact J.
    + exfalso. apply Hovl. right.
      assert (Hin : In (RChain c2) [RChain c2t])
        by (rewrite HRK2; apply in_or_app; right; left; reflexivity).
      destruct Hin as [E | []]. injection E as ->. reflexivity.
Qed.

(** The frame_wf discharge of a chaining-vs-PARALLEL-merge (R7/R13)
    overlap: a merge operand [cm2] coincides with a chaining tail
    operand ([c1t] or [c2t]).  The merge's own decomposition witnesses
    [has_twin] (its two operands share endpoints), while the R10 tail
    makes the shared chain a chaining operand ([tail_chainable c2t] /
    [left_tail_chainable c1t]); [frame_wf] forbids the two together. *)
Lemma chain_parallel_merge_absurd :
  forall cs siblings c1t c2t L' cm1 M cm2 R',
    frame_wf cs ->
    cs = siblings ++ [RChain c1t; RChain c2t] ->
    cs = L' ++ RChain cm1 :: (M ++ RChain cm2 :: R') ->
    ch_destination c1t = ch_origin c2t ->
    ch_origin cm1 = ch_origin cm2 ->
    ch_destination cm1 = ch_destination cm2 ->
    (cm2 = c1t \/ cm2 = c2t) -> False.
Proof.
  intros cs siblings c1t c2t L' cm1 M cm2 R'
         [Hfw _] Htail Hmerge Hadj Ho Hd Hovl.
  assert (Htwin : has_twin cs cm2).
  { exists L', M, R', cm1. split; [rewrite Hmerge; reflexivity |].
    split; [exact Ho | exact Hd]. }
  destruct Hovl as [E | E]; subst cm2.
  - apply (Hfw c1t);
      [ right; exists siblings, c2t; split; [exact Htail | exact Hadj]
      | exact Htwin ].
  - apply (Hfw c2t);
      [ left; exists siblings, (RChain c1t); split; [exact Htail | exact Hadj]
      | exact Htwin ].
Qed.

(** Leaf-tail variant of [chain_parallel_merge_absurd] (R6/R12 tail
    [[RLeaf t; RChain c]]): the single chain operand [c] is the last
    child ([tail_chainable]); a parallel merge coinciding with it
    contradicts [frame_wf].  [cs] is generic (the frame's child list in
    either spelling); [Htail]/[Hmerge] locate it. *)
Lemma chain_leaf_parallel_merge_absurd :
  forall cs siblings t c L' cm1 M cm2 R',
    frame_wf cs ->
    cs = siblings ++ [RLeaf t; RChain c] ->
    cs = L' ++ RChain cm1 :: (M ++ RChain cm2 :: R') ->
    chain_adj (RLeaf t) c ->
    ch_origin cm1 = ch_origin cm2 ->
    ch_destination cm1 = ch_destination cm2 ->
    cm2 = c -> False.
Proof.
  intros cs siblings t c L' cm1 M cm2 R' [Hfw _] Htail Hmerge Hadj Ho Hd E.
  assert (Htwin : has_twin cs cm2)
    by (exists L', M, R', cm1; split; [rewrite Hmerge; reflexivity |];
        split; [exact Ho | exact Hd]).
  subst cm2. apply (Hfw c);
    [ left; exists siblings, (RLeaf t); split; [exact Htail | exact Hadj]
    | exact Htwin ].
Qed.

(** The [frame_staged] discharge of a chaining-vs-ANNOTATION (R14/R15)
    overlap: the annotation operand [ca] coincides with the chain [c]
    that R6/R12 extends.  The tail makes [c] a chaining operand
    ([tail_chainable]) and the annotation rule's own premises make it an
    [annot_redex]; [frame_staged] forbids the two together. *)
Lemma chain_leaf_annotate_absurd :
  forall cs siblings t c ca,
    frame_wf cs ->
    cs = siblings ++ [RLeaf t; RChain c] ->
    chain_adj (RLeaf t) c ->
    ch_origin ca = ch_destination ca ->
    is_labeled (ch_label ca) = false ->
    ca = c -> False.
Proof.
  intros cs siblings t c ca [_ Hst] Htail Hadj Hclosed Hunlab E.
  subst ca. apply (Hst c);
    [ left; exists siblings, (RLeaf t); split; [exact Htail | exact Hadj]
    | split; [exact Hclosed | exact Hunlab] ].
Qed.

(** Sequential-tail variant of [chain_leaf_annotate_absurd] (R10 tail
    [[RChain c1t; RChain c2t]]): the left chain is
    [left_tail_chainable], the right one is [tail_chainable], so
    [frame_staged] forbids either of them from being an annotation
    redex. *)
Lemma chain_seq_annotate_absurd :
  forall cs siblings c1t c2t ca,
    frame_wf cs ->
    cs = siblings ++ [RChain c1t; RChain c2t] ->
    ch_destination c1t = ch_origin c2t ->
    ch_origin ca = ch_destination ca ->
    is_labeled (ch_label ca) = false ->
    (ca = c1t \/ ca = c2t) -> False.
Proof.
  intros cs siblings c1t c2t ca [_ Hst] Htail Hadj Hclosed Hunlab Hovl.
  destruct Hovl as [E | E]; subst ca.
  - apply (Hst c1t);
      [ right; left; exists siblings, c2t; split; [exact Htail | exact Hadj]
      | split; [exact Hclosed | exact Hunlab] ].
  - apply (Hst c2t);
      [ left; exists siblings, (RChain c1t); split; [exact Htail | exact Hadj]
      | split; [exact Hclosed | exact Hunlab] ].
Qed.

(** The [frame_staged] discharge of a MERGE-vs-annotation overlap: the
    annotation operand [ca] coincides with one of the merge operands.
    Every merge rule gives its two operands a common origin and a
    common destination, so each is a [parallel_sibling] of the other
    (the left one via the second disjunct, the right one via the
    first); the annotation rule's own premises make [ca] an
    [annot_redex]; [frame_staged] forbids the two together.  This is
    what replaces the [is_labeled] premises R8, R9 and R13 used to
    carry and the implementation never tests. *)
Lemma merge_annotate_absurd :
  forall cs L' c1 M c2 R' ca,
    frame_wf cs ->
    cs = L' ++ RChain c1 :: (M ++ RChain c2 :: R') ->
    ch_origin c1 = ch_origin c2 ->
    ch_destination c1 = ch_destination c2 ->
    ch_origin ca = ch_destination ca ->
    is_labeled (ch_label ca) = false ->
    (ca = c1 \/ ca = c2) -> False.
Proof.
  intros cs L' c1 M c2 R' ca [_ Hst] Hspan Ho Hd Hclosed Hunlab Hovl.
  destruct Hovl as [E | E]; subst ca.
  - apply (Hst c1);
      [ right; right; exists L', M, R', c2; split;
          [ right; exact Hspan
          | split; [exact (eq_sym Ho) | exact (eq_sym Hd)] ]
      | split; [exact Hclosed | exact Hunlab] ].
  - apply (Hst c2);
      [ right; right; exists L', M, R', c1; split;
          [ left; exact Hspan | split; [exact Ho | exact Hd] ]
      | split; [exact Hclosed | exact Hunlab] ].
Qed.

(** Two lists with equal two-element tails are equal componentwise
    (right-injectivity of [++] applied twice).  Used to reconcile the
    two decompositions of a chaining-vs-chaining critical pair, whose
    redexes are the SAME last two children. *)
Lemma tail2_eq :
  forall (A : Type) (l1 l2 : list A) (x1 y1 x2 y2 : A),
    l1 ++ [x1; y1] = l2 ++ [x2; y2] -> l1 = l2 /\ x1 = x2 /\ y1 = y2.
Proof.
  intros A l1 l2 x1 y1 x2 y2 H.
  assert (H' : (l1 ++ [x1]) ++ [y1] = (l2 ++ [x2]) ++ [y2])
    by (rewrite <- !app_assoc; exact H).
  apply app_inj_tail in H'. destruct H' as [H1 Hy].
  apply app_inj_tail in H1. destruct H1 as [Hl Hx].
  split; [exact Hl | split; [exact Hx | exact Hy]].
Qed.

(** Chaining-vs-chaining on a leaf-onto-chain tail (R6/R12 vs R6/R12):
    the two redexes are the SAME last two children, so both fire on the
    same [(t,c)] and the prepend/append builder is deterministic (the
    disjuncts are mutually exclusive on [tr_dest t = ch_origin c]).
    [decompose] flattens each rule's premise conjunction (R6 and R12
    differ only in extra token conjuncts), so the same tactic covers all
    four rule pairings. *)
Ltac leaf_chain_det :=
  match goal with
  | H : _ ++ [RLeaf _; RChain _] = _ ++ [RLeaf _; RChain _] |- _ =>
      apply tail2_eq in H; destruct H as [? [Ht Hc]];
      injection Ht as ->; injection Hc as ->; subst
  end;
  match goal with
  | Hd1 : (tr_dest ?tt = ch_origin ?cc /\ _) \/ _,
    Hd2 : (tr_dest ?tt = ch_origin ?cc /\ _) \/ _ |- _ =>
      destruct Hd1 as [Hp1 | Hp1]; destruct Hd2 as [Hp2 | Hp2];
      decompose [and] Hp1; decompose [and] Hp2;
      solve [ match goal with
              | Ha : _ = prepend_leaf_chain ?t ?c,
                Hb : _ = prepend_leaf_chain ?t ?c |- _ =>
                  rewrite Ha, Hb; apply joinable_mod_kappa_refl
              | Ha : _ = append_leaf_chain ?c ?t,
                Hb : _ = append_leaf_chain ?c ?t |- _ =>
                  rewrite Ha, Hb; apply joinable_mod_kappa_refl
              end
            | exfalso; congruence ]
  end.

(** Discharge an annotate-vs-merge root-root cell: build the two
    [local_step] facts from the inverted rule premises and appeal to
    [joinable_annotate_vs_merge].  [annlem] is [local_annotate_arb] or
    [local_annotate_cyc]; [mergelem] is one of the four [local_merge_*].
    The two overlap obligations go to [merge_annotate_absurd] under the
    node's [frame_staged]; the merge operands' shared endpoints come
    from the merge rule's own inversion, by [congruence] for R9, which
    states them through the two closures. *)
Ltac get_hfw :=
  match goal with Hwf : wf_rcft ?f (RTree ?a ?cs) |- _ =>
    pose proof (wf_rcft_tree_inv f a cs Hwf) as [Hfw _] end.

Ltac merge_annot side :=
  let E := fresh "E" in
  let Hf := fresh "Hf" in
  intro E;
  match goal with
  | Hwf : wf_rcft ?f (RTree ?a ?cs) |- _ =>
      pose proof (wf_rcft_tree_inv f a cs Hwf) as [Hf _]
  end;
  eapply merge_annotate_absurd;
    [ | | | | | | side; exact E ];
    [ exact Hf
    | solve [reflexivity | eassumption | symmetry; eassumption
            | symmetry; match goal with H : _ = _ |- _ => exact H end
            | match goal with H : _ = _ |- _ => exact H end]
    | solve [eassumption | symmetry; eassumption | congruence]
    | solve [eassumption | symmetry; eassumption | congruence]
    | solve [eassumption | symmetry; eassumption]
    | solve [eassumption | assumption] ].

Ltac ann_merge annlem mergelem :=
  eapply joinable_annotate_vs_merge;
    [ | | | | solve [symmetry; eassumption | eassumption] ];
    [ apply annlem; solve [assumption | reflexivity]
    | intro Mx; apply mergelem; solve [assumption | reflexivity]
    | merge_annot ltac:(left)
    | merge_annot ltac:(right) ].

(** Discharge a merge-vs-merge root-root cell via [joinable_merge_vs_merge]:
    build both merge [local_step]s from the inverted rule premises
    ([mlemA]/[mlemB] the two [local_merge_*]), take the field facts and
    the children equation from the inversions, and the [merge_lr]
    left-to-right order from the node's [wf_rcft] ([Hwf]).  Solve the two
    [ch_children] goals first (they pin the operand metavariables). *)
(** mm_cell: discharge a merge-vs-merge cell via [joinable_merge_vs_
    merge].  [linear] of the node comes from [wf_rcft_tree_inv]; the
    field facts and the shared children equation come from the two rule
    inversions.  The [mlemA]/[mlemB] arguments are vestigial (the join no
    longer needs the operand [local_step]s); kept so the 16 call sites
    need no edit.  Field facts are discharged first to pin the merge
    operands, then the equation to pin the split. *)
Ltac mm_cell mlemA mlemB :=
  match goal with
  | Hwf : wf_rcft ?f (RTree ?a ?cs) |- _ =>
      let Hlin := fresh "Hlin" in
      pose proof (wf_rcft_tree_inv f a cs Hwf) as [_ [Hlin _]];
      eapply joinable_merge_vs_merge;
        [ | eassumption | | eassumption
        | solve [eassumption | symmetry; eassumption] | ];
        [ eassumption | eassumption | exact Hlin ]
  end.

(** O3: local confluence modulo kappa over well-formed terms.
    Well-founded induction on [rcft_size]; a [RS_lift] step is
    handled by [lc_lift_vs], an [RS_under] step by [lc_under_vs]
    (its child-confluence hypothesis is the WF induction hypothesis
    pre-applied to the child, whose [wf_rcft] comes from
    [wf_rcft_tree_inv]); when both steps are root rules the
    root-root critical-pair analysis applies. *)
(* --- O3 cell-closing tactics: factor the critical-pair boilerplate
   that recurs across the R6/R7/R10/R12/R13 merge cells of the
   assembly below.  Each reproduces the exact inline block it
   replaces: [leaf_adj] derives the adjacency disjunction [Hadj],
   [get_hfw] extracts the frame-well-formedness [Hfw], and
   [leaf_twin]/[seq_twin] discharge the parallel-merge twin as absurd
   under [frame_wf]. --- *)
Ltac leaf_adj :=
  match goal with
  | H : (tr_dest ?t = ch_origin ?c /\ _) \/
        (ch_destination ?c = tr_source ?t /\ _) |- _ =>
      assert (Hadj : tr_dest t = ch_origin c \/
                     ch_destination c = tr_source t)
        by (destruct H as [[HH _] | [HH _]]; [left | right]; exact HH)
  end.

Ltac leaf_twin Hfw Hadj :=
  let E := fresh "E" in
  intro E; eapply chain_leaf_parallel_merge_absurd;
    [ exact Hfw
    | solve [reflexivity | eassumption | symmetry; eassumption]
    | solve [reflexivity | eassumption | symmetry; eassumption]
    | exact Hadj
    | solve [eassumption | symmetry; eassumption | assumption
            | symmetry; assumption | congruence]
    | solve [eassumption | symmetry; eassumption | assumption
            | symmetry; assumption | congruence]
    | exact E ].

Ltac leaf_annot Hfw Hadj :=
  let E := fresh "E" in
  intro E; eapply chain_leaf_annotate_absurd;
    [ exact Hfw
    | solve [reflexivity | eassumption | symmetry; eassumption]
    | exact Hadj
    | solve [eassumption | symmetry; eassumption | assumption
            | symmetry; assumption | congruence]
    | solve [eassumption | assumption]
    | exact E ].

Ltac seq_annot side :=
  let E := fresh "E" in
  let Hf := fresh "Hf" in
  intro E;
  match goal with
  | Hwf : wf_rcft ?f (RTree ?a ?cs) |- _ =>
      pose proof (wf_rcft_tree_inv f a cs Hwf) as [Hf _]
  end;
  eapply chain_seq_annotate_absurd;
    [ | | | | | side; exact E ];
    [ exact Hf
    | solve [reflexivity | eassumption | symmetry; eassumption
            | symmetry; match goal with H : _ = _ |- _ => exact H end
            | match goal with H : _ = _ |- _ => exact H end]
    | solve [eassumption | symmetry; eassumption]
    | solve [eassumption | symmetry; eassumption]
    | solve [eassumption | assumption] ].

Ltac seq_twin Hfw :=
  let Hc := fresh "Hc" in
  intro Hc; eapply chain_parallel_merge_absurd;
    [ | | | | | | exact Hc ];
    [ exact Hfw
    | solve [reflexivity | eassumption | symmetry; eassumption]
    | solve [reflexivity | eassumption | symmetry; eassumption]
    | solve [eassumption | symmetry; eassumption]
    | solve [eassumption | symmetry; eassumption | congruence]
    | solve [eassumption | symmetry; eassumption | congruence] ].

Lemma local_confluent_mod_kappa_holds :
  forall from_ T, wf_rcft from_ T ->
    forall T1 T2,
      rewrite_step from_ T T1 -> rewrite_step from_ T T2 ->
      joinable_mod_kappa from_ T1 T2.
Proof.
  intros from_.
  assert (KEY : forall n T, rcft_size T = n -> wf_rcft from_ T ->
             forall T1 T2,
               rewrite_step from_ T T1 -> rewrite_step from_ T T2 ->
               joinable_mod_kappa from_ T1 T2).
  { intro n. induction n as [n IH] using (well_founded_induction lt_wf).
    intros T Hn Hwf T1 T2 H1 H2.
    pose proof H1 as G1.
    inversion H1; subst.
    - (* R1 *) exact (local_confluence_two_leaf from_ _ _ _ _ _ G1 H2).
    - (* R2 *) exact (local_confluence_two_leaf from_ _ _ _ _ _ G1 H2).
    - (* R3 *) exact (local_confluence_two_leaf from_ _ _ _ _ _ G1 H2).
    - (* R4 *) exact (local_confluence_two_leaf from_ _ _ _ _ _ G1 H2).
    - (* R5 *) exact (local_confluence_two_leaf from_ _ _ _ _ _ G1 H2).
    - (* R6 *)
      inversion H2; subst;
        try two_leaf_contra; try (sym_lift G1); try (sym_under G1 IH).
      + leaf_chain_det. (* vs R6 : deterministic builder *)
      + leaf_chain_det. (* vs R12 : deterministic builder *)
      + (* vs R10 : R10's chain-first tail vs R6's leaf-first tail *)
        exfalso.
        match goal with
        | H : _ ++ [RChain _; RChain _] = _ ++ [RLeaf _; RChain _] |- _ =>
            apply tail2_eq in H; destruct H as [_ [Hbad _]]; discriminate Hbad
        end.
      + (* vs R7 : parallel merge, vacated by frame_wf leaf twin *)
        leaf_adj;
        get_hfw;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_leaf_chain from_ t c c' addr s);
              solve [assumption | reflexivity]
          | intro Mx; apply local_merge_endpoints; solve [assumption | reflexivity | eassumption | symmetry; eassumption]
          | leaf_twin Hfw Hadj ].
      + (* vs R8 : parallel merge, vacated by frame_wf leaf twin *)
        leaf_adj;
        get_hfw;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_leaf_chain from_ t c c' addr s);
              solve [assumption | reflexivity]
          | intro Mx; apply local_merge_add; solve [assumption | reflexivity]
          | leaf_twin Hfw Hadj ].
      + (* vs R9 : parallel merge, vacated by frame_wf leaf twin *)
        leaf_adj;
        get_hfw;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_leaf_chain from_ t c c' addr s);
              solve [assumption | reflexivity]
          | intro Mx; apply local_merge_closed_R9; solve [assumption | reflexivity]
          | leaf_twin Hfw Hadj ].
      + (* vs R13 : parallel merge, vacated by frame_wf leaf twin *)
        leaf_adj;
        get_hfw;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_leaf_chain from_ t c c' addr s);
              solve [assumption | reflexivity]
          | intro Mx; apply local_merge_node; solve [assumption | reflexivity]
          | leaf_twin Hfw Hadj ].
      + (* vs R14 : annotation redex, vacated by frame_staged *)
        leaf_adj;
        get_hfw;
        eapply joinable_chain_leaf_vs_annotate;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_leaf_chain from_ t c c' addr s);
              solve [assumption | reflexivity]
          | apply local_annotate_arb; solve [assumption | reflexivity]
          | leaf_annot Hfw Hadj ].
      + (* vs R15 : annotation redex, vacated by frame_staged *)
        leaf_adj;
        get_hfw;
        eapply joinable_chain_leaf_vs_annotate;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_leaf_chain from_ t c c' addr s);
              solve [assumption | reflexivity]
          | apply local_annotate_cyc; solve [assumption | reflexivity]
          | leaf_annot Hfw Hadj ].
    - (* R12 *)
      inversion H2; subst;
        try two_leaf_contra; try (sym_lift G1); try (sym_under G1 IH).
      + leaf_chain_det. (* vs R6 *)
      + leaf_chain_det. (* vs R12 *)
      + (* vs R10 : R10's chain-first tail vs R12's leaf-first tail *)
        exfalso.
        match goal with
        | H : _ ++ [RChain _; RChain _] = _ ++ [RLeaf _; RChain _] |- _ =>
            apply tail2_eq in H; destruct H as [_ [Hbad _]]; discriminate Hbad
        end.
      + (* vs R7 : parallel merge, frame_wf leaf twin *)
        leaf_adj;
        get_hfw;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_node_leaf_chain from_ t c c' addr s);
              solve [assumption | reflexivity]
          | intro Mx; apply local_merge_endpoints; solve [assumption | reflexivity | eassumption | symmetry; eassumption]
          | leaf_twin Hfw Hadj ].
      + (* vs R8 : parallel merge, frame_wf leaf twin *)
        leaf_adj;
        get_hfw;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_node_leaf_chain from_ t c c' addr s);
              solve [assumption | reflexivity]
          | intro Mx; apply local_merge_add; solve [assumption | reflexivity]
          | leaf_twin Hfw Hadj ].
      + (* vs R9 : parallel merge, frame_wf leaf twin *)
        leaf_adj;
        get_hfw;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_node_leaf_chain from_ t c c' addr s);
              solve [assumption | reflexivity]
          | intro Mx; apply local_merge_closed_R9; solve [assumption | reflexivity]
          | leaf_twin Hfw Hadj ].
      + (* vs R13 : parallel merge, frame_wf leaf twin *)
        leaf_adj;
        get_hfw;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_node_leaf_chain from_ t c c' addr s);
              solve [assumption | reflexivity]
          | intro Mx; apply local_merge_node; solve [assumption | reflexivity]
          | leaf_twin Hfw Hadj ].
      + (* vs R14 : annotation redex, vacated by frame_staged *)
        leaf_adj;
        get_hfw;
        eapply joinable_chain_leaf_vs_annotate;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_node_leaf_chain from_ t c c' addr s);
              solve [assumption | reflexivity]
          | apply local_annotate_arb; solve [assumption | reflexivity]
          | leaf_annot Hfw Hadj ].
      + (* vs R15 : annotation redex, vacated by frame_staged *)
        leaf_adj;
        get_hfw;
        eapply joinable_chain_leaf_vs_annotate;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_node_leaf_chain from_ t c c' addr s);
              solve [assumption | reflexivity]
          | apply local_annotate_cyc; solve [assumption | reflexivity]
          | leaf_annot Hfw Hadj ].
    - (* R10 *)
      inversion H2; subst;
        try two_leaf_contra; try (sym_lift G1); try (sym_under G1 IH).
      + (* vs R6 : R6's leaf-first tail clashes with R10's chain-first tail *)
        exfalso.
        match goal with
        | H : _ ++ [RLeaf _; RChain _] = _ ++ [RChain _; RChain _] |- _ =>
            apply tail2_eq in H; destruct H as [_ [Hbad _]]; discriminate Hbad
        end.
      + (* vs R12 : same clash as R6 *)
        exfalso.
        match goal with
        | H : _ ++ [RLeaf _; RChain _] = _ ++ [RChain _; RChain _] |- _ =>
            apply tail2_eq in H; destruct H as [_ [Hbad _]]; discriminate Hbad
        end.
      + (* vs R10 : same last-two, c' = seq_chain is deterministic -> refl *)
        match goal with
        | H : _ ++ [RChain _; RChain _] = _ ++ [RChain _; RChain _] |- _ =>
            apply tail2_eq in H; destruct H as [Hs [Hx Hy]];
            injection Hx as ->; injection Hy as ->; subst
        end;
        apply joinable_mod_kappa_refl.
      + (* vs R7 : parallel merge, vacated by frame_wf twin *)
        get_hfw;
        eapply joinable_chain_seq_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_chain_seq from_ c1 c2 (seq_chain c1 c2) addr s);
              solve [assumption | reflexivity]
          | intro Mx; apply local_merge_endpoints; solve [assumption | reflexivity | eassumption | symmetry; eassumption]
          | seq_twin Hfw ].
      + (* vs R8 : parallel merge, vacated by frame_wf twin *)
        get_hfw;
        eapply joinable_chain_seq_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_chain_seq from_ c1 c2 (seq_chain c1 c2) addr s);
              solve [assumption | reflexivity]
          | intro Mx; apply local_merge_add; solve [assumption | reflexivity]
          | seq_twin Hfw ].
      + (* vs R9 : parallel merge, vacated by frame_wf twin *)
        get_hfw;
        eapply joinable_chain_seq_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_chain_seq from_ c1 c2 (seq_chain c1 c2) addr s);
              solve [assumption | reflexivity]
          | intro Mx; apply local_merge_closed_R9; solve [assumption | reflexivity]
          | seq_twin Hfw ].
      + (* vs R13 : parallel merge, vacated by frame_wf twin *)
        get_hfw;
        eapply joinable_chain_seq_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_chain_seq from_ c1 c2 (seq_chain c1 c2) addr s);
              solve [assumption | reflexivity]
          | intro Mx; apply local_merge_node; solve [assumption | reflexivity]
          | seq_twin Hfw ].
      + (* vs R14 *)
        eapply joinable_chain_seq_vs_annotate;
          [ | | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_chain_seq from_ c1 c2 (seq_chain c1 c2) addr s);
              solve [assumption | reflexivity]
          | apply local_annotate_arb; solve [assumption | reflexivity]
          | seq_annot ltac:(left) | seq_annot ltac:(right) ].
      + (* vs R15 *)
        eapply joinable_chain_seq_vs_annotate;
          [ | | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply (RS_chain_seq from_ c1 c2 (seq_chain c1 c2) addr s);
              solve [assumption | reflexivity]
          | apply local_annotate_cyc; solve [assumption | reflexivity]
          | seq_annot ltac:(left) | seq_annot ltac:(right) ].
    - (* R11 *) exact (local_confluence_two_leaf from_ _ _ _ _ _ G1 H2).
    - (* lift *)
      match goal with
      | Hfl : Forall _ ?ch, Hok : lift_children_ok ?ch |- _ =>
          exact (lc_lift_vs from_ _ _ ch _ T2 Hfl Hok H2)
      end.
    - (* R7 *)
      inversion H2; subst;
        try two_leaf_contra; try (sym_lift G1); try (sym_under G1 IH).
      + (* vs R6 : chaining H2, sym of chain_leaf_vs_merge (parallel, frame_wf) *)
        leaf_adj;
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_leaf_chain; solve [assumption | reflexivity]
          | intro Mx; apply local_merge_endpoints; solve [assumption | reflexivity | eassumption | symmetry; eassumption]
          | leaf_twin Hfw Hadj ].
      + (* vs R12 *)
        leaf_adj;
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_node_leaf_chain; solve [assumption | reflexivity]
          | intro Mx; apply local_merge_endpoints; solve [assumption | reflexivity | eassumption | symmetry; eassumption]
          | leaf_twin Hfw Hadj ].
      + (* vs R10 *)
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_seq_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_chain_seq; solve [assumption | reflexivity]
          | intro Mx; apply local_merge_endpoints; solve [assumption | reflexivity | eassumption | symmetry; eassumption]
          | seq_twin Hfw ].
      + mm_cell local_merge_endpoints local_merge_endpoints. (* vs R7 *)
      + mm_cell local_merge_endpoints local_merge_add. (* vs R8 *)
      + mm_cell local_merge_endpoints local_merge_closed_R9. (* vs R9 *)
      + mm_cell local_merge_endpoints local_merge_node. (* vs R13 *)
      + apply joinable_mod_kappa_sym;
        ann_merge local_annotate_arb local_merge_endpoints. (* vs R14 *)
      + apply joinable_mod_kappa_sym;
        ann_merge local_annotate_cyc local_merge_endpoints. (* vs R15 *)
    - (* R8 *)
      inversion H2; subst;
        try two_leaf_contra; try (sym_lift G1); try (sym_under G1 IH).
      + (* vs R6 : chaining H2, sym of chain_leaf_vs_merge (frame_wf twin) *)
        leaf_adj;
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_leaf_chain; solve [assumption | reflexivity]
          | intro Mx; apply local_merge_add; solve [assumption | reflexivity]
          | leaf_twin Hfw Hadj ].
      + (* vs R12 *)
        leaf_adj;
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_node_leaf_chain; solve [assumption | reflexivity]
          | intro Mx; apply local_merge_add; solve [assumption | reflexivity]
          | leaf_twin Hfw Hadj ].
      + (* vs R10 : parallel merge, vacated by frame_wf twin *)
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_seq_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_chain_seq; solve [assumption | reflexivity]
          | intro Mx; apply local_merge_add; solve [assumption | reflexivity]
          | seq_twin Hfw ].
      + mm_cell local_merge_add local_merge_endpoints. (* vs R7 *)
      + mm_cell local_merge_add local_merge_add. (* vs R8 *)
      + mm_cell local_merge_add local_merge_closed_R9. (* vs R9 *)
      + mm_cell local_merge_add local_merge_node. (* vs R13 *)
      + apply joinable_mod_kappa_sym;
        ann_merge local_annotate_arb local_merge_add. (* vs R14 *)
      + apply joinable_mod_kappa_sym;
        ann_merge local_annotate_cyc local_merge_add. (* vs R15 *)
    - (* R9 *)
      inversion H2; subst;
        try two_leaf_contra; try (sym_lift G1); try (sym_under G1 IH).
      + (* vs R6 : chaining H2, sym of chain_leaf_vs_merge (frame_wf twin) *)
        leaf_adj;
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_leaf_chain; solve [assumption | reflexivity]
          | intro Mx; apply local_merge_closed_R9; solve [assumption | reflexivity]
          | leaf_twin Hfw Hadj ].
      + (* vs R12 *)
        leaf_adj;
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_node_leaf_chain; solve [assumption | reflexivity]
          | intro Mx; apply local_merge_closed_R9; solve [assumption | reflexivity]
          | leaf_twin Hfw Hadj ].
      + (* vs R10 : parallel merge, vacated by frame_wf twin *)
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_seq_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_chain_seq; solve [assumption | reflexivity]
          | intro Mx; apply local_merge_closed_R9; solve [assumption | reflexivity]
          | seq_twin Hfw ].
      + mm_cell local_merge_closed_R9 local_merge_endpoints. (* vs R7 *)
      + mm_cell local_merge_closed_R9 local_merge_add. (* vs R8 *)
      + mm_cell local_merge_closed_R9 local_merge_closed_R9. (* vs R9 *)
      + mm_cell local_merge_closed_R9 local_merge_node. (* vs R13 *)
      + apply joinable_mod_kappa_sym;
        ann_merge local_annotate_arb local_merge_closed_R9. (* vs R14 *)
      + apply joinable_mod_kappa_sym;
        ann_merge local_annotate_cyc local_merge_closed_R9. (* vs R15 *)
    - (* R13 *)
      inversion H2; subst;
        try two_leaf_contra; try (sym_lift G1); try (sym_under G1 IH).
      + (* vs R6 : chaining H2, sym of chain_leaf_vs_merge (parallel, frame_wf) *)
        leaf_adj;
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_leaf_chain; solve [assumption | reflexivity]
          | intro Mx; apply local_merge_node; solve [assumption | reflexivity]
          | leaf_twin Hfw Hadj ].
      + (* vs R12 *)
        leaf_adj;
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_leaf_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_node_leaf_chain; solve [assumption | reflexivity]
          | intro Mx; apply local_merge_node; solve [assumption | reflexivity]
          | leaf_twin Hfw Hadj ].
      + (* vs R10 *)
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_seq_vs_merge;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_chain_seq; solve [assumption | reflexivity]
          | intro Mx; apply local_merge_node; solve [assumption | reflexivity]
          | seq_twin Hfw ].
      + mm_cell local_merge_node local_merge_endpoints. (* vs R7 *)
      + mm_cell local_merge_node local_merge_add. (* vs R8 *)
      + mm_cell local_merge_node local_merge_closed_R9. (* vs R9 *)
      + mm_cell local_merge_node local_merge_node. (* vs R13 *)
      + apply joinable_mod_kappa_sym;
        ann_merge local_annotate_arb local_merge_node. (* vs R14 *)
      + apply joinable_mod_kappa_sym;
        ann_merge local_annotate_cyc local_merge_node. (* vs R15 *)
    - (* R14 *)
      inversion H2; subst;
        try two_leaf_contra; try (sym_lift G1); try (sym_under G1 IH).
      + (* vs R6 : chaining H2, sym of chain_leaf_vs_annotate *)
        leaf_adj;
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_leaf_vs_annotate;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_leaf_chain; solve [assumption | reflexivity]
          | apply local_annotate_arb; solve [assumption | reflexivity]
          | leaf_annot Hfw Hadj ].
      + (* vs R12 *)
        leaf_adj;
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_leaf_vs_annotate;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_node_leaf_chain; solve [assumption | reflexivity]
          | apply local_annotate_arb; solve [assumption | reflexivity]
          | leaf_annot Hfw Hadj ].
      + (* vs R10 *)
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_seq_vs_annotate;
          [ | | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_chain_seq; solve [assumption | reflexivity]
          | apply local_annotate_arb; solve [assumption | reflexivity]
          | seq_annot ltac:(left) | seq_annot ltac:(right) ].
      + ann_merge local_annotate_arb local_merge_endpoints. (* vs R7 *)
      + ann_merge local_annotate_arb local_merge_add. (* vs R8 *)
      + ann_merge local_annotate_arb local_merge_closed_R9. (* vs R9 *)
      + ann_merge local_annotate_arb local_merge_node. (* vs R13 *)
      + (* vs R14 *)
        match goal with
        | Heq : ?L0 ++ RChain ?c0 :: ?R0 = ?Lc ++ RChain ?cc :: ?Rc |- _ =>
            destruct (list_two_hole _ L0 (RChain c0) R0 Lc (RChain cc) Rc Heq)
              as [ (HL & Hx & HR) | [ (Mm & HLM & HRM) | (Mm & HLM & HRM) ] ]
        end.
        * (* same chain *) injection Hx as ->; subst; apply joinable_mod_kappa_refl.
        * (* c0 before c *)
          subst; rewrite <- !app_assoc; apply joinable_mod_kappa_sym;
          apply (joinable_disjoint_local from_ addr _
                   [RChain c0] [RChain (set_chain_label c0 Arbitrage)] Mm
                   [RChain c] [RChain (set_chain_label c Arbitrage)] _);
            apply local_annotate_arb; solve [assumption | reflexivity].
        * (* c before c0 *)
          subst; rewrite <- !app_assoc;
          apply (joinable_disjoint_local from_ addr _
                   [RChain c] [RChain (set_chain_label c Arbitrage)] Mm
                   [RChain c0] [RChain (set_chain_label c0 Arbitrage)] _);
            apply local_annotate_arb; solve [assumption | reflexivity].
      + (* vs R15 *)
        match goal with
        | Heq : ?L0 ++ RChain ?c0 :: ?R0 = ?Lc ++ RChain ?cc :: ?Rc |- _ =>
            destruct (list_two_hole _ L0 (RChain c0) R0 Lc (RChain cc) Rc Heq)
              as [ (HL & Hx & HR) | [ (Mm & HLM & HRM) | (Mm & HLM & HRM) ] ]
        end.
        * (* same chain: R14 & R15 mutually exclusive *)
          injection Hx as ->; subst; exfalso;
          eapply annotate_arb_cyc_exclusive; eassumption.
        * (* c0 (Cycle) before c (Arbitrage) *)
          subst; rewrite <- !app_assoc; apply joinable_mod_kappa_sym;
          apply (joinable_disjoint_local from_ addr _
                   [RChain c0] [RChain (set_chain_label c0 Cycle)] Mm
                   [RChain c] [RChain (set_chain_label c Arbitrage)] _);
            [ apply local_annotate_cyc | apply local_annotate_arb ];
            solve [assumption | reflexivity].
        * (* c (Arbitrage) before c0 (Cycle) *)
          subst; rewrite <- !app_assoc;
          apply (joinable_disjoint_local from_ addr _
                   [RChain c] [RChain (set_chain_label c Arbitrage)] Mm
                   [RChain c0] [RChain (set_chain_label c0 Cycle)] _);
            [ apply local_annotate_arb | apply local_annotate_cyc ];
            solve [assumption | reflexivity].
    - (* R15 *)
      inversion H2; subst;
        try two_leaf_contra; try (sym_lift G1); try (sym_under G1 IH).
      + (* vs R6 *)
        leaf_adj;
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_leaf_vs_annotate;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_leaf_chain; solve [assumption | reflexivity]
          | apply local_annotate_cyc; solve [assumption | reflexivity]
          | leaf_annot Hfw Hadj ].
      + (* vs R12 *)
        leaf_adj;
        get_hfw;
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_leaf_vs_annotate;
          [ | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_node_leaf_chain; solve [assumption | reflexivity]
          | apply local_annotate_cyc; solve [assumption | reflexivity]
          | leaf_annot Hfw Hadj ].
      + (* vs R10 *)
        apply joinable_mod_kappa_sym;
        eapply joinable_chain_seq_vs_annotate;
          [ | | | | solve [symmetry; eassumption | eassumption] ];
          [ intro s; apply RS_chain_seq; solve [assumption | reflexivity]
          | apply local_annotate_cyc; solve [assumption | reflexivity]
          | seq_annot ltac:(left) | seq_annot ltac:(right) ].
      + ann_merge local_annotate_cyc local_merge_endpoints. (* vs R7 *)
      + ann_merge local_annotate_cyc local_merge_add. (* vs R8 *)
      + ann_merge local_annotate_cyc local_merge_closed_R9. (* vs R9 *)
      + ann_merge local_annotate_cyc local_merge_node. (* vs R13 *)
      + (* vs R14 *)
        match goal with
        | Heq : ?L0 ++ RChain ?c0 :: ?R0 = ?Lc ++ RChain ?cc :: ?Rc |- _ =>
            destruct (list_two_hole _ L0 (RChain c0) R0 Lc (RChain cc) Rc Heq)
              as [ (HL & Hx & HR) | [ (Mm & HLM & HRM) | (Mm & HLM & HRM) ] ]
        end.
        * (* same chain: R15 & R14 mutually exclusive *)
          injection Hx as ->; subst; exfalso;
          eapply annotate_arb_cyc_exclusive; eassumption.
        * (* c0 (Arbitrage) before c (Cycle) *)
          subst; rewrite <- !app_assoc; apply joinable_mod_kappa_sym;
          apply (joinable_disjoint_local from_ addr _
                   [RChain c0] [RChain (set_chain_label c0 Arbitrage)] Mm
                   [RChain c] [RChain (set_chain_label c Cycle)] _);
            [ apply local_annotate_arb | apply local_annotate_cyc ];
            solve [assumption | reflexivity].
        * (* c (Cycle) before c0 (Arbitrage) *)
          subst; rewrite <- !app_assoc;
          apply (joinable_disjoint_local from_ addr _
                   [RChain c] [RChain (set_chain_label c Cycle)] Mm
                   [RChain c0] [RChain (set_chain_label c0 Arbitrage)] _);
            [ apply local_annotate_cyc | apply local_annotate_arb ];
            solve [assumption | reflexivity].
      + (* vs R15 *)
        match goal with
        | Heq : ?L0 ++ RChain ?c0 :: ?R0 = ?Lc ++ RChain ?cc :: ?Rc |- _ =>
            destruct (list_two_hole _ L0 (RChain c0) R0 Lc (RChain cc) Rc Heq)
              as [ (HL & Hx & HR) | [ (Mm & HLM & HRM) | (Mm & HLM & HRM) ] ]
        end.
        * (* same chain *) injection Hx as ->; subst; apply joinable_mod_kappa_refl.
        * (* c0 before c *)
          subst; rewrite <- !app_assoc; apply joinable_mod_kappa_sym;
          apply (joinable_disjoint_local from_ addr _
                   [RChain c0] [RChain (set_chain_label c0 Cycle)] Mm
                   [RChain c] [RChain (set_chain_label c Cycle)] _);
            apply local_annotate_cyc; solve [assumption | reflexivity].
        * (* c before c0 *)
          subst; rewrite <- !app_assoc;
          apply (joinable_disjoint_local from_ addr _
                   [RChain c] [RChain (set_chain_label c Cycle)] Mm
                   [RChain c0] [RChain (set_chain_label c0 Cycle)] _);
            apply local_annotate_cyc; solve [assumption | reflexivity].
    - (* under *)
      match goal with
      | Hu : rewrite_step from_ ?tc ?tc',
        Hwf' : wf_rcft from_ (RTree ?a (?ll ++ [?tc] ++ ?rr)) |- _ =>
          assert (Hin : In tc (ll ++ [tc] ++ rr))
            by (apply in_or_app; right; left; reflexivity);
          pose proof (wf_rcft_tree_inv from_ a (ll ++ [tc] ++ rr) Hwf') as [_ [_ Hall]];
          assert (Hwftc : wf_rcft from_ tc)
            by (rewrite Forall_forall in Hall; apply Hall; exact Hin);
          apply (lc_under_vs from_ a ll tc tc' rr T2);
            [ intros U1 U2 HU1 HU2;
              exact (IH (rcft_size tc)
                       (rcft_size_child_lt a (ll ++ [tc] ++ rr) tc Hin)
                       tc eq_refl Hwftc U1 U2 HU1 HU2)
            | exact Hu | exact H2 ]
      end. }
  intros T Hwf T1 T2 H1 H2.
  exact (KEY (rcft_size T) T eq_refl Hwf T1 T2 H1 H2).
Qed.

(* ============================================================
   Section 34: Observable confluence over delta-conservation

   Reduction is confluent modulo kappa on the NON-INTERFERING
   part of the system: disjoint and parallel walks do not
   interfere, so they commute; a bundle of parallel chains merges
   in any order and [kappa] equates the results ([kappa_merge_eq],
   the associative-commutative 3-chain case) -- the words the
   grammar produces are well-defined modulo kappa.  This is O3's
   content ([local_confluent_mod_kappa_holds]).

   Across ALL reductions -- including the one genuinely-interfering
   overlap, a chain that is simultaneously a chaining operand and a
   parallel-merge operand -- the system obeys a CONSERVATION LAW:
   every rewrite step only permutes the transfer multiset
   ([rcft_transfers_perm]).  Conservation is not merely scalar: it
   pins the entire net-flow structure -- the signed delta at every
   (address, token) is invariant under every reduction order.  So
   any two reductions of a tree agree on the whole delta map, hence
   on the value-level verdict, for every observer.  The system is
   confluent with respect to conservation of funds; order-
   independence of the answer is inherited from conservation,
   underpinned by local confluence for the non-interfering walks.
   ============================================================ *)

(** The net signed flow of a whole tree at [(a, tok)]: the sum of
    the per-transfer deltas over every leaf.  A fold over the
    transfer multiset, hence a conserved observable. *)
Definition rcft_delta (T : reduced_cft) (a : address) (tok : token) : Z :=
  fold_right Z.add 0%Z
    (map (fun t => transfer_delta t a tok) (rcft_transfers T)).

(** A permutation of transfers leaves every net delta unchanged. *)
Lemma rcft_delta_perm :
  forall l1 l2 a tok,
    Permutation l1 l2 ->
    fold_right Z.add 0%Z (map (fun t => transfer_delta t a tok) l1)
    = fold_right Z.add 0%Z (map (fun t => transfer_delta t a tok) l2).
Proof.
  intros l1 l2 a tok Hp. apply fold_right_Zadd_perm.
  apply Permutation_map. exact Hp.
Qed.

(** REPORTING SOUNDNESS.  Every delta the pipeline reports off a reduced
    tree is a delta of the input trace: the net signed flow at any
    (address, token) is the same before and after reduction, for every
    reduction.  Reported profits are therefore properties of the
    transaction, not artefacts of the rewriting. *)
Corollary reported_deltas_are_input_deltas :
  forall from_ T0 Tf a tok,
    rewrite_star from_ T0 Tf ->
    rcft_delta Tf a tok = rcft_delta T0 a tok.
Proof.
  intros from_ T0 Tf a tok Hstar.
  unfold rcft_delta.
  apply rcft_delta_perm.
  apply Permutation_sym.
  apply (rcft_transfers_perm_star from_ T0 Tf Hstar).
Qed.

(** OBSERVABLE CONFLUENCE (funds level).  Any two reductions of a
    tree reach states with the SAME transfer multiset. *)
Lemma observable_confluence :
  forall from_ T T1 T2,
    rewrite_star from_ T T1 ->
    rewrite_star from_ T T2 ->
    Permutation (rcft_transfers T1) (rcft_transfers T2).
Proof.
  intros from_ T T1 T2 H1 H2.
  eapply perm_trans;
    [ apply Permutation_sym; apply (rcft_transfers_perm_star from_ T T1 H1)
    | apply (rcft_transfers_perm_star from_ T T2 H2) ].
Qed.

(** OBSERVABLE CONFLUENCE (structure level).  The whole net-flow
    map is invariant: any two reductions of a tree agree on the
    signed delta at EVERY address and token.  Structural
    non-confluence of the nondeterministic system is invisible
    through this conserved observable -- the detector's answer,
    which reads the delta, is order-independent by conservation,
    underpinned by O3's local confluence for the non-interfering
    walks. *)
Lemma observable_confluence_delta :
  forall from_ T T1 T2,
    rewrite_star from_ T T1 ->
    rewrite_star from_ T T2 ->
    forall a tok, rcft_delta T1 a tok = rcft_delta T2 a tok.
Proof.
  intros from_ T T1 T2 H1 H2 a tok. unfold rcft_delta.
  apply rcft_delta_perm. exact (observable_confluence from_ T T1 T2 H1 H2).
Qed.

(* ============================================================
   Section 35: Decidable structural equivalence

   Two sigma-CFTs are structurally equivalent when they share a
   canonical form.  [kappa] AC-normalizes parallel bundles
   ([op_sort] over the flattened operands), so this is exactly
   equality up to reordering of parallel walks -- the structural
   congruence of the flow algebra.  Because [kappa] is a
   computable, idempotent canonical map and [reduced_cft] has
   decidable equality, the equivalence is DECIDABLE.
   ============================================================ *)

Definition struct_equiv (T1 T2 : reduced_cft) : Prop :=
  kappa T1 = kappa T2.

Lemma struct_equiv_refl : forall T, struct_equiv T T.
Proof. reflexivity. Qed.

Lemma struct_equiv_sym :
  forall T1 T2, struct_equiv T1 T2 -> struct_equiv T2 T1.
Proof. unfold struct_equiv. intros T1 T2 H. symmetry. exact H. Qed.

Lemma struct_equiv_trans :
  forall T1 T2 T3,
    struct_equiv T1 T2 -> struct_equiv T2 T3 -> struct_equiv T1 T3.
Proof.
  unfold struct_equiv. intros T1 T2 T3 H1 H2. rewrite H1. exact H2.
Qed.

(** DECIDABLE STRUCTURAL EQUIVALENCE.  Compute both canonical forms
    and compare with the structural [reduced_cft_eq_dec].  Closed with
    [Defined] rather than [Qed]: this is a decision procedure, and
    extraction must see its body to emit a runnable comparison. *)
Lemma struct_equiv_dec :
  forall T1 T2, {struct_equiv T1 T2} + {~ struct_equiv T1 T2}.
Proof.
  intros T1 T2. unfold struct_equiv. apply reduced_cft_eq_dec.
Defined.

(** The AC criterion, [A ‖ B ‖ C = every reordering], split into its
    two laws on a parallel bundle.  Associativity is unconditional;
    commutativity holds under linearity (Property 1: the operand
    signatures are distinct, so [op_sort] fully canonicalizes the
    order).  Together they give equivalence under any permutation. *)
Corollary struct_equiv_bundle_assoc :
  forall c1 c2 c3,
    struct_equiv (RChain (merge_chain (merge_chain c1 c2) c3))
                 (RChain (merge_chain c1 (merge_chain c2 c3))).
Proof. intros c1 c2 c3. unfold struct_equiv. apply kappa_merge_assoc. Qed.

Corollary struct_equiv_bundle_comm :
  forall c1 c2,
    linear (RChain (merge_chain c1 c2)) ->
    struct_equiv (RChain (merge_chain c1 c2)) (RChain (merge_chain c2 c1)).
Proof.
  intros c1 c2 Hlin. unfold struct_equiv. cbn [kappa]. f_equal.
  apply kappa_ct_merge_comm_linear. exact Hlin.
Qed.

(** Extraction to OCaml.  VERIFIED, and left commented so that an
    ordinary build does not write generated files into the tree:
    uncommenting the block below emits [arbitrage_verified.ml] /
    [.mli], carrying the rewriting kernel ([step_fn],
    [try_combine_leaves]), the verdict cascade ([classify]),
    and the canonical map with its decidable structural
    equivalence ([kappa], [struct_equiv_dec]).  The emitted
    module has been checked to compile under [ocamlc] against
    the realizers below and to run: the verdict cascade returns
    [VArbitrage] on an empty reason list and [VNone] on
    [NoCycles], and [struct_equiv_dec] confirms [kappa] is at a
    fixpoint on a two-leaf test tree.
    The eleven declared [Parameter]s are: the two
    carrier types ([address], [token]) with their
    decidable equalities, token equivalence, burn/mint
    detection, singleton-router membership,
    token-contract membership, the cost model
    ([net_positive]), and the trace-order key
    ([trace_key]).  They are supplied as realizers at
    extraction time; the realizers shown below are
    placeholders for unit-testing the extracted kernel
    ([trace_key]'s injectivity, [is_trace_key_wf], is a
    realizer obligation, not a theorem).  Every theorem
    in this file is parametric in these realizers, so
    soundness, confluence, and termination transfer to
    any realizer choice.  [nat] is realized as OCaml [int]
    so that the trace-order key is a machine integer; this
    is an extraction directive and carries no logical
    content. *)
(*
Require Extraction.
Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive nat => "int" [ "0" "Stdlib.succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Constant address => "string".
Extract Constant token => "string".
Extract Inlined Constant address_eq_dec => "(=)".
Extract Inlined Constant token_eq_dec => "(=)".
Extract Inlined Constant token_equiv => "(=)".
Extract Inlined Constant is_burn => "(fun _ -> false)".
Extract Inlined Constant is_mint => "(fun _ -> false)".
Extract Inlined Constant is_singleton_router => "(fun _ -> false)".
Extract Inlined Constant is_token_contract => "(fun _ _ -> false)".
Extract Inlined Constant net_positive => "(fun _ -> true)".
Extract Inlined Constant trace_key => "Hashtbl.hash".

Extraction "arbitrage_verified.ml"
  step_fn try_combine_leaves classify kappa struct_equiv_dec.
*)