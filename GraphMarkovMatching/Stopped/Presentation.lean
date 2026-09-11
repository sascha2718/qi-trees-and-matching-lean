/-
The Markov model of a common-core presentation (`markov_matching_new_proof.tex`,
`sec:common-presentations`, `sec:types`): two arity laws `ν_L, ν_R` with finite supports, a
common core `S` with core profiles `D a` (`a ∈ S`), and for every supported arity `k` on
either side a composite profile `C σ k` with `k` leaves built from the core profiles, the
core arities using the one-term expression `C σ a = D a`.

* `PType`: the raw types `(σ, none)` (the fresh type of side `σ`) and `(σ, some τ)` (the
  forced type of side `σ` with remaining tree `τ`); `typeOf σ τ` sends a leaf to the fresh
  type and a node to the forced type;
* `Presentation`: the data and their conditions;
* `live`: the finite set of types actually occurring: the two fresh types and the forced
  types at the proper subtrees of the supported profiles; `Live` its subtype;
* `rawKernel`, `toModel`: the child-type kernel (a fresh vertex draws an arity `k ~ ν σ` and
  places `C σ k`; a forced vertex descends deterministically) and the model over the live
  types with a state space `(V, R, zero, μ)`;
* `flatten_realisation` (the construction in `thm:atomic-normalisation` and
  `thm:fresh-positive`): a charged realisation of a forced type matching a source can be
  replaced by a charged realisation of the flattened type matching the same source;
* `side_change` (the target-side reproduction in `thm:fresh-positive`): a charged
  realisation of a type matching a source can be replaced by a charged realisation of the
  same remaining tree on the other side matching the same source;
* `freshPositive` (`thm:fresh-positive`), `selection` with `budget_le`
  (`thm:atomic-normalisation`, the budget `B = max_σ ∑_{a ∈ S} ν_σ(a)^{-α}`), `card_live_le`
  (`eq:type-count`).

The phases and the return bound `thm:bounded-return` are in `Returns.lean`.
-/
import GraphMarkovMatching.Stopped.Paths
import GraphMarkovMatching.Stopped.Profiles

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

/-- The raw types of a two-sided presentation: `(σ, none)` is the fresh type of side `σ`,
`(σ, some τ)` the forced type of side `σ` with remaining tree `τ`. -/
abbrev PType := Bool × Option MTree

/-- The type below a vertex of side `σ` with remaining tree `τ`: fresh at a leaf, forced
otherwise. -/
def typeOf (σ : Bool) : MTree → PType
  | .leaf => (σ, none)
  | t => (σ, some t)

/-- The child-type pair at the root of a remaining tree (junk at a leaf). -/
def rootPair (σ : Bool) : MTree → PType × PType
  | .leaf => ((σ, none), (σ, none))
  | .node l r => (typeOf σ l, typeOf σ r)
  | .gnode l r => (typeOf σ l, typeOf σ r)

/-- A common-core presentation of two arity laws (`sec:common-presentations`). -/
structure Presentation where
  /-- the common core arities -/
  S : Finset ℕ
  /-- the core profiles, `D a` a graft-free node with `a` leaves for `a ∈ S` -/
  D : ℕ → MTree
  /-- the arity laws of the two sides -/
  ν : Bool → PMF ℕ
  /-- the finite supports of the arity laws -/
  supp : Bool → Finset ℕ
  /-- the composite profile of each supported arity on each side -/
  C : Bool → ℕ → MTree
  mem_supp : ∀ σ k, ν σ k ≠ 0 ↔ k ∈ supp σ
  S_nonempty : S.Nonempty
  two_le_S : ∀ a ∈ S, 2 ≤ a
  D_leaves : ∀ a ∈ S, (D a).leaves = a
  D_noGraft : ∀ a ∈ S, (D a).NoGraft
  D_node : ∀ a ∈ S, ∃ l r, D a = MTree.node l r
  S_subset_supp : ∀ σ, S ⊆ supp σ
  two_le_supp : ∀ σ k, k ∈ supp σ → 2 ≤ k
  C_leaves : ∀ σ k, k ∈ supp σ → (C σ k).leaves = k
  C_gnode : ∀ σ k, k ∈ supp σ → ∃ l r, C σ k = MTree.gnode l r
  C_allComp : ∀ σ k, k ∈ supp σ → MTree.AllComp S D (C σ k)
  /-- core arities use the one-term expression: `C σ a` is the marked core profile -/
  C_core : ∀ σ a, a ∈ S → C σ a = MTree.markRoot (D a)

namespace Presentation

variable (P : Presentation)

/-- The finite set of live types: the two fresh types and the forced types at the proper
subtrees (other than leaves) of the supported profiles. -/
noncomputable def live : Finset PType :=
  ({(false, none), (true, none)} : Finset PType)
    ∪ (Finset.univ (α := Bool)).biUnion fun σ =>
        (P.supp σ).biUnion fun k =>
          ((P.C σ k).subtrees.filter fun τ => τ ≠ P.C σ k ∧ τ ≠ MTree.leaf).image fun τ =>
            (σ, some τ)

/-- The live types as a finite type. -/
def Live : Type := {t : PType // t ∈ P.live}

noncomputable instance : Fintype P.Live := by
  unfold Live; infer_instance

instance : DecidableEq P.Live := by
  unfold Live; infer_instance

/-- The fresh type of side `σ` is live. -/
lemma fresh_mem_live (σ : Bool) : (σ, none) ∈ P.live := by
  cases σ <;> simp [live]

/-- The fresh live type of side `σ`. -/
def freshL (σ : Bool) : P.Live := ⟨(σ, none), P.fresh_mem_live σ⟩

/-- Coerce a raw type into the live types, defaulting to the left fresh type. -/
noncomputable def toLive (t : PType) : P.Live :=
  if h : t ∈ P.live then ⟨t, h⟩ else P.freshL false

/-- The raw child-type kernel: a fresh vertex draws an arity from its side's law and places
the corresponding profile, a forced vertex descends deterministically. -/
noncomputable def rawKernel : PType → PMF (PType × PType)
  | (σ, none) => (P.ν σ).map fun k => rootPair σ (P.C σ k)
  | (σ, some τ) => PMF.pure (rootPair σ τ)

/-- The child-type kernel on the live types. -/
noncomputable def kernelL (t : P.Live) : PMF (P.Live × P.Live) :=
  (P.rawKernel t.1).map fun p => (P.toLive p.1, P.toLive p.2)

/-! ### Types, remaining trees and liveness -/

/-- The type of a leaf is the fresh type. -/
lemma typeOf_leaf (σ : Bool) : typeOf σ MTree.leaf = (σ, none) := rfl

/-- The type of a tree other than a leaf is the forced type with that remaining tree. -/
lemma typeOf_of_ne_leaf (σ : Bool) {τ : MTree} (h : τ ≠ MTree.leaf) :
    typeOf σ τ = (σ, some τ) := by
  cases τ with
  | leaf => exact absurd rfl h
  | node l r => rfl
  | gnode l r => rfl

/-- The root pair of a node is the pair of child types. -/
lemma rootPair_node (σ : Bool) (l r : MTree) :
    rootPair σ (MTree.node l r) = (typeOf σ l, typeOf σ r) := rfl

/-- The root pair of a graft root is the pair of child types. -/
lemma rootPair_gnode (σ : Bool) (l r : MTree) :
    rootPair σ (MTree.gnode l r) = (typeOf σ l, typeOf σ r) := rfl

/-- A forced type is live exactly when its remaining tree is a proper subtree, other than
a leaf, of a supported profile of its side (`sec:types`). -/
lemma mem_live_some_iff (σ : Bool) (τ : MTree) :
    (σ, some τ) ∈ P.live
      ↔ ∃ k ∈ P.supp σ,
          τ ∈ (P.C σ k).subtrees ∧ τ ≠ P.C σ k ∧ τ ≠ MTree.leaf := by
  cases σ <;> simp [live]

/-- The type of a proper subtree of a supported profile is live. -/
lemma typeOf_mem_live_of_subtree {σ : Bool} {k : ℕ} (hk : k ∈ P.supp σ) {l : MTree}
    (hl : l ∈ (P.C σ k).subtrees) (hne : l ≠ P.C σ k) : typeOf σ l ∈ P.live := by
  by_cases hleaf : l = MTree.leaf
  · rw [hleaf, typeOf_leaf]
    exact P.fresh_mem_live σ
  · rw [typeOf_of_ne_leaf σ hleaf, P.mem_live_some_iff]
    exact ⟨k, hk, hl, hne, hleaf⟩

/-- The type of a subtree of a supported profile of smaller height is live. -/
lemma typeOf_mem_live_of_height_lt {σ : Bool} {k : ℕ} (hk : k ∈ P.supp σ) {l : MTree}
    (hl : l ∈ (P.C σ k).subtrees) (hlt : l.height < (P.C σ k).height) :
    typeOf σ l ∈ P.live :=
  P.typeOf_mem_live_of_subtree hk hl fun heq => by
    rw [heq] at hlt
    exact lt_irrefl _ hlt

/-- The child types at the root of a subtree of a supported profile are live. -/
lemma rootPair_mem_live {σ : Bool} {k : ℕ} (hk : k ∈ P.supp σ) {τ : MTree}
    (hτ : τ ∈ (P.C σ k).subtrees) :
    (rootPair σ τ).1 ∈ P.live ∧ (rootPair σ τ).2 ∈ P.live := by
  have hh := MTree.height_le_of_mem_subtrees hτ
  cases τ with
  | leaf => exact ⟨P.fresh_mem_live σ, P.fresh_mem_live σ⟩
  | node l r =>
    have hl : l.height < (MTree.node l r).height := by
      show l.height < max l.height r.height + 1
      omega
    have hr : r.height < (MTree.node l r).height := by
      show r.height < max l.height r.height + 1
      omega
    exact ⟨P.typeOf_mem_live_of_height_lt hk
        (MTree.subtrees_trans (MTree.subtrees_node_left l r) hτ) (by omega),
      P.typeOf_mem_live_of_height_lt hk
        (MTree.subtrees_trans (MTree.subtrees_node_right l r) hτ) (by omega)⟩
  | gnode l r =>
    have hl : l.height < (MTree.gnode l r).height := by
      show l.height < max l.height r.height + 1
      omega
    have hr : r.height < (MTree.gnode l r).height := by
      show r.height < max l.height r.height + 1
      omega
    exact ⟨P.typeOf_mem_live_of_height_lt hk
        (MTree.subtrees_trans (MTree.subtrees_gnode_left l r) hτ) (by omega),
      P.typeOf_mem_live_of_height_lt hk
        (MTree.subtrees_trans (MTree.subtrees_gnode_right l r) hτ) (by omega)⟩

/-- The child types of a live forced type are live. -/
lemma rootPair_mem_live_of_mem {σ : Bool} {τ : MTree} (h : (σ, some τ) ∈ P.live) :
    (rootPair σ τ).1 ∈ P.live ∧ (rootPair σ τ).2 ∈ P.live := by
  obtain ⟨k, hk, hτ, -, -⟩ := (P.mem_live_some_iff σ τ).mp h
  exact P.rootPair_mem_live hk hτ

/-- The child types of the core block of a core profile are live on either side. -/
lemma core_children_mem_live (σ : Bool) {a : ℕ} (ha : a ∈ P.S) {l r : MTree}
    (hD : MTree.node l r = P.D a) : typeOf σ l ∈ P.live ∧ typeOf σ r ∈ P.live := by
  have hC : P.C σ a = MTree.gnode l r := by
    rw [P.C_core σ a ha, ← hD]
    rfl
  have := P.rootPair_mem_live (P.S_subset_supp σ ha) (MTree.mem_subtrees_self (P.C σ a))
  rw [hC] at this
  exact this

/-! ### The raw kernel -/

/-- The raw kernel at a fresh type. -/
lemma rawKernel_fresh (σ : Bool) :
    P.rawKernel (σ, none) = (P.ν σ).map fun k => rootPair σ (P.C σ k) := rfl

/-- The raw kernel at a forced type. -/
lemma rawKernel_forced (σ : Bool) (τ : MTree) :
    P.rawKernel (σ, some τ) = PMF.pure (rootPair σ τ) := rfl

/-- The charged transitions of a fresh type are the root pairs of the supported profiles. -/
lemma rawKernel_fresh_ne_zero_iff (σ : Bool) (p : PType × PType) :
    P.rawKernel (σ, none) p ≠ 0 ↔ ∃ k, P.ν σ k ≠ 0 ∧ p = rootPair σ (P.C σ k) := by
  rw [rawKernel_fresh, PMF.map_apply, Ne, ENNReal.tsum_eq_zero]
  push Not
  refine exists_congr fun k => ?_
  by_cases h : p = rootPair σ (P.C σ k) <;> simp [h]

/-- The single charged transition of a forced type is its root pair. -/
lemma rawKernel_forced_ne_zero_iff (σ : Bool) (τ : MTree) (p : PType × PType) :
    P.rawKernel (σ, some τ) p ≠ 0 ↔ p = rootPair σ τ := by
  rw [rawKernel_forced, PMF.pure_apply]
  by_cases h : p = rootPair σ τ <;> simp [h]

/-- The coercion is the identity on live types. -/
lemma toLive_of_mem {t : PType} (h : t ∈ P.live) : P.toLive t = ⟨t, h⟩ := dif_pos h

/-- The children of a live type in a charged transition are live. -/
lemma rawKernel_live (t : P.Live) (p : PType × PType) (hp : P.rawKernel t.1 p ≠ 0) :
    p.1 ∈ P.live ∧ p.2 ∈ P.live := by
  obtain ⟨⟨σ, oτ⟩, ht⟩ := t
  cases oτ with
  | none =>
    obtain ⟨k, hk, rfl⟩ := (P.rawKernel_fresh_ne_zero_iff σ p).mp hp
    exact P.rootPair_mem_live ((P.mem_supp σ k).mp hk) (MTree.mem_subtrees_self _)
  | some τ =>
    obtain rfl := (P.rawKernel_forced_ne_zero_iff σ τ p).mp hp
    exact P.rootPair_mem_live_of_mem ht

/-- **The Markov model of a presentation** over a state space with a reflexive symmetric
compatibility relation, a distinguished state and a fresh state law. -/
noncomputable def toModel {V : Type} (R : V → V → Prop) (zero : V) (μ : PMF V) :
    Model V P.Live where
  R := R
  zero := zero
  μ := μ
  fresh := fun t => t.1.2 = none
  π := P.kernelL

variable {V : Type} (R : V → V → Prop) (zero : V) (μ : PMF V)

/-- The fresh live types are exactly the fresh types of the model. -/
lemma fresh_iff (t : P.Live) : (P.toModel R zero μ).fresh t ↔ t.1.2 = none := Iff.rfl

/-- The kernel of a charged transition at a live type is the raw kernel: the coercion is the
identity on charged pairs. -/
lemma kernelL_apply_of_live (t : P.Live) (p : PType × PType) (h1 : p.1 ∈ P.live)
    (h2 : p.2 ∈ P.live) :
    P.kernelL t (⟨p.1, h1⟩, ⟨p.2, h2⟩) = P.rawKernel t.1 p := by
  rw [kernelL, PMF.map_apply]
  refine (tsum_congr fun p' => ?_).trans (tsum_ite_eq p (P.rawKernel t.1))
  by_cases hp' : P.rawKernel t.1 p' = 0
  · simp [hp']
  · obtain ⟨h1', h2'⟩ := P.rawKernel_live t p' hp'
    rw [P.toLive_of_mem h1', P.toLive_of_mem h2']
    congr 1
    apply propext
    constructor
    · intro e
      obtain ⟨e1, e2⟩ := Prod.mk.inj e
      exact (Prod.ext_iff.mpr ⟨Subtype.mk.inj e1, Subtype.mk.inj e2⟩).symm
    · rintro rfl
      rfl

/-- A charged transition of the model is a charged transition of the raw kernel between live
types. -/
lemma kernelL_ne_zero_iff (t : P.Live) (j : P.Live × P.Live) :
    P.kernelL t j ≠ 0 ↔ P.rawKernel t.1 (j.1.1, j.2.1) ≠ 0 := by
  have h : P.kernelL t j = P.rawKernel t.1 (j.1.1, j.2.1) :=
    P.kernelL_apply_of_live t (j.1.1, j.2.1) j.1.2 j.2.2
  rw [h]

/-- The forced type of a live node descends to the types of its children. -/
lemma kernelL_forced (σ : Bool) (τ : MTree) (h : (σ, some τ) ∈ P.live) :
    P.kernelL ⟨(σ, some τ), h⟩ = PMF.pure (P.toLive (rootPair σ τ).1, P.toLive (rootPair σ τ).2) := by
  rw [kernelL]
  show (P.rawKernel (σ, some τ)).map _ = _
  rw [rawKernel_forced, PMF.pure_map]

/-! ### The model at the live types -/

/-- A type built from a remaining tree is fresh exactly at a leaf. -/
lemma fresh_typeOf_iff (σ : Bool) (τ : MTree) (h : typeOf σ τ ∈ P.live) :
    (P.toModel R zero μ).fresh ⟨typeOf σ τ, h⟩ ↔ τ = MTree.leaf := by
  show (typeOf σ τ).2 = none ↔ τ = MTree.leaf
  cases τ <;> simp [typeOf]

/-- The root law of a type built from a remaining tree: `μ` at a leaf, the point mass at
`0` otherwise; it does not depend on the side. -/
lemma rootLaw_typeOf (σ : Bool) (τ : MTree) (h : typeOf σ τ ∈ P.live) :
    (P.toModel R zero μ).rootLaw ⟨typeOf σ τ, h⟩
      = if τ = MTree.leaf then μ else PMF.pure zero := by
  by_cases hτ : τ = MTree.leaf
  · rw [if_pos hτ]
    exact Model.rootLaw_fresh _ ((P.fresh_typeOf_iff R zero μ σ τ h).mpr hτ)
  · rw [if_neg hτ]
    exact Model.rootLaw_forced _ fun hf => hτ ((P.fresh_typeOf_iff R zero μ σ τ h).mp hf)

/-- The root law of a forced type is the point mass at `0`. -/
lemma rootLaw_forced' {σ : Bool} {τ : MTree} (h : (σ, some τ) ∈ P.live) :
    (P.toModel R zero μ).rootLaw ⟨(σ, some τ), h⟩ = PMF.pure zero :=
  Model.rootLaw_forced _ (Option.some_ne_none τ)

/-- The root law of a fresh type is `μ`. -/
lemma rootLaw_fresh' {σ : Bool} (h : (σ, none) ∈ P.live) :
    (P.toModel R zero μ).rootLaw ⟨(σ, none), h⟩ = μ :=
  Model.rootLaw_fresh _ rfl

/-- A charged root state of a forced type is `0`. -/
lemma eq_zero_of_rootLaw_ne_zero {σ : Bool} {τ : MTree} (h : (σ, some τ) ∈ P.live) {v : V}
    (hv : (P.toModel R zero μ).rootLaw ⟨(σ, some τ), h⟩ v ≠ 0) : v = zero := by
  rw [P.rootLaw_forced' R zero μ, PMF.pure_apply] at hv
  by_contra hc
  rw [if_neg hc] at hv
  exact hv rfl

/-- The state `0` is charged at a forced type. -/
lemma rootLaw_forced_zero_ne_zero {σ : Bool} {τ : MTree} (h : (σ, some τ) ∈ P.live) :
    (P.toModel R zero μ).rootLaw ⟨(σ, some τ), h⟩ zero ≠ 0 := by
  rw [P.rootLaw_forced' R zero μ, PMF.pure_apply, if_pos rfl]
  exact one_ne_zero

/-- A state charged by `μ` is charged at a fresh type. -/
lemma rootLaw_fresh_ne_zero {σ : Bool} (h : (σ, none) ∈ P.live) {w : V} (hw : μ w ≠ 0) :
    (P.toModel R zero μ).rootLaw ⟨(σ, none), h⟩ w ≠ 0 := by
  rw [P.rootLaw_fresh' R zero μ]
  exact hw

/-- The charged transition of a forced type is the root pair of its remaining tree. -/
lemma eq_of_kernelL_forced_ne_zero {σ : Bool} {τ : MTree} (h : (σ, some τ) ∈ P.live)
    {j : P.Live × P.Live} (hj : P.kernelL ⟨(σ, some τ), h⟩ j ≠ 0) :
    j = (P.toLive (rootPair σ τ).1, P.toLive (rootPair σ τ).2) := by
  rw [P.kernelL_forced, PMF.pure_apply] at hj
  by_contra hc
  rw [if_neg hc] at hj
  exact hj rfl

/-- The core transition at a fresh type is charged: the root pair of the core block of a
core profile (`sec:positive-fresh`). -/
lemma kernelL_fresh_core_ne_zero (σ : Bool) {a : ℕ} (ha : a ∈ P.S) {l r : MTree}
    (hD : MTree.node l r = P.D a) (hl : typeOf σ l ∈ P.live) (hr : typeOf σ r ∈ P.live) :
    P.kernelL (P.freshL σ) (⟨typeOf σ l, hl⟩, ⟨typeOf σ r, hr⟩) ≠ 0 := by
  rw [P.kernelL_ne_zero_iff]
  show P.rawKernel (σ, none) (typeOf σ l, typeOf σ r) ≠ 0
  rw [P.rawKernel_fresh_ne_zero_iff]
  refine ⟨a, (P.mem_supp σ a).mpr (P.S_subset_supp σ ha), ?_⟩
  rw [P.C_core σ a ha, ← hD]
  rfl

/-- A good degree is positive exactly when some compatible point is charged. -/
private lemma rE_ne_zero_iff' {X : Type} (ν : PMF X) (Q : X → X → Prop) (x : X) :
    rE ν Q x ≠ 0 ↔ ∃ y, Q x y ∧ ν y ≠ 0 := by
  rw [rE, Ne, ENNReal.tsum_eq_zero]
  push Not
  refine exists_congr fun y => ?_
  by_cases h : Q x y <;> simp [h]

/-- Every realised state has a charged compatible state (`sec:positive-fresh`): a state in
the support by reflexivity, the state `0` by `b(0) > 0`. -/
lemma exists_fresh_state (hc : (P.toModel R zero μ).IsCompat) (hb0 : rE μ R zero ≠ 0)
    {v : V} (hv : v ∈ (P.toModel R zero μ).Vmu) : ∃ w, μ w ≠ 0 ∧ R v w := by
  rcases hv with hv | hv
  · exact ⟨v, hv, hc.refl v⟩
  · rw [Set.mem_singleton_iff] at hv
    obtain ⟨w, hw, hμ⟩ := (rE_ne_zero_iff' μ R zero).mp hb0
    exact ⟨w, hμ, hv ▸ hw⟩

/-- Matching a branch under a swap bit and two child automorphisms. -/
lemma fullMatchesK_branch_iff {h : ℕ} (b : Bool) (π₁ π₂ : AutK 1 0 h)
    (x : FullLab (P.Live × V) (h + 1)) (s : P.Live × V)
    (p : FullLab (P.Live × V) h × FullLab (P.Live × V) h) :
    fullMatchesK (P.toModel R zero μ).srel 1 0 (h + 1) (b, π₁, π₂) x (branch s p)
      ↔ R x.1.2 s.2
        ∧ fullMatchesK (P.toModel R zero μ).srel 1 0 h π₁ x.2.1 (bif b then p.2 else p.1)
        ∧ fullMatchesK (P.toModel R zero μ).srel 1 0 h π₂ x.2.2 (bif b then p.1 else p.2) :=
  Iff.rfl

/-- Lifting two child-wise replacements through the swap bit of a branch matching. -/
private lemma swap_lift {G A B : Type} {M1 : G → A → B → Prop} {Sx : A → Prop}
    {C1 C2 : B → Prop} (b : Bool) {π₁ π₂ : G} {x₁ x₂ : A} {y₁ y₂ : B}
    (rep₁ : ∀ π x, Sx x → M1 π x y₁ → ∃ y', C1 y' ∧ M1 π x y')
    (rep₂ : ∀ π x, Sx x → M1 π x y₂ → ∃ y', C2 y' ∧ M1 π x y')
    (hx₁ : Sx x₁) (hx₂ : Sx x₂)
    (hm1 : M1 π₁ x₁ (bif b then y₂ else y₁))
    (hm2 : M1 π₂ x₂ (bif b then y₁ else y₂)) :
    ∃ y₁' y₂', C1 y₁' ∧ C2 y₂'
      ∧ M1 π₁ x₁ (bif b then y₂' else y₁')
      ∧ M1 π₂ x₂ (bif b then y₁' else y₂') := by
  cases b
  · obtain ⟨y₁', h1, m1⟩ := rep₁ π₁ x₁ hx₁ hm1
    obtain ⟨y₂', h2, m2⟩ := rep₂ π₂ x₂ hx₂ hm2
    exact ⟨y₁', y₂', h1, h2, m1, m2⟩
  · obtain ⟨y₂', h2, m2⟩ := rep₂ π₁ x₁ hx₁ hm1
    obtain ⟨y₁', h1, m1⟩ := rep₁ π₂ x₂ hx₂ hm2
    exact ⟨y₁', y₂', h1, h2, m2, m1⟩

/-- The children of a charged realisation of a forced type: the root state is `0` and the
two subtrees are charged realisations of the child types. -/
lemma forced_children {σ : Bool} {τ l r : MTree}
    (hτr : rootPair σ τ = (typeOf σ l, typeOf σ r))
    (hτ : (σ, some τ) ∈ P.live) (hl : typeOf σ l ∈ P.live) (hr : typeOf σ r ∈ P.live)
    {h : ℕ} {y : FullLab (P.Live × V) (h + 1)}
    (hy : (P.toModel R zero μ).rho ⟨(σ, some τ), hτ⟩ (h + 1) y ≠ 0) :
    y.1.2 = zero ∧ (P.toModel R zero μ).rho ⟨typeOf σ l, hl⟩ h y.2.1 ≠ 0
      ∧ (P.toModel R zero μ).rho ⟨typeOf σ r, hr⟩ h y.2.2 ≠ 0 := by
  have hy' : (P.toModel R zero μ).rho ⟨(σ, some τ), hτ⟩ (h + 1)
      (branch y.1 (y.2.1, y.2.2)) ≠ 0 := hy
  rw [Model.rho_succ_ne_zero_iff] at hy'
  obtain ⟨-, hy2, j, hj, hj1, hj2⟩ := hy'
  have hjeq : j = ((⟨typeOf σ l, hl⟩ : P.Live), (⟨typeOf σ r, hr⟩ : P.Live)) := by
    rw [P.eq_of_kernelL_forced_ne_zero hτ hj, hτr]
    show (P.toLive (typeOf σ l), P.toLive (typeOf σ r)) = _
    rw [P.toLive_of_mem hl, P.toLive_of_mem hr]
    rfl
  subst hjeq
  exact ⟨P.eq_zero_of_rootLaw_ne_zero R zero μ hτ hy2, hj1, hj2⟩

/-- A branch with root state `0` over charged realisations of the child types is a charged
realisation of a forced type. -/
lemma rho_forced_branch_ne_zero {σ : Bool} {τ l r : MTree}
    (hτr : rootPair σ τ = (typeOf σ l, typeOf σ r))
    (hτ : (σ, some τ) ∈ P.live) (hl : typeOf σ l ∈ P.live) (hr : typeOf σ r ∈ P.live)
    {h : ℕ} {p : FullLab (P.Live × V) h × FullLab (P.Live × V) h}
    (h1 : (P.toModel R zero μ).rho ⟨typeOf σ l, hl⟩ h p.1 ≠ 0)
    (h2 : (P.toModel R zero μ).rho ⟨typeOf σ r, hr⟩ h p.2 ≠ 0) :
    (P.toModel R zero μ).rho ⟨(σ, some τ), hτ⟩ (h + 1)
      (branch (⟨(σ, some τ), hτ⟩, zero) p) ≠ 0 := by
  rw [Model.rho_succ_ne_zero_iff]
  refine ⟨rfl, P.rootLaw_forced_zero_ne_zero R zero μ hτ,
    ((⟨typeOf σ l, hl⟩ : P.Live), (⟨typeOf σ r, hr⟩ : P.Live)), ?_, h1, h2⟩
  show P.kernelL ⟨(σ, some τ), hτ⟩ _ ≠ 0
  rw [P.kernelL_forced, hτr]
  show PMF.pure (P.toLive (typeOf σ l), P.toLive (typeOf σ r)) _ ≠ 0
  rw [P.toLive_of_mem hl, P.toLive_of_mem hr, PMF.pure_apply, if_pos rfl]
  exact one_ne_zero

/-- A branch with a charged fresh root state over charged realisations of the child types
of a core block is a charged realisation of the fresh type. -/
lemma rho_fresh_branch_ne_zero {σ : Bool} (hF : (σ, none) ∈ P.live) {a : ℕ}
    (ha : a ∈ P.S) {l r : MTree} (hD : MTree.node l r = P.D a) (hl : typeOf σ l ∈ P.live)
    (hr : typeOf σ r ∈ P.live) {h : ℕ}
    {p : FullLab (P.Live × V) h × FullLab (P.Live × V) h}
    (h1 : (P.toModel R zero μ).rho ⟨typeOf σ l, hl⟩ h p.1 ≠ 0)
    (h2 : (P.toModel R zero μ).rho ⟨typeOf σ r, hr⟩ h p.2 ≠ 0) {w : V} (hw : μ w ≠ 0) :
    (P.toModel R zero μ).rho ⟨(σ, none), hF⟩ (h + 1)
      (branch (⟨(σ, none), hF⟩, w) p) ≠ 0 := by
  rw [Model.rho_succ_ne_zero_iff]
  exact ⟨rfl, P.rootLaw_fresh_ne_zero R zero μ hF hw,
    ((⟨typeOf σ l, hl⟩ : P.Live), (⟨typeOf σ r, hr⟩ : P.Live)),
    P.kernelL_fresh_core_ne_zero σ ha hD hl hr, h1, h2⟩

/-! ### Flattening -/

/-- A graft-free tree is a composite profile. -/
private lemma allComp_of_noGraft {S : Finset ℕ} {D : ℕ → MTree} :
    ∀ t : MTree, t.NoGraft → MTree.AllComp S D t
  | .leaf, _ => trivial
  | .node l r, ⟨hl, hr⟩ => ⟨allComp_of_noGraft l hl, allComp_of_noGraft r hr⟩
  | .gnode _ _, h => h.elim

/-- A node of a composite profile flattens either to a subtree of the flattened profile or
to a proper subtree of a core profile (`thm:atomic-normalisation`: every internal vertex
lies in a core block). -/
private lemma flatten_mem_of_allComp {S : Finset ℕ} {D : ℕ → MTree} :
    ∀ (u : MTree), MTree.AllComp S D u → ∀ {l r : MTree}, MTree.node l r ∈ u.subtrees →
      (MTree.node l r).flatten ∈ u.flatten.subtrees
        ∨ ∃ a ∈ S, ∃ l' r', D a = MTree.node l' r'
            ∧ (MTree.node l r).flatten ∈ l'.subtrees ∪ r'.subtrees := by
  intro u
  induction u with
  | leaf =>
    intro _ l r hmem
    simp [MTree.subtrees] at hmem
  | node ul ur ihl ihr =>
    intro hcomp l r hmem
    obtain ⟨hcl, hcr⟩ := hcomp
    rw [MTree.subtrees, Finset.mem_insert, Finset.mem_union] at hmem
    rcases hmem with heq | hmem | hmem
    · left
      rw [heq]
      exact MTree.mem_subtrees_self _
    · rcases ihl hcl hmem with h | h
      · exact Or.inl (MTree.subtrees_trans h (MTree.subtrees_node_left _ _))
      · exact Or.inr h
    · rcases ihr hcr hmem with h | h
      · exact Or.inl (MTree.subtrees_trans h (MTree.subtrees_node_right _ _))
      · exact Or.inr h
  | gnode ul ur ihl ihr =>
    intro hcomp l r hmem
    obtain ⟨⟨a, ha, hDa⟩, hcl, hcr⟩ := hcomp
    rw [MTree.subtrees, Finset.mem_insert, Finset.mem_union] at hmem
    rcases hmem with heq | hmem | hmem
    · exact absurd heq (by simp)
    · rcases ihl hcl hmem with h | h
      · exact Or.inr ⟨a, ha, ul.flatten, ur.flatten, hDa.symm, Finset.mem_union_left _ h⟩
      · exact Or.inr h
    · rcases ihr hcr hmem with h | h
      · exact Or.inr ⟨a, ha, ul.flatten, ur.flatten, hDa.symm, Finset.mem_union_right _ h⟩
      · exact Or.inr h

/-- The flattened type of a live remaining tree is live: it is a subtree of a core profile. -/
lemma typeOf_flatten_mem_live (σ : Bool) (τ : MTree) (hτ : typeOf σ τ ∈ P.live)
    (hcomp : MTree.AllComp P.S P.D τ) : typeOf σ τ.flatten ∈ P.live := by
  cases τ with
  | leaf => exact hτ
  | gnode l r => exact P.fresh_mem_live σ
  | node l r =>
    have hτ' : (σ, some (MTree.node l r)) ∈ P.live := hτ
    obtain ⟨k, hk, hsub, -, -⟩ := (P.mem_live_some_iff σ _).mp hτ'
    rcases flatten_mem_of_allComp (P.C σ k) (P.C_allComp σ k hk) hsub with
      h | ⟨a, ha, l', r', hDa, hmem⟩
    · exfalso
      obtain ⟨cl, cr, hC⟩ := P.C_gnode σ k hk
      rw [hC] at h
      simp [MTree.flatten, MTree.subtrees] at h
    · have hCa : P.C σ a = MTree.gnode l' r' := by
        rw [P.C_core σ a ha, hDa]
        rfl
      show (σ, some (MTree.node l.flatten r.flatten)) ∈ P.live
      rw [P.mem_live_some_iff]
      refine ⟨a, P.S_subset_supp σ ha, ?_, ?_, by simp⟩
      · rw [hCa, MTree.subtrees]
        exact Finset.mem_insert_of_mem hmem
      · rw [hCa]
        simp

/-- **The flattening of a realisation** (the construction of `thm:fresh-positive` and
`thm:atomic-normalisation`): a charged realisation `y` of the type of a remaining tree `τ`
of side `σ` that matches a source `x` under an automorphism can be replaced by a charged
realisation `y'` of the type of the flattened tree matching `x` under the same automorphism,
provided all states of `x` are realised (`V_μ`) and `b(0) > 0`. Every graft root becomes a
fresh vertex drawing the core arity of its core block and a charged state compatible with
the corresponding source state. -/
theorem flatten_realisation (hc : (P.toModel R zero μ).IsCompat)
    (hb0 : rE μ R zero ≠ 0) (σ : Bool) :
    ∀ (h : ℕ) (τ : MTree), MTree.AllComp P.S P.D τ →
      ∀ (hτ : typeOf σ τ ∈ P.live) (hτ' : typeOf σ τ.flatten ∈ P.live)
        (y x : FullLab (P.Live × V) h),
        (P.toModel R zero μ).rho ⟨typeOf σ τ, hτ⟩ h y ≠ 0 →
        Model.StatesIn (P.toModel R zero μ).Vmu h x →
        ∀ π : AutK 1 0 h, fullMatchesK (P.toModel R zero μ).srel 1 0 h π x y →
          ∃ y', (P.toModel R zero μ).rho ⟨typeOf σ τ.flatten, hτ'⟩ h y' ≠ 0
            ∧ fullMatchesK (P.toModel R zero μ).srel 1 0 h π x y' := by
  intro h
  induction h with
  | zero =>
    intro τ _ hτ hτ' y x hy hx π hm
    obtain ⟨-, hy2⟩ := (Model.rho_zero_ne_zero_iff _ _ y).mp hy
    have hm' : R x.2 y.2 := hm
    cases τ with
    | leaf => exact ⟨y, hy, hm⟩
    | node l r =>
      have hz := P.eq_zero_of_rootLaw_ne_zero R zero μ (τ := MTree.node l r) hτ hy2
      refine ⟨leaf (⟨_, hτ'⟩, zero), ?_, ?_⟩
      · rw [Model.rho_zero_ne_zero_iff]
        exact ⟨rfl, P.rootLaw_forced_zero_ne_zero R zero μ
          (τ := MTree.node l.flatten r.flatten) hτ'⟩
      · show R x.2 zero
        rw [← hz]
        exact hm'
    | gnode l r =>
      obtain ⟨w, hw, hxw⟩ := P.exists_fresh_state R zero μ hc hb0 hx
      refine ⟨leaf (⟨_, hτ'⟩, w), ?_, hxw⟩
      rw [Model.rho_zero_ne_zero_iff]
      exact ⟨rfl, P.rootLaw_fresh_ne_zero R zero μ hτ' hw⟩
  | succ h ih =>
    intro τ hcomp hτ hτ' y x hy hx π hm
    obtain ⟨b, π₁, π₂⟩ := π
    cases τ with
    | leaf => exact ⟨y, hy, hm⟩
    | node l r =>
      obtain ⟨hcl, hcr⟩ := hcomp
      obtain ⟨hl, hr⟩ := P.rootPair_mem_live_of_mem (σ := σ) (τ := MTree.node l r) hτ
      obtain ⟨hz, hj1, hj2⟩ := P.forced_children R zero μ (rootPair_node σ l r) hτ hl hr hy
      obtain ⟨hx0, hx1, hx2⟩ := hx
      obtain ⟨hm0, hm1, hm2⟩ :=
        (P.fullMatchesK_branch_iff R zero μ b π₁ π₂ x y.1 (y.2.1, y.2.2)).mp hm
      have hl' := P.typeOf_flatten_mem_live σ l hl hcl
      have hr' := P.typeOf_flatten_mem_live σ r hr hcr
      obtain ⟨y₁', y₂', hy₁', hy₂', hm₁', hm₂'⟩ := swap_lift
        (M1 := fun π x y => fullMatchesK (P.toModel R zero μ).srel 1 0 h π x y)
        (Sx := Model.StatesIn (P.toModel R zero μ).Vmu h)
        (C1 := fun y' => (P.toModel R zero μ).rho ⟨typeOf σ l.flatten, hl'⟩ h y' ≠ 0)
        (C2 := fun y' => (P.toModel R zero μ).rho ⟨typeOf σ r.flatten, hr'⟩ h y' ≠ 0) b
        (fun π x hx hm => ih l hcl hl hl' y.2.1 x hj1 hx π hm)
        (fun π x hx hm => ih r hcr hr hr' y.2.2 x hj2 hx π hm) hx1 hx2 hm1 hm2
      refine ⟨branch (⟨_, hτ'⟩, zero) (y₁', y₂'), ?_, ?_⟩
      · exact P.rho_forced_branch_ne_zero R zero μ (rootPair_node σ l.flatten r.flatten)
          hτ' hl' hr' hy₁' hy₂'
      · rw [P.fullMatchesK_branch_iff]
        refine ⟨?_, hm₁', hm₂'⟩
        show R x.1.2 zero
        rw [← hz]
        exact hm0
    | gnode l r =>
      obtain ⟨⟨a, ha, hDa⟩, hcl, hcr⟩ := hcomp
      obtain ⟨hl, hr⟩ := P.rootPair_mem_live_of_mem (σ := σ) (τ := MTree.gnode l r) hτ
      obtain ⟨-, hj1, hj2⟩ := P.forced_children R zero μ (rootPair_gnode σ l r) hτ hl hr hy
      obtain ⟨hx0, hx1, hx2⟩ := hx
      obtain ⟨hm0, hm1, hm2⟩ :=
        (P.fullMatchesK_branch_iff R zero μ b π₁ π₂ x y.1 (y.2.1, y.2.2)).mp hm
      have hl' := P.typeOf_flatten_mem_live σ l hl hcl
      have hr' := P.typeOf_flatten_mem_live σ r hr hcr
      obtain ⟨y₁', y₂', hy₁', hy₂', hm₁', hm₂'⟩ := swap_lift
        (M1 := fun π x y => fullMatchesK (P.toModel R zero μ).srel 1 0 h π x y)
        (Sx := Model.StatesIn (P.toModel R zero μ).Vmu h)
        (C1 := fun y' => (P.toModel R zero μ).rho ⟨typeOf σ l.flatten, hl'⟩ h y' ≠ 0)
        (C2 := fun y' => (P.toModel R zero μ).rho ⟨typeOf σ r.flatten, hr'⟩ h y' ≠ 0) b
        (fun π x hx hm => ih l hcl hl hl' y.2.1 x hj1 hx π hm)
        (fun π x hx hm => ih r hcr hr hr' y.2.2 x hj2 hx π hm) hx1 hx2 hm1 hm2
      obtain ⟨w, hw, hxw⟩ := P.exists_fresh_state R zero μ hc hb0 hx0
      refine ⟨branch (⟨_, hτ'⟩, w) (y₁', y₂'), ?_, ?_⟩
      · exact P.rho_fresh_branch_ne_zero R zero μ hτ' ha hDa hl' hr' hy₁' hy₂' hw
      · rw [P.fullMatchesK_branch_iff]
        exact ⟨hxw, hm₁', hm₂'⟩

/-- **Changing the side** (the target-side reproduction in `thm:fresh-positive`): a
charged realisation of the type of a remaining tree `τ` on side `σ` matching a source under
an automorphism can be replaced by a charged realisation of the type of `τ` on side `σ'`
matching the same source under the same automorphism, provided all states of the source
are realised and `b(0) > 0`. Below a fresh vertex the source-side profile is flattened to
its core block, whose arity is a core arity of either side. -/
theorem side_change (hc : (P.toModel R zero μ).IsCompat) (hb0 : rE μ R zero ≠ 0)
    (σ σ' : Bool) :
    ∀ (h : ℕ) (τ : MTree), MTree.AllComp P.S P.D τ →
      ∀ (hτ : typeOf σ τ ∈ P.live) (hτ' : typeOf σ' τ ∈ P.live)
        (y x : FullLab (P.Live × V) h),
        (P.toModel R zero μ).rho ⟨typeOf σ τ, hτ⟩ h y ≠ 0 →
        Model.StatesIn (P.toModel R zero μ).Vmu h x →
        ∀ π : AutK 1 0 h, fullMatchesK (P.toModel R zero μ).srel 1 0 h π x y →
          ∃ y', (P.toModel R zero μ).rho ⟨typeOf σ' τ, hτ'⟩ h y' ≠ 0
            ∧ fullMatchesK (P.toModel R zero μ).srel 1 0 h π x y' := by
  intro h
  induction h with
  | zero =>
    intro τ _ hτ hτ' y x hy _ π hm
    obtain ⟨-, hy2⟩ := (Model.rho_zero_ne_zero_iff _ _ y).mp hy
    refine ⟨leaf (⟨typeOf σ' τ, hτ'⟩, y.2), ?_, hm⟩
    rw [Model.rho_zero_ne_zero_iff]
    refine ⟨rfl, ?_⟩
    rw [P.rootLaw_typeOf R zero μ] at hy2 ⊢
    exact hy2
  | succ h ih =>
    intro τ hcomp hτ hτ' y x hy hx π hm
    obtain ⟨b, π₁, π₂⟩ := π
    have hy' : (P.toModel R zero μ).rho ⟨typeOf σ τ, hτ⟩ (h + 1)
        (branch y.1 (y.2.1, y.2.2)) ≠ 0 := hy
    rw [Model.rho_succ_ne_zero_iff] at hy'
    obtain ⟨-, hy2, j, hj, hj1, hj2⟩ := hy'
    obtain ⟨hx0, hx1, hx2⟩ := hx
    obtain ⟨hm0, hm1, hm2⟩ :=
      (P.fullMatchesK_branch_iff R zero μ b π₁ π₂ x y.1 (y.2.1, y.2.2)).mp hm
    have hroot : (P.toModel R zero μ).rootLaw ⟨typeOf σ' τ, hτ'⟩ y.1.2 ≠ 0 := by
      rw [P.rootLaw_typeOf R zero μ] at hy2 ⊢
      exact hy2
    cases τ with
    | leaf =>
      obtain ⟨⟨j1, hj1l⟩, ⟨j2, hj2l⟩⟩ := j
      have hraw : P.rawKernel (σ, none) (j1, j2) ≠ 0 :=
        (P.kernelL_ne_zero_iff ⟨(σ, none), hτ⟩ (⟨j1, hj1l⟩, ⟨j2, hj2l⟩)).mp hj
      obtain ⟨k, hk, hjeq⟩ := (P.rawKernel_fresh_ne_zero_iff σ (j1, j2)).mp hraw
      have hks : k ∈ P.supp σ := (P.mem_supp σ k).mp hk
      obtain ⟨l, r, hC⟩ := P.C_gnode σ k hks
      have hcompC := P.C_allComp σ k hks
      rw [hC] at hjeq hcompC
      change (j1, j2) = (typeOf σ l, typeOf σ r) at hjeq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hjeq
      obtain ⟨⟨a, ha, hDa⟩, hcl, hcr⟩ := hcompC
      have hl' := P.typeOf_flatten_mem_live σ l hj1l hcl
      have hr' := P.typeOf_flatten_mem_live σ r hj2l hcr
      obtain ⟨hl'', hr''⟩ := P.core_children_mem_live σ' ha hDa
      obtain ⟨y₁', y₂', hy₁', hy₂', hm₁', hm₂'⟩ := swap_lift
        (M1 := fun π x y => fullMatchesK (P.toModel R zero μ).srel 1 0 h π x y)
        (Sx := Model.StatesIn (P.toModel R zero μ).Vmu h)
        (C1 := fun y' => (P.toModel R zero μ).rho ⟨typeOf σ' l.flatten, hl''⟩ h y' ≠ 0)
        (C2 := fun y' => (P.toModel R zero μ).rho ⟨typeOf σ' r.flatten, hr''⟩ h y' ≠ 0) b
        (fun π x hx hm => by
          obtain ⟨z, hz, hmz⟩ := P.flatten_realisation R zero μ hc hb0 σ h l hcl hj1l hl'
            y.2.1 x hj1 hx π hm
          exact ih l.flatten (allComp_of_noGraft _ (MTree.flatten_noGraft l)) hl' hl'' z x
            hz hx π hmz)
        (fun π x hx hm => by
          obtain ⟨z, hz, hmz⟩ := P.flatten_realisation R zero μ hc hb0 σ h r hcr hj2l hr'
            y.2.2 x hj2 hx π hm
          exact ih r.flatten (allComp_of_noGraft _ (MTree.flatten_noGraft r)) hr' hr'' z x
            hz hx π hmz)
        hx1 hx2 hm1 hm2
      have hroot' : μ y.1.2 ≠ 0 := by
        rw [P.rootLaw_typeOf R zero μ, if_pos rfl] at hroot
        exact hroot
      refine ⟨branch (⟨typeOf σ' MTree.leaf, hτ'⟩, y.1.2) (y₁', y₂'), ?_, ?_⟩
      · exact P.rho_fresh_branch_ne_zero R zero μ hτ' ha hDa hl'' hr'' hy₁' hy₂' hroot'
      · rw [P.fullMatchesK_branch_iff]
        exact ⟨hm0, hm₁', hm₂'⟩
    | node l r =>
      obtain ⟨hcl, hcr⟩ := hcomp
      obtain ⟨hl, hr⟩ := P.rootPair_mem_live_of_mem (σ := σ) (τ := MTree.node l r) hτ
      obtain ⟨hl', hr'⟩ := P.rootPair_mem_live_of_mem (σ := σ') (τ := MTree.node l r) hτ'
      obtain ⟨-, hj1, hj2⟩ := P.forced_children R zero μ (rootPair_node σ l r) hτ hl hr hy
      obtain ⟨y₁', y₂', hy₁', hy₂', hm₁', hm₂'⟩ := swap_lift
        (M1 := fun π x y => fullMatchesK (P.toModel R zero μ).srel 1 0 h π x y)
        (Sx := Model.StatesIn (P.toModel R zero μ).Vmu h)
        (C1 := fun y' => (P.toModel R zero μ).rho ⟨typeOf σ' l, hl'⟩ h y' ≠ 0)
        (C2 := fun y' => (P.toModel R zero μ).rho ⟨typeOf σ' r, hr'⟩ h y' ≠ 0) b
        (fun π x hx hm => ih l hcl hl hl' y.2.1 x hj1 hx π hm)
        (fun π x hx hm => ih r hcr hr hr' y.2.2 x hj2 hx π hm) hx1 hx2 hm1 hm2
      refine ⟨branch (⟨typeOf σ' (MTree.node l r), hτ'⟩, y.1.2) (y₁', y₂'), ?_, ?_⟩
      · rw [P.eq_zero_of_rootLaw_ne_zero R zero μ (τ := MTree.node l r) hτ' hroot]
        exact P.rho_forced_branch_ne_zero R zero μ (rootPair_node σ' l r) hτ' hl' hr'
          hy₁' hy₂'
      · rw [P.fullMatchesK_branch_iff]
        exact ⟨hm0, hm₁', hm₂'⟩
    | gnode l r =>
      obtain ⟨-, hcl, hcr⟩ := hcomp
      obtain ⟨hl, hr⟩ := P.rootPair_mem_live_of_mem (σ := σ) (τ := MTree.gnode l r) hτ
      obtain ⟨hl', hr'⟩ := P.rootPair_mem_live_of_mem (σ := σ') (τ := MTree.gnode l r) hτ'
      obtain ⟨-, hj1, hj2⟩ := P.forced_children R zero μ (rootPair_gnode σ l r) hτ hl hr hy
      obtain ⟨y₁', y₂', hy₁', hy₂', hm₁', hm₂'⟩ := swap_lift
        (M1 := fun π x y => fullMatchesK (P.toModel R zero μ).srel 1 0 h π x y)
        (Sx := Model.StatesIn (P.toModel R zero μ).Vmu h)
        (C1 := fun y' => (P.toModel R zero μ).rho ⟨typeOf σ' l, hl'⟩ h y' ≠ 0)
        (C2 := fun y' => (P.toModel R zero μ).rho ⟨typeOf σ' r, hr'⟩ h y' ≠ 0) b
        (fun π x hx hm => ih l hcl hl hl' y.2.1 x hj1 hx π hm)
        (fun π x hx hm => ih r hcr hr hr' y.2.2 x hj2 hx π hm) hx1 hx2 hm1 hm2
      refine ⟨branch (⟨typeOf σ' (MTree.gnode l r), hτ'⟩, y.1.2) (y₁', y₂'), ?_, ?_⟩
      · rw [P.eq_zero_of_rootLaw_ne_zero R zero μ (τ := MTree.gnode l r) hτ' hroot]
        exact P.rho_forced_branch_ne_zero R zero μ (rootPair_gnode σ' l r) hτ' hl' hr'
          hy₁' hy₂'
      · rw [P.fullMatchesK_branch_iff]
        exact ⟨hm0, hm₁', hm₂'⟩

/-- **`thm:fresh-positive`**: every charged realisation of a fresh type has positive degree
against either fresh type. -/
theorem freshPositive (hc : (P.toModel R zero μ).IsCompat) (hb0 : rE μ R zero ≠ 0) :
    (P.toModel R zero μ).FreshPositive := by
  intro h f f' x hf hf' hx
  obtain ⟨⟨σ, oτ⟩, hfl⟩ := f
  obtain ⟨⟨σ', oτ'⟩, hfl'⟩ := f'
  have hoτ : oτ = none := hf
  have hoτ' : oτ' = none := hf'
  subst hoτ hoτ'
  obtain ⟨π, hπ⟩ := fullSim_refl (P.toModel R zero μ).srel (Model.srel_refl _ hc) h x
  obtain ⟨y', hy', hm'⟩ := P.side_change R zero μ hc hb0 σ σ' h MTree.leaf trivial hfl hfl'
    x x hx (Model.statesIn_of_rho_ne_zero _ _ h x hx) π hπ
  rw [Model.deg, rE_ne_zero_iff']
  exact ⟨y', Exists.intro π hm', hy'⟩

/-- The selected transitions (`eq:transition-budget`, `sec:positive-fresh`): the root pairs
of the core profiles at a fresh type, the unique transition at a forced type. -/
noncomputable def selJ (t : P.Live) : Finset (P.Live × P.Live) :=
  match t.1 with
  | (σ, none) => P.S.image fun a => (P.toLive (rootPair σ (P.C σ a)).1,
      P.toLive (rootPair σ (P.C σ a)).2)
  | (σ, some τ) => {(P.toLive (rootPair σ τ).1, P.toLive (rootPair σ τ).2)}

/-- **`thm:atomic-normalisation`**: the core root pairs are a transition selection. -/
noncomputable def selection (hc : (P.toModel R zero μ).IsCompat) (hb0 : rE μ R zero ≠ 0) :
    Model.Selection (P.toModel R zero μ) where
  J := P.selJ
  nonempty := by
    intro t
    obtain ⟨⟨σ, oτ⟩, ht⟩ := t
    cases oτ with
    | none =>
      show (P.S.image _).Nonempty
      exact P.S_nonempty.image _
    | some τ =>
      show ({_} : Finset (P.Live × P.Live)).Nonempty
      exact Finset.singleton_nonempty _
  charged := by
    intro t j hj
    obtain ⟨⟨σ, oτ⟩, ht⟩ := t
    cases oτ with
    | none =>
      have hj' : j ∈ P.S.image fun a =>
          (P.toLive (rootPair σ (P.C σ a)).1, P.toLive (rootPair σ (P.C σ a)).2) := hj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj'
      have hraw : P.rawKernel (σ, none) (rootPair σ (P.C σ a)) ≠ 0 :=
        (P.rawKernel_fresh_ne_zero_iff σ _).mpr
          ⟨a, (P.mem_supp σ a).mpr (P.S_subset_supp σ ha), rfl⟩
      obtain ⟨h1, h2⟩ := P.rawKernel_live ⟨(σ, none), ht⟩ _ hraw
      show P.kernelL ⟨(σ, none), ht⟩ _ ≠ 0
      rw [P.toLive_of_mem h1, P.toLive_of_mem h2, P.kernelL_apply_of_live]
      exact hraw
    | some τ =>
      have hj' : j = (P.toLive (rootPair σ τ).1, P.toLive (rootPair σ τ).2) :=
        Finset.mem_singleton.mp hj
      subst hj'
      show P.kernelL ⟨(σ, some τ), ht⟩ _ ≠ 0
      rw [P.kernelL_forced, PMF.pure_apply, if_pos rfl]
      exact one_ne_zero
  positive := by
    intro t h p hp1 hp2 hr
    rw [Model.childMix, Ne, rE_bind_eq_zero_iff] at hr
    push Not at hr
    obtain ⟨j, hj, hj'⟩ := hr
    obtain ⟨⟨σ, oτ⟩, ht⟩ := t
    cases oτ with
    | some τ =>
      have hjeq := P.eq_of_kernelL_forced_ne_zero ht hj
      subst hjeq
      exact ⟨_, Finset.mem_singleton_self _, hj'⟩
    | none =>
      obtain ⟨⟨j1, hj1l⟩, ⟨j2, hj2l⟩⟩ := j
      have hraw : P.rawKernel (σ, none) (j1, j2) ≠ 0 :=
        (P.kernelL_ne_zero_iff ⟨(σ, none), ht⟩ (⟨j1, hj1l⟩, ⟨j2, hj2l⟩)).mp hj
      obtain ⟨k, hk, hjeq⟩ := (P.rawKernel_fresh_ne_zero_iff σ (j1, j2)).mp hraw
      have hks : k ∈ P.supp σ := (P.mem_supp σ k).mp hk
      obtain ⟨l, r, hC⟩ := P.C_gnode σ k hks
      have hcompC := P.C_allComp σ k hks
      rw [hC] at hjeq hcompC
      change (j1, j2) = (typeOf σ l, typeOf σ r) at hjeq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hjeq
      obtain ⟨⟨a, ha, hDa⟩, hcl, hcr⟩ := hcompC
      obtain ⟨⟨y1, y2⟩, hsq, hy⟩ := (rE_ne_zero_iff' _ _ _).mp hj'
      rw [prodPMF_apply] at hy
      have hy1 : (P.toModel R zero μ).rho ⟨typeOf σ l, hj1l⟩ h y1 ≠ 0 :=
        left_ne_zero_of_mul hy
      have hy2 : (P.toModel R zero μ).rho ⟨typeOf σ r, hj2l⟩ h y2 ≠ 0 :=
        right_ne_zero_of_mul hy
      have hl' := P.typeOf_flatten_mem_live σ l hj1l hcl
      have hr' := P.typeOf_flatten_mem_live σ r hj2l hcr
      have hsel : ((⟨typeOf σ l.flatten, hl'⟩ : P.Live),
          (⟨typeOf σ r.flatten, hr'⟩ : P.Live)) ∈ P.selJ ⟨(σ, none), ht⟩ := by
        show _ ∈ P.S.image _
        refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
        have hCa : P.C σ a = MTree.gnode l.flatten r.flatten := by
          rw [P.C_core σ a ha, ← hDa]
          rfl
        rw [hCa]
        show (P.toLive (typeOf σ l.flatten), P.toLive (typeOf σ r.flatten)) = _
        rw [P.toLive_of_mem hl', P.toLive_of_mem hr']
        rfl
      refine ⟨_, hsel, ?_⟩
      rw [rE_ne_zero_iff']
      rcases hsq with ⟨⟨π1, hm1⟩, ⟨π2, hm2⟩⟩ | ⟨⟨π1, hm1⟩, ⟨π2, hm2⟩⟩
      · obtain ⟨y1', hy1', hm1'⟩ := P.flatten_realisation R zero μ hc hb0 σ h l hcl hj1l hl'
          y1 p.1 hy1 hp1 π1 hm1
        obtain ⟨y2', hy2', hm2'⟩ := P.flatten_realisation R zero μ hc hb0 σ h r hcr hj2l hr'
          y2 p.2 hy2 hp2 π2 hm2
        refine ⟨(y1', y2'), Or.inl ⟨Exists.intro π1 hm1', Exists.intro π2 hm2'⟩, ?_⟩
        rw [prodPMF_apply]
        exact mul_ne_zero hy1' hy2'
      · obtain ⟨y2', hy2', hm2'⟩ := P.flatten_realisation R zero μ hc hb0 σ h r hcr hj2l hr'
          y2 p.1 hy2 hp1 π1 hm1
        obtain ⟨y1', hy1', hm1'⟩ := P.flatten_realisation R zero μ hc hb0 σ h l hcl hj1l hl'
          y1 p.2 hy1 hp2 π2 hm2
        refine ⟨(y1', y2'), Or.inr ⟨Exists.intro π1 hm2', Exists.intro π2 hm1'⟩, ?_⟩
        rw [prodPMF_apply]
        exact mul_ne_zero hy1' hy2'

/-- **The budget** (`sec:positive-fresh`): `∑_{j ∈ J_t} π_t(j)^{-α} ≤ max_σ ∑_{a ∈ S} ν_σ(a)^{-α}`
for every live type. -/
theorem budget_le (hc : (P.toModel R zero μ).IsCompat) (hb0 : rE μ R zero ≠ 0) {α : ℝ}
    (hα : 0 ≤ α) (t : P.Live) :
    (P.selection R zero μ hc hb0).budget α t
      ≤ max (∑ a ∈ P.S, (P.ν false a) ^ (-α)) (∑ a ∈ P.S, (P.ν true a) ^ (-α)) := by
  have hmax : ∀ σ, (∑ a ∈ P.S, (P.ν σ a) ^ (-α))
      ≤ max (∑ a ∈ P.S, (P.ν false a) ^ (-α)) (∑ a ∈ P.S, (P.ν true a) ^ (-α)) := by
    intro σ
    cases σ
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hone : ∀ σ, (1 : ℝ≥0∞) ≤ ∑ a ∈ P.S, (P.ν σ a) ^ (-α) := by
    intro σ
    obtain ⟨a, ha⟩ := P.S_nonempty
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => zero_le) ha)
    calc (1 : ℝ≥0∞) = (P.ν σ a) ^ (0 : ℝ) := ENNReal.rpow_zero.symm
      _ ≤ (P.ν σ a) ^ (-α) :=
        ENNReal.rpow_le_rpow_of_exponent_ge (PMF.coe_le_one _ _) (by linarith)
  obtain ⟨⟨σ, oτ⟩, ht⟩ := t
  cases oτ with
  | some τ =>
    show ∑ j ∈ ({(P.toLive (rootPair σ τ).1, P.toLive (rootPair σ τ).2)} :
        Finset (P.Live × P.Live)),
      ((P.toModel R zero μ).π ⟨(σ, some τ), ht⟩ j) ^ (-α) ≤ _
    rw [Finset.sum_singleton]
    have h1 : (P.toModel R zero μ).π ⟨(σ, some τ), ht⟩
        (P.toLive (rootPair σ τ).1, P.toLive (rootPair σ τ).2) = 1 := by
      show P.kernelL ⟨(σ, some τ), ht⟩ _ = 1
      rw [P.kernelL_forced, PMF.pure_apply, if_pos rfl]
    rw [h1, ENNReal.one_rpow]
    exact (hone σ).trans (hmax σ)
  | none =>
    show ∑ j ∈ P.S.image (fun a =>
        (P.toLive (rootPair σ (P.C σ a)).1, P.toLive (rootPair σ (P.C σ a)).2)),
      ((P.toModel R zero μ).π ⟨(σ, none), ht⟩ j) ^ (-α) ≤ _
    refine le_trans (Finset.sum_image_le_of_nonneg fun _ _ => zero_le) ?_
    refine le_trans (Finset.sum_le_sum fun a ha => ?_) (hmax σ)
    apply rpow_neg_antitone hα
    have hraw : P.rawKernel (σ, none) (rootPair σ (P.C σ a)) ≠ 0 :=
      (P.rawKernel_fresh_ne_zero_iff σ _).mpr
        ⟨a, (P.mem_supp σ a).mpr (P.S_subset_supp σ ha), rfl⟩
    obtain ⟨h1, h2⟩ := P.rawKernel_live ⟨(σ, none), ht⟩ _ hraw
    show P.ν σ a ≤ P.kernelL ⟨(σ, none), ht⟩ _
    rw [P.toLive_of_mem h1, P.toLive_of_mem h2, P.kernelL_apply_of_live, rawKernel_fresh,
      PMF.map_apply]
    refine le_trans ?_ (ENNReal.le_tsum a)
    rw [if_pos rfl]

/-- The subtrees other than leaves of a tree number at most its leaves minus one: a full
binary tree with `k` leaves has `k - 1` internal vertices (`eq:type-count`). -/
private lemma card_internal_le :
    ∀ t : MTree, (t.subtrees.filter fun τ => τ ≠ MTree.leaf).card + 1 ≤ t.leaves
  | .leaf => by simp [MTree.subtrees, MTree.leaves]
  | .node l r => by
    have ihl := card_internal_le l
    have ihr := card_internal_le r
    have hsub : ((MTree.node l r).subtrees.filter fun τ => τ ≠ MTree.leaf)
        ⊆ insert (MTree.node l r) ((l.subtrees.filter fun τ => τ ≠ MTree.leaf)
          ∪ (r.subtrees.filter fun τ => τ ≠ MTree.leaf)) := by
      intro τ hτ
      rw [Finset.mem_filter, MTree.subtrees, Finset.mem_insert, Finset.mem_union] at hτ
      rw [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases hτ with ⟨h | h | h, hne⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h, hne⟩)
      · exact Or.inr (Or.inr ⟨h, hne⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (MTree.node l r)
      ((l.subtrees.filter fun τ => τ ≠ MTree.leaf)
        ∪ (r.subtrees.filter fun τ => τ ≠ MTree.leaf))
    have h3 := Finset.card_union_le (l.subtrees.filter fun τ => τ ≠ MTree.leaf)
      (r.subtrees.filter fun τ => τ ≠ MTree.leaf)
    show _ + 1 ≤ l.leaves + r.leaves
    omega
  | .gnode l r => by
    have ihl := card_internal_le l
    have ihr := card_internal_le r
    have hsub : ((MTree.gnode l r).subtrees.filter fun τ => τ ≠ MTree.leaf)
        ⊆ insert (MTree.gnode l r) ((l.subtrees.filter fun τ => τ ≠ MTree.leaf)
          ∪ (r.subtrees.filter fun τ => τ ≠ MTree.leaf)) := by
      intro τ hτ
      rw [Finset.mem_filter, MTree.subtrees, Finset.mem_insert, Finset.mem_union] at hτ
      rw [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases hτ with ⟨h | h | h, hne⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h, hne⟩)
      · exact Or.inr (Or.inr ⟨h, hne⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (MTree.gnode l r)
      ((l.subtrees.filter fun τ => τ ≠ MTree.leaf)
        ∪ (r.subtrees.filter fun τ => τ ≠ MTree.leaf))
    have h3 := Finset.card_union_le (l.subtrees.filter fun τ => τ ≠ MTree.leaf)
      (r.subtrees.filter fun τ => τ ≠ MTree.leaf)
    show _ + 1 ≤ l.leaves + r.leaves
    omega

/-- The proper subtrees other than leaves of a tree other than a leaf number at most its
leaves minus two (`eq:type-count`: the internal vertices other than the root). -/
private lemma card_proper_internal_le (t : MTree) (ht : t ≠ MTree.leaf) :
    (t.subtrees.filter fun τ => τ ≠ t ∧ τ ≠ MTree.leaf).card + 2 ≤ t.leaves := by
  have h1 := card_internal_le t
  have hsub : insert t (t.subtrees.filter fun τ => τ ≠ t ∧ τ ≠ MTree.leaf)
      ⊆ t.subtrees.filter fun τ => τ ≠ MTree.leaf := by
    intro τ hτ
    rw [Finset.mem_insert, Finset.mem_filter] at hτ
    rw [Finset.mem_filter]
    rcases hτ with rfl | ⟨h, -, h2⟩
    · exact ⟨MTree.mem_subtrees_self _, ht⟩
    · exact ⟨h, h2⟩
  have hnot : t ∉ t.subtrees.filter fun τ => τ ≠ t ∧ τ ≠ MTree.leaf := by
    rw [Finset.mem_filter]
    rintro ⟨-, h, -⟩
    exact h rfl
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at h2
  omega

/-- **`eq:type-count`**: the number of live types is at most
`2 + ∑_σ ∑_{k ∈ supp ν_σ} (k - 2)`. -/
theorem card_live_le :
    P.live.card ≤ 2 + ∑ σ : Bool, ∑ k ∈ P.supp σ, (k - 2) := by
  rw [live]
  refine (Finset.card_union_le _ _).trans ?_
  rw [Finset.card_pair (by simp)]
  refine Nat.add_le_add_left ?_ 2
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun σ _ => ?_)
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k hk => ?_)
  refine Finset.card_image_le.trans ?_
  have hne : P.C σ k ≠ MTree.leaf := by
    obtain ⟨l, r, hC⟩ := P.C_gnode σ k hk
    rw [hC]
    simp
  have := card_proper_internal_le (P.C σ k) hne
  rw [P.C_leaves σ k hk] at this
  omega

/-- The maximal profile height `ℓ`. -/
noncomputable def ell : ℕ := (Finset.univ (α := Bool)).sup fun σ => (P.supp σ).sup fun k => (P.C σ k).height

/-- Every live forced type has remaining tree of height at most `ℓ`. -/
lemma height_le_ell (σ : Bool) (τ : MTree) (h : (σ, some τ) ∈ P.live) : τ.height ≤ P.ell := by
  obtain ⟨k, hk, hsub, -, -⟩ := (P.mem_live_some_iff σ τ).mp h
  refine (MTree.height_le_of_mem_subtrees hsub).trans ?_
  refine le_trans (Finset.le_sup (f := fun k => (P.C σ k).height) hk) ?_
  exact Finset.le_sup (f := fun σ => (P.supp σ).sup fun k => (P.C σ k).height)
    (Finset.mem_univ σ)

end Presentation

end GraphMarkovMatching.Stopped
