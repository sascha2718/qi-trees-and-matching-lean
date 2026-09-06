import Mathlib.Tactic

/-!
`sec:encoding` of `matching_classes_simple.tex`, the deterministic layer of the
chain encoding.

* `Word`: finite words over two letters; `false` is the paper's letter `1`
  (the chain direction) and `true` its letter `2`.
* `InTree χ`: the sample tree of an offspring field `χ : Word → Bool`
  (`false` = one child, `true` = two children), as a prefix-closed vertex set.
* `Chains χ`: every chain terminates, the deterministic content of the event
  `Ω₀`; its probability is not this file's concern.
* `kappa` (the chain length), `iota` (`eq:phi-def`; its unfolding is
  `eq:normal-form`), `lab` (`eq:lambda-def`).
* `thm:chains`: `ray_chain_disjoint` is part (ii); `mem_chain_of_mem_tree`,
  `mem_tree_of_mem_chain`, `chain_unique` and `chain_level_unique` assemble
  part (i), the chain partition of the tree.
-/

namespace ChainClasses

/-- Finite words over two letters; `false` is the paper's letter `1`. -/
abbrev Word : Type := List Bool

variable (χ : Word → Bool)

/-- The sample tree of the offspring field `χ`: the root, one child `v·1`
always (`θ₀ = 0`: every vertex has at least one child), and a second child
`v·2` exactly when `χ v = true`. -/
inductive InTree : Word → Prop
  | root : InTree []
  | one {v : Word} : InTree v → InTree (v ++ [false])
  | two {v : Word} : InTree v → χ v = true → InTree (v ++ [true])

/-- Every chain terminates: the deterministic content of `Ω₀`. -/
def Chains : Prop := ∀ v : Word, ∃ k : ℕ, χ (v ++ List.replicate k false) = true

variable {χ}

/-- The chain length `κ(v)`, the least `k ≥ 1` with `χ(v·1^{k-1}) = 2`. -/
noncomputable def kappa (hχ : Chains χ) (v : Word) : ℕ := Nat.find (hχ v) + 1

lemma kappa_pos (hχ : Chains χ) (v : Word) : 1 ≤ kappa hχ v := Nat.le_add_left 1 _

/-- The defining property of `κ`: the branch point sits at `v·1^{κ(v)-1}`. -/
lemma kappa_spec (hχ : Chains χ) (v : Word) :
    χ (v ++ List.replicate (kappa hχ v - 1) false) = true := by
  simpa [kappa] using Nat.find_spec (hχ v)

/-- Minimality of `κ`: below the branch point every vertex has one child. -/
lemma kappa_min (hχ : Chains χ) (v : Word) {l : ℕ} (hl : l < kappa hχ v - 1) :
    χ (v ++ List.replicate l false) = false := by
  have h := Nat.find_min (hχ v) (m := l) (by simp only [kappa] at hl; omega)
  simpa using h

/-- `eq:phi-def`, iterated: the map `ι` locating chain starts, arriving directly in the
normal form `eq:normal-form`. -/
noncomputable def iota (hχ : Chains χ) (w : Word) : Word :=
  w.foldl (fun v j => v ++ List.replicate (kappa hχ v - 1) false ++ [j]) []

@[simp] lemma iota_nil (hχ : Chains χ) : iota hχ [] = [] := rfl

/-- `eq:phi-def`: the recursion step of `ι`. -/
lemma iota_concat (hχ : Chains χ) (w : Word) (j : Bool) :
    iota hχ (w ++ [j])
      = iota hχ w ++ List.replicate (kappa hχ (iota hχ w) - 1) false ++ [j] := by
  simp [iota, List.foldl_append]

/-- `eq:lambda-def`: the label of `w`. -/
noncomputable def lab (hχ : Chains χ) (w : Word) : ℕ := kappa hχ (iota hχ w)

lemma lab_pos (hχ : Chains χ) (w : Word) : 1 ≤ lab hχ w := kappa_pos hχ _

/-- The chain of `w`: the vertices `ι(w)·1^l`, `0 ≤ l ≤ λ(w) - 1`. -/
def InChain (hχ : Chains χ) (w : Word) (v : Word) : Prop :=
  ∃ l : ℕ, l ≤ lab hχ w - 1 ∧ v = iota hχ w ++ List.replicate l false

/-- The ray of `w`: the vertices `ι(w)·1^j`, `j ≥ 0`. -/
def InRay (hχ : Chains χ) (w : Word) (v : Word) : Prop :=
  ∃ j : ℕ, v = iota hχ w ++ List.replicate j false

lemma InChain.toRay {hχ : Chains χ} {w v : Word} (h : InChain hχ w v) :
    InRay hχ w v := by
  obtain ⟨l, _, rfl⟩ := h; exact ⟨l, rfl⟩

/-! ### Prefix structure of `ι` -/

/-- The recursion only appends: `ι` is monotone for the prefix order. -/
lemma iota_prefix (hχ : Chains χ) {w w' : Word} (h : w <+: w') :
    iota hχ w <+: iota hχ w' := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc]
      calc iota hχ w <+: iota hχ (w ++ u) := ih
        _ <+: iota hχ (w ++ u ++ [j]) := by
            rw [iota_concat]
            exact (List.prefix_append _ _).trans (List.prefix_append _ _)

/-- The length of `ι` grows by exactly `λ` per letter. -/
lemma iota_concat_length (hχ : Chains χ) (w : Word) (j : Bool) :
    (iota hχ (w ++ [j])).length = (iota hχ w).length + lab hχ w := by
  rw [iota_concat]
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  have h1 := lab_pos hχ w
  simp only [lab] at h1 ⊢
  omega

/-! ### Part (ii) of `thm:chains` -/

/-- First divergence of two prefix-incomparable words. -/
lemma exists_diverge {w w' : Word} (h1 : ¬ w <+: w') (h2 : ¬ w' <+: w) :
    ∃ (p : Word) (a b : Bool), a ≠ b ∧ (p ++ [a]) <+: w ∧ (p ++ [b]) <+: w' := by
  induction w generalizing w' with
  | nil => exact absurd (List.nil_prefix) h1
  | cons x t ih =>
      cases w' with
      | nil => exact absurd (List.nil_prefix) h2
      | cons x' t' =>
          by_cases hx : x = x'
          · subst hx
            have h1' : ¬ t <+: t' := fun hp => h1 ((List.cons_prefix_cons).mpr ⟨rfl, hp⟩)
            have h2' : ¬ t' <+: t := fun hp => h2 ((List.cons_prefix_cons).mpr ⟨rfl, hp⟩)
            obtain ⟨p, a, b, hab, hpa, hpb⟩ := ih h1' h2'
            exact ⟨x :: p, a, b, hab,
              (List.cons_prefix_cons).mpr ⟨rfl, hpa⟩,
              (List.cons_prefix_cons).mpr ⟨rfl, hpb⟩⟩
          · exact ⟨[], x, x', hx, ⟨t, rfl⟩, ⟨t', rfl⟩⟩

/-- Two prefixes of one word are comparable. -/
lemma prefix_total_of_prefix : ∀ {v p q : Word}, p <+: v → q <+: v →
    p <+: q ∨ q <+: p := by
  intro v
  induction v with
  | nil =>
      intro p q hp hq
      rw [List.prefix_nil] at hp hq
      subst hp; subst hq
      exact Or.inl (List.prefix_refl _)
  | cons x t ih =>
      intro p q hp hq
      cases p with
      | nil => exact Or.inl (List.nil_prefix)
      | cons a p' =>
          cases q with
          | nil => exact Or.inr (List.nil_prefix)
          | cons b q' =>
              rw [List.cons_prefix_cons] at hp hq
              obtain ⟨rfl, hp'⟩ := hp
              obtain ⟨rfl, hq'⟩ := hq
              rcases ih hp' hq' with h | h
              · exact Or.inl ((List.cons_prefix_cons).mpr ⟨rfl, h⟩)
              · exact Or.inr ((List.cons_prefix_cons).mpr ⟨rfl, h⟩)

/-- Two prefixes of one word of equal length coincide. -/
lemma prefix_eq_of_length {v p q : Word} (hp : p <+: v) (hq : q <+: v)
    (hlen : p.length = q.length) : p = q := by
  rcases prefix_total_of_prefix hp hq with h | h
  · exact List.IsPrefix.eq_of_length h hlen
  · exact (List.IsPrefix.eq_of_length h hlen.symm).symm

/-- **`thm:chains`, part (ii)**: if `w` is not a prefix of `w'`, the ray of `w`
is disjoint from the chain of `w'`. -/
theorem ray_chain_disjoint (hχ : Chains χ) {w w' : Word} (h : ¬ w <+: w')
    {v : Word} (hv : InRay hχ w v) (hv' : InChain hχ w' v) : False := by
  obtain ⟨j, hj⟩ := hv
  obtain ⟨l, hl, hl'⟩ := hv'
  by_cases h2 : w' <+: w
  · -- `w'` is a strict prefix of `w`: compare lengths.
    obtain ⟨u, rfl⟩ := h2
    cases u with
    | nil => exact h (by simp)
    | cons c rest =>
        have hpre : iota hχ (w' ++ [c]) <+: iota hχ (w' ++ c :: rest) :=
          iota_prefix hχ ⟨rest, by simp⟩
        have hlen1 : (iota hχ (w' ++ [c])).length ≤ (iota hχ (w' ++ c :: rest)).length :=
          hpre.length_le
        have hlen2 : (iota hχ (w' ++ [c])).length = (iota hχ w').length + lab hχ w' :=
          iota_concat_length hχ w' c
        have hv1 : v.length = (iota hχ (w' ++ c :: rest)).length + j := by
          rw [hj]; simp
        have hv2 : v.length = (iota hχ w').length + l := by
          rw [hl']; simp
        have hlab := lab_pos hχ w'
        omega
  · -- divergent words: the letters after the common prefix differ.
    obtain ⟨p, a, b, hab, hpa, hpb⟩ := exists_diverge h h2
    -- both `ι(p·a)` and `ι(p·b)` are prefixes of `v`, of equal length
    have hqa : iota hχ (p ++ [a]) <+: v := by
      have h1 : iota hχ (p ++ [a]) <+: iota hχ w := iota_prefix hχ hpa
      have h2' : iota hχ w <+: v := ⟨List.replicate j false, hj.symm⟩
      exact h1.trans h2'
    have hqb : iota hχ (p ++ [b]) <+: v := by
      have h1 : iota hχ (p ++ [b]) <+: iota hχ w' := iota_prefix hχ hpb
      have h2' : iota hχ w' <+: v := ⟨List.replicate l false, hl'.symm⟩
      exact h1.trans h2'
    have hlen : (iota hχ (p ++ [a])).length = (iota hχ (p ++ [b])).length := by
      rw [iota_concat_length, iota_concat_length]
    have heq := prefix_eq_of_length hqa hqb hlen
    rw [iota_concat, iota_concat] at heq
    have : a = b := by
      have := List.append_cancel_left heq
      simpa using this
    exact hab this

/-! ### Part (i) of `thm:chains` -/

/-- Rays stay inside the tree: the chain letter is always available. -/
lemma ray_mem_tree {v : Word} (hv : InTree χ v) (j : ℕ) :
    InTree χ (v ++ List.replicate j false) := by
  induction j with
  | zero => simpa using hv
  | succ j ih =>
      have hstep : v ++ List.replicate (j + 1) false
          = (v ++ List.replicate j false) ++ [false] := by
        rw [List.replicate_succ', ← List.append_assoc]
      rw [hstep]
      exact InTree.one ih

/-- `ι` lands in the tree. -/
lemma iota_mem_tree (hχ : Chains χ) (w : Word) : InTree χ (iota hχ w) := by
  induction w using List.reverseRecOn with
  | nil => exact InTree.root
  | append_singleton w j ih =>
      rw [iota_concat]
      cases j with
      | false => exact InTree.one (ray_mem_tree ih _)
      | true => exact InTree.two (ray_mem_tree ih _) (kappa_spec hχ _)

/-- Chains lie inside the tree. -/
lemma mem_tree_of_mem_chain (hχ : Chains χ) {w v : Word} (h : InChain hχ w v) :
    InTree χ v := by
  obtain ⟨l, _, rfl⟩ := h
  exact ray_mem_tree (iota_mem_tree hχ w) l

/-- Every tree vertex lies in a chain. -/
lemma mem_chain_of_mem_tree (hχ : Chains χ) {v : Word} (hv : InTree χ v) :
    ∃ w, InChain hχ w v := by
  induction hv with
  | root => exact ⟨[], 0, Nat.zero_le _, by simp⟩
  | @one v hv ih =>
      obtain ⟨w, l, hl, rfl⟩ := ih
      by_cases hcase : l + 1 ≤ lab hχ w - 1
      · refine ⟨w, l + 1, hcase, ?_⟩
        rw [List.replicate_succ', ← List.append_assoc]
      · have hl' : l = lab hχ w - 1 := by omega
        refine ⟨w ++ [false], 0, Nat.zero_le _, ?_⟩
        rw [iota_concat]
        subst hl'
        simp [lab]
  | @two v hv hχv ih =>
      obtain ⟨w, l, hl, rfl⟩ := ih
      have hl' : l = lab hχ w - 1 := by
        by_contra hne
        have hlt : l < kappa hχ (iota hχ w) - 1 := by
          simp only [lab] at hl hne; omega
        have hfalse := kappa_min hχ (iota hχ w) hlt
        rw [hfalse] at hχv
        exact Bool.false_ne_true hχv
      refine ⟨w ++ [true], 0, Nat.zero_le _, ?_⟩
      rw [iota_concat]
      subst hl'
      simp [lab]

/-- **`thm:chains`, part (i), uniqueness of the chain**: distinct chains are
disjoint. -/
theorem chain_unique (hχ : Chains χ) {w w' v : Word}
    (h : InChain hχ w v) (h' : InChain hχ w' v) : w = w' := by
  by_contra hne
  by_cases hp : w <+: w'
  · have hp' : ¬ w' <+: w := fun hp' =>
      hne (List.IsPrefix.eq_of_length hp
        (Nat.le_antisymm (List.IsPrefix.length_le hp) (List.IsPrefix.length_le hp')))
    exact ray_chain_disjoint hχ hp' h'.toRay h
  · exact ray_chain_disjoint hχ hp h.toRay h'

/-- **`thm:chains`, part (i), uniqueness of the level**. -/
theorem chain_level_unique (hχ : Chains χ) {w v : Word} {l l' : ℕ}
    (h : v = iota hχ w ++ List.replicate l false)
    (h' : v = iota hχ w ++ List.replicate l' false) : l = l' := by
  have := congrArg List.length (h.symm.trans h')
  simpa using this

/-- **`thm:chains`, part (i)**: the tree is the union of the chains. -/
theorem tree_eq_chains (hχ : Chains χ) (v : Word) :
    InTree χ v ↔ ∃ w, InChain hχ w v :=
  ⟨mem_chain_of_mem_tree hχ, fun ⟨_, h⟩ => mem_tree_of_mem_chain hχ h⟩

end ChainClasses
