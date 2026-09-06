import Mathlib.Tactic
import ChainClasses.Chain.Labelling

/-!
`thm:isometry` of `matching_classes_simple.tex`: automorphisms of the index
tree act on labellings, and this action is by isometries of the associated
trees.

* `autOf`: the automorphism of the binary index tree determined by a portrait
  `σ : Word → Bool ≃ Bool`, applying `σ p` to the letter after the prefix `p`;
  it preserves lengths (`autOf_length`), prefixes (`autOf_prefix_iff`) and
  first divergences (`autOf_diverge`).
* `relabelMap`: the vertex map of the tex proof, sending the normal form over
  `w` to the normal form over `autOf σ w` at the same level.
* `isometry_of_relabel`: `thm:isometry`, stated for `lam = lam' ∘ autOf σ`
  (the tex's `λ'(w) = λ(π⁻¹ w)` with `π = autOf σ`): `relabelMap` maps the
  tree associated with `lam` onto the tree associated with `lam'`, preserving
  `treeDist`.
-/

namespace ChainClasses

/-! ### Portrait automorphisms of the index tree -/

/-- The automorphism of the index tree with portrait `σ`: the letter after the
consumed prefix `p` is transformed by `σ p`. -/
def autOf (σ : Word → Bool ≃ Bool) (w : Word) : Word :=
  (w.foldl (fun p j => (p.1 ++ [j], p.2 ++ [σ p.1 j])) (([] : Word), ([] : Word))).2

/-- The first fold component records the consumed prefix. -/
lemma autOf_foldl_fst (σ : Word → Bool ≃ Bool) (w a b : Word) :
    (w.foldl (fun p j => (p.1 ++ [j], p.2 ++ [σ p.1 j])) (a, b)).1 = a ++ w := by
  induction w generalizing a b with
  | nil => simp
  | cons j t ih => simpa using ih (a ++ [j]) (b ++ [σ a j])

@[simp] lemma autOf_nil (σ : Word → Bool ≃ Bool) : autOf σ [] = [] := rfl

/-- The recursion step of `autOf`. -/
lemma autOf_concat (σ : Word → Bool ≃ Bool) (w : Word) (j : Bool) :
    autOf σ (w ++ [j]) = autOf σ w ++ [σ w j] := by
  have h := autOf_foldl_fst σ w [] []
  simp only [List.nil_append] at h
  simp [autOf, List.foldl_append]
  rw [h]

/-- `autOf` preserves word lengths. -/
lemma autOf_length (σ : Word → Bool ≃ Bool) (w : Word) : (autOf σ w).length = w.length := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w j ih => rw [autOf_concat]; simp [ih]

/-- The recursion only appends: `autOf` is monotone for the prefix order. -/
lemma autOf_prefix (σ : Word → Bool ≃ Bool) {w w' : Word} (h : w <+: w') :
    autOf σ w <+: autOf σ w' := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc, autOf_concat]
      exact ih.trans (List.prefix_append _ _)

lemma autOf_injective (σ : Word → Bool ≃ Bool) : Function.Injective (autOf σ) := by
  intro w w' h
  induction w using List.reverseRecOn generalizing w' with
  | nil =>
      have hlen := congrArg List.length h
      rw [autOf_length, autOf_length] at hlen
      simpa using (List.eq_nil_of_length_eq_zero hlen.symm).symm
  | append_singleton t j ih =>
      rcases w'.eq_nil_or_concat with rfl | ⟨t', j', rfl⟩
      · have hlen := congrArg List.length h
        rw [autOf_length, autOf_length] at hlen
        simp at hlen
      · simp only [List.concat_eq_append] at h ⊢
        rw [autOf_concat, autOf_concat] at h
        have hlen : (autOf σ t).length = (autOf σ t').length := by
          have := congrArg List.length h
          simpa using this
        obtain ⟨h1, h2⟩ := List.append_inj h hlen
        have ht : t = t' := ih h1
        subst ht
        have hj : j = j' := (σ t).injective (by simpa using h2)
        rw [hj]

lemma autOf_surjective (σ : Word → Bool ≃ Bool) : Function.Surjective (autOf σ) := by
  intro v
  induction v using List.reverseRecOn with
  | nil => exact ⟨[], rfl⟩
  | append_singleton v c ih =>
      obtain ⟨w, rfl⟩ := ih
      exact ⟨w ++ [(σ w).symm c], by rw [autOf_concat, Equiv.apply_symm_apply]⟩

/-- `autOf` preserves the prefix order in both directions. -/
lemma autOf_prefix_iff (σ : Word → Bool ≃ Bool) {w w' : Word} :
    autOf σ w <+: autOf σ w' ↔ w <+: w' := by
  refine ⟨fun h => ?_, autOf_prefix σ⟩
  have htake : autOf σ (w'.take w.length) <+: autOf σ w' :=
    autOf_prefix σ (List.take_prefix _ _)
  have hlen : (autOf σ (w'.take w.length)).length = (autOf σ w).length := by
    have hle := h.length_le
    rw [autOf_length, autOf_length] at hle
    rw [autOf_length, autOf_length, List.length_take]
    omega
  have hw : w'.take w.length = w := autOf_injective σ (prefix_eq_of_length htake h hlen)
  exact hw ▸ List.take_prefix _ _

/-- `autOf` maps the two children of a word to the two children of its image:
first divergences are preserved. -/
lemma autOf_diverge (σ : Word → Bool ≃ Bool) {p w w' : Word} {a b : Bool} (hab : a ≠ b)
    (ha : p ++ [a] <+: w) (hb : p ++ [b] <+: w') :
    σ p a ≠ σ p b ∧ autOf σ p ++ [σ p a] <+: autOf σ w
      ∧ autOf σ p ++ [σ p b] <+: autOf σ w' := by
  refine ⟨fun h => hab ((σ p).injective h), ?_, ?_⟩
  · rw [← autOf_concat]
    exact autOf_prefix σ ha
  · rw [← autOf_concat]
    exact autOf_prefix σ hb

/-! ### The vertex map between the associated trees -/

/-- The addresses of corresponding chain starts for a labelling and its relabelling
along `autOf σ` have equal lengths. -/
lemma iotaL_autOf_length (σ : Word → Bool ≃ Bool) {lam lam' : Word → ℕ}
    (hcomp : ∀ w, lam' (autOf σ w) = lam w) (w : Word) :
    (iotaL lam' (autOf σ w)).length = (iotaL lam w).length := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w j ih =>
      rw [autOf_concat, iotaL_concat, iotaL_concat]
      simp only [List.length_append, List.length_replicate, List.length_singleton]
      rw [hcomp, ih]

open Classical in
/-- The vertex map of the tex proof: the normal form over `w` at level `l` is
sent to the normal form over `autOf σ w` at level `l`; junk value off the
associated tree. -/
noncomputable def relabelMap (σ : Word → Bool ≃ Bool) (lam lam' : Word → ℕ) (x : Word) : Word :=
  if h : InAssoc lam x then
    iotaL lam' (autOf σ (Exists.choose h))
      ++ List.replicate (Exists.choose (Exists.choose_spec h)) false
  else x

/-- `relabelMap` on an explicit normal form. -/
lemma relabelMap_apply (σ : Word → Bool ≃ Bool) {lam : Word → ℕ} (lam' : Word → ℕ)
    (hlam : ∀ u, 1 ≤ lam u) {w : Word} {l : ℕ} (hl : l ≤ lam w - 1) :
    relabelMap σ lam lam' (iotaL lam w ++ List.replicate l false)
      = iotaL lam' (autOf σ w) ++ List.replicate l false := by
  have hx : InAssoc lam (iotaL lam w ++ List.replicate l false) := ⟨w, l, hl, rfl⟩
  simp only [relabelMap, dif_pos hx]
  obtain ⟨hl', heq⟩ := Exists.choose_spec (Exists.choose_spec hx)
  obtain ⟨hw, hll⟩ := assoc_rep_unique lam hlam hl' hl heq.symm
  exact congrArg₂ (· ++ ·) (by rw [hw]) (by rw [hll])

/-! ### `thm:isometry` -/

/-- `thm:isometry`: relabelling along an automorphism of the index tree gives
an isometric associated tree. The relabelled labelling is written as
`lam = lam' ∘ autOf σ`, the tex's `λ'(w) = λ(π⁻¹ w)` with `π = autOf σ`. -/
theorem isometry_of_relabel (σ : Word → Bool ≃ Bool) {lam lam' : Word → ℕ}
    (hlam : ∀ w, 1 ≤ lam w) (_hlam' : ∀ w, 1 ≤ lam' w)
    (hcomp : ∀ w, lam' (autOf σ w) = lam w) :
    ∃ f : Word → Word,
      (∀ x, InAssoc lam x → InAssoc lam' (f x)) ∧
      (∀ y, InAssoc lam' y → ∃ x, InAssoc lam x ∧ f x = y) ∧
      (∀ x y, InAssoc lam x → InAssoc lam y → treeDist (f x) (f y) = treeDist x y) := by
  refine ⟨relabelMap σ lam lam', ?_, ?_, ?_⟩
  · -- the associated tree of `lam` lands in the associated tree of `lam'`
    rintro x ⟨w, l, hl, rfl⟩
    rw [relabelMap_apply σ lam' hlam hl]
    exact ⟨autOf σ w, l, by rw [hcomp]; exact hl, rfl⟩
  · -- and onto: pull back the word of a normal form through `autOf`
    rintro y ⟨u, l, hl, rfl⟩
    obtain ⟨w, rfl⟩ := autOf_surjective σ u
    rw [hcomp] at hl
    exact ⟨iotaL lam w ++ List.replicate l false, ⟨w, l, hl, rfl⟩,
      relabelMap_apply σ lam' hlam hl⟩
  · -- distances, by the relative position of the two words
    rintro x y ⟨w, l, hl, rfl⟩ ⟨w', l', hl', rfl⟩
    rw [relabelMap_apply σ lam' hlam hl, relabelMap_apply σ lam' hlam hl']
    by_cases hww : w = w'
    · -- same word: both wedges sit on the common chain
      subst hww
      simp only [treeDist, assoc_wedge_same, List.length_append, List.length_replicate,
        iotaL_autOf_length σ hcomp]
    · by_cases hp : w <+: w'
      · -- strict prefix: both vertices are comparable, distances are length gaps
        have hxy := assoc_prefix lam hp hww hl l'
        have hfl : l ≤ lam' (autOf σ w) - 1 := by rw [hcomp]; exact hl
        have hfne : autOf σ w ≠ autOf σ w' := fun h => hww (autOf_injective σ h)
        have hfxy := assoc_prefix lam' (autOf_prefix σ hp) hfne hfl l'
        rw [treeDist_of_prefix hxy, treeDist_of_prefix hfxy]
        simp only [List.length_append, List.length_replicate, iotaL_autOf_length σ hcomp]
      · by_cases hp' : w' <+: w
        · -- the mirrored prefix case
          have hww' : w' ≠ w := fun h => hww h.symm
          have hxy := assoc_prefix lam hp' hww' hl' l
          have hfl' : l' ≤ lam' (autOf σ w') - 1 := by rw [hcomp]; exact hl'
          have hfne : autOf σ w' ≠ autOf σ w := fun h => hww' (autOf_injective σ h)
          have hfxy := assoc_prefix lam' (autOf_prefix σ hp') hfne hfl' l
          rw [treeDist_comm, treeDist_of_prefix hfxy,
            treeDist_comm (iotaL lam w ++ List.replicate l false), treeDist_of_prefix hxy]
          simp only [List.length_append, List.length_replicate, iotaL_autOf_length σ hcomp]
        · -- divergent words: both wedges sit at the branch point over `p`
          obtain ⟨p, a, b, hab, hpa, hpb⟩ := exists_diverge hp hp'
          obtain ⟨hfab, hfa, hfb⟩ := autOf_diverge σ hab hpa hpb
          rw [treeDist, treeDist, assoc_wedge_diverge lam hab hpa hpb,
            assoc_wedge_diverge lam' hfab hfa hfb]
          simp only [List.length_append, List.length_replicate,
            iotaL_autOf_length σ hcomp, hcomp]

end ChainClasses
