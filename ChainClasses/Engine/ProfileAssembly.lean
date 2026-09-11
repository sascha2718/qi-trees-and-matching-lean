import ChainClasses.Engine.ProfileGeometry

/-! Gluing compatible labelled pieces after an arbitrary bounded-profile encoding. -/

namespace ChainClasses.Profile

open GraphMarkovMatching GraphMarkovMatching.Support
open BranchingProcess (sample)
open scoped ENNReal Classical

variable {N N' : ℕ}

/-- Every encoded piece retains its prescribed state; inserted singleton pieces carry
the distinguished state. -/
lemma bFamily_state {L : ℕ} (C : Family) {c : GWord N → ℕ}
    (hs : SkelBounded L (gArityAt c)) (A : GShape → ℕ → Prop) (v0 : ℕ)
    (h0 : A gOne v0) {lab : GWord N → ℕ}
    (hlab : ∀ u, u ∈ sample (gArityAt c) → A (gShapeAt c u) (lab u)) (w : Word) :
    A ((profileEnc C L (gArityAt c) (arityBounded_gArityAt hs)).bFamily
      (gShapeAt c) (bnat w)) (encField C lab (gArityAt c) v0 w).1 := by
  let E := profileEnc C L (gArityAt c) (arityBounded_gArityAt hs)
  by_cases h : ∃ u, u ∈ sample (gArityAt c) ∧ w = profileEncWord C L (gArityAt c) u
  · obtain ⟨u, hu, rfl⟩ := h
    have hb : E.bFamily (gShapeAt c) (bnat (E.enc u)) = gShapeAt c u :=
      CascadeEnc.bFamily_enc (E := E) hu
    change A (E.bFamily (gShapeAt c) (bnat (E.enc u))) _
    rw [hb, encField_enc C lab (arityBounded_gArityAt hs) v0 hu]
    exact hlab u hu
  · have hb : E.bFamily (gShapeAt c) (bnat w) = gOne := by
      refine CascadeEnc.bFamily_of_not_isImage ?_
      rintro ⟨u, hu, hw⟩
      exact h ⟨u, hu, bnat_injective hw⟩
    change A (E.bFamily (gShapeAt c) (bnat w)) _
    rw [hb, encField_of_not_image C lab (arityBounded_gArityAt hs) hs
      (gArityAt_le_alphabet c) v0 h]
    exact h0

/-- A state-only matching gives a quasi-isometry whenever compatible states prescribe
uniform marked comparisons of the corresponding pieces, including singleton pieces. -/
theorem sample_qi_of_encoded_match {L L' : ℕ} (C C' : Family)
    {c : GWord N → ℕ} {c' : GWord N' → ℕ} (hc : IsGHairySample c) (hc' : IsGHairySample c')
    (hs : SkelBounded L (gArityAt c)) (hs' : SkelBounded L' (gArityAt c'))
    (hL : 1 ≤ L) (hL' : 1 ≤ L') {K : ℝ} (hK : 1 ≤ K)
    (A A' : GShape → ℕ → Prop) (R : ℕ → ℕ → Prop) (v0 : ℕ)
    (h0 : A gOne v0) (h0' : A' gOne v0)
    (hcomp : ∀ τ τ' x y, A τ x → A' τ' y → R x y →
      MarkedQI K (gShapeSpace τ) (gShapeSpace τ'))
    {lab : GWord N → ℕ} {lab' : GWord N' → ℕ}
    (hlab : ∀ u, u ∈ sample (gArityAt c) → A (gShapeAt c u) (lab u))
    (hlab' : ∀ u, u ∈ sample (gArityAt c') → A' (gShapeAt c' u) (lab' u))
    (hm : InfMatch R (fun n => encodedStates C lab (gArityAt c) v0 n)
      (fun n => encodedStates C' lab' (gArityAt c') v0 n)) :
    ∃ F : {v : GWord N // v ∈ sample c} → {v : GWord N' // v ∈ sample c'},
      BranchingProcess.IsQIWith ⌈216 * L * L' ^ 2 * K ^ 2⌉₊
        (wordGraphN (· ∈ sample c)) (wordGraphN (· ∈ sample c')) F := by
  obtain ⟨π, hπ⟩ := exists_portrait_of_infMatchK R hm
  let E := profileEnc C L (gArityAt c) (arityBounded_gArityAt hs)
  let E' := profileEnc C' L' (gArityAt c') (arityBounded_gArityAt hs')
  refine sample_qi_of_bShape_matching hc hc' E E' rfl rfl hL hL' hK π (fun w => ?_) (fun w => ?_)
  · exact ⟨fun _ => profileEnc_inClosure C' _ hs' (gArityAt_le_alphabet c') _,
      fun _ => profileEnc_inClosure C _ hs (gArityAt_le_alphabet c) _⟩
  · have hrel := hπ w
    rw [labelAt_encodedStates _ _ _ _ le_rfl,
      labelAt_encodedStates _ _ _ _ (by rw [autOf_length])] at hrel
    exact hcomp _ _ _ _ (bFamily_state C hs A v0 h0 hlab w)
      (bFamily_state C' hs' A' v0 h0' hlab' (autOf π w)) hrel

end ChainClasses.Profile
