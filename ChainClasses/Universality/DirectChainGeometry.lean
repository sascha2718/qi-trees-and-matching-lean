import ChainClasses.Engine.ProfileAssembly
import ChainClasses.Universality.ChainPieces
import ChainClasses.Regime.DirectChainLabels

/-! The original chain pieces are bare necks. Compatible quantised lengths give marked
comparisons of size proportional to the square of the scale, also at inserted vertices. -/

namespace ChainClasses

open GraphMarkovMatching GraphMarkovMatching.Support
open BranchingProcess (sample)
open scoped ENNReal Classical

variable {N N' : ℕ}

/-- The direct geometric bridge for arbitrary finite binary profiles and the original
reduced necks; its local comparison constant is `2 chainRatio D² + 1`. -/
theorem sample_qi_of_direct_chain_match [NeZero N] [NeZero N'] {L L' : ℕ}
    (C C' : Profile.Family) {c : GWord N → ℕ} {c' : GWord N' → ℕ}
    (hc : IsGBushySample c) (hc' : IsGBushySample c')
    (h1 : ∀ v, 1 ≤ c v) (h1' : ∀ v, 1 ≤ c' v)
    (hs : Profile.SkelBounded L (gArityAt c)) (hs' : Profile.SkelBounded L' (gArityAt c'))
    (hL : 1 ≤ L) (hL' : 1 ≤ L') {a b : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    {D : ℕ} (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1))
    (uField : GWord N' → ℝ)
    (hm : InfMatch (GraphMatching.compat GraphMatching.pathGraph)
      (fun n => Profile.encodedStates C (directChainLab D c) (gArityAt c) 0 n)
      (fun n => Profile.encodedStates C' (directCrossLab a b D (c', uField)) (gArityAt c') 0 n)) :
    ∃ F : {v : GWord N // v ∈ sample c} → {v : GWord N' // v ∈ sample c'},
      BranchingProcess.IsQIWith ⌈216 * L * L' ^ 2 * (2 * chainRatio a b * (D : ℝ) ^ 2 + 1) ^ 2⌉₊
        (wordGraphN (· ∈ sample c)) (wordGraphN (· ∈ sample c')) F := by
  let A : GShape → ℕ → Prop := fun τ x => ∃ n, τ = flatG n ∧ x = levelMap D (n + 1)
  let A' : GShape → ℕ → Prop := fun τ x => ∃ n u, τ = flatG n ∧ x = ellQ a b D (n + 1) u
  have hR : 1 ≤ chainRatio a b * (D : ℝ) ^ 2 := by
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
    have hDR := one_le_pow₀ (n := 2) hD1
    nlinarith [one_le_chainRatio a b]
  have hK : 1 ≤ 2 * chainRatio a b * (D : ℝ) ^ 2 + 1 := by nlinarith
  refine Profile.sample_qi_of_encoded_match C C' hc hc' hs hs' hL hL' hK A A'
    (GraphMatching.compat GraphMatching.pathGraph) 0 ?_ ?_ ?_ ?_ ?_ hm
  · refine ⟨0, rfl, ?_⟩
    have := (level_eq_iff hD (by omega : 1 ≤ 0 + 1)).mpr (by simp; omega : D ^ 0 ≤ 0 + 1 ∧ 0 + 1 < D ^ (0 + 1))
    exact this.symm
  · exact ⟨0, 0, rfl, (ellQ_one ha ha1 hb hb1 hD hgD 0).symm⟩
  · rintro τ τ' x y ⟨n, rfl, rfl⟩ ⟨n', u, rfl, rfl⟩ hrel
    obtain ⟨hleft, hright⟩ := neck_ratio_of_compat ha ha1 hb hb1 hD hgD hrel
    simpa only [mul_assoc] using flatG_markedQI hR hleft hright
  · intro u hu
    exact ⟨neckAt c u, gShapeAt_eq_flatG hc h1 hu, rfl⟩
  · intro u hu
    exact ⟨neckAt c' u, uField u, gShapeAt_eq_flatG hc' h1' hu, rfl⟩

end ChainClasses
