import ChainClasses.Engine.SkeletonPatterns
import ChainClasses.Engine.ProfileMatching
import ChainClasses.Chain.Eta

/-! Quantised geometric labels for a fixed pair of original arity laws. All profile
data and the core probabilities are fixed before the geometric scale is chosen. -/

namespace ChainClasses

open GraphMarkovMatching.Stopped
open scoped ENNReal Classical

/-- Any fixed common-profile presentation admits arbitrarily reliable matching at
large geometric scales. The scale may also satisfy any prescribed finite lower bound. -/
theorem quantised_profile_scale (P : Presentation) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {δ : ℝ} (hδ : 0 < δ) (M : ℕ) :
    ∃ (D : ℕ) (hD : 5 ≤ D), M ≤ D ∧
      ∀ n, (P.toModel (GraphMatching.compat GraphMatching.pathGraph) 0
        (qPMF ha.le ha1 (by omega : 2 ≤ D))).failProb (P.freshL false) (P.freshL true) n
          ≤ ENNReal.ofReal δ := by
  obtain ⟨c0, hc0, hc1, hfloor⟩ := P.exists_floor
  obtain ⟨K, ε, hε, hmatch⟩ := P.presentation_matching_eta_exists paramsFiveHalf hc0 hc1 hfloor
    (p0 := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hK : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have he : 0 < min ε (δ / max K 1) := lt_min hε (div_pos hδ hK)
  obtain ⟨D, hD, hM, h1, h2, h3, -, hB⟩ := exists_scale ha ha1 he M
  have hB' : 16 * qBound a D ≤ min ε (δ / max K 1) := by
    have := qBound_nonneg a D
    linarith
  refine ⟨D, hD, hM, fun n => ?_⟩
  let μ := qPMF ha.le ha1 (by omega : 2 ≤ D)
  let R := GraphMatching.compat GraphMatching.pathGraph
  have hμ : ENNReal.ofReal (1 / 2 : ℝ) ≤ μ 0 := by
    rw [qPMF_apply, qF_zero]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have heta : (P.toModel R 0 μ).eta paramsFiveHalf.α = GraphMatching.etaG μ GraphMatching.pathGraph := by
    rw [paramsFiveHalf_α]
    exact etaG_compat_eq μ GraphMatching.pathGraph
  have hetaB : GraphMatching.etaG μ GraphMatching.pathGraph ≤ ENNReal.ofReal (16 * qBound a D) :=
    quantised_eta_le ha ha1 hD h1 h2 h3
  have hbound := hmatch R 0 μ
    ⟨GraphMatching.compat_refl _, GraphMatching.compat_symm _⟩ hμ
    (by rw [heta]; exact hetaB.trans (ENNReal.ofReal_le_ofReal (hB'.trans (min_le_left _ _))))
    false true n
  rw [heta] at hbound
  have hsmall : max K 1 * (16 * qBound a D) ≤ δ := by
    have := (le_div_iff₀ hK).mp (hB'.trans (min_le_right _ _))
    nlinarith
  calc _ ≤ ENNReal.ofReal K * GraphMatching.etaG μ GraphMatching.pathGraph := hbound
    _ ≤ ENNReal.ofReal (max K 1) * ENNReal.ofReal (16 * qBound a D) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hetaB
    _ = ENNReal.ofReal (max K 1 * (16 * qBound a D)) := (ENNReal.ofReal_mul hK.le).symm
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hsmall

end ChainClasses
