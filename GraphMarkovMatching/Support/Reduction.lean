/-
The mean bad degree is below the potential: `meanBad_le_Phi` converts a
potential bound into a failure probability bound.
-/
import GraphMarkovMatching.Support.Contraction

namespace GraphMarkovMatching.Support

open scoped ENNReal Classical

/-! ### The mean bad degree is below the potential -/

variable {X : Type*}

/-- `𝔼[q] ≤ Φ_α`: the failure probability (mean bad degree) is at most the
potential, since `q ≤ φ_α(q)` on the support. Needs `α ≥ 0`. -/
lemma meanBad_le_Phi {α : ℝ} (hα : 0 ≤ α) {μ : PMF X} {R : X → X → Prop}
    (hrefl : ∀ x, R x x) :
    ∑' x, μ x * qE μ R x ≤ Phi α μ R := by
  rw [Phi]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : μ x = 0
  · simp [hx]
  · have hq : μ x * qE μ R x = μ x * ENNReal.ofReal (q μ R x) := by
      rw [q, ENNReal.ofReal_toReal qE_ne_top]
    rw [hq]
    exact mul_q_le_summand hα (hrefl x) hx

end GraphMarkovMatching.Support
