/-
The directed product lemma:

    Φ_α(μ₁⊗μ₂ → ν₁⊗ν₂; R₁ ⊗ R₂) ≤ Φ₁ + Φ₂ + 2α Φ₁ Φ₂,

with the directed potentials `Φᵢ = Φ_α(μᵢ → νᵢ; Rᵢ)`. This is the one-sided
step of the Markov recursion: when only one pairing of patterns is
compatible, the matching relation is the plain tensor product and the
potential grows by at most the product-lemma amount.

In the safe `phiE` convention no reflexivity or support hypotheses are
needed: a degree-one point makes the corresponding potential `⊤` and the
bound is trivial there. The pointwise heart is `phiE_split`, which is the
mixture split at `e := q₁`, `q̃ := q₂`.
-/
import GraphMarkovMatching.FourLaw.Base

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X₁ X₂ : Type u}

/-- Averaging a summand shape `A(x₁) + B(x₂) + c·A(x₁)B(x₂)` against a
product law splits into the marginal averages. -/
lemma tsum_prod_shape (μ₁ : PMF X₁) (μ₂ : PMF X₂)
    (A : X₁ → ℝ≥0∞) (B : X₂ → ℝ≥0∞) (c : ℝ≥0∞) :
    ∑' p : X₁ × X₂, prodPMF μ₁ μ₂ p * (A p.1 + B p.2 + c * (A p.1 * B p.2))
      = (∑' x, μ₁ x * A x) + (∑' x, μ₂ x * B x)
        + c * ((∑' x, μ₁ x * A x) * (∑' x, μ₂ x * B x)) := by
  have hsplit : ∀ p : X₁ × X₂,
      prodPMF μ₁ μ₂ p * (A p.1 + B p.2 + c * (A p.1 * B p.2))
        = (μ₁ p.1 * A p.1) * μ₂ p.2 + μ₁ p.1 * (μ₂ p.2 * B p.2)
          + c * ((μ₁ p.1 * A p.1) * (μ₂ p.2 * B p.2)) := by
    intro p
    rw [prodPMF_apply]
    ring
  rw [tsum_congr hsplit, ENNReal.tsum_add, ENNReal.tsum_add]
  congr 1
  · congr 1
    · rw [tsum_prod_split (fun x => μ₁ x * A x) (fun x => μ₂ x), PMF.tsum_coe, mul_one]
    · rw [tsum_prod_split (fun x => μ₁ x) (fun x => μ₂ x * B x), PMF.tsum_coe, one_mul]
  · rw [show (∑' p : X₁ × X₂, c * ((μ₁ p.1 * A p.1) * (μ₂ p.2 * B p.2)))
        = c * ∑' p : X₁ × X₂, (μ₁ p.1 * A p.1) * (μ₂ p.2 * B p.2) from
      ENNReal.tsum_mul_left]
    rw [tsum_prod_split (fun x => μ₁ x * A x) (fun x => μ₂ x * B x)]

/-- **The directed product lemma**: for independent coordinates and the
tensor relation,

    `Φ(μ₁⊗μ₂ → ν₁⊗ν₂) ≤ Φ₁ + Φ₂ + 2α Φ₁Φ₂`. -/
theorem PhiD_prodPMF_le {α : ℝ} (hα : 1 ≤ α)
    (μ₁ ν₁ : PMF X₁) (μ₂ ν₂ : PMF X₂)
    (R₁ : X₁ → X₁ → Prop) (R₂ : X₂ → X₂ → Prop) :
    PhiD α (prodPMF μ₁ μ₂) (prodPMF ν₁ ν₂) (ProdRel R₁ R₂)
      ≤ PhiD α μ₁ ν₁ R₁ + PhiD α μ₂ ν₂ R₂
        + ENNReal.ofReal (2 * α) * (PhiD α μ₁ ν₁ R₁ * PhiD α μ₂ ν₂ R₂) := by
  have hpoint : ∀ p : X₁ × X₂,
      phiE α (q (prodPMF ν₁ ν₂) (ProdRel R₁ R₂) p)
        ≤ phiE α (q ν₁ R₁ p.1) + phiE α (q ν₂ R₂ p.2)
          + ENNReal.ofReal (2 * α) * (phiE α (q ν₁ R₁ p.1) * phiE α (q ν₂ R₂ p.2)) := by
    intro p
    have hq : q (prodPMF ν₁ ν₂) (ProdRel R₁ R₂) p
        = 1 - (1 - q ν₁ R₁ p.1) * (1 - q ν₂ R₂ p.2) := by
      have h := q_prodPMF ν₁ ν₂ R₁ R₂ p
      exact h
    have he : q ν₁ R₁ p.1 + (1 - q ν₁ R₁ p.1) * q ν₂ R₂ p.2
        = 1 - (1 - q ν₁ R₁ p.1) * (1 - q ν₂ R₂ p.2) := by ring
    rw [hq, ← he]
    exact phiE_split hα q_nonneg q_le_one q_nonneg q_le_one
  calc PhiD α (prodPMF μ₁ μ₂) (prodPMF ν₁ ν₂) (ProdRel R₁ R₂)
      ≤ ∑' p : X₁ × X₂, prodPMF μ₁ μ₂ p
          * (phiE α (q ν₁ R₁ p.1) + phiE α (q ν₂ R₂ p.2)
            + ENNReal.ofReal (2 * α)
              * (phiE α (q ν₁ R₁ p.1) * phiE α (q ν₂ R₂ p.2))) := by
        rw [PhiD]
        exact ENNReal.tsum_le_tsum fun p => mul_le_mul_right (hpoint p) _
    _ = PhiD α μ₁ ν₁ R₁ + PhiD α μ₂ ν₂ R₂
          + ENNReal.ofReal (2 * α) * (PhiD α μ₁ ν₁ R₁ * PhiD α μ₂ ν₂ R₂) := by
        rw [tsum_prod_shape μ₁ μ₂ (fun x => phiE α (q ν₁ R₁ x))
          (fun x => phiE α (q ν₂ R₂ x)) (ENNReal.ofReal (2 * α))]
        rfl

end GraphMarkovMatching
