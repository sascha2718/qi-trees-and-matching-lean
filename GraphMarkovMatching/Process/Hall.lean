/-
The screened `2×2` Hall classification (`arbitrary_offspring_matching.tex`
§3, Lemma `thm:hall`) and the resolved normalization it feeds:

* `straight_le_rE_square` / `crossed_le_rE_square`: either pairing
  minorizes the square good degree (`eq:club` before selection);
* `rE_square_eq_zero_iff`: the pair degree vanishes exactly when both
  pairings are blocked;
* `rE_square_eq_zero_iff_hall`: the same in Hall form: a zero row (one
  source child dead against both targets) or a zero column (both source
  children dead against one target);
* `phiE_square_resolved_le` / `phiE_square_resolved_le_crossed`: on a
  resolved cell the potential summand is bounded by the product of the
  two inverse degrees of a surviving matching — the source coordinates
  separate, which is what routes resolved rows into `B`-entries and one
  screen times an inverse moment into `N`-entries.
-/
import GraphMarkovMatching.FourLaw.Square
import GraphMarkovMatching.Potential.ZeroInterface
import GraphMarkovMatching.Process.Screens

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {X : Type}

/-- The straight pairing minorizes the square good degree. -/
lemma straight_le_rE_square (ρc ρd : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    rE ρc R x₀ * rE ρd R x₁
      ≤ rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) := by
  rw [rE_eq_tsum_mul ρc R x₀, rE_eq_tsum_mul ρd R x₁,
    rE_eq_tsum_mul (prodPMF ρc ρd) (SquareRel R) (x₀, x₁),
    ← tsum_prod_split (fun y => ρc y * goodInd R x₀ y)
      (fun y => ρd y * goodInd R x₁ y)]
  refine ENNReal.tsum_le_tsum fun p => ?_
  by_cases h0 : R x₀ p.1 <;> by_cases h1 : R x₁ p.2
  · have hsq : SquareRel R (x₀, x₁) p := Or.inl ⟨h0, h1⟩
    simp [goodInd, h0, h1, hsq, prodPMF_apply]
  · simp [goodInd, h1]
  · simp [goodInd, h0]
  · simp [goodInd, h0]

/-- The crossed pairing minorizes the square good degree. -/
lemma crossed_le_rE_square (ρc ρd : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    rE ρc R x₁ * rE ρd R x₀
      ≤ rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) := by
  rw [rE_eq_tsum_mul ρc R x₁, rE_eq_tsum_mul ρd R x₀,
    rE_eq_tsum_mul (prodPMF ρc ρd) (SquareRel R) (x₀, x₁),
    ← tsum_prod_split (fun y => ρc y * goodInd R x₁ y)
      (fun y => ρd y * goodInd R x₀ y)]
  refine ENNReal.tsum_le_tsum fun p => ?_
  by_cases h0 : R x₀ p.2 <;> by_cases h1 : R x₁ p.1
  · have hsq : SquareRel R (x₀, x₁) p := Or.inr ⟨h0, h1⟩
    simp [goodInd, h0, h1, hsq, prodPMF_apply]
  · simp [goodInd, h1]
  · simp [goodInd, h0]
  · simp [goodInd, h0]

/-- **The Hall zero dichotomy, product form** (`thm:hall`): the square
good degree vanishes exactly when both pairings are blocked. -/
lemma rE_square_eq_zero_iff (ρc ρd : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) = 0 ↔
      rE ρc R x₀ * rE ρd R x₁ = 0 ∧ rE ρc R x₁ * rE ρd R x₀ = 0 := by
  constructor
  · intro hR
    exact ⟨le_antisymm ((straight_le_rE_square ρc ρd R x₀ x₁).trans hR.le)
        zero_le,
      le_antisymm ((crossed_le_rE_square ρc ρd R x₀ x₁).trans hR.le) zero_le⟩
  · rintro ⟨hs, hc⟩
    have hle : rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁)
        ≤ rE ρc R x₀ * rE ρd R x₁ + rE ρd R x₀ * rE ρc R x₁ := by
      calc rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁)
          ≤ rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁)
            + aOverlap ρc R x₀ x₁ * aOverlap ρd R x₀ x₁ := le_self_add
        _ = _ := rE_square_two ρc ρd R x₀ x₁
    rw [hs, zero_add, mul_comm (rE ρd R x₀) (rE ρc R x₁), hc] at hle
    exact le_antisymm hle zero_le

/-- **The Hall classification** (`thm:hall`): the pair degree vanishes
exactly on a zero row (one source child dead against both targets) or a
zero column (both source children dead against one target). -/
lemma rE_square_eq_zero_iff_hall (ρc ρd : PMF X) (R : X → X → Prop)
    (x₀ x₁ : X) :
    rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) = 0 ↔
      ((rE ρc R x₀ = 0 ∧ rE ρd R x₀ = 0)
        ∨ (rE ρc R x₁ = 0 ∧ rE ρd R x₁ = 0))
      ∨ ((rE ρc R x₀ = 0 ∧ rE ρc R x₁ = 0)
        ∨ (rE ρd R x₀ = 0 ∧ rE ρd R x₁ = 0)) := by
  rw [rE_square_eq_zero_iff, mul_eq_zero, mul_eq_zero]
  tauto

/-- **The resolved normalization, straight form** (`eq:club` plus
separation): when the straight matching survives, the square potential
summand is bounded by the product of its two inverse degrees. -/
lemma phiE_square_resolved_le {α : ℝ} (hα : 0 < α) (ρc ρd : PMF X)
    (R : X → X → Prop) (x₀ x₁ : X)
    (h0 : rE ρc R x₀ ≠ 0) (h1 : rE ρd R x₁ ≠ 0) :
    phiE α (q (prodPMF ρc ρd) (SquareRel R) (x₀, x₁))
      ≤ (rE ρc R x₀) ^ (-α) * (rE ρd R x₁) ^ (-α) := by
  rw [phiE_eq_qE_mul_rpow α (SquareRel R) (prodPMF ρc ρd) hα (x₀, x₁)]
  calc qE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁)
        * rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) ^ (-α)
      ≤ 1 * rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) ^ (-α) :=
        mul_le_mul_left qE_le_one _
    _ = rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) ^ (-α) := one_mul _
    _ ≤ (rE ρc R x₀ * rE ρd R x₁) ^ (-α) :=
        rpow_neg_antitone (le_of_lt hα)
          (straight_le_rE_square ρc ρd R x₀ x₁)
    _ = (rE ρc R x₀) ^ (-α) * (rE ρd R x₁) ^ (-α) :=
        ENNReal.mul_rpow_of_ne_zero h0 h1 (-α)

/-- The resolved normalization, crossed form. -/
lemma phiE_square_resolved_le_crossed {α : ℝ} (hα : 0 < α) (ρc ρd : PMF X)
    (R : X → X → Prop) (x₀ x₁ : X)
    (h0 : rE ρc R x₁ ≠ 0) (h1 : rE ρd R x₀ ≠ 0) :
    phiE α (q (prodPMF ρc ρd) (SquareRel R) (x₀, x₁))
      ≤ (rE ρc R x₁) ^ (-α) * (rE ρd R x₀) ^ (-α) := by
  rw [phiE_eq_qE_mul_rpow α (SquareRel R) (prodPMF ρc ρd) hα (x₀, x₁)]
  calc qE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁)
        * rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) ^ (-α)
      ≤ 1 * rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) ^ (-α) :=
        mul_le_mul_left qE_le_one _
    _ = rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) ^ (-α) := one_mul _
    _ ≤ (rE ρc R x₁ * rE ρd R x₀) ^ (-α) :=
        rpow_neg_antitone (le_of_lt hα)
          (crossed_le_rE_square ρc ρd R x₀ x₁)
    _ = (rE ρc R x₁) ^ (-α) * (rE ρd R x₀) ^ (-α) :=
        ENNReal.mul_rpow_of_ne_zero h0 h1 (-α)

end GraphMarkovMatching
