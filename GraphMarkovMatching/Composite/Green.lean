/-
The denominator-free Green estimate for an abstract weighted screen ledger.

This file is deliberately analytic and grammar-free.  It takes a finite
one-step ledger whose rows have been assembled as `N + zeta M` for arbitrary
matrices `N M : iota -> iota -> ENNReal` on a finite index, and removes the
last resolvent denominator.  If the common operator is nilpotent in `r` steps
and

    zeta * (2 C)^r <= 1/2,

then the full Green factor is at most

    2 * sum_{j < r} (2 C)^j.

The theorem `graftWeightedLedger_estimate` then gives a height-uniform bound
for both the ordinary coordinate and every tagged debt coordinate; it is the
invariant box consumed by the composite two-law ledger.
-/
import GraphMarkovMatching.Composite.RareMatrix

namespace GraphMarkovMatching

open scoped ENNReal Classical

set_option maxRecDepth 100000
variable {iota : Type} [Fintype iota]

/-- The finite remainder in the block-geometric Green estimate. -/
noncomputable def graftGreenRemainder (C : ℝ≥0∞) (r : ℕ) : ℝ≥0∞ :=
  ∑ j : Fin r, (2 * C) ^ (j : ℕ)

/-- The denominator-free Green multiplier obtained when the rare block
contraction is at most `1/2`. -/
noncomputable def graftGreenMultiplier (C : ℝ≥0∞) (r : ℕ) : ℝ≥0∞ :=
  2 * graftGreenRemainder C r

/-- At rare block mass at most one half, the geometric denominator is at
most two. -/
lemma graft_geometric_denominator_le_two {rho : ℝ≥0∞} (hrho : rho ≤ 2⁻¹) :
    (1 - rho)⁻¹ ≤ 2 := by
  rw [show (2 : ℝ≥0∞) = ((2 : ℝ≥0∞)⁻¹)⁻¹ by norm_num,
    ENNReal.inv_le_inv]
  apply ENNReal.le_sub_of_add_le_right
    (ne_top_of_le_ne_top (by norm_num : (2⁻¹ : ℝ≥0∞) ≠ ⊤) hrho)
  calc
    2⁻¹ + rho ≤ 2⁻¹ + 2⁻¹ := add_le_add le_rfl hrho
    _ = 1 := ENNReal.inv_two_add_inv_two

/-- **The tagged weighted-ledger estimate.**  Once the literal tagged
ordinary/screen rows have the displayed `N + zeta M` form, nilpotence of the
common block and the single quantitative condition
`zeta * (2*C)^r <= 1/2` give the explicit invariant

    Xi = 2 * (sum_{j<r} (2*C)^j) * u.

This is the complete Hall/Green estimate: no inverse denominator and no
unweighted `2*M <= M` premise remains. -/
theorem graftWeightedLedger_estimate
    (N M : iota → iota → ℝ≥0∞) (zeta C : ℝ≥0∞) (r : ℕ) (hr : 0 < r)
    (hzeta : zeta ≤ 1)
    (hNrow : ∀ i, ∑ j, N i j ≤ C)
    (hMrow : ∀ i, ∑ j, M i j ≤ C)
    (hnil : (mulVec N)^[r] (fun _ => 1) = fun _ => 0)
    (hhalf : zeta * (2 * C) ^ r ≤ 2⁻¹)
    (Kc eta u : ℝ≥0∞)
    (Psi : ℕ → ℝ≥0∞) (E : ℕ → iota → ℝ≥0∞)
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (hf : ∀ a a' b b', a ≤ a' → b ≤ b' → f a b ≤ f a' b')
    (hg : ∀ a a' b b', a ≤ a' → b ≤ b' → g a b ≤ g a' b')
    (hPsi0 : Psi 0 ≤ Kc * eta)
    (hE0 : ∀ i, E 0 i ≤ u)
    (hPsistep : ∀ h, Psi (h + 1) ≤ f (Psi h) (⨆ i, E h i))
    (hEstep : ∀ h i,
      E (h + 1) i ≤ g (Psi h) (⨆ j, E h j) +
        mulVecInf (rareMatrix N M zeta) (E h) i)
    (hu : g (Kc * eta) (graftGreenMultiplier C r * u) ≤ u)
    (hclose : f (Kc * eta) (graftGreenMultiplier C r * u) ≤ Kc * eta) :
    ∀ h, Psi h ≤ Kc * eta ∧
      ∀ i, E h i ≤ graftGreenMultiplier C r * u := by
  refine screened_uniform_bound_rareMatrix_with_debt
    N M zeta C r hr hzeta hNrow hMrow hnil Kc eta u
      (graftGreenMultiplier C r * u) ?_
      Psi E f g hf hg hPsi0 hE0 hPsistep hEstep hu hclose
  rw [graftGreenMultiplier, graftGreenRemainder]
  calc
    (1 - zeta * (2 * C) ^ r)⁻¹ *
          (∑ j : Fin r, (2 * C) ^ (j : ℕ)) * u
        ≤ 2 * (∑ j : Fin r, (2 * C) ^ (j : ℕ)) * u := by
          gcongr
          exact graft_geometric_denominator_le_two hhalf
    _ = (2 * graftGreenRemainder C r) * u := by
          rw [graftGreenRemainder]

end GraphMarkovMatching
