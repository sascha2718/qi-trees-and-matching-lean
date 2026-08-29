/-
The zero-label charge for the literal 11/13 grafts.

The offspring and graph-label draws are independent.  Consequently the
probability of the selected replacement cylinder is the product

  nu(root) * mu(v0) * nu(5).

If the one extra zero required by a replacement chart fails with mass
`delta0`, the resulting Hall term has source coefficient `delta0`, not the
exceptional offspring coefficient `zeta`.  The correct quantitative
hypothesis is therefore

  delta0 <= zeta * d * replacementMass ^ alpha.

It cancels the inverse replacement price and leaves the genuine rare factor
`zeta`.  The two theorems below are the exact 11/13 macro statements.
-/
import GraphMarkovMatching.Archive.VaryingGraftedHallClose

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

/-- Mass outside the distinguished zero label. -/
noncomputable def graftZeroDefect {V : Type} (mu : PMF V) (v0 : V) :
    ℝ≥0∞ := 1 - mu v0

/-- The smaller of the two literal replacement-cylinder probabilities. -/
noncomputable def elevenThirteenReplacementFloor {V : Type}
    (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V) : ℝ≥0∞ :=
  min (replacementMass (nuR 7) (mu v0) (nuR 5))
    (replacementMass (nuL 9) (mu v0) (nuL 5))

/-- The mass of graph labels different from the distinguished label is
exactly `1 - mu v0`.  This is an unconditional PMF identity. -/
lemma pmf_off_atom_mass {V : Type} (mu : PMF V) (v0 : V) :
    (∑' v, if v = v0 then 0 else (mu v : ℝ≥0∞)) =
      graftZeroDefect mu v0 := by
  have hsplit0 : (mu v0 : ℝ≥0∞) +
      (∑' v, if v = v0 then 0 else (mu v : ℝ≥0∞)) = 1 := by
    calc
      (mu v0 : ℝ≥0∞) +
          (∑' v, if v = v0 then 0 else (mu v : ℝ≥0∞)) =
        ∑' v, (mu v : ℝ≥0∞) :=
          (ENNReal.tsum_eq_add_tsum_ite v0).symm
      _ = 1 := mu.tsum_coe
  have hsplit :
      (∑' v, if v = v0 then 0 else (mu v : ℝ≥0∞)) +
        (mu v0 : ℝ≥0∞) = 1 := by
    simpa [add_comm] using hsplit0
  exact ENNReal.eq_sub_of_add_eq (PMF.apply_ne_top mu v0) hsplit

/-- Algebraic failed-label extraction.  If every row integrand away from
`v0` is at most `B`, its unconditional contribution is at most
`(1 - mu v0) * B`.  No offspring event appears in this statement and no
conditioning is performed. -/
lemma pmf_off_atom_weighted_le {V : Type} (mu : PMF V) (v0 : V)
    (H : V → ℝ≥0∞) (B : ℝ≥0∞)
    (hH : ∀ v, v ≠ v0 → H v ≤ B) :
    (∑' v, if v = v0 then 0 else (mu v : ℝ≥0∞) * H v) ≤
      graftZeroDefect mu v0 * B := by
  calc
    (∑' v, if v = v0 then 0 else (mu v : ℝ≥0∞) * H v) ≤
        ∑' v, (if v = v0 then 0 else (mu v : ℝ≥0∞)) * B := by
      refine ENNReal.tsum_le_tsum fun v => ?_
      by_cases hv : v = v0
      · simp [hv]
      · simp only [hv, if_false]
        exact mul_le_mul_right (hH v hv) _
    _ = (∑' v, if v = v0 then 0 else (mu v : ℝ≥0∞)) * B :=
      ENNReal.tsum_mul_right
    _ = graftZeroDefect mu v0 * B := by rw [pmf_off_atom_mass]

/-- A zero-label defect satisfying the cylinder affordability inequality
has inverse-cylinder load at most `zeta * d`. -/
lemma graftZeroDefect_rpow_price_le {V : Type} {alpha : ℝ}
    (mu : PMF V) (v0 : V) {p zeta d : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤)
    (hsmall : graftZeroDefect mu v0 ≤ zeta * d * p ^ alpha) :
    graftZeroDefect mu v0 * p ^ (-alpha) ≤ zeta * d := by
  apply rare_rpow_price_le hp0 hpT
  simpa [mul_assoc] using hsmall

/-- Simultaneous scalar cancellation for the two 11/13 replacement
cylinders. -/
theorem elevenThirteen_zero_defect_price_le {V : Type} {alpha : ℝ}
    (halpha : 0 ≤ alpha) (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    {zeta d : ℝ≥0∞}
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (hsmall : graftZeroDefect mu v0 ≤
      zeta * d * elevenThirteenReplacementFloor mu nuL nuR v0 ^ alpha) :
    (graftZeroDefect mu v0 *
        replacementMass (nuR 7) (mu v0) (nuR 5) ^ (-alpha) ≤ zeta * d) ∧
      (graftZeroDefect mu v0 *
        replacementMass (nuL 9) (mu v0) (nuL 5) ^ (-alpha) ≤ zeta * d) := by
  have hfloor11 : elevenThirteenReplacementFloor mu nuL nuR v0 ≤
      replacementMass (nuR 7) (mu v0) (nuR 5) := min_le_left _ _
  have hfloor13 : elevenThirteenReplacementFloor mu nuL nuR v0 ≤
      replacementMass (nuL 9) (mu v0) (nuL 5) := min_le_right _ _
  have hp11T : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
      (PMF.apply_ne_top _ _)
  have hp13T : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
      (PMF.apply_ne_top _ _)
  constructor
  · apply graftZeroDefect_rpow_price_le mu v0 hp11 hp11T
    refine hsmall.trans ?_
    exact mul_le_mul_right
      (ENNReal.rpow_le_rpow hfloor11 halpha) (zeta * d)
  · apply graftZeroDefect_rpow_price_le mu v0 hp13 hp13T
    refine hsmall.trans ?_
    exact mul_le_mul_right
      (ENNReal.rpow_le_rpow hfloor13 halpha) (zeta * d)

/-- A weight-floor version of the zero-label condition.  If the three
common weights used by the grafts are at least `w` and `mu(v0) >= 1/2`, it
is enough to require

  1 - mu(v0) <= zeta * d * (2^-1 * w^2)^alpha.

This is the explicit relation between concentration of `mu` and the
exceptional offspring mass. -/
theorem elevenThirteen_zero_defect_price_le_of_common_floor
    {V : Type} {alpha : ℝ} (halpha : 0 ≤ alpha)
    (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    (hhalf : 2⁻¹ ≤ (mu v0 : ℝ≥0∞)) (w : ℝ≥0∞)
    (hR5 : w ≤ (nuR 5 : ℝ≥0∞))
    (hR7 : w ≤ (nuR 7 : ℝ≥0∞))
    (hL5 : w ≤ (nuL 5 : ℝ≥0∞))
    (hL9 : w ≤ (nuL 9 : ℝ≥0∞))
    {zeta d : ℝ≥0∞}
    (hw0 : w ≠ 0)
    (hsmall : graftZeroDefect mu v0 ≤
      zeta * d * (2⁻¹ * (w * w)) ^ alpha) :
    (graftZeroDefect mu v0 *
        replacementMass (nuR 7) (mu v0) (nuR 5) ^ (-alpha) ≤ zeta * d) ∧
      (graftZeroDefect mu v0 *
        replacementMass (nuL 9) (mu v0) (nuL 5) ^ (-alpha) ≤ zeta * d) := by
  have hpR : 2⁻¹ * (w * w) ≤
      replacementMass (nuR 7) (mu v0) (nuR 5) := by
    calc
      2⁻¹ * (w * w) ≤ 2⁻¹ * ((nuR 7 : ℝ≥0∞) * nuR 5) :=
        mul_le_mul_right (mul_le_mul' hR7 hR5) _
      _ ≤ replacementMass (nuR 7) (mu v0) (nuR 5) :=
        replacementMass_half_lower hhalf
  have hpL : 2⁻¹ * (w * w) ≤
      replacementMass (nuL 9) (mu v0) (nuL 5) := by
    calc
      2⁻¹ * (w * w) ≤ 2⁻¹ * ((nuL 9 : ℝ≥0∞) * nuL 5) :=
        mul_le_mul_right (mul_le_mul' hL9 hL5) _
      _ ≤ replacementMass (nuL 9) (mu v0) (nuL 5) :=
        replacementMass_half_lower hhalf
  have hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0 := by
    intro hp
    rw [hp] at hpR
    have : (2⁻¹ : ℝ≥0∞) * (w * w) ≠ 0 :=
      mul_ne_zero (by norm_num) (mul_ne_zero hw0 hw0)
    exact this (le_antisymm hpR zero_le)
  have hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0 := by
    intro hp
    rw [hp] at hpL
    have : (2⁻¹ : ℝ≥0∞) * (w * w) ≠ 0 :=
      mul_ne_zero (by norm_num) (mul_ne_zero hw0 hw0)
    exact this (le_antisymm hpL zero_le)
  apply elevenThirteen_zero_defect_price_le halpha mu nuL nuR v0 hp11 hp13
  refine hsmall.trans ?_
  apply mul_le_mul_right
  exact ENNReal.rpow_le_rpow (le_min hpR hpL) halpha

/-- The failed-zero version of the concrete grafted-11 Hall estimate.  The
coefficient left after cancellation is `zeta * d`. -/
theorem zeroCharged_elevenGraftedMacro_PhiDres_le
    {V X : Type} {alpha : ℝ} (halpha : 1 ≤ alpha)
    (mu : PMF V) (nuR : PMF ℕ) (v0 : V) (rhoL rhoR : PMF X)
    (Rv : V → V → Prop) (R : X → X → Prop)
    (f : (ℕ × (V × ℕ)) → PMF (V × ProductPower X 11))
    (eta M : ℝ≥0∞) {zeta d : ℝ≥0∞}
    (hetaTop : eta ≠ ⊤) (hMTop : M ≠ ⊤)
    (heta : PhiD alpha mu mu Rv ≤ eta)
    (hM : PhiD alpha rhoL rhoR R ≤ M)
    (hp : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hzero : graftZeroDefect mu v0 ≤
      zeta * d * replacementMass (nuR 7) (mu v0) (nuR 5) ^ alpha)
    (hcomponent : f (elevenReplacementChoice v0) =
      graftedMacroLaw mu rhoR 11) :
    graftZeroDefect mu v0 *
        PhiDres alpha (graftedMacroLaw mu rhoL 11)
          ((twoStageCounterChoice mu nuR).bind f)
          (graftedMacroRel Rv R 11) ≤
      (zeta * d) *
        (1 + ENNReal.ofReal alpha * graftedMacroBound alpha eta M 11) := by
  exact rare_elevenGraftedMacro_PhiDres_le halpha mu nuR v0 rhoL rhoR
    Rv R f eta M hetaTop hMTop heta hM hp hzero hcomponent

/-- Reverse-orientation failed-zero estimate for the grafted-13 chart. -/
theorem zeroCharged_thirteenGraftedMacro_PhiDres_le
    {V X : Type} {alpha : ℝ} (halpha : 1 ≤ alpha)
    (mu : PMF V) (nuL : PMF ℕ) (v0 : V) (rhoL rhoR : PMF X)
    (Rv : V → V → Prop) (R : X → X → Prop)
    (f : (ℕ × (V × ℕ)) → PMF (V × ProductPower X 13))
    (eta M : ℝ≥0∞) {zeta d : ℝ≥0∞}
    (hetaTop : eta ≠ ⊤) (hMTop : M ≠ ⊤)
    (heta : PhiD alpha mu mu Rv ≤ eta)
    (hM : PhiD alpha rhoR rhoL R ≤ M)
    (hp : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (hzero : graftZeroDefect mu v0 ≤
      zeta * d * replacementMass (nuL 9) (mu v0) (nuL 5) ^ alpha)
    (hcomponent : f (thirteenReplacementChoice v0) =
      graftedMacroLaw mu rhoL 13) :
    graftZeroDefect mu v0 *
        PhiDres alpha (graftedMacroLaw mu rhoR 13)
          ((twoStageCounterChoice mu nuL).bind f)
          (graftedMacroRel Rv R 13) ≤
      (zeta * d) *
        (1 + ENNReal.ofReal alpha * graftedMacroBound alpha eta M 13) := by
  exact rare_thirteenGraftedMacro_PhiDres_le halpha mu nuL v0 rhoL rhoR
    Rv R f eta M hetaTop hMTop heta hM hp hzero hcomponent

end GraphMarkovMatching
