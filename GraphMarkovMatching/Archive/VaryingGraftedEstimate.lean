/-
The explicit Green estimate for a tagged 11/13 screen ledger.

This file specialises the abstract weighted-ledger estimate of
`Closure/Green.lean` to the literal graft screen alphabet: it fixes the
finite tagged index, the coefficient-free envelope for the exceptional rows,
and the common row-sum constant, and discharges nilpotence and both row
bounds once and for all in `graftConcreteWeightedLedger_estimate`.  The
separate lemma
`elevenThirteenHallSmallness_of_half` records the simultaneous 11/13
replacement condition in terms of the literal common weights.
-/
import GraphMarkovMatching.Archive.VaryingGraftedGrammar
import GraphMarkovMatching.Closure.Green

namespace GraphMarkovMatching

open scoped ENNReal Classical

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

variable {iota : Type} [Fintype iota]

/-! ### The concrete finite tagged matrix -/

abbrev GraftLedgerIndex :=
  Bool × {sc // sc ∈ graftLiveScreens}

lemma graftLiveScreens_nonempty : graftLiveScreens.Nonempty := by
  refine ⟨⟨GraftTgt.Z2, {GraftTgt.Z3}, none⟩, ?_⟩
  simp [graftLiveScreens]

lemma graftLedgerIndex_card_pos : 0 < Fintype.card GraftLedgerIndex := by
  have hsc : (⟨GraftTgt.Z2, {GraftTgt.Z3}, none⟩ : GraftScreen) ∈
      graftLiveScreens := by simp [graftLiveScreens]
  exact Fintype.card_pos_iff.mpr
    ⟨(false, ⟨⟨GraftTgt.Z2, {GraftTgt.Z3}, none⟩, hsc⟩)⟩

/-- A coefficient-free envelope for every exceptional screen transition.
The actual rare transition graph is a subgraph of this same-orientation
complete block, so using it only enlarges the Green bound. -/
noncomputable def graftRareM (RW : ℝ≥0∞) :
    GraftLedgerIndex → GraftLedgerIndex → ℝ≥0∞ :=
  fun i j => if i.1 = j.1 then RW else 0

lemma graftRareM_row_sum_le (RW : ℝ≥0∞) (i : GraftLedgerIndex) :
    ∑ j, graftRareM RW i j ≤ RW * Fintype.card GraftLedgerIndex := by
  calc
    ∑ j, graftRareM RW i j ≤ ∑ _j : GraftLedgerIndex, RW := by
      exact Finset.sum_le_sum fun j _ => by
        by_cases h : i.1 = j.1
        · rw [graftRareM, if_pos h]
        · rw [graftRareM, if_neg h]
          exact zero_le
    _ = (Fintype.card GraftLedgerIndex : ℝ≥0∞) * RW := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = RW * Fintype.card GraftLedgerIndex := mul_comm _ _

/-- One row-sum constant which simultaneously dominates the common and rare
tagged blocks. -/
noncomputable def graftMatrixC (CW RW : ℝ≥0∞) : ℝ≥0∞ :=
  (CW + RW) * Fintype.card GraftLedgerIndex

lemma graftCommonN_row_sum_le_matrixC (CW RW : ℝ≥0∞)
    (i : GraftLedgerIndex) :
    ∑ j, graftCommonN CW i j ≤ graftMatrixC CW RW := by
  refine (graftCommonN_row_sum_le CW i).trans ?_
  rw [graftMatrixC]
  exact mul_le_mul_left le_self_add _

lemma graftRareM_row_sum_le_matrixC (CW RW : ℝ≥0∞)
    (i : GraftLedgerIndex) :
    ∑ j, graftRareM RW i j ≤ graftMatrixC CW RW := by
  refine (graftRareM_row_sum_le RW i).trans ?_
  rw [graftMatrixC]
  exact mul_le_mul_left le_add_self _

/-- **Concrete seven-symbol Hall/Green estimate.**  This specializes the
weighted ledger theorem to the literal graft screen alphabet.  Nilpotence,
positivity of the block length, and both matrix row bounds are discharged
here; downstream users need only prove their semantic one-step rows against
the displayed common-plus-rare matrix. -/
theorem graftConcreteWeightedLedger_estimate
    (CW RW zeta : ℝ≥0∞) (hzeta : zeta ≤ 1)
    (hhalf : zeta * (2 * graftMatrixC CW RW) ^
      Fintype.card GraftLedgerIndex ≤ 2⁻¹)
    (Kc eta u : ℝ≥0∞)
    (Psi : ℕ → ℝ≥0∞) (E : ℕ → GraftLedgerIndex → ℝ≥0∞)
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (hf : ∀ a a' b b', a ≤ a' → b ≤ b' → f a b ≤ f a' b')
    (hg : ∀ a a' b b', a ≤ a' → b ≤ b' → g a b ≤ g a' b')
    (hPsi0 : Psi 0 ≤ Kc * eta)
    (hE0 : ∀ i, E 0 i ≤ u)
    (hPsistep : ∀ h, Psi (h + 1) ≤ f (Psi h) (⨆ i, E h i))
    (hEstep : ∀ h i,
      E (h + 1) i ≤ g (Psi h) (⨆ j, E h j) +
        mulVecInf
          (rareMatrix (graftCommonN CW) (graftRareM RW) zeta) (E h) i)
    (hu : g (Kc * eta)
      (graftGreenMultiplier (graftMatrixC CW RW)
        (Fintype.card GraftLedgerIndex) * u) ≤ u)
    (hclose : f (Kc * eta)
      (graftGreenMultiplier (graftMatrixC CW RW)
        (Fintype.card GraftLedgerIndex) * u) ≤ Kc * eta) :
    ∀ h, Psi h ≤ Kc * eta ∧
      ∀ i, E h i ≤
        graftGreenMultiplier (graftMatrixC CW RW)
          (Fintype.card GraftLedgerIndex) * u := by
  exact graftWeightedLedger_estimate
    (graftCommonN CW) (graftRareM RW) zeta (graftMatrixC CW RW)
    (Fintype.card GraftLedgerIndex) graftLedgerIndex_card_pos hzeta
    (graftCommonN_row_sum_le_matrixC CW RW)
    (graftRareM_row_sum_le_matrixC CW RW)
    (graftCommonN_nilpotent CW (fun _ => 1)) hhalf
    Kc eta u Psi E f g hf hg hPsi0 hE0 hPsistep hEstep hu hclose

/-! ### The simultaneous literal 11/13 Hall threshold -/

/-- Under `mu(v0) >= 1/2`, one weight-only condition pays both literal
replacement cylinders.  Notice that it involves the *specific* common
weights at `5,7,9`; the largest common atom alone cannot imply it. -/
theorem elevenThirteenHallSmallness_of_half {V : Type} {alpha : ℝ}
    (halpha : 0 ≤ alpha) (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    (hhalf : 2⁻¹ ≤ (mu v0 : ℝ≥0∞)) {zeta c : ℝ≥0∞}
    (hsmall : zeta ≤ c * min
      ((2⁻¹ * ((nuR 7 : ℝ≥0∞) * nuR 5)) ^ alpha)
      ((2⁻¹ * ((nuL 9 : ℝ≥0∞) * nuL 5)) ^ alpha)) :
    zeta ≤ c * min
      ((replacementMass (nuR 7) (mu v0) (nuR 5)) ^ alpha)
      ((replacementMass (nuL 9) (mu v0) (nuL 5)) ^ alpha) := by
  have h11 : (2⁻¹ * ((nuR 7 : ℝ≥0∞) * nuR 5)) ^ alpha ≤
      (replacementMass (nuR 7) (mu v0) (nuR 5)) ^ alpha :=
    ENNReal.rpow_le_rpow (replacementMass_half_lower hhalf) halpha
  have h13 : (2⁻¹ * ((nuL 9 : ℝ≥0∞) * nuL 5)) ^ alpha ≤
      (replacementMass (nuL 9) (mu v0) (nuL 5)) ^ alpha :=
    ENNReal.rpow_le_rpow (replacementMass_half_lower hhalf) halpha
  exact hsmall.trans (mul_le_mul_right (min_le_min h11 h13) c)

/-- A convenient uniform-floor form.  If the three common weights used by
the two grafts are all at least `w`, then each replacement cylinder has mass
at least `2⁻¹ * w²`.  Hence `zeta <= c * (2⁻¹*w²)^alpha` pays both
exceptional Hall rows. -/
theorem elevenThirteenHallSmallness_of_common_floor {V : Type} {alpha : ℝ}
    (halpha : 0 ≤ alpha) (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    (hhalf : 2⁻¹ ≤ (mu v0 : ℝ≥0∞)) (w : ℝ≥0∞)
    (hR5 : w ≤ (nuR 5 : ℝ≥0∞))
    (hR7 : w ≤ (nuR 7 : ℝ≥0∞))
    (hL5 : w ≤ (nuL 5 : ℝ≥0∞))
    (hL9 : w ≤ (nuL 9 : ℝ≥0∞))
    {zeta c : ℝ≥0∞}
    (hsmall : zeta ≤ c * (2⁻¹ * (w * w)) ^ alpha) :
    zeta ≤ c * min
      ((replacementMass (nuR 7) (mu v0) (nuR 5)) ^ alpha)
      ((replacementMass (nuL 9) (mu v0) (nuL 5)) ^ alpha) := by
  have hprodR : w * w ≤ (nuR 7 : ℝ≥0∞) * nuR 5 :=
    mul_le_mul' hR7 hR5
  have hprodL : w * w ≤ (nuL 9 : ℝ≥0∞) * nuL 5 :=
    mul_le_mul' hL9 hL5
  have hrepR : 2⁻¹ * (w * w) ≤
      replacementMass (nuR 7) (mu v0) (nuR 5) := by
    calc
      2⁻¹ * (w * w) ≤ 2⁻¹ * ((nuR 7 : ℝ≥0∞) * nuR 5) :=
        by simpa [mul_comm] using
          (mul_le_mul_left hprodR (2⁻¹ : ℝ≥0∞))
      _ ≤ replacementMass (nuR 7) (mu v0) (nuR 5) :=
        replacementMass_half_lower hhalf
  have hrepL : 2⁻¹ * (w * w) ≤
      replacementMass (nuL 9) (mu v0) (nuL 5) := by
    calc
      2⁻¹ * (w * w) ≤ 2⁻¹ * ((nuL 9 : ℝ≥0∞) * nuL 5) :=
        by simpa [mul_comm] using
          (mul_le_mul_left hprodL (2⁻¹ : ℝ≥0∞))
      _ ≤ replacementMass (nuL 9) (mu v0) (nuL 5) :=
        replacementMass_half_lower hhalf
  exact hsmall.trans (mul_le_mul_right
    (le_min (ENNReal.rpow_le_rpow hrepR halpha)
      (ENNReal.rpow_le_rpow hrepL halpha)) c)

/-- The two genuinely independent smallness requirements for the fixed
example: the rare transition must contract the finite screen block, and it
must fit into both literal replacement cylinders. -/
def ElevenThirteenEstimateSmallness {V : Type} (alpha : ℝ)
    (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    (C : ℝ≥0∞) (r : ℕ) (zeta c : ℝ≥0∞) : Prop :=
  zeta ≤ 1 ∧
  zeta * (2 * C) ^ r ≤ 2⁻¹ ∧
  zeta ≤ c * min
    ((replacementMass (nuR 7) (mu v0) (nuR 5)) ^ alpha)
    ((replacementMass (nuL 9) (mu v0) (nuL 5)) ^ alpha)

end GraphMarkovMatching
