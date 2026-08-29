/-
The verified structural and weight reduction for the four-point common core
`{3,5,7,9}` with exceptional counters `11` and `13`.

If the common weights have total mass `1 - ε` and `ε ≤ 1/2`, a maximal
common atom has mass at least `1/8`.  Indexing the four possible heavy
arities by `r_i = 2i+3`, with `m_i=i+1`, gives the exact shifted identity

  m_i * (13 - 1) = m_i * (11 - 1) + (r_i - 1).

Thus a block of at most four exceptional `13` offsets is balanced by the
same number of exceptional `11` offsets and one occurrence of the selected
common arity.  The exceptional factors `ε^m` stay on both sides, while the
selected common factor is uniformly at least `1/8`.  All possible selected
arities, and both exceptional arities, have two consecutive fresh-return
depths.

This module deliberately stops at that finite structural/weight reduction.
It does not assert the cross-law matching theorem: the weighted Hall
ordinary/screen rows and their scalar closure are still to be instantiated.
-/
import GraphMarkovMatching.Grammar.Depths
import GraphMarkovMatching.Potential.ZeroInterface

namespace GraphMarkovMatching

open scoped ENNReal Classical BigOperators

/-- An index where a four-point ENNReal weight vector attains its maximum. -/
noncomputable def heavyCoreIndex (w : Fin 4 → ℝ≥0∞) : Fin 4 :=
  Classical.choose
    (Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty w)

lemma heavyCoreIndex_spec (w : Fin 4 → ℝ≥0∞) :
    Finset.univ.sup' Finset.univ_nonempty w = w (heavyCoreIndex w) := by
  exact (Classical.choose_spec
    (Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty w)).2

lemma weight_le_heavyCoreWeight (w : Fin 4 → ℝ≥0∞) (i : Fin 4) :
    w i ≤ w (heavyCoreIndex w) := by
  rw [← heavyCoreIndex_spec w]
  exact Finset.le_sup' w (Finset.mem_univ i)

/-- Four times the maximal core weight dominates the total core mass. -/
theorem sum_le_four_mul_heavyCoreWeight (w : Fin 4 → ℝ≥0∞) :
    (∑ i, w i) ≤ 4 * w (heavyCoreIndex w) := by
  calc
    (∑ i, w i) ≤ ∑ _i : Fin 4, w (heavyCoreIndex w) :=
      Finset.sum_le_sum fun i _ => weight_le_heavyCoreWeight w i
    _ = 4 * w (heavyCoreIndex w) := by simp [mul_comm]

theorem eighth_le_heavyCoreWeight_of_half_le_sum (w : Fin 4 → ℝ≥0∞)
    (hhalf : 2⁻¹ ≤ ∑ i, w i) :
    8⁻¹ ≤ w (heavyCoreIndex w) := by
  have hfour : 2⁻¹ ≤ 4 * w (heavyCoreIndex w) :=
    hhalf.trans (sum_le_four_mul_heavyCoreWeight w)
  apply (ENNReal.mul_le_mul_iff_right
    (show (4 : ℝ≥0∞) ≠ 0 by norm_num)
    (show (4 : ℝ≥0∞) ≠ ∞ by norm_num)).mp
  calc
    4 * 8⁻¹ = 2⁻¹ := by
      change (↑(4 : NNReal) : ℝ≥0∞) * (↑(8 : NNReal) : ℝ≥0∞)⁻¹ =
        (↑(2 : NNReal) : ℝ≥0∞)⁻¹
      rw [← ENNReal.coe_inv (show (8 : NNReal) ≠ 0 by norm_num),
        ← ENNReal.coe_inv (show (2 : NNReal) ≠ 0 by norm_num),
        ← ENNReal.coe_mul]
      norm_num
    _ ≤ 4 * w (heavyCoreIndex w) := hfour

/-- If the exceptional mass is at most one half, some common atom has mass
at least one eighth.  No lower bound on every common atom is assumed. -/
theorem eighth_le_heavyCoreWeight {ε : ℝ≥0∞} (w : Fin 4 → ℝ≥0∞)
    (hε : ε ≤ 2⁻¹) (hsum : (∑ i, w i) = 1 - ε) :
    8⁻¹ ≤ w (heavyCoreIndex w) := by
  apply eighth_le_heavyCoreWeight_of_half_le_sum
  rw [hsum]
  apply ENNReal.le_sub_of_add_le_right
    (ne_top_of_le_ne_top (show (2⁻¹ : ℝ≥0∞) ≠ ∞ by norm_num) hε)
  calc
    2⁻¹ + ε ≤ 2⁻¹ + 2⁻¹ := add_le_add le_rfl hε
    _ = 1 := ENNReal.inv_two_add_inv_two

/-- The crude negative-real-power factor from selecting the heavy atom is
uniformly at most `8^α`. -/
theorem heavyCoreWeight_rpow_neg_le {ε : ℝ≥0∞} (w : Fin 4 → ℝ≥0∞)
    (hε : ε ≤ 2⁻¹) (hsum : (∑ i, w i) = 1 - ε)
    {α : ℝ} (hα : 0 ≤ α) :
    (w (heavyCoreIndex w)) ^ (-α) ≤ (8 : ℝ≥0∞) ^ α := by
  calc
    (w (heavyCoreIndex w)) ^ (-α) ≤ ((8 : ℝ≥0∞)⁻¹) ^ (-α) :=
      rpow_neg_antitone hα (eighth_le_heavyCoreWeight w hε hsum)
    _ = (8 : ℝ≥0∞) ^ α := by
      rw [ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]

/-- A distribution-free condition `ε ≤ c (1/8)^α` implies the
maximal-weight-dependent condition `ε ≤ c w_*^α`. -/
theorem uniform_epsilon_implies_heavy_epsilon {ε c : ℝ≥0∞}
    (w : Fin 4 → ℝ≥0∞) (hcore : 8⁻¹ ≤ w (heavyCoreIndex w))
    {α : ℝ} (hα : 0 ≤ α)
    (hε : ε ≤ c * ((8 : ℝ≥0∞)⁻¹) ^ α) :
    ε ≤ c * (w (heavyCoreIndex w)) ^ α := by
  calc
    ε ≤ c * ((8 : ℝ≥0∞)⁻¹) ^ α := hε
    _ ≤ c * (w (heavyCoreIndex w)) ^ α := by gcongr

/-- Multiplying both sides by the common exceptional block factor `ε^m`
does not introduce an inverse exceptional mass. -/
theorem heavy_block_mass_lower {ε : ℝ≥0∞} (w : Fin 4 → ℝ≥0∞)
    (hcore : 8⁻¹ ≤ w (heavyCoreIndex w)) (m : ℕ) :
    8⁻¹ * ε ^ m ≤ w (heavyCoreIndex w) * ε ^ m := by
  gcongr

/-- The four common arities, indexed so that index `i` has arity
`2(i+1)+1 = 2i+3`. -/
def rareCoreArity (i : Fin 4) : ℕ := 2 * i.1 + 3

def rareCoreSupport : Finset ℕ := {3, 5, 7, 9}

lemma rareCoreArity_mem (i : Fin 4) :
    rareCoreArity i ∈ rareCoreSupport := by
  fin_cases i <;> simp [rareCoreArity, rareCoreSupport]

/-- Both exceptional offsets belong to the additive semigroup generated by
the shifted common support.  The witnesses are `10=2+8` and `12=4+8`. -/
theorem rareCore_exception_offsets_mem :
    11 - 1 ∈ AddSubmonoid.closure
        ((fun k : ℕ => k - 1) '' (rareCoreSupport : Set ℕ)) ∧
      13 - 1 ∈ AddSubmonoid.closure
        ((fun k : ℕ => k - 1) '' (rareCoreSupport : Set ℕ)) := by
  let M := AddSubmonoid.closure
    ((fun k : ℕ => k - 1) '' (rareCoreSupport : Set ℕ))
  have h2 : 2 ∈ M := AddSubmonoid.subset_closure ⟨3, by
    simp [rareCoreSupport], by norm_num⟩
  have h4 : 4 ∈ M := AddSubmonoid.subset_closure ⟨5, by
    simp [rareCoreSupport], by norm_num⟩
  have h8 : 8 ∈ M := AddSubmonoid.subset_closure ⟨9, by
    simp [rareCoreSupport], by norm_num⟩
  constructor
  · simpa [M] using AddSubmonoid.add_mem M h2 h8
  · simpa [M] using AddSubmonoid.add_mem M h4 h8

/-- The shifted frontier identity behind the four repair blocks. -/
theorem rare_block_identity (m : ℕ) :
    m * (13 - 1) = m * (11 - 1) + ((2 * m + 1) - 1) := by
  omega

theorem rare_block_identity_of_core_index (i : Fin 4) :
    (i.1 + 1) * (13 - 1) =
      (i.1 + 1) * (11 - 1) + ((2 * i.1 + 3) - 1) := by
  omega

lemma rareCore_toFresh_five : toFresh 5 = {2, 3} := by
  rw [toFresh_of_ge (by omega)]
  norm_num
  rw [toFresh_three, toFresh_le_two (by omega)]
  decide

lemma rareCore_toFresh_seven : toFresh 7 = {2, 3} := by
  rw [toFresh_of_ge (by omega)]
  norm_num
  rw [toFresh_three]
  have h4 : toFresh 4 = {2} := by
    rw [toFresh_of_ge (by omega)]
    norm_num
    simp [toFresh_le_two]
  rw [h4]
  decide

lemma rareCore_toFresh_nine : toFresh 9 = {3, 4} := by
  rw [toFresh_of_ge (by omega)]
  norm_num
  rw [rareCore_toFresh_five]
  have h4 : toFresh 4 = {2} := by
    rw [toFresh_of_ge (by omega)]
    norm_num
    simp [toFresh_le_two]
  rw [h4]
  decide

lemma rareCore_toFresh_eleven : toFresh 11 = {3, 4} := by
  rw [toFresh_of_ge (by omega)]
  norm_num
  rw [rareCore_toFresh_five]
  have h6 : toFresh 6 = {2, 3} := by
    rw [toFresh_of_ge (by omega)]
    norm_num
    rw [toFresh_three]
    decide
  rw [h6]
  decide

lemma rareCore_toFresh_thirteen : toFresh 13 = {3, 4} := by
  rw [toFresh_of_ge (by omega)]
  norm_num
  rw [rareCore_toFresh_seven]
  have h6 : toFresh 6 = {2, 3} := by
    rw [toFresh_of_ge (by omega)]
    norm_num
    rw [toFresh_three]
    decide
  rw [h6]
  decide

/-- Every possible heavy common arity has two consecutive fresh-return
depths; the witness is uniform over the four cases. -/
theorem rareCoreArity_has_consecutive_returns (i : Fin 4) :
    ∃ d, d ∈ toFresh (rareCoreArity i) ∧
      d + 1 ∈ toFresh (rareCoreArity i) := by
  fin_cases i
  · exact ⟨1, by simp [rareCoreArity, toFresh_three]⟩
  · exact ⟨2, by simp [rareCoreArity, rareCore_toFresh_five]⟩
  · exact ⟨2, by simp [rareCoreArity, rareCore_toFresh_seven]⟩
  · exact ⟨3, by simp [rareCoreArity, rareCore_toFresh_nine]⟩

/-- Headline reduction: choose a common arity of mass at least `1/8`;
that arity supplies both the exact shifted repair identity and consecutive
binary fresh-return depths. -/
theorem exists_heavy_rare_core_repair {ε : ℝ≥0∞}
    (w : Fin 4 → ℝ≥0∞) (hε : ε ≤ 2⁻¹)
    (hsum : (∑ i, w i) = 1 - ε) :
    ∃ i : Fin 4, ∃ d : ℕ,
      8⁻¹ ≤ w i ∧
      rareCoreArity i ∈ rareCoreSupport ∧
      (i.1 + 1) * (13 - 1) =
        (i.1 + 1) * (11 - 1) + (rareCoreArity i - 1) ∧
      d ∈ toFresh (rareCoreArity i) ∧
      d + 1 ∈ toFresh (rareCoreArity i) := by
  let i := heavyCoreIndex w
  obtain ⟨d, hd, hd1⟩ := rareCoreArity_has_consecutive_returns i
  refine ⟨i, d, eighth_le_heavyCoreWeight w hε hsum,
    rareCoreArity_mem i, ?_, hd, hd1⟩
  simpa [rareCoreArity] using rare_block_identity_of_core_index i

end GraphMarkovMatching
