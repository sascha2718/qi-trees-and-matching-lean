import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
`sec:quantisation` of `matching_classes_simple.tex`: the level map, the level
comparison, and the quantised geometric law.

* `levelMap`: `ℓ_D = Nat.log D`, with the fibre description `level_eq_iff`
  (the classes `𝒞_k` of `sec:quantisation`).
* `thm:level`: `level_comparable` and the two-sided `level_close_comparable`.
* The quantised law: `qF a D k = a^{D^k-1} - a^{D^{k+1}-1}`, the closed form
  `eq:qk`; `class_sum` identifies it with the geometric mass of the class
  (the summation in `thm:quantised-law`); `qF_zero` and `qF_le` give the
  zero-class mass and tail bound in the same lemma; `qPMF` packages the law as a `PMF ℕ`.

The probabilistic clauses of `thm:quantised-law` (independence of the
quantised labels) sit with `thm:geometric` and are not treated here.
-/

namespace ChainClasses

open scoped ENNReal

/-! ### The level map and `thm:level` -/

/-- The level map `ℓ_D(m) = ⌊log_D m⌋`. -/
def levelMap (D m : ℕ) : ℕ := Nat.log D m

/-- The fibres of the level map are the classes `𝒞_k` of `sec:quantisation`:
`ℓ_D(m) = k` iff `D^k ≤ m < D^{k+1}`. -/
lemma level_eq_iff {D m k : ℕ} (hD : 2 ≤ D) (hm : 1 ≤ m) :
    levelMap D m = k ↔ D ^ k ≤ m ∧ m < D ^ (k + 1) := by
  constructor
  · rintro rfl
    exact ⟨Nat.pow_log_le_self D (by omega), Nat.lt_pow_succ_log_self (by omega) m⟩
  · rintro ⟨h1, h2⟩
    have hle : k ≤ levelMap D m := Nat.le_log_of_pow_le (by omega) h1
    have hlt : levelMap D m < k + 1 := by
      by_contra hcon
      have : D ^ (k + 1) ≤ D ^ (levelMap D m) := Nat.pow_le_pow_right (by omega) (by omega)
      have := le_trans this (Nat.pow_log_le_self D (by omega))
      omega
    omega

/-- One half of **`thm:level`**: `ℓ_D(m) ≤ ℓ_D(m') + 1` gives `m < D² m'`. -/
theorem level_comparable {D m m' : ℕ} (hD : 2 ≤ D) (_hm : 1 ≤ m) (hm' : 1 ≤ m')
    (h : levelMap D m ≤ levelMap D m' + 1) : m < D ^ 2 * m' := by
  have h1 : m < D ^ (levelMap D m + 1) := Nat.lt_pow_succ_log_self (by omega) m
  have h2 : D ^ levelMap D m' ≤ m' := Nat.pow_log_le_self D (by omega)
  calc m < D ^ (levelMap D m + 1) := h1
    _ ≤ D ^ (levelMap D m' + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = D ^ 2 * D ^ levelMap D m' := by ring
    _ ≤ D ^ 2 * m' := Nat.mul_le_mul_left _ h2

/-- **`thm:level`**: levels within one force length ratios within `D²`. -/
theorem level_close_comparable {D m m' : ℕ} (hD : 2 ≤ D) (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (h : levelMap D m ≤ levelMap D m' + 1) (h' : levelMap D m' ≤ levelMap D m + 1) :
    m < D ^ 2 * m' ∧ m' < D ^ 2 * m :=
  ⟨level_comparable hD hm hm' h, level_comparable hD hm' hm h'⟩

/-- The within-class ratio bound in `sec:quantisation`: two members of one
class are within the factor `D`. -/
lemma class_ratio {D m n k : ℕ} (hD : 2 ≤ D) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmk : levelMap D m = k) (hnk : levelMap D n = k) : n < D * m := by
  have h1 := (level_eq_iff hD hn).mp hnk
  have h2 := (level_eq_iff hD hm).mp hmk
  calc n < D ^ (k + 1) := h1.2
    _ = D * D ^ k := by rw [pow_succ, Nat.mul_comm]
    _ ≤ D * m := Nat.mul_le_mul_left D h2.1

/-! ### The quantised geometric law -/

variable {a : ℝ}

/-- The tail values `b_k = a^{D^k - 1}` of the geometric law at the class
boundaries: `b_k = ℙ(λ ≥ D^k)`. -/
noncomputable def tailB (a : ℝ) (D k : ℕ) : ℝ := a ^ (D ^ k - 1)

/-- `eq:qk`, as a definition: the class masses
`p^{(D)}_k = a^{D^k-1} - a^{D^{k+1}-1}` of the quantised law `p^{(D)}`. -/
noncomputable def qF (a : ℝ) (D k : ℕ) : ℝ := tailB a D k - tailB a D (k + 1)

lemma tailB_zero (a : ℝ) (D : ℕ) : tailB a D 0 = 1 := by simp [tailB]

lemma tailB_nonneg (ha : 0 ≤ a) (D k : ℕ) : 0 ≤ tailB a D k := pow_nonneg ha _

lemma tailB_le_one (ha : 0 ≤ a) (ha1 : a ≤ 1) (D k : ℕ) : tailB a D k ≤ 1 :=
  pow_le_one₀ ha ha1

lemma tailB_antitone (ha : 0 ≤ a) (ha1 : a ≤ 1) {D : ℕ} (hD : 2 ≤ D) {j k : ℕ}
    (h : j ≤ k) : tailB a D k ≤ tailB a D j := by
  apply pow_le_pow_of_le_one ha ha1
  have := Nat.pow_le_pow_right (show 1 ≤ D by omega) h
  have hj : 1 ≤ D ^ j := Nat.one_le_pow _ _ (by omega)
  omega

lemma qF_nonneg (ha : 0 ≤ a) (ha1 : a ≤ 1) {D : ℕ} (hD : 2 ≤ D) (k : ℕ) :
    0 ≤ qF a D k :=
  sub_nonneg.mpr (tailB_antitone ha ha1 hD (Nat.le_succ k))

/-- The zero-class mass in **`thm:quantised-law`**: `p^{(D)}_0 = 1 - a^{D-1}`. -/
lemma qF_zero (a : ℝ) (D : ℕ) : qF a D 0 = 1 - a ^ (D - 1) := by
  simp [qF, tailB]

/-- The tail bound in **`thm:quantised-law`**: `p^{(D)}_k ≤ a^{D^k - 1}`. -/
lemma qF_le (ha : 0 ≤ a) (_ha1 : a ≤ 1) {D : ℕ} (_hD : 2 ≤ D) (k : ℕ) :
    qF a D k ≤ tailB a D k :=
  sub_le_self _ (tailB_nonneg ha D (k + 1))

/-- The class summation of **`thm:quantised-law`** (`eq:qk`): the geometric
mass of the class `𝒞_k = [D^k, D^{k+1})` is `a^{D^k-1} - a^{D^{k+1}-1}`. Here
the geometric law is written with its natural index, `ℙ(λ = n) = a^{n-1}(1-a)`
summed over `n ∈ 𝒞_k`. -/
lemma class_sum (_ha : 0 ≤ a) {D : ℕ} (hD : 2 ≤ D) (k : ℕ) :
    ∑ n ∈ Finset.Ico (D ^ k) (D ^ (k + 1)), a ^ (n - 1) * (1 - a) = qF a D k := by
  have hk1 : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
  have hkk : D ^ k ≤ D ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  set f : ℕ → ℝ := fun j => a ^ (D ^ k + j - 1) with hf
  have hcong : ∑ n ∈ Finset.Ico (D ^ k) (D ^ (k + 1)), a ^ (n - 1) * (1 - a)
      = ∑ i ∈ Finset.range (D ^ (k + 1) - D ^ k), (f i - f (i + 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hstep : a ^ (D ^ k + i) = a ^ (D ^ k + i - 1) * a := by
      rw [← pow_succ]
      congr 1
      omega
    have hidx : D ^ k + (i + 1) - 1 = D ^ k + i := by omega
    simp only [hf, hidx]
    rw [hstep]
    ring
  rw [hcong, Finset.sum_range_sub']
  simp only [hf, qF, tailB]
  have h1 : D ^ k + 0 - 1 = D ^ k - 1 := by omega
  have h2 : D ^ k + (D ^ (k + 1) - D ^ k) - 1 = D ^ (k + 1) - 1 := by omega
  rw [h1, h2]

/-! ### The law as a `PMF` -/

/-- The tails vanish: `b_K → 0`. -/
lemma tailB_tendsto (ha : 0 ≤ a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) :
    Filter.Tendsto (fun k => tailB a D k) Filter.atTop (nhds 0) := by
  have hle : ∀ k, tailB a D k ≤ a ^ k := by
    intro k
    apply pow_le_pow_of_le_one ha ha1.le
    have : k < D ^ k := Nat.lt_pow_self (by omega)
    omega
  have hgeo : Filter.Tendsto (fun k : ℕ => a ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1
  exact squeeze_zero (fun k => tailB_nonneg ha D k) hle hgeo

lemma qF_summable (ha : 0 ≤ a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) :
    Summable (qF a D) := by
  refine Summable.of_nonneg_of_le (fun k => qF_nonneg ha ha1.le hD k)
    (fun k => ?_) (summable_geometric_of_lt_one ha ha1)
  calc qF a D k ≤ tailB a D k := qF_le ha ha1.le hD k
    _ ≤ a ^ k := by
        apply pow_le_pow_of_le_one ha ha1.le
        have : k < D ^ k := Nat.lt_pow_self (by omega)
        omega

/-- The class masses sum to one. -/
lemma qF_tsum (ha : 0 ≤ a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) :
    ∑' k, qF a D k = 1 := by
  have hsum := qF_summable ha ha1 hD
  have htend := hsum.hasSum.tendsto_sum_nat
  have hpartial : ∀ K, ∑ k ∈ Finset.range K, qF a D k = 1 - tailB a D K := by
    intro K
    rw [show (1 : ℝ) = tailB a D 0 from (tailB_zero a D).symm]
    exact Finset.sum_range_sub' (tailB a D) K
  have htend' : Filter.Tendsto (fun K => ∑ k ∈ Finset.range K, qF a D k)
      Filter.atTop (nhds 1) := by
    simp only [hpartial]
    have := (tailB_tendsto ha ha1 hD).const_sub 1
    simpa using this
  exact tendsto_nhds_unique htend htend'

/-- The class masses sum to one, in `ℝ≥0∞`. -/
lemma qF_tsum_ennreal (ha : 0 ≤ a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) :
    ∑' k, ENNReal.ofReal (qF a D k) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => qF_nonneg ha ha1.le hD k)
      (qF_summable ha ha1 hD),
    qF_tsum ha ha1 hD, ENNReal.ofReal_one]

/-- The quantised geometric law `p^{(D)}` as a `PMF ℕ`. -/
noncomputable def qPMF (ha : 0 ≤ a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (qF a D k), by
    have h := ENNReal.summable.hasSum (f := fun k => ENNReal.ofReal (qF a D k))
    rwa [qF_tsum_ennreal ha ha1 hD] at h⟩

lemma qPMF_apply (ha : 0 ≤ a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) (k : ℕ) :
    qPMF ha ha1 hD k = ENNReal.ofReal (qF a D k) := rfl

lemma qPMF_toReal (ha : 0 ≤ a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) (k : ℕ) :
    (qPMF ha ha1 hD k).toReal = qF a D k := by
  rw [qPMF_apply, ENNReal.toReal_ofReal (qF_nonneg ha ha1.le hD k)]

end ChainClasses
