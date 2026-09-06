import GraphMatching.DoubleExp
import ChainClasses.Chain.Quantise

/-!
`thm:eta-bound` of `gw_classes_simple.tex`: the potential of the
quantised geometric law on the path graph, `η_{𝖯,α}(p^{(D)}) ≤ 16 a^{D(D-5/2)}
≤ 10⁻⁴`, the parametrisation of `thm:double-exp` from base `e^{-1}` to base
`a = θ₁`.

Conventions. The four largeness conditions `eq:d0-conditions` enter as
hypotheses `h1`-`h4`; the exponent `D(D-5/2)` is kept half-integral through
`qBound a D = √(a^{D(2D-5)})`, in the square-root convention of the library
(`rpow_alpha_eq_sqrt_pow`). The tails of the law are exact: the bad degree at
`0` is `a^{D²-1}` and at `1` is `a^{D³-1}` (`qE_zero_eq`, `qE_one_eq`), so no
tail-sum estimates are needed for the degrees; the term bounds and the
geometric tail then mirror `GraphMatching/DoubleExp.lean` step by step,
ending in `quantised_eta_le` and the matching instance `quantised_matching`.
-/

namespace ChainClasses

open GraphMatching
open scoped ENNReal Classical
open Real

variable {a : ℝ} {D : ℕ}

/-! ### Tails and positivity -/

/-- Tail telescoping: `∑_{k≥m} p^{(D)}_k = b_m`. -/
lemma qF_tail_tsum (ha : 0 ≤ a) (ha1 : a < 1) (hD : 2 ≤ D) (m : ℕ) :
    ∑' k, qF a D (k + m) = tailB a D m := by
  have hsum : Summable (fun k => qF a D (k + m)) :=
    (summable_nat_add_iff m).mpr (qF_summable ha ha1 hD)
  have htend := hsum.hasSum.tendsto_sum_nat
  have hpartial : ∀ K, ∑ k ∈ Finset.range K, qF a D (k + m)
      = tailB a D m - tailB a D (m + K) := by
    intro K
    have := Finset.sum_range_sub' (fun i => tailB a D (m + i)) K
    simp only [Nat.add_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [qF]
    congr 2 <;> omega
  have htend' : Filter.Tendsto (fun K => ∑ k ∈ Finset.range K, qF a D (k + m))
      Filter.atTop (nhds (tailB a D m)) := by
    simp only [hpartial]
    have hshift : Filter.Tendsto (fun K => tailB a D (m + K)) Filter.atTop (nhds 0) :=
      (tailB_tendsto ha ha1 hD).comp
        (Filter.tendsto_atTop_mono (fun K => Nat.le_add_left K m) Filter.tendsto_id)
    have := hshift.const_sub (tailB a D m)
    simpa using this
  exact tendsto_nhds_unique htend htend'

lemma qF_pos (ha : 0 < a) (ha1 : a < 1) (hD : 2 ≤ D) (k : ℕ) : 0 < qF a D k := by
  have hlt : D ^ k - 1 < D ^ (k + 1) - 1 := by
    have h1 : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
    have h2 : D ^ k < D ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have := pow_lt_pow_right_of_lt_one₀ ha ha1 hlt
  simp only [qF, tailB]
  linarith

/-! ### The bad degrees, exactly -/

/-- The bad degree at `0` is the mass beyond the ball `{0,1}`: `a^{D²-1}`. -/
lemma qE_zero_eq (ha : 0 ≤ a) (ha1 : a < 1) (hD : 2 ≤ D) :
    qE (qPMF ha ha1 hD) (compat pathGraph) 0 = ENNReal.ofReal (tailB a D 2) := by
  rw [qE, tsum_eq_zero_add' ENNReal.summable, tsum_eq_zero_add' ENNReal.summable]
  have e0 : (if compat pathGraph 0 0 then (0 : ℝ≥0∞) else qPMF ha ha1 hD 0) = 0 :=
    if_pos (Or.inl rfl)
  have e1 : (if compat pathGraph 0 (0 + 1) then (0 : ℝ≥0∞) else qPMF ha ha1 hD (0 + 1)) = 0 :=
    if_pos (Or.inr (by rw [pathGraph_adj]; omega))
  have e2 : ∀ k, (if compat pathGraph 0 (k + 1 + 1) then (0 : ℝ≥0∞)
      else qPMF ha ha1 hD (k + 1 + 1)) = ENNReal.ofReal (qF a D (k + 2)) := by
    intro k
    have hnc : ¬ compat pathGraph 0 (k + 1 + 1) := by
      rintro (h | h)
      · omega
      · rw [pathGraph_adj] at h; omega
    rw [if_neg hnc, qPMF_apply]
  rw [e0, e1, zero_add, zero_add]
  simp only [e2]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => qF_nonneg ha ha1.le hD _)
      ((summable_nat_add_iff 2).mpr (qF_summable ha ha1 hD)),
    qF_tail_tsum ha ha1 hD 2]

/-- The bad degree at `1` is the mass beyond the ball `{0,1,2}`: `a^{D³-1}`. -/
lemma qE_one_eq (ha : 0 ≤ a) (ha1 : a < 1) (hD : 2 ≤ D) :
    qE (qPMF ha ha1 hD) (compat pathGraph) 1 = ENNReal.ofReal (tailB a D 3) := by
  rw [qE, tsum_eq_zero_add' ENNReal.summable, tsum_eq_zero_add' ENNReal.summable,
    tsum_eq_zero_add' ENNReal.summable]
  have e0 : (if compat pathGraph 1 0 then (0 : ℝ≥0∞) else qPMF ha ha1 hD 0) = 0 :=
    if_pos (Or.inr (by rw [pathGraph_adj]; omega))
  have e1 : (if compat pathGraph 1 (0 + 1) then (0 : ℝ≥0∞) else qPMF ha ha1 hD (0 + 1)) = 0 :=
    if_pos (Or.inl rfl)
  have e2 : (if compat pathGraph 1 (0 + 1 + 1) then (0 : ℝ≥0∞)
      else qPMF ha ha1 hD (0 + 1 + 1)) = 0 :=
    if_pos (Or.inr (by rw [pathGraph_adj]; omega))
  have e3 : ∀ k, (if compat pathGraph 1 (k + 1 + 1 + 1) then (0 : ℝ≥0∞)
      else qPMF ha ha1 hD (k + 1 + 1 + 1)) = ENNReal.ofReal (qF a D (k + 3)) := by
    intro k
    have hnc : ¬ compat pathGraph 1 (k + 1 + 1 + 1) := by
      rintro (h | h)
      · omega
      · rw [pathGraph_adj] at h; omega
    rw [if_neg hnc, qPMF_apply]
  rw [e0, e1, e2, zero_add, zero_add, zero_add]
  simp only [e3]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => qF_nonneg ha ha1.le hD _)
      ((summable_nat_add_iff 3).mpr (qF_summable ha ha1 hD)),
    qF_tail_tsum ha ha1 hD 3]

/-! ### The good degrees -/

lemma qgdeg_pos (ha : 0 < a) (ha1 : a < 1) (hD : 2 ≤ D) (j : ℕ) :
    0 < gdeg (qPMF ha.le ha1 hD) pathGraph j := by
  refine lt_of_lt_of_le ?_
    (p_toReal_le_gdeg (qPMF ha.le ha1 hD) pathGraph (compat_refl pathGraph j))
  rw [qPMF_toReal]
  exact qF_pos ha ha1 hD j

lemma qgdeg_zero_gt (ha : 0 < a) (ha1 : a < 1) (hD : 2 ≤ D)
    (h1 : a ^ (D - 1) ≤ 1 / 10) :
    1 / 2 < gdeg (qPMF ha.le ha1 hD) pathGraph 0 := by
  have h := p_toReal_le_gdeg (qPMF ha.le ha1 hD) pathGraph (compat_refl pathGraph 0)
  rw [qPMF_toReal, qF_zero] at h
  linarith

lemma qgdeg_one_gt (ha : 0 < a) (ha1 : a < 1) (hD : 2 ≤ D)
    (h1 : a ^ (D - 1) ≤ 1 / 10) :
    1 / 2 < gdeg (qPMF ha.le ha1 hD) pathGraph 1 := by
  have h := p_toReal_le_gdeg (qPMF ha.le ha1 hD) pathGraph (v := 1) (w := 0)
    (Or.inr (by rw [pathGraph_adj]; omega))
  rw [qPMF_toReal, qF_zero] at h
  linarith

/-! ### The η terms -/

/-- The real summand of `η_{𝖯,α}` for the quantised law. -/
noncomputable def qTerm (ha : 0 < a) (ha1 : a < 1) (hD : 2 ≤ D) (j : ℕ) : ℝ :=
  (qPMF ha.le ha1 hD j).toReal *
    ((1 - gdeg (qPMF ha.le ha1 hD) pathGraph j)
      / gdeg (qPMF ha.le ha1 hD) pathGraph j ^ alpha)

lemma qTerm_nonneg (ha : 0 < a) (ha1 : a < 1) (hD : 2 ≤ D) (j : ℕ) :
    0 ≤ qTerm ha ha1 hD j := by
  have h1 : (0 : ℝ) ≤ 1 - gdeg (qPMF ha.le ha1 hD) pathGraph j := by
    have h2 : gdeg (qPMF ha.le ha1 hD) pathGraph j ≤ 1 := by
      rw [gdeg]; exact ENNReal.toReal_mono ENNReal.one_ne_top rE_le_one
    linarith
  have h3 : 0 < gdeg (qPMF ha.le ha1 hD) pathGraph j ^ alpha :=
    Real.rpow_pos_of_pos (qgdeg_pos ha ha1 hD j) alpha
  exact mul_nonneg ENNReal.toReal_nonneg (div_nonneg h1 h3.le)

lemma qTerm_zero_le (ha : 0 < a) (ha1 : a < 1) (hD : 2 ≤ D)
    (h1 : a ^ (D - 1) ≤ 1 / 10) :
    qTerm ha ha1 hD 0 ≤ 6 * tailB a D 2 := by
  have hp : (qPMF ha.le ha1 hD 0).toReal ≤ 1 := mu_toReal_le_one _ 0
  have hs0a : 0 < gdeg (qPMF ha.le ha1 hD) pathGraph 0 ^ alpha :=
    Real.rpow_pos_of_pos (qgdeg_pos ha ha1 hD 0) alpha
  have hinv : 1 / gdeg (qPMF ha.le ha1 hD) pathGraph 0 ^ alpha ≤ 6 :=
    inv_rpow_le_six (qgdeg_zero_gt ha ha1 hD h1)
  have hsub : 1 - gdeg (qPMF ha.le ha1 hD) pathGraph 0 = tailB a D 2 := by
    rw [one_sub_gdeg, qE_zero_eq ha.le ha1 hD,
      ENNReal.toReal_ofReal (tailB_nonneg ha.le D 2)]
  have hb : 0 ≤ tailB a D 2 := tailB_nonneg ha.le D 2
  have hXle : (1 - gdeg (qPMF ha.le ha1 hD) pathGraph 0)
      * (1 / gdeg (qPMF ha.le ha1 hD) pathGraph 0 ^ alpha) ≤ tailB a D 2 * 6 := by
    rw [hsub]
    exact mul_le_mul_of_nonneg_left hinv hb
  have hXnn : 0 ≤ (1 - gdeg (qPMF ha.le ha1 hD) pathGraph 0)
      * (1 / gdeg (qPMF ha.le ha1 hD) pathGraph 0 ^ alpha) := by
    rw [hsub]
    exact mul_nonneg hb (one_div_pos.mpr hs0a).le
  rw [qTerm, div_eq_mul_one_div]
  nlinarith [ENNReal.toReal_nonneg (a := qPMF ha.le ha1 hD 0), hXnn, hXle, hb]

lemma qTerm_one_le (ha : 0 < a) (ha1 : a < 1) (hD : 2 ≤ D)
    (h1 : a ^ (D - 1) ≤ 1 / 10) :
    qTerm ha ha1 hD 1 ≤ 6 * tailB a D 3 := by
  have hp : (qPMF ha.le ha1 hD 1).toReal ≤ 1 := mu_toReal_le_one _ 1
  have hs1a : 0 < gdeg (qPMF ha.le ha1 hD) pathGraph 1 ^ alpha :=
    Real.rpow_pos_of_pos (qgdeg_pos ha ha1 hD 1) alpha
  have hinv : 1 / gdeg (qPMF ha.le ha1 hD) pathGraph 1 ^ alpha ≤ 6 :=
    inv_rpow_le_six (qgdeg_one_gt ha ha1 hD h1)
  have hsub : 1 - gdeg (qPMF ha.le ha1 hD) pathGraph 1 = tailB a D 3 := by
    rw [one_sub_gdeg, qE_one_eq ha.le ha1 hD,
      ENNReal.toReal_ofReal (tailB_nonneg ha.le D 3)]
  have hb : 0 ≤ tailB a D 3 := tailB_nonneg ha.le D 3
  have hXle : (1 - gdeg (qPMF ha.le ha1 hD) pathGraph 1)
      * (1 / gdeg (qPMF ha.le ha1 hD) pathGraph 1 ^ alpha) ≤ tailB a D 3 * 6 := by
    rw [hsub]
    exact mul_le_mul_of_nonneg_left hinv hb
  have hXnn : 0 ≤ (1 - gdeg (qPMF ha.le ha1 hD) pathGraph 1)
      * (1 / gdeg (qPMF ha.le ha1 hD) pathGraph 1 ^ alpha) := by
    rw [hsub]
    exact mul_nonneg hb (one_div_pos.mpr hs1a).le
  rw [qTerm, div_eq_mul_one_div]
  nlinarith [ENNReal.toReal_nonneg (a := qPMF ha.le ha1 hD 1), hXnn, hXle, hb]

/-! ### Square roots of powers -/

lemma sqrt_pow_eq (ha : 0 ≤ a) (n : ℕ) :
    Real.sqrt (a ^ n) = Real.sqrt a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg ha n), ih, pow_succ]

/-- The half-integral bound `a^{D(D-5/2)}`, in the square-root convention. -/
noncomputable def qBound (a : ℝ) (D : ℕ) : ℝ := Real.sqrt (a ^ (D * (2 * D - 5)))

lemma qBound_nonneg (a : ℝ) (D : ℕ) : 0 ≤ qBound a D := Real.sqrt_nonneg _

/-- `6 a^{D²-1} ≤ a^{D(D-5/2)}`, the third condition of `eq:d0-conditions`. -/
lemma six_tailB_le_qBound (ha : 0 < a) (_ha1 : a < 1) (hD : 5 ≤ D)
    (h3 : 36 * a ^ (5 * D - 2) ≤ 1) :
    6 * tailB a D 2 ≤ qBound a D := by
  have hb : (0 : ℝ) ≤ 6 * tailB a D 2 := by
    have := tailB_nonneg ha.le D 2
    linarith
  rw [show (6 : ℝ) * tailB a D 2 = Real.sqrt ((6 * tailB a D 2) ^ 2) from
    (Real.sqrt_sq hb).symm]
  apply Real.sqrt_le_sqrt
  have hd2 : 1 ≤ D ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h5 : 5 ≤ 2 * D := by omega
  have h52 : 2 ≤ 5 * D := by omega
  have hexp : 2 * (D ^ 2 - 1) = D * (2 * D - 5) + (5 * D - 2) := by
    zify [hd2, h5, h52]
    ring
  have hsq : (6 * tailB a D 2) ^ 2 = 36 * a ^ (2 * (D ^ 2 - 1)) := by
    have h2c : 2 * (D ^ 2 - 1) = (D ^ 2 - 1) * 2 := Nat.mul_comm _ _
    rw [h2c]
    simp only [tailB]
    rw [mul_pow, ← pow_mul]
    norm_num
  rw [hsq, hexp, pow_add]
  calc 36 * (a ^ (D * (2 * D - 5)) * a ^ (5 * D - 2))
      = a ^ (D * (2 * D - 5)) * (36 * a ^ (5 * D - 2)) := by ring
    _ ≤ a ^ (D * (2 * D - 5)) * 1 :=
        mul_le_mul_of_nonneg_left h3 (pow_nonneg ha.le _)
    _ = a ^ (D * (2 * D - 5)) := mul_one _

/-! ### The tail terms -/

/-- The tail-bound sequence `u_j = a^{D^{j+1}(D-5/2)}`. -/
noncomputable def qU (a : ℝ) (D j : ℕ) : ℝ :=
  Real.sqrt (a ^ (D ^ (j + 1) * (2 * D - 5)))

lemma qU_nonneg (a : ℝ) (D j : ℕ) : 0 ≤ qU a D j := Real.sqrt_nonneg _

lemma qU_pos (ha : 0 < a) (D j : ℕ) : 0 < qU a D j :=
  Real.sqrt_pos.mpr (pow_pos ha _)

lemma qU_zero_eq (a : ℝ) (D : ℕ) : qU a D 0 = qBound a D := by
  simp [qU, qBound]

/-- The half of `eq:d0-conditions` used for the tail: `p_{j+1} ≥ b_{j+1}/2`. -/
lemma qF_ge_half_tailB (ha : 0 < a) (ha1 : a < 1) (hD : 2 ≤ D)
    (h2 : a ^ (D ^ 2 - D) ≤ 1 / 2) (k : ℕ) (hk : 1 ≤ k) :
    tailB a D k / 2 ≤ qF a D k := by
  have hsplit : tailB a D (k + 1) = tailB a D k * a ^ (D ^ (k + 1) - D ^ k) := by
    simp only [tailB]
    rw [← pow_add]
    congr 1
    have h1 : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
    have h2' : D ^ k ≤ D ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hmono : a ^ (D ^ (k + 1) - D ^ k) ≤ a ^ (D ^ 2 - D) := by
    apply pow_le_pow_of_le_one ha.le ha1.le
    have e1 : D ^ (k + 1) - D ^ k = D ^ k * (D - 1) := by
      rw [pow_succ, Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
    have e2 : D ^ 2 - D = D * (D - 1) := by
      rw [sq, Nat.mul_sub, Nat.mul_one]
    have hDP : D ≤ D ^ k := Nat.le_self_pow (by omega) D
    rw [e1, e2]
    exact Nat.mul_le_mul_right _ hDP
  have hhalf : a ^ (D ^ (k + 1) - D ^ k) ≤ 1 / 2 := le_trans hmono h2
  have hbpos : 0 ≤ tailB a D k := tailB_nonneg ha.le D k
  simp only [qF]
  rw [hsplit]
  nlinarith [hbpos, hhalf]

/-- `2^{5/2} ≤ 6`. -/
lemma two_rpow_alpha_le_six : (2 : ℝ) ^ alpha ≤ 6 := by
  rw [rpow_alpha_eq_sqrt_pow (by norm_num : (0:ℝ) ≤ 2)]
  have h : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3:ℝ)/2 = Real.sqrt ((3/2)^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h5 : Real.sqrt 2 ^ 5 = 4 * Real.sqrt 2 := by
    have hh : Real.sqrt 2 ^ 5 = (Real.sqrt 2 ^ 2) ^ 2 * Real.sqrt 2 := by ring
    rw [hh, h2]; norm_num
  rw [h5]; nlinarith [h, h0]

/-- The raw tail bound: `T_{j+2} ≤ b_{j+2} · 2^α / b_{j+1}^α`. -/
lemma qTerm_tail_raw (ha : 0 < a) (ha1 : a < 1) (hD : 2 ≤ D)
    (h2 : a ^ (D ^ 2 - D) ≤ 1 / 2) (j : ℕ) :
    qTerm ha ha1 hD (j + 2)
      ≤ tailB a D (j + 2) * ((2 : ℝ) ^ alpha / tailB a D (j + 1) ^ alpha) := by
  have hp : (qPMF ha.le ha1 hD (j + 2)).toReal ≤ tailB a D (j + 2) := by
    rw [qPMF_toReal]; exact qF_le ha.le ha1.le hD (j + 2)
  have hgd : tailB a D (j + 1) / 2 ≤ gdeg (qPMF ha.le ha1 hD) pathGraph (j + 2) := by
    have h := p_toReal_le_gdeg (qPMF ha.le ha1 hD) pathGraph (v := j + 2) (w := j + 1)
      (Or.inr (by rw [pathGraph_adj]; omega))
    rw [qPMF_toReal] at h
    exact le_trans (qF_ge_half_tailB ha ha1 hD h2 (j + 1) (by omega)) h
  have hbpos : 0 < tailB a D (j + 1) := pow_pos ha _
  have hhalfpos : 0 < tailB a D (j + 1) / 2 := by linarith
  have hgpos := qgdeg_pos ha ha1 hD (j + 2)
  have hsub1 : 1 - gdeg (qPMF ha.le ha1 hD) pathGraph (j + 2) ≤ 1 := by linarith
  have hsubnn : 0 ≤ 1 - gdeg (qPMF ha.le ha1 hD) pathGraph (j + 2) := by
    have hle1 : gdeg (qPMF ha.le ha1 hD) pathGraph (j + 2) ≤ 1 := by
      rw [gdeg]; exact ENNReal.toReal_mono ENNReal.one_ne_top rE_le_one
    linarith
  have hgpow : (tailB a D (j + 1) / 2) ^ alpha
      ≤ gdeg (qPMF ha.le ha1 hD) pathGraph (j + 2) ^ alpha :=
    Real.rpow_le_rpow hhalfpos.le hgd alpha_nonneg
  have hhpowpos : 0 < (tailB a D (j + 1) / 2) ^ alpha :=
    Real.rpow_pos_of_pos hhalfpos alpha
  have hs2a : 0 < gdeg (qPMF ha.le ha1 hD) pathGraph (j + 2) ^ alpha :=
    Real.rpow_pos_of_pos hgpos alpha
  have hquot : (1 - gdeg (qPMF ha.le ha1 hD) pathGraph (j + 2))
      / gdeg (qPMF ha.le ha1 hD) pathGraph (j + 2) ^ alpha
      ≤ 1 / (tailB a D (j + 1) / 2) ^ alpha :=
    div_le_div₀ zero_le_one hsub1 hhpowpos hgpow
  have hmul : qTerm ha ha1 hD (j + 2)
      ≤ tailB a D (j + 2) * (1 / (tailB a D (j + 1) / 2) ^ alpha) := by
    rw [qTerm]
    exact mul_le_mul hp hquot (div_nonneg hsubnn hs2a.le) (tailB_nonneg ha.le D _)
  refine le_trans hmul ?_
  rw [Real.div_rpow hbpos.le (by norm_num : (0:ℝ) ≤ 2), one_div_div]

/-- The power step: `b_{j+2}·2^α/b_{j+1}^α ≤ 6 u_j`. -/
lemma qratio_le (ha : 0 < a) (ha1 : a < 1) (hD : 5 ≤ D) (j : ℕ) :
    tailB a D (j + 2) * ((2 : ℝ) ^ alpha / tailB a D (j + 1) ^ alpha)
      ≤ 6 * qU a D j := by
  set A : ℕ := D ^ (j + 1) - 1 with hA
  set B : ℕ := D ^ (j + 2) - 1 with hB
  set C : ℕ := D ^ (j + 1) * (2 * D - 5) with hC
  have hP1 : 1 ≤ D ^ (j + 1) := Nat.one_le_pow _ _ (by omega)
  have hQ1 : 1 ≤ D ^ (j + 2) := Nat.one_le_pow _ _ (by omega)
  have hPQ : D ^ (j + 2) = D ^ (j + 1) * D := pow_succ D (j + 1)
  have hkey : 2 * B = 5 * A + C + 3 := by
    have hb1 : 5 ≤ 2 * D := by omega
    simp only [hA, hB, hC]
    zify [hP1, hQ1, hb1]
    ring
  have hcast : (2 : ℝ) * B = 5 * A + C + 3 := by exact_mod_cast hkey
  have hb2 : tailB a D (j + 2) = a ^ ((B : ℝ)) := by
    rw [tailB, ← Real.rpow_natCast a B]
  have hb1a : tailB a D (j + 1) ^ alpha = a ^ ((A : ℝ) * alpha) := by
    rw [tailB, ← Real.rpow_natCast a A, ← Real.rpow_mul ha.le]
  have hqU : qU a D j = a ^ ((C : ℝ) / 2) := by
    rw [qU, Real.sqrt_eq_rpow, ← Real.rpow_natCast a C, ← Real.rpow_mul ha.le]
    congr 1
    ring
  have hexp_le : (C : ℝ) / 2 ≤ (B : ℝ) - (A : ℝ) * alpha := by
    simp only [alpha]
    linarith [hcast]
  have hbase : a ^ ((B : ℝ)) / a ^ ((A : ℝ) * alpha)
      = a ^ ((B : ℝ) - (A : ℝ) * alpha) := (Real.rpow_sub ha _ _).symm
  rw [hb2, hb1a, hqU]
  calc a ^ ((B : ℝ)) * ((2:ℝ) ^ alpha / a ^ ((A : ℝ) * alpha))
      = (2:ℝ) ^ alpha * (a ^ ((B : ℝ)) / a ^ ((A : ℝ) * alpha)) := by ring
    _ = (2:ℝ) ^ alpha * a ^ ((B : ℝ) - (A : ℝ) * alpha) := by rw [hbase]
    _ ≤ 6 * a ^ ((C : ℝ) / 2) :=
        mul_le_mul two_rpow_alpha_le_six
          (Real.rpow_le_rpow_of_exponent_ge ha ha1.le hexp_le)
          (Real.rpow_pos_of_pos ha _).le (by norm_num)

/-- The combined tail bound `T_{j+2} ≤ 6 u_j`. -/
lemma qTerm_tail_le (ha : 0 < a) (ha1 : a < 1) (hD : 5 ≤ D)
    (h2 : a ^ (D ^ 2 - D) ≤ 1 / 2) (j : ℕ) :
    qTerm ha ha1 (show 2 ≤ D by omega) (j + 2) ≤ 6 * qU a D j :=
  le_trans (qTerm_tail_raw ha ha1 (show 2 ≤ D by omega) h2 j) (qratio_le ha ha1 hD j)

/-- The ratio of the tail bounds is at most `1/2`. -/
lemma qU_ratio (ha : 0 < a) (ha1 : a < 1) (hD : 5 ≤ D)
    (h2 : a ^ (D ^ 2 - D) ≤ 1 / 2) (j : ℕ) :
    qU a D (j + 1) ≤ (1 / 2) * qU a D j := by
  have hPQ : D ^ (j + 2) = D ^ (j + 1) * D := pow_succ D (j + 1)
  have hmon : D ^ (j + 1) ≤ D ^ (j + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hsplitN : D ^ (j + 2) * (2 * D - 5)
      = D ^ (j + 1) * (2 * D - 5) + (2 * D - 5) * (D ^ (j + 2) - D ^ (j + 1)) := by
    have hb1 : 5 ≤ 2 * D := by omega
    zify [hmon, hb1]
    ring
  have hDelta : 2 * (D ^ 2 - D) ≤ (2 * D - 5) * (D ^ (j + 2) - D ^ (j + 1)) := by
    have e1 : D ^ (j + 2) - D ^ (j + 1) = D ^ (j + 1) * (D - 1) := by
      rw [pow_succ, Nat.mul_sub, Nat.mul_one]
    have e2 : D ^ 2 - D = D * (D - 1) := by rw [sq, Nat.mul_sub, Nat.mul_one]
    have hDP : D ≤ D ^ (j + 1) := Nat.le_self_pow (by omega) D
    rw [e1, e2]
    calc 2 * (D * (D - 1)) ≤ (2 * D - 5) * (D * (D - 1)) :=
          Nat.mul_le_mul_right _ (by omega)
      _ ≤ (2 * D - 5) * (D ^ (j + 1) * (D - 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hDP)
  have hsplit : qU a D (j + 1)
      = qU a D j * Real.sqrt (a ^ ((2 * D - 5) * (D ^ (j + 2) - D ^ (j + 1)))) := by
    rw [qU, qU, ← Real.sqrt_mul (pow_nonneg ha.le _), ← pow_add, hsplitN]
  have hle : Real.sqrt (a ^ ((2 * D - 5) * (D ^ (j + 2) - D ^ (j + 1)))) ≤ 1 / 2 := by
    have hmono : a ^ ((2 * D - 5) * (D ^ (j + 2) - D ^ (j + 1)))
        ≤ (a ^ (D ^ 2 - D)) ^ 2 := by
      rw [← pow_mul]
      apply pow_le_pow_of_le_one ha.le ha1.le
      omega
    have hs := Real.sqrt_le_sqrt hmono
    rw [Real.sqrt_sq (pow_nonneg ha.le _)] at hs
    linarith
  rw [hsplit]
  have hqUnn := qU_nonneg a D j
  calc qU a D j * Real.sqrt (a ^ ((2 * D - 5) * (D ^ (j + 2) - D ^ (j + 1))))
      ≤ qU a D j * (1 / 2) := mul_le_mul_of_nonneg_left hle hqUnn
    _ = (1 / 2) * qU a D j := by ring

lemma qU_tail (ha : 0 < a) (ha1 : a < 1) (hD : 5 ≤ D)
    (h2 : a ^ (D ^ 2 - D) ≤ 1 / 2) :
    Summable (qU a D) ∧ ∑' j, qU a D j ≤ 2 * qU a D 0 :=
  geo_tail (fun j => qU_nonneg a D j) (fun j => qU_ratio ha ha1 hD h2 j)

lemma summable_qTerm (ha : 0 < a) (ha1 : a < 1) (hD : 5 ≤ D)
    (h2 : a ^ (D ^ 2 - D) ≤ 1 / 2) :
    Summable (qTerm ha ha1 (show 2 ≤ D by omega)) := by
  rw [← summable_nat_add_iff 2]
  exact Summable.of_nonneg_of_le (fun j => qTerm_nonneg ha ha1 _ (j + 2))
    (fun j => qTerm_tail_le ha ha1 hD h2 j)
    ((qU_tail ha ha1 hD h2).1.mul_left 6)

lemma qEtaP_eq (ha : 0 < a) (ha1 : a < 1) (hD : 5 ≤ D)
    (h2 : a ^ (D ^ 2 - D) ≤ 1 / 2) :
    etaP (qPMF ha.le ha1 (show 2 ≤ D by omega))
      = ENNReal.ofReal (∑' j, qTerm ha ha1 (show 2 ≤ D by omega) j) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun j => qTerm_nonneg ha ha1 _ j)
    (summable_qTerm ha ha1 hD h2), etaP, etaG]
  refine tsum_congr fun j => ?_
  rw [qTerm, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal ((qPMF ha.le ha1 (show 2 ≤ D by omega)).apply_ne_top j)]

/-- **`thm:eta-bound`, the potential estimate**: under the largeness conditions
`eq:d0-conditions`, `η_{𝖯,α}(p^{(D)}) ≤ 16 a^{D(D-5/2)}`. -/
theorem quantised_eta_le (ha : 0 < a) (ha1 : a < 1) (hD : 5 ≤ D)
    (h1 : a ^ (D - 1) ≤ 1 / 10) (h2 : a ^ (D ^ 2 - D) ≤ 1 / 2)
    (h3 : 36 * a ^ (5 * D - 2) ≤ 1) :
    etaP (qPMF ha.le ha1 (show 2 ≤ D by omega))
      ≤ ENNReal.ofReal (16 * qBound a D) := by
  rw [qEtaP_eq ha ha1 hD h2]
  apply ENNReal.ofReal_le_ofReal
  have hsum := summable_qTerm ha ha1 hD h2
  have hpeel : ∑' j, qTerm ha ha1 (show 2 ≤ D by omega) j
      = qTerm ha ha1 (show 2 ≤ D by omega) 0
        + (qTerm ha ha1 (show 2 ≤ D by omega) 1
          + ∑' j, qTerm ha ha1 (show 2 ≤ D by omega) (j + 2)) := by
    rw [hsum.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hsum).tsum_eq_zero_add]
  have htail : ∑' j, qTerm ha ha1 (show 2 ≤ D by omega) (j + 2)
      ≤ 12 * qBound a D := by
    have hle := Summable.tsum_le_tsum (fun j => qTerm_tail_le ha ha1 hD h2 j)
      ((summable_nat_add_iff 2).mpr hsum) ((qU_tail ha ha1 hD h2).1.mul_left 6)
    have heq : ∑' j, 6 * qU a D j = 6 * ∑' j, qU a D j := tsum_mul_left
    have hqu := (qU_tail ha ha1 hD h2).2
    rw [heq] at hle
    rw [← qU_zero_eq a D]
    linarith [hle, hqu]
  have hb32 : tailB a D 3 ≤ tailB a D 2 :=
    tailB_antitone ha.le ha1.le (by omega) (by omega)
  have hqB := six_tailB_le_qBound ha ha1 hD h3
  have h0 : qTerm ha ha1 (show 2 ≤ D by omega) 0 ≤ qBound a D :=
    le_trans (qTerm_zero_le ha ha1 _ h1) hqB
  have h1' : qTerm ha ha1 (show 2 ≤ D by omega) 1 ≤ qBound a D := by
    refine le_trans (qTerm_one_le ha ha1 _ h1) (le_trans ?_ hqB)
    linarith
  rw [hpeel]
  have hqBnn := qBound_nonneg a D
  linarith [h0, h1', htail]

/-- **`thm:eta-bound`, the matching instance**: with the final condition
`16 a^{D(D-5/2)} ≤ 10⁻⁴`, the full-matching failure probability of the
quantised law is at most `16 η_{𝖯,α}(p^{(D)})`. -/
theorem quantised_matching (ha : 0 < a) (ha1 : a < 1) (hD : 5 ≤ D)
    (h1 : a ^ (D - 1) ≤ 1 / 10) (h2 : a ^ (D ^ 2 - D) ≤ 1 / 2)
    (h3 : 36 * a ^ (5 * D - 2) ≤ 1) (h4 : 16 * qBound a D ≤ 1 / 10000) (h : ℕ) :
    ∑' x, fullMu (qPMF ha.le ha1 (show 2 ≤ D by omega)) h x
        * qE (fullMu (qPMF ha.le ha1 (show 2 ≤ D by omega)) h)
          (fullSim (compat pathGraph) h) x
      ≤ 16 * etaP (qPMF ha.le ha1 (show 2 ≤ D by omega)) := by
  refine path_full_matching_bound _ ?_ h
  refine le_trans (quantised_eta_le ha ha1 hD h1 h2 h3) ?_
  rw [show (1 : ℝ≥0∞) / 10000 = ENNReal.ofReal (1 / 10000) from by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]]
  exact ENNReal.ofReal_le_ofReal h4

/-! ### The largeness conditions are met -/

/-- **`eq:d0-conditions` hold at some scale.**  Every condition is a bound on a
power of `a<1`, so all of them follow once `a^{D-1}` is small enough.  The
prescribed lower bound `M` lets a caller ask in addition for a scale meeting a
further condition of its own, as `thm:cross-law` does for `γ(D-1)≥1`. -/
theorem exists_scale {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    ∃ D : ℕ, 5 ≤ D ∧ M ≤ D ∧
      a ^ (D - 1) ≤ 1 / 10 ∧ a ^ (D ^ 2 - D) ≤ 1 / 2 ∧
      36 * a ^ (5 * D - 2) ≤ 1 ∧ 16 * qBound a D ≤ 1 / 10000 ∧
      256 * qBound a D < ε := by
  set δ : ℝ := min (min (1 / 36) ((ε / 512) ^ 2)) ((1 / 160000) ^ 2) with hδdef
  have hδ : 0 < δ := by
    refine lt_min (lt_min (by norm_num) ?_) (by norm_num)
    positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Filter.Tendsto.eventually_le_const hδ
      (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1))
  set D : ℕ := max (max 5 (N + 1)) M with hDdef
  have hD5 : 5 ≤ D := le_trans (le_max_left 5 (N + 1)) (le_max_left _ _)
  have hDN : N ≤ D - 1 := by
    have := le_trans (le_max_right 5 (N + 1)) (le_max_left _ _ : max 5 (N + 1) ≤ D)
    omega
  have hDM : M ≤ D := le_max_right _ _
  have key : a ^ (D - 1) ≤ δ := hN (D - 1) hDN
  have h36 : δ ≤ 1 / 36 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hmono : ∀ m : ℕ, D - 1 ≤ m → a ^ m ≤ δ :=
    fun m hm ↦ le_trans (pow_le_pow_of_le_one ha0.le ha1.le hm) key
  have hqle : qBound a D ≤ Real.sqrt δ := by
    rw [qBound]
    refine Real.sqrt_le_sqrt (hmono _ ?_)
    calc D - 1 ≤ D * 1 := by omega
      _ ≤ D * (2 * D - 5) := Nat.mul_le_mul_left D (by omega)
  have hs1 : Real.sqrt δ ≤ 1 / 160000 := by
    have h : δ ≤ (1 / 160000 : ℝ) ^ 2 := min_le_right _ _
    calc Real.sqrt δ ≤ Real.sqrt ((1 / 160000 : ℝ) ^ 2) := Real.sqrt_le_sqrt h
      _ = 1 / 160000 := Real.sqrt_sq (by norm_num)
  have hs2 : Real.sqrt δ ≤ ε / 512 := by
    have h : δ ≤ (ε / 512 : ℝ) ^ 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    calc Real.sqrt δ ≤ Real.sqrt ((ε / 512 : ℝ) ^ 2) := Real.sqrt_le_sqrt h
      _ = ε / 512 := Real.sqrt_sq (by positivity)
  refine ⟨D, hD5, hDM, le_trans key (by linarith), ?_, ?_, ?_, ?_⟩
  · refine le_trans (hmono _ ?_) (by linarith)
    have h5 : 5 * D ≤ D * D := Nat.mul_le_mul_right D hD5
    have hsq : D ^ 2 = D * D := sq D
    omega
  · have h : a ^ (5 * D - 2) ≤ δ := hmono _ (by omega)
    linarith
  · have h : qBound a D ≤ 1 / 160000 := le_trans hqle hs1
    linarith
  · have h : qBound a D ≤ ε / 512 := le_trans hqle hs2
    linarith

/-- **`eq:d0-conditions` hold at every large scale**: each condition is a bound
on a power of `a < 1`, so all of them hold past one threshold `D₀(a)`. -/
theorem forall_scale {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → 5 ≤ D ∧
      a ^ (D - 1) ≤ 1 / 10 ∧ a ^ (D ^ 2 - D) ≤ 1 / 2 ∧
      36 * a ^ (5 * D - 2) ≤ 1 ∧ 16 * qBound a D ≤ 1 / 10000 := by
  set δ : ℝ := min (1 / 36) ((1 / 160000) ^ 2) with hδdef
  have hδ : 0 < δ := lt_min (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Filter.Tendsto.eventually_le_const hδ
      (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1))
  refine ⟨max 5 (N + 1), fun D hD ↦ ?_⟩
  have hD5 : 5 ≤ D := le_trans (le_max_left _ _) hD
  have hDN : N ≤ D - 1 := by
    have := le_trans (le_max_right 5 (N + 1)) hD
    omega
  have key : a ^ (D - 1) ≤ δ := hN (D - 1) hDN
  have h36 : δ ≤ 1 / 36 := min_le_left _ _
  have hmono : ∀ m : ℕ, D - 1 ≤ m → a ^ m ≤ δ :=
    fun m hm ↦ le_trans (pow_le_pow_of_le_one ha0.le ha1.le hm) key
  have hqle : qBound a D ≤ Real.sqrt δ := by
    rw [qBound]
    refine Real.sqrt_le_sqrt (hmono _ ?_)
    calc D - 1 ≤ D * 1 := by omega
      _ ≤ D * (2 * D - 5) := Nat.mul_le_mul_left D (by omega)
  have hs1 : Real.sqrt δ ≤ 1 / 160000 := by
    have h : δ ≤ (1 / 160000 : ℝ) ^ 2 := min_le_right _ _
    calc Real.sqrt δ ≤ Real.sqrt ((1 / 160000 : ℝ) ^ 2) := Real.sqrt_le_sqrt h
      _ = 1 / 160000 := Real.sqrt_sq (by norm_num)
  refine ⟨hD5, le_trans key (by linarith), ?_, ?_, ?_⟩
  · refine le_trans (hmono _ ?_) (by linarith)
    have h5 : 5 * D ≤ D * D := Nat.mul_le_mul_right D hD5
    have hsq : D ^ 2 = D * D := sq D
    omega
  · have h : a ^ (5 * D - 2) ≤ δ := hmono _ (by omega)
    linarith
  · have h : qBound a D ≤ 1 / 160000 := le_trans hqle hs1
    linarith

end ChainClasses
