/-
`thm:double-exp` of `graph_matching_selfcontained.tex`, the double-exponential tail.
For `D ≥ 5` and the law `p_j = e^{-D^j}` (`j ≥ 1`), `p_0 = 1 - ∑_{j≥1} e^{-D^j}` on
the path graph, the full-matching failure probability is at most `16 η_{𝖯,α}(p)`, with

    η_{𝖯,α}(p) ≤ 4 e^{-D(D-5/2)} < 10⁻⁴.

The sequence `a_j = e^{-D^j}` has ratio `≤ e^{-20} < 1/2` from index 1 on, so all
tail sums are geometric (`dseq_tail_le`, via `geo_tail`). The good degree `s_j` is
`> 1/2` at `j = 0,1` and `≥ a_{j-1}` beyond; the bad degree tails are `∑_{k≥2} a_k`
and `∑_{k≥3} a_k` (`badDeg_zero`/`badDeg_one`). Writing `η_{𝖯,α} = ofReal(∑_j T_j)`
(`etaP_eq`), the three contributions `T_0 ≤ 12 e^{-D^2} ≤ β`, `T_1 ≤ 12 e^{-(D+D^3)}
≤ β`, `∑_{j≥2} T_j ≤ 2β` sum to `4β`, and `4β < 10⁻⁴` since `e^{12} > 40000`
(`exp_twelve_gt`).
-/
import GraphMatching.Examples
import Mathlib.Analysis.Complex.ExponentialBounds

namespace GraphMatching
open scoped ENNReal Classical
open Real

/-! ### The double-exponential sequence -/

/-- `a_j = e^{-D^j}`. -/
noncomputable def dseq (D : ℝ) (j : ℕ) : ℝ := Real.exp (-(D ^ j))

lemma dseq_pos (D : ℝ) (j : ℕ) : 0 < dseq D j := Real.exp_pos _

/-- `e^{-x} ≤ 1/2` once `x ≥ 20`. -/
lemma exp_neg_le_half {x : ℝ} (hx : 20 ≤ x) : Real.exp (-x) ≤ 1 / 2 := by
  have he : (2 : ℝ) ≤ Real.exp x := by have := Real.add_one_le_exp x; linarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) he

/-- The consecutive ratio is at most `1/2` from index `1` on. -/
lemma dseq_ratio {D : ℝ} (hD : 5 ≤ D) (k : ℕ) (hk : 1 ≤ k) :
    dseq D (k + 1) ≤ (1 / 2) * dseq D k := by
  have hexp : dseq D (k + 1) = dseq D k * Real.exp (-(D ^ (k + 1) - D ^ k)) := by
    rw [dseq, dseq, ← Real.exp_add]; congr 1; ring
  have hDk : D ≤ D ^ k := by
    calc D = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ k := pow_le_pow_right₀ (by linarith) hk
  have hge : (20 : ℝ) ≤ D ^ (k + 1) - D ^ k := by
    have h : D ^ (k + 1) - D ^ k = D ^ k * (D - 1) := by ring
    rw [h]
    nlinarith [hDk, mul_nonneg (show (0:ℝ) ≤ D ^ k - D by linarith) (show (0:ℝ) ≤ D - 1 by linarith)]
  rw [hexp]
  nlinarith [(dseq_pos D k), exp_neg_le_half hge, Real.exp_pos (-(D ^ (k + 1) - D ^ k))]

/-- Tail sum bound: `∑_{n} a_{n+m} ≤ 2 a_m` for `m ≥ 1`. -/
lemma dseq_tail_le {D : ℝ} (hD : 5 ≤ D) (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun n => dseq D (n + m)) ∧ ∑' n, dseq D (n + m) ≤ 2 * dseq D m := by
  have h := geo_tail (c := fun n => dseq D (n + m)) (fun n => (dseq_pos D _).le)
    (fun n => by
      show dseq D (n + 1 + m) ≤ 1 / 2 * dseq D (n + m)
      rw [show n + 1 + m = n + m + 1 from by omega]
      exact dseq_ratio hD (n + m) (by omega))
  simpa using h

/-! ### The `exp` numerics -/

lemma exp_five_gt : (20 : ℝ) < Real.exp 5 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]; nlinarith [h1, pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h1 5]

lemma exp_twelve_gt : (40000 : ℝ) < Real.exp 12 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : Real.exp 12 = Real.exp 1 ^ 12 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  calc (40000 : ℝ) < 2.7 ^ 12 := by norm_num
    _ ≤ Real.exp 1 ^ 12 := by
        apply pow_le_pow_left₀ (by norm_num) h1.le

/-! ### The double-exponential law -/

/-- `S = ∑_{j≥1} a_j`. -/
noncomputable def dsum (D : ℝ) : ℝ := ∑' n, dseq D (n + 1)

lemma dsum_nonneg (D : ℝ) : 0 ≤ dsum D := tsum_nonneg (fun n => (dseq_pos D (n + 1)).le)

lemma dsum_lt {D : ℝ} (hD : 5 ≤ D) : dsum D < 1 / 10 := by
  have hexpD : (20 : ℝ) < Real.exp D := lt_of_lt_of_le exp_five_gt (Real.exp_le_exp.mpr (by linarith))
  have hd1 : dseq D 1 < 1 / 20 := by
    rw [dseq, pow_one, Real.exp_neg, inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hexpD
  calc dsum D ≤ 2 * dseq D 1 := (dseq_tail_le hD 1 le_rfl).2
    _ < 2 * (1 / 20) := by linarith
    _ = 1 / 10 := by norm_num

/-- The mass function of the double-exponential law. -/
noncomputable def dexpF (D : ℝ) : ℕ → ℝ≥0∞ :=
  fun n => if n = 0 then ENNReal.ofReal (1 - dsum D) else ENNReal.ofReal (dseq D n)

lemma dexpF_tsum {D : ℝ} (hD : 5 ≤ D) : ∑' n, dexpF D n = 1 := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  have h0 : dexpF D 0 = ENNReal.ofReal (1 - dsum D) := ite_eq_left rfl
  have hs : ∀ n, dexpF D (n + 1) = ENNReal.ofReal (dseq D (n + 1)) := fun n => ite_eq_right (by omega)
  rw [h0]
  simp only [hs]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (dseq_pos D _).le) (dseq_tail_le hD 1 le_rfl).1,
    show (∑' n, dseq D (n + 1)) = dsum D from rfl,
    ← ENNReal.ofReal_add (by linarith [dsum_lt hD]) (dsum_nonneg D),
    show (1 - dsum D) + dsum D = 1 from by ring, ENNReal.ofReal_one]

/-- The double-exponential law `p` as a `PMF ℕ`. -/
noncomputable def dexpPMF {D : ℝ} (hD : 5 ≤ D) : PMF ℕ :=
  ⟨dexpF D, by have := ENNReal.summable.hasSum (f := dexpF D); rwa [dexpF_tsum hD] at this⟩

lemma dexpPMF_apply {D : ℝ} (hD : 5 ≤ D) (n : ℕ) : dexpPMF hD n = dexpF D n := rfl

lemma dexpPMF_zero_toReal {D : ℝ} (hD : 5 ≤ D) : (dexpPMF hD 0).toReal = 1 - dsum D := by
  rw [dexpPMF_apply, dexpF, ite_eq_left rfl, ENNReal.toReal_ofReal (by linarith [dsum_lt hD])]

lemma dexpPMF_succ_toReal {D : ℝ} (hD : 5 ≤ D) (n : ℕ) :
    (dexpPMF hD (n + 1)).toReal = dseq D (n + 1) := by
  rw [dexpPMF_apply, dexpF, ite_eq_right (by omega), ENNReal.toReal_ofReal (dseq_pos D _).le]

/-! ### The good and bad degrees -/

/-- The mass at a compatible vertex is below the good degree. -/
lemma p_toReal_le_gdeg {W : Type*} (μ : PMF W) (G : SimpleGraph W) {v w : W}
    (h : compat G v w) : (μ w).toReal ≤ gdeg μ G v := by
  have hle : μ w ≤ rE μ (compat G) v := by
    rw [rE]
    calc μ w = if compat G v w then μ w else 0 := (ite_eq_left h).symm
      _ ≤ ∑' k, if compat G v k then μ k else 0 :=
          ENNReal.le_tsum (f := fun k => if compat G v k then μ k else 0) w
  exact ENNReal.toReal_mono rE_ne_top hle

/-- Bad degree at `0`: the mass beyond the ball `{0,1}` is `∑_{k≥2} a_k`. -/
lemma badDeg_zero {D : ℝ} (hD : 5 ≤ D) :
    qE (dexpPMF hD) (compat pathGraph) 0 = ENNReal.ofReal (∑' k, dseq D (k + 2)) := by
  rw [qE, tsum_eq_zero_add' ENNReal.summable, tsum_eq_zero_add' ENNReal.summable]
  have e0 : (if compat pathGraph 0 0 then (0 : ℝ≥0∞) else dexpPMF hD 0) = 0 := ite_eq_left (Or.inl rfl)
  have e1 : (if compat pathGraph 0 (0 + 1) then (0 : ℝ≥0∞) else dexpPMF hD (0 + 1)) = 0 :=
    ite_eq_left (Or.inr (by rw [pathGraph_adj]; omega))
  have e2 : ∀ k, (if compat pathGraph 0 (k + 1 + 1) then (0 : ℝ≥0∞) else dexpPMF hD (k + 1 + 1))
      = ENNReal.ofReal (dseq D (k + 2)) := by
    intro k
    have hnc : ¬ compat pathGraph 0 (k + 1 + 1) := by
      rintro (h | h)
      · omega
      · rw [pathGraph_adj] at h; omega
    rw [ite_eq_right hnc, dexpPMF_apply, dexpF, ite_eq_right (by omega)]
  rw [e0, e1, zero_add, zero_add]
  simp only [e2]
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => (dseq_pos D _).le) (dseq_tail_le hD 2 (by norm_num)).1]

/-- Bad degree at `1`: the mass beyond the ball `{0,1,2}` is `∑_{k≥3} a_k`. -/
lemma badDeg_one {D : ℝ} (hD : 5 ≤ D) :
    qE (dexpPMF hD) (compat pathGraph) 1 = ENNReal.ofReal (∑' k, dseq D (k + 3)) := by
  rw [qE, tsum_eq_zero_add' ENNReal.summable, tsum_eq_zero_add' ENNReal.summable,
    tsum_eq_zero_add' ENNReal.summable]
  have e0 : (if compat pathGraph 1 0 then (0 : ℝ≥0∞) else dexpPMF hD 0) = 0 :=
    ite_eq_left (Or.inr (by rw [pathGraph_adj]; omega))
  have e1 : (if compat pathGraph 1 (0 + 1) then (0 : ℝ≥0∞) else dexpPMF hD (0 + 1)) = 0 :=
    ite_eq_left (Or.inl rfl)
  have e2 : (if compat pathGraph 1 (0 + 1 + 1) then (0 : ℝ≥0∞) else dexpPMF hD (0 + 1 + 1)) = 0 :=
    ite_eq_left (Or.inr (by rw [pathGraph_adj]; omega))
  have e3 : ∀ k,
      (if compat pathGraph 1 (k + 1 + 1 + 1) then (0 : ℝ≥0∞) else dexpPMF hD (k + 1 + 1 + 1))
        = ENNReal.ofReal (dseq D (k + 3)) := by
    intro k
    have hnc : ¬ compat pathGraph 1 (k + 1 + 1 + 1) := by
      rintro (h | h)
      · omega
      · rw [pathGraph_adj] at h; omega
    rw [ite_eq_right hnc, dexpPMF_apply, dexpF, ite_eq_right (by omega)]
  rw [e0, e1, e2, zero_add, zero_add, zero_add]
  simp only [e3]
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => (dseq_pos D _).le) (dseq_tail_le hD 3 (by norm_num)).1]

/-! ### The good degree of the double-exponential law -/

lemma gdeg_zero_gt {D : ℝ} (hD : 5 ≤ D) : 1 / 2 < gdeg (dexpPMF hD) pathGraph 0 := by
  have h := p_toReal_le_gdeg (dexpPMF hD) pathGraph (compat_refl pathGraph 0)
  rw [dexpPMF_zero_toReal] at h
  linarith [dsum_lt hD]

lemma gdeg_one_gt {D : ℝ} (hD : 5 ≤ D) : 1 / 2 < gdeg (dexpPMF hD) pathGraph 1 := by
  have h := p_toReal_le_gdeg (dexpPMF hD) pathGraph (v := 1) (w := 0)
    (Or.inr (by rw [pathGraph_adj]; omega))
  rw [dexpPMF_zero_toReal] at h
  linarith [dsum_lt hD]

lemma one_sub_gdeg_zero {D : ℝ} (hD : 5 ≤ D) :
    1 - gdeg (dexpPMF hD) pathGraph 0 = ∑' k, dseq D (k + 2) := by
  rw [one_sub_gdeg, badDeg_zero, ENNReal.toReal_ofReal (tsum_nonneg (fun k => (dseq_pos D _).le))]

lemma one_sub_gdeg_one {D : ℝ} (hD : 5 ≤ D) :
    1 - gdeg (dexpPMF hD) pathGraph 1 = ∑' k, dseq D (k + 3) := by
  rw [one_sub_gdeg, badDeg_one, ENNReal.toReal_ofReal (tsum_nonneg (fun k => (dseq_pos D _).le))]

/-- `1/6 ≤ (1/2)^{5/2}`, so `s^{-5/2} ≤ 6` once `s > 1/2`. -/
lemma one_sixth_le_half_rpow : (1 : ℝ) / 6 ≤ (1 / 2 : ℝ) ^ alpha := by
  rw [rpow_alpha_eq_sqrt_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsqrt : (2 : ℝ) / 3 ≤ Real.sqrt (1 / 2) := by
    rw [show (2:ℝ)/3 = Real.sqrt ((2/3)^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsq : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hpow5 : Real.sqrt (1 / 2) ^ 5 = (1 / 4) * Real.sqrt (1 / 2) := by
    have : Real.sqrt (1 / 2) ^ 5 = (Real.sqrt (1 / 2) ^ 2) ^ 2 * Real.sqrt (1 / 2) := by ring
    rw [this, hsq]; ring
  rw [hpow5]; nlinarith [hsqrt, Real.sqrt_nonneg (1 / 2 : ℝ)]

/-- The inverse `α`-power bound from `s > 1/2`. -/
lemma inv_rpow_le_six {s : ℝ} (hs : 1 / 2 < s) : 1 / s ^ alpha ≤ 6 := by
  have h1 : (1 / 2 : ℝ) ^ alpha ≤ s ^ alpha := Real.rpow_le_rpow (by norm_num) hs.le alpha_nonneg
  have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ alpha := Real.rpow_pos_of_pos (by norm_num) alpha
  have h6 : (1 : ℝ) / 6 ≤ s ^ alpha := le_trans one_sixth_le_half_rpow h1
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) h6)]
  nlinarith [h6]

/-! ### The term bounds -/

/-- The real summand of `η_{𝖯,α}`: `T_j = p_j (1-s_j)/s_j^{5/2}`. -/
noncomputable def dTerm {D : ℝ} (hD : 5 ≤ D) (j : ℕ) : ℝ :=
  (dexpPMF hD j).toReal *
    ((1 - gdeg (dexpPMF hD) pathGraph j) / gdeg (dexpPMF hD) pathGraph j ^ alpha)

lemma gdeg_pos_dexp {D : ℝ} (hD : 5 ≤ D) (j : ℕ) : 0 < gdeg (dexpPMF hD) pathGraph j := by
  refine lt_of_lt_of_le ?_ (p_toReal_le_gdeg (dexpPMF hD) pathGraph (compat_refl pathGraph j))
  rcases j with _ | n
  · rw [dexpPMF_zero_toReal]; linarith [dsum_lt hD]
  · rw [dexpPMF_succ_toReal]; exact dseq_pos D _

lemma dTerm_nonneg {D : ℝ} (hD : 5 ≤ D) (j : ℕ) : 0 ≤ dTerm hD j := by
  have h1 : (0 : ℝ) ≤ 1 - gdeg (dexpPMF hD) pathGraph j := by
    have := mu_toReal_le_one (dexpPMF hD) j
    have h2 : gdeg (dexpPMF hD) pathGraph j ≤ 1 := by
      rw [gdeg]; exact ENNReal.toReal_mono ENNReal.one_ne_top rE_le_one
    linarith
  have h3 : 0 < gdeg (dexpPMF hD) pathGraph j ^ alpha :=
    Real.rpow_pos_of_pos (gdeg_pos_dexp hD j) alpha
  exact mul_nonneg ENNReal.toReal_nonneg (div_nonneg h1 h3.le)

lemma dTerm_zero_le {D : ℝ} (hD : 5 ≤ D) : dTerm hD 0 ≤ 12 * dseq D 2 := by
  have hp : (dexpPMF hD 0).toReal ≤ 1 := mu_toReal_le_one _ 0
  have hs0a : 0 < gdeg (dexpPMF hD) pathGraph 0 ^ alpha :=
    Real.rpow_pos_of_pos (gdeg_pos_dexp hD 0) alpha
  have hinv : 1 / gdeg (dexpPMF hD) pathGraph 0 ^ alpha ≤ 6 := inv_rpow_le_six (gdeg_zero_gt hD)
  have hsublt : 1 - gdeg (dexpPMF hD) pathGraph 0 ≤ 2 * dseq D 2 := by
    rw [one_sub_gdeg_zero hD]; exact (dseq_tail_le hD 2 (by norm_num)).2
  have hsubnn : 0 ≤ 1 - gdeg (dexpPMF hD) pathGraph 0 := by
    rw [one_sub_gdeg_zero hD]; exact tsum_nonneg (fun k => (dseq_pos D _).le)
  have hd2 : 0 ≤ dseq D 2 := (dseq_pos D 2).le
  have hXnn : 0 ≤ (1 - gdeg (dexpPMF hD) pathGraph 0) * (1 / gdeg (dexpPMF hD) pathGraph 0 ^ alpha) :=
    mul_nonneg hsubnn (one_div_pos.mpr hs0a).le
  have hXle : (1 - gdeg (dexpPMF hD) pathGraph 0) * (1 / gdeg (dexpPMF hD) pathGraph 0 ^ alpha)
      ≤ 2 * dseq D 2 * 6 :=
    mul_le_mul hsublt hinv (one_div_pos.mpr hs0a).le (by linarith)
  rw [dTerm, div_eq_mul_one_div]
  nlinarith [ENNReal.toReal_nonneg (a := dexpPMF hD 0), hp, hXnn, hXle, hd2,
    mul_nonneg (by linarith [hp] : (0:ℝ) ≤ 1 - (dexpPMF hD 0).toReal) hXnn]

lemma dTerm_one_le {D : ℝ} (hD : 5 ≤ D) : dTerm hD 1 ≤ 12 * (dseq D 1 * dseq D 3) := by
  have hp : (dexpPMF hD 1).toReal = dseq D 1 := dexpPMF_succ_toReal hD 0
  have hp1 : 0 ≤ dseq D 1 := (dseq_pos D 1).le
  have hs1a : 0 < gdeg (dexpPMF hD) pathGraph 1 ^ alpha :=
    Real.rpow_pos_of_pos (gdeg_pos_dexp hD 1) alpha
  have hinv : 1 / gdeg (dexpPMF hD) pathGraph 1 ^ alpha ≤ 6 := inv_rpow_le_six (gdeg_one_gt hD)
  have hsublt : 1 - gdeg (dexpPMF hD) pathGraph 1 ≤ 2 * dseq D 3 := by
    rw [one_sub_gdeg_one hD]; exact (dseq_tail_le hD 3 (by norm_num)).2
  have hsubnn : 0 ≤ 1 - gdeg (dexpPMF hD) pathGraph 1 := by
    rw [one_sub_gdeg_one hD]; exact tsum_nonneg (fun k => (dseq_pos D _).le)
  have hd3 : 0 ≤ dseq D 3 := (dseq_pos D 3).le
  have hXle : (1 - gdeg (dexpPMF hD) pathGraph 1) * (1 / gdeg (dexpPMF hD) pathGraph 1 ^ alpha)
      ≤ 2 * dseq D 3 * 6 :=
    mul_le_mul hsublt hinv (one_div_pos.mpr hs1a).le (by linarith)
  rw [dTerm, div_eq_mul_one_div, hp]
  nlinarith [hp1, hXle,
    mul_nonneg hsubnn (one_div_pos.mpr hs1a).le]

/-- The tail-bound sequence `u_j = e^{-(D-5/2)D^{j+1}}`. -/
noncomputable def ubound (D : ℝ) (j : ℕ) : ℝ := Real.exp (-((D - 5 / 2) * D ^ (j + 1)))

lemma ubound_eq (D : ℝ) (j : ℕ) :
    dseq D (j + 2) / dseq D (j + 1) ^ alpha = ubound D j := by
  have hpow : dseq D (j + 1) ^ alpha = Real.exp (-D ^ (j + 1) * alpha) := by
    rw [dseq, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  rw [ubound, dseq, hpow, ← Real.exp_sub]
  congr 1
  rw [show D ^ (j + 2) = D * D ^ (j + 1) from by ring, alpha]; ring

lemma dTerm_tail_le {D : ℝ} (hD : 5 ≤ D) (j : ℕ) : dTerm hD (j + 2) ≤ ubound D j := by
  rw [← ubound_eq]
  have hpj : (dexpPMF hD (j + 2)).toReal = dseq D (j + 2) := dexpPMF_succ_toReal hD (j + 1)
  have hlow : dseq D (j + 1) ≤ gdeg (dexpPMF hD) pathGraph (j + 2) := by
    have h := p_toReal_le_gdeg (dexpPMF hD) pathGraph (v := j + 2) (w := j + 1)
      (Or.inr (by rw [pathGraph_adj]; omega))
    rwa [dexpPMF_succ_toReal hD j] at h
  have hd1pos : 0 < dseq D (j + 1) := dseq_pos D _
  have hgpow : dseq D (j + 1) ^ alpha ≤ gdeg (dexpPMF hD) pathGraph (j + 2) ^ alpha :=
    Real.rpow_le_rpow hd1pos.le hlow alpha_nonneg
  have hd1powpos : 0 < dseq D (j + 1) ^ alpha := Real.rpow_pos_of_pos hd1pos alpha
  have hsubnn : 0 ≤ 1 - gdeg (dexpPMF hD) pathGraph (j + 2) := by
    have h2 : gdeg (dexpPMF hD) pathGraph (j + 2) ≤ 1 := by
      rw [gdeg]; exact ENNReal.toReal_mono ENNReal.one_ne_top rE_le_one
    linarith
  have hsub1 : 1 - gdeg (dexpPMF hD) pathGraph (j + 2) ≤ 1 := by
    linarith [gdeg_pos_dexp hD (j + 2)]
  rw [dTerm, hpj]
  have hs2α : 0 < gdeg (dexpPMF hD) pathGraph (j + 2) ^ alpha :=
    Real.rpow_pos_of_pos (gdeg_pos_dexp hD (j + 2)) alpha
  have hquot : (1 - gdeg (dexpPMF hD) pathGraph (j + 2)) / gdeg (dexpPMF hD) pathGraph (j + 2) ^ alpha
      ≤ 1 / dseq D (j + 1) ^ alpha := by
    calc (1 - gdeg (dexpPMF hD) pathGraph (j + 2)) / gdeg (dexpPMF hD) pathGraph (j + 2) ^ alpha
        = (1 - gdeg (dexpPMF hD) pathGraph (j + 2)) * (1 / gdeg (dexpPMF hD) pathGraph (j + 2) ^ alpha) :=
          div_eq_mul_one_div _ _
      _ ≤ 1 * (1 / gdeg (dexpPMF hD) pathGraph (j + 2) ^ alpha) :=
          mul_le_mul_of_nonneg_right hsub1 (one_div_nonneg.mpr hs2α.le)
      _ = 1 / gdeg (dexpPMF hD) pathGraph (j + 2) ^ alpha := one_mul _
      _ ≤ 1 / dseq D (j + 1) ^ alpha := one_div_le_one_div_of_le hd1powpos hgpow
  have hdnn : 0 ≤ dseq D (j + 2) := (dseq_pos D _).le
  calc dseq D (j + 2)
        * ((1 - gdeg (dexpPMF hD) pathGraph (j + 2)) / gdeg (dexpPMF hD) pathGraph (j + 2) ^ alpha)
      ≤ dseq D (j + 2) * (1 / dseq D (j + 1) ^ alpha) := by
        apply mul_le_mul_of_nonneg_left hquot hdnn
    _ = dseq D (j + 2) / dseq D (j + 1) ^ alpha := by rw [mul_one_div]

/-! ### Assembling the bound -/

lemma ubound_pos (D : ℝ) (j : ℕ) : 0 < ubound D j := Real.exp_pos _

lemma ubound_ratio {D : ℝ} (hD : 5 ≤ D) (j : ℕ) : ubound D (j + 1) ≤ (1 / 2) * ubound D j := by
  have hexp : ubound D (j + 1)
      = ubound D j * Real.exp (-((D - 5 / 2) * (D ^ (j + 2) - D ^ (j + 1)))) := by
    rw [ubound, ubound, ← Real.exp_add]; congr 1; ring
  have hDk : D ≤ D ^ (j + 1) := by
    calc D = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ (j + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have h20 : (20 : ℝ) ≤ D ^ (j + 1) * (D - 1) := by
    nlinarith [hDk, mul_nonneg (show (0:ℝ) ≤ D ^ (j + 1) - D by linarith)
      (show (0:ℝ) ≤ D - 1 by linarith)]
  have hge : (20 : ℝ) ≤ (D - 5 / 2) * (D ^ (j + 2) - D ^ (j + 1)) := by
    rw [show D ^ (j + 2) - D ^ (j + 1) = D ^ (j + 1) * (D - 1) from by ring]
    nlinarith [mul_le_mul (show (5:ℝ)/2 ≤ D - 5/2 by linarith) h20 (by norm_num) (by linarith)]
  rw [hexp]
  nlinarith [ubound_pos D j, exp_neg_le_half hge,
    Real.exp_pos (-((D - 5 / 2) * (D ^ (j + 2) - D ^ (j + 1))))]

lemma ubound_tail {D : ℝ} (hD : 5 ≤ D) :
    Summable (ubound D) ∧ ∑' j, ubound D j ≤ 2 * ubound D 0 :=
  geo_tail (fun n => (ubound_pos D n).le) (fun n => ubound_ratio hD n)

lemma summable_dTerm {D : ℝ} (hD : 5 ≤ D) : Summable (dTerm hD) := by
  rw [← summable_nat_add_iff 2]
  exact Summable.of_nonneg_of_le (fun j => dTerm_nonneg hD (j + 2)) (fun j => dTerm_tail_le hD j)
    (ubound_tail hD).1

lemma etaP_eq {D : ℝ} (hD : 5 ≤ D) :
    etaP (dexpPMF hD) = ENNReal.ofReal (∑' j, dTerm hD j) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun j => dTerm_nonneg hD j) (summable_dTerm hD), etaP, etaG]
  refine tsum_congr fun j => ?_
  rw [dTerm, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ((dexpPMF hD).apply_ne_top j)]

/-- `12 e^{-D^2} ≤ β`. -/
lemma dseq_two_le_ubound {D : ℝ} (hD : 5 ≤ D) : 12 * dseq D 2 ≤ ubound D 0 := by
  have h12 : (12 : ℝ) ≤ Real.exp ((5 / 2) * D) := by
    have := Real.add_one_le_exp ((5 / 2) * D); nlinarith [this, hD]
  have heq : ubound D 0 = dseq D 2 * Real.exp ((5 / 2) * D) := by
    rw [ubound, dseq, ← Real.exp_add]; congr 1
    simp only [pow_succ, pow_zero, one_mul]; ring
  rw [heq]; nlinarith [dseq_pos D 2, h12]

/-- `12 e^{-(D+D^3)} ≤ β`. -/
lemma dseq_prod_le_ubound {D : ℝ} (hD : 5 ≤ D) :
    12 * (dseq D 1 * dseq D 3) ≤ ubound D 0 := by
  have hprod : dseq D 1 * dseq D 3 = Real.exp (-(D + D ^ 3)) := by
    rw [dseq, dseq, ← Real.exp_add]; congr 1; rw [pow_one]; ring
  have h12 : (12 : ℝ) ≤ Real.exp (D ^ 3 - D ^ 2 + (7 / 2) * D) := by
    have := Real.add_one_le_exp (D ^ 3 - D ^ 2 + (7 / 2) * D)
    nlinarith [this, hD, mul_nonneg (show (0:ℝ) ≤ D - 5 by linarith) (sq_nonneg D)]
  have heq : ubound D 0 = Real.exp (-(D + D ^ 3)) * Real.exp (D ^ 3 - D ^ 2 + (7 / 2) * D) := by
    rw [ubound, ← Real.exp_add]; congr 1
    simp only [pow_succ, pow_zero, one_mul]; ring
  rw [hprod, heq]; nlinarith [Real.exp_pos (-(D + D ^ 3)), h12]

lemma etaP_le {D : ℝ} (hD : 5 ≤ D) :
    etaP (dexpPMF hD) ≤ ENNReal.ofReal (4 * ubound D 0) := by
  rw [etaP_eq hD]
  apply ENNReal.ofReal_le_ofReal
  have hpeel : ∑' j, dTerm hD j = dTerm hD 0 + (dTerm hD 1 + ∑' j, dTerm hD (j + 2)) := by
    rw [(summable_dTerm hD).tsum_eq_zero_add,
      ((summable_nat_add_iff 1).mpr (summable_dTerm hD)).tsum_eq_zero_add]
  have htail : ∑' j, dTerm hD (j + 2) ≤ 2 * ubound D 0 :=
    le_trans (Summable.tsum_le_tsum (fun j => dTerm_tail_le hD j)
      ((summable_nat_add_iff 2).mpr (summable_dTerm hD)) (ubound_tail hD).1) (ubound_tail hD).2
  have hb0 : dTerm hD 0 ≤ ubound D 0 := le_trans (dTerm_zero_le hD) (dseq_two_le_ubound hD)
  have hb1 : dTerm hD 1 ≤ ubound D 0 := le_trans (dTerm_one_le hD) (dseq_prod_le_ubound hD)
  rw [hpeel]; linarith [hb0, hb1, htail]

lemma four_ubound_lt {D : ℝ} (hD : 5 ≤ D) : 4 * ubound D 0 < 1 / 10000 := by
  have heq : ubound D 0 = Real.exp (-(D ^ 2 - (5 / 2) * D)) := by
    rw [ubound]; congr 1; simp only [pow_succ, pow_zero, one_mul]; ring
  have hge : (12 : ℝ) ≤ D ^ 2 - (5 / 2) * D := by
    nlinarith [hD, mul_nonneg (show (0:ℝ) ≤ D - 5 by linarith) (show (0:ℝ) ≤ D by linarith)]
  have hexpge : (40000 : ℝ) < Real.exp (D ^ 2 - (5 / 2) * D) :=
    lt_of_lt_of_le exp_twelve_gt (Real.exp_le_exp.mpr hge)
  rw [heq, Real.exp_neg]
  have hinv : (Real.exp (D ^ 2 - (5 / 2) * D))⁻¹ < 1 / 40000 := by
    rw [inv_eq_one_div]; exact one_div_lt_one_div_of_lt (by norm_num) hexpge
  nlinarith [hinv, Real.exp_pos (D ^ 2 - (5 / 2) * D)]

/-- **`thm:double-exp`** (double-exponential tail): for the law `p_j = e^{-D^j}` on the
path graph with `D ≥ 5`, the full matching failure probability is at most
`16 η_{𝖯,α}(p)`, and `η_{𝖯,α}(p) ≤ 4 e^{-D(D-5/2)} < 10⁻⁴` (`eq:eta-double`). -/
theorem double_exp_matching {D : ℝ} (hD : 5 ≤ D) (h : ℕ) :
    ∑' x, fullMu (dexpPMF hD) h x * qE (fullMu (dexpPMF hD) h) (fullSim (compat pathGraph) h) x
      ≤ 16 * etaP (dexpPMF hD) := by
  refine path_full_matching_bound (dexpPMF hD) ?_ h
  have h1 : etaP (dexpPMF hD) ≤ ENNReal.ofReal (4 * ubound D 0) := etaP_le hD
  have h2 : ENNReal.ofReal (4 * ubound D 0) ≤ 1 / 10000 := by
    rw [show (1 : ℝ≥0∞) / 10000 = ENNReal.ofReal (1 / 10000) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]]
    exact ENNReal.ofReal_le_ofReal (four_ubound_lt hD).le
  exact le_trans h1 h2

end GraphMatching
