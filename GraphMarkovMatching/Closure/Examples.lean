/-
The two label-law examples of `arbitrary_offspring_matching.tex`
(`thm:exponential`, `thm:doubleexp`), certified against the general
matching theorem.  Self-contained: the path relation, the
double-exponential toolkit, and both potential bounds are developed
here against the library's own degrees `qE`/`rE` and the safe `phiE`
convention.

* `pathCompat`: the nearest-neighbour relation on the half-line.
* `exp3PMF`: the exponential three-label law `p₁ = e^{-D}`,
  `p₂ = e^{-D²}`, `p₀` the remainder, on the path `0 - 1 - 2`;
  `exp3_etaG_le`: `η ≤ 9 e^{-(D-5/2)D}` for `D ≥ 5`.
* `dexpPMF`: the double-exponential law on the half-line,
  `p_k = e^{-D^k}` (`k ≥ 1`), `p₀` the remainder;
  `dexp_etaG_le`: `η(α) ≤ 4 e^{-(D-α)D}` for `D ≥ max(5, α+1)` (the
  two root rows are bounded by `2^{α+1} e^{-D²} ≤ e^{-(D-α)D}`, the
  remaining rows by the geometric tail of `u_j = e^{-(D-α)D^{j+1}}`).
* `varying_exp3_failure_le` / `varying_exp3_matching_le` and
  `varying_doubleExp_failure_le` / `varying_doubleExp_matching_le`:
  `varying_failure_le` and `varying_matching_le` instantiated at the
  two laws, with the potential replaced by its certified budget.
-/
import GraphMarkovMatching.Closure.Numeric

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

/-! ### The path relation on `ℕ` -/

/-- The nearest-neighbour compatibility relation on the half-line:
`j ∼ k` iff `|j - k| ≤ 1`. -/
def pathCompat (j k : ℕ) : Prop := j = k ∨ j + 1 = k ∨ k + 1 = j

lemma pathCompat_iff {j k : ℕ} :
    pathCompat j k ↔ j = k ∨ j + 1 = k ∨ k + 1 = j := Iff.rfl

lemma pathCompat_refl : ∀ v, pathCompat v v := fun _ => Or.inl rfl

lemma pathCompat_symm : ∀ a b, pathCompat a b → pathCompat b a := by
  intro a b h
  unfold pathCompat at h ⊢
  omega

/-! ### A geometric-tail tool -/

/-- A nonnegative sequence with ratio `≤ 1/2` is summable, with sum at
most twice its first term. -/
lemma geo_tail {c : ℕ → ℝ} (hnn : ∀ n, 0 ≤ c n)
    (hr : ∀ n, c (n + 1) ≤ (1 / 2) * c n) :
    Summable c ∧ ∑' n, c n ≤ 2 * c 0 := by
  have hbound : ∀ n, c n ≤ (1 / 2) ^ n * c 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc c (n + 1) ≤ (1 / 2) * c n := hr n
          _ ≤ (1 / 2) * ((1 / 2) ^ n * c 0) := by gcongr
          _ = (1 / 2) ^ (n + 1) * c 0 := by ring
  have hgeo : Summable (fun n => (1 / 2 : ℝ) ^ n * c 0) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hsum : Summable c := hgeo.of_nonneg_of_le hnn hbound
  refine ⟨hsum, ?_⟩
  calc ∑' n, c n ≤ ∑' n, (1 / 2 : ℝ) ^ n * c 0 :=
      Summable.tsum_le_tsum hbound hsum hgeo
    _ = (∑' n, (1 / 2 : ℝ) ^ n) * c 0 := tsum_mul_right
    _ = 2 * c 0 := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num

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
    nlinarith [hDk, mul_nonneg (show (0:ℝ) ≤ D ^ k - D by linarith)
      (show (0:ℝ) ≤ D - 1 by linarith)]
  rw [hexp]
  nlinarith [(dseq_pos D k), exp_neg_le_half hge,
    Real.exp_pos (-(D ^ (k + 1) - D ^ k))]

/-- Tail sum bound: `∑_n a_{n+m} ≤ 2 a_m` for `m ≥ 1`. -/
lemma dseq_tail_le {D : ℝ} (hD : 5 ≤ D) (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun n => dseq D (n + m)) ∧ ∑' n, dseq D (n + m) ≤ 2 * dseq D m := by
  have h := geo_tail (c := fun n => dseq D (n + m)) (fun n => (dseq_pos D _).le)
    (fun n => by
      show dseq D (n + 1 + m) ≤ 1 / 2 * dseq D (n + m)
      rw [show n + 1 + m = n + m + 1 from by omega]
      exact dseq_ratio hD (n + m) (by omega))
  simpa using h

lemma exp_five_gt : (20 : ℝ) < Real.exp 5 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]; nlinarith [h1, pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h1 5]

/-- `e^{-x} < 1/20` for `x ≥ 5`. -/
lemma exp_neg_lt_twentieth {x : ℝ} (hx : 5 ≤ x) :
    Real.exp (-x) < 1 / 20 := by
  have h1 : Real.exp (-x) ≤ Real.exp (-(5 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(5 : ℝ)) < 1 / 20 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) exp_five_gt
  linarith

/-! ### The double-exponential law -/

/-- `S = ∑_{j≥1} a_j`. -/
noncomputable def dsum (D : ℝ) : ℝ := ∑' n, dseq D (n + 1)

lemma dsum_nonneg (D : ℝ) : 0 ≤ dsum D :=
  tsum_nonneg (fun n => (dseq_pos D (n + 1)).le)

lemma dsum_lt {D : ℝ} (hD : 5 ≤ D) : dsum D < 1 / 10 := by
  have hd1 : dseq D 1 < 1 / 20 := by
    rw [dseq, pow_one]
    exact exp_neg_lt_twentieth hD
  calc dsum D ≤ 2 * dseq D 1 := (dseq_tail_le hD 1 le_rfl).2
    _ < 2 * (1 / 20) := by linarith
    _ = 1 / 10 := by norm_num

/-- The mass function of the double-exponential law. -/
noncomputable def dexpF (D : ℝ) : ℕ → ℝ≥0∞ :=
  fun n => if n = 0 then ENNReal.ofReal (1 - dsum D) else ENNReal.ofReal (dseq D n)

lemma dexpF_tsum {D : ℝ} (hD : 5 ≤ D) : ∑' n, dexpF D n = 1 := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  have h0 : dexpF D 0 = ENNReal.ofReal (1 - dsum D) := if_pos rfl
  have hs : ∀ n, dexpF D (n + 1) = ENNReal.ofReal (dseq D (n + 1)) :=
    fun n => if_neg (by omega)
  rw [h0]
  simp only [hs]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (dseq_pos D _).le)
      (dseq_tail_le hD 1 le_rfl).1,
    show (∑' n, dseq D (n + 1)) = dsum D from rfl,
    ← ENNReal.ofReal_add (by linarith [dsum_lt hD]) (dsum_nonneg D),
    show (1 - dsum D) + dsum D = 1 from by ring, ENNReal.ofReal_one]

/-- The double-exponential law on the half-line as a `PMF ℕ`. -/
noncomputable def dexpPMF {D : ℝ} (hD : 5 ≤ D) : PMF ℕ :=
  ⟨dexpF D, by
    have := ENNReal.summable.hasSum (f := dexpF D)
    rwa [dexpF_tsum hD] at this⟩

lemma dexpPMF_apply {D : ℝ} (hD : 5 ≤ D) (n : ℕ) :
    dexpPMF hD n = dexpF D n := rfl

lemma dexpPMF_zero_toReal {D : ℝ} (hD : 5 ≤ D) :
    (dexpPMF hD 0).toReal = 1 - dsum D := by
  rw [dexpPMF_apply, dexpF, if_pos rfl,
    ENNReal.toReal_ofReal (by linarith [dsum_lt hD])]

lemma dexpPMF_succ {D : ℝ} (hD : 5 ≤ D) {n : ℕ} (hn : 1 ≤ n) :
    dexpPMF hD n = ENNReal.ofReal (dseq D n) := by
  rw [dexpPMF_apply, dexpF, if_neg (by omega)]

lemma dexpPMF_succ_toReal {D : ℝ} (hD : 5 ≤ D) {n : ℕ} (hn : 1 ≤ n) :
    (dexpPMF hD n).toReal = dseq D n := by
  rw [dexpPMF_succ hD hn, ENNReal.toReal_ofReal (dseq_pos D _).le]

/-- The root carries most of the mass: `p₀ ≥ 9/10 ≥ 1/2`. -/
lemma dexp_half_le {D : ℝ} (hD : 5 ≤ D) : 2⁻¹ ≤ dexpPMF hD 0 := by
  refine (ENNReal.toReal_le_toReal (by norm_num)
    ((dexpPMF hD).apply_ne_top 0)).mp ?_
  rw [dexpPMF_zero_toReal hD, ENNReal.toReal_inv]
  have := dsum_lt hD
  norm_num
  linarith

/-! ### The tail budget -/

/-- The tail-bound sequence `u_j = e^{-(D-α)D^{j+1}}`. -/
noncomputable def ubound (α D : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-((D - α) * D ^ (j + 1)))

lemma ubound_pos (α D : ℝ) (j : ℕ) : 0 < ubound α D j := Real.exp_pos _

lemma ubound_eq (α D : ℝ) (j : ℕ) :
    dseq D (j + 2) / dseq D (j + 1) ^ α = ubound α D j := by
  have hpow : dseq D (j + 1) ^ α = Real.exp (-D ^ (j + 1) * α) := by
    rw [dseq, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  rw [ubound, dseq, hpow, ← Real.exp_sub]
  congr 1
  rw [show D ^ (j + 2) = D * D ^ (j + 1) from by ring]; ring

lemma ubound_ratio {α D : ℝ} (hD : 5 ≤ D) (hDα : α + 1 ≤ D) (j : ℕ) :
    ubound α D (j + 1) ≤ (1 / 2) * ubound α D j := by
  have hexp : ubound α D (j + 1)
      = ubound α D j * Real.exp (-((D - α) * (D ^ (j + 2) - D ^ (j + 1)))) := by
    rw [ubound, ubound, ← Real.exp_add]; congr 1; ring
  have hDk : D ≤ D ^ (j + 1) := by
    calc D = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ (j + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have h20 : (20 : ℝ) ≤ D ^ (j + 1) * (D - 1) := by
    nlinarith [hDk, mul_nonneg (show (0:ℝ) ≤ D ^ (j + 1) - D by linarith)
      (show (0:ℝ) ≤ D - 1 by linarith)]
  have hge : (20 : ℝ) ≤ (D - α) * (D ^ (j + 2) - D ^ (j + 1)) := by
    rw [show D ^ (j + 2) - D ^ (j + 1) = D ^ (j + 1) * (D - 1) from by ring]
    nlinarith [h20, mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ D - α by linarith)
      (by linarith : (0:ℝ) ≤ D ^ (j + 1) * (D - 1))]
  rw [hexp]
  nlinarith [(ubound_pos α D j), exp_neg_le_half hge,
    Real.exp_pos (-((D - α) * (D ^ (j + 2) - D ^ (j + 1))))]

lemma ubound_tail {α D : ℝ} (hD : 5 ≤ D) (hDα : α + 1 ≤ D) :
    Summable (ubound α D) ∧ ∑' j, ubound α D j ≤ 2 * ubound α D 0 :=
  geo_tail (fun n => (ubound_pos α D n).le) (fun n => ubound_ratio hD hDα n)

/-- `2^{α+1} ≤ e^{αD}`, the numeric step that absorbs the `2^α`
factors. -/
lemma two_rpow_le_exp {α D : ℝ} (hα1 : 1 ≤ α) (hD : 5 ≤ D) :
    (2 : ℝ) ^ (α + 1) ≤ Real.exp (α * D) := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlognn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : (2 : ℝ) ^ (α + 1) = Real.exp (Real.log 2 * (α + 1)) :=
    Real.rpow_def_of_pos (by norm_num) _
  rw [h1]
  apply Real.exp_le_exp.mpr
  have h2 : Real.log 2 * (α + 1) ≤ α + 1 := by nlinarith
  nlinarith

/-- The inverse `α`-power bound from `s > 1/2`: `1/s^α ≤ 2^α`. -/
lemma inv_rpow_le_two_rpow {α s : ℝ} (hα0 : 0 ≤ α) (hs : 1 / 2 < s) :
    1 / s ^ α ≤ (2 : ℝ) ^ α := by
  have h1 : ((1 : ℝ) / 2) ^ α ≤ s ^ α := Real.rpow_le_rpow (by norm_num) hs.le hα0
  have h2 : ((1 : ℝ) / 2) ^ α = ((2 : ℝ) ^ α)⁻¹ := by
    rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
  have h3 : (0 : ℝ) < ((1 : ℝ) / 2) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have h4 : (0 : ℝ) < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  rw [div_le_iff₀ (lt_of_lt_of_le h3 h1)]
  rw [h2] at h1
  calc (1 : ℝ) = (2 : ℝ) ^ α * ((2 : ℝ) ^ α)⁻¹ := (mul_inv_cancel₀ h4.ne').symm
    _ ≤ (2 : ℝ) ^ α * s ^ α := mul_le_mul_of_nonneg_left h1 h4.le

/-! ### The double-exponential degrees -/

/-- The two root rows have bad degree at most the geometric tail
`2 a₂`. -/
lemma dexp_q_le {D : ℝ} (hD : 5 ≤ D) {j : ℕ} (hj : j ≤ 1) :
    q (dexpPMF hD) pathCompat j ≤ 2 * dseq D 2 := by
  have hsub : (dexpPMF hD 0 + dexpPMF hD 1 : ℝ≥0∞)
      ≤ rE (dexpPMF hD) pathCompat j := by
    have h0 : pathCompat j 0 := by unfold pathCompat; omega
    have h1 : pathCompat j 1 := by unfold pathCompat; omega
    calc dexpPMF hD 0 + dexpPMF hD 1
        = ∑ y ∈ ({0, 1} : Finset ℕ),
            (if pathCompat j y then dexpPMF hD y else 0) := by
          rw [Finset.sum_insert (by decide), Finset.sum_singleton,
            if_pos h0, if_pos h1]
      _ ≤ ∑' y, (if pathCompat j y then dexpPMF hD y else 0) :=
          ENNReal.sum_le_tsum _
      _ = rE (dexpPMF hD) pathCompat j := by rw [rE]
  have hr : (1 - dsum D) + dseq D 1 ≤ (rE (dexpPMF hD) pathCompat j).toReal := by
    have := ENNReal.toReal_mono rE_ne_top hsub
    rwa [ENNReal.toReal_add ((dexpPMF hD).apply_ne_top 0)
        ((dexpPMF hD).apply_ne_top 1),
      dexpPMF_zero_toReal hD, dexpPMF_succ_toReal hD le_rfl] at this
  have hq : q (dexpPMF hD) pathCompat j
      = 1 - (rE (dexpPMF hD) pathCompat j).toReal := by
    have h := toReal_rE_add_toReal_qE (dexpPMF hD) pathCompat j
    rw [q]; linarith
  have hs1 := (dseq_tail_le hD 1 le_rfl).1
  have hpeel : dsum D = dseq D (0 + 1) + ∑' n, dseq D (n + 1 + 1) := by
    rw [dsum, hs1.tsum_eq_zero_add]
  have hshift : (∑' n, dseq D (n + 1 + 1)) = ∑' n, dseq D (n + 2) :=
    tsum_congr fun n => rfl
  have h2 := (dseq_tail_le hD 2 (by norm_num)).2
  have htail : dsum D - dseq D 1 ≤ 2 * dseq D 2 := by
    rw [hpeel, hshift]
    have h01 : dseq D (0 + 1) = dseq D 1 := rfl
    rw [h01]
    linarith
  rw [hq]
  linarith

/-- The far rows have good degree at least the previous mass, so
`φ(q) ≤ a_{j+1}^{-α}`. -/
lemma dexp_phi_tail_le {α : ℝ} (hα0 : 0 ≤ α) {D : ℝ} (hD : 5 ≤ D) (j : ℕ) :
    phi α (q (dexpPMF hD) pathCompat (j + 2)) ≤ 1 / dseq D (j + 1) ^ α := by
  have hrlow : dseq D (j + 1) ≤ (rE (dexpPMF hD) pathCompat (j + 2)).toReal := by
    have hone : (dexpPMF hD (j + 1) : ℝ≥0∞)
        ≤ rE (dexpPMF hD) pathCompat (j + 2) := by
      calc (dexpPMF hD (j + 1) : ℝ≥0∞)
          = (if pathCompat (j + 2) (j + 1) then dexpPMF hD (j + 1) else 0) := by
            rw [if_pos (by unfold pathCompat; omega)]
        _ ≤ ∑' y, (if pathCompat (j + 2) y then dexpPMF hD y else 0) :=
            ENNReal.le_tsum _
        _ = rE (dexpPMF hD) pathCompat (j + 2) := by rw [rE]
    have := ENNReal.toReal_mono rE_ne_top hone
    rwa [dexpPMF_succ_toReal hD (by omega)] at this
  have h1q : dseq D (j + 1) ≤ 1 - q (dexpPMF hD) pathCompat (j + 2) := by
    have h := toReal_rE_add_toReal_qE (dexpPMF hD) pathCompat (j + 2)
    rw [q]; linarith
  have hd : (0:ℝ) < dseq D (j + 1) ^ α :=
    Real.rpow_pos_of_pos (dseq_pos D (j + 1)) α
  have hpow : dseq D (j + 1) ^ α
      ≤ (1 - q (dexpPMF hD) pathCompat (j + 2)) ^ α :=
    Real.rpow_le_rpow (dseq_pos D (j + 1)).le h1q hα0
  have h1qpos : (0:ℝ) < (1 - q (dexpPMF hD) pathCompat (j + 2)) ^ α :=
    lt_of_lt_of_le hd hpow
  rw [phi]
  calc q (dexpPMF hD) pathCompat (j + 2)
        / (1 - q (dexpPMF hD) pathCompat (j + 2)) ^ α
      = q (dexpPMF hD) pathCompat (j + 2)
          * (1 / (1 - q (dexpPMF hD) pathCompat (j + 2)) ^ α) :=
        div_eq_mul_one_div _ _
    _ ≤ 1 * (1 / (1 - q (dexpPMF hD) pathCompat (j + 2)) ^ α) :=
        mul_le_mul_of_nonneg_right q_le_one
          (one_div_nonneg.mpr h1qpos.le)
    _ = 1 / (1 - q (dexpPMF hD) pathCompat (j + 2)) ^ α := one_mul _
    _ ≤ 1 / dseq D (j + 1) ^ α := one_div_le_one_div_of_le hd hpow

/-- The far rows bounded by the tail budget. -/
lemma dexp_row_tail_le {α : ℝ} (hα0 : 0 ≤ α) {D : ℝ} (hD : 5 ≤ D) (j : ℕ) :
    dexpPMF hD (j + 2) * phiE α (q (dexpPMF hD) pathCompat (j + 2))
      ≤ ENNReal.ofReal (ubound α D j) := by
  have hne : dexpPMF hD (j + 2) ≠ 0 := by
    rw [dexpPMF_succ hD (by omega)]
    exact (ENNReal.ofReal_pos.mpr (dseq_pos D (j + 2))).ne'
  have hqlt : q (dexpPMF hD) pathCompat (j + 2) < 1 :=
    q_lt_one (pathCompat_refl _) hne
  rw [phiE_of_lt hqlt, dexpPMF_succ hD (by omega),
    ← ENNReal.ofReal_mul (dseq_pos D (j + 2)).le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← ubound_eq α D j]
  calc dseq D (j + 2) * phi α (q (dexpPMF hD) pathCompat (j + 2))
      ≤ dseq D (j + 2) * (1 / dseq D (j + 1) ^ α) :=
        mul_le_mul_of_nonneg_left (dexp_phi_tail_le hα0 hD j)
          (dseq_pos D (j + 2)).le
    _ = dseq D (j + 2) / dseq D (j + 1) ^ α := (div_eq_mul_one_div _ _).symm

/-- The two root rows bounded by the head budget `u₀`. -/
lemma dexp_row_head_le {α : ℝ} (hα1 : 1 ≤ α) {D : ℝ} (hD : 5 ≤ D)
    {j : ℕ} (hj : j ≤ 1) :
    dexpPMF hD j * phiE α (q (dexpPMF hD) pathCompat j)
      ≤ ENNReal.ofReal (ubound α D 0) := by
  have hα0 : (0:ℝ) ≤ α := by linarith
  have ha2 : dseq D 2 < 1 / 20 := by
    rw [dseq]
    exact exp_neg_lt_twentieth (by nlinarith)
  have h2a2lt : 2 * dseq D 2 < 1 := by linarith
  have hphi : phi α (2 * dseq D 2) ≤ ubound α D 0 := by
    have hs : 1 / 2 < 1 - 2 * dseq D 2 := by linarith
    have hinv := inv_rpow_le_two_rpow hα0 hs
    have h2exp := two_rpow_le_exp hα1 hD
    have hub0 : ubound α D 0 = Real.exp (α * D) * dseq D 2 := by
      rw [ubound, dseq, ← Real.exp_add]; congr 1; ring
    have ha2nn : (0:ℝ) ≤ 2 * dseq D 2 := by linarith [dseq_pos D 2]
    calc phi α (2 * dseq D 2)
        = (2 * dseq D 2) * (1 / (1 - 2 * dseq D 2) ^ α) := by
          rw [phi]; exact div_eq_mul_one_div _ _
      _ ≤ (2 * dseq D 2) * (2:ℝ) ^ α :=
          mul_le_mul_of_nonneg_left hinv ha2nn
      _ = (2:ℝ) ^ (α + 1) * dseq D 2 := by
          rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]; ring
      _ ≤ Real.exp (α * D) * dseq D 2 :=
          mul_le_mul_of_nonneg_right h2exp (dseq_pos D 2).le
      _ = ubound α D 0 := hub0.symm
  calc dexpPMF hD j * phiE α (q (dexpPMF hD) pathCompat j)
      ≤ 1 * phiE α (2 * dseq D 2) :=
        mul_le_mul' (PMF.coe_le_one _ _)
          (phiE_mono hα0 q_nonneg (dexp_q_le hD hj))
    _ = phiE α (2 * dseq D 2) := one_mul _
    _ = ENNReal.ofReal (phi α (2 * dseq D 2)) := phiE_of_lt h2a2lt
    _ ≤ ENNReal.ofReal (ubound α D 0) := ENNReal.ofReal_le_ofReal hphi

/-- **The double-exponential potential bound**: `η(α) ≤ 4 e^{-(D-α)D}`
for `D ≥ max(5, α+1)`. -/
lemma dexp_etaG_le {α : ℝ} (hα1 : 1 ≤ α) {D : ℝ} (hD : 5 ≤ D)
    (hDα : α + 1 ≤ D) :
    etaG α pathCompat (dexpPMF hD) ≤ ENNReal.ofReal (4 * ubound α D 0) := by
  have hα0 : (0:ℝ) ≤ α := by linarith
  have hu0 := (ubound_pos α D 0).le
  have htsum : (∑' j, ENNReal.ofReal (ubound α D j))
      ≤ ENNReal.ofReal (2 * ubound α D 0) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => (ubound_pos α D j).le)
        (ubound_tail hD hDα).1]
    exact ENNReal.ofReal_le_ofReal (ubound_tail hD hDα).2
  rw [etaG, PhiD, tsum_eq_zero_add' ENNReal.summable,
    tsum_eq_zero_add' ENNReal.summable]
  refine le_trans (add_le_add (dexp_row_head_le hα1 hD (by norm_num))
    (add_le_add (dexp_row_head_le hα1 hD (by norm_num))
      (le_trans (ENNReal.tsum_le_tsum fun j => dexp_row_tail_le hα0 hD j)
        htsum))) ?_
  rw [← ENNReal.ofReal_add hu0 (by linarith),
    ← ENNReal.ofReal_add hu0 (by linarith)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### The exponential three-label law -/

/-- The two exponential masses together stay below `1/10`. -/
lemma exp3_tail_lt {D : ℝ} (hD : 5 ≤ D) :
    Real.exp (-D) + Real.exp (-(D ^ 2)) < 1 / 10 := by
  have h1 := exp_neg_lt_twentieth hD
  have h2 := exp_neg_lt_twentieth (show (5 : ℝ) ≤ D ^ 2 by nlinarith)
  linarith

/-- The mass function of the exponential three-label law:
`p₁ = e^{-D}`, `p₂ = e^{-D²}`, `p₀` the remainder. -/
noncomputable def exp3F (D : ℝ) : ℕ → ℝ≥0∞ :=
  fun n =>
    if n = 0 then ENNReal.ofReal (1 - Real.exp (-D) - Real.exp (-(D ^ 2)))
    else if n = 1 then ENNReal.ofReal (Real.exp (-D))
    else if n = 2 then ENNReal.ofReal (Real.exp (-(D ^ 2)))
    else 0

lemma exp3F_zero (D : ℝ) :
    exp3F D 0 = ENNReal.ofReal (1 - Real.exp (-D) - Real.exp (-(D ^ 2))) := by
  simp [exp3F]

lemma exp3F_one (D : ℝ) :
    exp3F D 1 = ENNReal.ofReal (Real.exp (-D)) := by
  simp [exp3F]

lemma exp3F_two (D : ℝ) :
    exp3F D 2 = ENNReal.ofReal (Real.exp (-(D ^ 2))) := by
  simp [exp3F]

lemma exp3F_of_ge {D : ℝ} {n : ℕ} (hn : 3 ≤ n) : exp3F D n = 0 := by
  simp only [exp3F]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma exp3F_tsum {D : ℝ} (hD : 5 ≤ D) : ∑' n, exp3F D n = 1 := by
  have htail := exp3_tail_lt hD
  have hz : ∀ n ∉ ({0, 1, 2} : Finset ℕ), exp3F D n = 0 := by
    intro n hn
    rcases n with _ | _ | _ | m
    · exact absurd (by decide) hn
    · exact absurd (by decide) hn
    · exact absurd (by decide) hn
    · exact exp3F_of_ge (by omega)
  rw [tsum_eq_sum hz, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    exp3F_zero, exp3F_one, exp3F_two,
    ← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
    ← ENNReal.ofReal_add (by linarith) (by positivity),
    show 1 - Real.exp (-D) - Real.exp (-(D ^ 2))
        + (Real.exp (-D) + Real.exp (-(D ^ 2))) = 1 from by ring,
    ENNReal.ofReal_one]

/-- The exponential three-label law as a `PMF ℕ` (support `{0,1,2}`). -/
noncomputable def exp3PMF {D : ℝ} (hD : 5 ≤ D) : PMF ℕ :=
  ⟨exp3F D, by
    have := ENNReal.summable.hasSum (f := exp3F D)
    rwa [exp3F_tsum hD] at this⟩

lemma exp3PMF_apply {D : ℝ} (hD : 5 ≤ D) (n : ℕ) :
    exp3PMF hD n = exp3F D n := rfl

/-- The root carries most of the mass: `p₀ ≥ 9/10 ≥ 1/2`. -/
lemma exp3_half_le {D : ℝ} (hD : 5 ≤ D) : 2⁻¹ ≤ exp3PMF hD 0 := by
  have htail := exp3_tail_lt hD
  refine (ENNReal.toReal_le_toReal (by norm_num)
    ((exp3PMF hD).apply_ne_top 0)).mp ?_
  rw [exp3PMF_apply hD, exp3F_zero, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by linarith)]
  norm_num
  linarith

/-! ### The three-label degrees -/

lemma exp3_qE_zero {D : ℝ} (hD : 5 ≤ D) :
    qE (exp3PMF hD) pathCompat 0 = ENNReal.ofReal (Real.exp (-(D ^ 2))) := by
  rw [qE]
  have hz : ∀ y ∉ ({2} : Finset ℕ),
      (if pathCompat 0 y then 0 else exp3PMF hD y) = 0 := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    rcases y with _ | _ | _ | n
    · exact if_pos (pathCompat_refl 0)
    · exact if_pos (pathCompat_iff.mpr (by omega))
    · exact absurd rfl hy
    · split_ifs
      · rfl
      · rw [exp3PMF_apply hD]
        exact exp3F_of_ge (by omega)
  rw [tsum_eq_sum hz, Finset.sum_singleton,
    if_neg (fun h => by rw [pathCompat_iff] at h; omega),
    exp3PMF_apply hD, exp3F_two]

lemma exp3_qE_one {D : ℝ} (hD : 5 ≤ D) :
    qE (exp3PMF hD) pathCompat 1 = 0 := by
  rw [qE, ENNReal.tsum_eq_zero]
  intro y
  rcases y with _ | _ | _ | n
  · exact if_pos (pathCompat_iff.mpr (by omega))
  · exact if_pos (pathCompat_refl 1)
  · exact if_pos (pathCompat_iff.mpr (by omega))
  · split_ifs
    · rfl
    · rw [exp3PMF_apply hD]
      exact exp3F_of_ge (by omega)

lemma exp3_qE_two {D : ℝ} (hD : 5 ≤ D) :
    qE (exp3PMF hD) pathCompat 2
      = ENNReal.ofReal (1 - Real.exp (-D) - Real.exp (-(D ^ 2))) := by
  rw [qE]
  have hz : ∀ y ∉ ({0} : Finset ℕ),
      (if pathCompat 2 y then 0 else exp3PMF hD y) = 0 := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    rcases y with _ | _ | _ | n
    · exact absurd rfl hy
    · exact if_pos (pathCompat_iff.mpr (by omega))
    · exact if_pos (pathCompat_refl 2)
    · split_ifs
      · rfl
      · rw [exp3PMF_apply hD]
        exact exp3F_of_ge (by omega)
  rw [tsum_eq_sum hz, Finset.sum_singleton,
    if_neg (fun h => by rw [pathCompat_iff] at h; omega),
    exp3PMF_apply hD, exp3F_zero]

lemma exp3_q_zero {D : ℝ} (hD : 5 ≤ D) :
    q (exp3PMF hD) pathCompat 0 = Real.exp (-(D ^ 2)) := by
  rw [q, exp3_qE_zero hD, ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma exp3_q_one {D : ℝ} (hD : 5 ≤ D) :
    q (exp3PMF hD) pathCompat 1 = 0 := by
  rw [q, exp3_qE_one hD]
  simp

lemma exp3_q_two {D : ℝ} (hD : 5 ≤ D) :
    q (exp3PMF hD) pathCompat 2
      = 1 - Real.exp (-D) - Real.exp (-(D ^ 2)) := by
  have htail := exp3_tail_lt hD
  rw [q, exp3_qE_two hD, ENNReal.toReal_ofReal (by linarith)]

/-! ### The three-label potential bound -/

/-- The exponential three-label potential bound: for `D ≥ 5`,
`η ≤ 9 e^{-(D-5/2)D}` (`8 e^{-D²}` from the root row, `e^{-D²+(5/2)D}`
from the far row, the middle row vanishes). -/
lemma exp3_etaG_le {D : ℝ} (hD : 5 ≤ D) :
    etaG (5 / 2) pathCompat (exp3PMF hD)
      ≤ ENNReal.ofReal (9 * ubound (5 / 2) D 0) := by
  have htail := exp3_tail_lt hD
  have hp1 : (0 : ℝ) < Real.exp (-D) := Real.exp_pos _
  have hp2 : (0 : ℝ) < Real.exp (-(D ^ 2)) := Real.exp_pos _
  have hq0lt : Real.exp (-(D ^ 2)) < 1 := by linarith
  have hq2lt : 1 - Real.exp (-D) - Real.exp (-(D ^ 2)) < 1 := by linarith
  -- the two live rows
  have hphi0 : phi (5 / 2) (Real.exp (-(D ^ 2))) ≤ 8 * Real.exp (-(D ^ 2)) := by
    rw [phi]
    have hs : 1 / 2 < 1 - Real.exp (-(D ^ 2)) := by linarith
    have hinv := inv_rpow_le_two_rpow (show (0 : ℝ) ≤ 5 / 2 by norm_num) hs
    have h8 := two_rpow_five_half_le_eight
    calc Real.exp (-(D ^ 2)) / (1 - Real.exp (-(D ^ 2))) ^ ((5 : ℝ) / 2)
        = Real.exp (-(D ^ 2))
            * (1 / (1 - Real.exp (-(D ^ 2))) ^ ((5 : ℝ) / 2)) :=
          div_eq_mul_one_div _ _
      _ ≤ Real.exp (-(D ^ 2)) * (2 : ℝ) ^ ((5 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
      _ ≤ Real.exp (-(D ^ 2)) * 8 :=
          mul_le_mul_of_nonneg_left h8 (Real.exp_pos _).le
      _ = 8 * Real.exp (-(D ^ 2)) := mul_comm _ _
  have hphi2 : phi (5 / 2) (1 - Real.exp (-D) - Real.exp (-(D ^ 2)))
      ≤ Real.exp (5 / 2 * D) := by
    rw [phi,
      show 1 - (1 - Real.exp (-D) - Real.exp (-(D ^ 2)))
          = Real.exp (-D) + Real.exp (-(D ^ 2)) from by ring]
    have hexp : Real.exp (-D) ^ ((5 : ℝ) / 2) = Real.exp (-(5 / 2 * D)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    calc (1 - Real.exp (-D) - Real.exp (-(D ^ 2)))
          / (Real.exp (-D) + Real.exp (-(D ^ 2))) ^ ((5 : ℝ) / 2)
        ≤ 1 / Real.exp (-D) ^ ((5 : ℝ) / 2) := by
          gcongr
          linarith
      _ = Real.exp (5 / 2 * D) := by
          rw [hexp, one_div, Real.exp_neg, inv_inv]
  -- assemble the three rows
  have ht0 : exp3PMF hD 0 * phiE (5 / 2) (q (exp3PMF hD) pathCompat 0)
      ≤ ENNReal.ofReal (8 * Real.exp (-(D ^ 2))) := by
    rw [exp3_q_zero hD, phiE_of_lt hq0lt]
    refine le_trans (mul_le_mul' (PMF.coe_le_one _ _)
      (ENNReal.ofReal_le_ofReal hphi0)) ?_
    rw [one_mul]
  have ht1 : exp3PMF hD 1 * phiE (5 / 2) (q (exp3PMF hD) pathCompat 1) = 0 := by
    rw [exp3_q_one hD, phiE_zero, mul_zero]
  have ht2 : exp3PMF hD 2 * phiE (5 / 2) (q (exp3PMF hD) pathCompat 2)
      ≤ ENNReal.ofReal (Real.exp (-(D ^ 2)) * Real.exp (5 / 2 * D)) := by
    rw [exp3_q_two hD, phiE_of_lt hq2lt, exp3PMF_apply hD, exp3F_two,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hphi2 (Real.exp_pos _).le)
  have hz : ∀ y ∉ ({0, 1, 2} : Finset ℕ),
      exp3PMF hD y * phiE (5 / 2) (q (exp3PMF hD) pathCompat y) = 0 := by
    intro y hy
    rcases y with _ | _ | _ | n
    · exact absurd (by decide) hy
    · exact absurd (by decide) hy
    · exact absurd (by decide) hy
    · rw [exp3PMF_apply hD, exp3F_of_ge (by omega), zero_mul]
  have hu : ubound (5 / 2) D 0 = Real.exp (-(D ^ 2) + 5 / 2 * D) := by
    rw [ubound]
    congr 1
    ring
  rw [etaG, PhiD, tsum_eq_sum hz, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  refine le_trans (add_le_add ht0 (add_le_add ht1.le ht2)) ?_
  rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity), hu]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmono : Real.exp (-(D ^ 2)) ≤ Real.exp (-(D ^ 2) + 5 / 2 * D) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [← Real.exp_add]
  linarith

/-! ### The general theorem at the two laws -/

/-- **`thm:exponential`, failure form**: the general matching theorem at
the exponential three-label law, with the potential replaced by its
certified budget `9 e^{-(D-5/2)D}`. -/
theorem varying_exp3_failure_le {D : ℝ} (hD : 5 ≤ D)
    (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (cN nA : ℕ) (hcN : (scrIndex N S).card ≤ cN)
    (hnA : (tgtUniv N).card ≤ nA)
    (hsmall : genSmallC cN S.card nA T
        * ENNReal.ofReal (9 * ubound (5 / 2) D 0) ≤ 1) :
    ∀ h, (∑' x, Tlaw (exp3PMF hD) ν 0 h x
        * qE (Tlaw (exp3PMF hD) ν 0 h) (fullSim (labRel pathCompat) h) x)
      ≤ genKcC cN S.card T
        * ENNReal.ofReal (9 * ubound (5 / 2) D 0) := by
  have hη := exp3_etaG_le hD
  have hsmall' : genSmallC cN S.card nA T
      * etaG (5 / 2) pathCompat (exp3PMF hD) ≤ 1 :=
    le_trans (mul_le_mul' le_rfl hη) hsmall
  intro h
  exact le_trans
    (varying_failure_le pathCompat (exp3PMF hD) 0 ν N S
      pathCompat_refl pathCompat_symm (exp3_half_le hD) hN hS hSne hSsupp
      T hT cN nA hcN hnA hsmall' h)
    (mul_le_mul' le_rfl hη)

/-- **`thm:exponential`, infinite-tree form**. -/
theorem varying_exp3_matching_le {Ω : Type*} [MeasurableSpace Ω]
    (Pm : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure Pm]
    {D : ℝ} (hD : 5 ≤ D)
    (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (cN nA : ℕ) (hcN : (scrIndex N S).card ≤ cN)
    (hnA : (tgtUniv N).card ≤ nA)
    (hsmall : genSmallC cN S.card nA T
        * ENNReal.ofReal (9 * ubound (5 / 2) D 0) ≤ 1)
    (X Y : (n : ℕ) → Ω → FullLab (ℕ × ℕ) n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hpair : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, Pm.map (fun ω => (X n ω, Y n ω))
        = (prodPMF (Tlaw (exp3PMF hD) ν 0 n)
            (Tlaw (exp3PMF hD) ν 0 n)).toMeasure) :
    1 - genKcC cN S.card T * ENNReal.ofReal (9 * ubound (5 / 2) D 0)
      ≤ Pm {ω | InfMatch (labRel pathCompat)
          (fun n => X n ω) (fun n => Y n ω)} := by
  have hη := exp3_etaG_le hD
  have hsmall' : genSmallC cN S.card nA T
      * etaG (5 / 2) pathCompat (exp3PMF hD) ≤ 1 :=
    le_trans (mul_le_mul' le_rfl hη) hsmall
  refine le_trans (tsub_le_tsub_left (mul_le_mul' le_rfl hη) 1) ?_
  exact varying_matching_le pathCompat (exp3PMF hD) 0 Pm ν N S
    pathCompat_refl pathCompat_symm (exp3_half_le hD) hN hS hSne hSsupp
    T hT cN nA hcN hnA hsmall' X Y hX hY hpair hlaw

/-- **`thm:doubleexp`, failure form**: the general matching theorem at
the double-exponential law on the half-line, with the potential
replaced by its certified budget `4 e^{-(D-5/2)D}`. -/
theorem varying_doubleExp_failure_le {D : ℝ} (hD : 5 ≤ D)
    (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (cN nA : ℕ) (hcN : (scrIndex N S).card ≤ cN)
    (hnA : (tgtUniv N).card ≤ nA)
    (hsmall : genSmallC cN S.card nA T
        * ENNReal.ofReal (4 * ubound (5 / 2) D 0) ≤ 1) :
    ∀ h, (∑' x, Tlaw (dexpPMF hD) ν 0 h x
        * qE (Tlaw (dexpPMF hD) ν 0 h) (fullSim (labRel pathCompat) h) x)
      ≤ genKcC cN S.card T
        * ENNReal.ofReal (4 * ubound (5 / 2) D 0) := by
  have hη := dexp_etaG_le (α := 5 / 2) (by norm_num) hD (by linarith)
  have hsmall' : genSmallC cN S.card nA T
      * etaG (5 / 2) pathCompat (dexpPMF hD) ≤ 1 :=
    le_trans (mul_le_mul' le_rfl hη) hsmall
  intro h
  exact le_trans
    (varying_failure_le pathCompat (dexpPMF hD) 0 ν N S
      pathCompat_refl pathCompat_symm (dexp_half_le hD) hN hS hSne hSsupp
      T hT cN nA hcN hnA hsmall' h)
    (mul_le_mul' le_rfl hη)

/-- **`thm:doubleexp`, infinite-tree form**. -/
theorem varying_doubleExp_matching_le {Ω : Type*} [MeasurableSpace Ω]
    (Pm : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure Pm]
    {D : ℝ} (hD : 5 ≤ D)
    (ν : PMF ℕ) (N : ℕ) (S : Finset ℕ)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (T : ℝ≥0∞)
    (hT : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-(5 / 2 : ℝ))) ≤ T)
    (cN nA : ℕ) (hcN : (scrIndex N S).card ≤ cN)
    (hnA : (tgtUniv N).card ≤ nA)
    (hsmall : genSmallC cN S.card nA T
        * ENNReal.ofReal (4 * ubound (5 / 2) D 0) ≤ 1)
    (X Y : (n : ℕ) → Ω → FullLab (ℕ × ℕ) n)
    (hX : ∀ n ω, restrictLab n (X (n + 1) ω) = X n ω)
    (hY : ∀ n ω, restrictLab n (Y (n + 1) ω) = Y n ω)
    (hpair : ∀ n, Measurable (fun ω => (X n ω, Y n ω)))
    (hlaw : ∀ n, Pm.map (fun ω => (X n ω, Y n ω))
        = (prodPMF (Tlaw (dexpPMF hD) ν 0 n)
            (Tlaw (dexpPMF hD) ν 0 n)).toMeasure) :
    1 - genKcC cN S.card T * ENNReal.ofReal (4 * ubound (5 / 2) D 0)
      ≤ Pm {ω | InfMatch (labRel pathCompat)
          (fun n => X n ω) (fun n => Y n ω)} := by
  have hη := dexp_etaG_le (α := 5 / 2) (by norm_num) hD (by linarith)
  have hsmall' : genSmallC cN S.card nA T
      * etaG (5 / 2) pathCompat (dexpPMF hD) ≤ 1 :=
    le_trans (mul_le_mul' le_rfl hη) hsmall
  refine le_trans (tsub_le_tsub_left (mul_le_mul' le_rfl hη) 1) ?_
  exact varying_matching_le pathCompat (dexpPMF hD) 0 Pm ν N S
    pathCompat_refl pathCompat_symm (dexp_half_le hD) hN hS hSne hSsupp
    T hT cN nA hcN hnA hsmall' X Y hX hY hpair hlaw

/-! ### The binary law as an instance of the general theorem -/

/-- `ν = δ₂` as an instance of the general numeric closure at `N = 2`,
`S = {2}`, `T = 1`, `cN = 7·2⁷·8 = 7168`, `nA = 7` (`rem:delta2`).
The instance is
superseded outright: at `δ₂` every counter equals `2`, the label field
is i.i.d., and the i.i.d. development (library `GraphMatching`,
`full_matching_bound` and `infinite_tree_matching_prob_of_law`)
certifies the failure bound `16η` under `η ≤ 10⁻⁴`; the point here is
the instantiation. -/
theorem delta2_failure_le_of_general {V : Type} (Rv : V → V → Prop)
    (μ : PMF V) (v0 : V) (hrefl : ∀ v, Rv v v)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0)
    (hsmall : genSmallC 7168 1 7 1 * etaG (5 / 2) Rv μ ≤ 1) :
    ∀ h, (∑' x, Tlaw μ (PMF.pure 2) v0 h x
        * qE (Tlaw μ (PMF.pure 2) v0 h) (fullSim (labRel Rv) h) x)
      ≤ genKcC 7168 1 1 * etaG (5 / 2) Rv μ := by
  have hcard : ({2} : Finset ℕ).card = 1 := Finset.card_singleton 2
  have hSsupp : ∀ i : ℕ, ((PMF.pure 2 : PMF ℕ) i : ℝ≥0∞) ≠ 0
      ↔ i ∈ ({2} : Finset ℕ) := by
    intro i
    by_cases hi : i = 2
    · subst hi
      simp [PMF.pure_apply]
    · simp [PMF.pure_apply, hi]
  have hT : (∑' i, if ((PMF.pure 2 : PMF ℕ) i : ℝ≥0∞) = 0 then 0
      else ((PMF.pure 2 : PMF ℕ) i : ℝ≥0∞) ^ (-(5 / 2 : ℝ)))
      ≤ (1 : ℝ≥0∞) := by
    have hpt : ∀ i : ℕ, (if ((PMF.pure 2 : PMF ℕ) i : ℝ≥0∞) = 0 then 0
        else ((PMF.pure 2 : PMF ℕ) i : ℝ≥0∞) ^ (-(5 / 2 : ℝ)))
        = if i = 2 then 1 else 0 := by
      intro i
      by_cases hi : i = 2
      · subst hi
        rw [if_pos rfl]
        rw [if_neg (by simp [PMF.pure_apply])]
        simp [PMF.pure_apply, ENNReal.one_rpow]
      · rw [if_neg hi, if_pos (by simp [PMF.pure_apply, hi])]
    rw [tsum_congr hpt]
    rw [tsum_ite_eq]
  have hcN : (scrIndex 2 ({2} : Finset ℕ)).card ≤ 7168 := by
    refine le_trans (scrIndex_card_le 2 {2}) ?_
    refine le_trans (screenUniv_card_le 2) ?_
    norm_num
  have hnA : (tgtUniv 2).card ≤ 7 :=
    le_trans (tgtUniv_card_le 2) (by norm_num)
  have h := varying_failure_le Rv μ v0 (PMF.pure 2) 2 {2}
    hrefl hsymm hhalf (by norm_num)
    (fun k hk => by rw [Finset.mem_singleton] at hk; omega)
    ⟨2, Finset.mem_singleton_self 2⟩ hSsupp 1 hT 7168 7 hcN hnA
    (by rw [hcard] at *; exact hsmall)
  rw [hcard] at h
  exact h

end GraphMarkovMatching
