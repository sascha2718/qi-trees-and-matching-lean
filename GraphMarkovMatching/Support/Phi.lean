/-
The weight `φ_α t = t / (1-t)^α` at a *free* exponent `α`, together with the
elementary facts the support layer needs:

* `le_phi`              `t ≤ φ_α t` on `[0,1)`
* `one_sub_rpow_le`     the tangent line to `t ↦ t^α` at `t = 1` (Bernoulli)
* `rpow_neg_alpha_le`   `(1-t)^{-α} ≤ 1 + α φ_α(t)`
* `chord`               `(1-z)^{-α} ≤ 1 + c_α z` on `[0,1/2]`, `c_α = 2(2^α - 1)`
* `add_sq_le_weighted`  the weighted mean inequality behind `A_δ`

The exponent is a variable throughout.  The chord is proved from concavity
of `log` (both endpoint values of `z ↦ log(1+c_α z) + α log(1-z)` on
`[0,1/2]` vanish), which works for every `α ≥ 0`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

namespace GraphMarkovMatching.Support

open Real

/-- `φ_α t = t / (1-t)^α`. The paper defines it on `[0,1)`; off that range
Lean's junk values apply and every lemma below carries `t < 1`. -/
noncomputable def phi (α t : ℝ) : ℝ := t / (1 - t) ^ α

/-- On `(-∞,1)` the denominator of `φ_α` is positive. -/
lemma rpow_denom_pos (α : ℝ) {t : ℝ} (h : t < 1) : 0 < (1 - t) ^ α :=
  Real.rpow_pos_of_pos (by linarith) α

lemma phi_nonneg {α t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : 0 ≤ phi α t :=
  div_nonneg h0 (rpow_denom_pos α h1).le

/-- `t ≤ φ_α t` on `[0,1)`, since `(1-t)^α ≤ 1` for `α ≥ 0`. -/
lemma le_phi {α t : ℝ} (hα : 0 ≤ α) (h0 : 0 ≤ t) (h1 : t < 1) : t ≤ phi α t := by
  rw [phi, le_div_iff₀ (rpow_denom_pos α h1)]
  have h : (1 - t) ^ α ≤ 1 :=
    Real.rpow_le_one (by linarith) (by linarith) hα
  nlinarith

/-- The tangent line to `t ↦ t^α` at `t = 1` lies below the graph:
`1 - r^α ≤ α (1-r)` for `0 ≤ r` and `α ≥ 1` (Bernoulli). -/
lemma one_sub_rpow_le {α r : ℝ} (hα : 1 ≤ α) (hr : 0 ≤ r) :
    1 - r ^ α ≤ α * (1 - r) := by
  have h := one_add_mul_self_le_rpow_one_add (s := r - 1) (by linarith) hα
  have e : (1 : ℝ) + (r - 1) = r := by ring
  rw [e] at h
  linarith

/-- `(1-t)^{-α} ≤ 1 + α φ_α(t)` on `(-∞,1)` for `α ≥ 1`: the form in which
the tangent bound is consumed by the product lemma and the second term of the
contraction lemma (`W(x) - 1 ≤ α φ_α(q(x))`). -/
lemma rpow_neg_alpha_le {α t : ℝ} (hα : 1 ≤ α) (h1 : t < 1) :
    (1 - t) ^ (-α) ≤ 1 + α * phi α t := by
  have hr : (0 : ℝ) < 1 - t := by linarith
  have hp : (0 : ℝ) < (1 - t) ^ α := rpow_denom_pos α h1
  rw [Real.rpow_neg hr.le, inv_eq_one_div, div_le_iff₀ hp]
  have h := one_sub_rpow_le hα hr.le
  have hphi : α * phi α t * (1 - t) ^ α = α * t := by
    rw [phi]; field_simp
  nlinarith [h, hphi]

/-! ### The chord bound at a free exponent

`(1-z)^{-α} ≤ 1 + c_α z` on `[0,1/2]` with the exact chord slope
`c_α = 2(2^α - 1)` through `(0,1)` and `(1/2, 2^α)`. At a free exponent the
proof uses concavity of `log`: the
function `g z = log(1 + c_α z) + α log(1-z)` satisfies `g 0 = g (1/2) = 0`
and is concave, hence nonnegative on `[0,1/2]`, and `exp g` is the claim. -/

/-- The chord slope `c_α = 2(2^α - 1)`. -/
noncomputable def chordConst (α : ℝ) : ℝ := 2 * ((2 : ℝ) ^ α - 1)

lemma one_le_two_rpow {α : ℝ} (hα : 0 ≤ α) : (1 : ℝ) ≤ (2 : ℝ) ^ α := by
  calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
  _ ≤ (2 : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le one_le_two hα

lemma chordConst_nonneg {α : ℝ} (hα : 0 ≤ α) : 0 ≤ chordConst α := by
  have := one_le_two_rpow hα
  rw [chordConst]; linarith

/-- The multiplicative form of the chord bound:
`1 ≤ (1 + c_α z)(1-z)^α` on `[0,1/2]`. -/
lemma chord_key {α z : ℝ} (hα : 0 ≤ α) (h0 : 0 ≤ z) (h1 : z ≤ 1 / 2) :
    1 ≤ (1 + chordConst α * z) * (1 - z) ^ α := by
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ α := one_le_two_rpow hα
  have hz1 : (0 : ℝ) < 1 - z := by linarith
  have hcz : (0 : ℝ) < 1 + chordConst α * z := by
    have := mul_nonneg (chordConst_nonneg hα) h0
    linarith
  -- concavity of log, applied twice with weights (1-2z, 2z)
  have hconc : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have ha : (0 : ℝ) ≤ 1 - 2 * z := by linarith
  have hb : (0 : ℝ) ≤ 2 * z := by linarith
  have hab : (1 - 2 * z) + 2 * z = 1 := by ring
  -- first application: points 1 and 2^α, giving log (1 + c_α z)
  have hx1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hy1 : (2 : ℝ) ^ α ∈ Set.Ioi (0 : ℝ) := Real.rpow_pos_of_pos two_pos α
  have hlog1 : (1 - 2 * z) * Real.log 1 + (2 * z) * Real.log ((2 : ℝ) ^ α)
      ≤ Real.log ((1 - 2 * z) * 1 + (2 * z) * ((2 : ℝ) ^ α)) := by
    have := hconc.2 hx1 hy1 ha hb hab
    simpa [smul_eq_mul] using this
  have he1 : (1 - 2 * z) * 1 + (2 * z) * ((2 : ℝ) ^ α) = 1 + chordConst α * z := by
    rw [chordConst]; ring
  have hl1 : 2 * z * (α * Real.log 2) ≤ Real.log (1 + chordConst α * z) := by
    rw [he1] at hlog1
    rw [Real.log_one] at hlog1
    rw [Real.log_rpow two_pos] at hlog1
    linarith [hlog1]
  -- second application: points 1 and 1/2, giving log (1 - z)
  have hy2 : (1 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hlog2 : (1 - 2 * z) * Real.log 1 + (2 * z) * Real.log (1 / 2 : ℝ)
      ≤ Real.log ((1 - 2 * z) * 1 + (2 * z) * (1 / 2 : ℝ)) := by
    have := hconc.2 hx1 hy2 ha hb hab
    simpa [smul_eq_mul] using this
  have he2 : (1 - 2 * z) * 1 + (2 * z) * (1 / 2 : ℝ) = 1 - z := by ring
  have hl2 : -(2 * z * Real.log 2) ≤ Real.log (1 - z) := by
    rw [he2] at hlog2
    rw [Real.log_one] at hlog2
    have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [hhalf] at hlog2
    linarith [hlog2]
  -- multiply the second by α ≥ 0 and add
  have hl2' : α * (-(2 * z * Real.log 2)) ≤ α * Real.log (1 - z) :=
    mul_le_mul_of_nonneg_left hl2 hα
  have hsum : 0 ≤ Real.log (1 + chordConst α * z) + α * Real.log (1 - z) := by
    nlinarith [hl1, hl2']
  -- exponentiate
  have hprod : (1 + chordConst α * z) * (1 - z) ^ α
      = Real.exp (Real.log (1 + chordConst α * z) + α * Real.log (1 - z)) := by
    rw [Real.exp_add, Real.exp_log hcz, Real.rpow_def_of_pos hz1, mul_comm α]
  rw [hprod]
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
  _ ≤ Real.exp (Real.log (1 + chordConst α * z) + α * Real.log (1 - z)) :=
      Real.exp_le_exp.mpr hsum

/-- **The chord bound**: `(1-z)^{-α} ≤ 1 + c_α z` on `[0,1/2]`, `α ≥ 0`. -/
lemma chord {α z : ℝ} (hα : 0 ≤ α) (h0 : 0 ≤ z) (h1 : z ≤ 1 / 2) :
    (1 - z) ^ (-α) ≤ 1 + chordConst α * z := by
  have hz : (0 : ℝ) ≤ 1 - z := by linarith
  have hP : 0 < (1 - z) ^ α := rpow_denom_pos α (by linarith)
  rw [Real.rpow_neg hz, inv_eq_one_div, div_le_iff₀ hP]
  exact chord_key hα h0 h1

/-! ### The weighted mean inequality

`(x+y)² ≤ (1+δ)x² + (1+δ⁻¹)y²` for `δ > 0`; at `δ = 1` this is the plain
`(x+y)² ≤ 2x² + 2y²`. It is what produces the contraction constant
`A_δ(α) = 2L(α) + 2(1+δ)K(α)` in the second term of the contraction lemma. -/
lemma add_sq_le_weighted {δ x y : ℝ} (hδ : 0 < δ) :
    (x + y) ^ 2 ≤ (1 + δ) * x ^ 2 + (1 + δ⁻¹) * y ^ 2 := by
  have hinv : δ * δ⁻¹ = 1 := mul_inv_cancel₀ hδ.ne'
  have key : δ * ((1 + δ) * x ^ 2 + (1 + δ⁻¹) * y ^ 2 - (x + y) ^ 2)
      = (δ * x - y) ^ 2 + (δ * δ⁻¹ - 1) * y ^ 2 := by ring
  have hS : 0 ≤ δ * ((1 + δ) * x ^ 2 + (1 + δ⁻¹) * y ^ 2 - (x + y) ^ 2) := by
    rw [key, hinv]
    nlinarith [sq_nonneg (δ * x - y)]
  have hD : (0 : ℝ) ≤ (1 + δ) * x ^ 2 + (1 + δ⁻¹) * y ^ 2 - (x + y) ^ 2 := by
    have h0 : δ * 0 ≤ δ * ((1 + δ) * x ^ 2 + (1 + δ⁻¹) * y ^ 2 - (x + y) ^ 2) := by
      rw [mul_zero]; exact hS
    exact le_of_mul_le_mul_left h0 hδ
  linarith

end GraphMarkovMatching.Support
