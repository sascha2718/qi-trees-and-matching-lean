/-
The scalar functions of `arbitrary_offspring_matching.tex` (`eq:mean-constants`,
`eq:four-law-constants`) and the pointwise inequalities of the four-law
contraction (`eq:four-law-product` to `eq:four-law-weight`):

* `Lfun α β = max_{0 ≤ q ≤ 1} (q/(1+q)^α + β (1-q)^α)`, as a supremum;
* `Kfun α β = α^α/(α+1)^{α+1} (1-β)^{α+1}`, the maximum of `(q-β)(1-q)^α` on `[0,1]`;
* `lambda α = 2 min_{0 ≤ β ≤ 1} (Lfun α β + Kfun α β)`, the exponent condition `lambda α < 1`;
* `Cfun α L0 u = 4 L0 ((1-u)^{-α} - 1)/u + 4/u + 8α + 2α²`, the quadratic coefficient;
* `phi_sq_le`, `phi_mul_le_beta`: `φ(q²) ≤ L φ(q) - β q` and the product bound
  `φ(xy) ≤ (L/2)(φ(x) + φ(y)) - (β/2)(x + y)`;
* `sq_le_K_phi_add`: `q² ≤ K φ(q) + β q`;
* `chord_gen`: the chord `(1-s)^{-α} ≤ 1 + c s` on `[0,u]`, `c = ((1-u)^{-α} - 1)/u`;
* `rpow_one_sub_le`: `s^{1-α} ≤ 1 + (α-1)(1-s)/s^α` on `(0,1]`;
* the explicit values of `Lfun α 0` and the closed form of `Kfun` as a maximum;
* `exists_beta_of_lambda_lt_one`, `exists_beta_min`: a minimising `β` exists, and the
  exponent condition supplies a `β` with `2 (L + K) < 1`;
* `amgm_pow`: weighted AM–GM in the power form `y x^γ ≤ ((y + γx)/(γ+1))^{γ+1}`, behind
  both the maximum `K_α(β)` and the value of `L_α` for `α ≥ 2`.

The parameters `L`, `K`, `L0` enter the four-law contraction as hypotheses (the bounds
`le_Lfun`, `Kfun_bound`, `le_Lfun` at `β = 0`), so that rational surrogates can replace
the exact maxima in numerical instances.
-/
import GraphMarkovMatching.Support.Phi
import GraphMarkovMatching.Potential.Directed

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching.Support Real

/-! ### The scalar functions -/

/-- The summand of `L_α(β)` at `q`. -/
noncomputable def Lsummand (α β q : ℝ) : ℝ := q / (1 + q) ^ α + β * (1 - q) ^ α

/-- `L_α(β) = max_{0 ≤ q ≤ 1} (q/(1+q)^α + β(1-q)^α)` (`eq:mean-constants`). -/
noncomputable def Lfun (α β : ℝ) : ℝ := sSup (Lsummand α β '' Set.Icc 0 1)

/-- `K_α(β) = α^α/(α+1)^{α+1} (1-β)^{α+1}` (`eq:mean-constants`). -/
noncomputable def Kfun (α β : ℝ) : ℝ := α ^ α / (α + 1) ^ (α + 1) * (1 - β) ^ (α + 1)

/-- `λ_α = 2 min_{0 ≤ β ≤ 1} (L_α(β) + K_α(β))` (`eq:mean-constants`). -/
noncomputable def lambda (α : ℝ) : ℝ :=
  2 * sInf ((fun β => Lfun α β + Kfun α β) '' Set.Icc 0 1)

/-- The quadratic coefficient `C_α(u)` of `eq:four-law-constants`, with `L_α` as a
parameter `L0`. -/
noncomputable def Cfun (α L0 u : ℝ) : ℝ :=
  4 * L0 * ((1 - u) ^ (-α) - 1) / u + 4 / u + 8 * α + 2 * α ^ 2

/-- The chord slope `c = ((1-u)^{-α} - 1)/u`. -/
noncomputable def chordSlope (α u : ℝ) : ℝ := ((1 - u) ^ (-α) - 1) / u

/-! ### Weighted AM–GM in power form

`y x^γ ≤ ((y + γ x)/(γ+1))^{γ+1}` for `x, y ≥ 0` and `γ ≥ 0`: the two-point weighted
AM–GM inequality with weights `1/(γ+1)`, `γ/(γ+1)`, raised to the power `γ + 1`. It
supplies the maximum of `(q-β)(1-q)^α` (`Kfun_bound`) and the value of `L_α` for
`α ≥ 2` (`Lfun_zero_eq_of_two_le`). -/

/-- Weighted AM–GM in power form (`thm:four-law-contraction`). -/
lemma amgm_pow {γ x y : ℝ} (hγ : 0 ≤ γ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y * x ^ γ ≤ ((y + γ * x) / (γ + 1)) ^ (γ + 1) := by
  have hγ1 : (0 : ℝ) < γ + 1 := by linarith
  have hw₁ : (0 : ℝ) ≤ 1 / (γ + 1) := by positivity
  have hw₂ : (0 : ℝ) ≤ γ / (γ + 1) := by positivity
  have hw : 1 / (γ + 1) + γ / (γ + 1) = 1 := by
    rw [← add_div, add_comm, div_self hγ1.ne']
  have h := Real.geom_mean_le_arith_mean2_weighted hw₁ hw₂ hy hx hw
  have hG : 0 ≤ y ^ (1 / (γ + 1)) * x ^ (γ / (γ + 1)) :=
    mul_nonneg (Real.rpow_nonneg hy _) (Real.rpow_nonneg hx _)
  have h2 := Real.rpow_le_rpow hG h hγ1.le
  have e1 : (y ^ (1 / (γ + 1)) * x ^ (γ / (γ + 1))) ^ (γ + 1) = y * x ^ γ := by
    rw [Real.mul_rpow (Real.rpow_nonneg hy _) (Real.rpow_nonneg hx _),
      ← Real.rpow_mul hy, ← Real.rpow_mul hx]
    have e2 : 1 / (γ + 1) * (γ + 1) = 1 := by field_simp
    have e3 : γ / (γ + 1) * (γ + 1) = γ := by field_simp
    rw [e2, e3, Real.rpow_one]
  have e4 : 1 / (γ + 1) * y + γ / (γ + 1) * x = (y + γ * x) / (γ + 1) := by
    field_simp
  rw [e1, e4] at h2
  exact h2

/-! ### The suprema -/

/-- The summand of `L_α(β)` is nonnegative on `[0,1]`. -/
lemma Lsummand_nonneg {α β q : ℝ} (hβ : 0 ≤ β) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ Lsummand α β q := by
  unfold Lsummand
  have h1 : 0 ≤ q / (1 + q) ^ α := div_nonneg hq0 (Real.rpow_nonneg (by linarith) α)
  have h2 : 0 ≤ β * (1 - q) ^ α := mul_nonneg hβ (Real.rpow_nonneg (by linarith) α)
  linarith

/-- The summand of `L_α(β)` is at most `1 + β` on `[0,1]`, so the supremum is finite. -/
lemma Lsummand_le {α β q : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Lsummand α β q ≤ 1 + β := by
  unfold Lsummand
  have h1 : (1 : ℝ) ≤ (1 + q) ^ α := Real.one_le_rpow (by linarith) hα
  have h2 : (1 - q) ^ α ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) hα
  have h3 : q / (1 + q) ^ α ≤ q := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h4 : β * (1 - q) ^ α ≤ β := by
    have := mul_le_mul_of_nonneg_left h2 hβ
    linarith
  linarith

/-- Every summand is at most `L_α(β)`. -/
lemma le_Lfun {α β q : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Lsummand α β q ≤ Lfun α β := by
  apply le_csSup
  · refine ⟨1 + β, ?_⟩
    rintro _ ⟨q', ⟨hq'0, hq'1⟩, rfl⟩
    exact Lsummand_le hα hβ hq'0 hq'1
  · exact ⟨q, ⟨hq0, hq1⟩, rfl⟩

/-- `L_α(β)` is the least upper bound. -/
lemma Lfun_le {α β L : ℝ} (hL : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α β q ≤ L) :
    Lfun α β ≤ L := by
  apply csSup_le
  · exact ⟨Lsummand α β 0, 0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
  · rintro _ ⟨q', ⟨hq'0, hq'1⟩, rfl⟩
    exact hL q' hq'0 hq'1

/-- `0 ≤ L_α(β)`. -/
lemma Lfun_nonneg {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) : 0 ≤ Lfun α β :=
  (Lsummand_nonneg (α := α) hβ (le_refl 0) zero_le_one).trans
    (le_Lfun hα hβ (le_refl 0) zero_le_one)

/-- `β ≤ L_α(β)` (take `q = 0`). -/
lemma beta_le_Lfun {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) : β ≤ Lfun α β := by
  have h := le_Lfun (α := α) hα hβ (le_refl 0) zero_le_one
  have e : Lsummand α β 0 = β := by
    unfold Lsummand
    simp
  rw [e] at h
  exact h

/-- `2^{-α} ≤ L_α(β)` (take `q = 1`). -/
lemma two_rpow_neg_le_Lfun {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (2 : ℝ) ^ (-α) ≤ Lfun α β := by
  have h := le_Lfun (α := α) hα hβ zero_le_one (le_refl 1)
  have e : (2 : ℝ) ^ (-α) ≤ Lsummand α β 1 := by
    unfold Lsummand
    rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      inv_eq_one_div]
    exact le_add_of_nonneg_right (mul_nonneg hβ (Real.rpow_nonneg (by norm_num) α))
  exact e.trans h

/-- `L_α(β) ≤ 1/2 + β` for `α ≥ 1`. -/
lemma Lfun_le_half_add {α β : ℝ} (hα : 1 ≤ α) (hβ : 0 ≤ β) : Lfun α β ≤ 1 / 2 + β := by
  apply Lfun_le
  intro q hq0 hq1
  unfold Lsummand
  have h1 : (1 + q) ^ (1 : ℝ) ≤ (1 + q) ^ α :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hα
  rw [Real.rpow_one] at h1
  have h2 : (1 - q) ^ α ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (by linarith)
  have h3 : q / (1 + q) ^ α ≤ q / (1 + q) :=
    div_le_div_of_nonneg_left hq0 (by linarith) h1
  have h4 : q / (1 + q) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h5 : β * (1 - q) ^ α ≤ β := by
    have := mul_le_mul_of_nonneg_left h2 hβ
    linarith
  linarith

/-- `v (1-v)^α ≤ α^α/(α+1)^{α+1}` on `[0,1]` for `α > 0`: the normalised form of
`Kfun_bound`, from `amgm_pow` at `y = (α+1) v`, `x = (α+1)(1-v)/α`. -/
lemma mul_one_sub_rpow_le {α v : ℝ} (hα : 0 < α) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    v * (1 - v) ^ α ≤ α ^ α / (α + 1) ^ (α + 1) := by
  have hα1 : (0 : ℝ) < α + 1 := by linarith
  have hv : 0 ≤ 1 - v := by linarith
  have hx : 0 ≤ (α + 1) * (1 - v) / α := div_nonneg (mul_nonneg hα1.le hv) hα.le
  have hy : 0 ≤ (α + 1) * v := mul_nonneg hα1.le hv0
  have h := amgm_pow hα.le hx hy
  have e1 : ((α + 1) * v + α * ((α + 1) * (1 - v) / α)) / (α + 1) = 1 := by
    field_simp
    ring
  rw [e1, Real.one_rpow] at h
  have e2 : (α + 1) * v * ((α + 1) * (1 - v) / α) ^ α
      = (α + 1) ^ (α + 1) * (v * (1 - v) ^ α) / α ^ α := by
    rw [Real.div_rpow (mul_nonneg hα1.le hv) hα.le, Real.mul_rpow hα1.le hv,
      Real.rpow_add_one' hα1.le hα1.ne']
    field_simp
  rw [e2, div_le_iff₀ (Real.rpow_pos_of_pos hα α), one_mul] at h
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hα1 _)]
  linarith

/-- `0 ≤ K_α(β)` for `β ≤ 1`. -/
lemma Kfun_nonneg {α β : ℝ} (hα : 0 ≤ α) (hβ1 : β ≤ 1) : 0 ≤ Kfun α β := by
  unfold Kfun
  have h1 : 0 ≤ α ^ α := Real.rpow_nonneg hα α
  have h2 : 0 ≤ (α + 1) ^ (α + 1) := Real.rpow_nonneg (by linarith) _
  have h3 : 0 ≤ (1 - β) ^ (α + 1) := Real.rpow_nonneg (by linarith) _
  exact mul_nonneg (div_nonneg h1 h2) h3

/-- The maximum of `(q - β)(1-q)^α` on `[0,1]` is `K_α(β)` (`thm:four-law-contraction`):
weighted AM–GM at `v = (q-β)/(1-β)`. -/
lemma Kfun_bound {α β q : ℝ} (hα : 1 ≤ α) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : (q - β) * (1 - q) ^ α ≤ Kfun α β := by
  -- `hβ0` and `hq0` belong to the interface; the bound holds without them
  have _ := hβ0
  have _ := hq0
  have hK : 0 ≤ Kfun α β := Kfun_nonneg (by linarith) hβ1
  have hpow : 0 ≤ (1 - q) ^ α := Real.rpow_nonneg (by linarith) α
  rcases lt_or_ge q β with hqβ | hqβ
  · have h0 : (q - β) * (1 - q) ^ α ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hpow
    exact h0.trans hK
  rcases eq_or_lt_of_le hβ1 with hβeq | hβlt
  · have h0 : (q - β) * (1 - q) ^ α ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hpow
    exact h0.trans hK
  have h1β : (0 : ℝ) < 1 - β := by linarith
  set v : ℝ := (q - β) / (1 - β) with hv_def
  have hv0 : 0 ≤ v := div_nonneg (by linarith) h1β.le
  have hv1 : v ≤ 1 := by
    rw [hv_def, div_le_one h1β]
    linarith
  have hqβ' : q - β = (1 - β) * v := by
    rw [hv_def]
    field_simp
  have h1q : 1 - q = (1 - β) * (1 - v) := by
    rw [hv_def]
    field_simp
    ring
  rw [hqβ', h1q, Real.mul_rpow h1β.le (by linarith), Kfun,
    Real.rpow_add_one' h1β.le (by linarith)]
  have hm := mul_one_sub_rpow_le (α := α) (by linarith) hv0 hv1
  have hpos : 0 ≤ (1 - β) ^ α * (1 - β) := mul_nonneg (Real.rpow_nonneg h1β.le α) h1β.le
  calc (1 - β) * v * ((1 - β) ^ α * (1 - v) ^ α)
      = (1 - β) ^ α * (1 - β) * (v * (1 - v) ^ α) := by ring
    _ ≤ (1 - β) ^ α * (1 - β) * (α ^ α / (α + 1) ^ (α + 1)) :=
        mul_le_mul_of_nonneg_left hm hpos
    _ = α ^ α / (α + 1) ^ (α + 1) * ((1 - β) ^ α * (1 - β)) := by ring

/-- The bound `K_α(β)` is attained, at `q = β + (1-β)/(α+1)`. -/
lemma Kfun_attained {α β : ℝ} (hα : 1 ≤ α) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∃ q, 0 ≤ q ∧ q ≤ 1 ∧ (q - β) * (1 - q) ^ α = Kfun α β := by
  have hα1 : (0 : ℝ) < α + 1 := by linarith
  have h1β : (0 : ℝ) ≤ 1 - β := by linarith
  refine ⟨β + (1 - β) / (α + 1), by positivity, ?_, ?_⟩
  · have : (1 - β) / (α + 1) ≤ 1 - β := div_le_self h1β (by linarith)
    linarith
  · have e1 : β + (1 - β) / (α + 1) - β = (1 - β) / (α + 1) := by ring
    have e2 : 1 - (β + (1 - β) / (α + 1)) = (1 - β) * (α / (α + 1)) := by
      field_simp
      ring
    rw [e1, e2, Real.mul_rpow h1β (by positivity), Real.div_rpow (by linarith) hα1.le, Kfun,
      Real.rpow_add_one' (x := α + 1) hα1.le hα1.ne', Real.rpow_add_one' (x := 1 - β) h1β hα1.ne']
    field_simp

/-- `K_α(0) ≤ 1/4` for `α ≥ 1`. -/
lemma Kfun_zero_le_quarter {α : ℝ} (hα : 1 ≤ α) : Kfun α 0 ≤ 1 / 4 := by
  obtain ⟨q, hq0, hq1, hq⟩ := Kfun_attained hα (le_refl 0) zero_le_one
  rw [← hq, sub_zero]
  have h1 : (1 - q) ^ α ≤ (1 - q) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' (by linarith) (by linarith) zero_le_one hα
  rw [Real.rpow_one] at h1
  have h2 : q * (1 - q) ^ α ≤ q * (1 - q) := mul_le_mul_of_nonneg_left h1 hq0
  nlinarith [sq_nonneg (q - 1 / 2)]

/-- `L_α(β) ≤ L_α(β') + |β - β'|`: one half of the Lipschitz bound. -/
lemma Lfun_le_add_abs {α β β' : ℝ} (hα : 0 ≤ α) (hβ' : 0 ≤ β') :
    Lfun α β ≤ Lfun α β' + |β - β'| := by
  apply Lfun_le
  intro q hq0 hq1
  have h1 : Lsummand α β' q ≤ Lfun α β' := le_Lfun hα hβ' hq0 hq1
  have h2 : Lsummand α β q = Lsummand α β' q + (β - β') * (1 - q) ^ α := by
    unfold Lsummand; ring
  have h3 : (1 - q) ^ α ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) hα
  have h4 : 0 ≤ (1 - q) ^ α := Real.rpow_nonneg (by linarith) α
  have h5 : (β - β') * (1 - q) ^ α ≤ |β - β'| := by
    calc (β - β') * (1 - q) ^ α ≤ |β - β'| * (1 - q) ^ α :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h4
      _ ≤ |β - β'| * 1 := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = |β - β'| := mul_one _
  linarith

/-- `L_α(β)` is `1`-Lipschitz in `β`. -/
lemma Lfun_lipschitz {α β β' : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hβ' : 0 ≤ β') :
    |Lfun α β - Lfun α β'| ≤ |β - β'| := by
  rw [abs_sub_le_iff]
  constructor
  · have := Lfun_le_add_abs (β := β) (β' := β') hα hβ'
    linarith
  · have := Lfun_le_add_abs (β := β') (β' := β) hα hβ
    rw [abs_sub_comm] at this
    linarith

/-- `β ↦ L_α(β) + K_α(β)` is continuous on `[0,1]`. -/
lemma continuousOn_Lfun_add_Kfun {α : ℝ} (hα : 0 ≤ α) :
    ContinuousOn (fun β => Lfun α β + Kfun α β) (Set.Icc 0 1) := by
  apply ContinuousOn.add
  · have hL : LipschitzOnWith 1 (Lfun α) (Set.Icc 0 1) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      rw [Real.dist_eq, Real.dist_eq]
      simpa using Lfun_lipschitz hα hx.1 hy.1
    exact hL.continuousOn
  · apply Continuous.continuousOn
    unfold Kfun
    apply Continuous.mul continuous_const
    exact (Real.continuous_rpow_const (by linarith)).comp (continuous_const.sub continuous_id)

/-- The minimum in `λ_α` is attained (`sec:exponent-values`: compactness). -/
lemma exists_beta_min {α : ℝ} (hα : 1 ≤ α) :
    ∃ β, 0 ≤ β ∧ β ≤ 1 ∧ lambda α = 2 * (Lfun α β + Kfun α β)
      ∧ ∀ β', 0 ≤ β' → β' ≤ 1 → Lfun α β + Kfun α β ≤ Lfun α β' + Kfun α β' := by
  obtain ⟨β, ⟨hβ0, hβ1⟩, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr zero_le_one)
    (continuousOn_Lfun_add_Kfun (α := α) (by linarith))
  rw [isMinOn_iff] at hmin
  refine ⟨β, hβ0, hβ1, ?_, fun β' h0 h1 => hmin β' ⟨h0, h1⟩⟩
  unfold lambda
  congr 1
  apply IsLeast.csInf_eq
  refine ⟨⟨β, ⟨hβ0, hβ1⟩, rfl⟩, ?_⟩
  rintro _ ⟨β', hβ', rfl⟩
  exact hmin β' hβ'

/-- `λ_α ≤ 2 (L_α(β) + K_α(β))` for every admissible `β`. -/
lemma lambda_le {α β : ℝ} (hα : 1 ≤ α) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    lambda α ≤ 2 * (Lfun α β + Kfun α β) := by
  obtain ⟨β₀, _, _, hlam, hmin⟩ := exists_beta_min hα
  rw [hlam]
  have := hmin β hβ0 hβ1
  linarith

/-- The exponent condition supplies a `β` with linear coefficient below one. -/
lemma exists_beta_of_lambda_lt_one {α : ℝ} (hα : 1 ≤ α) (h : lambda α < 1) :
    ∃ β, 0 ≤ β ∧ β ≤ 1 ∧ 2 * (Lfun α β + Kfun α β) < 1 := by
  obtain ⟨β, hβ0, hβ1, hlam, _⟩ := exists_beta_min hα
  exact ⟨β, hβ0, hβ1, hlam ▸ h⟩

/-! ### The explicit value of `L_α = L_α(0)` -/

/-- `L_α = 2^{-α}` for `1 ≤ α ≤ 2`. -/
lemma Lfun_zero_eq_of_le_two {α : ℝ} (hα1 : 1 ≤ α) (hα2 : α ≤ 2) :
    Lfun α 0 = (2 : ℝ) ^ (-α) := by
  apply le_antisymm
  · apply Lfun_le
    intro q hq0 hq1
    unfold Lsummand
    rw [zero_mul, add_zero, Real.rpow_neg (by norm_num), inv_eq_one_div]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ α := Real.rpow_pos_of_pos two_pos α
    have hq : (0 : ℝ) < (1 + q) ^ α := Real.rpow_pos_of_pos (by linarith) α
    rw [div_le_div_iff₀ hq h2, one_mul]
    -- `q 2^α ≤ (1+q)^α`, i.e. `q ≤ ((1+q)/2)^α`, and `((1+q)/2)^α ≥ ((1+q)/2)^2 ≥ q`
    have hx0 : (0 : ℝ) ≤ (1 + q) / 2 := by linarith
    have hx1 : (1 + q) / 2 ≤ 1 := by linarith
    have h3 : ((1 + q) / 2) ^ (2 : ℝ) ≤ ((1 + q) / 2) ^ α :=
      Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 (by linarith) hα2
    rw [Real.rpow_two] at h3
    have h4 : q ≤ ((1 + q) / 2) ^ 2 := by nlinarith [sq_nonneg (1 - q)]
    have h5 : ((1 + q) / 2) ^ α = (1 + q) ^ α / 2 ^ α :=
      Real.div_rpow (by linarith) (by norm_num) α
    rw [h5] at h3
    have h6 : q ≤ (1 + q) ^ α / 2 ^ α := h4.trans h3
    rw [le_div_iff₀ h2] at h6
    exact h6
  · exact two_rpow_neg_le_Lfun (by linarith) (le_refl 0)

/-- `L_α = (α-1)^{α-1}/α^α` for `α ≥ 2`. -/
lemma Lfun_zero_eq_of_two_le {α : ℝ} (hα : 2 ≤ α) :
    Lfun α 0 = (α - 1) ^ (α - 1) / α ^ α := by
  have hα1 : (0 : ℝ) < α - 1 := by linarith
  have hα0 : (0 : ℝ) < α := by linarith
  have hP : 0 < (α - 1) ^ (α - 1) := Real.rpow_pos_of_pos hα1 _
  have hPα : 0 < α ^ α := Real.rpow_pos_of_pos hα0 _
  apply le_antisymm
  · apply Lfun_le
    intro q hq0 hq1
    unfold Lsummand
    rw [zero_mul, add_zero]
    have hx : 0 ≤ α / (α - 1) := div_nonneg hα0.le hα1.le
    have hy : 0 ≤ α * q := mul_nonneg hα0.le hq0
    have h := amgm_pow hα1.le hx hy
    have e1 : (α * q + (α - 1) * (α / (α - 1))) / (α - 1 + 1) = 1 + q := by
      field_simp
      ring
    have e2 : α - 1 + 1 = α := by ring
    rw [e1, e2, Real.div_rpow hα0.le hα1.le, Real.rpow_sub_one hα0.ne' α] at h
    -- `h : α q (α^α/α)/(α-1)^{α-1} ≤ (1+q)^α`
    have hq : (0 : ℝ) < (1 + q) ^ α := Real.rpow_pos_of_pos (by linarith) α
    rw [div_le_div_iff₀ hq hPα]
    have e3 : α * q * (α ^ α / α / (α - 1) ^ (α - 1)) = q * α ^ α / (α - 1) ^ (α - 1) := by
      field_simp
    rw [e3, div_le_iff₀ hP] at h
    linarith
  · have hq0 : 0 ≤ 1 / (α - 1) := div_nonneg zero_le_one hα1.le
    have hq1 : 1 / (α - 1) ≤ 1 := by
      rw [div_le_one hα1]
      linarith
    have h := le_Lfun (α := α) (β := 0) hα0.le (le_refl 0) hq0 hq1
    have e : Lsummand α 0 (1 / (α - 1)) = (α - 1) ^ (α - 1) / α ^ α := by
      unfold Lsummand
      rw [zero_mul, add_zero]
      have e1 : 1 + 1 / (α - 1) = α / (α - 1) := by
        field_simp
        ring
      rw [e1, Real.div_rpow hα0.le hα1.le, Real.rpow_sub_one hα1.ne' α]
      field_simp
    rw [e] at h
    exact h

/-! ### The pointwise inequalities of the four-law contraction -/

/-- `φ_α(q²) = φ_α(q) · q/(1+q)^α` on `[0,1)`. -/
lemma phi_sq_eq {α q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    phi α (q ^ 2) = phi α q * (q / (1 + q) ^ α) := by
  have hfac : (1 - q ^ 2) ^ α = (1 - q) ^ α * (1 + q) ^ α := by
    rw [show (1 : ℝ) - q ^ 2 = (1 - q) * (1 + q) from by ring,
      Real.mul_rpow (by linarith) (by linarith)]
  simp only [phi]
  rw [hfac, div_mul_div_comm, sq]

/-- `φ_α(q²) ≤ L φ_α(q) - β q` under the `L`-hypothesis. -/
lemma phi_sq_le {α β L q : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hL : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α β q ≤ L) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    phi α (q ^ 2) ≤ L * phi α q - β * q := by
  -- `hα` and `hβ` belong to the interface; the identity `phi_sq_eq` needs neither
  have _ := hα
  have _ := hβ
  have h := hL q hq0 hq1.le
  unfold Lsummand at h
  rw [phi_sq_eq hq0 hq1]
  have hp : 0 ≤ phi α q := phi_nonneg hq0 hq1
  have hphi : phi α q * (1 - q) ^ α = q := by
    rw [phi, div_mul_cancel₀ _ (rpow_denom_pos α hq1).ne']
  have h2 : phi α q * (q / (1 + q) ^ α) ≤ phi α q * (L - β * (1 - q) ^ α) :=
    mul_le_mul_of_nonneg_left (by linarith) hp
  calc phi α q * (q / (1 + q) ^ α) ≤ phi α q * (L - β * (1 - q) ^ α) := h2
    _ = L * phi α q - β * (phi α q * (1 - q) ^ α) := by ring
    _ = L * phi α q - β * q := by rw [hphi]

/-- `φ_α(xy) ≤ (φ_α(x²) + φ_α(y²))/2`: the geometric-mean step of the product bound
(`eq:four-law-product`), from `(1-xy)² - (1-x²)(1-y²) = (x-y)²`. -/
lemma phi_mul_le_half_sq {α x y : ℝ} (hα : 0 ≤ α) (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y)
    (hy1 : y < 1) : phi α (x * y) ≤ (phi α (x ^ 2) + phi α (y ^ 2)) / 2 := by
  have hx2 : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  have hy2 : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hAx : (0 : ℝ) < (1 - x ^ 2) ^ (α / 2) := Real.rpow_pos_of_pos hx2 _
  have hAy : (0 : ℝ) < (1 - y ^ 2) ^ (α / 2) := Real.rpow_pos_of_pos hy2 _
  set a : ℝ := x / (1 - x ^ 2) ^ (α / 2) with ha_def
  set b : ℝ := y / (1 - y ^ 2) ^ (α / 2) with hb_def
  have hsq : ∀ z : ℝ, 0 < z → ((z ^ (α / 2) : ℝ)) ^ 2 = z ^ α := by
    intro z hz
    rw [sq, ← Real.rpow_add hz]
    congr 1
    ring
  have ha2 : a ^ 2 = phi α (x ^ 2) := by
    rw [ha_def, div_pow, hsq _ hx2, phi]
  have hb2 : b ^ 2 = phi α (y ^ 2) := by
    rw [hb_def, div_pow, hsq _ hy2, phi]
  have hden : (1 - x ^ 2) ^ (α / 2) * (1 - y ^ 2) ^ (α / 2) ≤ (1 - x * y) ^ α := by
    have h1 : (1 - x ^ 2) ^ (α / 2) * (1 - y ^ 2) ^ (α / 2)
        = ((1 - x ^ 2) * (1 - y ^ 2)) ^ (α / 2) :=
      (Real.mul_rpow hx2.le hy2.le).symm
    have h2 : (1 - x * y) ^ α = ((1 - x * y) ^ 2) ^ (α / 2) := by
      rw [← Real.rpow_natCast (1 - x * y) 2, ← Real.rpow_mul (by nlinarith)]
      congr 1
      push_cast
      ring
    rw [h1, h2]
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    nlinarith [sq_nonneg (x - y)]
  have hstep1 : phi α (x * y) ≤ a * b := by
    rw [phi, ha_def, hb_def, div_mul_div_comm]
    exact div_le_div_of_nonneg_left hxy0 (by positivity) hden
  have hstep2 : a * b ≤ (phi α (x ^ 2) + phi α (y ^ 2)) / 2 := by
    rw [← ha2, ← hb2]
    nlinarith [sq_nonneg (a - b)]
  exact hstep1.trans hstep2

/-- **The product bound** (`eq:four-law-product`):
`φ_α(xy) ≤ (L/2)(φ_α(x) + φ_α(y)) - (β/2)(x + y)`. -/
lemma phi_mul_le_beta {α β L x y : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hL : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α β q ≤ L)
    (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    phi α (x * y) ≤ L / 2 * (phi α x + phi α y) - β / 2 * (x + y) := by
  have h1 := phi_mul_le_half_sq hα hx0 hx1 hy0 hy1
  have hx := phi_sq_le hα hβ hL hx0 hx1
  have hy := phi_sq_le hα hβ hL hy0 hy1
  linarith

/-- **The square bound** (`eq:four-law-square`): `q² ≤ K φ_α(q) + β q`. -/
lemma sq_le_K_phi_add {α β K q : ℝ} (hα : 0 ≤ α)
    (hK : ∀ q, 0 ≤ q → q ≤ 1 → (q - β) * (1 - q) ^ α ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    q ^ 2 ≤ K * phi α q + β * q := by
  -- `hα` belongs to the interface; the argument needs only the `K`-hypothesis
  have _ := hα
  have h := hK q hq0 hq1.le
  have hp : 0 ≤ phi α q := phi_nonneg hq0 hq1
  have hphi : phi α q * (1 - q) ^ α = q := by
    rw [phi, div_mul_cancel₀ _ (rpow_denom_pos α hq1).ne']
  have h2 : (q - β) * (1 - q) ^ α * phi α q ≤ K * phi α q :=
    mul_le_mul_of_nonneg_right h hp
  have e : (q - β) * (1 - q) ^ α * phi α q = (q - β) * q := by
    rw [mul_assoc, mul_comm ((1 - q) ^ α), hphi]
  rw [e] at h2
  linarith

/-- The chord slope is nonnegative: `(1-u)^{-α} ≥ 1` for `u ∈ (0,1)`. -/
lemma chordSlope_nonneg {α u : ℝ} (hα : 0 ≤ α) (hu0 : 0 < u) (hu1 : u < 1) :
    0 ≤ chordSlope α u := by
  unfold chordSlope
  have h : (1 : ℝ) ≤ (1 - u) ^ (-α) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) (by linarith)
  exact div_nonneg (by linarith) hu0.le

/-- **The chord bound** on `[0,u]`: `(1-s)^{-α} ≤ 1 + c s` with `c = ((1-u)^{-α} - 1)/u`,
by concavity of the logarithm. -/
lemma chord_gen {α u s : ℝ} (hα : 0 ≤ α) (hu0 : 0 < u) (hu1 : u < 1) (hs0 : 0 ≤ s)
    (hsu : s ≤ u) : (1 - s) ^ (-α) ≤ 1 + chordSlope α u * s := by
  have hs1 : (0 : ℝ) < 1 - s := by linarith
  have hP : 0 < (1 - s) ^ α := rpow_denom_pos α (by linarith)
  have hcs : (0 : ℝ) < 1 + chordSlope α u * s := by
    have := mul_nonneg (chordSlope_nonneg hα hu0 hu1) hs0
    linarith
  rw [Real.rpow_neg hs1.le, inv_eq_one_div, div_le_iff₀ hP]
  -- concavity of log with weights `(1 - s/u, s/u)`
  have hconc : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have ha : (0 : ℝ) ≤ 1 - s / u := by
    rw [sub_nonneg, div_le_one hu0]; exact hsu
  have hb : (0 : ℝ) ≤ s / u := div_nonneg hs0 hu0.le
  have hab : (1 - s / u) + s / u = 1 := by ring
  have hx1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hu' : (0 : ℝ) < 1 - u := by linarith
  -- first application: points `1` and `(1-u)^{-α}`, giving `log (1 + c s)`
  have hy1 : (1 - u) ^ (-α) ∈ Set.Ioi (0 : ℝ) := Real.rpow_pos_of_pos hu' _
  have hlog1 : (1 - s / u) * Real.log 1 + (s / u) * Real.log ((1 - u) ^ (-α))
      ≤ Real.log ((1 - s / u) * 1 + (s / u) * (1 - u) ^ (-α)) := by
    have := hconc.2 hx1 hy1 ha hb hab
    simpa [smul_eq_mul] using this
  have he1 : (1 - s / u) * 1 + (s / u) * (1 - u) ^ (-α) = 1 + chordSlope α u * s := by
    unfold chordSlope
    field_simp
    ring
  have hl1 : (s / u) * (-α * Real.log (1 - u)) ≤ Real.log (1 + chordSlope α u * s) := by
    rw [he1, Real.log_one, Real.log_rpow hu'] at hlog1
    linarith [hlog1]
  -- second application: points `1` and `1 - u`, giving `log (1 - s)`
  have hy2 : (1 - u) ∈ Set.Ioi (0 : ℝ) := hu'
  have hlog2 : (1 - s / u) * Real.log 1 + (s / u) * Real.log (1 - u)
      ≤ Real.log ((1 - s / u) * 1 + (s / u) * (1 - u)) := by
    have := hconc.2 hx1 hy2 ha hb hab
    simpa [smul_eq_mul] using this
  have he2 : (1 - s / u) * 1 + (s / u) * (1 - u) = 1 - s := by
    field_simp
    ring
  have hl2 : (s / u) * Real.log (1 - u) ≤ Real.log (1 - s) := by
    rw [he2, Real.log_one] at hlog2
    linarith [hlog2]
  have hl2' : α * ((s / u) * Real.log (1 - u)) ≤ α * Real.log (1 - s) :=
    mul_le_mul_of_nonneg_left hl2 hα
  have hsum : 0 ≤ Real.log (1 + chordSlope α u * s) + α * Real.log (1 - s) := by
    nlinarith [hl1, hl2']
  have hprod : (1 + chordSlope α u * s) * (1 - s) ^ α
      = Real.exp (Real.log (1 + chordSlope α u * s) + α * Real.log (1 - s)) := by
    rw [Real.exp_add, Real.exp_log hcs, Real.rpow_def_of_pos hs1, mul_comm α]
  rw [hprod]
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (Real.log (1 + chordSlope α u * s) + α * Real.log (1 - s)) :=
        Real.exp_le_exp.mpr hsum

/-- `s^{1-α} ≤ 1 + (α-1)(1-s)/s^α` on `(0,1]` (`sec:independent-root`), from
`s - s^α ≤ (α-1)(1-s)`. -/
lemma rpow_one_sub_le {α s : ℝ} (hα : 1 ≤ α) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    s ^ (1 - α) ≤ 1 + (α - 1) * ((1 - s) / s ^ α) := by
  -- `hs1` belongs to the interface; Bernoulli's inequality holds for every `s ≥ 0`
  have _ := hs1
  have hP : 0 < s ^ α := Real.rpow_pos_of_pos hs0 α
  have hB := one_sub_rpow_le hα hs0.le
  rw [Real.rpow_sub hs0, Real.rpow_one]
  have e : 1 + (α - 1) * ((1 - s) / s ^ α) = (s ^ α + (α - 1) * (1 - s)) / s ^ α := by
    field_simp
  rw [e, div_le_div_iff_of_pos_right hP]
  linarith

/-- The root identity `(1 - sr)/(sr)^α = (1-s)/s^α · r^{-α} + s^{1-α} (1-r)/r^α`
(`sec:independent-root`). -/
lemma root_split {α s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    (1 - s * r) / (s * r) ^ α
      = (1 - s) / s ^ α * r ^ (-α) + s ^ (1 - α) * ((1 - r) / r ^ α) := by
  have hsP : 0 < s ^ α := Real.rpow_pos_of_pos hs α
  have hrP : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  rw [Real.mul_rpow hs.le hr.le, Real.rpow_neg hr.le, Real.rpow_sub hs, Real.rpow_one]
  field_simp
  ring

/-- `C_α(u)` is nonnegative. -/
lemma Cfun_nonneg {α L0 u : ℝ} (hα : 0 ≤ α) (hL0 : 0 ≤ L0) (hu0 : 0 < u) (hu1 : u < 1) :
    0 ≤ Cfun α L0 u := by
  unfold Cfun
  have h : (1 : ℝ) ≤ (1 - u) ^ (-α) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) (by linarith)
  have h1 : 0 ≤ 4 * L0 * ((1 - u) ^ (-α) - 1) / u :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hu0.le
  have h2 : 0 ≤ 4 / u := by positivity
  have h3 : 0 ≤ 8 * α := by linarith
  have h4 : 0 ≤ 2 * α ^ 2 := by positivity
  linarith

end GraphMarkovMatching.Stopped
