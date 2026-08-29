/-
The two calculus constants of the contraction (the `L_α`, `K_α` of
`arbitrary_offspring_matching.tex` `thm:four-law`) at a free exponent, in the
generous rational forms the development needs:

    L_le : t/(1+t)^α ≤ 1/(2α)   for α ≥ 2, t ≥ 0
    K_le : t·(1-t)^α ≤ 1/(2α)   for α > 0, t ∈ [0,1]

together with the sharp `α = 2` instance `K_two : t(1-t)² ≤ 4/27` needed
by the parameter menu at `k = 1`.

Both general bounds avoid `deriv` and any argmax entirely:

* `L_le` is Bernoulli-then-square: `(1+t)^α = ((1+t)^{α/2})² ≥
  (1 + (α/2)t)² ≥ 2αt`, the last step being `(1-s)² ≥ 0` at `s = (α/2)t`.
  At `α = 2` this is tight: `L(2) = 1/4 = 1/(2·2)`.
* `K_le` goes through `(1-t)^α ≤ e^{-αt}` and `2s ≤ e^s`, the latter from
  `e^s = (e^{s/2})² ≥ (1+s/2)² ≥ 2s`.

The downstream consumer is the contraction constant
`A_δ(α) = 2L + 2(1+δ)K ≤ (2+δ)/α` and the `k = 1` menu instance
`A_{1/8}(2) = 1/2 + (9/4)(4/27) = 5/6 < 7/8`.
-/
import GraphMarkovMatching.Support.Phi

namespace GraphMarkovMatching.Support

open Real

/-- `t/(1+t)^α ≤ 1/(2α)` for `α ≥ 2` and `t ≥ 0`. Bernoulli at exponent
`α/2`, then the square trick `(1+s)² ≥ 4s`. Tight at `α = 2`, `t = 1`. -/
lemma L_le {α t : ℝ} (hα : 2 ≤ α) (h0 : 0 ≤ t) :
    t / (1 + t) ^ α ≤ 1 / (2 * α) := by
  have hαpos : (0 : ℝ) < α := by linarith
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hp : (0 : ℝ) < (1 + t) ^ α := Real.rpow_pos_of_pos h1t α
  have hhalf : (1 : ℝ) ≤ α / 2 := by linarith
  have hbern : 1 + α / 2 * t ≤ (1 + t) ^ (α / 2) :=
    one_add_mul_self_le_rpow_one_add (by linarith : (-1 : ℝ) ≤ t) hhalf
  have hsq : ((1 + t) ^ (α / 2)) ^ (2 : ℕ) = (1 + t) ^ α := by
    rw [← Real.rpow_natCast ((1 + t) ^ (α / 2)) 2, ← Real.rpow_mul h1t.le]
    norm_num
  have hb0 : (0 : ℝ) ≤ 1 + α / 2 * t := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ α / 2) h0
    linarith
  have hmono : (1 + α / 2 * t) ^ (2 : ℕ) ≤ ((1 + t) ^ (α / 2)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hb0 hbern 2
  have hexp : 2 * α * t ≤ (1 + α / 2 * t) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (1 - α / 2 * t)]
  have hkey : 2 * α * t ≤ (1 + t) ^ α := by
    calc 2 * α * t ≤ (1 + α / 2 * t) ^ (2 : ℕ) := hexp
    _ ≤ ((1 + t) ^ (α / 2)) ^ (2 : ℕ) := hmono
    _ = (1 + t) ^ α := hsq
  rw [div_le_div_iff₀ hp (by positivity : (0 : ℝ) < 2 * α)]
  nlinarith [hkey]

/-- `t·(1-t)^α ≤ 1/(2α)` for `α > 0` and `t ∈ [0,1]`, via `(1-t)^α ≤ e^{-αt}`
and `2s ≤ e^s`. -/
lemma K_le {α t : ℝ} (hα : 0 < α) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t * (1 - t) ^ α ≤ 1 / (2 * α) := by
  have hu : (0 : ℝ) ≤ 1 - t := by linarith
  -- `(1-t)^α ≤ exp(-(α t))`
  have hbase : 1 - t ≤ Real.exp (-t) := by
    have h := Real.add_one_le_exp (-t); linarith
  have hpow : (1 - t) ^ α ≤ Real.exp (-t) ^ α :=
    Real.rpow_le_rpow hu hbase hα.le
  have hexp : Real.exp (-t) ^ α = Real.exp (-(α * t)) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  -- `2 s ≤ exp s` at `s = α t`
  have h2s : 2 * (α * t) ≤ Real.exp (α * t) := by
    have hh := Real.add_one_le_exp (α * t / 2)
    have hsq : (1 + α * t / 2) ^ (2 : ℕ) ≤ Real.exp (α * t / 2) ^ (2 : ℕ) := by
      have hb0 : (0 : ℝ) ≤ 1 + α * t / 2 := by
        have := mul_nonneg hα.le h0
        linarith
      exact pow_le_pow_left₀ hb0 (by linarith) 2
    have hsq2 : Real.exp (α * t / 2) ^ (2 : ℕ) = Real.exp (α * t) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    nlinarith [sq_nonneg (1 - α * t / 2), hsq, hsq2]
  -- combine
  have hmul : t * (1 - t) ^ α ≤ t * Real.exp (-(α * t)) := by
    apply mul_le_mul_of_nonneg_left _ h0
    calc (1 - t) ^ α ≤ Real.exp (-t) ^ α := hpow
    _ = Real.exp (-(α * t)) := hexp
  have hepos : (0 : ℝ) < Real.exp (α * t) := Real.exp_pos _
  have hfinal : t * Real.exp (-(α * t)) ≤ 1 / (2 * α) := by
    rw [Real.exp_neg, ← div_eq_mul_inv,
      div_le_div_iff₀ hepos (by positivity : (0 : ℝ) < 2 * α)]
    nlinarith [h2s]
  linarith

/-- The sharp `α = 2` instance: `t(1-t)² ≤ 4/27` on `[0,1]`, attained at
`t = 1/3`. Certificate: `4 - 27 t (1-t)² = (3t-1)²(4-3t)`. Needed for the
`k = 1` menu entry `A_{1/8}(2) = 1/2 + (9/4)(4/27) = 5/6`. -/
lemma K_two {t : ℝ} (_h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t * (1 - t) ^ (2 : ℝ) ≤ 4 / 27 := by
  have hn : (1 - t) ^ (2 : ℝ) = (1 - t) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (1 - t) 2]
    norm_num
  rw [hn]
  nlinarith [mul_nonneg (sq_nonneg (3 * t - 1)) (by linarith : (0 : ℝ) ≤ 4 - 3 * t)]

/-- The `α = 2` instance of `L_le`: `t/(1+t)² ≤ 1/4`, tight at `t = 1`. -/
lemma L_two {t : ℝ} (h0 : 0 ≤ t) : t / (1 + t) ^ (2 : ℝ) ≤ 1 / 4 := by
  have h := L_le (α := 2) le_rfl h0
  have e : (1 : ℝ) / (2 * 2) = 1 / 4 := by norm_num
  rw [e] at h
  exact h

end GraphMarkovMatching.Support
