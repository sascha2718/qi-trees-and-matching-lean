/-
Numeric constants for the restricted four-law at `α = 5/2`
(`arbitrary_offspring_matching.tex`, the `δ = 3` instantiation).

The two scalar hypotheses of `PhiDres_fourlaw_le` are discharged with
deliberately coarse rational constants, using only exponent
monotonicity of `Real.rpow` and polynomial arithmetic; no genuine
`5/2`-power analysis is needed:

* `quarter_L_bound`: `L = 1/4` works, since `(1+t)^(5/2) ≥ (1+t)^2`
  (base at least one, exponent monotonicity) and `(1+t)^2 ≥ 4t`;
* `fourTwentySeventh_K_bound`: `K = 4/27` works, since
  `(1-t)^(5/2) ≤ (1-t)^2` on `[0,1]` (base in `[0,1]`, larger exponent)
  and `t(1-t)^2 ≤ 4/27`;
* `delta3_A_lt_one`, `delta3_A_le`: at `δ = 1/8` the linear four-law
  constant is `2L + 2(1+δ)K = 1/2 + 1/3 = 5/6 < 1`;
* `two_rpow_five_half_le_eight`, `ennreal_two_rpow_five_half_le_eight`,
  `chordConst_five_half_le`: the rpow numerals `2^{5/2} ≤ 8`, in `ℝ` and
  in `ℝ≥0∞`, and `chordConst(5/2) ≤ 14`.
-/
import GraphMarkovMatching.Process.Ledger

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal

/-- The `L`-hypothesis of the restricted four-law at `α = 5/2` with the
coarse constant `L = 1/4`: for `t ≥ 0`,
`t / (1+t)^(5/2) ≤ t / (1+t)^2 ≤ 1/4`, the first step by exponent
monotonicity of `rpow` on a base at least one, the second because
`(1+t)^2 - 4t = (1-t)^2 ≥ 0`. -/
lemma quarter_L_bound : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ (5 / 2 : ℝ) ≤ 1 / 4 := by
  intro t ht
  have h1 : (1 : ℝ) ≤ 1 + t := by linarith
  have hsq : (0 : ℝ) < (1 + t) ^ 2 := by positivity
  have hexp : (1 + t) ^ (2 : ℝ) ≤ (1 + t) ^ (5 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  rw [Real.rpow_two] at hexp
  have hstep : t / (1 + t) ^ (5 / 2 : ℝ) ≤ t / (1 + t) ^ 2 :=
    div_le_div_of_nonneg_left ht hsq hexp
  refine hstep.trans ?_
  rw [div_le_iff₀ hsq]
  nlinarith [sq_nonneg (1 - t)]

/-- The `K`-hypothesis of the restricted four-law at `α = 5/2` with the
coarse constant `K = 4/27`: for `t ∈ [0,1]`,
`t(1-t)^(5/2) ≤ t(1-t)^2 ≤ 4/27`, the first step by exponent
monotonicity of `rpow` on a base in `[0,1]` (the degenerate base zero
is covered by `Real.rpow_le_rpow_of_exponent_ge'`), the second from
the factorisation `4/27 - t(1-t)^2 = (3t-1)^2 (4/3 - t) / 9`. -/
lemma fourTwentySeventh_K_bound :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ (5 / 2 : ℝ) ≤ 4 / 27 := by
  intro t ht ht1
  have h0 : (0 : ℝ) ≤ 1 - t := by linarith
  have h1 : (1 : ℝ) - t ≤ 1 := by linarith
  have hexp : (1 - t) ^ (5 / 2 : ℝ) ≤ (1 - t) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' h0 h1 (by norm_num) (by norm_num)
  rw [Real.rpow_two] at hexp
  have hstep : t * (1 - t) ^ (5 / 2 : ℝ) ≤ t * (1 - t) ^ 2 :=
    mul_le_mul_of_nonneg_left hexp ht
  refine hstep.trans ?_
  nlinarith [sq_nonneg (3 * t - 1), mul_nonneg (sq_nonneg (3 * t - 1)) h0]

/-- At `δ = 1/8` the linear four-law constant `2L + 2(1+δ)K` built from
`L = 1/4` and `K = 4/27` is `5/6`, strictly below one, in the safe
`ℝ≥0∞` form used by the ledger. -/
lemma delta3_A_lt_one :
    ENNReal.ofReal (2 * (1 / 4) + 2 * (1 + (1 / 8 : ℝ)) * (4 / 27)) < 1 := by
  rw [ENNReal.ofReal_lt_one]
  norm_num

/-- The linear four-law constant at `δ = 1/8` evaluates to `5/6`, for
downstream rewriting. -/
lemma delta3_A_le :
    (2 * (1 / 4 : ℝ) + 2 * (1 + (1 / 8 : ℝ)) * (4 / 27)) = 5 / 6 := by
  norm_num

/-! ### rpow numerals -/

/-- `2^{5/2} ≤ 8` in `ℝ`. -/
lemma two_rpow_five_half_le_eight : (2 : ℝ) ^ ((5 : ℝ) / 2) ≤ 8 := by
  calc (2 : ℝ) ^ ((5 : ℝ) / 2)
      ≤ (2 : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)
    _ = 8 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num,
          Real.rpow_natCast]
        norm_num

/-- `2^{5/2} ≤ 8` in `ℝ≥0∞`. -/
lemma ennreal_two_rpow_five_half_le_eight :
    (2 : ℝ≥0∞) ^ ((5 : ℝ) / 2) ≤ 8 := by
  calc (2 : ℝ≥0∞) ^ ((5 : ℝ) / 2)
      ≤ (2 : ℝ≥0∞) ^ (3 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 8 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num,
          ENNReal.rpow_natCast]
        norm_num

/-- The chord constant at `α = 5/2` is at most `14`. -/
lemma chordConst_five_half_le : chordConst ((5 : ℝ) / 2) ≤ 14 := by
  rw [chordConst]
  linarith [two_rpow_five_half_le_eight]

end GraphMarkovMatching
