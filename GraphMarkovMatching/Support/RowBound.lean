/-
The row bound (the first-term pointwise estimate in the proof of the
contraction lemma), at a free exponent `α ≥ 1`.

With `d = max(q₀,q₁)`, `e = min(q₀,q₁)`, `u = 1-d`, `s = 1+d-2e`, and
`0 ≤ e ≤ d < 1`, the claim is

    (d²+e²)/(u^α s^α) ≤ L(φ_α(d)+φ_α(e)) + (2L·c_α + 5/2)·φ_α(d)φ_α(e),

for any constant `L` bounding `t ↦ t/(1+t)^α` at `t = d` (the caller supplies
`L = 1/(2α)` from `Maxima.lean`, or a sharper instance), with
`c_α = 2(2^α - 1)` the chord constant of `Phi.lean`.

Two-case split:

* `e ≤ d/2`  the d-term goes through the `L`-hypothesis and the `chord` with
             `z = 2e/(1+d) ≤ 1/2`; the e-term is a `v ≤ s` monotonicity plus
             `e ≤ d/2`, giving `(1/2)φφ`.
* `e > d/2`  then `s ≥ v` and `d²+e² ≤ (5/2)de` (roots at `e = d/2` and
             `e = 2d`) give `(5/2)φφ` directly.

The coefficients stay symbolic throughout; no rational surrogates or
numeric checks are needed.
-/
import GraphMarkovMatching.Support.Phi

namespace GraphMarkovMatching.Support

open Real

/-- **The row bound at exponent α**, with an abstract λ-constant `L`. -/
lemma rowBound {α L d e : ℝ} (hα : 1 ≤ α) (hL0 : 0 ≤ L)
    (hL : d / (1 + d) ^ α ≤ L)
    (he0 : 0 ≤ e) (hed : e ≤ d) (hd1 : d < 1) :
    (d ^ 2 + e ^ 2) / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
      ≤ L * (phi α d + phi α e)
        + (2 * L * chordConst α + 5 / 2) * (phi α d * phi α e) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hde0 : 0 ≤ d := le_trans he0 hed
  have he1 : e < 1 := lt_of_le_of_lt hed hd1
  have hu : (0 : ℝ) < 1 - d := by linarith
  have hv : (0 : ℝ) < 1 - e := by linarith
  have hs : (0 : ℝ) < 1 + d - 2 * e := by linarith
  have hUp : (0 : ℝ) < (1 - d) ^ α := Real.rpow_pos_of_pos hu α
  have hVp : (0 : ℝ) < (1 - e) ^ α := Real.rpow_pos_of_pos hv α
  have hSp : (0 : ℝ) < (1 + d - 2 * e) ^ α := Real.rpow_pos_of_pos hs α
  -- `s ≥ v`, hence `v^α ≤ s^α` (base monotonicity of `rpow`).
  have hVS : (1 - e) ^ α ≤ (1 + d - 2 * e) ^ α :=
    Real.rpow_le_rpow hv.le (by linarith) hα0
  have hphid : 0 ≤ phi α d := phi_nonneg hde0 hd1
  have hphie : 0 ≤ phi α e := phi_nonneg he0 he1
  have hphidval : phi α d = d / (1 - d) ^ α := rfl
  have hphieval : phi α e = e / (1 - e) ^ α := rfl
  have hCnn : (0 : ℝ) ≤ chordConst α := chordConst_nonneg hα0
  -- The `s`-denominator dominates the `v`-denominator, so every ratio drops to
  -- the `u^α v^α` denominator. Used in both cases.
  have hstep1 : ∀ x : ℝ, 0 ≤ x →
      x / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
        ≤ x / ((1 - d) ^ α * (1 - e) ^ α) := fun x hx =>
    div_le_div_of_nonneg_left hx (mul_pos hUp hVp)
      (mul_le_mul_of_nonneg_left hVS hUp.le)
  by_cases hcase : e ≤ d / 2
  · -- Case `e ≤ d/2`.
    -- e-term: `e²/(u^α s^α) ≤ (1/2) φ(d) φ(e)`.
    have e_term : e ^ 2 / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
        ≤ 1 / 2 * (phi α d * phi α e) := by
      have hrw : 1 / 2 * (phi α d * phi α e)
          = d * e / 2 / ((1 - d) ^ α * (1 - e) ^ α) := by
        rw [hphidval, hphieval]; ring
      rw [hrw]
      calc e ^ 2 / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
          ≤ e ^ 2 / ((1 - d) ^ α * (1 - e) ^ α) := hstep1 _ (by positivity)
        _ ≤ d * e / 2 / ((1 - d) ^ α * (1 - e) ^ α) :=
            div_le_div_of_nonneg_right
              (by nlinarith [mul_nonneg he0 (show (0 : ℝ) ≤ d - 2 * e by linarith)])
              (mul_pos hUp hVp).le
    -- d-term: `d²/(u^α s^α) ≤ L φ(d) + 2L c_α φ(d) φ(e)`, via `hL` and the
    -- `chord` with `z = 2e/(1+d)`.
    have h1d : (0 : ℝ) < 1 + d := by linarith
    have hPp : (0 : ℝ) < (1 + d) ^ α := Real.rpow_pos_of_pos h1d α
    have h1dne : (1 + d) ≠ 0 := ne_of_gt h1d
    have hz0 : (0 : ℝ) ≤ 2 * e / (1 + d) := div_nonneg (by linarith) h1d.le
    have hz_half : 2 * e / (1 + d) ≤ 1 / 2 := by
      rw [div_le_iff₀ h1d]; linarith
    have hchord := chord hα0 hz0 hz_half
    have h1z : (1 + d - 2 * e) / (1 + d) = 1 - 2 * e / (1 + d) := by
      rw [sub_div, div_self h1dne]
    rw [← h1z] at hchord
    have hconv : ((1 + d - 2 * e) / (1 + d)) ^ (-α)
        = (1 + d) ^ α / (1 + d - 2 * e) ^ α := by
      rw [Real.rpow_neg (div_nonneg hs.le h1d.le) α,
          Real.div_rpow hs.le h1d.le α, inv_div]
    rw [hconv] at hchord
    -- `hchord : (1+d)^α / (1+d-2e)^α ≤ 1 + c_α·(2e/(1+d))`
    have h2e : 2 * e / (1 + d) ≤ 2 * e := by
      rw [div_le_iff₀ h1d]; nlinarith [mul_nonneg he0 hde0]
    have hzphi : 2 * e / (1 + d) ≤ 2 * phi α e := by
      have hle := le_phi hα0 he0 he1; linarith
    have hPS : (1 + d) ^ α / (1 + d - 2 * e) ^ α
        ≤ 1 + chordConst α * (2 * phi α e) := by
      have hmul := mul_le_mul_of_nonneg_left hzphi hCnn
      linarith
    have hd_le : d ≤ L * (1 + d) ^ α := (div_le_iff₀ hPp).1 hL
    have hP_le : (1 + d) ^ α
        ≤ (1 + chordConst α * (2 * phi α e)) * (1 + d - 2 * e) ^ α :=
      (div_le_iff₀ hSp).1 hPS
    have d_over_S : d / (1 + d - 2 * e) ^ α
        ≤ L * (1 + chordConst α * (2 * phi α e)) := by
      rw [div_le_iff₀ hSp]
      calc d ≤ L * (1 + d) ^ α := hd_le
        _ ≤ L * ((1 + chordConst α * (2 * phi α e)) * (1 + d - 2 * e) ^ α) :=
            mul_le_mul_of_nonneg_left hP_le hL0
        _ = L * (1 + chordConst α * (2 * phi α e)) * (1 + d - 2 * e) ^ α := by
            ring
    have hd2eq : d ^ 2 / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
        = phi α d * (d / (1 + d - 2 * e) ^ α) := by
      rw [hphidval, div_mul_div_comm, ← pow_two]
    have d_term : d ^ 2 / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
        ≤ phi α d * (L * (1 + chordConst α * (2 * phi α e))) := by
      rw [hd2eq]; exact mul_le_mul_of_nonneg_left d_over_S hphid
    rw [add_div]
    nlinarith [d_term, e_term, mul_nonneg hL0 hphie, mul_nonneg hphid hphie]
  · -- Case `e > d/2`: `s ≥ v` and `d²+e² ≤ (5/2)de`.
    rw [not_le] at hcase
    have h52 : d ^ 2 + e ^ 2 ≤ 5 / 2 * (d * e) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ e - d / 2 by linarith)
                   (show (0 : ℝ) ≤ 2 * d - e by linarith)]
    calc (d ^ 2 + e ^ 2) / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
        ≤ (d ^ 2 + e ^ 2) / ((1 - d) ^ α * (1 - e) ^ α) := hstep1 _ (by positivity)
      _ ≤ 5 / 2 * (phi α d * phi α e) := by
          have hrw : 5 / 2 * (phi α d * phi α e)
              = 5 / 2 * (d * e) / ((1 - d) ^ α * (1 - e) ^ α) := by
            rw [hphidval, hphieval]; ring
          rw [hrw]
          exact div_le_div_of_nonneg_right h52 (mul_pos hUp hVp).le
      _ ≤ L * (phi α d + phi α e)
            + (2 * L * chordConst α + 5 / 2) * (phi α d * phi α e) := by
          nlinarith [mul_nonneg hphid hphie, mul_nonneg hL0 (add_nonneg hphid hphie),
            mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hL0) hCnn)
              (mul_nonneg hphid hphie)]

end GraphMarkovMatching.Support
