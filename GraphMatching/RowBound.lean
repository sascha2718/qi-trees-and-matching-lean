/-
`sec:contraction` of `graph_matching_selfcontained.tex`, the row-bound `eq:row-bound`: the
first-term pointwise estimate in the proof of the contraction `thm:contraction`.

With `d = max(q₀,q₁)`, `e = min(q₀,q₁)`, `u = 1-d`, `v = 1-e`, `s = 1+d-2e`, and
`0 ≤ e ≤ d < 1`, the claim is

    (d²+e²)/(u^α s^α) ≤ L_α(φ(d)+φ(e)) + 4φ(d)φ(e),      L_α = 14/75.

This is the one genuinely two-variable `rpow` inequality in the whole
development, and the paper proves it by a two-case split on `e ≤ d/2`:

* `e ≤ d/2`  the d-term goes through `L_bound` (`eq:lambda-max`) and the `chord`
             (`eq:chord`) with `z = 2e/(1+d) ≤ 1/2`; the e-term is a `v ≤ s`
             monotonicity plus `e ≤ d/2`. The product-term coefficient is
             `2·(14/75)·(28/3) + 1/2 = 3.984 < 4`, the same rational check that
             fixes the constants in `Maxima.lean`.
* `e > d/2`  then `s ≥ v` and `d²+e² ≤ 4de` (an elementary inequality for
             `d/2 < e ≤ d`) give the bound directly with the product term alone.

The paper writes `L_α = 6√15/125` and `C = 8√2-2` in `eq:row-bound`, `eq:lambda-max`
and `eq:chord`; we use the rational surrogates `L_α = 14/75` and
`C = chordConst = 28/3` throughout, so no surd enters. Both cases reduce every
denominator to `u^α v^α` via `s ≥ v`, so
the only `rpow` facts used are `chord`, `L_bound`, `Real.rpow_le_rpow`
(base monotonicity) and the `Real.div_rpow`/`Real.rpow_neg` bookkeeping that
turns `(s/(1+d))^{-α}` into `(1+d)^α/s^α`.
-/
import GraphMatching.Maxima

namespace GraphMatching

open Real

/-- **`eq:row-bound`** at a general exponent: the first-term pointwise estimate for
`thm:contraction`, with the constants `L_α` and `M_α` of `eq:contraction-constants`. The two
case coefficients are `2 L_α C_α + 1/2` and `5/2`, and `M_α` is *defined* as their maximum, so
no numeric input enters. -/
lemma rowBoundA {α : ℝ} (hα : 1 ≤ α) {d e : ℝ} (he0 : 0 ≤ e) (hed : e ≤ d) (hd1 : d < 1) :
    (d ^ 2 + e ^ 2) / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
      ≤ LA α * (phiA α d + phiA α e) + MA α * (phiA α d * phiA α e) := by
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
  have hphid : 0 ≤ phiA α d := phiA_nonneg α hde0 hd1
  have hphie : 0 ≤ phiA α e := phiA_nonneg α he0 he1
  have hphidval : phiA α d = d / (1 - d) ^ α := rfl
  have hphieval : phiA α e = e / (1 - e) ^ α := rfl
  have hLnn : 0 ≤ LA α := LA_nonneg hα0
  -- The `s`-denominator dominates the `v`-denominator, so every ratio drops to
  -- the `u^α v^α` denominator. Used in both cases.
  have hstep1 : ∀ x : ℝ, 0 ≤ x →
      x / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
        ≤ x / ((1 - d) ^ α * (1 - e) ^ α) := fun x hx =>
    div_le_div_of_nonneg_left hx (mul_pos hUp hVp)
      (mul_le_mul_of_nonneg_left hVS hUp.le)
  by_cases hcase : e ≤ d / 2
  · -- Case `e ≤ d/2`, coefficient `2 L_α C_α + 1/2`.
    -- e-term: `e²/(u^α s^α) ≤ (1/2) φ_α(d) φ_α(e)`.
    have e_term : e ^ 2 / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
        ≤ 1 / 2 * (phiA α d * phiA α e) := by
      have hrw : 1 / 2 * (phiA α d * phiA α e)
          = d * e / 2 / ((1 - d) ^ α * (1 - e) ^ α) := by
        rw [hphidval, hphieval]; ring
      rw [hrw]
      calc e ^ 2 / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
          ≤ e ^ 2 / ((1 - d) ^ α * (1 - e) ^ α) := hstep1 _ (by positivity)
        _ ≤ d * e / 2 / ((1 - d) ^ α * (1 - e) ^ α) :=
            div_le_div_of_nonneg_right
              (by nlinarith [mul_nonneg he0 (show (0 : ℝ) ≤ d - 2 * e by linarith)])
              (mul_pos hUp hVp).le
    -- d-term: `d²/(u^α s^α) ≤ L_α φ_α(d) + 2 L_α C_α φ_α(d) φ_α(e)`, via `le_LA` and
    -- `chordA` with `z = 2e/(1+d)`.
    have h1d : (0 : ℝ) < 1 + d := by linarith
    have hPp : (0 : ℝ) < (1 + d) ^ α := Real.rpow_pos_of_pos h1d α
    have h1dne : (1 + d) ≠ 0 := ne_of_gt h1d
    have hz0 : (0 : ℝ) ≤ 2 * e / (1 + d) := div_nonneg (by linarith) h1d.le
    have hz_half : 2 * e / (1 + d) ≤ 1 / 2 := by
      rw [div_le_iff₀ h1d]; linarith
    have hchord := chordA hα0 hz0 hz_half
    have h1z : (1 + d - 2 * e) / (1 + d) = 1 - 2 * e / (1 + d) := by
      rw [sub_div, div_self h1dne]
    rw [← h1z] at hchord
    have hconv : ((1 + d - 2 * e) / (1 + d)) ^ (-α)
        = (1 + d) ^ α / (1 + d - 2 * e) ^ α := by
      rw [Real.rpow_neg (div_nonneg hs.le h1d.le) α,
          Real.div_rpow hs.le h1d.le α, inv_div]
    rw [hconv] at hchord
    -- `hchord : (1+d)^α / (1+d-2e)^α ≤ 1 + C_α·(2e/(1+d))`
    have h2e : 2 * e / (1 + d) ≤ 2 * e := by
      rw [div_le_iff₀ h1d]; nlinarith [mul_nonneg he0 hde0]
    have hzphi : 2 * e / (1 + d) ≤ 2 * phiA α e := by
      have hle := le_phiA hα0 he0 he1; linarith
    have hCnn : (0 : ℝ) ≤ chordConstA α := chordConstA_nonneg hα0
    have hPS : (1 + d) ^ α / (1 + d - 2 * e) ^ α
        ≤ 1 + chordConstA α * (2 * phiA α e) := by
      have hmul := mul_le_mul_of_nonneg_left hzphi hCnn
      linarith
    have hdP : d / (1 + d) ^ α ≤ LA α := le_LA hα0 hde0 hd1.le
    have hd_le : d ≤ LA α * (1 + d) ^ α := (div_le_iff₀ hPp).1 hdP
    have hP_le : (1 + d) ^ α
        ≤ (1 + chordConstA α * (2 * phiA α e)) * (1 + d - 2 * e) ^ α :=
      (div_le_iff₀ hSp).1 hPS
    have d_over_S : d / (1 + d - 2 * e) ^ α
        ≤ LA α * (1 + chordConstA α * (2 * phiA α e)) := by
      rw [div_le_iff₀ hSp]
      calc d ≤ LA α * (1 + d) ^ α := hd_le
        _ ≤ LA α * ((1 + chordConstA α * (2 * phiA α e)) * (1 + d - 2 * e) ^ α) :=
            mul_le_mul_of_nonneg_left hP_le hLnn
        _ = LA α * (1 + chordConstA α * (2 * phiA α e)) * (1 + d - 2 * e) ^ α := by
            ring
    have hd2eq : d ^ 2 / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
        = phiA α d * (d / (1 + d - 2 * e) ^ α) := by
      rw [hphidval, div_mul_div_comm, ← pow_two]
    have d_term : d ^ 2 / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
        ≤ phiA α d * (LA α * (1 + chordConstA α * (2 * phiA α e))) := by
      rw [hd2eq]; exact mul_le_mul_of_nonneg_left d_over_S hphid
    -- the assembled product coefficient is `2 L_α C_α + 1/2 ≤ M_α`
    have hM := case_one_le_MA α
    rw [add_div]
    nlinarith [d_term, e_term, hphie, hphid, hM, mul_nonneg hphid hphie, hLnn]
  · -- Case `e > d/2`, coefficient `d/e + e/d < 5/2`.
    rw [not_le] at hcase
    have h5de : d ^ 2 + e ^ 2 ≤ 5 / 2 * (d * e) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * d - e by linarith)
                   (show (0 : ℝ) ≤ 2 * e - d by linarith)]
    have hM := case_two_le_MA α
    calc (d ^ 2 + e ^ 2) / ((1 - d) ^ α * (1 + d - 2 * e) ^ α)
        ≤ (d ^ 2 + e ^ 2) / ((1 - d) ^ α * (1 - e) ^ α) := hstep1 _ (by positivity)
      _ ≤ 5 / 2 * (phiA α d * phiA α e) := by
          have hrw : 5 / 2 * (phiA α d * phiA α e)
              = 5 / 2 * (d * e) / ((1 - d) ^ α * (1 - e) ^ α) := by
            rw [hphidval, hphieval]; ring
          rw [hrw]
          exact div_le_div_of_nonneg_right h5de (mul_pos hUp hVp).le
      _ ≤ LA α * (phiA α d + phiA α e) + MA α * (phiA α d * phiA α e) := by
          nlinarith [hphid, hphie, hLnn, hM, mul_nonneg hphid hphie]

/-- `eq:row-bound` at `α = 5/2`, in the rational form the numeric chain runs on. -/
lemma rowBound {d e : ℝ} (he0 : 0 ≤ e) (hed : e ≤ d) (hd1 : d < 1) :
    (d ^ 2 + e ^ 2) / ((1 - d) ^ alpha * (1 + d - 2 * e) ^ alpha)
      ≤ 14 / 75 * (phi d + phi e) + 4 * phi d * phi e := by
  have hde0 : 0 ≤ d := le_trans he0 hed
  have he1 : e < 1 := lt_of_le_of_lt hed hd1
  have h := rowBoundA one_le_alpha he0 hed hd1
  have hphid : 0 ≤ phi d := phi_nonneg hde0 hd1
  have hphie : 0 ≤ phi e := phi_nonneg he0 he1
  simp only [← phi_eq_phiA] at h
  nlinarith [h, LA_alpha_le, MA_alpha_le, hphid, hphie, mul_nonneg hphid hphie]

end GraphMatching
