/-
The pointwise core of the four-law directed contraction
(`arbitrary_offspring_matching.tex`, Theorem `thm:four-law`).

New ingredients over the one-law contraction:

* `phi_mul_le`      the product argument `φ_α(xy) ≤ (L/2)(φ_α(x) + φ_α(y))`,
                    from `(1-xy)² - (1-x²)(1-y²) = (x-y)²` and the
                    `L`-hypothesis; this replaces the `d²`-analysis of the
                    one-law row bound.
* `rows_rearrange`  the row-bad sum is dominated by the aligned pairing,
                    `q₀⁰q₀¹ + q₁⁰q₁¹ ≤ d₀d₁ + e₀e₁` (rearrangement).
* `diag_lower`      the diagonal sum minus the overlap is at least the
                    crossed sorted sum `𝔰 = u₀v₁ + u₁v₀ - u₀u₁`.
* `fourlaw_weak_le` the weak-pair dichotomy: chord route when the strong
                    degrees are small against `1 - d₀d₁`, bounded-ratio route
                    (threshold 4) otherwise.
* `fourlaw_strong_le` the strong-pair term is purely quadratic.
* `fourlaw_rows_le` the combined pointwise row bound.

Everything is real arithmetic on sorted per-column quantities
`e_j ≤ d_j < 1`; the measure-level assembly (degree identities for two-law
product columns, the H/K overlap analysis, and the averaging with the
rearrangement of `φ`-products) mirrors `GraphMarkovMatching.Support.Contraction`
and is carried out in `FourLaw/Square.lean`, `FourLaw/Pointwise.lean`, and
`FourLaw/Assembly.lean`.
-/
import GraphMarkovMatching.Process.TreePotential
import GraphMarkovMatching.Potential.Split

namespace GraphMarkovMatching

open GraphMarkovMatching.Support Real
open scoped ENNReal Classical

set_option maxHeartbeats 800000

/-! ### The product argument -/

/-- **The product argument**: `φ_α(xy) ≤ (L/2)(φ_α(x) + φ_α(y))` under the
`L`-hypothesis `t/(1+t)^α ≤ L`. The identity
`(1-xy)² - (1-x²)(1-y²) = (x-y)²` makes the geometric-mean step exact. -/
lemma phi_mul_le {α L : ℝ} (hα : 0 ≤ α)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    phi α (x * y) ≤ L / 2 * (phi α x + phi α y) := by
  have hx2 : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  have hy2 : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hxy1 : x * y < 1 := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hy1.le)]
  have hAx : (0 : ℝ) < (1 - x ^ 2) ^ (α / 2) := Real.rpow_pos_of_pos hx2 _
  have hAy : (0 : ℝ) < (1 - y ^ 2) ^ (α / 2) := Real.rpow_pos_of_pos hy2 _
  set a : ℝ := x / (1 - x ^ 2) ^ (α / 2) with ha_def
  set b : ℝ := y / (1 - y ^ 2) ^ (α / 2) with hb_def
  -- squares of the geometric-mean factors
  have hsq : ∀ z : ℝ, 0 < z → ((z ^ (α / 2) : ℝ)) ^ 2 = z ^ α := by
    intro z hz
    rw [sq, ← Real.rpow_add hz]
    congr 1
    ring
  have ha2 : a ^ 2 = phi α (x ^ 2) := by
    rw [ha_def, div_pow, hsq _ hx2, phi]
  have hb2 : b ^ 2 = phi α (y ^ 2) := by
    rw [hb_def, div_pow, hsq _ hy2, phi]
  -- step 1: φ(xy) ≤ a b
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
  -- step 2: a b ≤ (a² + b²)/2, then the L-hypothesis
  have hstep2 : a * b ≤ (phi α (x ^ 2) + phi α (y ^ 2)) / 2 := by
    rw [← ha2, ← hb2]
    nlinarith [sq_nonneg (a - b)]
  have hLbound : ∀ t : ℝ, 0 ≤ t → t < 1 → phi α (t ^ 2) ≤ L * phi α t := by
    intro t ht0 ht1
    have hfac : (1 - t ^ 2) ^ α = (1 - t) ^ α * (1 + t) ^ α := by
      rw [show (1 : ℝ) - t ^ 2 = (1 - t) * (1 + t) from by ring,
        Real.mul_rpow (by linarith) (by linarith)]
    have hut : (0 : ℝ) < (1 - t) ^ α := rpow_denom_pos α ht1
    have h1t : (0 : ℝ) < (1 + t) ^ α := Real.rpow_pos_of_pos (by linarith) _
    have hid : phi α (t ^ 2) = phi α t * (t / (1 + t) ^ α) := by
      simp only [phi]
      rw [hfac, div_mul_div_comm, sq]
    rw [hid]
    calc phi α t * (t / (1 + t) ^ α) ≤ phi α t * L :=
          mul_le_mul_of_nonneg_left (hL t ht0) (phi_nonneg ht0 ht1)
      _ = L * phi α t := mul_comm _ _
  have hLx := hLbound x hx0 hx1
  have hLy := hLbound y hy0 hy1
  linarith

/-! ### Rearrangement facts -/

/-- The row-bad sum is dominated by the aligned sorted pairing. -/
lemma rows_rearrange {q00 q01 q10 q11 : ℝ} :
    q00 * q01 + q10 * q11
      ≤ max q00 q10 * max q01 q11 + min q00 q10 * min q01 q11 := by
  rcases le_total q00 q10 with h0 | h0 <;> rcases le_total q01 q11 with h1 | h1
  · rw [max_eq_right h0, max_eq_right h1, min_eq_left h0, min_eq_left h1]
    linarith
  · rw [max_eq_right h0, max_eq_left h1, min_eq_left h0, min_eq_right h1]
    nlinarith [mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
  · rw [max_eq_left h0, max_eq_right h1, min_eq_right h0, min_eq_left h1]
    nlinarith [mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
  · rw [max_eq_left h0, max_eq_left h1, min_eq_right h0, min_eq_right h1]

/-- The diagonal sum minus the overlap dominates the crossed sorted sum
`𝔰 = u₀v₁ + u₁v₀ - u₀u₁`. -/
lemma diag_lower {r00 r01 r10 r11 a0 a1 : ℝ}
    (_h00 : 0 ≤ r00) (_h01 : 0 ≤ r01) (_h10 : 0 ≤ r10) (_h11 : 0 ≤ r11)
    (ha00 : 0 ≤ a0) (ha0 : a0 ≤ min r00 r10) (ha10 : 0 ≤ a1) (ha1 : a1 ≤ min r01 r11) :
    min r00 r10 * max r01 r11 + min r01 r11 * max r00 r10
        - min r00 r10 * min r01 r11
      ≤ r00 * r11 + r01 * r10 - a0 * a1 := by
  have hA : a0 * a1 ≤ min r00 r10 * min r01 r11 :=
    mul_le_mul ha0 ha1 ha10 (le_trans ha00 ha0)
  rcases le_total r00 r10 with h0 | h0 <;> rcases le_total r01 r11 with h1 | h1
  · rw [min_eq_left h0, min_eq_left h1, max_eq_right h0, max_eq_right h1] at *
    linarith
  · rw [min_eq_left h0, min_eq_right h1, max_eq_right h0, max_eq_left h1] at *
    nlinarith [mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
  · rw [min_eq_right h0, min_eq_left h1, max_eq_left h0, max_eq_right h1] at *
    nlinarith [mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
  · rw [min_eq_right h0, min_eq_right h1, max_eq_left h0, max_eq_left h1] at *
    linarith

/-! ### The pointwise row bounds on sorted quantities -/

section RowBounds

variable {α L d0 d1 e0 e1 R : ℝ}

/-- The strong-pair term is purely quadratic. -/
lemma fourlaw_strong_le (hα : 0 ≤ α)
    (he0 : 0 ≤ e0) (hed0 : e0 ≤ d0) (hd0 : d0 < 1)
    (he1 : 0 ≤ e1) (hed1 : e1 ≤ d1) (hd1 : d1 < 1)
    (hR : (1 - d0) * (1 - e1) ≤ R) :
    e0 * e1 / R ^ α ≤ phi α d0 * phi α e1 := by
  have hu0 : (0 : ℝ) < 1 - d0 := by linarith
  have hv1 : (0 : ℝ) < 1 - e1 := by linarith
  have he10 : 0 ≤ e1 := he1
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (by positivity) hR
  have hRα : (1 - d0) ^ α * (1 - e1) ^ α ≤ R ^ α := by
    rw [← Real.mul_rpow hu0.le hv1.le]
    exact Real.rpow_le_rpow (by positivity) hR hα
  calc e0 * e1 / R ^ α
      ≤ e0 * e1 / ((1 - d0) ^ α * (1 - e1) ^ α) :=
        div_le_div_of_nonneg_left (mul_nonneg he0 he10)
          (mul_pos (Real.rpow_pos_of_pos hu0 _) (Real.rpow_pos_of_pos hv1 _)) hRα
    _ = (e0 / (1 - d0) ^ α) * (e1 / (1 - e1) ^ α) := by
        rw [div_mul_div_comm]
    _ ≤ (d0 / (1 - d0) ^ α) * (e1 / (1 - e1) ^ α) := by
        gcongr
    _ = phi α d0 * phi α e1 := rfl

/-- **The weak-pair dichotomy**: chord route for small strong degrees,
bounded-ratio route (threshold `4`) otherwise; the stated bound is the sum of
the two routes and is valid unconditionally. -/
lemma fourlaw_weak_le (hα1 : 1 ≤ α)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (he0 : 0 ≤ e0) (hed0 : e0 ≤ d0) (hd0 : d0 < 1)
    (he1 : 0 ≤ e1) (hed1 : e1 ≤ d1) (hd1 : d1 < 1)
    (hR1 : (1 - d0 * d1) - e0 * (1 - d1) - e1 * (1 - d0) ≤ R) :
    d0 * d1 / R ^ α
      ≤ L / 2 * (phi α d0 + phi α d1)
        + L * chordConst α / 2 * ((phi α e0 + phi α e1) * (phi α d0 + phi α d1))
        + 4 * (phi α d0 * phi α e1 + phi α d1 * phi α e0) := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα1
  have hd00 : 0 ≤ d0 := le_trans he0 hed0
  have hd10 : 0 ≤ d1 := le_trans he1 hed1
  have hu0 : (0 : ℝ) < 1 - d0 := by linarith
  have hu1 : (0 : ℝ) < 1 - d1 := by linarith
  have hv0 : (0 : ℝ) < 1 - e0 := by linarith
  have hv1 : (0 : ℝ) < 1 - e1 := by linarith
  have hdd : (0 : ℝ) < 1 - d0 * d1 := by nlinarith
  have he01 : e0 < 1 := lt_of_le_of_lt hed0 hd0
  have he11 : e1 < 1 := lt_of_le_of_lt hed1 hd1
  -- nonnegativity of the φ's
  have hp_d0 : 0 ≤ phi α d0 := phi_nonneg hd00 hd0
  have hp_d1 : 0 ≤ phi α d1 := phi_nonneg hd10 hd1
  have hp_e0 : 0 ≤ phi α e0 := phi_nonneg he0 he01
  have hp_e1 : 0 ≤ phi α e1 := phi_nonneg he1 he11
  have hcc : 0 ≤ chordConst α := chordConst_nonneg hα0
  -- the crossed lower bounds, from the 𝔰-identity
  have hs_u0v1 : (1 - d0) * (1 - e1)
      ≤ (1 - d0 * d1) - e0 * (1 - d1) - e1 * (1 - d0) := by nlinarith
  have hs_u1v0 : (1 - d1) * (1 - e0)
      ≤ (1 - d0 * d1) - e0 * (1 - d1) - e1 * (1 - d0) := by nlinarith
  have hRu0v1 : (1 - d0) * (1 - e1) ≤ R := le_trans hs_u0v1 hR1
  have hRu1v0 : (1 - d1) * (1 - e0) ≤ R := le_trans hs_u1v0 hR1
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (by positivity) hRu0v1
  by_cases hz : e0 * (1 - d1) + e1 * (1 - d0) ≤ (1 - d0 * d1) / 2
  · -- chord route
    set z : ℝ := (e0 * (1 - d1) + e1 * (1 - d0)) / (1 - d0 * d1) with hz_def
    have hz0 : 0 ≤ z := by positivity
    have hz12 : z ≤ 1 / 2 := by
      rw [hz_def, div_le_div_iff₀ hdd (by norm_num : (0:ℝ) < 2)]
      linarith
    have hzsum : z ≤ e0 + e1 := by
      rw [hz_def, div_le_iff₀ hdd]
      nlinarith [mul_nonneg (mul_nonneg he0 hd10) (sub_nonneg.mpr hd0.le),
        mul_nonneg (mul_nonneg he1 hd00) (sub_nonneg.mpr hd1.le)]
    have hzR : (1 - d0 * d1) * (1 - z) ≤ R := by
      have h : (1 - d0 * d1) * (1 - z)
          = (1 - d0 * d1) - e0 * (1 - d1) - e1 * (1 - d0) := by
        rw [hz_def]
        field_simp
        ring
      rw [h]
      exact hR1
    -- R^α ≥ (1 - d0 d1)^α (1 - z)^α
    have hz1' : (0 : ℝ) ≤ 1 - z := by linarith
    have hRα : (1 - d0 * d1) ^ α * (1 - z) ^ α ≤ R ^ α := by
      rw [← Real.mul_rpow hdd.le hz1']
      exact Real.rpow_le_rpow (mul_nonneg hdd.le hz1') hzR hα0
    have hchord := chord (α := α) hα0 hz0 hz12
    have hdd1 : d0 * d1 < 1 := by nlinarith [mul_nonneg hd00 (sub_nonneg.mpr hd1.le)]
    have hp_dd : 0 ≤ phi α (d0 * d1) := phi_nonneg (mul_nonneg hd00 hd10) hdd1
    have hkey : d0 * d1 / R ^ α ≤ phi α (d0 * d1) * (1 + chordConst α * z) := by
      have hzpos : (0 : ℝ) < 1 - z := lt_of_lt_of_le (by norm_num) (by linarith : (1:ℝ)/2 ≤ 1 - z)
      have h1 : d0 * d1 / R ^ α ≤ d0 * d1 / ((1 - d0 * d1) ^ α * (1 - z) ^ α) :=
        div_le_div_of_nonneg_left (mul_nonneg hd00 hd10)
          (mul_pos (Real.rpow_pos_of_pos hdd _) (Real.rpow_pos_of_pos hzpos _)) hRα
      have h2 : d0 * d1 / ((1 - d0 * d1) ^ α * (1 - z) ^ α)
          = phi α (d0 * d1) * ((1 - z) ^ α)⁻¹ := by
        rw [phi, div_mul_eq_div_div, div_eq_mul_inv]
      have h3 : ((1 - z) ^ α)⁻¹ ≤ 1 + chordConst α * z := by
        rw [← Real.rpow_neg (by linarith)]
        exact hchord
      calc d0 * d1 / R ^ α
          ≤ phi α (d0 * d1) * ((1 - z) ^ α)⁻¹ := by rw [← h2]; exact h1
        _ ≤ phi α (d0 * d1) * (1 + chordConst α * z) :=
            mul_le_mul_of_nonneg_left h3 hp_dd
    have hprod := phi_mul_le hα0 hL hd00 hd0 hd10 hd1
    have hz_phi : z ≤ phi α e0 + phi α e1 := by
      have h0 := le_phi hα0 he0 he01
      have h1 := le_phi hα0 he1 he11
      linarith
    -- assemble the chord-route bound without one big nlinarith
    have hcz0 : 0 ≤ 1 + chordConst α * z := by
      have := mul_nonneg hcc hz0
      linarith
    have hb1 : phi α (d0 * d1) * (1 + chordConst α * z)
        ≤ (L / 2 * (phi α d0 + phi α d1)) * (1 + chordConst α * z) :=
      mul_le_mul_of_nonneg_right hprod hcz0
    have hb2 : (L / 2 * (phi α d0 + phi α d1)) * (1 + chordConst α * z)
        = L / 2 * (phi α d0 + phi α d1)
          + (L / 2 * (phi α d0 + phi α d1) * chordConst α) * z := by ring
    have hb3 : (L / 2 * (phi α d0 + phi α d1) * chordConst α) * z
        ≤ (L / 2 * (phi α d0 + phi α d1) * chordConst α) * (phi α e0 + phi α e1) := by
      refine mul_le_mul_of_nonneg_left hz_phi ?_
      positivity
    have hb4 : (L / 2 * (phi α d0 + phi α d1) * chordConst α) * (phi α e0 + phi α e1)
        = L * chordConst α / 2 * ((phi α e0 + phi α e1) * (phi α d0 + phi α d1)) := by
      ring
    have h4 : 0 ≤ 4 * (phi α d0 * phi α e1 + phi α d1 * phi α e0) := by
      have h1 := mul_nonneg hp_d0 hp_e1
      have h2 := mul_nonneg hp_d1 hp_e0
      linarith
    nlinarith [hkey, hb1, hb3]
  · -- bounded-ratio route
    push Not at hz
    have hratio : d1 ≤ 4 * e1 ∨ d0 ≤ 4 * e0 := by
      by_contra hc
      push Not at hc
      obtain ⟨hc1, hc0⟩ := hc
      have h1 : d0 * (1 - d1) + d1 * (1 - d0) ≤ 2 * (1 - d0 * d1) := by nlinarith
      nlinarith [mul_nonneg he0 (sub_nonneg.mpr hd1.le),
        mul_nonneg he1 (sub_nonneg.mpr hd0.le)]
    have hchord0 : 0 ≤ L * chordConst α / 2
        * ((phi α e0 + phi α e1) * (phi α d0 + phi α d1)) := by positivity
    have hlin0 : 0 ≤ L / 2 * (phi α d0 + phi α d1) := by positivity
    rcases hratio with hr | hr
    · -- d1 ≤ 4 e1: use R ≥ u0 v1
      have hRα : (1 - d0) ^ α * (1 - e1) ^ α ≤ R ^ α := by
        rw [← Real.mul_rpow hu0.le hv1.le]
        exact Real.rpow_le_rpow (by positivity) hRu0v1 hα0
      have hkey : d0 * d1 / R ^ α ≤ 4 * (phi α d0 * phi α e1) := by
        calc d0 * d1 / R ^ α
            ≤ d0 * d1 / ((1 - d0) ^ α * (1 - e1) ^ α) :=
              div_le_div_of_nonneg_left (mul_nonneg hd00 hd10)
                (mul_pos (Real.rpow_pos_of_pos hu0 _) (Real.rpow_pos_of_pos hv1 _)) hRα
          _ = (d0 / (1 - d0) ^ α) * (d1 / (1 - e1) ^ α) := by rw [div_mul_div_comm]
          _ ≤ (d0 / (1 - d0) ^ α) * (4 * e1 / (1 - e1) ^ α) := by gcongr
          _ = 4 * (phi α d0 * phi α e1) := by rw [phi, phi]; ring
      have h2 : 0 ≤ phi α d1 * phi α e0 := mul_nonneg hp_d1 hp_e0
      linarith
    · -- d0 ≤ 4 e0: use R ≥ u1 v0
      have hRα : (1 - d1) ^ α * (1 - e0) ^ α ≤ R ^ α := by
        rw [← Real.mul_rpow hu1.le hv0.le]
        exact Real.rpow_le_rpow (by positivity) hRu1v0 hα0
      have hkey : d0 * d1 / R ^ α ≤ 4 * (phi α d1 * phi α e0) := by
        calc d0 * d1 / R ^ α
            ≤ d0 * d1 / ((1 - d1) ^ α * (1 - e0) ^ α) :=
              div_le_div_of_nonneg_left (mul_nonneg hd00 hd10)
                (mul_pos (Real.rpow_pos_of_pos hu1 _) (Real.rpow_pos_of_pos hv0 _)) hRα
          _ = (d1 / (1 - d1) ^ α) * (d0 / (1 - e0) ^ α) := by
              rw [div_mul_div_comm]
              ring_nf
          _ ≤ (d1 / (1 - d1) ^ α) * (4 * e0 / (1 - e0) ^ α) := by gcongr
          _ = 4 * (phi α d1 * phi α e0) := by rw [phi, phi]; ring
      have h2 : 0 ≤ phi α d0 * phi α e1 := mul_nonneg hp_d0 hp_e1
      linarith

/-- **The combined pointwise row bound** on sorted per-column quantities. -/
lemma fourlaw_rows_le (hα1 : 1 ≤ α)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (he0 : 0 ≤ e0) (hed0 : e0 ≤ d0) (hd0 : d0 < 1)
    (he1 : 0 ≤ e1) (hed1 : e1 ≤ d1) (hd1 : d1 < 1)
    (hR1 : (1 - d0 * d1) - e0 * (1 - d1) - e1 * (1 - d0) ≤ R) :
    (d0 * d1 + e0 * e1) / R ^ α
      ≤ L / 2 * (phi α d0 + phi α d1)
        + L * chordConst α / 2 * ((phi α e0 + phi α e1) * (phi α d0 + phi α d1))
        + 4 * (phi α d0 * phi α e1 + phi α d1 * phi α e0)
        + phi α d0 * phi α e1 := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα1
  have hs_u0v1 : (1 - d0) * (1 - e1)
      ≤ (1 - d0 * d1) - e0 * (1 - d1) - e1 * (1 - d0) := by nlinarith
  have hRu0v1 : (1 - d0) * (1 - e1) ≤ R := le_trans hs_u0v1 hR1
  have hweak := fourlaw_weak_le hα1 hL0 hL he0 hed0 hd0 he1 hed1 hd1 hR1
  have hstrong := fourlaw_strong_le hα0 he0 hed0 hd0 he1 hed1 hd1 hRu0v1
  have hsplit : (d0 * d1 + e0 * e1) / R ^ α
      = d0 * d1 / R ^ α + e0 * e1 / R ^ α := add_div _ _ _
  linarith

end RowBounds

end GraphMarkovMatching
