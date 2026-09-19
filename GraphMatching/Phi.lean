/-
The weight `φ_α` of `graph_matching_selfcontained.tex`, `eq:alpha`, together with the
elementary facts the rest of the development needs:

* `le_phiA`             `eq:phi-dominates`:  `t ≤ φ_α t` on `[0,1)`
* `one_sub_rpow_leA`    the tangent line to `t ↦ t^α` at `t = 1`, used for `eq:W-bound`
* `chordA`              `eq:chord`:  `(1-z)^{-α} ≤ 1 + C_α z` on `[0,1/2]`
* `rpow_alpha_eq_sqrt_pow`  the substitution `s = √(1-t)` that removes `rpow`
                        from the analysis at `α = 5/2`

The first two hold at an arbitrary exponent, as in the paper; `alpha`, `phi` and the
unsuffixed lemmas are the instances at `α = 5/2`, where the numeric chain runs.

The `rpow` at exponent `5/2` is the main obstacle to automation in this file.
`rpow_alpha_eq_sqrt_pow` is the bridge that turns `φ` into a rational function of
`s`, which is what makes `Maxima.lean` tractable.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

namespace GraphMatching

open Real

/-! ### The weight at a general exponent

`eq:alpha` defines `φ_α t = t/(1-t)^α` for an exponent left free; the paper carries
`α ≥ 1` through the definitions, `thm:product` and `sec:graph`, and fixes `α = 5/2`
only at `thm:contraction` and below. The general statements are the `A`-suffixed
lemmas here; `alpha` and `phi` are the pinned instance the numeric chain runs at,
and each pinned lemma is the corresponding general one applied at `alpha`. -/

/-- **`eq:alpha`**: the weight `φ_α t = t / (1-t)^α` at a general exponent. The paper
defines it on `[0,1)`; off that range Lean's junk values apply and every lemma below
carries `t < 1`. -/
noncomputable def phiA (α t : ℝ) : ℝ := t / (1 - t) ^ α

/-- On `[0,1)` the denominator of `φ_α` is positive, for every exponent. -/
lemma phiA_denom_pos (α : ℝ) {t : ℝ} (h : t < 1) : 0 < (1 - t) ^ α :=
  Real.rpow_pos_of_pos (by linarith) α

lemma phiA_nonneg (α : ℝ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : 0 ≤ phiA α t :=
  div_nonneg h0 (phiA_denom_pos α h1).le

/-- **`eq:phi-dominates`** at a general exponent: `t ≤ φ_α t` on `[0,1)` whenever
`α ≥ 0`, since then `(1-t)^α ≤ 1`. -/
lemma le_phiA {α : ℝ} (hα : 0 ≤ α) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : t ≤ phiA α t := by
  rw [phiA, le_div_iff₀ (phiA_denom_pos α h1)]
  have h : (1 - t) ^ α ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) hα
  nlinarith

/-- The tangent line to `t ↦ t^α` at `t = 1` lies below the graph:
`1 - r^α ≤ α (1-r)` for `0 ≤ r`, at any `α ≥ 1`. This is the inequality behind
`eq:W-bound` (`W(x) - 1 ≤ α φ_α(q(x))`). It is Bernoulli, so Mathlib supplies it. -/
lemma one_sub_rpow_leA {α : ℝ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 ≤ r) :
    1 - r ^ α ≤ α * (1 - r) := by
  have h := one_add_mul_self_le_rpow_one_add (s := r - 1) (by linarith) hα
  have e : (1 : ℝ) + (r - 1) = r := by ring
  rw [e] at h
  linarith

/-- **`eq:W-bound`** at a general exponent, in the form `thm:product` uses:
`(1-t)^{-α} ≤ 1 + α φ_α t` on `[0,1)` for `α ≥ 1`. This is `one_sub_rpow_leA`
divided through by `(1-t)^α`; the paper writes it as `W(x) - 1 ≤ α φ_α(q(x))`
with `W = r^{-α}`. -/
lemma rpow_neg_alpha_leA {α : ℝ} (hα : 1 ≤ α) {t : ℝ} (h1 : t < 1) :
    (1 - t) ^ (-α) ≤ 1 + α * phiA α t := by
  have hr : (0 : ℝ) < 1 - t := by linarith
  have hp : (0 : ℝ) < (1 - t) ^ α := phiA_denom_pos α h1
  rw [Real.rpow_neg hr.le, inv_eq_one_div, div_le_iff₀ hp]
  have h := one_sub_rpow_leA hα hr.le
  have hphi : α * phiA α t * (1 - t) ^ α = α * t := by
    rw [phiA]; field_simp
  nlinarith [h, hphi]

/-! ### The pinned exponent -/

/-- The exponent `α = 5/2` at which `thm:contraction` and everything below it runs,
`eq:alpha`. -/
noncomputable def alpha : ℝ := 5 / 2

lemma one_le_alpha : (1 : ℝ) ≤ alpha := by norm_num [alpha]

lemma alpha_nonneg : (0 : ℝ) ≤ alpha := by norm_num [alpha]

/-- `φ = φ_α` at the pinned exponent, `eq:alpha`. -/
noncomputable def phi (t : ℝ) : ℝ := t / (1 - t) ^ alpha

lemma phi_eq_phiA (t : ℝ) : phi t = phiA alpha t := rfl

/-- On `[0,1)` the denominator of `φ` is positive. -/
lemma rpow_denom_pos {t : ℝ} (h : t < 1) : 0 < (1 - t) ^ alpha :=
  phiA_denom_pos alpha h

lemma phi_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : 0 ≤ phi t :=
  phiA_nonneg alpha h0 h1

/-- **`eq:phi-dominates`** at `α = 5/2`. -/
lemma le_phi {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : t ≤ phi t :=
  le_phiA alpha_nonneg h0 h1

/-- The tangent-line inequality at `α = 5/2`. -/
lemma one_sub_rpow_le {r : ℝ} (hr : 0 ≤ r) : 1 - r ^ alpha ≤ alpha * (1 - r) :=
  one_sub_rpow_leA one_le_alpha hr

/-- **`eq:W-bound`** at `α = 5/2`. -/
lemma rpow_neg_alpha_le {t : ℝ} (h1 : t < 1) :
    (1 - t) ^ (-alpha) ≤ 1 + alpha * phi t :=
  rpow_neg_alpha_leA one_le_alpha h1

/-- `x^α = (√x)^5` for `x ≥ 0`. The substitution trades the `rpow` at `5/2`
for a natural power of a square root, after which the estimates of
`Maxima.lean` become polynomial. -/
lemma rpow_alpha_eq_sqrt_pow {x : ℝ} (hx : 0 ≤ x) : x ^ alpha = (Real.sqrt x) ^ (5 : ℕ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (x ^ (1 / (2 : ℝ))) 5, ← Real.rpow_mul hx]
  norm_num [alpha]

/-! ### The chord bound, `eq:chord`

`z ↦ (1-z)^{-α}` is convex on `[0,1/2]` and so lies below the chord through
`(0,1)` and `(1/2, 2^α)`, whose slope is `C_α = 2(2^α - 1)`. Mathlib has no
convexity lemma for negative `rpow` exponents (`convexOn_rpow` needs `1 ≤ p`),
but convexity of `x ↦ b^x` (`convexOn_rpow_left`) delivers the bound in two
applications, both at exponents the chord itself supplies:

* at `b = 2` between `0` and `-1`: `2^{-2z} ≤ 1 - z`, i.e. `(1-z)^{-1} ≤ 2^{2z}`;
* raising that to the power `α`: `(1-z)^{-α} ≤ 2^{2αz}`;
* at `b = 2` between `0` and `α`: `2^{2αz} ≤ 1 + C_α z`.

No derivative and no surd enters, and the argument holds at every `α ≥ 0`. -/

/-- **`eq:chord`**: the chord slope `C_α = 2(2^α - 1)` through `(0,1)` and
`(1/2, 2^α)`. -/
noncomputable def chordConstA (α : ℝ) : ℝ := 2 * (2 ^ α - 1)

/-- `2^{-2z} ≤ 1 - z` on `[0,1/2]`: the convex `z ↦ 2^{-2z}` meets the affine
`1 - z` at both endpoints, so it lies below it in between. -/
lemma two_rpow_neg_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1 / 2) :
    (2 : ℝ) ^ (-(2 * z)) ≤ 1 - z := by
  have hcv := convexOn_rpow_left (b := (2 : ℝ)) (by norm_num)
  have h : (2 : ℝ) ^ ((1 - 2 * z) • (0 : ℝ) + (2 * z) • (-1 : ℝ))
      ≤ (1 - 2 * z) • (2 : ℝ) ^ (0 : ℝ) + (2 * z) • (2 : ℝ) ^ (-1 : ℝ) :=
    hcv.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) (by linarith) (by ring)
  have h2 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
  rw [h2, Real.rpow_zero] at h
  simp only [smul_eq_mul] at h
  have he : (1 - 2 * z) * (0 : ℝ) + 2 * z * (-1 : ℝ) = -(2 * z) := by ring
  rw [he] at h
  linarith

/-- `2^{2αz} ≤ 1 + C_α z` on `[0,1/2]`: the convex `x ↦ 2^x` lies below its chord
between `0` and `α`, read at `x = 2αz`. -/
lemma two_rpow_chord {α z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1 / 2) :
    (2 : ℝ) ^ (2 * α * z) ≤ 1 + chordConstA α * z := by
  have hcv := convexOn_rpow_left (b := (2 : ℝ)) (by norm_num)
  have h : (2 : ℝ) ^ ((1 - 2 * z) • (0 : ℝ) + (2 * z) • α)
      ≤ (1 - 2 * z) • (2 : ℝ) ^ (0 : ℝ) + (2 * z) • (2 : ℝ) ^ α :=
    hcv.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) (by linarith) (by ring)
  rw [Real.rpow_zero] at h
  simp only [smul_eq_mul] at h
  have he : (1 - 2 * z) * (0 : ℝ) + 2 * z * α = 2 * α * z := by ring
  rw [he] at h
  rw [chordConstA]
  nlinarith [h]

/-- **`eq:chord`** at a general exponent: `(1-z)^{-α} ≤ 1 + C_α z` on `[0,1/2]`,
for every `α ≥ 0`. -/
lemma chordA {α : ℝ} (hα : 0 ≤ α) {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1 / 2) :
    (1 - z) ^ (-α) ≤ 1 + chordConstA α * z := by
  have hz : (0 : ℝ) < 1 - z := by linarith
  have hp : (0 : ℝ) < (2 : ℝ) ^ (2 * z) := Real.rpow_pos_of_pos (by norm_num) _
  -- `(1-z)⁻¹ ≤ 2^{2z}`, from `2^{-2z} ≤ 1 - z`
  have hneg := two_rpow_neg_le h0 h1
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hneg
  have hmul : 1 ≤ (2 : ℝ) ^ (2 * z) * (1 - z) := by
    have := mul_le_mul_of_nonneg_left hneg hp.le
    rwa [mul_inv_cancel₀ hp.ne'] at this
  have hstep1 : (1 - z)⁻¹ ≤ (2 : ℝ) ^ (2 * z) := by
    rw [inv_eq_one_div, div_le_iff₀ hz]
    exact hmul
  calc (1 - z) ^ (-α) = ((1 - z)⁻¹) ^ α := by
        rw [Real.inv_rpow hz.le, Real.rpow_neg hz.le]
    _ ≤ ((2 : ℝ) ^ (2 * z)) ^ α := Real.rpow_le_rpow (by positivity) hstep1 hα
    _ = (2 : ℝ) ^ (2 * α * z) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]; ring_nf
    _ ≤ 1 + chordConstA α * z := two_rpow_chord h0 h1

/-- The chord slope for `eq:chord`.

The paper uses the exact chord slope `8√2 - 2 ≈ 9.3137` through `(0,1)` and
`(1/2, 2^{5/2})`. Any `C ≥ 8√2 - 2` bounds the function on `[0,1/2]` just as
well, and the only downstream use (the coefficient check after `eq:row-bound`,
`2L_α·C + 1/2 < 4` with `2L_α ≤ 93/250`) needs `C < 3.5·250/93 ≈ 9.4086`. The
rational `28/3 ≈ 9.3333` sits in that window with margin at both ends, which
keeps `√2` out of the development and leaves the downstream check at
`93/250 · 28/3 + 1/2 = 3.972 < 4`. -/
noncomputable def chordConst : ℝ := 28 / 3

/-- `(x^α)² = x⁵`. This is what lets `eq:chord` be squared into a polynomial. -/
lemma sq_rpow_alpha {x : ℝ} (hx : 0 ≤ x) : (x ^ alpha) ^ (2 : ℕ) = x ^ (5 : ℕ) := by
  rw [← Real.rpow_natCast (x ^ alpha) 2, ← Real.rpow_mul hx, ← Real.rpow_natCast x 5]
  norm_num [alpha]

/-- `C_{5/2} = 8√2 - 2 ≤ 28/3`: the rational surrogate is a valid chord slope.
Squaring, this is `2^5 = 32 ≤ (17/3)^2 = 289/9`, with margin `1/9`. -/
lemma chordConstA_alpha_le : chordConstA alpha ≤ chordConst := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ alpha := Real.rpow_pos_of_pos (by norm_num) _
  have hsq : ((2 : ℝ) ^ alpha) ^ (2 : ℕ) = 32 := by
    rw [sq_rpow_alpha (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have h : (2 : ℝ) ^ alpha ≤ 17 / 3 := by nlinarith [hpos, hsq]
  rw [chordConstA, chordConst]
  linarith

/-- **`eq:chord`** at `α = 5/2`, with the rational slope in place of `C_α`. -/
lemma chord {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1 / 2) :
    (1 - z) ^ (-alpha) ≤ 1 + chordConst * z :=
  (chordA alpha_nonneg h0 h1).trans
    (by have := chordConstA_alpha_le; nlinarith [h0])

end GraphMatching
