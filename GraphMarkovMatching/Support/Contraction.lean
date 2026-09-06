/-
The facts of the one-law contraction lemma that the restricted four-law
and its callers reuse:

* `ennreal_add_sq_le_weighted`: the weighted mean inequality
  `(a+b)² ≤ (1+δ)a² + (1+δ⁻¹)b²` in `ℝ≥0∞`, for real `δ > 0`;
* `q_sq_le`: the `K`-step `q² ≤ K·φ_α(q)` on `[0,1)`, for every `K` with
  `t(1-t)^α ≤ K` on `[0,1]`;
* `cOverlap_le_one`, `aOverlap_ne_top`, `cOverlap_ne_top`: the overlap
  degrees are at most one, hence finite.

The contraction lemma itself, with its pointwise split and averaging
machinery, is kept in `Archive/Support/Contraction.lean`.
-/
import GraphMarkovMatching.Support.Square

namespace GraphMarkovMatching.Support

open Real
open scoped ENNReal Classical

/-! ### ℝ≥0∞ arithmetic helper -/

/-- The weighted mean inequality in `ℝ≥0∞`:
`(a+b)² ≤ (1+δ)a² + (1+δ⁻¹)b²` for real `δ > 0`. Proved by reducing the
finite case through `toReal` to `add_sq_le_weighted`. -/
theorem ennreal_add_sq_le_weighted {δ : ℝ} (hδ : 0 < δ) (a b : ℝ≥0∞) :
    (a + b) ^ 2 ≤ ENNReal.ofReal (1 + δ) * a ^ 2 + ENNReal.ofReal (1 + δ⁻¹) * b ^ 2 := by
  have hδ' : 0 < δ⁻¹ := inv_pos.mpr hδ
  rcases eq_top_or_lt_top a with rfl | ha
  · have hne : ENNReal.ofReal (1 + δ) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    simp [pow_two, ENNReal.mul_top, hne]
  rcases eq_top_or_lt_top b with rfl | hb
  · have hne : ENNReal.ofReal (1 + δ⁻¹) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    simp [pow_two, ENNReal.mul_top, hne]
  have hL : (a + b) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.add_ne_top.mpr ⟨ha.ne, hb.ne⟩)
  have hR : ENNReal.ofReal (1 + δ) * a ^ 2 + ENNReal.ofReal (1 + δ⁻¹) * b ^ 2 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ha.ne),
       ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hb.ne)⟩
  rw [← ENNReal.toReal_le_toReal hL hR, ENNReal.toReal_pow,
     ENNReal.toReal_add ha.ne hb.ne,
     ENNReal.toReal_add
       (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ha.ne))
       (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hb.ne)),
     ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
     ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 + δ),
     ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 + δ⁻¹)]
  exact add_sq_le_weighted hδ

/-! ### The `K`-step -/

/-- The `K`-step: `q² ≤ K·φ_α(q)` on `[0,1)`, from `q² = φ_α(q)·q(1-q)^α` and the
hypothesis `q(1-q)^α ≤ K`. -/
lemma q_sq_le {α K t : ℝ} (hK : t * (1 - t) ^ α ≤ K) (h0 : 0 ≤ t) (h1 : t < 1) :
    t ^ 2 ≤ K * phi α t := by
  have hpos : 0 < (1 - t) ^ α := rpow_denom_pos α h1
  have heq : t ^ 2 = phi α t * (t * (1 - t) ^ α) := by
    rw [phi]; field_simp
  rw [heq]
  have hphi0 : 0 ≤ phi α t := phi_nonneg h0 h1
  have := mul_le_mul_of_nonneg_left hK hphi0
  nlinarith [this, hphi0]

/-! ### The degrees (13),(14) transported to `ℝ` -/

variable {X : Type*}

lemma cOverlap_le_one (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    cOverlap μ R x₀ x₁ ≤ 1 := by
  rw [cOverlap, ← μ.tsum_coe]
  exact ENNReal.tsum_le_tsum fun y => by split_ifs <;> simp

lemma aOverlap_ne_top (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    aOverlap μ R x₀ x₁ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top ((aOverlap_le_rE_left μ R x₀ x₁).trans rE_le_one)

lemma cOverlap_ne_top (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    cOverlap μ R x₀ x₁ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (cOverlap_le_one μ R x₀ x₁)

end GraphMarkovMatching.Support
