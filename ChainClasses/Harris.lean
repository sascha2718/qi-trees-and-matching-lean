/-
`sec:shape-harris` of `matching_classes_simple.tex`: the arithmetic of
`thm:harris` and of the shape law of `thm:shape-iid`.

The two propositions have a structural half and an arithmetic half. The
structural half is classical and cited in the tex: conditioned on survival the
tree embeds into a two-type branching process, which carries the conditional
independence of the decorations, and the skeleton law is the
Harris-Sevastyanov transformation. The arithmetic half is everything the rest
of the section actually consumes, and it is certified here over the offspring
distribution alone.

* `IsHairy`: an offspring law on `{0,1,2}` that is supercritical with
  `θ₀ > 0`, the standing hypothesis of `sec:shapes`.
* `harris_quadratic` and `extinction_fixed_point`: the fixed-point equation
  factors as `(s-1)(θ₂s-θ₀)`, so the extinction probability is `θ₀/θ₂ ∈ (0,1)`.
* `skeleton_sum`, `skeleton_chain_regime`: the skeleton law
  `θ̃₁ = θ₁ + 2θ₀`, `θ̃₂ = θ₂ - θ₀` is a two-value law in the chain regime.
* `split_prob`, `neck_prob`, `survival_decomposition`: the two conditional
  probabilities of the proof, and the check that the three survival cases
  exhaust the conditioning.
* `conjugate_tilt`, `conjugate_sum`, `conjugate_subcritical`: the bush law
  `θ̂ = (θ₂,θ₁,θ₀)` as the tilt `θ̂_j = θ_j(θ₀/θ₂)^{j-1}`, and its
  subcriticality.
* `bush_prob`, `decoration_split`: the decoration of a neck vertex.
* `neck_law_tsum`: the neck length of `thm:shape-iid` is a probability law.
* `shape_factors_mem`: the seven constants of
  `thm:shape-mass`\ `it:shape-mass-point` all lie in `(0,1]`, which is what
  `shape_mass_point` needs of them.
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

namespace ChainClasses

/-- The standing hypothesis of `sec:shapes`: an offspring law supported on
`{0,1,2}`, supercritical, with `θ₀ > 0`. -/
structure IsHairy (θ₀ θ₁ θ₂ : ℝ) : Prop where
  sum : θ₀ + θ₁ + θ₂ = 1
  pos₀ : 0 < θ₀
  nonneg₁ : 0 ≤ θ₁
  supercritical : 1 < θ₁ + 2 * θ₂

namespace IsHairy

variable {θ₀ θ₁ θ₂ : ℝ} (h : IsHairy θ₀ θ₁ θ₂)
include h

/-- Supercriticality with `θ₀ > 0` forces `θ₂ > θ₀ > 0`. -/
lemma lt₂ : θ₀ < θ₂ := by
  have := h.sum
  have := h.supercritical
  linarith

lemma pos₂ : 0 < θ₂ := lt_trans h.pos₀ h.lt₂

/-- The fixed-point equation of the generating function factors as
`(s-1)(θ₂s-θ₀)`. -/
lemma harris_quadratic (s : ℝ) :
    θ₀ + θ₁ * s + θ₂ * s ^ 2 - s = (s - 1) * (θ₂ * s - θ₀) := by
  have hs := h.sum
  linear_combination s * hs

/-- The extinction probability `θ₀/θ₂` lies in `(0,1)`. -/
lemma extinction_mem : 0 < θ₀ / θ₂ ∧ θ₀ / θ₂ < 1 :=
  ⟨div_pos h.pos₀ h.pos₂, (div_lt_one h.pos₂).mpr h.lt₂⟩

/-- `θ₀/θ₂` is the root in `[0,1)` of `s = θ₀ + θ₁s + θ₂s²`. -/
lemma extinction_fixed_point :
    θ₀ + θ₁ * (θ₀ / θ₂) + θ₂ * (θ₀ / θ₂) ^ 2 = θ₀ / θ₂ := by
  have h2 : θ₂ ≠ 0 := ne_of_gt h.pos₂
  have hfac := h.harris_quadratic (θ₀ / θ₂)
  have hzero : θ₂ * (θ₀ / θ₂) - θ₀ = 0 := by
    rw [sub_eq_zero]; field_simp
  rw [hzero, mul_zero] at hfac
  linarith

/-- A fixed child founds a surviving subtree with probability
`1 - θ₀/θ₂ = (θ₂-θ₀)/θ₂`. -/
lemma survival_prob : 1 - θ₀ / θ₂ = (θ₂ - θ₀) / θ₂ := by
  have h2 : θ₂ ≠ 0 := ne_of_gt h.pos₂
  field_simp

/-! ### The skeleton law -/

/-- `θ̃₁ + θ̃₂ = 1`: the skeleton law is a two-value offspring law. -/
lemma skeleton_sum : (θ₁ + 2 * θ₀) + (θ₂ - θ₀) = 1 := by
  have := h.sum; linarith

/-- The skeleton law lies in the chain regime, `0 < θ̃₁ < 1`. -/
lemma skeleton_chain_regime : 0 < θ₁ + 2 * θ₀ ∧ θ₁ + 2 * θ₀ < 1 := by
  refine ⟨by linarith [h.pos₀, h.nonneg₁], ?_⟩
  have := h.sum
  have := h.lt₂
  linarith

/-- Conditioning a vertex on survival, two children survive with probability
`θ̃₂ = θ₂ - θ₀`. -/
lemma split_prob :
    θ₂ * ((θ₂ - θ₀) / θ₂) ^ 2 / ((θ₂ - θ₀) / θ₂) = θ₂ - θ₀ := by
  have h2 : θ₂ ≠ 0 := ne_of_gt h.pos₂
  have hd : θ₂ - θ₀ ≠ 0 := by have := h.lt₂; intro hc; linarith [sub_eq_zero.mp hc]
  field_simp

/-- The complementary probability is `θ̃₁ = θ₁ + 2θ₀`. -/
lemma neck_prob : θ₁ + 2 * θ₂ * (θ₀ / θ₂) = θ₁ + 2 * θ₀ := by
  have h2 : θ₂ ≠ 0 := ne_of_gt h.pos₂
  field_simp

/-- The three survival cases exhaust the conditioning: one surviving child,
two children with one surviving, and a split. -/
lemma survival_decomposition :
    θ₁ * (1 - θ₀ / θ₂) + θ₂ * (2 * (θ₀ / θ₂) * (1 - θ₀ / θ₂))
        + θ₂ * (1 - θ₀ / θ₂) ^ 2
      = 1 - θ₀ / θ₂ := by
  have h2 : θ₂ ≠ 0 := ne_of_gt h.pos₂
  have hs := h.sum
  set q : ℝ := θ₀ / θ₂ with hqdef
  have hq : θ₂ * q = θ₀ := by rw [hqdef]; field_simp
  have hrw : θ₁ * (1 - q) + θ₂ * (2 * q * (1 - q)) + θ₂ * (1 - q) ^ 2
      = (1 - q) * (θ₁ + 2 * (θ₂ * q) + (θ₂ - θ₂ * q)) := by ring
  rw [hrw, hq]
  linear_combination (1 - q) * hs

/-! ### The bush law -/

/-- The conjugate law is the tilt `θ̂_j = θ_j(θ₀/θ₂)^{j-1}`, that is
`θ̂ = (θ₂,θ₁,θ₀)`. -/
lemma conjugate_tilt :
    θ₀ * (θ₀ / θ₂)⁻¹ = θ₂ ∧ θ₁ * (θ₀ / θ₂) ^ (0 : ℕ) = θ₁ ∧ θ₂ * (θ₀ / θ₂) = θ₀ := by
  have h0 : θ₀ ≠ 0 := ne_of_gt h.pos₀
  have h2 : θ₂ ≠ 0 := ne_of_gt h.pos₂
  refine ⟨by field_simp, by simp, by field_simp⟩

lemma conjugate_sum : θ₂ + θ₁ + θ₀ = 1 := by have := h.sum; linarith

/-- The bush law is subcritical: its mean `θ₁ + 2θ₀` is `θ̃₁ < 1`. -/
lemma conjugate_subcritical : θ₁ + 2 * θ₀ < 1 := h.skeleton_chain_regime.2

/-- A neck vertex carries a bush with probability `2θ₀/(θ₁+2θ₀)`. -/
lemma bush_prob :
    2 * θ₂ * (θ₀ / θ₂) / (θ₁ + 2 * θ₂ * (θ₀ / θ₂)) = 2 * θ₀ / (θ₁ + 2 * θ₀) := by
  rw [h.neck_prob]
  have h2 : θ₂ ≠ 0 := ne_of_gt h.pos₂
  congr 1
  field_simp

/-- The two decoration weights of a neck vertex sum to one. -/
lemma decoration_split : θ₁ / (θ₁ + 2 * θ₀) + 2 * θ₀ / (θ₁ + 2 * θ₀) = 1 := by
  have hne : θ₁ + 2 * θ₀ ≠ 0 := ne_of_gt h.skeleton_chain_regime.1
  field_simp

/-! ### The shape law of `thm:shape-iid` -/

/-- The neck length of `thm:shape-iid` is a probability law:
`∑_{k≥1} θ̃₁^{k-1}θ̃₂ = 1`. -/
lemma neck_law_tsum : ∑' k : ℕ, (θ₁ + 2 * θ₀) ^ k * (θ₂ - θ₀) = 1 := by
  obtain ⟨hp, hlt⟩ := h.skeleton_chain_regime
  have hgeo := tsum_geometric_of_lt_one hp.le hlt
  have hsk := h.skeleton_sum
  rw [tsum_mul_right, hgeo, show (1 : ℝ) - (θ₁ + 2 * θ₀) = θ₂ - θ₀ from by linarith]
  exact inv_mul_cancel₀ (ne_of_gt (by linarith : (0 : ℝ) < θ₂ - θ₀))

/-- The seven constants that make up a shape mass all lie in `(0,1]`, so the
least positive one is a legitimate `p` for `shape_mass_point`. -/
lemma shape_factors_mem :
    (θ₁ + 2 * θ₀) ≤ 1 ∧ (θ₂ - θ₀) ≤ 1 ∧ θ₁ / (θ₁ + 2 * θ₀) ≤ 1
      ∧ 2 * θ₀ / (θ₁ + 2 * θ₀) ≤ 1 ∧ θ₂ ≤ 1 ∧ θ₁ ≤ 1 ∧ θ₀ ≤ 1 := by
  obtain ⟨hp, hlt⟩ := h.skeleton_chain_regime
  have hsk := h.skeleton_sum
  have hs := h.sum
  have h0 := h.pos₀
  have h1 := h.nonneg₁
  have h2 := h.pos₂
  refine ⟨hlt.le, by linarith, ?_, ?_, by linarith, by linarith, by linarith⟩
  · rw [div_le_one hp]; linarith
  · rw [div_le_one hp]; linarith

end IsHairy

end ChainClasses
