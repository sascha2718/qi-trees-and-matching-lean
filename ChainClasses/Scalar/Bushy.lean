import Mathlib.Tactic
import ChainClasses.Scalar.MarkedQI

/-!
`sec:shape-coupling` and the proposition labelled `thm:hairy` in
`gw_classes_simple.tex`: the sharpness discussion following
`thm:shape-coupling` and the two arithmetic steps of the proof of universality
in the bushy regime.  The historical word "hairy" is retained only in the
LaTeX labels `thm:hairy` and `eq:hairy-rate`.

`thm:hairy` assembles the argument, so what it adds on top of the lemmas it
quotes is the bookkeeping of the constants and the passage from a rate at each
scale `D` to an almost sure statement. Both are certified here, together with
the obstruction that makes `thm:shape-coupling` sharp.

* `dist_le_of_markedQI_subsingleton`: a shape comparable to a point at scale
  `K` has diameter at most `K²`. This is the sharpness discussion following
  `thm:shape-coupling`: for `θ₂ = 1` the
  shape law is the point mass at the one-vertex shape, so
  `it:shape-coupling-law` and `it:shape-coupling-qi` would bound the diameter
  of every shape of positive `μ'`-mass, which fails as soon as `μ'` gives
  positive mass to shapes of
  unbounded diameter.
* `coupling_scale` and `glued_scale`: the two constants of `eq:hairy-rate`,
  `3·(3·2·27D⁴)·2 = 972D⁴` for the two support fixes and
  `8(972D⁴)² = 8·972²D⁸` for the
  gluing.
* `bushy_rate_to_one`: the rates `16e^{-c₃D²}` tend to `0` along `D`, with an
  explicit threshold, which is the supremum over `D` in the last display of
  the proof.
-/

namespace ChainClasses

/-! ### Why the coupling statement is sharp -/

/-- **Sharpness of `thm:shape-coupling`.** A space `K`-comparable to a point has diameter at
most `K²`. Comparability to a point therefore cannot reach shapes of unbounded
diameter, whatever the scale. -/
theorem dist_le_of_markedQI_subsingleton {K : ℝ} {X Y : MarkedSpace}
    [Subsingleton Y.carrier] (h : MarkedQI K X Y) (x y : X.carrier) :
    dist x y ≤ K ^ 2 := by
  obtain ⟨f, hf⟩ := h
  have hzero : dist (f x) (f y) = 0 := by
    rw [Subsingleton.elim (f x) (f y), dist_self]
  have hlow := hf.lower x y
  rw [hzero, mul_zero, zero_add] at hlow
  calc dist x y ≤ K * K := hlow
    _ = K ^ 2 := (sq K).symm

/-- The contrapositive form used in the remark: a space of diameter exceeding
`K²` admits no `K`-marked quasi-isometry to a point. -/
theorem not_markedQI_subsingleton_of_dist_lt {K : ℝ} {X Y : MarkedSpace}
    [Subsingleton Y.carrier] {x y : X.carrier} (h : K ^ 2 < dist x y) :
    ¬ MarkedQI K X Y := fun hqi =>
  absurd (dist_le_of_markedQI_subsingleton hqi x y) (not_le.mpr h)

/-! ### The constants of `thm:hairy` -/

/-- The scale of `thm:shape-coupling`\ `it:shape-coupling-qi`: both ends may
sit off their supports, so the chain is `σ → σ° → σ'° → σ'`, a `2`-marked
support fix, the `27D⁴`-marked adjacency, and a second `2`-marked fix.  The
first two compose to `3·2·27D⁴ = 162D⁴` and that with the third to
`3·162D⁴·2 = 972D⁴`.  The shape-valued label of `ShapeCouplingSelf` reaches
the sharper `729D⁴`, the support fix being `1`-marked rather than `2`-marked. -/
lemma coupling_scale (D : ℝ) : 3 * (3 * 2 * (27 * D ^ 4)) * 2 = 972 * D ^ 4 := by ring

/-- The scale of `eq:hairy-rate`: `thm:glued-transfer` applied with
`K = 972D⁴` gives an `8·972²D⁸`-quasi-isometry. -/
lemma glued_scale (D : ℝ) : 8 * (972 * D ^ 4) ^ 2 = 8 * 972 ^ 2 * D ^ 8 := by ring

/-- **The last display of `thm:hairy`**: the failure rates `16e^{-c₃D²}` fall
below any threshold, so the events of `eq:hairy-rate` exhaust
`{𝒯 ≃ 𝒯'}` and the conclusion is almost sure. The threshold is explicit,
`D ≥ 16/(c₃ε) + 1`. -/
theorem bushy_rate_to_one {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → 16 * Real.exp (-(c * (D : ℝ) ^ 2)) < ε := by
  refine ⟨⌈16 / (c * ε)⌉₊ + 1, fun D hD => ?_⟩
  have hcast : ((⌈16 / (c * ε)⌉₊ + 1 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  push_cast at hcast
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) ⌈16 / (c * ε)⌉₊
    linarith
  have hlt : 16 / (c * ε) < (D : ℝ) := by
    have := Nat.le_ceil (16 / (c * ε))
    linarith
  have hsq : (D : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
  have hDsq : (0 : ℝ) < (D : ℝ) ^ 2 := by nlinarith
  set y : ℝ := c * (D : ℝ) ^ 2 with hy
  have hypos : 0 < y := mul_pos hc hDsq
  -- `y e^{-y} ≤ 1`, so `16 e^{-y} ≤ 16/y`
  have hkey : y * Real.exp (-y) ≤ 1 := by
    have h1 : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-y), mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-y)).le]
  -- and `y > 16/ε`
  have hylarge : 16 < y * ε := by
    have hce : 0 < c * ε := mul_pos hc hε
    rw [div_lt_iff₀ hce] at hlt
    rw [hy]
    nlinarith
  have hmul : y * (16 * Real.exp (-y)) < y * ε := by nlinarith [Real.exp_pos (-y)]
  exact lt_of_mul_lt_mul_left hmul hypos.le

end ChainClasses
