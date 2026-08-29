/-
The concrete monotone step functions of the `ν = δ₃` recursion
(`arbitrary_offspring_matching.tex`, proof of `thm:main-matching` at pure ternary
law): the common square-cell bound `delta3CB`, the ordinary step
function `delta3F`, the screen step function `delta3G`, their joint
monotonicity, and the screen-matrix row evaluations.  The assembled step
bounds (`delta3_Psi_step_assembled`, `delta3_E_step_assembled`) feed
these into the closure keystone `delta3_failure_uniform`.

* `delta3CB`: the resolved square-cell bound
  `c_A·a + c_B·a² + c_Z·b + 2b·(1 + α·a)`: every `δ₃` square cell's
  output screens sum to at most `2b` after diagonal pruning;
* `delta3Far` / `delta3FarMass`: the tilted and untilted far root
  masses;
* `delta3F`: the ordinary rows' common bound: root budget, square cell,
  and the quadratic cross term;
* `delta3G`: the screen rows' common bound: the far tilt against the
  square-cell moment, the tilt-split quadratic, the quadratic screens,
  and the far mass (the fresh-tilt row `e₄` vanishes identically by
  `screenE_tilt_self` and needs no budget);
* `delta3N_mulVec_three` / `delta3N_mulVec_four`: the two live rows of
  the screen matrix applied to an arbitrary screen vector.
-/
import GraphMarkovMatching.Delta3.Closure

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-- The tilted far root mass `∑_{v ↛ v0} μ(v)·r_μ(v)^{-α}`. -/
noncomputable def delta3Far : ℝ≥0∞ :=
  ∑' v, if Rv v v0 then 0 else μ v * (rE μ Rv v) ^ (-α)

/-- The untilted far root mass `∑_{v ↛ v0} μ(v)`. -/
noncomputable def delta3FarMass : ℝ≥0∞ :=
  ∑' v, if Rv v v0 then 0 else μ v

/-- The resolved square-cell bound: the one-cell row
`PhiDres_square_le` closes against the ordinary supremum `a` and the
screen supremum `b` in this shape, because every `δ₃` square cell's
four output screens sum to at most `2b` after diagonal pruning. -/
noncomputable def delta3CB (α δ L K : ℝ) (a b : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * a
    + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
      * a ^ 2
    + ENNReal.ofReal (2 * (1 + δ)) * b
    + 2 * b * (1 + ENNReal.ofReal α * a)

/-- The ordinary step function `f`: every ordinary row contributes at most the
root budget `η + φ(q(v0))`, one square cell, and the quadratic cross
term between them. -/
noncomputable def delta3F (δ L K : ℝ) (a b : ℝ≥0∞) : ℝ≥0∞ :=
  (etaG α Rv μ + phiE α (q μ Rv v0)) + delta3CB α δ L K a b
    + ENNReal.ofReal (2 * α)
      * ((etaG α Rv μ + phiE α (q μ Rv v0)) * delta3CB α δ L K a b)

/-- The screen step function `g`: the far tilt against the square-cell
moment, the tilt-split quadratic, the quadratic screens, and the far
mass.  The fresh-tilt row `e₄` needs no budget: its screen carries its
own tilt law in the zero list, so it vanishes identically
(`screenE_tilt_self`). -/
noncomputable def delta3G (δ L K : ℝ) (a b : ℝ≥0∞) : ℝ≥0∞ :=
  delta3Far α Rv μ v0 * (1 + ENNReal.ofReal α * delta3CB α δ L K a b)
    + 4 * (ENNReal.ofReal α * (delta3Tilt α Rv μ * (a * b)))
    + 3 * b ^ 2
    + delta3FarMass Rv μ v0

/-- The square-cell bound is monotone in both arguments. -/
lemma delta3CB_mono (α δ L K : ℝ) {a a' b b' : ℝ≥0∞}
    (ha : a ≤ a') (hb : b ≤ b') :
    delta3CB α δ L K a b ≤ delta3CB α δ L K a' b' := by
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
  · exact mul_le_mul_right ha _
  · exact mul_le_mul_right (pow_le_pow_left' ha 2) _
  · exact mul_le_mul_right hb _
  · exact mul_le_mul' (mul_le_mul_right hb 2)
      (add_le_add le_rfl (mul_le_mul_right ha _))

/-- The ordinary step function is monotone in both arguments. -/
lemma delta3F_mono (δ L K : ℝ) {a a' b b' : ℝ≥0∞}
    (ha : a ≤ a') (hb : b ≤ b') :
    delta3F α Rv μ v0 δ L K a b ≤ delta3F α Rv μ v0 δ L K a' b' := by
  refine add_le_add (add_le_add le_rfl (delta3CB_mono α δ L K ha hb)) ?_
  exact mul_le_mul_right
    (mul_le_mul_right (delta3CB_mono α δ L K ha hb) _) _

/-- The screen step function is monotone in both arguments. -/
lemma delta3G_mono (δ L K : ℝ) {a a' b b' : ℝ≥0∞}
    (ha : a ≤ a') (hb : b ≤ b') :
    delta3G α Rv μ v0 δ L K a b ≤ delta3G α Rv μ v0 δ L K a' b' := by
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) le_rfl
  · exact mul_le_mul_right
      (add_le_add le_rfl
        (mul_le_mul_right (delta3CB_mono α δ L K ha hb) _)) _
  · exact mul_le_mul_right
      (mul_le_mul_right (mul_le_mul_right (mul_le_mul' ha hb) _) _) _
  · exact mul_le_mul_right (pow_le_pow_left' hb 2) 3

/-- The square-cell bound sits inside the ordinary step function. -/
lemma delta3CB_le_F (δ L K : ℝ) (a b : ℝ≥0∞) :
    delta3CB α δ L K a b ≤ delta3F α Rv μ v0 δ L K a b :=
  le_trans le_add_self le_self_add

/-- The `e₂`-row of the screen matrix applied to a screen vector. -/
lemma delta3N_mulVec_three (E : Fin 5 → ℝ≥0∞) :
    mulVec (delta3N α Rv μ) E 3
      = delta3Tilt α Rv μ * E 0 + delta3Tilt α Rv μ * E 1 := by
  rw [mulVec, Fin.sum_univ_five,
    show delta3N α Rv μ 3 0 = delta3Tilt α Rv μ from by simp [delta3N],
    show delta3N α Rv μ 3 1 = delta3Tilt α Rv μ from by simp [delta3N],
    show delta3N α Rv μ 3 2 = 0 from by simp [delta3N],
    show delta3N α Rv μ 3 3 = 0 from by simp [delta3N],
    show delta3N α Rv μ 3 4 = 0 from by simp [delta3N]]
  ring

/-- The `z_{TZ}`-row of the screen matrix applied to a screen vector. -/
lemma delta3N_mulVec_four (E : Fin 5 → ℝ≥0∞) :
    mulVec (delta3N α Rv μ) E 4 = E 2 := by
  rw [mulVec, Fin.sum_univ_five,
    show delta3N α Rv μ 4 0 = 0 from by simp [delta3N],
    show delta3N α Rv μ 4 1 = 0 from by simp [delta3N],
    show delta3N α Rv μ 4 2 = 1 from by simp [delta3N],
    show delta3N α Rv μ 4 3 = 0 from by simp [delta3N],
    show delta3N α Rv μ 4 4 = 0 from by simp [delta3N]]
  ring

end GraphMarkovMatching
