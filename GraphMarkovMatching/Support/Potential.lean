/-
The countable probability space `(X, μ)` with a symmetric reflexive relation
`R`, the bad and good degrees `q` and `r`, and the potential `Φ(R,μ)` (the
diagonal case of `arbitrary_offspring_matching.tex` `sec:four-law`).

Design:

* `μ : PMF X`. Note this needs **no** `[Countable X]` hypothesis: a `PMF`
  sums to `1`, which forces its support to be countable automatically, so
  the standing countability assumption is encoded rather than assumed.
* No finiteness. Sums are `tsum`, and working in `ℝ≥0∞` makes them
  unconditionally summable by Fubini's theorem.
* `Φ` lands in `ℝ≥0∞`: the value `Φ = ∞` is meaningful and allowed.
-/
import GraphMarkovMatching.Support.Phi
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace GraphMarkovMatching.Support

open scoped ENNReal Classical

variable {X : Type*} {μ : PMF X} {R : X → X → Prop} {x y : X}

/-! ### The two degrees -/

/-- The good degree `r(x) = μ{y : x R y}` of §2. -/
noncomputable def rE (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ∑' y, if R x y then μ y else 0

/-- The bad degree `q(x) = μ{y : ¬ x R y}` of §2. -/
noncomputable def qE (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ∑' y, if R x y then 0 else μ y

/-- `r(x) + q(x) = 1`: the two degrees partition the total mass. -/
lemma rE_add_qE (μ : PMF X) (R : X → X → Prop) (x : X) : rE μ R x + qE μ R x = 1 := by
  rw [rE, qE, ← ENNReal.tsum_add, ← μ.tsum_coe]
  exact tsum_congr fun y => by split_ifs <;> simp

lemma qE_le_one : qE μ R x ≤ 1 := by
  rw [← rE_add_qE μ R x]; exact le_add_self

lemma rE_le_one : rE μ R x ≤ 1 := by
  rw [← rE_add_qE μ R x]; exact le_self_add

lemma qE_ne_top : qE μ R x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top qE_le_one

lemma rE_ne_top : rE μ R x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top rE_le_one

/-- Reflexivity puts `x`'s own mass into the good degree: `μ{x} ≤ r(x)`. This
is the observation of §2 that makes `q < 1` on the support. -/
lemma le_rE_of_refl (hrefl : R x x) : μ x ≤ rE μ R x := by
  rw [rE]
  calc (μ x : ℝ≥0∞) = if R x x then μ x else 0 := by simp [hrefl]
    _ ≤ ∑' y, if R x y then μ y else 0 := ENNReal.le_tsum x

/-! ### The potential, eq (9)

Both degrees are finite (`≤ 1`), so it is cleanest to pass to `ℝ` once and do
the `q < 1` arithmetic there with `linarith`, rather than fight truncated
subtraction in `ℝ≥0∞`. -/

/-- The bad degree as a real number. On the support it lies in `[0,1)`, by
`q_nonneg` and `q_lt_one`. -/
noncomputable def q (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ := (qE μ R x).toReal

/-- The real form of `r + q = 1`, available because both degrees are finite. -/
lemma toReal_rE_add_toReal_qE (μ : PMF X) (R : X → X → Prop) (x : X) :
    (rE μ R x).toReal + (qE μ R x).toReal = 1 := by
  rw [← ENNReal.toReal_add rE_ne_top qE_ne_top, rE_add_qE, ENNReal.toReal_one]

lemma q_nonneg : 0 ≤ q μ R x := ENNReal.toReal_nonneg

lemma q_le_one : q μ R x ≤ 1 := by
  have h := toReal_rE_add_toReal_qE μ R x
  have : (0 : ℝ) ≤ (rE μ R x).toReal := ENNReal.toReal_nonneg
  rw [q]; linarith

/-- **`q(x) < 1` on the support.** This is exactly the point the LaTeX was
tightened to make: off the support `q(x) = 1` is possible and `φ(q(x))` is then
undefined; reflexivity together with `μ{x} > 0` is what rules it out. -/
lemma q_lt_one (hrefl : R x x) (hx : μ x ≠ 0) : q μ R x < 1 := by
  have h := toReal_rE_add_toReal_qE μ R x
  have h1 : (0 : ℝ) < (μ x).toReal := ENNReal.toReal_pos hx (μ.apply_ne_top x)
  have h2 : (μ x).toReal ≤ (rE μ R x).toReal :=
    ENNReal.toReal_mono rE_ne_top (le_rE_of_refl hrefl)
  rw [q]; linarith

/-- The `ℝ≥0∞` form of `q_lt_one`. -/
lemma qE_lt_one (hrefl : R x x) (hx : μ x ≠ 0) : qE μ R x < 1 := by
  rw [← ENNReal.toReal_lt_toReal qE_ne_top ENNReal.one_ne_top, ENNReal.toReal_one]
  exact q_lt_one hrefl hx

/-- **The potential** `Φ(R,μ) = 𝔼 φ(q(X)) = ∑_{x ∈ S} μ{x} φ(q(x))`.

The sum may be read over the support `S` alone, where `q(x) < 1` keeps
`φ(q(x))` defined: the `tsum` over all of `X` agrees, since off the support
`μ x = 0` annihilates the term, and in `ℝ≥0∞` this is unconditional
(`0 * ⊤ = 0`). So the formal statement needs no support side condition; see
`Phi_summand_eq_zero`. -/
noncomputable def Phi (α : ℝ) (μ : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, μ x * ENNReal.ofReal (phi α (q μ R x))

/-- Off the support the summand vanishes, so the `tsum` over `X` in `Phi` is
the sum over the support `S`. -/
lemma Phi_summand_eq_zero {α : ℝ} (hx : μ x = 0) :
    μ x * ENNReal.ofReal (phi α (q μ R x)) = 0 := by
  simp [hx]

/-- Each summand of `Φ` is bounded below by `μ{x} · q(x)`, since `t ≤ φ_α t`.
This is the step `P(fail) = 𝔼 q ≤ 𝔼 φ(q) = Φ` used at the end of the
reduction, in one-summand form. -/
lemma mul_q_le_summand {α : ℝ} (hα : 0 ≤ α) (hrefl : R x x) (hx : μ x ≠ 0) :
    μ x * ENNReal.ofReal (q μ R x) ≤ μ x * ENNReal.ofReal (phi α (q μ R x)) := by
  gcongr
  exact le_phi hα q_nonneg (q_lt_one hrefl hx)

/-! ### Symmetry -/

/-- Symmetry of `R` identifies the "in-degree" with the bad degree:
`μ{x : ¬ x R y} = q(y)`.

This is the step `𝔼_X 1_{X ⋡ y} = q(y)` in the second-term estimate of
Lemma 2.1, and it is the *only* place symmetry is used there. It is also
load-bearing: the numerical search found reflexive but non-symmetric relations
where Lemma 2.1 fails outright (the potential doubles instead of contracting),
so this lemma cannot be dispensed with. -/
lemma tsum_not_rel_eq_qE (hsymm : ∀ a b, R a b → R b a) (μ : PMF X) (y : X) :
    (∑' x, if R x y then 0 else μ x) = qE μ R y := by
  rw [qE]
  exact tsum_congr fun x => by
    by_cases h : R x y
    · rw [if_pos h, if_pos (hsymm x y h)]
    · rw [if_neg h, if_neg (fun hc => h (hsymm y x hc))]

end GraphMarkovMatching.Support
