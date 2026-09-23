/-
`sec:contraction` of `graph_matching_selfcontained.tex`: the countable probability
space `(X, μ)` with a symmetric reflexive relation `R`, the bad and good
degrees `q` and `r`, and the potential `Φ(R,μ)` of `eq:iid-potential`.

Design:

* D1: `μ : PMF X`. Note this needs **no** `[Countable X]` hypothesis: a `PMF`
  sums to `1`, which forces its support to be countable automatically. So the
  paper's standing countability assumption is encoded rather than assumed.
* D2: no finiteness. Sums are `tsum`, and working in `ℝ≥0∞` makes them
  unconditionally summable, which is what the paper gets from Fubini's theorem.
* `Φ` lands in `ℝ≥0∞` since the paper explicitly allows `Φ = ∞`.
-/
import GraphMatching.Phi
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace GraphMatching

open scoped ENNReal Classical

variable {X : Type*} {μ : PMF X} {R : X → X → Prop} {x y : X}

/-! ### The two degrees -/

/-- The good degree `r(x) = μ{y : x R y}` of `sec:contraction`. -/
noncomputable def rE (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ∑' y, if R x y then μ y else 0

/-- The bad degree `q(x) = μ{y : ¬ x R y}` of `sec:contraction`. -/
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
is the observation of `sec:contraction` that makes `q < 1` on the support. -/
lemma le_rE_of_refl (hrefl : R x x) : μ x ≤ rE μ R x := by
  rw [rE]
  calc (μ x : ℝ≥0∞) = if R x x then μ x else 0 := by simp [hrefl]
    _ ≤ ∑' y, if R x y then μ y else 0 :=
        ENNReal.le_tsum (f := fun y => if R x y then μ y else 0) x

/-! ### The potential, `eq:iid-potential`

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

/-- **`eq:iid-potential`**: the potential `Φ(R,μ) = 𝔼 φ(q(X)) = ∑_{x ∈ S} μ{x} φ(q(x))`.

The paper restricts the sum to the support `S`, because `φ(q(x))` is undefined
where `q(x) = 1`. Here the `tsum` ranges over all of `X` and still agrees with
the paper's sum: off the support `μ x = 0` annihilates the term, and in `ℝ≥0∞`
this is unconditional (`0 * ⊤ = 0`). So the formal statement needs no support
side condition; see `Phi_summand_eq_zero`. -/
noncomputable def Phi (μ : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, μ x * ENNReal.ofReal (phi (q μ R x))

/-- **`eq:iid-potential`** at a general exponent: `Φ_α(R,μ) = 𝔼 φ_α(q(X))`. The paper
defines the potential with the exponent free and pins it only at `thm:contraction`,
so the statements that do not use the value are proved here at `PhiA` and read off at
`alpha`. -/
noncomputable def PhiA (α : ℝ) (μ : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, μ x * ENNReal.ofReal (phiA α (q μ R x))

lemma Phi_eq_PhiA (μ : PMF X) (R : X → X → Prop) : Phi μ R = PhiA alpha μ R := rfl

/-- Off the support the summand vanishes, so the `tsum` over `X` in `Phi` is
the paper's sum over `S`. -/
lemma Phi_summand_eq_zero (hx : μ x = 0) : μ x * ENNReal.ofReal (phi (q μ R x)) = 0 := by
  simp [hx]

/-- Each summand of `Φ_α` is bounded below by `μ{x} · q(x)`, since `t ≤ φ_α t`
(`eq:phi-dominates`). This is the step `P(fail) = 𝔼 q ≤ 𝔼 φ_α(q) = Φ_α` used at the
end of `thm:reduction`, in one-summand form; the exponent enters only through
`eq:phi-dominates`, so `α ≥ 0` suffices. -/
lemma mul_q_le_summandA {α : ℝ} (hα : 0 ≤ α) (hrefl : R x x) (hx : μ x ≠ 0) :
    μ x * ENNReal.ofReal (q μ R x) ≤ μ x * ENNReal.ofReal (phiA α (q μ R x)) := by
  gcongr
  exact le_phiA hα q_nonneg (q_lt_one hrefl hx)

/-- The one-summand bound at `α = 5/2`. -/
lemma mul_q_le_summand (hrefl : R x x) (hx : μ x ≠ 0) :
    μ x * ENNReal.ofReal (q μ R x) ≤ μ x * ENNReal.ofReal (phi (q μ R x)) :=
  mul_q_le_summandA alpha_nonneg hrefl hx

/-! ### Symmetry -/

/-- Symmetry of `R` identifies the "in-degree" with the bad degree:
`μ{x : ¬ x R y} = q(y)`.

This is the step `𝔼_X 1_{X ⋡ y} = q(y)` in the second-term estimate of
`thm:contraction`, and it is the *only* place symmetry is used there. It is also
load-bearing: the numerical search found reflexive but non-symmetric relations
where `thm:contraction` fails outright (the potential doubles instead of contracting),
so this lemma cannot be dispensed with. -/
lemma tsum_not_rel_eq_qE (hsymm : ∀ a b, R a b → R b a) (μ : PMF X) (y : X) :
    (∑' x, if R x y then 0 else μ x) = qE μ R y := by
  rw [qE]
  exact tsum_congr fun x => by
    by_cases h : R x y
    · rw [ite_eq_left h, ite_eq_left (hsymm x y h)]
    · rw [ite_eq_right h, ite_eq_right (fun hc => h (hsymm y x hc))]

end GraphMatching
