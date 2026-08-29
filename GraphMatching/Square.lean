/-
`sec:contraction` of `graph_matching_selfcontained.tex`, the symmetrised square `R^□`
of `eq:square`, and the setup for the contraction `thm:contraction`.

This file (M6a) fixes the definitions and the structural facts:

* `SquareRel`      the relation `eq:square` on `X × X`
* refl / symm      preserved from `R`, as required to feed `R^□` back into
                   `thm:contraction`
* `aOverlap`       `a = μ{y : x₀ R y ∧ x₁ R y}`, the paper's `a`
* `cOverlap`       `c = μ{y : x₀ ⋡ y ∧ x₁ ⋡ y}`, the paper's `c`
* `aOverlap_le_rE` `a ≤ r_i`, since a single `Y` compatible with both is in
                   particular compatible with each (the paper's `a ≤ min(r₀,r₁)`)

The degree identities `eq:R-exact`, `eq:Q-union` and the contraction estimate
itself are M6b-e.
-/
import GraphMatching.Product

namespace GraphMatching

open scoped ENNReal Classical

variable {X : Type*}

/-! ### The symmetrised square, `eq:square` -/

/-- The symmetrised square `R^□` of `eq:square`:
`(x₀,x₁) R^□ (y₀,y₁) ↔ (x₀ R y₀ ∧ x₁ R y₁) ∨ (x₀ R y₁ ∧ x₁ R y₀)`.

The second disjunct crosses the coordinates; this is what distinguishes `R^□`
from the tensor square `ProdRel R R`, and it is exactly the "good antidiagonal"
of the transversal `thm:transversal`. -/
def SquareRel (R : X → X → Prop) : X × X → X × X → Prop :=
  fun x y => (R x.1 y.1 ∧ R x.2 y.2) ∨ (R x.1 y.2 ∧ R x.2 y.1)

lemma SquareRel_refl {R : X → X → Prop} (hrefl : ∀ x, R x x) (x : X × X) :
    SquareRel R x x :=
  Or.inl ⟨hrefl x.1, hrefl x.2⟩

lemma SquareRel_symm {R : X → X → Prop} (hsymm : ∀ a b, R a b → R b a) (x y : X × X) :
    SquareRel R x y → SquareRel R y x := by
  rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · exact Or.inl ⟨hsymm _ _ h₁, hsymm _ _ h₂⟩
  · exact Or.inr ⟨hsymm _ _ h₂, hsymm _ _ h₁⟩

/-! ### The one-variable overlaps `a` and `c` -/

/-- The paper's `a = μ{y : x₀ R y ∧ x₁ R y}`: the mass of labels compatible with
both `x₀` and `x₁`. -/
noncomputable def aOverlap (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) : ℝ≥0∞ :=
  ∑' y, if R x₀ y ∧ R x₁ y then μ y else 0

/-- The paper's `c = μ{y : x₀ ⋡ y ∧ x₁ ⋡ y}`: the mass of labels incompatible
with both. This is the per-column bad probability in the transversal argument. -/
noncomputable def cOverlap (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) : ℝ≥0∞ :=
  ∑' y, if ¬ R x₀ y ∧ ¬ R x₁ y then μ y else 0

/-- `a ≤ r₀`: a label compatible with both `x₀` and `x₁` is in particular
compatible with `x₀`. Half of the paper's `a ≤ min(r₀,r₁)`. -/
lemma aOverlap_le_rE_left (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    aOverlap μ R x₀ x₁ ≤ rE μ R x₀ := by
  rw [aOverlap, rE]
  refine ENNReal.tsum_le_tsum fun y => ?_
  by_cases h : R x₀ y ∧ R x₁ y
  · simp [h]
  · simp only [h, if_false]; positivity

/-- `a ≤ r₁`, the other half of `a ≤ min(r₀,r₁)`. -/
lemma aOverlap_le_rE_right (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    aOverlap μ R x₀ x₁ ≤ rE μ R x₁ := by
  rw [aOverlap, rE]
  refine ENNReal.tsum_le_tsum fun y => ?_
  by_cases h : R x₀ y ∧ R x₁ y
  · simp [h]
  · simp only [h, if_false]; positivity

/-- `c` is symmetric in its two arguments: the defining condition
`¬ R x₀ y ∧ ¬ R x₁ y` is unchanged when `x₀` and `x₁` are swapped. This is what
lets the two columns of the transversal array share one bad-column probability
in the union bound of M6b. -/
lemma cOverlap_symm (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    cOverlap μ R x₀ x₁ = cOverlap μ R x₁ x₀ := by
  rw [cOverlap, cOverlap]
  exact tsum_congr fun y => by
    by_cases h₀ : R x₀ y <;> by_cases h₁ : R x₁ y <;> simp [h₀, h₁]

/-! ### M6b: pair-sum helpers

The degrees of `R^□` are sums over pairs `(Y₀,Y₁)`. By Fubini's theorem, which
is immediate in `ℝ≥0∞`, they reduce to `tsum_prod_split` once each summand is reshaped, by a
coordinatewise case split, into a product of two one-coordinate weights. The
reshape is kept as an explicit `tsum_congr` at each use, rather than a lemma
abstracting the condition as a `Prop`: abstracting the condition forces the
`if` onto `Classical.propDecidable` of the whole conjunction, which then fails
to unify with the structural `instDecidableAnd` of a hand-written compound
condition. Keeping every condition hand-written keeps the `Decidable` instances
aligned. -/

/-- `∑' y, 𝟙[¬R x y] μ y = q(x)`: the negated-indicator form of the bad degree. -/
private lemma tsum_ite_not (μ : PMF X) (R : X → X → Prop) (x : X) :
    (∑' y, if ¬ R x y then μ y else 0) = qE μ R x := by
  rw [qE]; exact tsum_congr fun y => by by_cases h : R x y <;> simp [h]

/-! ### M6b: the good and bad degree of `R^□`, `eq:R-exact` and `eq:Q-union` -/

/-- **`eq:R-exact`**, the good-degree inclusion-exclusion for `R^□`, in additive
form (so no `ℝ≥0∞` subtraction): `r^□ + a² = 2 r₀ r₁`.

The two diagonals of the `2×2` array each succeed with probability `r₀ r₁`, and
both succeed exactly when each of `Y₀, Y₁` is compatible with both `x₀, x₁`, an
event of probability `a²`. Termwise, `𝟙[A∪B] + 𝟙[A∩B] = 𝟙[A] + 𝟙[B]`, and each
of the four sums factors by `tsum_prod_split`. -/
lemma rE_square_add_aOverlap_sq (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    rE (prodPMF μ μ) (SquareRel R) (x₀, x₁) + aOverlap μ R x₀ x₁ ^ 2
      = 2 * (rE μ R x₀ * rE μ R x₁) := by
  have hSq : (∑' p : X × X, if SquareRel R (x₀, x₁) p then μ p.1 * μ p.2 else 0)
      = rE (prodPMF μ μ) (SquareRel R) (x₀, x₁) := by
    rw [rE]; simp_rw [prodPMF_apply]
  have hInt : (∑' p : X × X,
        if (R x₀ p.1 ∧ R x₁ p.1) ∧ (R x₀ p.2 ∧ R x₁ p.2) then μ p.1 * μ p.2 else 0)
      = aOverlap μ R x₀ x₁ ^ 2 := by
    rw [show aOverlap μ R x₀ x₁ = ∑' y, if R x₀ y ∧ R x₁ y then μ y else 0 from rfl, pow_two]
    rw [tsum_congr fun p : X × X => show
        (if (R x₀ p.1 ∧ R x₁ p.1) ∧ (R x₀ p.2 ∧ R x₁ p.2) then μ p.1 * μ p.2 else 0)
          = (if R x₀ p.1 ∧ R x₁ p.1 then μ p.1 else 0) * (if R x₀ p.2 ∧ R x₁ p.2 then μ p.2 else 0)
        by by_cases h00 : R x₀ p.1 <;> by_cases h01 : R x₀ p.2 <;>
             by_cases h10 : R x₁ p.1 <;> by_cases h11 : R x₁ p.2 <;> simp [h00, h01, h10, h11]]
    exact tsum_prod_split (fun y => if R x₀ y ∧ R x₁ y then μ y else 0)
      (fun y => if R x₀ y ∧ R x₁ y then μ y else 0)
  have hA : (∑' p : X × X, if R x₀ p.1 ∧ R x₁ p.2 then μ p.1 * μ p.2 else 0)
      = rE μ R x₀ * rE μ R x₁ := by
    rw [tsum_congr fun p : X × X => show
        (if R x₀ p.1 ∧ R x₁ p.2 then μ p.1 * μ p.2 else 0)
          = (if R x₀ p.1 then μ p.1 else 0) * (if R x₁ p.2 then μ p.2 else 0)
        by by_cases ha : R x₀ p.1 <;> by_cases hb : R x₁ p.2 <;> simp [ha, hb]]
    exact tsum_prod_split (fun y => if R x₀ y then μ y else 0) (fun y => if R x₁ y then μ y else 0)
  have hB : (∑' p : X × X, if R x₁ p.1 ∧ R x₀ p.2 then μ p.1 * μ p.2 else 0)
      = rE μ R x₁ * rE μ R x₀ := by
    rw [tsum_congr fun p : X × X => show
        (if R x₁ p.1 ∧ R x₀ p.2 then μ p.1 * μ p.2 else 0)
          = (if R x₁ p.1 then μ p.1 else 0) * (if R x₀ p.2 then μ p.2 else 0)
        by by_cases ha : R x₁ p.1 <;> by_cases hb : R x₀ p.2 <;> simp [ha, hb]]
    exact tsum_prod_split (fun y => if R x₁ y then μ y else 0) (fun y => if R x₀ y then μ y else 0)
  have hadd : (∑' p : X × X, if SquareRel R (x₀, x₁) p then μ p.1 * μ p.2 else 0)
        + (∑' p : X × X,
            if (R x₀ p.1 ∧ R x₁ p.1) ∧ (R x₀ p.2 ∧ R x₁ p.2) then μ p.1 * μ p.2 else 0)
      = (∑' p : X × X, if R x₀ p.1 ∧ R x₁ p.2 then μ p.1 * μ p.2 else 0)
        + (∑' p : X × X, if R x₁ p.1 ∧ R x₀ p.2 then μ p.1 * μ p.2 else 0) := by
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun p => ?_
    by_cases h00 : R x₀ p.1 <;> by_cases h01 : R x₀ p.2 <;>
      by_cases h10 : R x₁ p.1 <;> by_cases h11 : R x₁ p.2 <;>
      simp [SquareRel, h00, h01, h10, h11]
  rw [hSq, hInt, hA, hB] at hadd
  rw [hadd]; ring

/-- **`eq:Q-union`**, the bad-degree union bound for `R^□`: `q^□ ≤ q₀² + q₁² + 2c`.

A pair `(Y₀,Y₁)` fails to give a good transversal exactly when
`(x₀,x₁) ⋠^□ (Y₀,Y₁)`; by the `2×2` transversal (`thm:transversal`, here the same
finite propositional fact dispatched by `tauto`) this forces a bad row or a bad
column. The four bad-line events have probabilities `q₀²`, `q₁²`, `c`, `c`, and
the pointwise indicator bound is the union bound. -/
lemma qE_square_le (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    qE (prodPMF μ μ) (SquareRel R) (x₀, x₁)
      ≤ qE μ R x₀ ^ 2 + qE μ R x₁ ^ 2 + 2 * cOverlap μ R x₀ x₁ := by
  have hq : qE (prodPMF μ μ) (SquareRel R) (x₀, x₁)
      = ∑' p : X × X, if SquareRel R (x₀, x₁) p then 0 else μ p.1 * μ p.2 := by
    rw [qE]; simp_rw [prodPMF_apply]
  -- pointwise union bound: a pair with no good transversal lands in one of the
  -- four bad lines (`thm:transversal`), so its weight is at most their indicator sum.
  have hpoint : ∀ p : X × X,
      (if SquareRel R (x₀, x₁) p then 0 else μ p.1 * μ p.2)
        ≤ (if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then μ p.1 * μ p.2 else 0)
          + (if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then μ p.1 * μ p.2 else 0)
          + (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then μ p.1 * μ p.2 else 0)
          + (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then μ p.1 * μ p.2 else 0) := by
    intro p
    by_cases hsq : SquareRel R (x₀, x₁) p
    · rw [if_pos hsq]; exact zero_le
    · rw [if_neg hsq]
      have hcov : (¬ R x₀ p.1 ∧ ¬ R x₀ p.2) ∨ (¬ R x₁ p.1 ∧ ¬ R x₁ p.2)
                ∨ (¬ R x₀ p.1 ∧ ¬ R x₁ p.1) ∨ (¬ R x₀ p.2 ∧ ¬ R x₁ p.2) := by
        by_contra hc
        exact hsq (by show (R x₀ p.1 ∧ R x₁ p.2) ∨ (R x₀ p.2 ∧ R x₁ p.1); tauto)
      set w := μ p.1 * μ p.2
      set t0 := (if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then w else 0)
      set t1 := (if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then w else 0)
      set t2 := (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then w else 0)
      set t3 := (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then w else 0)
      rcases hcov with h | h | h | h
      · calc w = t0 := (if_pos h).symm
          _ ≤ t0 + t1 := le_self_add
          _ ≤ t0 + t1 + t2 := le_self_add
          _ ≤ t0 + t1 + t2 + t3 := le_self_add
      · calc w = t1 := (if_pos h).symm
          _ ≤ t0 + t1 := le_add_self
          _ ≤ t0 + t1 + t2 := le_self_add
          _ ≤ t0 + t1 + t2 + t3 := le_self_add
      · calc w = t2 := (if_pos h).symm
          _ ≤ t0 + t1 + t2 := le_add_self
          _ ≤ t0 + t1 + t2 + t3 := le_self_add
      · calc w = t3 := (if_pos h).symm
          _ ≤ t0 + t1 + t2 + t3 := le_add_self
  -- the four bad-line probabilities
  have h0 : (∑' p : X × X, if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then μ p.1 * μ p.2 else 0)
      = qE μ R x₀ ^ 2 := by
    rw [tsum_congr fun p : X × X => show
        (if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then μ p.1 * μ p.2 else 0)
          = (if ¬ R x₀ p.1 then μ p.1 else 0) * (if ¬ R x₀ p.2 then μ p.2 else 0)
        by by_cases ha : R x₀ p.1 <;> by_cases hb : R x₀ p.2 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => if ¬ R x₀ y then μ y else 0) (fun y => if ¬ R x₀ y then μ y else 0),
      tsum_ite_not, pow_two]
  have h1 : (∑' p : X × X, if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then μ p.1 * μ p.2 else 0)
      = qE μ R x₁ ^ 2 := by
    rw [tsum_congr fun p : X × X => show
        (if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then μ p.1 * μ p.2 else 0)
          = (if ¬ R x₁ p.1 then μ p.1 else 0) * (if ¬ R x₁ p.2 then μ p.2 else 0)
        by by_cases ha : R x₁ p.1 <;> by_cases hb : R x₁ p.2 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => if ¬ R x₁ y then μ y else 0) (fun y => if ¬ R x₁ y then μ y else 0),
      tsum_ite_not, pow_two]
  have h2 : (∑' p : X × X, if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then μ p.1 * μ p.2 else 0)
      = cOverlap μ R x₀ x₁ := by
    rw [show cOverlap μ R x₀ x₁ = ∑' y, if ¬ R x₀ y ∧ ¬ R x₁ y then μ y else 0 from rfl]
    rw [tsum_congr fun p : X × X => show
        (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then μ p.1 * μ p.2 else 0)
          = (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then μ p.1 else 0) * μ p.2
        by by_cases ha : R x₀ p.1 <;> by_cases hb : R x₁ p.1 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => if ¬ R x₀ y ∧ ¬ R x₁ y then μ y else 0) (fun y => μ y),
      μ.tsum_coe, mul_one]
  have h3 : (∑' p : X × X, if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then μ p.1 * μ p.2 else 0)
      = cOverlap μ R x₀ x₁ := by
    rw [show cOverlap μ R x₀ x₁ = ∑' y, if ¬ R x₀ y ∧ ¬ R x₁ y then μ y else 0 from rfl]
    rw [tsum_congr fun p : X × X => show
        (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then μ p.1 * μ p.2 else 0)
          = μ p.1 * (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then μ p.2 else 0)
        by by_cases ha : R x₀ p.2 <;> by_cases hb : R x₁ p.2 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => μ y) (fun y => if ¬ R x₀ y ∧ ¬ R x₁ y then μ y else 0),
      μ.tsum_coe, one_mul]
  rw [hq]
  calc ∑' p : X × X, (if SquareRel R (x₀, x₁) p then 0 else μ p.1 * μ p.2)
      ≤ ∑' p : X × X,
          ((if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then μ p.1 * μ p.2 else 0)
            + (if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then μ p.1 * μ p.2 else 0)
            + (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then μ p.1 * μ p.2 else 0)
            + (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then μ p.1 * μ p.2 else 0)) :=
        ENNReal.tsum_le_tsum hpoint
    _ = (∑' p : X × X, if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then μ p.1 * μ p.2 else 0)
          + (∑' p : X × X, if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then μ p.1 * μ p.2 else 0)
          + (∑' p : X × X, if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then μ p.1 * μ p.2 else 0)
          + (∑' p : X × X, if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then μ p.1 * μ p.2 else 0) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    _ = qE μ R x₀ ^ 2 + qE μ R x₁ ^ 2 + 2 * cOverlap μ R x₀ x₁ := by
        rw [h0, h1, h2, h3]; ring

end GraphMatching
