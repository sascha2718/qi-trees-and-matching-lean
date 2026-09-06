import Mathlib.Tactic

/-!
`sec:general-shapes` of `matching_classes_general.tex`: the obstruction of
`thm:split-joint`.

The joint law `eq:split-joint` of the arity `k` and the bush count `r` at a
split gives positive mass to `(J,0)` and `(2,J-2)`, by `θ_J > 0` and
`q > 0`, and none to `(J,J-2)`, since `2J-2 > J`.  A product law giving
positive mass to the first two points gives positive mass to the third, so
for `J ≥ 3` the joint law is a product for no offspring law, which is the
obstruction the transport relabelling of `sec:general-relabel` resolves.

* `splitJoint`: `eq:split-joint` up to its normalisation, which a
  factorisation would have to absorb into one of the factors.
* `splitJoint_pos`, `splitJoint_vanish`: the support points.
* `splitJoint_not_product`: no factorisation `g(k)h(r)` exists, for any real
  factors whatsoever.
-/

namespace ChainClasses

/-- **`eq:split-joint`** up to normalisation: the joint weight of a split of
arity `k` carrying `r` bushes, `θ_{k+r} C(k+r,k) (1-q)^k q^r`. -/
noncomputable def splitJoint (θ : ℕ → ℝ) (q : ℝ) (k r : ℕ) : ℝ :=
  θ (k + r) * ((k + r).choose k : ℝ) * (1 - q) ^ k * q ^ r

/-- The support, positive part: every pair with `θ_{k+r} > 0` carries
positive weight. -/
lemma splitJoint_pos {θ : ℕ → ℝ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {k r : ℕ} (hθ : 0 < θ (k + r)) : 0 < splitJoint θ q k r :=
  mul_pos (mul_pos (mul_pos hθ
    (by exact_mod_cast Nat.choose_pos (Nat.le_add_right k r)))
    (pow_pos (by linarith) k)) (pow_pos hq0 r)

/-- The support, vanishing part: beyond the support bound the weight
is zero. -/
lemma splitJoint_vanish {θ : ℕ → ℝ} (q : ℝ) {J k r : ℕ}
    (hvan : ∀ j, J < j → θ j = 0) (h : J < k + r) : splitJoint θ q k r = 0 := by
  unfold splitJoint
  rw [hvan _ h]
  ring

/-- **`thm:split-joint`**: for `J ≥ 3` the joint law of arity and bush count at a
split factors as `g(k)h(r)` for no real factors at all: the support contains
`(J,0)` and `(2,J-2)` but not `(J,J-2)`. -/
theorem splitJoint_not_product {J : ℕ} {θ : ℕ → ℝ} {q : ℝ} (hJ : 3 ≤ J)
    (hpos : 0 < θ J) (hvan : ∀ j, J < j → θ j = 0)
    (hq0 : 0 < q) (hq1 : q < 1) :
    ¬ ∃ g h : ℕ → ℝ, ∀ k r, splitJoint θ q k r = g k * h r := by
  rintro ⟨g, h, hfac⟩
  have hbr : 2 + (J - 2) = J := by omega
  have h1 : 0 < splitJoint θ q J 0 :=
    splitJoint_pos hq0 hq1 (k := J) (r := 0) (by rwa [Nat.add_zero])
  have h2 : 0 < splitJoint θ q 2 (J - 2) :=
    splitJoint_pos hq0 hq1 (k := 2) (r := J - 2) (by rwa [hbr])
  have h3 : splitJoint θ q J (J - 2) = 0 :=
    splitJoint_vanish q hvan (by omega)
  rw [hfac J 0] at h1
  rw [hfac 2 (J - 2)] at h2
  rw [hfac J (J - 2)] at h3
  have hgb : g J ≠ 0 := fun hz => by
    rw [hz, zero_mul] at h1
    exact lt_irrefl 0 h1
  have hhr : h (J - 2) ≠ 0 := fun hz => by
    rw [hz, mul_zero] at h2
    exact lt_irrefl 0 h2
  exact mul_ne_zero hgb hhr h3

end ChainClasses