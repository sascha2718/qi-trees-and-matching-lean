/-
Screens for the arbitrary-support varying-offspring recursion
(`arbitrary_offspring_matching.tex` `sec:process`, `sec:screens`):

* `rE_bind`: the fresh-mixture identity `r_{·|F} = ∑_k ν_k r_{·|F_k}` for
  good degrees (Lemma `thm:fresh-mixture`, `eq:fresh-mixture`);
* `rE_bind_eq_zero_iff`: a zero degree toward the fresh mixture forces a
  zero degree toward every charged component;
* `mul_rE_le_rE_bind`: the first-positive-component minorization
  (before the `ν_*` normalization);
* `screenE`: normalized screens as tilted integrals over a zero event
  (Definition `def:screen`);
* `screen_mass_le`: the zero-event mass is at most the screen value
  (`eq:screen-mass`);
* `screenE_self_mem`: **diagonal pruning** (Lemma `thm:pruning`): a screen
  whose zero list contains its own cell law vanishes identically, because
  reflexivity puts every support atom's own mass into the good degree.
-/
import GraphMarkovMatching.Process.Basic

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

/-! ### The fresh-mixture identity (`thm:fresh-mixture`) -/

/-- The good indicator `𝟙[R z y]` as an `ℝ≥0∞` weight. -/
noncomputable def goodInd (R : X → X → Prop) (z y : X) : ℝ≥0∞ :=
  if R z y then 1 else 0

/-- `r_ν(z) = 𝔼_ν 𝟙[z ∼ ·]`: the good degree in the linear normal form. -/
lemma rE_eq_tsum_mul (ν : PMF X) (R : X → X → Prop) (z : X) :
    rE ν R z = ∑' y, ν y * goodInd R z y := by
  rw [rE]
  exact tsum_congr fun y => by by_cases h : R z y <;> simp [goodInd, h]

/-- The good degree under a pushforward column law. -/
lemma rE_map {A : Type u} (μ : PMF A) (g : A → X) (R : X → X → Prop) (z : X) :
    rE (μ.map g) R z = ∑' a, μ a * goodInd R z (g a) := by
  rw [rE_eq_tsum_mul, tsum_map_mul]

/-- The good degree toward a mixture is the mixture of component good
degrees: `r_{·|F} = ∑_k ν_k r_{·|F_k}` (`eq:fresh-mixture`). -/
lemma rE_bind {A : Type u} (w : PMF A) (f : A → PMF X) (R : X → X → Prop)
    (z : X) :
    rE (w.bind f) R z = ∑' a, w a * rE (f a) R z := by
  rw [rE_eq_tsum_mul, tsum_bind_mul]
  exact tsum_congr fun a => by rw [rE_eq_tsum_mul]

/-- A zero degree toward the fresh mixture forces a zero degree toward every
component the mixture charges (the zero direction of `thm:fresh-mixture`). -/
lemma rE_bind_eq_zero_iff {A : Type u} (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) (z : X) :
    rE (w.bind f) R z = 0 ↔ ∀ a, w a = 0 ∨ rE (f a) R z = 0 := by
  rw [rE_bind, ENNReal.tsum_eq_zero]
  exact forall_congr' fun a => mul_eq_zero

/-- The first-positive-component minorization (`thm:mixture-tilt`): one
charged component already bounds the mixture degree from below. -/
lemma mul_rE_le_rE_bind {A : Type u} (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) (z : X) (a : A) :
    w a * rE (f a) R z ≤ rE (w.bind f) R z := by
  rw [rE_bind]
  exact ENNReal.le_tsum a

/-! ### Screens (`def:screen`) -/

/-- The zero-event indicator of a list of target laws: `1` exactly when the
source point has zero good degree toward every law in the list. -/
noncomputable def screenInd (R : X → X → Prop) (zs : List (PMF X)) (x : X) :
    ℝ≥0∞ :=
  if ∀ ρ ∈ zs, rE ρ R x = 0 then 1 else 0

/-- The zero-event indicator is at most one. -/
lemma screenInd_le_one (R : X → X → Prop) (zs : List (PMF X)) (x : X) :
    screenInd R zs x ≤ 1 := by
  rw [screenInd]
  split_ifs <;> simp

/-- Distributing a two-term pointwise bound over a weighted, indicated
sum. -/
lemma tsum_ind_split (ρs : PMF X) (c W P Q : X → ℝ≥0∞) (hW : ∀ y, W y ≤ P y + Q y) :
    ∑' y, ρs y * (c y * W y)
      ≤ (∑' y, ρs y * (c y * P y)) + ∑' y, ρs y * (c y * Q y) := by
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun y => ?_
  calc ρs y * (c y * W y)
      ≤ ρs y * (c y * (P y + Q y)) :=
        mul_le_mul_right (mul_le_mul_right (hW y) _) _
    _ = ρs y * (c y * P y) + ρs y * (c y * Q y) := by ring

/-- The normalized screen `𝓔(ρ_s; z ↛ g)`: the `g`-tilted mass of the zero
event of the list `zs` under the cell law `ρs`.  The normalization `g` is
a single inverse degree (a diagonal reserve or a positive alternative); its
choice is left free here. -/
noncomputable def screenE (ρs : PMF X) (R : X → X → Prop) (zs : List (PMF X))
    (g : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, ρs x * screenInd R zs x * g x

/-- The zero-event mass is at most the screen value once the normalization
dominates `1` (`eq:screen-mass`; degrees are at most one, so inverse degrees
dominate one). -/
lemma screen_mass_le (ρs : PMF X) (R : X → X → Prop) (zs : List (PMF X))
    {g : X → ℝ≥0∞} (hg : ∀ x, 1 ≤ g x) :
    (∑' x, ρs x * screenInd R zs x) ≤ screenE ρs R zs g := by
  refine ENNReal.tsum_le_tsum fun x => ?_
  conv_lhs => rw [← mul_one (ρs x * screenInd R zs x)]
  exact mul_le_mul_right (hg x) _

/-- **Diagonal pruning** (`thm:pruning`): a screen whose zero list contains
its own cell law is identically zero, because at every support atom the
reflexive relation retains the atom's own mass in the good degree. -/
theorem screenE_self_mem (ρs : PMF X) (R : X → X → Prop) (zs : List (PMF X))
    (g : X → ℝ≥0∞) (hmem : ρs ∈ zs) (hrefl : ∀ x, R x x) :
    screenE ρs R zs g = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : ρs x = 0
  · simp [hx]
  · have hle : ρs x ≤ rE ρs R x := le_rE_of_refl (hrefl x)
    have hne : rE ρs R x ≠ 0 := fun h0 =>
      hx (le_antisymm (h0 ▸ hle) zero_le)
    have hind : screenInd R zs x = 0 := by
      rw [screenInd, if_neg]
      exact fun hall => hne (hall ρs hmem)
    simp [hind]

end GraphMarkovMatching
