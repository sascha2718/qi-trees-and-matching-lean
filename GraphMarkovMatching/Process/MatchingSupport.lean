/-
Generic support witnesses for directed matching.

A support witness records that every charged source atom has a related
charged target atom.  The property composes under mixtures, maps, products
and branch constructors, it kills the zero-interface mass `zMass`, and it
makes the restricted potential `PhiDres` agree with the ordinary directed
potential `PhiD`.  Nothing here refers to a particular grammar, so the
interface is shared by the grafted development and by the composite
two-law route.
-/
import GraphMarkovMatching.Process.Ledger

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

/-- Every charged source atom admits a related charged target atom. -/
def HasMatchingSupport {X Y : Type} (ρs : PMF X) (ρt : PMF Y)
    (R : X → Y → Prop) : Prop :=
  ∀ x, ρs x ≠ 0 → ∃ y, ρt y ≠ 0 ∧ R x y

lemma HasMatchingSupport.rE_ne_zero {X : Type} {ρs ρt : PMF X}
    {R : X → X → Prop} (h : HasMatchingSupport ρs ρt R)
    {x : X} (hx : ρs x ≠ 0) : rE ρt R x ≠ 0 := by
  obtain ⟨y, hy, hxy⟩ := h x hx
  rw [rE]
  have hterm : (if R x y then ρt y else 0) ≠ 0 := by
    simpa [hxy] using hy
  have hle : (if R x y then ρt y else 0) ≤
      ∑' z, if R x z then ρt z else 0 := ENNReal.le_tsum y
  intro hz
  exact hterm (le_antisymm (hle.trans (le_of_eq hz)) zero_le)

lemma HasMatchingSupport.zMass_eq_zero {X : Type} {ρs ρt : PMF X}
    {R : X → X → Prop} (h : HasMatchingSupport ρs ρt R) :
    zMass ρs ρt R = 0 := by
  rw [zMass]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : ρs x = 0
  · simp [hx]
  · simp [h.rE_ne_zero hx]

/-- If one member of a zero list supports every charged source atom, the
screen is exactly zero, independently of its normalization. -/
lemma screenE_eq_zero_of_matching_mem {X : Type}
    {rhoS rho0 : PMF X} {R : X → X → Prop}
    (hsupp : HasMatchingSupport rhoS rho0 R)
    (zs : List (PMF X)) (hmem : rho0 ∈ zs) (W : X → ℝ≥0∞) :
    screenE rhoS R zs W = 0 := by
  rw [screenE]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : rhoS x = 0
  · simp [hx]
  · have hr : rE rho0 R x ≠ 0 := hsupp.rE_ne_zero hx
    have hi : screenInd R zs x = 0 := by
      rw [screenInd, if_neg]
      intro hall
      exact hr (hall rho0 hmem)
    simp [hi]

end GraphMarkovMatching
