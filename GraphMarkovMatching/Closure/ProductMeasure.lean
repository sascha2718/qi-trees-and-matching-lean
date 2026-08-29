/-
The product-law mismatch identity for two different laws.

The Konig/measure packaging turns a uniform finite-height mismatch bound into
one infinite automorphism, and the bound it consumes is the measure of the
non-matching event under the height-`n` pair law.  This file identifies that
measure with the directed failure `failureD` when the two coordinates carry
different laws, which is what every two-law endpoint needs.  Nothing here
refers to a particular grammar.
-/
import GraphMarkovMatching.Closure.Measure
import GraphMarkovMatching.Tail.Quenched

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

/-- The product-law mismatch identity with different row and column laws. -/
lemma prodPMF_toMeasure_not_rel_cross {W : Type}
    [MeasurableSpace W] [MeasurableSingletonClass W] [Countable W]
    (rhoS rhoT : PMF W) (R : W → W → Prop) :
    (prodPMF rhoS rhoT).toMeasure {p : W × W | ¬ R p.1 p.2} =
      failureD rhoS rhoT R := by
  rw [(prodPMF rhoS rhoT).toMeasure_apply
      ((Set.to_countable _).measurableSet), ENNReal.tsum_prod', failureD]
  refine tsum_congr fun x => ?_
  rw [qE, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun y => ?_
  rw [Set.indicator_apply]
  by_cases h : R x y
  · simp [Set.mem_setOf_eq, h]
  · simp [Set.mem_setOf_eq, prodPMF_apply, h]

end GraphMarkovMatching
