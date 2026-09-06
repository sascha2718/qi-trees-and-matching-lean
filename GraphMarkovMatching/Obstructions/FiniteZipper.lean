/-
Finite macro-step zippers for two-law matching.

The important normalization point is that a zipper row must retain *every*
offspring outcome which has a continuation in the finite phase grammar.
Then the counter part of the compatible degree is the full row mass `1`;
no inverse power of an exceptional atom is introduced.  The only linear
weight left in the screen row is the integrated label inverse moment, which
is `1 + O(eta)` in the matching ledger.

This file makes that statement exact for an arbitrary finite macro grammar.
An outcome either closes the present zipper (`none`) or moves to a new live
phase (`some j`).  The killed kernel is the mass of live outcomes.  The
screen kernel multiplies a whole row by its integrated inverse-label moment.
If every row has killed mass at least `q`, the actual screen operator is
dominated by `A` times a substochastic kernel with one-step loss `q`, and the
weighted-renewal closure from `Composite/RareMatrix.lean` applies.
-/
import GraphMarkovMatching.Composite.RareMatrix

namespace GraphMarkovMatching

open scoped ENNReal Classical

variable {ι Ω : Type} [Fintype ι] [Fintype Ω]

/-- A finite macro-step grammar.  `mass i o` is the probability of outcome
`o` in phase `i`; `next i o = none` means that the zipper closes, while
`some j` is a surviving transition to phase `j`. -/
structure FiniteZipper where
  mass : ι → Ω → ℝ≥0∞
  next : ι → Ω → Option ι
  mass_sum : ∀ i, ∑ o, mass i o = 1

namespace FiniteZipper

/-! ### Exact finite-word interpretation of live-kernel powers -/

/-- Execute an outcome word.  Once the zipper has closed, it remains closed. -/
def run (Z : FiniteZipper (ι := ι) (Ω := Ω)) :
    Option ι → List Ω → Option ι
  | s, [] => s
  | none, _ :: os => Z.run none os
  | some i, o :: os => Z.run (Z.next i o) os

end FiniteZipper

end GraphMarkovMatching
