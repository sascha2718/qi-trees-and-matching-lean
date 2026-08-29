/-
# The archive of `GraphMarkovMatching`

Every module below is correct, complete and audited: none contains a `sorry`,
and `Archive/AxCheck.lean` certifies that each of their headline results
depends on `propext, Classical.choice, Quot.sound` and nothing else.  They are
kept here because the paper no longer refers to them: they are the finished
record of routes that were superseded, and of designs that were refuted on
purpose.  Nothing in the live library imports anything from this folder.

This module imports them all, so `lake build` keeps checking them.

## The per-state frozen-pattern ceiling

The first route to the infinite-tree theorem: a uniform ceiling on the
frozen-pattern square potentials, refined by splitting two-sided from
one-sided patterns, closed by the four-law contraction, and packaged with the
König/measure interface.  The generic pieces it grew, the pure-measure
helpers and the tree quantities `PhiM` and `etaD`, are now
`Process/TreePotential.lean`, and the projective consistency the live
endpoints use is `Closure/Measure.lean`.
The route itself is unusable for the paper's processes: their kernel budgets
`etaD` are infinite (`CaretObstruction`), so its hypothesis `hEta` is never
satisfiable.

* `Step`: the per-state one-step bound, the tilted conditional mixture and
  the pointwise split-and-Jensen estimate;
* `Reduction`: the invariance schema and the height-`n` failure bound;
* `TwoCeiling`: the β-refined step and the unconditional closed invariance;
* `MarkovInfinite`: the infinite-tree theorem the closed invariance yields.

## The caret layer and the legacy label-field modules

* `Caret`, `CaretObstruction`: the caret-state encoding of a finitely
  supported offspring law with `θ₀ = 0`, and the machine-checked refutation
  that its kernel budgets are infinite.
* `Extension`: the one-level extension kernel behind the Kolmogorov
  construction, superseded by the projective endpoint of
  `Closure/Measure.lean`.
* `VaryingRenewal`: the abstract renewal-block invariant of the retired
  varying-offspring draft, superseded by the closed recursion.

## The two-law cross ledger

The bidirectional coordinate system built before the composite grammar of
`Composite/`: the asymmetric screen grammar and its interpretation,
asymmetric one-step decompositions, the cross closure and its E-rows, the
bidirectional ledger with its unweighted closure and E-step, and the weighted
heavy-component reductions that fed it.  The two generic diagonal-screen
estimates it grew stay live in `Tail/Hybrid.lean`.

* `VaryingCrossGrammar`, `VaryingCrossInterp`;
* `VaryingCrossStep`, `VaryingCrossClosure`;
* `VaryingCrossERowCore`, `VaryingCrossERowForced`, `VaryingCrossERowFresh`;
* `VaryingTwoLawLedger`, `VaryingTwoLawClosure`, `VaryingTwoLawEStep`;
* `VaryingHeavyCoreWeighted`.

The no-go that ended this route, `unweighted_twoLaw_closure_forces_zero`,
stays live in `Obstructions/Semigroup.lean`.

## The grafted 11/13 pipeline

The fully worked concrete instance: the fixed law pair supported on
`{3,5,7,9}` with exceptional atoms `11` and `13`, carried from the counters
and the replacement cylinders through the tagged kernel, the grafted E-rows,
the heavy rows, the matrix route and the final closure.  The composite
development replaced it with a general grammar.  The generic interfaces it
grew stay live: the support witness is `Process/MatchingSupport.lean`, the
abstract weighted-ledger Green estimate is `Closure/Green.lean`, and the
two-law product mismatch identity is `Closure/ProductMeasure.lean`.

* `VaryingGraftedCounters`, `VaryingGraftedReplacement`,
  `VaryingGraftedProduct`, `VaryingGraftedHallClose`;
* `VaryingGraftedKernel`, `VaryingGraftedRows`, `VaryingGraftedGrammar`,
  `VaryingGraftedInterp`, `VaryingGraftedSupport`;
* `VaryingGraftedEstimate`, `VaryingGraftedEndpoint`;
* `VaryingGraftedERowCore`, `VaryingGraftedAssembly`;
* `VaryingGraftedHeavyRow`, `VaryingGraftedHeavyIntegrated`;
* `VaryingGraftedMatrixRoute`, `VaryingGraftedFinal`;
* `VaryingGraftedZeroCharge`, `VaryingGraftedSupportedNormalization`;
* `VaryingFiniteGraftGeneral`.
-/

import GraphMarkovMatching.Archive.Step
import GraphMarkovMatching.Archive.Reduction
import GraphMarkovMatching.Archive.TwoCeiling
import GraphMarkovMatching.Archive.MarkovInfinite

import GraphMarkovMatching.Archive.Caret
import GraphMarkovMatching.Archive.CaretObstruction
import GraphMarkovMatching.Archive.Extension
import GraphMarkovMatching.Archive.VaryingRenewal

import GraphMarkovMatching.Archive.VaryingCrossGrammar
import GraphMarkovMatching.Archive.VaryingCrossInterp
import GraphMarkovMatching.Archive.VaryingCrossStep
import GraphMarkovMatching.Archive.VaryingCrossClosure
import GraphMarkovMatching.Archive.VaryingCrossERowCore
import GraphMarkovMatching.Archive.VaryingCrossERowForced
import GraphMarkovMatching.Archive.VaryingCrossERowFresh
import GraphMarkovMatching.Archive.VaryingTwoLawLedger
import GraphMarkovMatching.Archive.VaryingTwoLawClosure
import GraphMarkovMatching.Archive.VaryingTwoLawEStep
import GraphMarkovMatching.Archive.VaryingHeavyCoreWeighted

import GraphMarkovMatching.Archive.VaryingGraftedCounters
import GraphMarkovMatching.Archive.VaryingGraftedReplacement
import GraphMarkovMatching.Archive.VaryingGraftedProduct
import GraphMarkovMatching.Archive.VaryingGraftedHallClose
import GraphMarkovMatching.Archive.VaryingGraftedKernel
import GraphMarkovMatching.Archive.VaryingGraftedRows
import GraphMarkovMatching.Archive.VaryingGraftedGrammar
import GraphMarkovMatching.Archive.VaryingGraftedInterp
import GraphMarkovMatching.Archive.VaryingGraftedSupport
import GraphMarkovMatching.Archive.VaryingGraftedEstimate
import GraphMarkovMatching.Archive.VaryingGraftedEndpoint
import GraphMarkovMatching.Archive.VaryingGraftedERowCore
import GraphMarkovMatching.Archive.VaryingGraftedAssembly
import GraphMarkovMatching.Archive.VaryingGraftedHeavyRow
import GraphMarkovMatching.Archive.VaryingGraftedHeavyIntegrated
import GraphMarkovMatching.Archive.VaryingGraftedMatrixRoute
import GraphMarkovMatching.Archive.VaryingGraftedFinal
import GraphMarkovMatching.Archive.VaryingGraftedZeroCharge
import GraphMarkovMatching.Archive.VaryingGraftedSupportedNormalization
import GraphMarkovMatching.Archive.VaryingFiniteGraftGeneral
