/-
`GraphMarkovMatching`: matching of tree-indexed Markov label fields on the
binary tree over the full automorphism group.  The certified results are
the varying-offspring theorems of `arbitrary_offspring_matching.tex`; the
general-`ν` layer follows `arbitrary_offspring_matching.tex`.  The library
is self-contained: the support layer lives in `Support/`.

# The support layer

* `Support/*`     the support layer: full labellings and automorphisms of
               `𝔹_h`, `φ_α` and its calculus, potentials, the
               product/square relations, the contraction toolkit, the
               König/measure interface, and the trajectory measure
               (`Support/Trajectory`): the Ionescu-Tulcea construction of
               the infinite sample pair behind the infinite-tree
               endpoints, with its consistent level processes

# Markov label systems and the four-law core

* `Process/Basic`      Markov label systems, the tree law `muM`, pair mixtures,
               change-of-variable helpers
* `Process/Sim`        the matching relation over the full group (`AutK 1` of the
               support layer), root compatibility
* `Potential/Directed`   directed potentials `Φ_α(μ → ν)` in the safe `phiE` convention
* `Potential/Jensen`     the supporting line of `φ_α` and countable mixture Jensen
* `Potential/Split`      the mixture split (product algebra via conditioning)
* `Process/TreePotential` the tree potential `PhiM`, the kernel budget `etaD`, and
               the pure-measure and root-attachment transports they rest on
* `FourLaw/Base`    the pointwise core of the four-law directed contraction
* `Potential/DirectedProduct`  the directed product lemma (one-sided step)
* `FourLaw/Square`    degree identities for two distinct column laws
* `FourLaw/Pointwise` the pointwise main bound
* `FourLaw/Assembly`  the measure-level four-law theorem and its tree form
* `Closure/Measure`    marginal consistency of the tree law and its
                     root-mixture form, the projective input of every
                     endpoint theorem
* `Closure/ProductMeasure`  the two-law product mismatch identity consumed by the
                     endpoint theorems

# The one-law varying-offspring development

* `Process/Kernel`          the varying-offspring process (arbitrary finitely
                     supported offspring laws), component dominations
* `Process/Contraction` the change-of-measure matching bound for the
                     varying-offspring process (corrected Step 2, one-block
                     form: exact root factorisation, split, change of
                     measure, four-law)
* `Process/CrossedContext`   renewal-grammar building blocks: same-counter context
                     recursion, the fresh-cherry contraction, and the
                     crossed-context obstruction (`Φ(Z₂ → T) = ⊤` for the
                     pure-ternary law: cross-type context potentials cannot
                     enter the block recursion unconditioned)
* `Potential/ZeroInterface`    the zero-interface estimates: the tilted-summand
                     identity `φ_α(q) = q·r^{-α}`, the far tail `≤ 2η`,
                     the inverse moments, and the exceptional pair bound
                     (the per-level `O(η)` charges of the block recursion)
* `Process/Screens`   normalized screens for the arbitrary-support proof:
                     the fresh-mixture identity for good degrees, the
                     zero-event mass bound, and the diagonal-pruning lemma
                     (a screen containing its own cell law vanishes)
* `Closure/Block`     the abstract screened block recursion: the nilpotent
                     invariant `Ê = ∑_{j<r} N^j(u·𝟙)` for the screen block
                     and the joint closure induction
                     `screened_uniform_bound` giving `Ψ_h ≤ K·η` uniformly
                     (the engine of `arbitrary_offspring_matching.tex`
                     `thm:main-matching`)
* `Grammar/Nilpotence` the nilpotence certificate: a rank decreasing along
                     the support of `N`, or acyclicity of the support
                     graph alone, discharges the hypothesis
                     `N^r(u·𝟙) = 0` of the block recursion
* `Process/Cells`     the fresh counter cells `Flaw k` of the process, the
                     mixture identity `Tlaw = ν.bind Flaw`, the
                     fresh-mixture degree identities at the process laws,
                     and the one-step decompositions in good-degree form:
                     `rE_succ_branch` (root indicator times pair degree),
                     `rE_Zlaw_succ_branch` (forced targets), and
                     `rE_Tlaw_succ_branch` (`r = b(x_r)·r(Ξ̄)`: the root
                     factor and the cascade mixture separate exactly)
* `Process/Hall`      the screened 2×2 Hall classification: both pairings
                     minorize the square good degree, the zero dichotomy
                     (zero row or zero column), and the resolved
                     normalization `φ(q^□) ≤ r₀^{-α}·r₁^{-α}`
* `Process/Ledger`    the restricted four-law: the square potential over
                     the doubly-positive set contracts against the eight
                     positive-set restricted potentials `PhiDres` with
                     the SAME constants as the full four-law, plus the
                     reversed zero-interface masses `zMass` (coefficient
                     `2(1+δ)`) — plus the one-cell row `PhiDres_square_le`
                     (four-law output + four singleton screens times
                     restricted inverse moments)
* `Process/MatchingSupport`  the generic support witness `HasMatchingSupport`
                     (every charged source atom has a related charged
                     target atom) with its closure under mixtures, maps,
                     products and branch constructors, the vanishing of
                     `zMass`, the identity `PhiDres = PhiD`, and the
                     vanishing of a screen holding a supporting member;
                     the interface shared by the one-law, grafted and
                     composite routes
* `Process/Descent`      the per-state-pair step: height-(h+1) restricted
                     ordinary coordinates reduce to height-h square
                     coordinates — forced targets exactly
                     (`PhiDres_muM_Zlaw_succ`), fresh targets by the
                     split bound (`PhiDres_muM_Tlaw_succ`), fresh sources
                     by the root mixture (`PhiDres_Tlaw_*_succ`: the root
                     integrates to `η`, the cascade to `∑ ν_k Φres(Ξ_k→·)`);
                     plus the fresh-target mixture split, the one-sided
                     screen conversions, and the height-0 base case
* `Process/ScreenStep` the screen-step rows: the height-(h+1) screens on
                     cell laws with diagonal tilt EQUAL the height-h
                     diagonal pair screens (forced and fresh zero lists),
                     and the mixture-dead indicator is below every
                     charged component's dead indicator
* `Process/ScreenTilt` the screen-step rows for arbitrary tilts, and the
                     tilt conversions for forced and fresh alternatives
* `Process/ZMass`     the zero-mass rows: forced and fresh dead-mass
                     steps, and the unit-tilt Hall factorization
* `Delta3/Step`    the pure-ternary instantiation: `Ξ̄ = Ξ₃` and the
                     principal ordinary row of the transfer lemma for
                     `ν = δ₃` as one machine-checked inequality
* `Delta3/Rows` the eight sibling ordinary rows for `ν = δ₃`
                     (forced-forced at all four cells, forced-fresh and
                     fresh-forced at both counters)

# The tail and heavy-core layer

The modules feeding the two-law development: the screened tail estimates and
their rare perturbations, the denominator-free Green estimate for an abstract
weighted screen ledger (`Closure/Green`), the quenched tail rows and the hybrid
screen conversions, and the heavy common core with its ledger and
realization.

# The two-law development `Composite/`

The composite two-law route at arbitrary proper offspring support: the formal
grammar and its anchoring (`Grammar`, `Anchor`, `Rank`), the tagged kernel and
its support and tilt layers (`Kernel`, `Support`, `Tilt`), the projective
endpoint (`Endpoint`), the ledger and its cell and screen descents (`Ledger`,
`CellStep`, `Bridge`, `ScreenDescent`, `Assembly`), the ordinary closure and
the headline interface (`Main`), the ledger certificates (`Debt`), the
concrete ledger instance (`Step`), and the unconditional numeric closure at
`α = 5/2` (`Numeric`).  `Composite/AxCheck.lean` audits them.

# The recorded obstructions

`Process/CrossedContext.crossed_context_potential_top` (cross-type context potentials
are infinite for the pure-ternary law), `Tail/QuenchedObstruction`
(a quenched fresh mode keeps a screen charged),
`Obstructions/Semigroup.unweighted_twoLaw_closure_forces_zero` (an
unweighted two-law closure forces the trivial level), and
`Obstructions/DepthPairing` (the fixed-depth realization obstruction).

# The archive

`Archive/` holds the modules the paper no longer refers to: the per-state
frozen-pattern ceiling and the infinite-tree theorem it closes, the caret
layer and its budget obstruction, the extension kernel, the retired
renewal-block invariant, the two-law cross ledger, and the finished grafted
11/13 pipeline.  They are complete, sorry-free and axiom-clean, they are
still built through `Archive.lean`, and `Archive/AxCheck.lean` audits them.
See `Archive.lean` for what each one contains.

---

The four-law directed contraction is fully certified
(`PhiD_fourlaw_le`, constant `A = 2L + 2(1+δ)K`, quadratic constant
`2Lc_α + 20 + 2(1+δ⁻¹)α²`), with `fourLaw_tree` discharging the step
hypothesis `hΓ`/`hFour` for two-sided pattern pairs. The two-ceiling `β`-refinement is done (`PhiM_succ_le_two`,
`PhiM_le_of_invariant_closed`, `markovMatching_failure_le_closed`): the
matching bound at every height holds from the budgets `ε` (kernel mismatch),
`β` (one-sided mass), `η_ι` (root) and one closure inequality, with no
undischarged mathematical hypotheses. The König packaging is done in interface form
(`markovMatching_infinite`: compatible measurable level projections with the
root-mixture laws give the infinite-tree matching bound).

The varying-offspring layer (`arbitrary_offspring_matching.tex`)
avoids the per-state budgets entirely: `varyingMatching_failure_le_closed`
certifies the nondegenerating bound (Theorem `thm:main-matching`)
through the exact root factorisation `q = δ_v + (1-δ_v)q̃`, the mixture
comparison `ν₂·T⊗T ≤ Ξ̄ ≤ C̄·T⊗T`, the certified change of measure, and the
four-law.

For `ν = δ₃` the screened block recursion is fully assembled:
`delta3_failure_uniform_assembled` bounds the matching failure at every
height by `Kc·η` from the ledger constants, the two closure inequalities
at the invariant levels, and the root budgets alone. The recursion runs
through the concrete monotone step functions `delta3F`/`delta3G`
(`Delta3/StepFun`), the assembled ordinary and screen step bounds
(`Delta3/PsiStep`, `Delta3/EStep`), and the closure keystone
with its five-dimensional screen matrix `delta3N`, nilpotent by the rank
certificate (`Delta3/Closure`).  The numeric closure is certified
with explicit constants (`Delta3/NumericClose.delta3_failure_le`):
at `α = 5/2` with `μ(v0) ≥ 1/2` and `2³⁰·η ≤ 1`, the matching failure
at every height is at most `16384·η`.  The König packaging is certified
in interface form (`Delta3/Infinite.delta3Matching_infinite`):
compatible measurable level projections with the process pair law give
a full-tree matching automorphism with probability at least
`1 - 16384·η`, with the marginal consistency of the process law
supplied by `Tlaw_map_restrictLab`.

For an ARBITRARY finitely supported offspring law the assembly is
complete in closure form (`Closure/Main.varying_failure_uniform`,
`varying_matching_infinite_closed`).  The coordinates are indexed by
the formal grammar: ordinary coordinates over the aligned pair
grammar `OrdAcc` generated from `(F, F)`, screen coordinates over the
accessible live index `scrIndex` generated from the state-pair seeds
and closed under sub-successors (`Grammar/Index`); anchoring propagates
through the closure, so the block matrix `accN` is nilpotent by the
anchored acyclicity (`accN_acyclic`, `accN_nilpotent`), with NO
nilpotence hypothesis in the final theorem.  The transfer rows are
certified generically: the ordinary rows through the componentized
square cells and the mixture one-sided charge with the pointwise
tilt conversion `WresD_XiBar_le_sum` (`Rows/Psi`,
`Process/Coordinates`), the screen rows through the multi-member Hall
factorization `hallFactorize` (`Process/Factorize`), the descent core
`memInd_branch_iff` (`Rows/ECore`), and the six cell-by-norm
rows (`Rows/EForced`, `Rows/EFresh`); the base case is
`Rows/Base`, the assembled steps and levels are `Closure/Gen`
and `Closure/EStep`, and the remaining hypotheses of the main
theorem are exactly the ledger constants, the finite tilt constants,
and the two closure inequalities at the invariant levels.  The
numeric closure is certified with explicit constants
(`Closure/Numeric.varying_failure_le`, `varying_matching_le`): at
`α = 5/2` the levels are built from the charged tilt sum `T`, the
support size, the accessible-index cardinality bound, and the
alphabet bound, and the failure at every height is at most
`genKcC·η` once `genSmallC·η ≤ 1`; the pure ternary law re-derives as
an instance (`delta3_failure_le_of_general`).  Two label-law examples
instantiate the theorem on the half-line path (`Closure/Examples`,
self-contained): the exponential three-label law with potential
budget `9 e^{-(D-5/2)D}` and the double-exponential law with budget
`4 e^{-(D-5/2)D}`.
-/

-- ## The support layer

import GraphMarkovMatching.Support.Phi
import GraphMarkovMatching.Support.Potential
import GraphMarkovMatching.Support.Product
import GraphMarkovMatching.Support.Square
import GraphMarkovMatching.Support.Maxima
import GraphMarkovMatching.Support.RowBound
import GraphMarkovMatching.Support.Contraction
import GraphMarkovMatching.Support.Tree
import GraphMarkovMatching.Support.Reduction
import GraphMarkovMatching.Support.ConcreteBlock
import GraphMarkovMatching.Support.Konig
import GraphMarkovMatching.Support.Measure
import GraphMarkovMatching.Support.Trajectory

-- ## Markov label systems and the four-law core

import GraphMarkovMatching.Process.Basic
import GraphMarkovMatching.Process.Sim
import GraphMarkovMatching.Potential.Directed
import GraphMarkovMatching.Potential.Jensen
import GraphMarkovMatching.Potential.Split
import GraphMarkovMatching.Process.TreePotential
import GraphMarkovMatching.FourLaw.Base
import GraphMarkovMatching.Potential.DirectedProduct
import GraphMarkovMatching.FourLaw.Square
import GraphMarkovMatching.FourLaw.Pointwise
import GraphMarkovMatching.FourLaw.Assembly
import GraphMarkovMatching.Closure.Measure
import GraphMarkovMatching.Closure.ProductMeasure

-- ## The one-law varying-offspring development

import GraphMarkovMatching.Process.Kernel
import GraphMarkovMatching.Process.Contraction
import GraphMarkovMatching.Process.CrossedContext
import GraphMarkovMatching.Potential.ZeroInterface
import GraphMarkovMatching.Process.Screens
import GraphMarkovMatching.Closure.Block
import GraphMarkovMatching.Grammar.Nilpotence
import GraphMarkovMatching.Process.Cells
import GraphMarkovMatching.Process.Hall
import GraphMarkovMatching.Process.Ledger
import GraphMarkovMatching.Process.MatchingSupport
import GraphMarkovMatching.Process.Descent
import GraphMarkovMatching.Process.ScreenStep
import GraphMarkovMatching.Process.ScreenTilt
import GraphMarkovMatching.Process.ZMass
import GraphMarkovMatching.Delta3.Step
import GraphMarkovMatching.Delta3.Rows
import GraphMarkovMatching.Process.ScreenBridges
import GraphMarkovMatching.Delta3.Base
import GraphMarkovMatching.Delta3.ScreensA
import GraphMarkovMatching.Delta3.ScreensB
import GraphMarkovMatching.Potential.Numerals
import GraphMarkovMatching.Process.Failure
import GraphMarkovMatching.Delta3.Closure
import GraphMarkovMatching.Delta3.StepFun
import GraphMarkovMatching.Delta3.PsiStep
import GraphMarkovMatching.Delta3.EStep
import GraphMarkovMatching.Delta3.Assembled
import GraphMarkovMatching.Delta3.NumericClose
import GraphMarkovMatching.Delta3.Infinite
import GraphMarkovMatching.Grammar.Depths
import GraphMarkovMatching.Grammar.Alphabet
import GraphMarkovMatching.Grammar.Descend
import GraphMarkovMatching.Grammar.SourceRay
import GraphMarkovMatching.Grammar.Accessible
import GraphMarkovMatching.Grammar.Interp
import GraphMarkovMatching.Process.Coordinates
import GraphMarkovMatching.Process.Factorize
import GraphMarkovMatching.Grammar.Index
import GraphMarkovMatching.Rows.Base
import GraphMarkovMatching.Rows.Psi
import GraphMarkovMatching.Rows.ECore
import GraphMarkovMatching.Rows.EForced
import GraphMarkovMatching.Rows.EFresh
import GraphMarkovMatching.Closure.Geometric
import GraphMarkovMatching.Closure.Gen
import GraphMarkovMatching.Closure.EStep
import GraphMarkovMatching.Closure.Infinite
import GraphMarkovMatching.Closure.Main
import GraphMarkovMatching.Closure.Numeric
import GraphMarkovMatching.Closure.Examples

-- ## The tail and heavy-core layer

import GraphMarkovMatching.Tail.Block
import GraphMarkovMatching.Closure.RareMatrix
import GraphMarkovMatching.Closure.Green
import GraphMarkovMatching.Obstructions.FiniteZipper
import GraphMarkovMatching.Tail.Combinatorics
import GraphMarkovMatching.Tail.Mixture
import GraphMarkovMatching.Tail.Quenched
import GraphMarkovMatching.Tail.QuenchedGrammar
import GraphMarkovMatching.Tail.QuenchedRows
import GraphMarkovMatching.Tail.Hybrid
import GraphMarkovMatching.Obstructions.HeavyCore
import GraphMarkovMatching.Obstructions.ExitLedger
import GraphMarkovMatching.Obstructions.DepthPairing

-- ## The two-law development

import GraphMarkovMatching.Composite.Grammar
import GraphMarkovMatching.Composite.Anchor
import GraphMarkovMatching.Composite.Rank
import GraphMarkovMatching.Composite.Kernel
import GraphMarkovMatching.Composite.Support
import GraphMarkovMatching.Composite.Tilt
import GraphMarkovMatching.Composite.Endpoint
import GraphMarkovMatching.Composite.Ledger
import GraphMarkovMatching.Composite.CellStep
import GraphMarkovMatching.Composite.Bridge
import GraphMarkovMatching.Composite.ScreenDescent
import GraphMarkovMatching.Composite.Assembly
import GraphMarkovMatching.Composite.Main
import GraphMarkovMatching.Composite.Debt
import GraphMarkovMatching.Composite.Step
import GraphMarkovMatching.Composite.Numeric

-- ## The recorded obstructions

import GraphMarkovMatching.Tail.QuenchedObstruction
import GraphMarkovMatching.Obstructions.Semigroup

-- ## The archive

import GraphMarkovMatching.Archive
