/-
`GraphMarkovMatching`: matching of tree-indexed Markov label fields on the
binary tree over the full automorphism group.  The certified results are
the varying-offspring theorems of `arbitrary_offspring_matching.tex`; the
general-`ν` layer follows `arbitrary_offspring_matching.tex`.  The library
is self-contained: the support layer lives in `Support/`.

# The support layer

* `Support/Phi`          the weight `φ_α` at a free exponent and its calculus
* `Support/Potential`    the countable label space, its degrees `q`/`r`, and the potential `Φ`
* `Support/Product`      the product of relations
* `Support/Square`       the symmetrised square `R^□` and the contraction setup
* `Support/RowBound`     the row bound of the contraction lemma
* `Support/Contraction`  the weighted mean inequality, the `K`-step and the finite overlap degrees
* `Support/Tree`         full labellings of `𝔹_n`, the restricted automorphism group, the phase recursions
* `Support/Reduction`    the mean bad degree is below the potential
* `Support/Konig`        the König step: matchings at every finite height give an infinite one
* `Support/Measure`      the measure half of the König step
* `Support/Trajectory`   the Ionescu-Tulcea construction of the infinite sample pair
                     behind the infinite-tree endpoints, with its consistent level processes

# Markov label systems and the four-law core

* `Process/Basic`      Markov label systems, the tree law `muM`, pair mixtures,
               change-of-variable helpers
* `Process/Sim`        the matching relation over the full group (`AutK 1` of the
               support layer), root compatibility
* `Potential/Directed`   directed potentials `Φ_α(μ → ν)` in the safe `phiE` convention
* `Potential/Jensen`     the supporting line of `φ_α` and countable mixture Jensen
* `Potential/Split`      the mixture split (product algebra via conditioning)
* `Process/TreePotential` the pure-measure and root-attachment transports of the tree laws
* `FourLaw/Base`    the pointwise core of the four-law directed contraction
* `FourLaw/Square`    degree identities for two distinct column laws
* `FourLaw/Pointwise` the pointwise main bound
* `FourLaw/Assembly`  the measure-level four-law theorem and its tree form
* `Closure/Measure`    marginal consistency of the tree law and its
                     root-mixture form, the projective input of every
                     endpoint theorem
* `Composite/ProductMeasure`  the two-law product mismatch identity consumed by the
                     endpoint theorems

# The one-law varying-offspring development

* `Process/Kernel`          the varying-offspring process (arbitrary finitely
                     supported offspring laws), component dominations
* `Process/Contraction` the change-of-measure matching bound for the
                     varying-offspring process (corrected Step 2, one-block
                     form: exact root factorisation, split, change of
                     measure, four-law)
* `Potential/ZeroInterface`    the zero-interface estimates: the tilted-summand
                     identity `φ_α(q) = q·r^{-α}`, the far tail `≤ 2η`, and
                     the inverse moments (the per-level `O(η)` charges of
                     the block recursion)
* `Process/Screens`   normalized screens for the arbitrary-support proof:
                     the fresh-mixture identity for good degrees, the
                     zero-event mass bound, and the diagonal-pruning lemma
                     (a screen containing its own cell law vanishes)
* `Closure/Block`     the abstract screened block recursion: the nilpotent
                     invariant `Ê = ∑_{j<r} N^j(u·𝟙)` for the screen block
                     and the joint closure induction
                     `screened_uniform_bound_mono` giving `Ψ_h ≤ K·η` uniformly
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
                     `2(1+δ)`), plus the one-cell row `PhiDres_square_le`
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
                     coordinates: forced targets exactly
                     (`PhiDres_muM_Zlaw_succ`), fresh targets by the
                     split bound (`PhiDres_muM_Tlaw_succ`), fresh sources
                     by the root mixture (`PhiDres_Tlaw_*_succ`: the root
                     integrates to `η`, the cascade to `∑ ν_k Φres(Ξ_k→·)`);
                     plus the fresh-target mixture split, the one-sided
                     screen conversions, and the height-0 base case
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
* `Process/ScreenBridges` bridging lemmas for the screen-row compositions
* `Delta3/Base`       the height-zero base of the `ν = δ₃` screen system
* `Delta3/ScreensA`   the fresh-source screen rows at `ν = δ₃`
* `Delta3/ScreensB`   the forced-source screen rows at `ν = δ₃`
* `Potential/Numerals` numeric constants at `α = 5/2`: the four-law hypotheses and the rpow numerals
* `Process/Failure`   the restricted failure bound, the height-zero degrees and the mixed base coordinates
* `Delta3/Closure`    the closure keystone at `ν = δ₃`: the five-dimensional screen
                     matrix and the uniform failure theorem
* `Delta3/StepFun`    the concrete monotone step functions `delta3F`/`delta3G`
* `Delta3/PsiStep`    the assembled ordinary step at `ν = δ₃`
* `Delta3/EStep`      the assembled screen step at `ν = δ₃`
* `Delta3/Assembled`  the assembled uniform failure bound at `ν = δ₃`
* `Delta3/NumericClose` the numeric closure at `ν = δ₃`: failure at most `16384·η`
* `Delta3/Infinite`   the infinite-tree matching theorem at `ν = δ₃`
* `Grammar/Depths`    the renewal-depth combinatorics and the numerical semigroup of
                     return lengths
* `Grammar/Alphabet`  the formal screen grammar: targets, cascade pairs, the successor step
* `Grammar/Descend`   admissible descents in the screen grammar
* `Grammar/SourceRay` the source ray of an infinite screen path
* `Grammar/Accessible` anchoring and the acyclicity of the screen graph
* `Grammar/Interp`    the interpretation of the formal grammar as context laws and screens
* `Process/Coordinates` the ordinary coordinates over the grammar and the mixture-tilt
                     conversion
* `Process/Factorize` the multi-member Hall factorization `hallFactorize`
* `Grammar/Index`     the accessible coordinate system and the concrete block matrix `accN`
* `Rows/Base`         the general-ν base case of the block recursion (`thm:base`)
* `Rows/Psi`          the general-ν ordinary rows (`thm:psi-rows`)
* `Rows/ECore`        the descent core of the screen rows (`thm:descent`)
* `Rows/EForced`      the forced-source screen rows (`thm:screen-rows`)
* `Rows/EFresh`       the fresh-source screen rows (`thm:screen-rows`)
* `Closure/Geometric` bridging identities for the closure and the geometric half of `thm:geom`
* `Closure/Gen`       the general-ν closure: coordinates, dichotomies, and levels
* `Closure/EStep`     the assembled screen step (`thm:e-step`)
* `Closure/Infinite`  the infinite-tree matching theorem at an arbitrary offspring law
                     (`thm:konig`)
* `Closure/Main`      the general-ν uniform failure theorem (`thm:closure-form`)
* `Closure/Numeric`   the numeric closure of the general matching theorem (`thm:numeric`)
* `Closure/Examples`  the two label-law examples (`thm:exponential`, `thm:doubleexp`)

# The tail and heavy-core layer

The countable-kernel closure and its rare perturbations feed the two-law
development.  The `Tail/` modules are the partial route toward an
exponential-tail theorem at unbounded support: the finite renewal
generators, the quenched counter environments with their grammar and
ordinary rows, and the hybrid screen conversions; `Tail/QuenchedObstruction`
below records where that route stops.  The heavy common core follows with
its ledger and realization.

* `Composite/Resolvent`      countable kernels and the screened closure through a finite invariant
* `Composite/RareMatrix`     rare two-law perturbations of a finite screen grammar
* `Composite/Green`          the denominator-free Green estimate for a weighted screen ledger
* `Obstructions/FiniteZipper` finite macro-step zippers for two-law matching
* `Tail/Combinatorics`     finite renewal generators and cascade estimates at unbounded support
* `Tail/Mixture`           weighted mixture identities
* `Tail/Quenched`          quenched counter environments
* `Tail/QuenchedGrammar`   the mixture-free target grammar over a quenched environment
* `Tail/QuenchedRows`      the ordinary restricted-potential rows of the quenched grammar
* `Tail/Hybrid`            hybrid annealed/quenched screen lemmas
* `Obstructions/HeavyCore` the structural and weight reduction for the common core `{3,5,7,9}`
* `Obstructions/ExitLedger` the full-retention lag ledger of the common core
* `Obstructions/DepthPairing` the physical-depth obstruction to promoting the flat ledger

# The two-law development `Composite/`

The composite two-law route at arbitrary proper offspring support.

* `Composite/Grammar`  the composite tagged grammar (`def:composite-grammar`)
* `Composite/Anchor`   anchoring and the acyclicity of the common block (`thm:composite-acyclic`)
* `Composite/Rank`     nilpotence from a rank, and a rank from acyclicity
* `Composite/Kernel`   the composite tagged kernel and the cluster minorization (`thm:cluster`)
* `Composite/Support`  support witnesses and exact pruning (`thm:support-equality`,
                     `thm:exact-pruning`)
* `Composite/Tilt`     the weighted mixture tilt (`thm:mixture-tilt-composite`)
* `Composite/Endpoint` the finite-to-infinite endpoint
* `Composite/Ledger`   from acyclicity to nilpotence of the transfer matrix
                     (`eq:composite-nilpotent`)
* `Composite/CellStep` the one-step reductions of the ordinary coordinates
* `Composite/Bridge`   the dictionary between the composite lemmas and the ledger functionals
* `Composite/ScreenDescent` the descent of zero events and tilts across the branch point
* `Composite/Assembly` the letter alphabet, the row constants, and the base rows
* `Composite/Main`     the ordinary height recursion and the closure constants
* `Composite/Debt`     the screen-debt discharge (`thm:geom`, `thm:engine`)
* `Composite/StepLetters`  the letter box, the debt index and the target sets of the ledger input
* `Composite/StepMatrices` the common and priced matrices and the nilpotence of the common block
* `Composite/StepRows`     the descended pair screens and the one-step descent
* `Composite/StepRouting`  the inhomogeneity and the routing of the ledger entries into the rows
* `Composite/StepMain`     the assembled one-step row and the priced final theorems
* `Composite/Step`         the merged block and the closed theorems
* `Composite/Numeric`  the numeric closure at `α = 5/2` (`thm:composite-matching`)

# The recorded obstructions

`Obstructions/CrossedContext.crossed_context_potential_top` (cross-type context potentials
are infinite for the pure-ternary law), `Tail/QuenchedObstruction`
(a quenched fresh mode keeps a screen charged),
`Obstructions/Semigroup.unweighted_twoLaw_closure_forces_zero` (an
unweighted two-law closure forces the trivial level), and
`Obstructions/DepthPairing` (the fixed-depth realization obstruction).

* `Obstructions/CrossedContext` the crossed-context obstruction: cross-type context
                     potentials are infinite for the pure-ternary law
* `Tail/QuenchedObstruction` a quenched fresh mode keeps a screen charged
* `Obstructions/Semigroup`   the finite-support obstruction to an asymmetric two-law theorem
# The standalone Markov proof (`markov_matching_new_proof.tex`)

The stopped-expansion proof of the general Markov matching theorem, in `Stopped/`:

* `Stopped/Model`      the Markov label models, their laws on typed labellings, the
                     matching degrees and the support of the laws
* `Stopped/Constants`  the one-site quantities `η`, `δ`, `ζ`, `f`, `R_μ`, `D_μ` and their bounds
* `Stopped/Paths`      restricted potentials, zero events, phases, possible paths, the stopping
                     predicate, transition selections and the explicit scalar functions
* `Stopped/Scalar`     `L_α(β)`, `K_α(β)`, `λ_α`, `C_α(u)` and the pointwise inequalities
* `Stopped/Moments`    the inverse moments, the selected inverse mixture, positivity at `δ = 0`,
                     the root factors
* `Stopped/ZeroExpansion`     the unweighted stopped expansion (`thm:explicit-zero-bound`)
* `Stopped/WeightedExpansion` the weighted stopped expansion (`thm:explicit-weighted-bound`)
* `Stopped/FourLaw`    the four-law contraction with the mean cancellation
                     (`thm:four-law-contraction`)
* `Stopped/Mixture`    zero-mixture convexity and the averaging of the transitions
* `Stopped/Root`       the independent root
* `Stopped/Induction`  the height induction and the finite-height failure bounds
* `Stopped/Infinite`   the pair of infinite processes and the infinite failure bound
* `Stopped/Threshold`  the scalar threshold `ε_K` and the quadratic `M_η`
* `Stopped/Main`       `thm:markov-matching` assembled, both alternatives
* `Stopped/Profiles`   marked binary profiles, composites, grafting and the height bounds
* `Stopped/Semigroup`  the branching semigroup, its atoms, and the finiteness of atoms
* `Stopped/Presentation` the model of a common-core presentation, fresh positivity and the
                     selected core transitions
* `Stopped/Returns`    the phase map and the return bound (`thm:bounded-return`)
* `Stopped/Application` the matching theorem for product laws with a common core
* `Stopped/Consequences` the explicit consequences at exponents `2` and `4/3`
* `Stopped/Numerics`   the exponent range, the exponents `4/3` and `2`
* `Stopped/LowerBounds` the lower bound for the linear coefficient and the order of the
                     failure probability
* `Stopped/ProfileObstruction` the obstruction for preassigned profiles
* `Stopped/Geometric`  the chain and bushy one-site estimates, the probability-one conclusion
* `Stopped/Unbounded`  the finite-height truncation estimate

-/

-- ## The support layer

import GraphMarkovMatching.Support.Phi
import GraphMarkovMatching.Support.Potential
import GraphMarkovMatching.Support.Product
import GraphMarkovMatching.Support.Square
import GraphMarkovMatching.Support.RowBound
import GraphMarkovMatching.Support.Contraction
import GraphMarkovMatching.Support.Tree
import GraphMarkovMatching.Support.Reduction
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
import GraphMarkovMatching.FourLaw.Square
import GraphMarkovMatching.FourLaw.Pointwise
import GraphMarkovMatching.FourLaw.Assembly
import GraphMarkovMatching.Closure.Measure
import GraphMarkovMatching.Composite.ProductMeasure

-- ## The one-law varying-offspring development

import GraphMarkovMatching.Process.Kernel
import GraphMarkovMatching.Process.Contraction
import GraphMarkovMatching.Potential.ZeroInterface
import GraphMarkovMatching.Process.Screens
import GraphMarkovMatching.Closure.Block
import GraphMarkovMatching.Grammar.Nilpotence
import GraphMarkovMatching.Process.Cells
import GraphMarkovMatching.Process.Hall
import GraphMarkovMatching.Process.Ledger
import GraphMarkovMatching.Process.MatchingSupport
import GraphMarkovMatching.Process.Descent
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

import GraphMarkovMatching.Composite.Resolvent
import GraphMarkovMatching.Composite.RareMatrix
import GraphMarkovMatching.Composite.Green
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
import GraphMarkovMatching.Composite.StepLetters
import GraphMarkovMatching.Composite.StepMatrices
import GraphMarkovMatching.Composite.StepRows
import GraphMarkovMatching.Composite.StepRouting
import GraphMarkovMatching.Composite.StepMain
import GraphMarkovMatching.Composite.Step
import GraphMarkovMatching.Composite.Numeric

-- ## The recorded obstructions

import GraphMarkovMatching.Obstructions.CrossedContext
import GraphMarkovMatching.Tail.QuenchedObstruction
import GraphMarkovMatching.Obstructions.Semigroup

-- ## The standalone Markov proof

import GraphMarkovMatching.Stopped.Model
import GraphMarkovMatching.Stopped.Constants
import GraphMarkovMatching.Stopped.Paths
import GraphMarkovMatching.Stopped.Scalar
import GraphMarkovMatching.Stopped.Moments
import GraphMarkovMatching.Stopped.ZeroExpansion
import GraphMarkovMatching.Stopped.WeightedExpansion
import GraphMarkovMatching.Stopped.FourLaw
import GraphMarkovMatching.Stopped.Mixture
import GraphMarkovMatching.Stopped.Root
import GraphMarkovMatching.Stopped.Induction
import GraphMarkovMatching.Stopped.Infinite
import GraphMarkovMatching.Stopped.Threshold
import GraphMarkovMatching.Stopped.Main
import GraphMarkovMatching.Stopped.Profiles
import GraphMarkovMatching.Stopped.Semigroup
import GraphMarkovMatching.Stopped.Presentation
import GraphMarkovMatching.Stopped.Returns
import GraphMarkovMatching.Stopped.Numerics
import GraphMarkovMatching.Stopped.LowerBounds
import GraphMarkovMatching.Stopped.ProfileObstruction
import GraphMarkovMatching.Stopped.Geometric
import GraphMarkovMatching.Stopped.Unbounded
