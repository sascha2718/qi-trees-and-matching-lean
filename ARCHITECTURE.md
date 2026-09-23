# Lean architecture and maintenance notes

This document explains the implementation and the distinctions needed when maintaining it.
[README.md](README.md) contains the public API, headline statements and build instructions.
[CHALLENGE_REVIEW.md](CHALLENGE_REVIEW.md) records dated audit evidence. The manuscript's
Appendix B and [paper-correspondence.yaml](paper-correspondence.yaml) give the detailed
statement correspondence; do not duplicate their declaration inventory here.

## Library dependencies

`BranchingProcess` depends on Mathlib, independently of the matching libraries.
`GraphMatching` and `GraphMarkovMatching` are also mutually independent. `ChainClasses`
combines all three. The root modules are the maintained import indexes:

- [BranchingProcess.lean](BranchingProcess.lean)
- [GraphMatching.lean](GraphMatching.lean)
- [GraphMarkovMatching.lean](GraphMarkovMatching.lean)
- [ChainClasses.lean](ChainClasses.lean)

Use `import ChainClasses.Classification` for the public classification interface. The files
`Classification/Simple`, `Complete`, `Finite` and `Embedding` separate the simple-support,
general infinite, finite-inclusive and mutual-embeddability conclusions. Older `trichotomy_*`
names are implementation interfaces, not additional headline results.

## Branching-process foundations

| Modules in `BranchingProcess/` | Role |
|---|---|
| `Word`, `Offspring`, `Sample` | Words, their metric, bounded offspring laws and generating functions, deterministic genealogy, extinction fixed point and survival skeleton |
| `Field`, `Law` | Independent coordinate fields, sample measures, measurability and identification of extinction probability |
| `Conditioned`, `Skeleton` | Survival conditioning, reduced and conjugate laws, re-addressed skeleton trees and their branching property |
| `Decorated`, `Harris` | Joint surviving/dying-child events, independent conjugate decorations and skeleton-degree laws |
| `Progeny` | Finite-tree point masses and exponential progeny moments |
| `Geometry`, `Embedding` | Graph quasi-isometries and embeddings, geodesic stability, bush/ray obstructions, composition and boundedness |
| `Pruning`, `PrunedTree` | Retention rounds, regular subtrees, exact binomial recursion and fixed point, and the conditional law of the retained tree |

The probability constructions use `Measure.infinitePi` and prefix-closed word trees. The
generating functions, extinction argument and Harris decomposition are developed in this
library. Tree geometry uses `SimpleGraph` paths and complementary components. The stability
lemma `exists_between_dist_le` gives constant `D`: consecutive images are at distance at most
`2D`, and a separating vertex lies within `D` of one of a consecutive pair. Skeleton rays are
constructed recursively from surviving children.

Representation details that matter:

- The alphabet is `Fin N`; children are appended on the right. A support bound `J` requires
  `J ≤ N`. Without it, `sample` truncates the offspring and the intended extinction identity
  is false. This is the hypothesis `hJN` in `sampleMeasure_not_survives`.
- Subtrees use `Descriptive.tree (Fin N)`. When dot notation does not resolve, write
  `Descriptive.Tree.subAt T v` explicitly.
- Conditioning a subtree to die gives the conjugate **tree law**, not the conjugate law of
  every coordinate in the ambient offspring field. Coordinates outside the realised tree
  remain unconditioned. Pass to the realised tree before identifying these laws.
- The pruning proof uses a union bound and the induction level `4/5`, rather than the paper's
  Chebyshev estimate at `3/4`. `retainedProb_succ`, `sampleMeasure_retainedInf_eq` and
  `retainedTreeLaw_eq_treeLaw` nevertheless provide the exact recursion, its fixed point and
  the Galton–Watson law of the re-addressed retained tree. Only the numerical estimate differs.

## Independent matching

`GraphMatching` implements the scalar potential and symmetrised-square argument, then applies
it to finite and infinite labellings.

| Modules in `GraphMatching/` | Role |
|---|---|
| `Phi`, `Maxima` | Scalar weight, chord bounds and parameterised contraction constants |
| `Potential`, `Product`, `Square`, `Transversal`, `RowBound`, `Contraction` | Relation degrees, products, pairings and the contraction estimate |
| `Transport`, `Tree`, `Reduction` | Transport of potentials, binary labellings and the height induction |
| `Konig`, `Measure`, `Kolmogorov`, `AutBridge` | Consistent finite matchings, infinite product law and actual rooted graph automorphisms |
| `Graph`, `Examples`, `DoubleExp` | Label-graph specialisation, path/star examples and tail estimates |
| `Probability` | Exact full-matching probability recursion and the scalar failure criterion |

`Tree.Aut` begins as an iterated swap group. `AutBridge` identifies it with the root-fixing
graph automorphism group at finite and infinite height. Keep this identification in the path
from the internal matching relation to a statement about graph automorphisms.

The general-exponent interfaces have names such as `phiA`, `PhiA`, `LA`, `KA`, `AA`, `BA`,
`OneStepA` and `ProdStepA`. Unsuffixed specialisations use exponent `5/2`. The reduction accepts
the analytic bounds as hypotheses, so the numerical choices belong in the instances rather
than the inductive argument. The maxima `LA` and `KA` are defined as suprema; a printed closed
formula must agree with that domain, including exponents below two.

The rational bounds `L = 14/75`, `K = 1/8` and chord constant `C = 28/3` are coupled through
`2L + 4K < 7/8` and `2LC + 1/2 < 4`. Changing one requires checking both inequalities.
They bound the paper's exact constants from above, as recorded in the correspondence manifest.

Useful proof-maintenance details:

- For exponent `5/2`, square nonnegative inequalities to turn powers into polynomials in
  the original variable. `Phi.sq_rpow_alpha` and `phi_eq_sqrt` supply the power identities.
- The chord proof uses `convexOn_rpow_left` for exponential functions, followed by
  `chordConstA_alpha_le`; it does not need a new differentiability argument for negative powers.
- Supply denominator positivity explicitly to division inequalities. For the rational maxima,
  critical-point hints at `2/7` and `2/3` help `nlinarith` use the available strict slack.
- Laws are `PMF`s and potentials take values in `ENNReal`, so countable support is automatic
  and off-support terms vanish through `0 * ∞ = 0`. The project uses `prodPMF` for products.
- Use nonnegative-sum commutation before moving finite arithmetic to `ℝ`. Avoid cancellation
  or subtraction arguments that silently assume finiteness in `ENNReal`.
- For indicator sums, align decidable instances and factor compound indicators into
  one-coordinate weights before applying `tsum_prod_split`.
- Product bounds need reflexivity; the contraction additionally needs symmetry. Do not remove
  that hypothesis merely because an intermediate product lemma does not use it.
- The finite-to-infinite step uses `exists_seq_forall_proj_of_forall_finite` from
  `Mathlib.Order.KonigLemma`, applied to good finite structures and restriction maps.

## Markov matching

The active proof is `GraphMarkovMatching.Stopped`. Its four headline conclusions are the
finite-type and zero-compatible alternatives, each at finite and infinite height. In the
uniform statements, constants are quantified before the model. Matching compares **states**;
types control transitions, cyclic classes and return conditions.

`Support/` contains shared arithmetic, binary labellings, automorphisms and probability
constructions. `Potential/` treats directed and restricted potentials, inverse-degree moments
and Jensen inequalities. `Process/` supplies finite-law recursion and consistency. `Models/`
contains the counter and composite models used in the applications.

| Modules in `GraphMarkovMatching/Stopped/` | Role |
|---|---|
| `Model`, `Constants`, `Scalar` | Types, processes, root quantities and scalar functions |
| `Moments`, `ZeroExpansion`, `WeightedExpansion`, `Paths` | Zero-degree and weighted stopping estimates |
| `FourLaw`, `Mixture`, `Root`, `Induction` | Local contraction, averaging and scalar induction |
| `Threshold`, `Main`, `Infinite`, `Transfer` | Explicit thresholds, matching conclusions and transfer to a given probability space |
| `Profiles`, `Semigroup`, `Presentation`, `Returns`, `Application` | Common atomic profiles, finite type sets, core probability bounds and common returns |
| `Projection`, `PresentationLaws` | State projection and identification of profile laws |
| `Numerics`, `Consequences`, `Exponent`, `ArityDependence`, `LowerBounds` | Numerical choices, exponent range and sharpness |
| `ProfileObstruction`, `Geometric`, `Unbounded`, `Perturbation`, `Original` | Prescribed-profile obstruction, one-site estimates, finite-height continuity and model identifications |

Keep these distinctions explicit:

- `phiE alpha t` is infinite at and above one. Do not replace this singular value by Lean's
  real-power value at zero.
- `PhiDres` integrates only over positive matching degrees. Zero-degree events and weighted
  zero-degree sums have separate estimates.
- `FullLab (I × V) h` records types and states; `Model.srel` compares states only. The
  Challenge formulations use state laws directly, with the projection proved in Solution.
- `Params` accepts upper bounds for the scalar extrema, so exact and rational choices use
  the same argument. Induction constants are in `ENNReal`; real estimates pass through `ofReal`.
- `FullLab` unfolds differently at height zero and successor height. Typed `leaf` and `branch`
  wrappers help control the folded form.
- The finite-type alternative requires the stated return, class-size and transition bounds.
  The zero-compatible alternative allows countably many types. Common-core probability
  floors cannot be dropped from a uniform theorem over changing arity laws.
- Equality of shifted semigroups permits choosing compatible profiles. It does not make
  arbitrary independently prescribed profiles compatible.

## Geometric assembly and classification

| Folder in `ChainClasses/` | Role |
|---|---|
| `Chain/` | Simple chain encoding, laws, metric transfer, quantisation, potential and coupling |
| `Scalar/`, `Shape/` | Marked spaces, gluing arithmetic, shape masses, contractions and assemblies |
| `Bushy/` | Simple-support shape fields, their laws and classification |
| `General/` | General Harris and shape constructions, relabelling, moments and assemblies |
| `Regime/` | Independent neck/arity laws, uniform fields and semigroup arithmetic |
| `Engine/` | Profile encoding, law identification, Markov matching and geometric transfer |
| `Universality/` | Full-tree geometry, bushy/chain universality, separation and concentrated pruning |
| `Classification/` | Public theorem interfaces |

Within `Engine/`, `ReducedProfiles` supplies the original reduced arity laws and their common
profiles. `ProfileKernel`, `ProfileLaw` and `ProfileProjection` construct the transitions,
identify the encoded law and pass to states. `ProfileMatching` applies matching on the given
probability space; `ProfileGeometry` transfers it to the original trees.
`BushyProfileBridge` and `ChainEngineBridge` supply the two regimes' probabilistic inputs.
The bare-neck geometry is in `Universality/ChainPieces` and `Universality/DirectChainGeometry`,
with its laws in `Regime/ChainNeckLaw` and `Regime/DirectChainLabels`. `Engine/ChainWitnesses`
and `Engine/ProfileWeightObstruction` establish the obstruction to uniform bounds as common
weights approach zero.

Bushy reduced laws both give positive mass to arity two, allowing the common binary core for
arbitrary support bounds. Chain laws use common atomic profiles from equality of their shifted
semigroups. The reduced arity laws and profiles remain fixed while the scale grows. The
classification uses the one-site bounds at exponent `5/2`.

Implementation boundaries:

- Binary addresses are `List Bool`, with `false,true` corresponding to the paper's `1,2`.
  General offspring laws also appear as real sequences with finite support, alongside the
  bundled `BranchingProcess.Offspring` interface. Shifted semigroups are `AddSubmonoid`s.
- `ChainClasses.IsQIWith` uses word metrics; `BranchingProcess.IsQIWith` uses graph metrics.
  `WordGraph` identifies them on prefix-closed trees. Preserve that bridge and root conditions.
- Geometric tails use `a^(D^k-1)`. Half-integral powers can be expressed by square roots, and
  auxiliary uniforms use Lebesgue measure restricted to `[0,1)`.
- Shrinking is defined on a tail of the shape space. Use `IsHalvingLevels` and the partial
  `IsCascadeOn` interface rather than imposing total shrinking and capacity everywhere.
  Couplings are available at every sufficiently large scale, not necessarily at every `D ≥ 30`.
  `hairy_ae_shape_tree_cross_large` and the general-support constructions use that threshold.
- `exists_scale` and `quantised_profile_scale` discharge largeness conditions; these are not
  extra assumptions of the final classification. Generic shape-tail and mass lemmas accept
  moment and factorisation hypotheses, which separate shape-law results establish.
- General couplings allow a distinct shrinking on each side and require comparability only
  for positive-mass atoms (`exists_gShapeCoupling_of_capacity₂'`).
- Keep the infinite-height matching argument at a fixed scale separate from the final limit
  over scales. The existence of some quasi-isometry is the event used in the latter limit.

The embedding proof uses the concentrated representative
`Offspring.concentrate`, with law `(7/8) δ_{J₁} + (1/8) θ` and `J₁ - 1 = 24 (J - 1)`.
It stays in the same infinite class. `Universality/ConcentratedPruning` finds a retained vertex
along the survival skeleton, including for laws with mass at zero. The first-child-ray version
and its tail estimate are also proved for the leafless setting. Classification transports the
binary embedding. The product-law argument uses `Measure.ae_ae_of_ae_prod` and positive
survival probability, without requiring measurability of the embedding event.

The printed proof instead chooses representatives by regime and uses the survival skeleton
for its bushy reduction. The correspondence manifest records this difference and the pruning
estimate difference.
Boundaries, fractal applications and continuous branching times remain outside the formalised
scope; see the exclusions in the correspondence manifest.

## Audit maintenance and local archives

`Challenge.lean` imports Mathlib alone. `Solution.lean` supplies the proofs, with definitions
and transports in `Solution/`. The thirteen endpoint names and the exact axiom whitelist are
maintained in [comparator.json](comparator.json), rather than in another list here.
Keep proof infrastructure and audit reports out of Challenge.

The [CI workflow](.github/workflows/build.yml) separates cached library builds from a fresh
audit. The audit prepares trusted Mathlib dependencies but does not restore project builds or
compile project code before the judge sees `Solution.lean`; preserve that guard.

The judge is `lake comparator` from the pinned toolchain, which also supplies the kernels it
replays through, so there is no separate verifier revision to pin and no exporter version to
check against the project toolchain. It sandboxes the build and export itself with bubblewrap,
binding `/` read-only, leaving only `.lake` writable, and giving the build, the export and the
kernels an empty network namespace; only dependency resolution has a network, which is why the
project must carry its `lake-manifest.json`.

Preserve the pinned bubblewrap build in the workflow. Ubuntu 24.04 restricts unprivileged user
namespaces by AppArmor, and the distribution package predates the fix for
GHSA-pxhw-h44j-8pfx, so the upstream release is built and a profile loaded for it, as
Palomar's verifier does. The sandbox is what the verdict rests on: neither the workflow nor
the local runner may pass `--inadvisably-no-sandbox`, and a host without bubblewrap simply
cannot run the audit.

The author's workstation retains deprecated proofs in `GraphMarkovMatching/Archive/FullMatching/`
and `ChainClasses/Archive/FullMatching/`. Their local source map is
`GraphMarkovMatching/Archive/FullMatching/README.md`. They are ignored by git and are not part
of a normal clone, default build, classification or audit. Preserve these local files. Their
original declaration names conflict with active counterparts, so keep their imports isolated.
Optional local targets are `GraphMarkovMatching.Archive` and `ChainClasses.Archive.FullMatching`;
the latter is separate from the unrelated `ChainClasses.Archive` target.
