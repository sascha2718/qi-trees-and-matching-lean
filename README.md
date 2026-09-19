# The quasi-isometry classes of Galton--Watson trees

This repository contains the Lean 4 formalisation accompanying the classification of bounded-
support Galton--Watson trees up to quasi-isometry. It includes the probabilistic foundations, two
matching libraries, the geometric assembly, and the public same-class/different-class
classification theorems.

- [Source repository](https://github.com/sascha2718/qi-trees-and-matching-lean)

## Libraries

The project has four default library targets.

| Library | Role |
|---|---|
| `BranchingProcess` | Galton--Watson trees, conditioning, skeletons, and geometric obstructions |
| `GraphMatching` | Matching i.i.d. labels on the binary tree by automorphisms |
| `GraphMarkovMatching` | The general Markov matching theorem and its common-semigroup applications (`Stopped/`) |
| `ChainClasses` | Chain and shape encodings, transfer, universality, separation, and classification |

The toolchain is pinned to Lean `v4.32.2`, with Mathlib pinned to the matching release in
`lakefile.toml`.

See [ARCHITECTURE.md](ARCHITECTURE.md) for the module map, representation choices and
proof-maintenance notes. [CHALLENGE_REVIEW.md](CHALLENGE_REVIEW.md) records dated audit evidence.

## Public classification API

Import the public façade with:

```lean
import ChainClasses.Classification
```

The main declarations below are in the `ChainClasses` namespace.

| Result | Public declaration |
|---|---|
| Complete theorem for offspring supported on `{0,1,2}` | `simple_classification` |
| Eventwise simple-support classification | `simple_classification_ae_iff` |
| Same-class simple-support conclusion | `simple_same_class_ae` |
| Different-class simple-support conclusion | `simple_different_class_ae` |
| Simple-support separation from the ray | `simple_not_ray_ae` |
| Eventwise classification for packaged conditioned laws | `classification_ae_iff` |
| Same-class conclusion at general bounded support | `same_class_ae` |
| Different-class conclusion at general bounded support | `different_class_ae` |
| Classification expanded for two offspring laws | `offspring_classification_ae_iff` |
| General separation from the ray | `classification_not_ray_ae` |
| Complete classification including the finite class, root-preserving | `full_classification_rooted_ae_iff` |

The conditioned declarations concern Galton--Watson laws conditioned on an infinite realisation
and classify the four infinite classes (R), (F), `(C_Λ)`, and (B). The last declaration is stated
over the unconditioned laws and includes the finite class `(Fin)`: two independent trees are
almost surely quasi-isometric exactly when both are finite, or both are infinite with laws in
the same infinite class.

The façade is split into `ChainClasses.Classification.Simple`,
`ChainClasses.Classification.Complete`, `ChainClasses.Classification.Finite` and
`ChainClasses.Classification.Embedding`. The proof implementation remains in
`ChainClasses.Bushy.Trichotomy`, `ChainClasses.Universality.GeneralTrichotomy`, and
`ChainClasses.Universality.ChainSeparationProof`. The last façade module proves the mutual
embeddability theorem `embedding_hierarchy_ae`: on survival, a sample of a finitely supported
supercritical law almost surely admits quasi-isometric embeddings into the binary tree and from
it. It rests on the pruning lemma of `BranchingProcess.Pruning`, applied along the skeleton
descent in `ChainClasses.Universality.ConcentratedPruning`, and on the classification, and
it records the strict hierarchy `Fin ≺ Ray ≺ Supercritical` of quasi-isometric embeddability.

## The audited statements

`Challenge.lean` states thirteen theorems over Mathlib alone, and `comparator.json` selects exactly
these for the audit. All are in the `Challenge` namespace. Compatibility of two labels means that
they are equal or adjacent in the label graph, `η_α` is the one-site potential of the label law,
and `ζ_α` is the one-site defect of a Markov model.

| Declaration | Statement |
|---|---|
| `audit_graph_leaf_matching_bound` | Labels are drawn i.i.d. from a law `μ` on the vertices of a graph `G`. If the potential `η_{5/2}` is at most `1/256`, two independent labellings of the leaves of the binary tree of height `h` fail to be matched by an automorphism with probability at most `(253/256)^h η_{5/2}`. |
| `audit_graph_full_matching_bound` | In the same setting with every vertex labelled, and `η_{5/2}` at most `10⁻⁴`, the failure probability is at most `16 η_{5/2}` at every height. |
| `audit_exists_infinite_tree_matching_graphAut` | For a reflexive symmetric compatibility relation with `η_{5/2}` at most `10⁻⁴` there is a probability space carrying two independent consistent labellings of the binary trees of all heights, with the i.i.d. laws, on which some root-fixing automorphism of the infinite binary tree matches the labels at every vertex with probability at least `1 - 16 η_{5/2}`. |
| `audit_bounded_graph_qi_point` | A connected graph of bounded diameter is quasi-isometric to the one-vertex graph. |
| `audit_extinction_of_not_supercritical` | A finitely supported offspring law of mean at most one, other than the deterministic single child, gives an almost surely finite tree. |
| `audit_full_classification_ae_iff` | For two independent Galton--Watson trees with finitely supported offspring laws, almost surely a root-preserving quasi-isometry exists exactly when both trees are finite, or both are infinite and the two laws lie in the same infinite class; and when the laws fail that condition there is almost surely no quasi-isometry at all. The infinite classes are the ray `θ(1) = 1`, the laws with `θ(0) = θ(1) = 0`, the chain laws `θ(0) = 0 < θ(1) < 1` grouped by the additive submonoid generated by their shifted support, and the laws with `θ(0) > 0`. |
| `audit_mutual_embeddability` | For a finitely supported supercritical offspring law, almost surely on survival the sample tree admits a quasi-isometric embedding into the binary tree `𝒩(2)` and receives a quasi-isometric embedding of the binary tree. A quasi-isometric embedding satisfies the two metric inequalities of a quasi-isometry without coarse density. |
| `audit_twovalue_ae_tree_family` | Two independent trees whose vertices have two children with probability `t` and one child otherwise are almost surely quasi-isometric by a root-preserving map, for every `t` in `[0,1]`. |
| `audit_twovalue_rate_tree` | For `0 < t < 1` there is a threshold above which the probability that no root-preserving `(D²+3)`-quasi-isometry exists is at most `256 √((1-t)^{D(2D-5)})`. |
| `audit_markov_matching_finite` | For `α ≥ 1` with `λ_α < 1` and bounds `H`, `T`, `B` there are constants `K` and `ε > 0` such that every model with at most `T` types per cyclic class, transition inverse sums at most `B`, fresh positivity, common returns within `H`, and defect `ζ_α` at most `ε`, has any two types of the same class failing to match with probability at most `K ζ_α`, at every height. |
| `audit_markov_matching_zero` | For `α ≥ 1` with `λ_α < 1` there are constants `K` and `ε > 0` such that every model with `δ = 0` and defect `ζ_α` at most `ε` has every pair of types failing to match with probability at most `K ζ_α`, at every height, with no finite-type or return hypothesis. |
| `audit_markov_matching_finite_infinite` | Under the hypotheses of the finite-type statement, two independent consistent processes of same-class types are carried by a probability space on which one root-fixing automorphism of the infinite binary tree matches their states at every vertex with probability at least `1 - K ζ_α`. |
| `audit_markov_matching_zero_infinite` | The same conclusion under the zero-compatible hypotheses, for any two of countably many types. |

The constants of the two Markov alternatives depend only on `α, H, T, B` and on `α` respectively,
and are uniform over models and heights.

## Build and audit

Run commands from the repository root. To build all four libraries:

```bash
lake build
```

`Challenge.lean` states the audited results using Mathlib alone. `Solution.lean` proves them
from the four libraries, with its definitions and proof transports in `Solution/`.

The [local audit runner](comparator-audit.sh) requires separately built Comparator and
lean4export tools. The exporter must match the project's `lean-toolchain`. Set
`COMPARATOR_TOOLS` to a directory containing the `comparator/` and `lean4export/` checkouts
and their built executables; the runner defaults to `~/Documents/lean`. On Linux, `landrun`
must be on `PATH` or selected through `COMPARATOR_LANDRUN`. `COMPARATOR_LEAN4EXPORT` can
override the exporter path. The [CI workflow](.github/workflows/build.yml), in its
“Build pinned verification tools” step, records the exact tool revisions and build commands.

With these prerequisites installed, for trusted local development run

```bash
./comparator-audit.sh
```

Comparator builds Challenge and Solution, compares their statements and definitions, checks
the permitted axioms, and replays the exported proofs through the Lean kernel. A separate
`lake build Challenge Solution` is useful during development but is not a prerequisite.

On macOS the local script uses Comparator's development shim, which does not sandbox the
builds. On Linux it defaults to real `landrun`. This local development command should not be
confused with the fresh audit of potentially untrusted code: the CI comparator job uses a
separate checkout, avoids compiling project code beforehand, and runs with real Landrun and
additional systemd restrictions. Its verification tools are pinned to immutable revisions.
The optional additional nanoda kernel is disabled in the current configuration.

The challenge imports Mathlib alone and contains only statement vocabulary and theorem holes;
Solution and the libraries contain the proofs. The comparator permits only `propext`,
`Classical.choice` and `Quot.sound`, and the thirteen proved statements use exactly those three
axioms and no literature axiom.

The GitHub Actions workflow builds the libraries and runs the comparator audit.

To check that every labelled manuscript declaration is accounted for in the
paper--Lean correspondence manifest, that every listed Lean name occurs as a source
declaration, and that the thirteen headline names agree across the challenge, solution,
comparator, and formalisation metadata, run

```bash
python3 -B scripts/check_paper_correspondence.py
```

This is a dependency-free static source check. It does not invoke Lean or LaTeX and
does not replace `lake build` or the comparator audit. In particular, dependency-minimality
of the definitions in `Challenge.lean` still requires semantic review in Lean's elaborated
environment.

This check also needs the manuscript sources: it reads the files listed in
`paper-correspondence.yaml`, together with `appendices.tex`, from the **parent directory of
the Lean checkout**. The author's layout is a manuscript repository containing this checkout
as `lean/`. A standalone clone supplies the Lean source but not those parent-directory files.
Reproducing the correspondence check requires the matching manuscript version in that layout;
the Lean library build and comparator audit do not require the manuscript sources.

On the author's workstation, `.lake/packages` is an untracked symlink to the package directory
of `~/Documents/lean/mathematics_in_lean`. Dependency resolution can therefore modify another
project's checkouts. Do not run `lake update` or edit the toolchain/dependency configuration as
routine maintenance in that layout. A fresh clone uses the tracked dependency configuration
without this machine-specific symlink.

The challenge uses one unrestricted automorphism family for both matching theorems, states
the Markov laws directly on state labels, and uses the full transition-support bound from the
paper. The two-value and general classification results share the parent-child graph and
quasi-isometry definitions. Only an upper offspring-support bound is required; positive mass
at that bound is not a hypothesis. The boundary and fractal applications and the continuous
branching-time results are outside the formalised scope, as disclosed in the manuscript.

## Provenance and process

The formalised results are the matching theorems and the classification of "The quasi-isometry
classes of Galton--Watson trees" by Jayadev S. Athreya and Sascha Troscheit. That manuscript is in
preparation and has not been posted, so a reader cannot consult it independently at present; its
appendix records the statement-by-statement correspondence with the Lean declarations. The
formalisation and the manuscript were developed together by the same authors, and no novelty is
claimed here beyond what the manuscript claims. No earlier formalisation of these results, in Lean
or in another system, is known to the authors.

AI tools were used extensively in the Lean development, following the principles of the Leiden
Declaration on the responsible use of artificial intelligence in research. Agentic sessions in
Claude Code wrote, refactored and repaired library proofs against a fixed statement surface; an
earlier AI-assisted workflow produced an intermediate formalisation that the present development
supersedes; and interactive assistance was used for individual arguments and for copy-editing. The
statement design, `Challenge.lean`, `Solution.lean` and the comparator configuration were written
and reviewed by the authors, who verified every non-human part of the development and accept full
responsibility for its contents. The Lean code has had no independent human review.

`formalization.yaml` records the sources, licence, classification codes, scope, divergences and
production process in the mathlib-initiative v0.4 self-reporting format.

## License

Apache License 2.0. See [`LICENSE`](LICENSE).
