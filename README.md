# The quasi-isometry classes of Galton--Watson trees

This repository contains the Lean 4 formalisation accompanying the classification of bounded-
support Galton--Watson trees up to quasi-isometry. It includes the probabilistic foundations, two
matching libraries, the geometric assembly, and the public same-class/different-class
classification theorems.

- [Blueprint and dependency graph](https://sascha2718.github.io/qi-trees-and-matching-lean/)
- [Printable blueprint](https://sascha2718.github.io/qi-trees-and-matching-lean/blueprint.pdf)
- [Generated API documentation](https://sascha2718.github.io/qi-trees-and-matching-lean/docs/)

The blueprint follows the mathematical proof in reading order. Each formalised statement links to
its Lean declaration, and the web version displays the theorem-dependency graph.

## Libraries

The project has four default library targets. 

| Library | Role |
|---|---|
| `BranchingProcess` | Galton--Watson trees, conditioning, skeletons, and geometric obstructions |
| `GraphMatching` | Matching i.i.d. labels on the binary tree by automorphisms |
| `GraphMarkovMatching` | The one-law and two-law matching engine for tree-indexed Markov label fields |
| `ChainClasses` | Chain and shape encodings, transfer, universality, separation, and classification |

The toolchain is pinned to Lean `v4.32.2`, with Mathlib pinned to the matching release in
`lakefile.toml`.

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

These general declarations concern Galton--Watson laws conditioned on an infinite realisation.
They classify the four infinite classes (R), (F), `(C_Λ)`, and (B). The elementary finite class
`(Fin)` in the paper lies outside the conditioned-infinite Lean endpoint.

The façade is split into `ChainClasses.Classification.Simple` and
`ChainClasses.Classification.Complete`. The proof implementation remains in
`ChainClasses.Bushy.Trichotomy`, `ChainClasses.Universality.GeneralTrichotomy`, and
`ChainClasses.Universality.ChainSeparationProof`.

## Build and audit

Run commands from the repository root. To build all four libraries:

```bash
lake build
```

The axiom audit is the comparator run. `Challenge.lean` restates the audited theorem surface using Mathlib alone, while `Solution.lean`
discharges those statements from the four libraries. Build the two modules with

```bash
lake build Challenge Solution
```

and run the independent kernel audit with

```bash
./comparator-audit.sh
```

The audited endpoints are listed in `comparator-config.json`. They cover the finite and infinite
general Markov matching theorem (the latter over an actual root-fixing graph automorphism), the
leaf, full, and infinite i.i.d. matching theorems, the complete conditioned-infinite
Galton--Watson classification, and both the qualitative and quantitative two-value results.

## Build the blueprint locally

The printable and web sources are in `blueprint/src`. A local PDF build requires XeLaTeX and
`latexmk`:

```bash
cd blueprint/src
latexmk
```

This writes `print.pdf`. To build the web version, install `leanblueprint`, `plasTeX`,
`plastexdepgraph`, and `plastexshowmore`, then run:

```bash
cd blueprint/src
plastex -c plastex.cfg web.tex
```

The web entry point is written to `blueprint/web/index.html`. The GitHub Actions workflows build
the libraries, comparator audit, blueprint, and API documentation, then deploy the combined site
to GitHub Pages.

## License

Apache License 2.0. See [`LICENSE`](LICENSE).
