# The quasi-isometry classes of Galton–Watson trees

This repository contains the Lean 4 formalisation of *The quasi-isometry classes of
Galton–Watson trees* by Jayadev S. Athreya and Sascha Troscheit. It develops the classification
of Galton–Watson trees with finitely supported offspring laws, together with the i.i.d. and
Markov automorphism-matching theorems used in its proof.

- **Paper:** [arXiv:2609.23882](https://arxiv.org/abs/2609.23882). Theorem numbers below refer
  to version 2.
- **Palomar:** [PALOMAR-2026-09-25-000002](https://palomar-registry.org/entry?id=PALOMAR-2026-09-25-000002).

A recent version of the formalisation is archived and machine-checked on Palomar. This
repository may contain subsequent changes. Significant changes will be uploaded to Palomar
as new snapshots.

## Formalised results

- **Classification (Theorem 1.2):** the complete quasi-isometry classification for finitely
  supported offspring laws, including the finite class and the classification on survival.
- **Mutual embeddability (Theorem 1.3):** almost surely on survival, a supercritical sample
  and the infinite binary tree admit quasi-isometric embeddings into one another.
- **Two-value universality (Theorem 1.4):** two independent samples from a fixed offspring
  law supported on `{1,2}` are almost surely quasi-isometric, with a quantitative bound on
  the failure probability at a prescribed quasi-isometry constant.
- **I.i.d. matching (Theorem 5.1):** automorphism matching of independent binary-tree
  labellings, with finite-height leaf and full bounds and an infinite-tree conclusion.
- **Markov matching (Theorem 6.1):** matching of typed binary-tree label processes at finite
  and infinite height, under the finite-type or zero-compatible hypotheses.

The libraries also prove the branching-process foundations, geometric obstructions, pruning
results and quantitative estimates supporting these theorems. Boundary quasisymmetry, the
fractal percolation applications and the results on continuous random branching times are
**not** formalised but follow easily from the prose proofs in the arXiv preprint.

## Statements and proofs

[Challenge.lean](Challenge.lean) states thirteen headline results using Mathlib alone, with
the definitions needed to read them independently of the proof libraries. Each theorem has
an intentional `sorry` placeholder. [Solution.lean](Solution.lean) proves these statements
from the four libraries; the solution and libraries contain no `sorry`.

The Comparator check verifies that the solution proves the same statements with the same
definitions, using only `propext`, `Classical.choice` and `Quot.sound`. No literature result
is assumed as an axiom. [comparator.json](comparator.json) specifies the thirteen declarations
and permitted axioms; the [verification workflow](.github/workflows/build.yml) checks the
libraries and runs the comparator audit.

Appendix B of the paper and [paper-correspondence.yaml](paper-correspondence.yaml) give the
detailed correspondence between the paper and Lean, including differences in formulation.
The [correspondence checker](scripts/check_paper_correspondence.py) checks the declaration
references against the Lean and manuscript sources.

## Libraries

| Library | Contents |
|---|---|
| [BranchingProcess](BranchingProcess.lean) | Galton–Watson trees, extinction, conditioning, skeletons, pruning and geometry |
| [GraphMatching](GraphMatching.lean) | I.i.d. automorphism matching on the binary tree |
| [GraphMarkovMatching](GraphMarkovMatching.lean) | Markov matching and common-semigroup applications |
| [ChainClasses](ChainClasses.lean) | Geometric constructions, universality, separation, classification and embeddings |

The two matching libraries are mutually independent. `ChainClasses` combines them with
`BranchingProcess`. The principal classification interface is
[ChainClasses.Classification](ChainClasses/Classification.lean); each library's root module
lists its constituent files.

## Attribution and licence

The paper and formalisation were developed together by the same authors. AI tools were used
extensively in the Lean development.

The Lean development is distributed under the [Apache License 2.0](LICENSE).
