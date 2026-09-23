# Challenge audit record

Audit of the statement surface and its mechanical verification at commit `68c8d2d`,
22 September 2026. Theorem, equation and condition numbers refer to version 1 of
[arXiv:2609.23882](https://arxiv.org/abs/2609.23882).

## Statement surface

`Challenge.lean` imports Mathlib alone and states the thirteen theorems selected in
`comparator.json`, each with the proof `sorry`. It contains no other theorem, lemma, axiom,
option or notation. Its vocabulary consists of 48 definitions and abbreviations, six structures
and one inductive predicate, together with two instances. An elaborated dependency traversal,
starting from the types of the thirteen theorems and following the types and values of the
`Challenge` declarations they use, reaches all 55 named declarations and the measurable-space
instance on full labellings. The coercion instance for offspring laws is used during
elaboration, and its applications are unfolded in the elaborated statements.

`comparator.json` selects exactly the thirteen theorems, declares no `definition_names`, and
permits only `propext`, `Quot.sound` and `Classical.choice`. `Solution.lean` proves declarations
of the same names and types from the four libraries. `Solution/Definitions.lean` repeats the
challenge vocabulary without importing `Challenge.lean`, `Solution/Infrastructure.lean` contains
the library transports, and `Solution/Transport.lean` proves the identifications needed by the
statements.

All names below are in namespace `Challenge`.

| Endpoint | Paper counterpart |
|---|---|
| `audit_graph_leaf_matching_bound` | Theorem 5.1(1), the leaf bound (5.2): threshold `1/256` and factor `(253/256)^h`. |
| `audit_graph_full_matching_bound` | Theorem 5.1(2), the full bound (5.3) at finite height: threshold `10⁻⁴` and failure bound `16 η_{5/2}`. |
| `audit_exists_infinite_tree_matching_graphAut` | Theorem 5.1(2) at infinite height, with one root-fixing automorphism of the infinite binary tree. |
| `audit_bounded_graph_qi_point` | The bounded-graph fact behind the finite class of Theorem 1.2. |
| `audit_extinction_of_not_supercritical` | Extinction for mean at most one, excluding the deterministic one-child law. |
| `audit_full_classification_ae_iff` | Theorem 1.2, including the finite class, eventwise under the unconditioned independent laws. |
| `audit_mutual_embeddability` | Theorem 1.3: on survival, the sample almost surely embeds quasi-isometrically into the binary tree and receives an embedding of it. |
| `audit_twovalue_ae_tree_family` | Theorem 1.4, almost-sure part, including both deterministic endpoint laws. |
| `audit_twovalue_rate_tree` | Theorem 1.4, the rate (1.1), with constant `D² + 3` and prefactor `256`. |
| `audit_markov_matching_finite` | Theorem 6.1, finite-type alternative, uniformly over the return, class-size and transition bounds. |
| `audit_markov_matching_zero` | Theorem 6.1, the alternative `b(0) = 1`, without finite-type or return hypotheses. |
| `audit_markov_matching_finite_infinite` | Theorem 6.1 at infinite height, finite-type alternative, with one root-fixing automorphism. |
| `audit_markov_matching_zero_infinite` | Theorem 6.1 at infinite height, alternative `b(0) = 1`, for countably many types. |

## Statement design

- One automorphism family, encoded by iterated swaps, and one full-matching relation serve the
  i.i.d. and the Markov statements. The infinite-height statements use root-fixing graph
  automorphisms of the infinite binary tree.
- One potential serves all matching statements. The solution identifies its extended-value
  convention with the paper's graph potential under reflexivity.
- Markov laws are defined directly on state labellings, and types index these laws. The
  solution proves that they are the state projections of the typed implementation, with the
  same matching degrees and failure probabilities.
- The finite-type transition bound sums over the full support of each transition law, as in
  Theorem 6.1. The bound `ζ_α ≤ η_α/p` of the detailed restatement is the library lemma
  `GraphMarkovMatching.Stopped.Model.zeta_le_eta_div`.
- Both Galton–Watson families use the same parent–child graph and quasi-isometry definitions.
  Distances are Mathlib's `SimpleGraph.dist`, which is the graph metric on the connected graphs
  used.
- Offspring laws carry an upper support bound `J ≤ N` without positive mass at `J`. The library
  tightens the bound internally.
- The classification is stated over the unconditioned laws. The library supplies positive
  survival probability and the restriction to the survival events.
- For `D ≥ 3` the square-root rate equals the paper's `θ(1)^(D(D - 5/2))` with `θ(1) = 1 - t`,
  and the existential threshold can always be raised to three.
- Boundaries, fractal applications and continuous branching times are outside the formalised
  scope, as disclosed in the paper. No literature result is assumed as an axiom.

## Evidence

- `lake --wfail build` builds the four libraries against Lean and Mathlib `v4.35.0-rc2` with no
  errors and no warnings, across 3,944 jobs. `lake --wfail build Solution` adds the comparator
  side, 9,116 jobs, equally clean.
- `lake env lean Challenge.lean` elaborates against Mathlib `v4.35.0-rc2` with exactly thirteen
  `sorry` warnings and no errors.
- `#print axioms` reports each of the thirteen audited theorems, as `Solution.lean` proves them,
  to depend on `propext`, `Classical.choice` and `Quot.sound` alone.
- `lake comparator --config comparator.json --paranoid` accepts the solution: the statements
  agree with the Challenge, the permitted axioms hold, and `leanchecker-paranoid`, `lean4lean`,
  `nanoda`, `con-leche`, `con-ron` and Lean's own kernel each accept the export of 47,200
  declarations. That run was made on macOS, which has no bubblewrap, so it passed
  `--inadvisably-no-sandbox` and the judge recorded the result as untrustworthy. It is a
  development check. The sandboxed audit is the CI comparator job, which provisions the pinned
  bubblewrap release and judges a fresh checkout that carries no compiled project code.
- The registry submission `9ji1jvxxbyjl` records the state at `cb13bb6`, on Lean `v4.32.2`. The
  upgraded tree needs its own Palomar preflight, at a pipeline commit that carries the
  toolchain's `lake comparator`, before it is submitted.
- The Challenge, at 605 lines and 33,315 bytes, exceeds Palomar's preferred review surface of
  300 lines and 32 KiB, and stays within the hard limits of 1,000 lines and 100 KiB.
- `python3 -B scripts/check_paper_correspondence.py` passes, with 89 labelled paper
  declarations, 13 structure entries and 6,564 Lean source declarations, against the authors'
  current manuscript sources and against the source files of arXiv:2609.23882v1.
- `formalization.yaml` passes Palomar's intake validation and the mathlib-initiative v0.4
  schema. The detected licence, Apache-2.0, matches the declared one. The project toolchain
  equals that of the pinned Mathlib revision, every manifest dependency is a GitHub repository
  pinned to a full commit, and the repository contains no submodules, LFS pointers or compiled
  artifacts.
