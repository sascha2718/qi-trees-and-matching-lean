Implementation audit of `Challenge.lean`, completed on 12 September 2026.

The challenge now uses a smaller statement vocabulary and retains the twelve endpoints selected
by the manuscript. `lake build Challenge Solution` and `./comparator-audit.sh` passed. Comparator
confirmed equality of the challenge and solution statements and their defining dependencies,
checked the permitted axioms, and accepted the proofs through Lean kernel replay. The
[Comparator log](/tmp/ja-st-comparator-refactor.log) records the successful run.

The refactor reduced the challenge from 659 to 470 lines, and from 89 to 53 named vocabulary
declarations. The remaining vocabulary consists of 47 definitions or abbreviations, five
structures and one inductive predicate, together with two instances. An elaborated dependency
traversal found that all 53 named declarations are used by the theorem statements. There are
exactly twelve `sorry` holes, no explicit lemma declarations, no non-hole theorem bodies and no
literature axioms. Challenge still imports Mathlib alone.

The definitions are repeated independently in `Solution/Definitions.lean`; Challenge does not
import that file. `Solution/Infrastructure.lean` contains the library transports, and
`Solution/Transport.lean` proves the identifications needed by the shorter statements. The
headline proofs are in `Solution.lean`.

The substantive simplifications are:

- One unrestricted automorphism family and one full-matching relation serve both i.i.d. and
  Markov labels. The restricted-swap family is absent from Challenge.
- One potential serves all matching statements. The proofs identify its extended-value
  convention with the paper's graph potential under reflexivity.
- The Markov law is defined directly by recursion on state labellings. Types index these laws
  without appearing in their labellings. The solution proves equality with the state projection
  of the typed implementation, preservation of matching degrees and failure probabilities, and
  the required laws and matching event at infinite height.
- The finite-type transition bound sums over the full positive transition support, as in the
  paper's headline. The optional selected-component refinement remains in the internal proof
  infrastructure. Thus the challenge no longer exposes that additional refinement, while the
  paper's stated result and uniform constants are preserved.
- Both Galton–Watson families use the same parent–child graph and graph quasi-isometry
  definitions. The duplicated word-distance formulae are absent from Challenge. The solution
  proves the graph identifications and transports the two-value result without changing its
  quasi-isometry constant or root condition.
- The contraction coefficient is written directly by its extremum formula, and the two-value
  rate is written directly in the quantitative statement.

The twelve headline endpoints remain exactly those in `comparator-config.json`. All names below
are in namespace `Challenge`.

| Endpoint | Paper counterpart |
|---|---|
| `audit_graph_leaf_matching_bound` | `thm:matching`(1), `eq:leaf-bound`: threshold `1/256` and factor `(253/256)^h`. |
| `audit_graph_full_matching_bound` | `thm:matching`(2), `eq:full-bound`: threshold `10⁻⁴` and failure bound `16η`. |
| `audit_exists_infinite_tree_matching_graphAut` | Infinite conclusion of `thm:matching`(2), with an actual root-fixing automorphism. |
| `audit_bounded_graph_qi_point` | The bounded-graph fact supporting the finite class in `thm:trichotomy`. |
| `audit_extinction_of_not_supercritical` | Extinction for mean at most one, excluding the deterministic one-child law. |
| `audit_full_classification_ae_iff` | `thm:trichotomy`, including the finite class, in eventwise form under the unconditioned independent laws. |
| `audit_twovalue_ae_tree_family` | Qualitative part of `thm:twovalue`, including both deterministic endpoint laws. |
| `audit_twovalue_rate_tree` | Quantitative part of `thm:twovalue`, with constant `D²+3` and prefactor `256`. |
| `audit_markov_matching_finite` | Finite-type alternative of `thm:markov-matching`, uniformly over the stated return, class-size and transition bounds. |
| `audit_markov_matching_zero` | The `b(0)=1` alternative, without finite-type or return assumptions. |
| `audit_markov_matching_finite_infinite` | Infinite-height finite-type alternative, with one root-fixing automorphism. |
| `audit_markov_matching_zero_infinite` | Infinite-height `b(0)=1` alternative for countably many types. |

The original mathematical scope qualifications remain:

- The unconditioned classification is a reformulation of the paper's conditioned result.
  Positive survival probability and restriction to the survival rectangle are supplied by the
  library. The twelve targets do not separately spell out every deterministic representative or
  every consequence of the classification.
- The two-value parameter `t` is the probability of two children. For `D ≥ 3`, the displayed
  square-root rate equals the paper's `theta₁^(D(D−5/2))`, with `theta₁=1−t`; an existential
  threshold can always be increased to three.
- The detailed Markov restatement's `η/p` consequence follows from `ζ ≤ η/p` and is represented
  in the library rather than as a thirteenth challenge endpoint.
- Boundaries, fractal applications and continuous branching times remain outside the
  formalised scope, as expressly disclosed by the manuscript. No external axioms were introduced.
- Graph quasi-isometry is used on connected graphs, where Mathlib's natural-valued graph
  distance agrees with the intended metric.

`formalization.yaml` now correctly states that only an upper offspring-support bound is
required. There is no positive-top-mass hypothesis; the library tightens the bound internally.
The metadata also describes the direct state laws, full-support transition bound and shared
quasi-isometry vocabulary.

The README now distinguishes trusted local development from the fresh CI audit of untrusted
code. The local script uses Comparator's unsandboxed development shim on macOS and defaults to
real Landrun on Linux. The inspected CI workflow uses a fresh checkout, avoids compiling project
code before Comparator, pins the verifier tools, and adds systemd restrictions. This audit ran
locally on macOS; it did not execute a fresh CI run or an additional independently implemented
kernel. Only `propext`, `Quot.sound` and `Classical.choice` are permitted, unchanged from before.
