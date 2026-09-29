module

/-
Matching of binary Markov tree label fields over the full rooted automorphism group.

The active proof is in `Stopped`: positive-degree stopping estimates, the four-law
contraction, scalar closure, and the finite and infinite matching theorems. Profile
presentations and their return bounds provide the common-core applications.

`Support` contains the shared scalar, product, tree and probability mathematics.
`Potential` contains directed and restricted potentials and their degree and moment
identities. `Process` contains the generic tree-law recursion and consistency facts.
`Models` contains the balanced counter laws used by the prescribed-profile obstruction
in `Stopped.ProfileObstruction`.

`Stopped.Transfer` applies finite estimates on any probability space with the specified
finite state or typed marginals. `Stopped.Perturbation` gives finite-height continuity
under changes to the root and child-pair laws.
-/

public import GraphMarkovMatching.Models.Counter
public import GraphMarkovMatching.Models.Examples
public import GraphMarkovMatching.Potential.Degrees
public import GraphMarkovMatching.Potential.Directed
public import GraphMarkovMatching.Potential.Inverse
public import GraphMarkovMatching.Potential.Jensen
public import GraphMarkovMatching.Potential.Restricted
public import GraphMarkovMatching.Process.Basic
public import GraphMarkovMatching.Process.Consistency
public import GraphMarkovMatching.Process.Recursion
public import GraphMarkovMatching.Process.Sim
public import GraphMarkovMatching.Support.Arithmetic
public import GraphMarkovMatching.Support.Contraction
public import GraphMarkovMatching.Support.Konig
public import GraphMarkovMatching.Support.Measure
public import GraphMarkovMatching.Support.Pairing
public import GraphMarkovMatching.Support.Phi
public import GraphMarkovMatching.Support.Potential
public import GraphMarkovMatching.Support.Product
public import GraphMarkovMatching.Support.Reduction
public import GraphMarkovMatching.Support.RowBound
public import GraphMarkovMatching.Support.Square
public import GraphMarkovMatching.Support.Trajectory
public import GraphMarkovMatching.Support.Tree

public import GraphMarkovMatching.Stopped.Application
public import GraphMarkovMatching.Stopped.ArityDependence
public import GraphMarkovMatching.Stopped.Consequences
public import GraphMarkovMatching.Stopped.Constants
public import GraphMarkovMatching.Stopped.Exponent
public import GraphMarkovMatching.Stopped.FourLaw
public import GraphMarkovMatching.Stopped.Geometric
public import GraphMarkovMatching.Stopped.Induction
public import GraphMarkovMatching.Stopped.Infinite
public import GraphMarkovMatching.Stopped.LowerBounds
public import GraphMarkovMatching.Stopped.Main
public import GraphMarkovMatching.Stopped.Mixture
public import GraphMarkovMatching.Stopped.Model
public import GraphMarkovMatching.Stopped.Moments
public import GraphMarkovMatching.Stopped.Numerics
public import GraphMarkovMatching.Stopped.Paths
public import GraphMarkovMatching.Stopped.Perturbation
public import GraphMarkovMatching.Stopped.Presentation
public import GraphMarkovMatching.Stopped.PresentationLaws
public import GraphMarkovMatching.Stopped.ProfileObstruction
public import GraphMarkovMatching.Stopped.Profiles
public import GraphMarkovMatching.Stopped.Projection
public import GraphMarkovMatching.Stopped.Returns
public import GraphMarkovMatching.Stopped.Root
public import GraphMarkovMatching.Stopped.Scalar
public import GraphMarkovMatching.Stopped.Semigroup
public import GraphMarkovMatching.Stopped.Threshold
public import GraphMarkovMatching.Stopped.Transfer
public import GraphMarkovMatching.Stopped.Unbounded
public import GraphMarkovMatching.Stopped.WeightedExpansion
public import GraphMarkovMatching.Stopped.ZeroExpansion
