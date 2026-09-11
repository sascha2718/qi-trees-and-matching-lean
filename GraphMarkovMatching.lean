/-
Matching of binary Markov tree label fields over the full rooted automorphism group.

The active proof is in `Stopped`: positive-degree stopping estimates, the four-law
contraction, scalar closure, and the finite and infinite matching theorems. Profile
presentations and their return bounds provide the common-core applications.

`Support` contains the shared scalar, product, tree and probability mathematics.
`Potential` contains directed and restricted potentials and their degree and moment
identities. `Process` contains the generic tree-law recursion and consistency facts.
`Models` retains the balanced and composite counter models used as examples of the
profile theorem, without the former matching proof for those models.

`Stopped.Transfer` applies finite estimates on any probability space with the specified
finite state or typed marginals. `Stopped.Perturbation` gives finite-height continuity
under changes to the root and child-pair laws.
-/

import GraphMarkovMatching.Models.Composite
import GraphMarkovMatching.Models.Counter
import GraphMarkovMatching.Models.Examples
import GraphMarkovMatching.Potential.Degrees
import GraphMarkovMatching.Potential.Directed
import GraphMarkovMatching.Potential.Inverse
import GraphMarkovMatching.Potential.Jensen
import GraphMarkovMatching.Potential.Restricted
import GraphMarkovMatching.Process.Basic
import GraphMarkovMatching.Process.Consistency
import GraphMarkovMatching.Process.Recursion
import GraphMarkovMatching.Process.Sim
import GraphMarkovMatching.Support.Arithmetic
import GraphMarkovMatching.Support.Contraction
import GraphMarkovMatching.Support.Konig
import GraphMarkovMatching.Support.Measure
import GraphMarkovMatching.Support.Pairing
import GraphMarkovMatching.Support.Phi
import GraphMarkovMatching.Support.Potential
import GraphMarkovMatching.Support.Product
import GraphMarkovMatching.Support.Reduction
import GraphMarkovMatching.Support.RowBound
import GraphMarkovMatching.Support.Square
import GraphMarkovMatching.Support.Trajectory
import GraphMarkovMatching.Support.Tree

import GraphMarkovMatching.Stopped.Application
import GraphMarkovMatching.Stopped.ArityDependence
import GraphMarkovMatching.Stopped.Consequences
import GraphMarkovMatching.Stopped.Constants
import GraphMarkovMatching.Stopped.Exponent
import GraphMarkovMatching.Stopped.FourLaw
import GraphMarkovMatching.Stopped.Geometric
import GraphMarkovMatching.Stopped.Induction
import GraphMarkovMatching.Stopped.Infinite
import GraphMarkovMatching.Stopped.LowerBounds
import GraphMarkovMatching.Stopped.Main
import GraphMarkovMatching.Stopped.Mixture
import GraphMarkovMatching.Stopped.Model
import GraphMarkovMatching.Stopped.Moments
import GraphMarkovMatching.Stopped.Numerics
import GraphMarkovMatching.Stopped.Original
import GraphMarkovMatching.Stopped.Paths
import GraphMarkovMatching.Stopped.Perturbation
import GraphMarkovMatching.Stopped.Presentation
import GraphMarkovMatching.Stopped.PresentationLaws
import GraphMarkovMatching.Stopped.ProfileObstruction
import GraphMarkovMatching.Stopped.Profiles
import GraphMarkovMatching.Stopped.Projection
import GraphMarkovMatching.Stopped.Returns
import GraphMarkovMatching.Stopped.Root
import GraphMarkovMatching.Stopped.Scalar
import GraphMarkovMatching.Stopped.Semigroup
import GraphMarkovMatching.Stopped.Threshold
import GraphMarkovMatching.Stopped.Transfer
import GraphMarkovMatching.Stopped.Unbounded
import GraphMarkovMatching.Stopped.WeightedExpansion
import GraphMarkovMatching.Stopped.ZeroExpansion
