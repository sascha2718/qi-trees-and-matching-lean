/-
The branching-process foundation: Galton-Watson trees over an `N`-ary
alphabet, their offspring laws, extinction, and the decomposition of a
supercritical sample into its surviving skeleton and the finite bushes hanging
off it.

The library is independent of the rest of the project. `ChainClasses` consumes
it; nothing here consumes `ChainClasses`, `GraphMatching` or
`GraphMarkovMatching`.

* `Word`: the ambient `N`-ary tree, its longest common prefix and metric, and
  subtrees as terms of `Descriptive.tree (Fin N)`.
* `Offspring`: offspring laws of bounded support, their mean and criticality,
  the generating function, and the extinction probability as its least fixed
  point.
* `Sample`: the genealogical tree cut out by a field of offspring counts, the
  branching property of the subtree at a vertex, survival, the skeleton of
  vertices with infinite progeny, and the rays it carries.
* `Law`: the law of a sample, tying the two halves together. The extinction
  probability of `Offspring` is the probability that the sample of `Sample` is
  finite, provided the alphabet carries the support.
* `Conditioned`: the law conditioned on survival, the law of the root's
  surviving-child count, which is the Harris transform, and the conjugate tilt
  at the root of a subtree conditioned to die.
* `Skeleton`: trees as a measurable space, the law of a sample as a measure on
  them, the reduced and the conjugate law as an `Offspring`, the skeleton as a
  measurable map with the branching property at the root, and the containment
  events as a generating π-system.
* `Decorated`: the joint box, constraining the surviving and the dying children
  of a vertex at once.
* `Harris`: **the Harris decomposition** `thm:harris` in its joint form, at
  general bounded support: conditionally on the skeleton, the decorations are
  independent conjugate samples, as one identity of laws.
* `Progeny`: a finite sample, the probability that the tree is exactly a
  prescribed one, and the number of its vertices.
* `Field`: the i.i.d. coordinate field over an arbitrary index type, built on
  `Measure.infinitePi`, with the Bernoulli specialisation in the shape the
  chain half of the paper consumes.
* `Geometry`: the coarse geometry of trees on `SimpleGraph`, with the two
  separations `thm:bush-separation` and `thm:three-rays`, the latter for
  quasi-isometric embeddings.
* `Embedding`: the calculus of quasi-isometric embeddings, composition, isometric
  maps, bounded graphs and the ray, behind `sec:embedding-hierarchy`.
* `Pruning`: `thm:concentrated-regular-subtree`, the pruning of a concentrated
  law, the lower bound on the probability that the root is retained, and the
  regular `m`-ary subtree below a retained vertex.
* `PrunedTree`: the exact binomial recursion of the pruning, its fixed point,
  and the retained descendant tree as a Galton-Watson tree with the binomial
  law conditioned to be at least `m`, under the law conditioned on a retained
  root.
-/
import BranchingProcess.Word
import BranchingProcess.Offspring
import BranchingProcess.Sample
import BranchingProcess.Law
import BranchingProcess.Conditioned
import BranchingProcess.Skeleton
import BranchingProcess.Decorated
import BranchingProcess.Harris
import BranchingProcess.Progeny
import BranchingProcess.Field
import BranchingProcess.Geometry
import BranchingProcess.Embedding
import BranchingProcess.Pruning
import BranchingProcess.PrunedTree
