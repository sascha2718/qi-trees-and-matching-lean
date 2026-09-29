module

/-
`GraphMatching`: the i.i.d. matching theorem over a countable label graph
(`graph_matching_selfcontained.tex`), at the exponent `α = 5/2`.

* `Phi`          the weight `φ_α` (`eq:alpha`) and its elementary facts
* `Maxima`       the two maxima `eq:lambda-max` and `eq:kappa`
* `Transversal`  the `2 × 2` transversal (`thm:transversal`)
* `Potential`    the label space, the degrees `q`/`r`, and the potential `Φ` (`eq:iid-potential`)
* `Product`      the product of relations (`thm:product`)
* `Square`       the symmetrised square `R^□` (`eq:square`)
* `RowBound`     the row bound `eq:row-bound`
* `Contraction`  the contraction `thm:contraction`
* `Transport`    isomorphism invariance of the potential
* `Tree`         the tree layer: leaf labellings and the swap group `Aut(𝔹_h)`
* `Reduction`    the reduction `thm:reduction`
* `Konig`        the König step of `sec:reduction`
* `Graph`        the graph specialisation (`sec:graph`)
* `Examples`     the path graph of `sec:integer` and the star example
* `DoubleExp`    the double-exponential tail `thm:double-exp`
* `Measure`      the measure step of the infinite-tree matching
* `Kolmogorov`   the i.i.d. product measure on the infinite tree
* `AutBridge`    the swap group as the automorphism group of the tree, and the
                 matching relations over graph automorphisms
* `Probability`  the exact full-labelling probability recursion, moment bounds and
                 scalar failure criterion in `prelims.tex`
-/
public import GraphMatching.Phi
public import GraphMatching.Maxima
public import GraphMatching.Transversal
public import GraphMatching.Potential
public import GraphMatching.Product
public import GraphMatching.Square
public import GraphMatching.RowBound
public import GraphMatching.Contraction
public import GraphMatching.Transport
public import GraphMatching.Tree
public import GraphMatching.Reduction
public import GraphMatching.Konig
public import GraphMatching.Graph
public import GraphMatching.Examples
public import GraphMatching.DoubleExp
public import GraphMatching.Measure
public import GraphMatching.Kolmogorov
public import GraphMatching.AutBridge
public import GraphMatching.Probability
