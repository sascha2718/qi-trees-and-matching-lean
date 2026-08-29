import GraphMatching.Graph
import GraphMatching.Examples
import GraphMatching.DoubleExp
import GraphMatching.Kolmogorov
import GraphMatching.AutBridge
/-!
Axiom check for the i.i.d. matching library, the counterpart of
`GraphMarkovMatching/AxCheck.lean`.  Every headline result of
`graph_matching_selfcontained.tex` must depend on `propext`,
`Classical.choice`, `Quot.sound` and nothing else.  Extend this file when a
major result is added.
-/

-- `thm:matching`, the two matching bounds and the infinite tree
#print axioms GraphMatching.graph_leaf_matching_bound
#print axioms GraphMatching.graph_full_matching_bound
#print axioms GraphMatching.exists_infinite_tree_matching

-- `sec:setup` and `thm:matching` over graph automorphisms: the swap group is the
-- automorphism group of the rooted binary tree, at every finite height and on the
-- infinite tree
#print axioms GraphMatching.fullSim_iff_graphAut
#print axioms GraphMatching.infMatch_iff_graphAut
#print axioms GraphMatching.exists_infinite_tree_matching_graphAut

-- `thm:dominance`, local dominance
#print axioms GraphMatching.etaG_le_localDominance

-- the statements the paper carries at a general exponent
#print axioms GraphMatching.le_phiA
#print axioms GraphMatching.rpow_neg_alpha_leA
#print axioms GraphMatching.chordA
#print axioms GraphMatching.le_LA
#print axioms GraphMatching.le_KA
#print axioms GraphMatching.PhiA_prodPMF_le
#print axioms GraphMatching.etaGA_eq_PhiA
#print axioms GraphMatching.etaGA_le_localDominance
#print axioms GraphMatching.starA_bound

-- `thm:reduction`, the abstract reduction and its measure layer
#print axioms GraphMatching.leaf_matching_bound
#print axioms GraphMatching.full_matching_bound
#print axioms GraphMatching.infinite_tree_matching_prob_of_law

-- `thm:contraction` and `thm:product`, the two analytic engines
#print axioms GraphMatching.Phi_square_le
#print axioms GraphMatching.Phi_square_le_of_small
#print axioms GraphMatching.Phi_prodPMF_le

-- `sec:integer` and the two examples
#print axioms GraphMatching.path_leaf_matching_bound
#print axioms GraphMatching.path_full_matching_bound
#print axioms GraphMatching.star_bound
#print axioms GraphMatching.double_exp_matching

-- `thm:reduction` at a general exponent: under its hypotheses `OneStepA`/`ProdStepA`,
-- and with `thm:contraction`/`thm:product` discharging them at `A_α`, `B_α`, `2α`
#print axioms GraphMatching.leaf_matching_boundA_of
#print axioms GraphMatching.full_matching_boundA_of
#print axioms GraphMatching.PhiLeafA_le
#print axioms GraphMatching.PhiFullA_le
#print axioms GraphMatching.leaf_matching_boundA
#print axioms GraphMatching.full_matching_boundA
#print axioms GraphMatching.rowBoundA
#print axioms GraphMatching.Phi_square_leA
#print axioms GraphMatching.Phi_square_le_of_smallA
