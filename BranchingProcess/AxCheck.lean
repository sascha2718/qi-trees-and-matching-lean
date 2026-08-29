/-
Axiom check for `BranchingProcess`. Every endpoint below must report
`propext`, `Classical.choice`, `Quot.sound` or a subset of them; anything else
means an axiom has crept in.

The groups follow the module order of the library root.
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

-- the ambient N-ary tree: the metric of `sec:words`
#print axioms BranchingProcess.treeDist_add
#print axioms BranchingProcess.treeDist_comm
#print axioms BranchingProcess.treeDist_eq_zero_iff
#print axioms BranchingProcess.treeDist_triangle
#print axioms BranchingProcess.treeDist_of_prefix
#print axioms BranchingProcess.treeDist_append_left
#print axioms BranchingProcess.treeDist_of_mem_children

-- subtrees as prefix-closed sets of words
#print axioms BranchingProcess.Subtree.mem_of_prefix
#print axioms BranchingProcess.Subtree.nil_mem
#print axioms BranchingProcess.Subtree.wedge_mem
#print axioms BranchingProcess.Subtree.mem_subAt
#print axioms BranchingProcess.Subtree.append_mem_of_prefix

-- offspring laws: the generating function of `sec:gw-trees`
#print axioms BranchingProcess.Offspring.gen_one
#print axioms BranchingProcess.Offspring.gen_le_one
#print axioms BranchingProcess.Offspring.gen_mono
#print axioms BranchingProcess.Offspring.hasDerivAt_gen
#print axioms BranchingProcess.Offspring.genDeriv_one

-- the extinction probability as the least fixed point
#print axioms BranchingProcess.Offspring.extinction_mem
#print axioms BranchingProcess.Offspring.gen_extinction
#print axioms BranchingProcess.Offspring.extinction_le_of_fixed
#print axioms BranchingProcess.Offspring.extinction_eq_zero_iff
#print axioms BranchingProcess.Offspring.extinction_pos
#print axioms BranchingProcess.Offspring.extinction_lt_one_of_supercritical

-- the sample tree cut out by a field of offspring counts
#print axioms BranchingProcess.mem_sample_append_singleton
#print axioms BranchingProcess.append_mem_sample_iff
#print axioms BranchingProcess.subAt_sample
#print axioms BranchingProcess.coe_sample
#print axioms BranchingProcess.finite_sample_of_forall_finite
#print axioms BranchingProcess.exists_infinite_child_of_infinite

-- survival, the skeleton, and the rays it carries
#print axioms BranchingProcess.nil_mem_skeleton_iff
#print axioms BranchingProcess.exists_child_mem_skeleton
#print axioms BranchingProcess.treeDist_of_chain
#print axioms BranchingProcess.exists_skeleton_ray
#print axioms BranchingProcess.exists_isometric_skeleton_ray

-- the law of the sample: the extinction probability is the probability of extinction
#print axioms BranchingProcess.Offspring.toPMF
#print axioms BranchingProcess.measurableSet_mem_sample
#print axioms BranchingProcess.measurableSet_survives
#print axioms BranchingProcess.map_split
#print axioms BranchingProcess.sampleMeasure_noLevel
#print axioms BranchingProcess.sampleMeasure_not_survives
#print axioms BranchingProcess.sampleMeasure_survives
#print axioms BranchingProcess.gen_extinctionProb

-- the i.i.d. coordinate field, and the Bernoulli instance the chain half needs
#print axioms BranchingProcess.coord_iIndepFun
#print axioms BranchingProcess.map_coord
#print axioms BranchingProcess.coord_law
#print axioms BranchingProcess.bernoulliField_iIndepFun
#print axioms BranchingProcess.bernoulliField_apply_true
#print axioms BranchingProcess.exists_bernoulli_field

-- tree coarse geometry: the two separations of `gw_classes_simple.tex`
#print axioms BranchingProcess.between_of_mem_support
#print axioms BranchingProcess.exists_between_dist_le
#print axioms BranchingProcess.IsLine.exists_far
#print axioms BranchingProcess.rayGraph_isTree
#print axioms BranchingProcess.not_quasiIsometric_of_hair_of_line
#print axioms BranchingProcess.not_quasiIsometric_rayGraph

-- the conditioned law, and the Harris transform at the root
#print axioms BranchingProcess.survivalMeasure_survives
#print axioms BranchingProcess.measurable_skeletonDegree
#print axioms BranchingProcess.sampleMeasure_root_survivors
#print axioms BranchingProcess.sampleMeasure_root_skeletonDegree
#print axioms BranchingProcess.Offspring.surviveWeight_zero
#print axioms BranchingProcess.sampleMeasure_skeletonDegree
#print axioms BranchingProcess.survivalMeasure_skeletonDegree
#print axioms BranchingProcess.bushMeasure_root

-- the law of a tree, and the skeleton
#print axioms BranchingProcess.measurable_sample
#print axioms BranchingProcess.treeLaw
#print axioms BranchingProcess.Offspring.reduced
#print axioms BranchingProcess.measurable_skelField
#print axioms BranchingProcess.measurable_skelTree
#print axioms BranchingProcess.survivalMeasure_bushAt
#print axioms BranchingProcess.survivalMeasure_skelSub
#print axioms BranchingProcess.survivalMeasure_mem_skelTree
#print axioms BranchingProcess.survivalMeasure_skelField
#print axioms BranchingProcess.sampleMeasure_mem_sample
#print axioms BranchingProcess.skeletonTreeLaw_mem_eq_treeLaw
#print axioms BranchingProcess.rankOf_orderEmbOfFin
#print axioms BranchingProcess.prod_rankOf
#print axioms BranchingProcess.survivalMeasure_skeletonDegree_bushes
#print axioms BranchingProcess.survivalMeasure_bushes
#print axioms BranchingProcess.survivalMeasure_subset_skelTree
#print axioms BranchingProcess.generateFrom_containmentSets
#print axioms BranchingProcess.skeletonTreeLaw_eq_treeLaw
#print axioms BranchingProcess.Offspring.conjugate
#print axioms BranchingProcess.bushMeasure_dying
#print axioms BranchingProcess.bushTreeLaw_eq_treeLaw

-- the joint box: surviving and dying children constrained at once
#print axioms BranchingProcess.sampleMeasure_root_joint
#print axioms BranchingProcess.survivalMeasure_root_one_survivor

-- the joint Harris decomposition: conditionally on the skeleton, the
-- decorations are independent conjugate samples
#print axioms BranchingProcess.survivalMeasure_root_decorated
#print axioms BranchingProcess.survivalMeasure_decorations
#print axioms BranchingProcess.survivalMeasure_decorations_treeLaw
#print axioms BranchingProcess.survivalMeasure_skelField_pattern

-- the point mass of a finite tree and the progeny exponential moment
#print axioms BranchingProcess.sampleMeasure_agreeOn
#print axioms BranchingProcess.ofReal_pow_le_bushMeasure_sample_eq
#print axioms BranchingProcess.Offspring.exists_progeny_fixedPoint
#print axioms BranchingProcess.exists_exponential_moment
#print axioms BranchingProcess.exists_exponential_moment_bushMeasure
