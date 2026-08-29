import ChainClasses.Encoding
import ChainClasses.Labelling
import ChainClasses.Isometry
import ChainClasses.Transfer
import ChainClasses.Geometric
import ChainClasses.Quantise
import ChainClasses.Eta
import ChainClasses.Coupling
import ChainClasses.MarkedQI
import ChainClasses.ShapeMass
import ChainClasses.ShapeEta
import ChainClasses.ShapeCoupling
import ChainClasses.GluedTransfer
import ChainClasses.Shape
import ChainClasses.Harris
import ChainClasses.Dilution
import ChainClasses.Hairy
import ChainClasses.GeneralHarris
import ChainClasses.GeneralShape
import ChainClasses.SplitJoint
import ChainClasses.Relabel
import ChainClasses.GeneralDilution
import ChainClasses.SemigroupMerge
import ChainClasses.ChainRegime
import ChainClasses.RenewalAlignment
import ChainClasses.GWInstance
import ChainClasses.TwoValue
import ChainClasses.Converse
import ChainClasses.CrossLaw
import ChainClasses.ShapeMetric
import ChainClasses.ShapeShrink
import ChainClasses.Contraction
import ChainClasses.ContractTree
import ChainClasses.ContractAddr
import ChainClasses.Assembly
import ChainClasses.Binarise
import ChainClasses.ShapeDecomposition
import ChainClasses.ShapeLaw
import ChainClasses.ShapeRootLaw
import ChainClasses.ShapeSplitLaw
import ChainClasses.ShapeIID
import ChainClasses.AssemblyRelabel
import ChainClasses.HairyUniversality
import ChainClasses.ShapeLabelLaw
import ChainClasses.ShapeCouplingSelf
import ChainClasses.ShapeMassPoint
import ChainClasses.ShapeMassBush
import ChainClasses.ShapeEtaBlock
import ChainClasses.ShapeSizeTail
import ChainClasses.ShapeEtaSelf
import ChainClasses.ShapeCouplingCross
import ChainClasses.ShapeCouplingBuild
import ChainClasses.ShapePairEta
import ChainClasses.MatchedPresentation
import ChainClasses.ChainCross
import ChainClasses.HairyCross
import ChainClasses.WordGraph
import ChainClasses.ThreeRays
import ChainClasses.GeneralShapeIID
import ChainClasses.GeneralShapeMetric
import ChainClasses.GeneralShapeShrink
import ChainClasses.ClusterIID
import ChainClasses.GeneralCoupling
import ChainClasses.BlobLaw
import ChainClasses.GeneralShrinkScale
import ChainClasses.GeneralAssembly
import ChainClasses.GeneralCascade
import ChainClasses.GeneralShapeCoupling
import ChainClasses.GeneralShapeEta
import ChainClasses.GeneralLabelField
import ChainClasses.GeneralObstructions
import ChainClasses.ChainLabelField
import ChainClasses.MatchedRule
import ChainClasses.EngineBridge
import ChainClasses.BAssembly
import ChainClasses.FullTree
import ChainClasses.ChainEngineBridge
import ChainClasses.HairyGeneral
import ChainClasses.BlobAssembly
import ChainClasses.ChainGeneral
import ChainClasses.StarSeparation
import ChainClasses.Classification
/-!
Axiom check for the chain-classes library, the counterpart of
`GraphMatching/AxCheck.lean` and `GraphMarkovMatching/AxCheck.lean`.  Every headline result in
the simple and complete conditioned-infinite classifications at finite support must depend on
`propext`, `Classical.choice`, `Quot.sound` and nothing else.  Extend this file when a major
result is added.
-/

-- Public classification endpoints.  See `ChainClasses.Classification`.
#print axioms ChainClasses.simple_classification_ae_iff
#print axioms ChainClasses.simple_classification
#print axioms ChainClasses.simple_same_class_ae
#print axioms ChainClasses.simple_different_class_ae
#print axioms ChainClasses.simple_not_ray_ae
#print axioms ChainClasses.classification_ae_iff
#print axioms ChainClasses.same_class_ae
#print axioms ChainClasses.different_class_ae
#print axioms ChainClasses.classification_not_ray_ae
#print axioms ChainClasses.offspring_classification_ae_iff
#print axioms ChainClasses.offspring_classification_not_ray_ae

-- `thm:chains`: the chain partition of the tree
#print axioms ChainClasses.ray_chain_disjoint
#print axioms ChainClasses.tree_eq_chains
#print axioms ChainClasses.chain_unique
#print axioms ChainClasses.chain_level_unique

-- `thm:level`: level comparison
#print axioms ChainClasses.level_close_comparable

-- `thm:chain-classes`, deterministic clauses
#print axioms ChainClasses.level_eq_iff
#print axioms ChainClasses.class_ratio

-- `thm:quantised-law` and the class sum of `eq:qk`
#print axioms ChainClasses.qF_zero
#print axioms ChainClasses.qF_le
#print axioms ChainClasses.class_sum
#print axioms ChainClasses.qF_tsum

-- `thm:eta-bound`: the potential estimate and the matching instance
#print axioms ChainClasses.quantised_eta_le
#print axioms ChainClasses.quantised_matching

-- the associated tree: normal-form uniqueness over an abstract labelling
#print axioms ChainClasses.assoc_rep_unique

-- `thm:isometry`: automorphisms act by isometries of the associated trees
#print axioms ChainClasses.isometry_of_relabel

-- `thm:transfer`: comparable labellings give quasi-isometric associated trees
#print axioms ChainClasses.transfer

-- `thm:geometric`: the label law and independence
#print axioms ChainClasses.chains_ae
#print axioms ChainClasses.exploration
#print axioms ChainClasses.label_prod
#print axioms ChainClasses.label_marginal
#print axioms ChainClasses.label_iIndepFun

-- `thm:chain-classes`, independence of the quantised labels
#print axioms ChainClasses.quantised_label_iIndepFun

-- `thm:geometric` on a constructed space: the offspring field of `sec:encoding`
-- built in `BranchingProcess`, discharging the hypotheses of the five above
#print axioms ChainClasses.chainMeasure_chains_ae
#print axioms ChainClasses.chainMeasure_exploration
#print axioms ChainClasses.chainMeasure_label_marginal
#print axioms ChainClasses.chainMeasure_label_iIndepFun
#print axioms ChainClasses.chainMeasure_quantised_label_iIndepFun
#print axioms ChainClasses.exists_chain_field

-- `thm:twovalue`: the rate `eq:rate` and the almost sure statement, on the
-- constructed space, for the trees encoded by the labels and for the samples
#print axioms ChainClasses.matching_prob_ge
#print axioms ChainClasses.qi_of_matching
#print axioms ChainClasses.twovalue_rate
#print axioms ChainClasses.twovalue_ae
#print axioms ChainClasses.twoSampleMeasure_chains_ae
#print axioms ChainClasses.inTree_eq_inAssoc
#print axioms ChainClasses.twovalue_rate_tree
#print axioms ChainClasses.twovalue_ae_tree

-- the metric on shape realisations, and `thm:shape-connected` for real shapes
#print axioms ChainClasses.Tri.instMetricSpaceVert
#print axioms ChainClasses.Tri.dist_eq_one_iff_adj
#print axioms ChainClasses.dist_entry_exit
#print axioms ChainClasses.Tri.exists_shrinks_del
#print axioms ChainClasses.exists_markedQI_shrink
#print axioms ChainClasses.size_repIdx_le
#print axioms ChainClasses.netLink_connected_shapeFamily

-- `thm:cross-law`: the same assembly across two chain laws
#print axioms ChainClasses.markedMeasure_class_iIndepFun
#print axioms ChainClasses.cross_matching_prob_ge
#print axioms ChainClasses.cross_comparable
#print axioms ChainClasses.qi_of_cross_matching
#print axioms ChainClasses.crosslaw_rate
#print axioms ChainClasses.crosslaw_ae
#print axioms ChainClasses.crosslaw_rate_tree
#print axioms ChainClasses.crosslaw_ae_tree

-- `thm:bottleneck` and the binary-tree half of `thm:converse`
#print axioms ChainClasses.not_isQIWith_binary_of_thinBalls
#print axioms ChainClasses.chainMeasure_labels_unbounded
#print axioms ChainClasses.assoc_ball_subset_chain
#print axioms ChainClasses.hasThinBalls_assoc
#print axioms ChainClasses.converse_binary_ae

-- `thm:shape-eta`, the collapse of a shape of small diameter
#print axioms ChainClasses.markedQI_of_subsingleton
#print axioms ChainClasses.Tri.treeDist_lt_size
#print axioms ChainClasses.markedQI_collapse
#print axioms ChainClasses.repIdx_shapeFamily_eq_zero_of_size_le

-- `thm:shape-shrink`(i), the support fix
#print axioms ChainClasses.supported_fix
#print axioms ChainClasses.size_fix_le
#print axioms ChainClasses.fix_eq_self
#print axioms ChainClasses.markedQI_shape_fix
#print axioms ChainClasses.markedQI_two_shape_fix

-- `thm:dilution`, the greedy contraction as a marked quasi-isometry
#print axioms ChainClasses.Tri.length_sub_length_part_le
#print axioms ChainClasses.Tri.part_append_singleton
#print axioms ChainClasses.partGraph_connected
#print axioms ChainClasses.dist_contract_le
#print axioms ChainClasses.treeDist_le_contract
#print axioms ChainClasses.markedQI_contract
#print axioms ChainClasses.markedQI_contract_shape
#print axioms ChainClasses.Tri.size_contractTree_le_div
#print axioms ChainClasses.Tri.mem_partList_iff
#print axioms ChainClasses.Tri.contractPair_spec
#print axioms ChainClasses.card_partVert
#print axioms ChainClasses.dilution_count_shape

-- `thm:glued-transfer`: the assembly as a metric space and the gluing
#print axioms ChainClasses.Assembly.dist_anc
#print axioms ChainClasses.Assembly.dist_div
#print axioms ChainClasses.Assembly.dist_eq_one_iff_adj
#print axioms ChainClasses.Assembly.glued_transfer

-- `thm:shape-shrink`(ii): binarisation, the neck construction, the composition
#print axioms ChainClasses.Tri.rawSize_le
#print axioms ChainClasses.Tri.length_rootForest_le_two_mul
#print axioms ChainClasses.Tri.size_binTree_le_div
#print axioms ChainClasses.Tri.size_neckShape_le
#print axioms ChainClasses.markedQI_neck
#print axioms ChainClasses.shrinkScale_sq_le
#print axioms ChainClasses.Tri.length_childList_le_four_mul
#print axioms ChainClasses.Tri.decode_binAddr
#print axioms ChainClasses.Tri.treeDist_binAddr_le_dist
#print axioms ChainClasses.Tri.dist_le_treeDist_binAddr
#print axioms ChainClasses.Tri.size_binOf_le
#print axioms ChainClasses.binarisesAt
#print axioms ChainClasses.markedQI_shape_shrink
#print axioms ChainClasses.markedQI_shape_shrink_of_le

-- the bridge to the graph setting of `BranchingProcess.Geometry`
#print axioms ChainClasses.wordGraph_dist
#print axioms ChainClasses.wordGraph_connected
#print axioms ChainClasses.wordGraph_isBridge
#print axioms ChainClasses.wordGraph_isTree
#print axioms ChainClasses.isQIWith_wordGraph
#print axioms ChainClasses.isQIWith_of_wordGraph
#print axioms ChainClasses.not_quasiIsometric_of_not_isQIWith

-- `thm:three-rays` in the sample tree, and `thm:converse` in full
#print axioms ChainClasses.isRay_of
#print axioms ChainClasses.rayWord_ne
#print axioms ChainClasses.not_quasiIsometric_rayGraph_of_splits
#print axioms ChainClasses.not_quasiIsometric_rayGraph_inTree
#print axioms ChainClasses.converse_ae

-- `thm:chain-coupling`: the classes, the law identity, and the cut-point ratio
#print axioms ChainClasses.ellQ_endpoint
#print axioms ChainClasses.ellQ_sandwich_upper
#print axioms ChainClasses.coupling_law
#print axioms ChainClasses.DQ_ratio

-- `thm:shape-net`, abstract form: the net calculus of marked quasi-isometries
#print axioms ChainClasses.markedQI_comp
#print axioms ChainClasses.markedQI_symm
#print axioms ChainClasses.repIdx_of_netMem
#print axioms ChainClasses.markedQI_of_repIdx_eq
#print axioms ChainClasses.markedQI_of_repIdx_adjacent

-- `thm:shape-connected`: the descent on the size and its two shape-level inputs
#print axioms ChainClasses.netAdj_reach_zero
#print axioms ChainClasses.netLink_connected
#print axioms ChainClasses.Shape.exists_shrink
#print axioms ChainClasses.Shape.eq_of_size_le_one

-- `thm:shape-mass`: the point-mass bound and the exponential tail
#print axioms ChainClasses.shape_mass_point
#print axioms ChainClasses.chernoff_tail
#print axioms ChainClasses.shape_mass_tail

-- `thm:shape-eta`: the one-site weights, the geometric sum, and the assembly
#print axioms ChainClasses.wgt_le_of_half
#print axioms ChainClasses.wgt_le_of_exp
#print axioms ChainClasses.wgt_le_of_half_exp
#print axioms ChainClasses.eta_tail_sum
#print axioms ChainClasses.shape_eta_le
#print axioms ChainClasses.shape_eta_final

-- `thm:shape-coupling`: the capacity bound `eq:capacity` and the cascade
#print axioms ChainClasses.capacity_small
#print axioms ChainClasses.capacity_large
#print axioms ChainClasses.IsCascade.halving
#print axioms ChainClasses.IsCascade.half_le_cascadeOut
#print axioms ChainClasses.IsCascade.cascadeOut_le
#print axioms ChainClasses.IsCascade.cascadeIn_eq
#print axioms ChainClasses.IsCascade.cascadeOut_add_cascadeIn
#print axioms ChainClasses.IsCascade.cascadeIn_le_half

-- `thm:glued-transfer`: the neck bounds and the termwise comparison
#print axioms ChainClasses.neck_le_of_markedQI
#print axioms ChainClasses.neck_bounds
#print axioms ChainClasses.neck_sum_bounds
#print axioms ChainClasses.glued_dist_bounds
#print axioms ChainClasses.glued_dist_same

-- `thm:harris` and the shape law of `thm:shape-iid`, the arithmetic half
#print axioms ChainClasses.IsHairy.harris_quadratic
#print axioms ChainClasses.IsHairy.extinction_fixed_point
#print axioms ChainClasses.IsHairy.skeleton_chain_regime
#print axioms ChainClasses.IsHairy.split_prob
#print axioms ChainClasses.IsHairy.neck_prob
#print axioms ChainClasses.IsHairy.survival_decomposition
#print axioms ChainClasses.IsHairy.conjugate_tilt
#print axioms ChainClasses.IsHairy.conjugate_subcritical
#print axioms ChainClasses.IsHairy.bush_prob
#print axioms ChainClasses.IsHairy.neck_law_tsum
#print axioms ChainClasses.IsHairy.shape_factors_mem

-- `def:shape`: shapes, their realisations and their size
#print axioms ChainClasses.Tri.code_append_inj
#print axioms ChainClasses.Shape.size_eq

-- `thm:dilution`: the greedy cut, the depth-first code, the count, the scale
#print axioms ChainClasses.Tri.remSize_lt
#print axioms ChainClasses.Tri.maxPart_le
#print axioms ChainClasses.Tri.cutCount_le_div
#print axioms ChainClasses.RTree.code_length
#print axioms ChainClasses.RTree.code_append_inj
#print axioms ChainClasses.RTree.dilution_count
#print axioms ChainClasses.cube_bound
#print axioms ChainClasses.inv_le_nine_rpow

-- `rem:coupling-sharp` and the constants and limit of `thm:hairy`
#print axioms ChainClasses.dist_le_of_markedQI_subsingleton
#print axioms ChainClasses.glued_scale
#print axioms ChainClasses.hairy_rate_to_one

-- `thm:relabel` of the general document: the comparability composition
#print axioms ChainClasses.markedQI_relabel
#print axioms ChainClasses.relabel_scale

-- `thm:harris-general`: the Harris-Sevastyanov transform at bounded support
#print axioms ChainClasses.hasDerivAt_genFun
#print axioms ChainClasses.transform_expansion
#print axioms ChainClasses.tilde_sum
#print axioms ChainClasses.tilde_one
#print axioms ChainClasses.reduced_sum
#print axioms ChainClasses.geometric_law_tsum
#print axioms ChainClasses.conjugate_sum_general
#print axioms ChainClasses.conjugate_mean_general
#print axioms ChainClasses.extinction_ge
#print axioms ChainClasses.genDeriv_pos
#print axioms ChainClasses.tilde_hairy
#print axioms ChainClasses.reduced_hairy

-- the hairy regime has full reduced support, so its branching semigroup is `ℕ₀`
#print axioms ChainClasses.surviveCoeff_pos
#print axioms ChainClasses.tilde_pos
#print axioms ChainClasses.reducedLaw_pos
#print axioms ChainClasses.branching_semigroup_eq_top

-- `def:shape-general`: shapes at general arity
#print axioms ChainClasses.GShape.size_eq
#print axioms ChainClasses.GShape.realise_degLe

-- `thm:split-joint`: the joint law of shape and arity is not a product
#print axioms ChainClasses.splitJoint_not_product

-- `thm:mass-uniform`: the mixture and the bouquet
#print axioms ChainClasses.mixture_moment_le
#print axioms ChainClasses.mixture_point_lower
#print axioms ChainClasses.mass_point_general
#print axioms ChainClasses.conv_moment

-- `thm:relabel` (i) and `thm:product-form`: the label law and the product
#print axioms ChainClasses.relabel_law
#print axioms ChainClasses.product_of_constant_conditional

-- `it:general-dilution`: the greedy cut at arity `b`
#print axioms ChainClasses.RTree.remSize_lt
#print axioms ChainClasses.RTree.maxPart_le
#print axioms ChainClasses.RTree.cutCount_le_div
#print axioms ChainClasses.RTree.part_le_mul

-- `thm:merge` and `def:branching-semigroup`
#print axioms ChainClasses.RTree.merge_arity
#print axioms ChainClasses.RTree.merge_size
#print axioms ChainClasses.merge_step
#print axioms ChainClasses.mem_of_coprime
#print axioms ChainClasses.exists_consecutive_of_gcd_one
#print axioms ChainClasses.semigroup_cofinite
#print axioms ChainClasses.semigroup_threshold

-- `it:general-hairy`: the rate, the gluing scale, and the cascade depth
#print axioms ChainClasses.general_rate_to_one
#print axioms ChainClasses.relabel_glued_scale
#print axioms ChainClasses.cascade_depth

-- `sec:general-chain`: the chain regime at general support
-- `thm:chain-independence`: the joint law factorises
#print axioms ChainClasses.chain_joint_factor
#print axioms ChainClasses.chain_reduced_sum

-- `thm:cluster-law`: the shifted convolution and the presented arity law
#print axioms ChainClasses.shiftConv_summable
#print axioms ChainClasses.shiftConv_tsum
#print axioms ChainClasses.clusterLaw_nonneg
#print axioms ChainClasses.clusterLaw_tsum
#print axioms ChainClasses.clusterLaw_range

-- `thm:reachable-arity` and `thm:cluster-flat`
#print axioms ChainClasses.cluster_shift_add
#print axioms ChainClasses.cluster_arity_mem
#print axioms ChainClasses.markedQI_of_collapse

-- `thm:blob-law`: convolution powers and their mixtures
#print axioms ChainClasses.convPow_nonneg
#print axioms ChainClasses.convPow_summable
#print axioms ChainClasses.convPow_tsum
#print axioms ChainClasses.mixPow_tsum

-- `thm:least-shift`: the least shift lies in every generating set
#print axioms ChainClasses.exists_generator_le
#print axioms ChainClasses.min_mem_of_generates

-- `rem:fixed-levels`: complete blocks of fixed depth cannot match the arities
#print axioms ChainClasses.three_pow_ne_five_pow

-- `ex:chain-cross`: the guiding example
#print axioms ChainClasses.shiftConv_delta
#print axioms ChainClasses.clusterLaw_two_point
#print axioms ChainClasses.initial_renewal_lag_mem_window
#print axioms ChainClasses.renewalWordRun_eq_zero
#print axioms ChainClasses.renewalLagStep_mem_window
#print axioms ChainClasses.renewalLagStep_mem_states
#print axioms ChainClasses.renewalPhaseStep_val
#print axioms ChainClasses.common_renewal_completion
#print axioms ChainClasses.common_renewal_run
#print axioms ChainClasses.generators_mutually_representable
#print axioms ChainClasses.finite_generators_uniformly_representable
#print axioms ChainClasses.common_core_exception_words
#print axioms ChainClasses.finite_common_renewal_completions
#print axioms ChainClasses.geometric_decay_of_block_contraction
#print axioms ChainClasses.no_screen_invariant_of_supercritical_gain
#print axioms ChainClasses.geometric_killing_does_not_control_weighted_screen
#print axioms ChainClasses.closure_two_four_eq_two_six

-- `thm:shape-iid`: the shape field and the isometry with the assembly
#print axioms ChainClasses.transWith_treeDist
#print axioms ChainClasses.isAddr_bushTri
#print axioms ChainClasses.Assembly.exists_code_concat_iff
#print axioms ChainClasses.transSample_code_spec
#print axioms ChainClasses.assembly_isometric_sample
#print axioms ChainClasses.fibreMeasurable_shapeAt
#print axioms ChainClasses.measurableSet_shapeAt_eq
#print axioms ChainClasses.ae_isHairySample
#print axioms ChainClasses.survivalMeasure_noSplit
#print axioms ChainClasses.ae_splits
#print axioms ChainClasses.ae_isHairySample_of_pos
#print axioms ChainClasses.ae_assembly_isometric_sample
#print axioms ChainClasses.survivalMeasure_neckLen
#print axioms ChainClasses.survivalMeasure_neck_step
#print axioms ChainClasses.survivalMeasure_shapeAt_nil
#print axioms ChainClasses.survivalMeasure_shapeAt_nil_split
#print axioms ChainClasses.shapeAt_cons
#print axioms ChainClasses.survivalMeasure_shapes
#print axioms ChainClasses.shape_decomposition

-- `thm:hairy`: the assembly relabelling and the hairy universality rates
#print axioms ChainClasses.Assembly.dist_relabel
#print axioms ChainClasses.qi_of_shape_matching
#print axioms ChainClasses.hairy_matching_prob_ge
#print axioms ChainClasses.hairy_rate
#print axioms ChainClasses.hairy_rate_tree
#print axioms ChainClasses.hairy_rate_tree_scale
#print axioms ChainClasses.hairy_ae_tree

-- the shape law's total mass, the label law, and the net coupling
#print axioms ChainClasses.tsum_shapeMass
#print axioms ChainClasses.survivalMeasure_shapeAt
#print axioms ChainClasses.tsum_labMass
#print axioms ChainClasses.hairyMeasure_shapeLab_prod
#print axioms ChainClasses.isNetLabel_netLab
#print axioms ChainClasses.markedQI_of_compat
#print axioms ChainClasses.hairy_rate_net_tree_self

-- `thm:dilution` closed: the rose-tree metric and the comparability step
#print axioms ChainClasses.RTree.mem_addrList_iff
#print axioms ChainClasses.RTree.rtreeGraph_connected
#print axioms ChainClasses.part_dropLast_mem_pairList
#print axioms ChainClasses.dist_toVert
#print axioms ChainClasses.isMarkedIsom_toVert
#print axioms ChainClasses.markedQI_of_shapeContractPair_eq
#print axioms ChainClasses.dilution
#print axioms ChainClasses.dilution_netMem

-- the shape-valued label, and the point mass of the shape law
#print axioms ChainClasses.markedQI_of_compat_shapeLabel
#print axioms ChainClasses.hairy_rate_shape_self
#print axioms ChainClasses.hairy_rate_shape_tree_self
#print axioms ChainClasses.hairy_ae_shape_tree_self
#print axioms ChainClasses.ofReal_pow_size_le_shapeMass
#print axioms ChainClasses.shape_mass_point_survivalMeasure

-- the point mass and the size tail of a bush, at the concrete law
#print axioms ChainClasses.Tri.ext_isAddr
#print axioms ChainClasses.bushPointBound
#print axioms ChainClasses.ofReal_pow_size_le_shapeMass_of_weights
#print axioms ChainClasses.size_bushTri
#print axioms ChainClasses.conjugate_isSubcritical
#print axioms ChainClasses.summable_bushSizeMass_mgf
#print axioms ChainClasses.exists_bush_size_tail

-- the potential bound with a small block, and the regrouping by size
#print axioms ChainClasses.wgt_block_le
#print axioms ChainClasses.shape_eta_block_le
#print axioms ChainClasses.shape_eta_le_of_block
#print axioms ChainClasses.tsum_fiber_size
#print axioms ChainClasses.etaG_le_size
#print axioms ChainClasses.etaG_shape_le

-- the exponential moment and tail of the shape size
#print axioms ChainClasses.tsum_shapeMass_mul_pow
#print axioms ChainClasses.exists_shape_size_moment
#print axioms ChainClasses.survivalMeasure_shape_stat
#print axioms ChainClasses.exists_shape_size_tail
#print axioms ChainClasses.exists_fix_size_tail

-- `thm:hairy` unconditional in the one-law case
#print axioms ChainClasses.ofReal_pow_size_le_shapeMass_supported
#print axioms ChainClasses.exists_etaG_shapeNet_le
#print axioms ChainClasses.exists_etaG_shapeNet_small
#print axioms ChainClasses.hairy_rate_shape_tree
#print axioms ChainClasses.hairy_rate_shape_tree_exp
#print axioms ChainClasses.hairy_ae_shape_tree

-- the two-law hairy universality, over a shape coupling
#print axioms ChainClasses.markedQI_of_compat_pairLab
#print axioms ChainClasses.etaG_pairNet_le
#print axioms ChainClasses.hairy_rate_shape_tree_cross
#print axioms ChainClasses.hairy_ae_shape_tree_cross
#print axioms ChainClasses.hairy_ae_shape_tree_diag

-- the cascade coupling, and two-law `thm:hairy` with no hypotheses
#print axioms ChainClasses.isCascadeOn_cascMass
#print axioms ChainClasses.exists_capacity_shapePMF
#print axioms ChainClasses.exists_coupling_of_capacity
#print axioms ChainClasses.exists_isShapeCoupling
#print axioms ChainClasses.hairy_ae_shape_tree_two_law

-- the two-law `eq:hairy-rate` at the constants of the paper: the label graph at the
-- edge scale `27D⁴`, the comparison `972D⁴` of matched labels, the potential estimate
-- over the cascade coupling, and the rate `8·972²D⁸`
#print axioms ChainClasses.markedQI_of_compat_pairLabS
#print axioms ChainClasses.exists_isShapeCoupling_etaS
#print axioms ChainClasses.hairy_rate_two_law

-- `thm:matched-presentation`, the law level: the coupled and free automata,
-- the bulk symmetry, the renewal tail, and the four clause theorems
#print axioms ChainClasses.Matched.ideal_bulk_symm
#print axioms ChainClasses.Matched.alive_word_le
#print axioms ChainClasses.Matched.alive_le_pow
#print axioms ChainClasses.Matched.couple_ideal_close
#print axioms ChainClasses.Matched.exhaust_le_sq
#print axioms ChainClasses.Matched.matchedShift_sum_eq_one
#print axioms ChainClasses.Matched.matchedShift_pos_iff
#print axioms ChainClasses.Matched.matchedShift_floor
#print axioms ChainClasses.Matched.matchedShift_bulk_close
#print axioms ChainClasses.Matched.matchedShift_window

-- `thm:chain-cross` and `thm:hairy-cross`, the composite-pair and chart
-- arithmetic, and `thm:qi-transitive`
#print axioms ChainClasses.Matched.exists_core_pair
#print axioms ChainClasses.Matched.exists_chart
#print axioms ChainClasses.Matched.matched_core_charged
#print axioms ChainClasses.Matched.chainCross_qi_scale
#print axioms ChainClasses.hairyCross_chart
#print axioms ChainClasses.hairyCross_core_charged
#print axioms ChainClasses.hairyCross_pair_floor
#print axioms ChainClasses.QuasiIsometric.trans
#print axioms ChainClasses.pairQI_trans

-- `thm:regime-obstructions`\labelcref{it:obstr-hair}, hairs of unbounded depth
#print axioms ChainClasses.exists_componentCompl_cone
#print axioms ChainClasses.survivalMeasure_shapes_avoid
#print axioms ChainClasses.unbounded_hairs_ae
#print axioms ChainClasses.hairsInHairyRegime

-- `thm:trichotomy-simple`
#print axioms ChainClasses.scaleCondition_holds
#print axioms ChainClasses.nearLine_inTree
#print axioms ChainClasses.raysInHairyRegime
#print axioms ChainClasses.QuasiIsometric.symm
#print axioms ChainClasses.same_regime_ae
#print axioms ChainClasses.not_ray_ae
#print axioms ChainClasses.diff_regime_ae
#print axioms ChainClasses.trichotomy_simple
#print axioms ChainClasses.quasiIsometric_rayWord_rayGraph
#print axioms ChainClasses.ray_ray_ae
#print axioms ChainClasses.twovalue_ae_tree_family
#print axioms ChainClasses.exists_twovalue_rate_tree
#print axioms ChainClasses.forall_scale
#print axioms ChainClasses.transferR
#print axioms ChainClasses.qi_of_cross_matchingR
#print axioms ChainClasses.crosslaw_rate_treeR
#print axioms ChainClasses.exists_crosslaw_rate_tree

-- `thm:conditional-iid`: the general shape field with exit bouquets, the joint
-- product formula, the reduced-law arity field, and the conditional laws
#print axioms ChainClasses.fibreMeasurableG_gShapeAt
#print axioms ChainClasses.fibreMeasurableG_gArityAt
#print axioms ChainClasses.survivalMeasure_gShapeSplit
#print axioms ChainClasses.survivalMeasure_gShapes
#print axioms ChainClasses.survivalMeasure_gArities
#print axioms ChainClasses.skeletonWeight_pos
#print axioms ChainClasses.reducedWeight_pos
#print axioms ChainClasses.conditional_iid

-- `thm:cross-relabel`\labelcref{it:cross-relabel-qi} and `thm:shape-connected`
-- at general arity, over the metric realisation of general shapes
#print axioms ChainClasses.gSize_repIdx_le
#print axioms ChainClasses.crossRelabel_qi
#print axioms ChainClasses.crossRelabel_qi_compat
#print axioms ChainClasses.markedQI_gSpace_del
#print axioms ChainClasses.exists_markedQI_gShrink
#print axioms ChainClasses.netLink_connected_gShapeFamily

-- `it:general-dilution`: the contraction on the addresses of a rose tree and
-- `thm:dilution` at general arity, constants unchanged
#print axioms ChainClasses.RTree.length_sub_length_part_le
#print axioms ChainClasses.markedQI_gContract
#print axioms ChainClasses.RTree.size_gContractTree_le_div
#print axioms ChainClasses.markedQI_gContractTree
#print axioms ChainClasses.degLe_gContractTree
#print axioms ChainClasses.markedQI_of_gShapeContractPair_eq
#print axioms ChainClasses.gDilution
#print axioms ChainClasses.gDilution_netMem

-- the address metric of rose trees
#print axioms ChainClasses.RTree.rtreeGraph_dist
#print axioms ChainClasses.RTree.dist_vert_eq_addrDist

-- `thm:shape-shrink`\labelcref{it:shape-shrink} at general arity: the moves after
-- the contraction, the shrinking map, and the small-pair collapse
#print axioms ChainClasses.markedQI_lcrs
#print axioms ChainClasses.markedQI_gNeck
#print axioms ChainClasses.markedQI_gPad
#print axioms ChainClasses.chargedG_gPad
#print axioms ChainClasses.markedQI_gShrinkOf
#print axioms ChainClasses.markedQI_gCollapse
#print axioms ChainClasses.markedQI_gSmallPair
#print axioms ChainClasses.GShape.ChargedG.degLe
#print axioms ChainClasses.markedQI_gShrink
#print axioms ChainClasses.size_gShrink_le
#print axioms ChainClasses.chargedG_gShrink
#print axioms ChainClasses.gShrinkScale_le
#print axioms ChainClasses.markedQI_gShrink_of_le

-- `it:general-glued`: the assembly at general arity and `thm:glued-transfer` over it
#print axioms ChainClasses.GAssembly.dist_anc
#print axioms ChainClasses.GAssembly.dist_div
#print axioms ChainClasses.GAssembly.dist_eq_one_iff_adj
#print axioms ChainClasses.GAssembly.glued_transfer

-- `thm:merge`\labelcref{it:merge-split}: the cascade code and its quasi-isometry
#print axioms ChainClasses.le_treeDist_cascWord
#print axioms ChainClasses.treeDist_cascWord_le
#print axioms ChainClasses.wordGraphN_dist
#print axioms ChainClasses.cascade_isQIWith
#print axioms ChainClasses.cascade_isQIWith_clog

-- `thm:mass-uniform`, the tail clause: the size of a general shape has an exponential
-- tail under every conditional law and under the mixture, at one rate
#print axioms ChainClasses.conjugate_isSubcritical_general
#print axioms ChainClasses.tsum_bushMassR_mul_pow
#print axioms ChainClasses.tsum_gPairMass_mul_pow
#print axioms ChainClasses.exists_gPairMass_moment
#print axioms ChainClasses.exists_gShape_size_tail
#print axioms ChainClasses.exists_gCond_size_tail
#print axioms ChainClasses.exists_gMix_size_tail

-- the cascade at a general size constant and with two shrinkings
#print axioms ChainClasses.capacity_of_mass_boundsT_const
#print axioms ChainClasses.exists_couplingT_of_capacity₂
#print axioms ChainClasses.exists_gShapeCoupling_of_capacity₂
#print axioms ChainClasses.exists_gShapeCoupling_of_capacity₂'

-- `thm:relabel` and `thm:cross-relabel`, the couplings of the conditional laws with
-- the mixture, supported on `9D³`-comparable pairs
#print axioms ChainClasses.chargedG_gShrinkAt
#print axioms ChainClasses.markedQI_gShrinkAt
#print axioms ChainClasses.degLe_of_gPairMass_ne_zero
#print axioms ChainClasses.degLe_of_gCondPMF_ne_zero
#print axioms ChainClasses.degLe_of_gMixPMF_ne_zero
#print axioms ChainClasses.exists_gCapacity_cond_mix
#print axioms ChainClasses.exists_gShapeCoupling_cond_mix
#print axioms ChainClasses.exists_gShapeCoupling_relabel

-- `thm:relabel`\labelcref{it:relabel-eta}: the potential of the class law on the label
-- graph, and the mass of the class of the one-vertex shape
#print axioms ChainClasses.gShapeEnum_zero
#print axioms ChainClasses.gNetLab_eq_zero_of_size_le
#print axioms ChainClasses.compat_gNetGraph_of_markedQI
#print axioms ChainClasses.exp_le_gdeg_gNetGraph
#print axioms ChainClasses.gClassPMF_zero_ge
#print axioms ChainClasses.exists_etaG_gNetGraph_le
#print axioms ChainClasses.exists_etaG_gNetGraph_small

-- the uniform field and the conditional draw, and `thm:product-form`,
-- `thm:hairy-cross`\labelcref{it:hairy-cross-product}: the labelled reduced skeleton
#print axioms ChainClasses.uniformField_pattern
#print axioms ChainClasses.volume_drawBy_fibre
#print axioms ChainClasses.volume_condDraw_mem
#print axioms ChainClasses.prod_uniformField_pattern
#print axioms ChainClasses.labelMeasure_partner_pattern
#print axioms ChainClasses.labelMeasure_label_pattern
#print axioms ChainClasses.labelMeasure_label_marginal
#print axioms ChainClasses.measurable_gLab

-- `thm:regime-obstructions-general`: the four clauses almost surely on the constructed
-- space, and the graph-level separations they feed
#print axioms ChainClasses.wordGraphN_isTree
#print axioms ChainClasses.not_quasiIsometric_rayGraph_of_threeRaysN
#print axioms ChainClasses.not_quasiIsometric_of_hairsN_of_nearLineN
#print axioms ChainClasses.not_quasiIsometric_binary_of_thinBalls
#print axioms ChainClasses.not_quasiIsometric_of_thinBallsN_of_binary
#print axioms ChainClasses.threeRays_ae
#print axioms ChainClasses.nearLine_gSample_ae
#print axioms ChainClasses.unbounded_hairs_gSample_ae
#print axioms ChainClasses.thinBalls_gSample_ae

-- `thm:chain-product-form` and `thm:chain-cross`\labelcref{it:chain-cross-product}: the
-- presented labellings of the chain regime on the constructed space
#print axioms ChainClasses.bArityLaw_tsum
#print axioms ChainClasses.bArityLaw_stopRule
#print axioms ChainClasses.qF_zero_ge_half
#print axioms ChainClasses.blobMeasure_chainLab_pattern
#print axioms ChainClasses.blobMeasure_chainLab_marginal
#print axioms ChainClasses.chain_product_form
#print axioms ChainClasses.crossLab_pattern
#print axioms ChainClasses.crossLab_marginal

-- `thm:matched-presentation`\labelcref{it:matched-product}: the matched rule as a rule of
-- `def:blob`, its presented arity law identified with the automaton, and the clauses on
-- the constructed space
#print axioms ChainClasses.bRuleMass_eq_sum_traceSum
#print axioms ChainClasses.Matched.coinRuleMass_matchedRule
#print axioms ChainClasses.Matched.coinRuleMass_div_matchedRule
#print axioms ChainClasses.Matched.matched_iid
#print axioms ChainClasses.Matched.presentedShift_eq
#print axioms ChainClasses.Matched.presentedShift_sum_eq_one
#print axioms ChainClasses.Matched.presentedShift_pos_iff
#print axioms ChainClasses.Matched.presentedShift_floor
#print axioms ChainClasses.Matched.presentedShift_window
#print axioms ChainClasses.Matched.presentedShift_bulk_close

-- `thm:hairy-general`, the identification with the engine's process: the cascade encoding of
-- the labelled reduced skeleton into the binary tree, its law at every height, and the
-- matching probability of `thm:composite-matching` on two independent labelled samples
#print axioms ChainClasses.restrictLab_encLab
#print axioms ChainClasses.measurable_encLab
#print axioms ChainClasses.encLab_eq_iff
#print axioms ChainClasses.cT_eq_recMass
#print axioms ChainClasses.survivalMeasure_compat_bad_null
#print axioms ChainClasses.labelMeasure_map_encLab
#print axioms ChainClasses.etaG_compat_eq
#print axioms ChainClasses.twoLabelMeasure_map_encLab
#print axioms ChainClasses.exists_engine_match

-- `thm:hairy-general`, the deterministic core: the sample isometric to the assembly of its
-- shapes over the reduced skeleton, the `𝔹`-assembly over a cascade encoding, the
-- relabelling by an automorphism, and the quasi-isometry of two matched samples
#print axioms ChainClasses.gAssembly_isometric_sample
#print axioms ChainClasses.CascadeEnc.skelToB_isQIMap
#print axioms ChainClasses.GAssembly.dist_relabel
#print axioms ChainClasses.CascadeEnc.qi_of_bShape_matching
#print axioms ChainClasses.sample_qi_of_bShape_matching

-- `thm:bushy`: full trees of bounded valence are quasi-isometric to the binary tree, through
-- the cascade and the unary-run contraction; and regime (F) almost surely
#print axioms ChainClasses.splitEmbed_isQIWith
#print axioms ChainClasses.quasiIsometric_binary_of_splitsWithin
#print axioms ChainClasses.cascSet_splitsWithin
#print axioms ChainClasses.fullTree_quasiIsometric_binary
#print axioms ChainClasses.fullTree_gSample

-- `thm:chain-general`, the identification with the engine's process: the encoded presented
-- labellings have the engine's law at every height, and the alignment probability with the
-- budgeted constant, uniform in `D`
#print axioms ChainClasses.map_encLab_of_pattern
#print axioms ChainClasses.blobMeasure_map_encLab
#print axioms ChainClasses.coupledBlobMeasure_map_encLab
#print axioms ChainClasses.composite_matching_bound_budget
#print axioms ChainClasses.matchedArityPMF_support_floor
#print axioms ChainClasses.exists_chain_scale
#print axioms ChainClasses.exists_engine_match_chain
#print axioms ChainClasses.exists_engine_match_chain'

-- `thm:hairy-general`: the engine's encoding as a cascade encoding, the portrait read off the
-- engine's automorphism, the deterministic core, the rate, and universality in the bushy
-- regime almost surely, the general gap chained through intermediate laws
#print axioms ChainClasses.engineEnc
#print axioms ChainClasses.engineEnc_inClosure
#print axioms ChainClasses.exists_portrait_of_infMatchK
#print axioms ChainClasses.sample_qi_of_engine_match
#print axioms ChainClasses.ae_isGHairySample
#print axioms ChainClasses.ae_partner_comparable
#print axioms ChainClasses.hairy_general_rate
#print axioms ChainClasses.hairy_general_ae_small'
#print axioms ChainClasses.gSampleQI_trans
#print axioms ChainClasses.bridgeLaw_supercritical
#print axioms ChainClasses.hairy_general_ae

-- `thm:chain-general`, the deterministic core: the assembly of multi-port pieces, its glued
-- transfer, the flattening of `thm:matched-presentation`(v), the sample isometric to the
-- assembly of its presented blobs, and the quasi-isometry of two samples with matched blobs
#print axioms ChainClasses.PAssembly.dist_anc
#print axioms ChainClasses.PAssembly.dist_div
#print axioms ChainClasses.PAssembly.glue_isQIMap
#print axioms ChainClasses.isPortQI_collapse
#print axioms ChainClasses.blobAssembly_isometric_sample
#print axioms ChainClasses.blobPiece_isNeckPiece
#print axioms ChainClasses.blob_flat_glued
#print axioms ChainClasses.flatToG_isometry
#print axioms ChainClasses.sample_qi_of_blob_matching'
#print axioms ChainClasses.quasiIsometric_of_blob_matching

-- `thm:chain-general`: matched necks comparable, the deterministic core, the rate, and
-- universality within a chain class almost surely
#print axioms ChainClasses.flatG_markedQI
#print axioms ChainClasses.neck_ratio_of_compat
#print axioms ChainClasses.encLab_congr
#print axioms ChainClasses.sample_qi_of_chain_match
#print axioms ChainClasses.ae_isChainField
#print axioms ChainClasses.chain_general_rate
#print axioms ChainClasses.chain_general_ae_small
#print axioms ChainClasses.chain_general_ae
#print axioms ChainClasses.semigroup_cofinite_gcd

-- `thm:trichotomy`: the infinite classes encoded by a coarse regime and, in the chain case,
-- a semigroup, with the positive and negative statements and one separation hypothesis left
#print axioms ChainClasses.ray_gSample
#print axioms ChainClasses.gRay_gRay_ae
#print axioms ChainClasses.gFull_gFull_ae
#print axioms ChainClasses.gBushy_gBushy_ae
#print axioms ChainClasses.gChain_gChain_ae
#print axioms ChainClasses.gRay_gFull_ae
#print axioms ChainClasses.gRay_gChain_ae
#print axioms ChainClasses.gRay_gBushy_ae
#print axioms ChainClasses.gBushy_gFull_ae
#print axioms ChainClasses.gBushy_gChain_ae
#print axioms ChainClasses.gChain_gFull_ae
#print axioms ChainClasses.gChain_gChain_sep_ae
#print axioms ChainClasses.same_gRegime_ae
#print axioms ChainClasses.diff_gRegime_ae
#print axioms ChainClasses.not_ray_gRegime_ae
#print axioms ChainClasses.trichotomy_general
#print axioms ChainClasses.chainUniversality
#print axioms ChainClasses.same_gRegime_ae'
#print axioms ChainClasses.trichotomy_general'

-- `thm:chain-separation` and the complete classification with no hypothesis: the star lemma,
-- the sphere count, and the core argument of the separation
#print axioms ChainClasses.star_pair_no_qi
#print axioms ChainClasses.ae_pattern_anchors
#print axioms ChainClasses.chainSeparation_side
#print axioms ChainClasses.chainSeparation
#print axioms ChainClasses.gChain_gChain_sep_ae'
#print axioms ChainClasses.trichotomy
#print axioms ChainClasses.trichotomy_ae_iff
#print axioms ChainClasses.trichotomy_not_ray
#print axioms ChainClasses.offspringIsChain_iff
#print axioms ChainClasses.sameOffspringClass_iff
#print axioms ChainClasses.GRegime.ofExact_invariant_iff
#print axioms ChainClasses.trichotomy_exact_ae_iff
#print axioms ChainClasses.trichotomy_exact_not_ray

-- `thm:cluster-law`, the i.i.d. clause over the presented skeleton
#print axioms ChainClasses.survivalMeasure_missEvent
#print axioms ChainClasses.survivalMeasure_gArity_eq_one
#print axioms ChainClasses.cluster_root_coin_true
#print axioms ChainClasses.survivalMeasure_clusterC
#print axioms ChainClasses.bernoulliField_pattern
#print axioms ChainClasses.cluster_iid
#print axioms ChainClasses.clusterMass_eq_clusterLaw
#print axioms ChainClasses.cluster_iid_chain

-- `thm:mass-uniform`(point), `def:conditional-laws` as laws, the mixture of
-- `thm:conditional-explicit`, and the cascade coupling at general shapes
#print axioms ChainClasses.bushRTree_eq_of_sample_eq
#print axioms ChainClasses.ofReal_pow_le_bushMassR
#print axioms ChainClasses.tsum_gPairMass
#print axioms ChainClasses.gCondPMF
#print axioms ChainClasses.tsum_gMixMass
#print axioms ChainClasses.ofReal_pow_le_gCondMass
#print axioms ChainClasses.ofReal_pow_le_gMixMass
#print axioms ChainClasses.capacity_of_mass_boundsT
#print axioms ChainClasses.exists_gShapeCoupling_of_capacity

-- `thm:blob-law`, the i.i.d. and adapted-stopping clauses over the presented
-- skeleton, uniformly in the rule
#print axioms ChainClasses.bExplore_eq_iff
#print axioms ChainClasses.blob_root_fixed
#print axioms ChainClasses.survivalMeasure_blobC
#print axioms ChainClasses.blob_iid
#print axioms ChainClasses.bRuleMass_pos
#print axioms ChainClasses.bRuleMass_stopRule
