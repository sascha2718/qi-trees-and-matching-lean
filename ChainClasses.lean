module

-- ## The chain encoding and the simple correspondence (`matching_classes_simple.tex`)

public import ChainClasses.Chain.Encoding
public import ChainClasses.Chain.Labelling
public import ChainClasses.Chain.Isometry
public import ChainClasses.Chain.Transfer
public import ChainClasses.Chain.TransferReal
public import ChainClasses.Chain.Geometric
public import ChainClasses.Chain.Quantise
public import ChainClasses.Chain.Eta
public import ChainClasses.Chain.Coupling
public import ChainClasses.Chain.WordGraph
public import ChainClasses.Chain.GWInstance
public import ChainClasses.Chain.Converse
public import ChainClasses.Chain.CrossLaw
public import ChainClasses.Chain.ThreeRays
public import ChainClasses.TwoValue

-- ## The scalar layer: marked quasi-isometries, shape masses, potentials and constants

public import ChainClasses.Scalar.MarkedQI
public import ChainClasses.Scalar.GluedTransfer
public import ChainClasses.Scalar.ShapeMass
public import ChainClasses.Scalar.ShapeEta
public import ChainClasses.Scalar.ShapeCoupling
public import ChainClasses.Scalar.Harris
public import ChainClasses.Scalar.Bushy
public import ChainClasses.Scalar.Relabel

-- ## Shapes, their metric and their contractions

public import ChainClasses.Shape.Shape
public import ChainClasses.Shape.Dilution
public import ChainClasses.Shape.ShapeMetric
public import ChainClasses.Shape.ShapeShrink
public import ChainClasses.Shape.Contraction
public import ChainClasses.Shape.ContractTree
public import ChainClasses.Shape.ContractAddr
public import ChainClasses.Shape.Assembly
public import ChainClasses.Shape.Binarise
public import ChainClasses.Shape.AddrMetric

-- ## The bushy regime of the simple case (`gw_classes_simple.tex`)

/-
Nomenclature follows the paper: "bushy" names regime (B), while a "bush" is
a finite component used as a geometric obstruction.  The strings `thm:hairy`
and `eq:hairy-rate` below are retained only because they are the existing
LaTeX labels in the paper.
-/

public import ChainClasses.Bushy.ShapeDecomposition
public import ChainClasses.Bushy.ShapeLaw
public import ChainClasses.Bushy.ShapeRootLaw
public import ChainClasses.Bushy.ShapeSplitLaw
public import ChainClasses.Bushy.ShapeIID
public import ChainClasses.Bushy.SplitJoint
public import ChainClasses.Bushy.AssemblyRelabel
public import ChainClasses.Bushy.Universality
public import ChainClasses.Bushy.ShapeLabelLaw
public import ChainClasses.Bushy.ShapeCouplingSelf
public import ChainClasses.Bushy.ShapeMassPoint
public import ChainClasses.Bushy.ShapeMassBush
public import ChainClasses.Bushy.ShapeEtaBlock
public import ChainClasses.Bushy.ShapeSizeTail
public import ChainClasses.Bushy.ShapeEtaSelf
public import ChainClasses.Bushy.ShapeCouplingCross
public import ChainClasses.Bushy.ShapeCouplingBuild
public import ChainClasses.Bushy.ShapePairEta
public import ChainClasses.Bushy.Bushes
public import ChainClasses.Bushy.Trichotomy

-- ## General bounded support (`matching_classes_general.tex`)

public import ChainClasses.General.GeneralHarris
public import ChainClasses.General.GeneralShape
public import ChainClasses.General.GeneralConstants
public import ChainClasses.General.GeneralDilution
public import ChainClasses.General.GeneralDecomposition
public import ChainClasses.General.GeneralShapeLaw
public import ChainClasses.General.GeneralShapeIID
public import ChainClasses.General.GeneralShapeMetric
public import ChainClasses.General.GeneralShapeShrink
public import ChainClasses.General.GeneralContraction
public import ChainClasses.General.GeneralShrink
public import ChainClasses.General.GeneralShrinkScale
public import ChainClasses.General.GeneralAssembly
public import ChainClasses.General.GeneralCascade
public import ChainClasses.General.GeneralBushPoint
public import ChainClasses.General.GeneralNeck
public import ChainClasses.General.GeneralShapeMass
public import ChainClasses.General.GeneralCoupling
public import ChainClasses.General.GeneralShapeTail
public import ChainClasses.General.GeneralShapeCoupling
public import ChainClasses.General.GeneralShapeEta
public import ChainClasses.General.GeneralLabelField

-- ## The original chain neck and arity laws at general support

public import ChainClasses.Regime.UniformField
public import ChainClasses.Regime.ChainNeckLaw
public import ChainClasses.Regime.DirectChainLabels

-- ## Arbitrary bounded profiles and the stopped Markov matching theorem

public import ChainClasses.Engine.ReducedProfiles
public import ChainClasses.Engine.SkeletonPatterns
public import ChainClasses.Engine.ProfileKernel
public import ChainClasses.Engine.ProfileLaw
public import ChainClasses.Engine.ProfileProjection
public import ChainClasses.Engine.ProfileMatching
public import ChainClasses.Engine.ProfileGeometry
public import ChainClasses.Engine.ProfileAssembly
public import ChainClasses.Engine.BushyProfileBridge
public import ChainClasses.Engine.QuantisedProfiles
public import ChainClasses.Engine.ChainEngineBridge

-- ## Universality and the classification (`trichotomy.tex`)

public import ChainClasses.Universality.GeneralObstructions
public import ChainClasses.Universality.BushyCross
public import ChainClasses.Universality.CascadeEncoding
public import ChainClasses.Universality.AssemblyAut
public import ChainClasses.Universality.SampleAssembly
public import ChainClasses.Universality.BAssembly
public import ChainClasses.Universality.FullTree
public import ChainClasses.Universality.BushyGeneral
public import ChainClasses.Universality.ChainPieces
public import ChainClasses.Universality.DirectChainGeometry
public import ChainClasses.Universality.ChainGeneral
public import ChainClasses.Universality.StarGeometry
public import ChainClasses.Universality.StarSeparation
public import ChainClasses.Universality.ChainSeparationProof
public import ChainClasses.Universality.GeneralTrichotomy
public import ChainClasses.Universality.ConcentratedPruning
public import ChainClasses.Classification
public import ChainClasses.Engine.ChainWitnesses
public import ChainClasses.Engine.ProfileWeightObstruction

/-!
# `ChainClasses`

The public quasi-isometry classification API is in `ChainClasses.Classification`:

* `simple_classification_ae_iff` for offspring supported on `{0,1,2}`;
* `classification_ae_iff` for packaged conditioned finite-support laws;
* `offspring_classification_ae_iff` for the complete conditioned-infinite raw-law statement;
* `same_class_ae` and `different_class_ae` for its two conclusions.

The remaining imports expose the implementation used by the paper, grouped in folders
that follow the paper: `Chain/` (the chain encoding, transfer, quantisation and coupling of
`matching_classes_simple.tex`, with the chain-side theorems of `gw_classes_simple.tex`),
`Scalar/` (marked quasi-isometries, shape masses and potentials, the scalar constants),
`Shape/` (shapes, their metric and their contractions), `Bushy/` (the bushy regime and the
simple classification), `General/` (general bounded support), `Regime/` (the chain regime
at general support through its original neck and arity laws), `Engine/` (bounded profiles
and the bridges to `GraphMarkovMatching.Stopped`), `Universality/` (the universality propositions and the general
classification), and `Classification/` (the public API).  `TwoValue` stays at the top
level, where `Solution.lean` imports it.
-/
