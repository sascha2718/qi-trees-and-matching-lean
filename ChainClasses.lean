-- ## The chain encoding and the simple correspondence (`matching_classes_simple.tex`)

import ChainClasses.Chain.Encoding
import ChainClasses.Chain.Labelling
import ChainClasses.Chain.Isometry
import ChainClasses.Chain.Transfer
import ChainClasses.Chain.TransferReal
import ChainClasses.Chain.Geometric
import ChainClasses.Chain.Quantise
import ChainClasses.Chain.Eta
import ChainClasses.Chain.Coupling
import ChainClasses.Chain.WordGraph
import ChainClasses.Chain.GWInstance
import ChainClasses.Chain.Converse
import ChainClasses.Chain.CrossLaw
import ChainClasses.Chain.ThreeRays
import ChainClasses.TwoValue

-- ## The scalar layer: marked quasi-isometries, shape masses, potentials and constants

import ChainClasses.Scalar.MarkedQI
import ChainClasses.Scalar.GluedTransfer
import ChainClasses.Scalar.ShapeMass
import ChainClasses.Scalar.ShapeEta
import ChainClasses.Scalar.ShapeCoupling
import ChainClasses.Scalar.Harris
import ChainClasses.Scalar.Bushy
import ChainClasses.Scalar.Relabel

-- ## Shapes, their metric and their contractions

import ChainClasses.Shape.Shape
import ChainClasses.Shape.Dilution
import ChainClasses.Shape.ShapeMetric
import ChainClasses.Shape.ShapeShrink
import ChainClasses.Shape.Contraction
import ChainClasses.Shape.ContractTree
import ChainClasses.Shape.ContractAddr
import ChainClasses.Shape.Assembly
import ChainClasses.Shape.Binarise
import ChainClasses.Shape.AddrMetric

-- ## The bushy regime of the simple case (`gw_classes_simple.tex`)

/-
Nomenclature follows the paper: "bushy" names regime (B), while a "bush" is
a finite component used as a geometric obstruction.  The strings `thm:hairy`
and `eq:hairy-rate` below are retained only because they are the existing
LaTeX labels in the paper.
-/

import ChainClasses.Bushy.ShapeDecomposition
import ChainClasses.Bushy.ShapeLaw
import ChainClasses.Bushy.ShapeRootLaw
import ChainClasses.Bushy.ShapeSplitLaw
import ChainClasses.Bushy.ShapeIID
import ChainClasses.Bushy.SplitJoint
import ChainClasses.Bushy.AssemblyRelabel
import ChainClasses.Bushy.Universality
import ChainClasses.Bushy.ShapeLabelLaw
import ChainClasses.Bushy.ShapeCouplingSelf
import ChainClasses.Bushy.ShapeMassPoint
import ChainClasses.Bushy.ShapeMassBush
import ChainClasses.Bushy.ShapeEtaBlock
import ChainClasses.Bushy.ShapeSizeTail
import ChainClasses.Bushy.ShapeEtaSelf
import ChainClasses.Bushy.ShapeCouplingCross
import ChainClasses.Bushy.ShapeCouplingBuild
import ChainClasses.Bushy.ShapePairEta
import ChainClasses.Bushy.Bushes
import ChainClasses.Bushy.Trichotomy

-- ## General bounded support (`matching_classes_general.tex`)

import ChainClasses.General.GeneralHarris
import ChainClasses.General.GeneralShape
import ChainClasses.General.GeneralConstants
import ChainClasses.General.GeneralDilution
import ChainClasses.General.GeneralDecomposition
import ChainClasses.General.GeneralShapeLaw
import ChainClasses.General.GeneralShapeIID
import ChainClasses.General.GeneralShapeMetric
import ChainClasses.General.GeneralShapeShrink
import ChainClasses.General.GeneralContraction
import ChainClasses.General.GeneralShrink
import ChainClasses.General.GeneralShrinkScale
import ChainClasses.General.GeneralAssembly
import ChainClasses.General.GeneralCascade
import ChainClasses.General.GeneralBushPoint
import ChainClasses.General.GeneralNeck
import ChainClasses.General.GeneralShapeMass
import ChainClasses.General.GeneralCoupling
import ChainClasses.General.GeneralShapeTail
import ChainClasses.General.GeneralShapeCoupling
import ChainClasses.General.GeneralShapeEta
import ChainClasses.General.GeneralLabelField

-- ## The original chain neck and arity laws at general support

import ChainClasses.Regime.UniformField
import ChainClasses.Regime.ChainNeckLaw
import ChainClasses.Regime.DirectChainLabels

-- ## Arbitrary bounded profiles and the stopped Markov matching theorem

import ChainClasses.Engine.ReducedProfiles
import ChainClasses.Engine.SkeletonPatterns
import ChainClasses.Engine.ProfileKernel
import ChainClasses.Engine.ProfileLaw
import ChainClasses.Engine.ProfileProjection
import ChainClasses.Engine.ProfileMatching
import ChainClasses.Engine.ProfileGeometry
import ChainClasses.Engine.ProfileAssembly
import ChainClasses.Engine.BushyProfileBridge
import ChainClasses.Engine.QuantisedProfiles
import ChainClasses.Engine.EngineBridge
import ChainClasses.Engine.ChainEngineBridge

-- ## Universality and the classification (`trichotomy.tex`)

import ChainClasses.Universality.GeneralObstructions
import ChainClasses.Universality.BushyCross
import ChainClasses.Universality.CascadeEncoding
import ChainClasses.Universality.AssemblyAut
import ChainClasses.Universality.SampleAssembly
import ChainClasses.Universality.BAssembly
import ChainClasses.Universality.FullTree
import ChainClasses.Universality.BushyGeneral
import ChainClasses.Universality.ChainPieces
import ChainClasses.Universality.DirectChainGeometry
import ChainClasses.Universality.ChainGeneral
import ChainClasses.Universality.StarGeometry
import ChainClasses.Universality.StarSeparation
import ChainClasses.Universality.ChainSeparationProof
import ChainClasses.Universality.GeneralTrichotomy
import ChainClasses.Classification
import ChainClasses.Engine.ChainWitnesses
import ChainClasses.Engine.ProfileWeightObstruction

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
