import ChainClasses.Encoding
import ChainClasses.Labelling
import ChainClasses.Isometry
import ChainClasses.Transfer
import ChainClasses.TransferReal
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
import ChainClasses.Hairs
import ChainClasses.MatchedPresentation
import ChainClasses.ChainCross
import ChainClasses.HairyCross
import ChainClasses.WordGraph
import ChainClasses.ThreeRays
import ChainClasses.GeneralDecomposition
import ChainClasses.GeneralShapeLaw
import ChainClasses.GeneralShapeIID
import ChainClasses.GeneralShapeMetric
import ChainClasses.GeneralShapeShrink
import ChainClasses.AddrMetric
import ChainClasses.GeneralContraction
import ChainClasses.GeneralShrink
import ChainClasses.GeneralShrinkScale
import ChainClasses.GeneralAssembly
import ChainClasses.GeneralCascade
import ChainClasses.ClusterField
import ChainClasses.ClusterRoot
import ChainClasses.ClusterIID
import ChainClasses.GeneralBushPoint
import ChainClasses.GeneralShapeMass
import ChainClasses.GeneralCoupling
import ChainClasses.GeneralShapeTail
import ChainClasses.GeneralShapeCoupling
import ChainClasses.GeneralShapeEta
import ChainClasses.UniformField
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
import ChainClasses.BlobField
import ChainClasses.BlobRoot
import ChainClasses.BlobLaw
import ChainClasses.Classification

/-!
# `ChainClasses`

The public quasi-isometry classification API is in `ChainClasses.Classification`:

* `simple_classification_ae_iff` for offspring supported on `{0,1,2}`;
* `classification_ae_iff` for packaged conditioned finite-support laws;
* `offspring_classification_ae_iff` for the complete conditioned-infinite raw-law statement;
* `same_class_ae` and `different_class_ae` for its two conclusions.

The remaining imports expose the implementation used by the paper.  Axiom audits are kept in the
separate module `ChainClasses.AxCheck` and are not part of this public umbrella.
-/
