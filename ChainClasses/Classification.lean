import ChainClasses.Classification.Simple
import ChainClasses.Classification.Complete

/-!
# Public quasi-isometry classification API

Import this module to use the classification results without navigating the implementation
modules.

* `simple_classification` is the complete paper endpoint for offspring supported on `{0,1,2}`.
* `simple_classification_ae_iff` is its pairwise eventwise core.
* `classification_ae_iff` is the complete eventwise theorem for packaged conditioned laws.
* `offspring_classification_ae_iff` is the complete conditioned-infinite theorem written directly
  for offspring laws.
* `same_class_ae` and `different_class_ae` expose its two conclusions separately.

The implementation remains in `ChainClasses.Bushy.Trichotomy`, `ChainClasses.Universality.GeneralTrichotomy`, and
`ChainClasses.Universality.ChainSeparationProof`.
-/
