import ChainClasses.Classification.Simple
import ChainClasses.Classification.Complete
import ChainClasses.Classification.Finite
import ChainClasses.Classification.Embedding

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
* `full_classification_ae_iff` is the complete theorem over the unconditioned laws, with the
  finite class included.
* `embedding_hierarchy_ae` is the mutual embeddability theorem `thm:embedding-hierarchy`, with
  `mutual_embeddability_ae` for two laws and the strict hierarchy `Fin ≺ Ray ≺ Supercritical`
  in `qiEmbeddable_rayGraph_of_not_survives`, `not_qiEmbeddable_rayGraph_of_not_survives`,
  `qiEmbeddable_rayGraph_of_survives` and `ae_not_qiEmbeddable_rayGraph`.

The implementation remains in `ChainClasses.Bushy.Trichotomy`, `ChainClasses.Universality.GeneralTrichotomy`,
`ChainClasses.Universality.ChainSeparationProof` and, for the embeddings,
`ChainClasses.Universality.ConcentratedPruning`.
-/
