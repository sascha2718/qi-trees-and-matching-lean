# Lean formalisation

The public entry point for the quasi-isometry classifications is:

```lean
import ChainClasses.Classification
```

All declarations below are in the `ChainClasses` namespace.

| Result | Public declaration |
|---|---|
| Full theorem for offspring supported on `{0,1,2}` | `simple_classification` |
| Pairwise eventwise simple-support classification | `simple_classification_ae_iff` |
| Packaged conditioned laws | `classification_ae_iff` |
| Two offspring laws, with the four infinite classes expanded | `offspring_classification_ae_iff` |
| Same-class conclusion | `same_class_ae` |
| Different-class conclusion | `different_class_ae` |

These declarations concern Galton--Watson laws conditioned on an infinite realisation.
Consequently, they classify the infinite classes (R), (F), `(C_Λ)`, and (B). The elementary
finite class `(Fin)` in the paper is outside this conditioned-infinite endpoint.

The façade is split into `ChainClasses.Classification.Simple` and
`ChainClasses.Classification.Complete`. The older modules `ChainClasses.Trichotomy`,
`ChainClasses.GeneralTrichotomy`, and `ChainClasses.ChainSeparationProof` contain the proof
implementation and retain their established declaration names.

## Build and audit

Run commands from this directory:

```bash
lake build ChainClasses
lake build ChainClasses.AxCheck
lake build Challenge Solution
```

`ChainClasses/AxCheck.lean` contains the detailed axiom audit. `Challenge.lean`,
`Solution.lean`, and `comparator-config.json` define the independent headline-theorem audit.
