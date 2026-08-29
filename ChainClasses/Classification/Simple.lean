import ChainClasses.Trichotomy

/-!
# Classification for offspring supported on `{0,1,2}`

This is the public entry point for the simple-support classification.  The proof is developed in
`ChainClasses.Trichotomy`. The declarations below give the result names that should be used by
downstream files.

The declaration `simple_classification` is the direct endpoint for the paper theorem, including
the one-sample ray separation.  Its pairwise core is `simple_classification_ae_iff`, which states
the same-class and different-class conclusions in one eventwise equivalence.  The separate
conclusions and the one-sample ray separation are available as `simple_same_class_ae`,
`simple_different_class_ae`, and `simple_not_ray_ae`.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (QuasiIsometric rayGraph)

/-- Two valid simple-support laws in the same class give quasi-isometric samples almost surely. -/
theorem simple_same_class_ae (r r' : Regime) (hr : r.Valid) (hr' : r'.Valid)
    (hclass : r.kind = r'.kind) :
    ∀ᵐ omega ∂((r.sampleLaw hr).law.prod (r'.sampleLaw hr').law),
      PairQI (r.sampleLaw hr) (r'.sampleLaw hr') omega :=
  same_regime_ae r r' hr hr' hclass

/-- Two valid simple-support laws in different classes give samples that are almost surely not
quasi-isometric. -/
theorem simple_different_class_ae (r r' : Regime) (hr : r.Valid) (hr' : r'.Valid)
    (hclass : r.kind ≠ r'.kind) :
    ∀ᵐ omega ∂((r.sampleLaw hr).law.prod (r'.sampleLaw hr').law),
      ¬ PairQI (r.sampleLaw hr) (r'.sampleLaw hr') omega :=
  diff_regime_ae r r' hr hr' hclass

/-- The eventwise quasi-isometry classification for offspring supported on `{0,1,2}`. -/
theorem simple_classification_ae_iff (r r' : Regime) (hr : r.Valid) (hr' : r'.Valid) :
    ∀ᵐ omega ∂((r.sampleLaw hr).law.prod (r'.sampleLaw hr').law),
      PairQI (r.sampleLaw hr) (r'.sampleLaw hr') omega ↔ r.kind = r'.kind := by
  by_cases hclass : r.kind = r'.kind
  · filter_upwards [simple_same_class_ae r r' hr hr' hclass] with omega hqi
    exact iff_of_true hqi hclass
  · filter_upwards [simple_different_class_ae r r' hr hr' hclass] with omega hnqi
    exact iff_of_false hnqi hclass

/-- The simple-support classification together with the one-sample ray separation. -/
theorem simple_classification (r r' : Regime) (hr : r.Valid) (hr' : r'.Valid) :
    (r.kind = r'.kind → ∀ᵐ omega ∂((r.sampleLaw hr).law.prod (r'.sampleLaw hr').law),
        PairQI (r.sampleLaw hr) (r'.sampleLaw hr') omega)
      ∧ (r.kind ≠ r'.kind →
        ∀ᵐ omega ∂((r.sampleLaw hr).law.prod (r'.sampleLaw hr').law),
        ¬ PairQI (r.sampleLaw hr) (r'.sampleLaw hr') omega)
      ∧ (r ≠ Regime.ray → ∀ᵐ omega ∂(r.sampleLaw hr).law,
          ¬ QuasiIsometric ((r.sampleLaw hr).graph omega) rayGraph) :=
  trichotomy_simple r r' hr hr'

/-- No sample outside the simple-support ray class is quasi-isometric to the ray, almost surely. -/
theorem simple_not_ray_ae (r : Regime) (hr : r.Valid) (hray : r ≠ Regime.ray) :
    ∀ᵐ omega ∂(r.sampleLaw hr).law,
      ¬ QuasiIsometric ((r.sampleLaw hr).graph omega) rayGraph :=
  not_ray_ae r hr hray

end ChainClasses
