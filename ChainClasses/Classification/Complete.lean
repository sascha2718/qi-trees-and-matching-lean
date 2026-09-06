import ChainClasses.Universality.ChainSeparationProof

/-!
# Complete classification for conditioned infinite Galton--Watson trees

This is the public entry point for the complete conditioned-infinite classification at finite
support.  The proof is developed in `ChainClasses.Universality.GeneralTrichotomy` and
`ChainClasses.Universality.ChainSeparationProof`.

The main declarations are:

* `classification_ae_iff`, the eventwise theorem for packaged classification cases.
* `offspring_classification_ae_iff`, the theorem expanded directly for two offspring laws.
* `same_class_ae` and `different_class_ae`, the two conclusions separately.

These declarations concern laws conditioned on an infinite realisation.  The elementary finite
class `(Fin)` in the paper is therefore outside their scope.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (Offspring QuasiIsometric rayGraph)

/-- Equality of the complete quasi-isometry class invariant for two packaged offspring laws. -/
def GRegime.SameClass (R R' : GRegime) : Prop :=
  R.kind = R'.kind ∧ (R.IsChain → R'.IsChain → R.semigroup = R'.semigroup)

/-- Two packaged offspring laws in the same class give quasi-isometric samples almost surely. -/
theorem same_class_ae (R R' : GRegime) (hclass : R.SameClass R') :
    ∀ᵐ omega ∂(R.sampleLaw.law.prod R'.sampleLaw.law),
      GPairQI R.sampleLaw R'.sampleLaw omega :=
  same_gRegime_ae' R R' hclass.1 hclass.2

/-- Two packaged offspring laws in different classes give samples that are almost surely not
quasi-isometric. -/
theorem different_class_ae (R R' : GRegime) (hclass : ¬ R.SameClass R') :
    ∀ᵐ omega ∂(R.sampleLaw.law.prod R'.sampleLaw.law),
      ¬ GPairQI R.sampleLaw R'.sampleLaw omega := by
  filter_upwards [trichotomy_ae_iff R R'] with omega homega
  exact fun hqi ↦ hclass ⟨(homega.mp hqi).1, (homega.mp hqi).2⟩

/-- The eventwise complete classification for packaged conditioned offspring laws. -/
theorem classification_ae_iff (R R' : GRegime) :
    ∀ᵐ omega ∂(R.sampleLaw.law.prod R'.sampleLaw.law),
      GPairQI R.sampleLaw R'.sampleLaw omega ↔ R.SameClass R' := by
  simpa [GRegime.SameClass] using trichotomy_ae_iff R R'

/-- No conditioned sample outside the ray class is quasi-isometric to the ray, almost surely. -/
theorem classification_not_ray_ae (R : GRegime) (hR : R.kind ≠ 0) :
    ∀ᵐ omega ∂R.sampleLaw.law,
      ¬ QuasiIsometric (R.sampleLaw.graph omega) rayGraph :=
  trichotomy_not_ray R hR

/-- The complete conditioned-infinite classification expanded directly for two finitely supported
offspring laws.

Every non-ray law is written with its largest supported offspring number as `J`.  The four
alternatives are classes (R), (F), `(C_Λ)` with equal branching semigroups, and (B).
-/
theorem offspring_classification_ae_iff {J J' N N' : ℕ}
    (theta : Offspring J) (hJN : J ≤ N)
    (hvalid : theta.IsSupercritical ∨ theta 1 = 1)
    (htop : theta 1 = 1 ∨ (2 ≤ J ∧ 0 < theta J))
    (theta' : Offspring J') (hJN' : J' ≤ N')
    (hvalid' : theta'.IsSupercritical ∨ theta' 1 = 1)
    (htop' : theta' 1 = 1 ∨ (2 ≤ J' ∧ 0 < theta' J')) :
    let R := GRegime.ofExact theta hJN hvalid htop
    let R' := GRegime.ofExact theta' hJN' hvalid' htop'
    ∀ᵐ omega ∂(R.sampleLaw.law.prod R'.sampleLaw.law),
      GPairQI R.sampleLaw R'.sampleLaw omega ↔
        (theta 1 = 1 ∧ theta' 1 = 1) ∨
        (theta 0 = 0 ∧ theta 1 = 0 ∧ theta' 0 = 0 ∧ theta' 1 = 0) ∨
        ((theta 0 = 0 ∧ 0 < theta 1 ∧ theta 1 < 1) ∧
          (theta' 0 = 0 ∧ 0 < theta' 1 ∧ theta' 1 < 1) ∧
          AddSubmonoid.closure (shiftSupp theta : Set ℕ) =
            AddSubmonoid.closure (shiftSupp theta' : Set ℕ)) ∨
        (0 < theta 0 ∧ 0 < theta' 0) :=
  trichotomy_exact_ae_iff theta hJN hvalid htop theta' hJN' hvalid' htop'

/-- The raw offspring-law form of the one-sample ray separation. -/
theorem offspring_classification_not_ray_ae {J N : ℕ}
    (theta : Offspring J) (hJN : J ≤ N)
    (hvalid : theta.IsSupercritical ∨ theta 1 = 1)
    (htop : theta 1 = 1 ∨ (2 ≤ J ∧ 0 < theta J)) (h1 : theta 1 ≠ 1) :
    let R := GRegime.ofExact theta hJN hvalid htop
    ∀ᵐ omega ∂R.sampleLaw.law,
      ¬ QuasiIsometric (R.sampleLaw.graph omega) rayGraph :=
  trichotomy_exact_not_ray theta hJN hvalid htop h1

end ChainClasses
