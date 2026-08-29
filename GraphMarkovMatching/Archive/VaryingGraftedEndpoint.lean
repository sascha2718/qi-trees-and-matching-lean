/-
The finite-to-infinite endpoint for the literal tagged 11/13 process.

This file deliberately assumes the uniform finite-height mismatch estimate.
It proves that no further process-law or compactness gap remains: the tagged
Markov laws are projectively consistent, and the generic Konig/measure
argument turns the finite-height estimate into one infinite automorphism.
-/
import GraphMarkovMatching.Archive.VaryingGraftedSupport
import GraphMarkovMatching.Closure.ProductMeasure

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

instance : MeasurableSpace GraftCounter := ⊤

instance : MeasurableSingletonClass GraftCounter := ⟨fun _ => trivial⟩

/-- The tagged root-mixture law is projectively consistent. -/
theorem graftTlaw_map_restrictLab {V : Type} (left : Bool)
    (mu : PMF V) (nu : PMF ℕ) (v0 : V) (n : ℕ) :
    (graftTlaw left mu nu v0 (n + 1)).map (restrictLab n) =
      graftTlaw left mu nu v0 n := by
  exact mix_map_restrictLab (graftK left mu nu v0)
    (graftFreshQ mu nu) n

/-- The two tagged laws are jointly projectively consistent. -/
theorem graftPairLaw_map_restrictLab {V : Type}
    (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V) (n : ℕ) :
    (prodPMF (graftTlaw true mu nuL v0 (n + 1))
        (graftTlaw false mu nuR v0 (n + 1))).map
        (Prod.map (restrictLab n) (restrictLab n)) =
      prodPMF (graftTlaw true mu nuL v0 n)
        (graftTlaw false mu nuR v0 n) := by
  rw [prodPMF_map_prodMap, graftTlaw_map_restrictLab,
    graftTlaw_map_restrictLab]

/-- The finite-height tagged mismatch is bounded by the corresponding full
directed potential. -/
theorem graftFailure_le_PhiD {V : Type} {alpha : ℝ} (halpha : 0 ≤ alpha)
    (Rv : V → V → Prop) (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    (n : ℕ) :
    failureD (graftTlaw true mu nuL v0 n)
        (graftTlaw false mu nuR v0 n) (fullSim (graftLabRel Rv) n) ≤
      PhiD alpha (graftTlaw true mu nuL v0 n)
        (graftTlaw false mu nuR v0 n) (fullSim (graftLabRel Rv) n) := by
  exact tsum_qE_le_PhiD halpha _ _ _

/-- **Tagged two-law infinite endpoint.**  A uniform mismatch bound for the
literal left-11/right-13 process at every finite height yields one binary-tree
automorphism matching the two infinite samples with probability at least
`1 - b`.  Thus a proof of the finite-height ledger estimate is the only
analytic input still needed by the endpoint. -/
theorem graftMatching_infinite {V : Type} {Omega : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Omega] (Pm : Measure Omega) [IsProbabilityMeasure Pm]
    (Rv : V → V → Prop) (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    (b : ℝ≥0∞)
    (hfail : ∀ n, failureD
      (graftTlaw true mu nuL v0 n) (graftTlaw false mu nuR v0 n)
      (fullSim (graftLabRel Rv) n) ≤ b)
    (X Y : (n : ℕ) → Omega → FullLab (GraftState V) n)
    (hX : ∀ n omega, restrictLab n (X (n + 1) omega) = X n omega)
    (hY : ∀ n omega, restrictLab n (Y (n + 1) omega) = Y n omega)
    (hpair : ∀ n, Measurable (fun omega => (X n omega, Y n omega)))
    (hlaw : ∀ n, Pm.map (fun omega => (X n omega, Y n omega)) =
      (prodPMF (graftTlaw true mu nuL v0 n)
        (graftTlaw false mu nuR v0 n)).toMeasure) :
    1 - b ≤ Pm {omega | InfMatch (graftLabRel Rv)
      (fun n => X n omega) (fun n => Y n omega)} := by
  refine infinite_tree_matchingK_prob Pm (graftLabRel Rv) 1 0 X Y hX hY
    (fun n => ?_) b (fun n => ?_)
  · exact (hpair n)
      ((Set.to_countable
        {p : FullLab (GraftState V) n × FullLab (GraftState V) n |
          fullSimK (graftLabRel Rv) 1 0 n p.1 p.2}).measurableSet)
  · rw [show {omega | ¬ fullSimK (graftLabRel Rv) 1 0 n
          (X n omega) (Y n omega)} =
        (fun omega => (X n omega, Y n omega)) ⁻¹'
          {p | ¬ fullSimK (graftLabRel Rv) 1 0 n p.1 p.2} from rfl,
      ← Measure.map_apply (hpair n) ((Set.to_countable _).measurableSet),
      hlaw n, prodPMF_toMeasure_not_rel_cross]
    exact hfail n

/-- Potential form of the tagged endpoint. -/
theorem graftMatching_infinite_of_PhiD {V : Type} {Omega : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Omega] (Pm : Measure Omega) [IsProbabilityMeasure Pm]
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (Rv : V → V → Prop) (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    (b : ℝ≥0∞)
    (hPhi : ∀ n, PhiD alpha
      (graftTlaw true mu nuL v0 n) (graftTlaw false mu nuR v0 n)
      (fullSim (graftLabRel Rv) n) ≤ b)
    (X Y : (n : ℕ) → Omega → FullLab (GraftState V) n)
    (hX : ∀ n omega, restrictLab n (X (n + 1) omega) = X n omega)
    (hY : ∀ n omega, restrictLab n (Y (n + 1) omega) = Y n omega)
    (hpair : ∀ n, Measurable (fun omega => (X n omega, Y n omega)))
    (hlaw : ∀ n, Pm.map (fun omega => (X n omega, Y n omega)) =
      (prodPMF (graftTlaw true mu nuL v0 n)
        (graftTlaw false mu nuR v0 n)).toMeasure) :
    1 - b ≤ Pm {omega | InfMatch (graftLabRel Rv)
      (fun n => X n omega) (fun n => Y n omega)} := by
  exact graftMatching_infinite Pm Rv mu nuL nuR v0 b
    (fun n => (graftFailure_le_PhiD halpha Rv mu nuL nuR v0 n).trans
      (hPhi n)) X Y hX hY hpair hlaw

/-- Restricted-potential endpoint for the fixed 11/13 law pair.  The new
support theorem removes the zero-interface contribution uniformly in the
height, so a bound on `PhiDres` itself is enough. -/
theorem graftMatching_infinite_of_PhiDres_law {V : Type} {Omega : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Omega] (Pm : Measure Omega) [IsProbabilityMeasure Pm]
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (Rv : V → V → Prop) (mu : PMF V) (nuL nuR : PMF ℕ) (v0 : V)
    {zeta : ℝ≥0∞} (hrefl : ∀ v, Rv v v)
    (hLaw : IsElevenThirteenLawPair nuL nuR zeta)
    (hp11 : replacementMass (nuR 7) (mu v0) (nuR 5) ≠ 0)
    (hp13 : replacementMass (nuL 9) (mu v0) (nuL 5) ≠ 0)
    (b : ℝ≥0∞)
    (hPhi : ∀ n, PhiDres alpha
      (graftTlaw true mu nuL v0 n) (graftTlaw false mu nuR v0 n)
      (fullSim (graftLabRel Rv) n) ≤ b)
    (X Y : (n : ℕ) → Omega → FullLab (GraftState V) n)
    (hX : ∀ n omega, restrictLab n (X (n + 1) omega) = X n omega)
    (hY : ∀ n omega, restrictLab n (Y (n + 1) omega) = Y n omega)
    (hpair : ∀ n, Measurable (fun omega => (X n omega, Y n omega)))
    (hlaw : ∀ n, Pm.map (fun omega => (X n omega, Y n omega)) =
      (prodPMF (graftTlaw true mu nuL v0 n)
        (graftTlaw false mu nuR v0 n)).toMeasure) :
    1 - b ≤ Pm {omega | InfMatch (graftLabRel Rv)
      (fun n => X n omega) (fun n => Y n omega)} := by
  exact graftMatching_infinite Pm Rv mu nuL nuR v0 b
    (fun n => (graftFailure_le_PhiDres_of_law Rv mu nuL nuR v0 alpha
      halpha hrefl hLaw hp11 hp13 n).trans (hPhi n))
    X Y hX hY hpair hlaw

end GraphMarkovMatching
