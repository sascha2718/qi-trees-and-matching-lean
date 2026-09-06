/-
The finite-to-infinite endpoint for the composite two-law matching
(`arbitrary_offspring_matching.tex`, `sec:composite`, the projective
endpoint sentence of the proof of `thm:composite-matching`).

The composite kernels restrict projectively, height `h + 1` to height
`h`, so the projective endpoint argument of the fixed-pair matching
theorem applies verbatim: this file instantiates the generic
root-mixture consistency (`mix_map_restrictLab`) and the generic
Konig/measure packaging (`infinite_tree_matchingK_prob`) at the
composite tagged kernel `compK`, and assumes only the uniform
finite-height mismatch estimate.

* `cT_map_restrictLab`: the composite fresh-mixture law is projectively
  consistent;
* `cT_hasMatchingSupport`, `cFailure_le_PhiDres_of_support`: under the
  support witness of `thm:support-equality` the zero interface vanishes, so
  the restricted potential alone bounds the finite-height mismatch;
* `cMatching_infinite`, `cMatching_infinite_of_PhiDres`: a uniform
  finite-height mismatch bound `b` yields one binary-tree automorphism
  matching the two infinite composite samples with probability at least
  `1 - b`;
* `cTPair`: the law of the two independent infinite composite samples,
  constructed as the product of two trajectory measures, a probability
  measure.
-/
import GraphMarkovMatching.Composite.Support
import GraphMarkovMatching.Composite.ProductMeasure
import GraphMarkovMatching.Process.MatchingSupport
import GraphMarkovMatching.Support.Trajectory

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

/-- An injective code for the tagged counters. -/
private def ctrCode : CtrC → ℕ ⊕ (ℕ × ℕ × ℕ)
  | CtrC.ord k => Sum.inl k
  | CtrC.mark a b i => Sum.inr (a, b, i)

instance : Countable CtrC := by
  have hinj : Function.Injective ctrCode := by
    intro c d hcd
    cases c <;> cases d <;> simp_all [ctrCode]
  exact hinj.countable

instance : MeasurableSpace CtrC := ⊤

instance : MeasurableSingletonClass CtrC := ⟨fun _ => trivial⟩

/-! ### Projective consistency of the composite laws -/

/-- The composite fresh-mixture law is projectively consistent:
restricting a height-`(n + 1)` sample to height `n` recovers the
height-`n` law. -/
theorem cT_map_restrictLab {V : Type} (exc : ℕ → Option (ℕ × ℕ))
    (μ : PMF V) (ν : PMF ℕ) (v0 : V) (n : ℕ) :
    (cT exc μ ν v0 (n + 1)).map (restrictLab n) = cT exc μ ν v0 n := by
  exact mix_map_restrictLab (compK exc μ ν v0) (freshC μ ν) n

/-! ### Finite-height mismatch against the potentials -/

/-- The support witness of `thm:support-equality`, packaged as a matching
support statement for the two composite fresh laws. -/
theorem cT_hasMatchingSupport {V : Type}
    (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (N : ℕ)
    (hrefl : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdecl : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (h : ℕ) :
    HasMatchingSupport (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
      (fullSim (cRel Rv) h) := by
  intro x hx
  obtain ⟨y, hy, hsim⟩ := exists_sim_of_cT_ne_zero Rv μ v0 exc1 exc2 ν1 ν2 N
    hrefl hμ0 hN hdecl hcharged h x hx
  exact ⟨y, hy, hsim⟩

/-- Restricted-potential form of the mismatch bound: under the support
witness the zero-interface term vanishes uniformly in the height, so a
bound on `PhiDres` itself is enough. -/
theorem cFailure_le_PhiDres_of_support {V : Type} {alpha : ℝ}
    (halpha : 0 ≤ alpha)
    (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (N : ℕ)
    (hrefl : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdecl : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (h : ℕ) :
    failureD (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
        (fullSim (cRel Rv) h) ≤
      PhiDres alpha (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
        (fullSim (cRel Rv) h) := by
  have hsupp := cT_hasMatchingSupport Rv μ v0 exc1 exc2 ν1 ν2 N
    hrefl hμ0 hN hdecl hcharged h
  have hrow := failureD_le_PhiDres_add_zMass alpha halpha
    (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h) (fullSim (cRel Rv) h)
  rw [hsupp.zMass_eq_zero, add_zero] at hrow
  exact hrow

/-! ### The infinite endpoint -/

/-- **Composite two-law infinite endpoint.**  A uniform mismatch bound
for the two composite processes at every finite height yields one
binary-tree automorphism matching the two infinite samples with
probability at least `1 - b`.  Thus a proof of the finite-height ledger
estimate is the only analytic input still needed by the endpoint. -/
theorem cMatching_infinite {V : Type} {Omega : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Omega] (Pm : Measure Omega) [IsProbabilityMeasure Pm]
    (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (b : ℝ≥0∞)
    (hfail : ∀ n, failureD
      (cT exc1 μ ν1 v0 n) (cT exc2 μ ν2 v0 n)
      (fullSim (cRel Rv) n) ≤ b)
    (X Y : (n : ℕ) → Omega → FullLab (CState V) n)
    (hX : ∀ n omega, restrictLab n (X (n + 1) omega) = X n omega)
    (hY : ∀ n omega, restrictLab n (Y (n + 1) omega) = Y n omega)
    (hpair : ∀ n, Measurable (fun omega => (X n omega, Y n omega)))
    (hlaw : ∀ n, Pm.map (fun omega => (X n omega, Y n omega)) =
      (prodPMF (cT exc1 μ ν1 v0 n)
        (cT exc2 μ ν2 v0 n)).toMeasure) :
    1 - b ≤ Pm {omega | InfMatch (cRel Rv)
      (fun n => X n omega) (fun n => Y n omega)} := by
  refine infinite_tree_matchingK_prob Pm (cRel Rv) 1 0 X Y hX hY
    (fun n => ?_) b (fun n => ?_)
  · exact (hpair n)
      ((Set.to_countable
        {p : FullLab (CState V) n × FullLab (CState V) n |
          fullSimK (cRel Rv) 1 0 n p.1 p.2}).measurableSet)
  · rw [show {omega | ¬ fullSimK (cRel Rv) 1 0 n
          (X n omega) (Y n omega)} =
        (fun omega => (X n omega, Y n omega)) ⁻¹'
          {p | ¬ fullSimK (cRel Rv) 1 0 n p.1 p.2} from rfl,
      ← Measure.map_apply (hpair n) ((Set.to_countable _).measurableSet),
      hlaw n, prodPMF_toMeasure_not_rel_cross]
    exact hfail n

/-- Restricted-potential form of the composite endpoint.  The support
witness removes the zero-interface contribution uniformly in the height,
so a bound on `PhiDres` itself is enough. -/
theorem cMatching_infinite_of_PhiDres {V : Type} {Omega : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Omega] (Pm : Measure Omega) [IsProbabilityMeasure Pm]
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (N : ℕ)
    (hrefl : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdecl : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (b : ℝ≥0∞)
    (hPhi : ∀ n, PhiDres alpha
      (cT exc1 μ ν1 v0 n) (cT exc2 μ ν2 v0 n)
      (fullSim (cRel Rv) n) ≤ b)
    (X Y : (n : ℕ) → Omega → FullLab (CState V) n)
    (hX : ∀ n omega, restrictLab n (X (n + 1) omega) = X n omega)
    (hY : ∀ n omega, restrictLab n (Y (n + 1) omega) = Y n omega)
    (hpair : ∀ n, Measurable (fun omega => (X n omega, Y n omega)))
    (hlaw : ∀ n, Pm.map (fun omega => (X n omega, Y n omega)) =
      (prodPMF (cT exc1 μ ν1 v0 n)
        (cT exc2 μ ν2 v0 n)).toMeasure) :
    1 - b ≤ Pm {omega | InfMatch (cRel Rv)
      (fun n => X n omega) (fun n => Y n omega)} := by
  exact cMatching_infinite Pm Rv μ v0 exc1 exc2 ν1 ν2 b
    (fun n => (cFailure_le_PhiDres_of_support halpha Rv μ v0 exc1 exc2
      ν1 ν2 N hrefl hμ0 hN hdecl hcharged n).trans (hPhi n))
    X Y hX hY hpair hlaw

/-! ### The constructed pair of infinite composite samples -/

/-- **The law of two independent infinite composite samples**: the product of two
trajectory measures over the composite level laws. -/
noncomputable def cTPair {V : Type} [Countable V] [MeasurableSpace V]
    [MeasurableSingletonClass V] (μ : PMF V) (v0 : V)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) :
    Measure ((Π n, FullLab (CState V) n) × (Π n, FullLab (CState V) n)) :=
  trajPairLab (cT exc1 μ ν1 v0) (fun n => cT_map_restrictLab exc1 μ ν1 v0 n)
    (cT exc2 μ ν2 v0) (fun n => cT_map_restrictLab exc2 μ ν2 v0 n)

instance {V : Type} [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (μ : PMF V) (v0 : V) (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) :
    IsProbabilityMeasure (cTPair μ v0 exc1 exc2 ν1 ν2) := by
  rw [cTPair]
  infer_instance

end Composite
end GraphMarkovMatching
