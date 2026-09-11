import ChainClasses.Engine.QuantisedProfiles
import ChainClasses.Regime.DirectChainLabels

/-! Direct matching for the original reduced arity laws of chain offspring processes.
The common atomic profiles and their positive probability floor are chosen once, before
varying the geometric scale. -/

namespace ChainClasses

open MeasureTheory
open GraphMarkovMatching.Stopped
open scoped ENNReal Classical
open BranchingProcess (Offspring survivalMeasure)

variable {J J' N N' : ℕ}

/-- Independent original samples, with a uniform field only for the neck-class coupling. -/
noncomputable def directChainMeasure (θ : Offspring J) (θ' : Offspring J') :
    Measure ((GWord N → ℕ) × ((GWord N' → ℕ) × (GWord N' → ℝ))) :=
  (survivalMeasure θ).prod (labelMeasure θ')

/-- Fixed atomic profiles match the original reduced chain laws with probability
arbitrarily close to one. -/
theorem exists_direct_chain_match (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : 0 < θ 1) (hθ1' : θ 1 < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hθ0' : θ' 0 = 0) (hθ1'₀ : 0 < θ' 1)
    (hθ1'' : θ' 1 < 1) (hJ2' : 2 ≤ J')
    (hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ) =
      AddSubmonoid.closure (shiftSupp θ' : Set ℕ)) :
    ∃ C C' : Profile.Family, ∀ δ : ℝ, 0 < δ → ∃ D : ℕ, 5 ≤ D ∧
      1 ≤ cgamma (θ 1) (θ' 1) * ((D : ℝ) - 1) ∧
      1 - ENNReal.ofReal δ ≤ directChainMeasure (N := N) (N' := N') θ θ'
        {ω | GraphMarkovMatching.InfMatch (GraphMatching.compat GraphMatching.pathGraph)
          (fun n => Profile.encodedStates C (directChainLab D ω.1) (gArityAt ω.1) 0 n)
          (fun n => Profile.encodedStates C' (directCrossLab (θ 1) (θ' 1) D ω.2)
            (gArityAt ω.2.1) 0 n)} := by
  let P := chainPresentation θ hθ0 hθ1' hJ2 hθJ θ' hθ0' hθ1'' hJ2' hsem
  let C := Profile.presentationFamily P false
  let C' := Profile.presentationFamily P true
  refine ⟨C, C', fun δ hδ => ?_⟩
  have hγ := cgamma_pos hθ1 hθ1' hθ1'₀ hθ1''
  obtain ⟨D, hD, hlarge, hfail⟩ := quantised_profile_scale P hθ1 hθ1' hδ
    (⌈1 / cgamma (θ 1) (θ' 1)⌉₊ + 1)
  have hgD : 1 ≤ cgamma (θ 1) (θ' 1) * ((D : ℝ) - 1) := by
    have hceil := Nat.le_ceil (1 / cgamma (θ 1) (θ' 1))
    have hcast : ((⌈1 / cgamma (θ 1) (θ' 1)⌉₊ + 1 : ℕ) : ℝ) ≤ D := Nat.cast_le.mpr hlarge
    push_cast at hcast
    have hd : 1 / cgamma (θ 1) (θ' 1) ≤ (D : ℝ) - 1 := by linarith
    have hm := mul_le_mul_of_nonneg_left hd hγ.le
    rwa [mul_one_div_cancel hγ.ne'] at hm
  refine ⟨D, hD, hgD, ?_⟩
  have hq := extinction_lt_one_of_chain θ hθ0
  have hq' := extinction_lt_one_of_chain θ' hθ0'
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  have _ := isProbabilityMeasure_labelMeasure (N' := N') θ' hJN' hq'
  let μ := qPMF hθ1.le hθ1' (by omega : 2 ≤ D)
  refine Profile.infMatch_of_patterns P C C'
    (fun k hk => Profile.presentationFamily_tree P false hk)
    (fun k hk => Profile.presentationFamily_tree P true hk)
    (survivalMeasure θ) (labelMeasure θ')
    (fun w a => measurableSet_directChainLab_fibre D w a)
    (fun w k => fibreMeasurableG_gArityAt w k)
    (fun w a => measurableSet_directCrossLab_fibre (θ 1) (θ' 1) D w a)
    (fun w k => measurable_fst (fibreMeasurableG_gArityAt w k)) μ
    (fun F hpc a k hcomp => directChainPattern θ hJN hθ0 hθ1' hJ2 (by omega) F hpc a k hcomp)
    (fun F hpc a k hcomp => directCrossPattern θ' hJN' hθ0' hθ1'₀ hθ1'' hJ2' hθ1 hθ1'
      (by omega) hgD F hpc a k hcomp) ?_ ?_
    (GraphMatching.compat GraphMatching.pathGraph) 0 (ENNReal.ofReal δ) hfail
  · intro k hk
    have hk' : k ∈ reducedSupport θ := hk
    have hb := (Finset.mem_filter.mp hk').1
    exact (by have := Finset.mem_range.mp hb; omega : k ≤ J).trans hJN
  · intro k hk
    have hk' : k ∈ reducedSupport θ' := hk
    have hb := (Finset.mem_filter.mp hk').1
    exact (by have := Finset.mem_range.mp hb; omega : k ≤ J').trans hJN'

end ChainClasses
