import ChainClasses.Engine.ChainEngineBridge
import ChainClasses.Universality.BushyGeneral
import ChainClasses.Universality.DirectChainGeometry

/-! Chain universality from common atomic profiles for the original reduced laws.
The profiles and their core probabilities are fixed, while quantisation makes the label
defect arbitrarily small. Compatible original necks compare at scale proportional to D². -/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal Classical
open BranchingProcess (Offspring survivalMeasure sample)

variable {J J' N N' : ℕ}

/-- Arity bounds on the original reduced skeleton, almost surely. -/
theorem ae_reduced_skelBounded (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1) (hJ2 : 2 ≤ J) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, Profile.SkelBounded J (gArityAt c) := by
  refine ae_all_iff.mpr fun u => ?_
  rw [ae_iff]
  simpa only [gCompat_iff_mem_sample, Set.mem_ofPred_eq, Classical.not_imp] using
    survivalMeasure_compat_bad_null θ hJN hq hs1 hJ2 u

/-- The original chain sample has finite bare-neck pieces and bounded reduced arities. -/
theorem ae_direct_chain_good (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : θ 1 < 1) (hJ2 : 2 ≤ J) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, IsGBushySample c ∧ (∀ v, 1 ≤ c v) ∧
      Profile.SkelBounded J (gArityAt c) := by
  have hq := extinction_lt_one_of_chain θ hθ0
  have hs1 := chain_hs1 θ hθ0 hθ1
  filter_upwards [ae_isGBushySample θ hJN hq hs1, ae_forall_pos_of_zero θ hθ0,
    ae_reduced_skelBounded θ hJN hq hs1 hJ2] with c hc hpos hbound
  exact ⟨hc, hpos, hbound⟩

/-- Two bounded chain laws with the same branching semigroup yield almost surely
quasi-isometric independent samples. The proof uses their original reduced arity laws. -/
theorem chain_general_ae (θ : Offspring J) (hJN : J ≤ N) (hθ0 : θ 0 = 0)
    (hθ1 : 0 < θ 1) (hθ1' : θ 1 < 1) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hθ0' : θ' 0 = 0) (hθ1'₀ : 0 < θ' 1)
    (hθ1'' : θ' 1 < 1) (hJ2' : 2 ≤ J') (_hθJ' : 0 < θ' J')
    (hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ) =
      AddSubmonoid.closure (shiftSupp θ' : Set ℕ)) :
    ∀ᵐ cc ∂((survivalMeasure (N := N) θ).prod (survivalMeasure (N := N') θ')),
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample cc.1))
        (wordGraphN (· ∈ sample cc.2)) := by
  have : NeZero N := ⟨by omega⟩
  have : NeZero N' := ⟨by omega⟩
  have hq := extinction_lt_one_of_chain θ hθ0
  have hq' := extinction_lt_one_of_chain θ' hθ0'
  have := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  have := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  have := isProbabilityMeasure_labelMeasure (N' := N') θ' hJN' hq'
  have : IsProbabilityMeasure (directChainMeasure (N := N) (N' := N') θ θ') :=
    inferInstanceAs (IsProbabilityMeasure ((survivalMeasure (N := N) θ).prod
      (labelMeasure (N' := N') θ')))
  obtain ⟨C, C', hmatch⟩ := exists_direct_chain_match θ hJN hθ0 hθ1 hθ1' hJ2 hθJ θ'
    hJN' hθ0' hθ1'₀ hθ1'' hJ2' hsem
  have hgood : ∀ᵐ ω ∂directChainMeasure (N := N) (N' := N') θ θ',
      (IsGBushySample ω.1 ∧ (∀ v, 1 ≤ ω.1 v) ∧ Profile.SkelBounded J (gArityAt ω.1)) ∧
      (IsGBushySample ω.2.1 ∧ (∀ v, 1 ≤ ω.2.1 v) ∧ Profile.SkelBounded J' (gArityAt ω.2.1)) := by
    filter_upwards [ae_of_fst (ν := labelMeasure (N' := N') θ')
      (ae_direct_chain_good θ hJN hθ0 hθ1' hJ2),
      ae_of_snd (μ := survivalMeasure (N := N) θ)
        (ae_of_fst (ν := uniformField (GWord N'))
          (ae_direct_chain_good θ' hJN' hθ0' hθ1'' hJ2'))] with ω h1 h2
    exact ⟨h1, h2⟩
  have hqi : ∀ᵐ ω ∂directChainMeasure (N := N) (N' := N') θ θ',
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
        (wordGraphN (· ∈ sample ω.2.1)) := by
    rw [ae_iff]
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
    obtain ⟨D, hD, hgD, hb⟩ := hmatch ε hε
    let E := {ω : (GWord N → ℕ) × ((GWord N' → ℕ) × (GWord N' → ℝ)) |
      GraphMarkovMatching.InfMatch (GraphMatching.compat GraphMatching.pathGraph)
        (fun n => Profile.encodedStates C (directChainLab D ω.1) (gArityAt ω.1) 0 n)
        (fun n => Profile.encodedStates C' (directCrossLab (θ 1) (θ' 1) D ω.2)
          (gArityAt ω.2.1) 0 n)}
    have hEm : MeasurableSet E := Profile.measurableSet_infMatch _ _ _
      (fun n ω => Profile.restrict_encodedStates C _ _ 0 n)
      (fun n ω => Profile.restrict_encodedStates C' _ _ 0 n)
      (fun n => ((Profile.measurable_encodedStates
        (fun w a => measurableSet_directChainLab_fibre D w a)
        (fun w k => fibreMeasurableG_gArityAt w k) C 0 n).comp measurable_fst).prodMk
        ((Profile.measurable_encodedStates
          (fun w a => measurableSet_directCrossLab_fibre (θ 1) (θ' 1) D w a)
          (fun w k => measurable_fst (fibreMeasurableG_gArityAt w k)) C' 0 n).comp measurable_snd))
    have hfail : directChainMeasure (N := N) (N' := N') θ θ' Eᶜ ≤ ENNReal.ofReal ε := by
      rw [prob_compl_eq_one_sub hEm]
      exact tsub_le_iff_right.mpr (by simpa only [add_comm] using tsub_le_iff_right.mp hb)
    have hsub : {ω : (GWord N → ℕ) × ((GWord N' → ℕ) × (GWord N' → ℝ)) |
        ¬ BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
          (wordGraphN (· ∈ sample ω.2.1))} ⊆ Eᶜ ∪
        {ω | ¬ ((IsGBushySample ω.1 ∧ (∀ v, 1 ≤ ω.1 v) ∧ Profile.SkelBounded J (gArityAt ω.1)) ∧
          (IsGBushySample ω.2.1 ∧ (∀ v, 1 ≤ ω.2.1 v) ∧ Profile.SkelBounded J' (gArityAt ω.2.1)))} := by
      intro ω hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not] at hcon
      obtain ⟨hm, ⟨hc, hp, hs⟩, ⟨hc', hp', hs'⟩⟩ := hcon
      obtain ⟨F, hF⟩ := sample_qi_of_direct_chain_match C C' hc hc' hp hp' hs hs'
        (by omega) (by omega) hθ1 hθ1' hθ1'₀ hθ1'' (by omega) hgD ω.2.2 hm
      exact hω ⟨_, F, hF⟩
    calc directChainMeasure (N := N) (N' := N') θ θ' _
      ≤ directChainMeasure (N := N) (N' := N') θ θ' (Eᶜ ∪ _) := measure_mono hsub
      _ ≤ directChainMeasure (N := N) (N' := N') θ θ' Eᶜ +
          directChainMeasure (N := N) (N' := N') θ θ' _ := measure_union_le _ _
      _ = directChainMeasure (N := N) (N' := N') θ θ' Eᶜ + 0 := by rw [ae_iff.mp hgood]
      _ ≤ ENNReal.ofReal ε := by simpa using hfail
      _ = 0 + (ε : ℝ≥0∞) := by simp
  exact ae_prod_fst_of_triple (μ := survivalMeasure (N := N) θ)
    (ν := survivalMeasure (N := N') θ') (τ := uniformField (GWord N')) hqi

end ChainClasses
