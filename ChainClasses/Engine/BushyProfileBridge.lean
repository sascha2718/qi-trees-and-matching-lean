import ChainClasses.Engine.SkeletonPatterns
import ChainClasses.Engine.ProfileMatching

/-! The direct bushy application: both reduced laws charge two, and every balanced
profile uses this same binary core. No relation between the two offspring bounds is needed. -/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal Classical
open BranchingProcess (Offspring survivalMeasure)
open GraphMarkovMatching.Stopped

noncomputable def balancedFamily : Profile.Family where
  tree := BinaryProfiles.balanced
  leaves k hk := by rw [BinaryProfiles.balanced_leaves, max_eq_left hk]
  root k := by
    obtain ⟨l, r, h⟩ := BinaryProfiles.balanced_gnode k
    exact ⟨l, r, Or.inr h⟩

variable {J J' N N' : ℕ}

/-- For arbitrary bounded bushy laws, one automorphism matches the encoded labels with
failure probability exponentially small in the shape scale. -/
theorem exists_profile_match (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (h0 : 0 < θ 0) (hθJ : 0 < θ J) (hJ2 : 2 ≤ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hθJ' : 0 < θ' J')
    (hJ2' : 2 ≤ J') :
    ∃ (D₆ : ℕ) (K c : ℝ), 0 < c ∧ ∀ D : ℕ, D₆ ≤ D →
      ∀ (π₁ : GCouplings θ)
        (_ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ κ),
          IsGShapeCoupling (D : ℝ) (gCondPMF θ hJN hq hq0 hs1 hκ hν) (gMixPMF θ hJN hq hq0 hs1)
            (π₁ κ hκ hν))
        (π₂ : GCouplings θ')
        (_ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
          IsGShapeCoupling (D : ℝ) (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν)
            (gMixPMF θ hJN hq hq0 hs1) (π₂ κ hκ hν)),
        1 - ENNReal.ofReal (K * Real.exp (-(c * (D : ℝ) ^ 2))) ≤
          twoLabelMeasure (N := N) (N' := N') θ θ'
            {ω | GraphMarkovMatching.InfMatch (GraphMatching.compat (gNetGraph D))
              (fun n => Profile.encodedStates balancedFamily (gLab D π₁ ω.1) (gArityAt ω.1.1) 0 n)
              (fun n => Profile.encodedStates balancedFamily (gLab D π₂ ω.2) (gArityAt ω.2.1) 0 n)} := by
  let ν1 := reducedPMF θ hq hs1 hJ2
  let ν2 := reducedPMF θ' hq' hs1' hJ2'
  have hsup1 : ∀ k, ν1 k ≠ 0 ↔ k ∈ Finset.Icc 2 J := fun k => by
    simpa only [Finset.mem_Icc] using reducedPMF_ne_zero_iff θ hq hq0 hs1 hJ2 hθJ k
  have hsup2 : ∀ k, ν2 k ≠ 0 ↔ k ∈ Finset.Icc 2 J' := fun k => by
    simpa only [Finset.mem_Icc] using reducedPMF_ne_zero_iff θ' hq' hq0' hs1' hJ2' hθJ' k
  let P := BinaryProfiles.presentation ν1 ν2 (Finset.Icc 2 J) (Finset.Icc 2 J') hsup1 hsup2
    (fun _ hk => (Finset.mem_Icc.mp hk).1) (fun _ hk => (Finset.mem_Icc.mp hk).1)
    (Finset.mem_Icc.mpr ⟨le_rfl, hJ2⟩) (Finset.mem_Icc.mpr ⟨le_rfl, hJ2'⟩)
  obtain ⟨c0, hc0, hc1, hfloor⟩ := P.exists_floor
  obtain ⟨K, ε, hε, hmatch⟩ := P.presentation_matching_eta_exists paramsFiveHalf hc0 hc1 hfloor
    (p0 := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨c, hc, D₀, hD₀⟩ := exists_etaG_gNetGraph_le θ hJN hq hq0 hs1 h0 hθJ hJ2
  obtain ⟨D₁, hD₁⟩ := exists_etaG_gNetGraph_le_ofReal θ hJN hq hq0 hs1 h0 hθJ hJ2 hε
  refine ⟨max D₀ D₁, max K 0, c, hc, fun D hD π₁ hπ₁ π₂ hπ₂ => ?_⟩
  obtain ⟨heta_exp, -⟩ := hD₀ D (le_trans (le_max_left _ _) hD)
  obtain ⟨-, heta_r, hhalf⟩ := hD₁ D (le_trans (le_max_right _ _) hD)
  let μ := gClassPMF θ hJN hq hq0 hs1 D
  let R := GraphMatching.compat (gNetGraph D)
  have hcompat : (P.toModel R 0 μ).IsCompat :=
    ⟨GraphMatching.compat_refl _, GraphMatching.compat_symm _⟩
  have heta : (P.toModel R 0 μ).eta paramsFiveHalf.α = GraphMatching.etaG μ (gNetGraph D) := by
    rw [paramsFiveHalf_α]
    exact etaG_compat_eq μ (gNetGraph D)
  have hhalf' : ENNReal.ofReal (1 / 2 : ℝ) ≤ μ 0 := by simpa using hhalf
  have hf : ∀ n, (P.toModel R 0 μ).failProb (P.freshL false) (P.freshL true) n ≤
      ENNReal.ofReal (max K 0 * Real.exp (-(c * (D : ℝ) ^ 2))) := by
    intro n
    have hb := hmatch R 0 μ hcompat hhalf' (by rw [heta]; exact heta_r) false true n
    rw [heta] at hb
    calc _ ≤ ENNReal.ofReal K * GraphMatching.etaG μ (gNetGraph D) := hb
      _ ≤ ENNReal.ofReal (max K 0) * ENNReal.ofReal (Real.exp (-(c * (D : ℝ) ^ 2))) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) heta_exp
      _ = _ := (ENNReal.ofReal_mul (le_max_right _ _)).symm
  have _ := isProbabilityMeasure_labelMeasure (N' := N) θ hJN hq
  have _ := isProbabilityMeasure_labelMeasure (N' := N') θ' hJN' hq'
  exact Profile.infMatch_of_patterns P balancedFamily balancedFamily
    (fun _ _ => rfl) (fun _ _ => rfl) (labelMeasure θ) (labelMeasure θ')
    (fun w a => measurableSet_gLab_fibre D π₁ w a)
    (fun w k => measurable_fst (fibreMeasurableG_gArityAt w k))
    (fun w a => measurableSet_gLab_fibre D π₂ w a)
    (fun w k => measurable_fst (fibreMeasurableG_gArityAt w k)) μ
    (fun F hpc a k hcomp => labelMeasure_label_pattern' θ hJN hq hq0 hs1 θ hJN hq hq0 hs1
      hJ2 hθJ π₁ hπ₁ F hpc a k hcomp)
    (fun F hpc a k hcomp => labelMeasure_label_pattern' θ hJN hq hq0 hs1 θ' hJN' hq' hq0' hs1'
      hJ2' hθJ' π₂ hπ₂ F hpc a k hcomp)
    (fun _ hk => (Finset.mem_Icc.mp hk).2.trans hJN)
    (fun _ hk => (Finset.mem_Icc.mp hk).2.trans hJN') R 0 _ hf

end ChainClasses
