import ChainClasses.Engine.ReducedProfiles
import ChainClasses.General.GeneralLabelField
import ChainClasses.General.GeneralShapeEta
import GraphMarkovMatching.Stopped.Exponent

/-! Product laws and almost-sure support on the original reduced skeleton. -/

namespace ChainClasses
open MeasureTheory
open scoped ENNReal Classical
open BranchingProcess (Offspring survivalMeasure)
variable {J N J' N' : ℕ}

lemma gClassMass_eq_gClassPMF (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) (D : ℝ) (a : ℕ) :
    gClassMass (N := N) θ D a = gClassPMF θ hJN hq hq0 hs1 D a := by
  rw [gClassMass_eq_tsum_ite, gClassPMF_eq_tsum]
  rfl

/-! ### Arities at compatible addresses -/

/-- An address is compatible with a sample when every letter on the way lies below the
arity of its parent. -/
def GCompat (c : GWord N' → ℕ) : GWord N' → Prop
  | [] => True
  | i :: u => (i : ℕ) < gArity c ∧ GCompat (gSplitBush c (i : ℕ)) u

/-- Compatibility in terms of the arity field: every letter of the address lies below the
arity at its parent. -/
lemma gCompat_iff : ∀ (w : GWord N') (c : GWord N' → ℕ), GCompat c w ↔
    ∀ (p : GWord N') (i : Fin N'), p ++ [i] <+: w → (i : ℕ) < gArityAt c p
  | [], c => by
      simp only [GCompat, true_iff]
      intro p i h
      rw [List.prefix_nil] at h
      exact absurd h (by simp)
  | i :: w, c => by
      simp only [GCompat]
      constructor
      · rintro ⟨h1, h2⟩ p i' hpi
        cases p with
        | nil =>
            rw [List.nil_append, List.cons_prefix_cons] at hpi
            rw [hpi.1, gArityAt_nil]
            exact h1
        | cons i'' p' =>
            rw [List.cons_append, List.cons_prefix_cons] at hpi
            rw [hpi.1, gArityAt_cons]
            exact (gCompat_iff w (gSplitBush c (i : ℕ))).mp h2 p' i' hpi.2
      · intro H
        refine ⟨?_, ?_⟩
        · have := H [] i (by simp)
          rwa [gArityAt_nil] at this
        · refine (gCompat_iff w (gSplitBush c (i : ℕ))).mpr fun p' i' hpi => ?_
          have := H (i :: p') i' (by rw [List.cons_append]; exact List.cons_prefix_cons.mpr ⟨rfl, hpi⟩)
          rwa [gArityAt_cons] at this

lemma measurableSet_gCompat : ∀ w : GWord N', MeasurableSet {c : GWord N' → ℕ | GCompat c w}
  | [] => by
      have : {c : GWord N' → ℕ | GCompat c []} = Set.univ := by
        ext c
        simp [GCompat]
      rw [this]
      exact MeasurableSet.univ
  | i :: w => by
      have : {c : GWord N' → ℕ | GCompat c (i :: w)}
          = {c : GWord N' → ℕ | gArity c ∈ {k : ℕ | (i : ℕ) < k}}
            ∩ (fun c : GWord N' → ℕ => gSplitBush c (i : ℕ)) ⁻¹' {d | GCompat d w} := by
        ext c
        simp [GCompat]
      rw [this]
      exact (fibreMeasurableG_gArity.preimage _).inter
        (measurable_gSplitBush (i : ℕ) (measurableSet_gCompat w))

/-- The arity at the root lies in the reduced support almost surely. -/
lemma survivalMeasure_gArity_bad_null (θ' : Offspring J') (hJN' : J' ≤ N')
    (hq' : θ'.extinction < 1) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') :
    survivalMeasure (N := N') θ' {c : GWord N' → ℕ | ¬ (2 ≤ gArity c ∧ gArity c ≤ J')} = 0 := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  have h1 : survivalMeasure (N := N') θ' {c : GWord N' → ℕ | 2 ≤ gArity c}ᶜ = 0 :=
    (prob_compl_eq_zero_iff (fibreMeasurableG_gArity.preimage {k : ℕ | 2 ≤ k})).mpr
      (survivalMeasure_two_le_gArity θ' hJN' hq' hs1')
  have h2 : survivalMeasure (N := N') θ'
      (⋃ j : ℕ, {c : GWord N' → ℕ | gArity c = J' + 1 + j}) = 0 := by
    refine measure_iUnion_null fun j => ?_
    rw [survivalMeasure_gArity_eq θ' hJN' hq' hs1' (by omega),
      reducedWeight_eq_zero_of_gt θ' (by omega), ENNReal.ofReal_zero]
  refine measure_mono_null (fun c hc => ?_) (measure_union_null h1 h2)
  simp only [Set.mem_ofPred_eq] at hc
  by_cases h2' : 2 ≤ gArity c
  · right
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨gArity c - J' - 1, by omega⟩
  · left
    exact h2'

/-- **The arities at compatible addresses lie in the reduced support almost surely.** -/
theorem survivalMeasure_compat_bad_null (θ' : Offspring J') (hJN' : J' ≤ N')
    (hq' : θ'.extinction < 1) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') :
    ∀ w : GWord N', survivalMeasure (N := N') θ'
      {c : GWord N' → ℕ | GCompat c w ∧ ¬ (2 ≤ gArityAt c w ∧ gArityAt c w ≤ J')} = 0 := by
  have hroot := survivalMeasure_gArity_bad_null θ' hJN' hq' hs1' hJ2'
  intro w
  induction w with
  | nil =>
      simpa [GCompat] using hroot
  | cons i w ih =>
      set S : Set (GWord N' → ℕ) :=
        {d | GCompat d w ∧ ¬ (2 ≤ gArityAt d w ∧ gArityAt d w ≤ J')} with hS
      have hSm : MeasurableSet S := (measurableSet_gCompat w).inter
        ((fibreMeasurableG_gArityAt w).preimage {k : ℕ | ¬ (2 ≤ k ∧ k ≤ J')})
      set A : ℕ → Set (GWord N' → ℕ) := fun m => if m = (i : ℕ) then S else Set.univ with hA
      have hAm : ∀ m, MeasurableSet (A m) := fun m => by
        simp only [hA]
        split_ifs
        · exact hSm
        · exact MeasurableSet.univ
      set B : ℕ → Set (GWord N' → ℕ) := fun κ =>
        if (i : ℕ) < κ then {c : GWord N' → ℕ | gArity c = κ}
          ∩ {c : GWord N' → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m} else ∅ with hB
      have hBnull : ∀ κ, survivalMeasure (N := N') θ' (B κ) = 0 := by
        intro κ
        simp only [hB]
        split_ifs with hiκ
        · by_cases hκ2 : 2 ≤ κ
          · rw [survivalMeasure_gArityPair θ' hJN' hq' hs1' hκ2 hAm,
              Finset.prod_eq_zero (Finset.mem_range.mpr hiκ) (by
                simp only [hA, ite_eq_left rfl]
                exact ih), mul_zero]
          · refine measure_mono_null (fun c hc => ?_) hroot
            simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hc ⊢
            omega
        · exact measure_empty
      refine measure_mono_null (fun c hc => ?_) (measure_iUnion_null hBnull)
      simp only [Set.mem_ofPred_eq, GCompat, gArityAt_cons] at hc
      obtain ⟨⟨hi, hcomp⟩, hbad⟩ := hc
      simp only [Set.mem_iUnion]
      refine ⟨gArity c, ?_⟩
      simp only [hB, ite_eq_left hi, Set.mem_inter_iff, Set.mem_ofPred_eq]
      refine ⟨by trivial, fun m _ => ?_⟩
      simp only [hA]
      split_ifs with hmi
      · subst hmi
        exact ⟨hcomp, hbad⟩
      · exact Set.mem_univ _

/-- The same on the labelled space. -/
lemma labelMeasure_compat_bad_null (θ' : Offspring J') (hJN' : J' ≤ N')
    (hq' : θ'.extinction < 1) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J') (w : GWord N') :
    labelMeasure θ' {ω : (GWord N' → ℕ) × (GWord N' → ℝ) |
      GCompat ω.1 w ∧ ¬ (2 ≤ gArityAt ω.1 w ∧ gArityAt ω.1 w ≤ J')} = 0 := by
  have hset : {ω : (GWord N' → ℕ) × (GWord N' → ℝ) |
        GCompat ω.1 w ∧ ¬ (2 ≤ gArityAt ω.1 w ∧ gArityAt ω.1 w ≤ J')}
      = {c : GWord N' → ℕ | GCompat c w ∧ ¬ (2 ≤ gArityAt c w ∧ gArityAt c w ≤ J')}
          ×ˢ (Set.univ : Set (GWord N' → ℝ)) := by
    ext ω
    simp
  rw [hset, labelMeasure, Measure.prod_prod,
    survivalMeasure_compat_bad_null θ' hJN' hq' hs1' hJ2' w, zero_mul]


theorem labelMeasure_label_pattern' (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') {D : ℝ} (π : GCouplings θ')
    (hπ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
      IsGShapeCoupling D (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν) (gMixPMF θ hJN hq hq0 hs1)
        (π κ hκ hν))
    (F : Finset (GWord N')) (hpc : ∀ u ∈ F, ∀ p : GWord N', p <+: u → p ∈ F)
    (a k : GWord N' → ℕ) (hcomp : ∀ u ∈ F, ∀ i : Fin N', u ++ [i] ∈ F → (i : ℕ) < k u) :
    labelMeasure θ'
        (⋂ u ∈ F, ({ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gLab D π ω u = a u}
          ∩ {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gArityAt ω.1 u = k u}))
      = ∏ u ∈ F, gClassPMF θ hJN hq hq0 hs1 D (a u) * reducedPMF θ' hq' hs1' hJ2' (k u) := by
  by_cases hall : ∀ u ∈ F, 2 ≤ k u ∧ k u ≤ J'
  · rw [labelMeasure_label_pattern θ hJN hq hq0 hs1 θ' hJN' hq' hq0' hs1' hJ2' hθJ' π hπ F hpc
      a k (fun u hu => (hall u hu).1) (fun u hu => (hall u hu).2) hcomp,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [gClassMass_eq_gClassPMF, reducedPMF_of_le θ' hq' hs1' hJ2' (hall u hu).1]
  · simp only [not_forall] at hall
    obtain ⟨t, ht, hbad⟩ := hall
    rw [Finset.prod_eq_zero ht (by rw [reducedPMF_eq_zero θ' hq' hs1' hJ2' hbad, mul_zero])]
    refine measure_mono_null ?_ (labelMeasure_compat_bad_null θ' hJN' hq' hs1' hJ2' t)
    intro ω hω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq] at hω
    refine ⟨?_, ?_⟩
    · rw [gCompat_iff]
      intro p i hpi
      have hmem : p ++ [i] ∈ F := hpc t ht _ hpi
      have hp : p ∈ F := hpc _ hmem p (List.prefix_append _ _)
      rw [(hω p hp).2]
      exact hcomp p hp i hmem
    · rw [(hω t ht).2]
      exact hbad


lemma etaG_compat_eq {V : Type} (μ : PMF V) (G : SimpleGraph V) :
    GraphMarkovMatching.etaG (5 / 2) (GraphMatching.compat G) μ = GraphMatching.etaG μ G := by
  rw [GraphMatching.etaG_eq_etaGA, GraphMatching.etaGA_eq_PhiA, GraphMarkovMatching.etaG,
    GraphMarkovMatching.PhiD, GraphMatching.PhiA]
  refine tsum_congr fun x => ?_
  by_cases hx : μ x = 0
  · rw [hx, zero_mul, zero_mul]
  · have hq : GraphMarkovMatching.Support.q μ (GraphMatching.compat G) x < 1 :=
      GraphMarkovMatching.Support.q_lt_one (GraphMatching.compat_refl G x) hx
    rw [GraphMarkovMatching.phiE_of_lt hq]
    rfl


noncomputable def twoLabelMeasure (θ : Offspring J) (θ' : Offspring J') :
    Measure (((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ))) :=
  (labelMeasure (N' := N) θ).prod (labelMeasure (N' := N') θ')

lemma isProbabilityMeasure_twoLabelMeasure (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1) :
    IsProbabilityMeasure (twoLabelMeasure (N := N) (N' := N') θ θ') := by
  have _ := isProbabilityMeasure_labelMeasure (N' := N) θ hJN hq
  have _ := isProbabilityMeasure_labelMeasure (N' := N') θ' hJN' hq'
  exact inferInstanceAs (IsProbabilityMeasure
    ((labelMeasure (N' := N) θ).prod (labelMeasure (N' := N') θ')))


end ChainClasses
