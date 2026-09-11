import ChainClasses.Engine.BushyProfileBridge
import ChainClasses.Engine.ProfileGeometry

/-! Direct universality for arbitrary bounded bushy offspring laws. The common binary
profiles and the stopped Markov theorem apply to the original reduced arity laws. -/

namespace ChainClasses
open MeasureTheory
open scoped ENNReal Classical
open BranchingProcess (Offspring survivalMeasure sample Survives skeletonDegree bushAt)
open GraphMarkovMatching.Support (FullLab restrictLab AutK restrictAutK fullMatchesK InfMatchK)
open Profile

variable {N N' : ℕ}

lemma measurable_profile_encoding (D : ℝ) {J : ℕ} {θ : Offspring J} (π : GCouplings θ)
    (C : Profile.Family) (v0 n : ℕ) :
    Measurable fun ω : (GWord N' → ℕ) × (GWord N' → ℝ) =>
      Profile.encodedStates C (gLab D π ω) (gArityAt ω.1) v0 n :=
  Profile.measurable_encodedStates (fun w a => measurableSet_gLab_fibre D π w a)
    (fun w k => measurable_fst (fibreMeasurableG_gArityAt w k)) C v0 n

section AlmostSure

variable {J J' : ℕ}

/-- **The shift to a subtree preserves the sample law.** -/
lemma map_ambSub (θ : Offspring J) : ∀ v : GWord N,
    (BranchingProcess.sampleMeasure (N := N) θ).map (fun c => ambSub c v)
      = BranchingProcess.sampleMeasure (N := N) θ
  | [] => by
      have h : (fun c : GWord N → ℕ => ambSub c []) = id := by
        funext c
        exact ambSub_nil c
      rw [h, Measure.map_id]
  | i :: v => by
      have h : (fun c : GWord N → ℕ => ambSub c (i :: v))
          = (fun c => ambSub c v) ∘ (fun c w => c (i :: w)) := by
        funext c w
        rfl
      rw [h, ← Measure.map_map (measurable_ambSub v) (BranchingProcess.measurable_shift i),
        BranchingProcess.map_shift, map_ambSub θ v]

/-- A null event of the conditioned law is null at every surviving subtree. -/
lemma survivalMeasure_ambSub_null (θ : Offspring J) {S : Set (GWord N → ℕ)}
    (hS : survivalMeasure (N := N) θ S = 0) (v : GWord N) :
    survivalMeasure (N := N) θ {c | Survives (ambSub c v) ∧ ambSub c v ∈ S} = 0 := by
  have hP : BranchingProcess.sampleMeasure (N := N) θ ({c | Survives c} ∩ S) = 0 := by
    rw [BranchingProcess.survivalMeasure_apply] at hS
    rcases mul_eq_zero.mp hS with h | h
    · exact absurd h (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    · exact h
  have hP' : BranchingProcess.sampleMeasure (N := N) θ
      {c | Survives (ambSub c v) ∧ ambSub c v ∈ S} = 0 := by
    refine le_antisymm ?_ bot_le
    calc BranchingProcess.sampleMeasure (N := N) θ {c | Survives (ambSub c v) ∧ ambSub c v ∈ S}
        = BranchingProcess.sampleMeasure (N := N) θ
            ((fun c => ambSub c v) ⁻¹' ({c | Survives c} ∩ S)) := rfl
      _ ≤ (BranchingProcess.sampleMeasure (N := N) θ).map (fun c => ambSub c v)
            ({c | Survives c} ∩ S) :=
          Measure.le_map_apply (measurable_ambSub v).aemeasurable _
      _ = 0 := by rw [map_ambSub, hP]
  exact ProbabilityTheory.cond_absolutelyContinuous hP'

/-- **A conditioned sample is hairy almost surely**: its offspring counts lie within the
alphabet, it survives, and every neck ray below a surviving vertex meets a split. -/
theorem ae_isGHairySample (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, IsGHairySample c := by
  have h1 : ∀ᵐ c ∂survivalMeasure (N := N) θ, ∀ v, c v ≤ N := by
    refine ae_all_iff.mpr fun v => ?_
    rw [ae_iff]
    have := BranchingProcess.survivalMeasure_coord_gt θ hJN v
    simpa [not_le] using this
  have h2 := ae_survives θ hJN hq
  have hsplit : survivalMeasure (N := N) θ {d | ¬ ∃ n, 2 ≤ skeletonDegree (neckIter d n)} = 0 := by
    refine measure_mono_null (fun d hd => ?_) (ae_iff.mp (ae_gArity_ge_two θ hJN hq hs1))
    simp only [Set.mem_setOf_eq, not_exists, not_le] at hd ⊢
    by_contra h2
    obtain ⟨n, hn⟩ := splitSet_nonempty_of_arity (not_lt.mp h2)
    exact absurd hn (not_le.mpr (hd n))
  have h3 : ∀ᵐ c ∂survivalMeasure (N := N) θ, ∀ v, Survives (ambSub c v) →
      ∃ n, 2 ≤ skeletonDegree (neckIter (ambSub c v) n) := by
    refine ae_all_iff.mpr fun v => ?_
    rw [ae_iff]
    have := survivalMeasure_ambSub_null θ hsplit v
    simpa [Set.mem_setOf_eq, Classical.not_imp] using this
  filter_upwards [h1, h2, h3] with c hc1 hc2 hc3
  exact ⟨hc1, hc2, hc3⟩

/-- Compatibility with a sample is membership in the reduced skeleton. -/
lemma gCompat_iff_mem_sample (c : GWord N → ℕ) (w : GWord N) :
    GCompat c w ↔ w ∈ sample (gArityAt c) := by
  rw [gCompat_iff, mem_sample_iff_prefix]

/-- **The skeleton is well formed almost surely**: every arity lies in `{2, …, J'}` and
every shape has positive conditional mass at its arity. -/
theorem ae_skeleton_good (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hJ2' : 2 ≤ J') (hθJ' : 0 < θ' J') :
    ∀ᵐ c ∂survivalMeasure (N := N') θ', ∀ u, u ∈ sample (gArityAt c) →
      (2 ≤ gArityAt c u ∧ gArityAt c u ≤ J') ∧
        gCondMass (N := N') θ' (gArityAt c u) (gShapeAt c u) ≠ 0 := by
  have hs1' : θ'.skeletonWeight 1 < 1 := skeletonWeight_one_lt_one_of θ' hq' hq0' hJ2' hθJ'
  refine ae_all_iff.mpr fun u => ?_
  rw [ae_iff]
  -- the probe: the prefixes of `u`
  set F : Finset (GWord N') := u.inits.toFinset with hF
  have hmemF : ∀ p, p ∈ F ↔ p <+: u := fun p => by
    rw [hF, List.mem_toFinset, List.mem_inits]
  have huF : u ∈ F := (hmemF u).mpr (List.prefix_refl u)
  have hpc : ∀ p ∈ F, ∀ q : GWord N', q <+: p → q ∈ F := fun p hp q hq =>
    (hmemF q).mpr (hq.trans ((hmemF p).mp hp))
  -- the patterns of shapes and arities over the probe
  let ext : (↥F → GShape × ℕ) → (GWord N' → GShape) × (GWord N' → ℕ) := fun g =>
    (fun p => if h : p ∈ F then (g ⟨p, h⟩).1 else gOne,
      fun p => if h : p ∈ F then (g ⟨p, h⟩).2 else 0)
  let Good : (↥F → GShape × ℕ) → Prop := fun g =>
    (∀ p : ↥F, 2 ≤ (g p).2 ∧ (g p).2 ≤ J') ∧
      (∀ (p : ↥F) (i : Fin N'), (p : GWord N') ++ [i] ∈ F → (i : ℕ) < (g p).2) ∧
      gCondMass (N := N') θ' (g ⟨u, huF⟩).2 (g ⟨u, huF⟩).1 = 0
  let A : (↥F → GShape × ℕ) → Set (GWord N' → ℕ) := fun g =>
    ⋂ p ∈ F, ({c : GWord N' → ℕ | gShapeAt c p = (ext g).1 p}
      ∩ {c : GWord N' → ℕ | gArityAt c p = (ext g).2 p})
  have hA : ∀ g, Good g → survivalMeasure (N := N') θ' (A g) = 0 := by
    intro g hg
    have hext1 : ∀ p : ↥F, (ext g).1 p = (g p).1 := fun p => by
      simp only [ext, dif_pos p.2]
    have hext2 : ∀ p : ↥F, (ext g).2 p = (g p).2 := fun p => by
      simp only [ext, dif_pos p.2]
    rw [conditional_iid θ' hJN' hq' hq0' hJ2' hθJ' F hpc (ext g).1 (ext g).2
      (fun p hp => by rw [hext2 ⟨p, hp⟩]; exact (hg.1 ⟨p, hp⟩).1)
      (fun p hp => by rw [hext2 ⟨p, hp⟩]; exact (hg.1 ⟨p, hp⟩).2)
      (fun p hp i hpi => by rw [hext2 ⟨p, hp⟩]; exact hg.2.1 ⟨p, hp⟩ i hpi)]
    rw [Finset.prod_eq_zero huF, zero_mul]
    rw [hext1 ⟨u, huF⟩, hext2 ⟨u, huF⟩]
    exact hg.2.2
  have hN1 : survivalMeasure (N := N') θ' (⋃ p ∈ F, {c : GWord N' → ℕ |
      GCompat c p ∧ ¬ (2 ≤ gArityAt c p ∧ gArityAt c p ≤ J')}) = 0 :=
    measure_biUnion_null_iff F.countable_toSet |>.mpr fun p _ =>
      survivalMeasure_compat_bad_null θ' hJN' hq' hs1' hJ2' p
  have hN2 : survivalMeasure (N := N') θ' (⋃ (g : ↥F → GShape × ℕ) (_ : Good g), A g) = 0 :=
    measure_iUnion_null fun g => measure_iUnion_null fun hg => hA g hg
  refine measure_mono_null (fun c hc => ?_) (measure_union_null hN1 hN2)
  simp only [Set.mem_setOf_eq, Classical.not_imp] at hc
  obtain ⟨hu, hbad⟩ := hc
  rw [not_and, not_not] at hbad
  by_cases hrange : ∀ p ∈ F, 2 ≤ gArityAt c p ∧ gArityAt c p ≤ J'
  · right
    refine Set.mem_iUnion.mpr ⟨fun p => (gShapeAt c p, gArityAt c p), Set.mem_iUnion.mpr
      ⟨⟨fun p => hrange p p.2, fun p i hpi => ?_, hbad (hrange u huF)⟩, ?_⟩⟩
    · have := (mem_sample_iff_prefix u).mp hu p i ((hmemF _).mp hpi)
      exact this
    · simp only [A, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, ext]
      intro p hp
      simp only [dif_pos hp, and_self]
  · left
    push Not at hrange
    obtain ⟨p, hp, hpbad⟩ := hrange
    refine Set.mem_biUnion hp ⟨?_, fun h => absurd (hpbad h.1) (not_lt.mpr h.2)⟩
    rw [gCompat_iff_mem_sample]
    exact BranchingProcess.Subtree.mem_of_prefix ((hmemF p).mp hp) hu

/-- **The uniform field lies in `[0,1)` at every index almost surely.** -/
lemma ae_uniform_mem_Ico (ι : Type*) [Countable ι] :
    ∀ᵐ U ∂uniformField ι, ∀ u, U u ∈ Set.Ico (0 : ℝ) 1 := by
  refine ae_all_iff.mpr fun u => ?_
  rw [ae_iff]
  have h : {U : ι → ℝ | ¬ U u ∈ Set.Ico (0 : ℝ) 1}
      = (BranchingProcess.coord u : (ι → ℝ) → ℝ) ⁻¹' (Set.Ico (0 : ℝ) 1)ᶜ := rfl
  rw [h, uniformField, BranchingProcess.coord_law _ u measurableSet_Ico.compl,
    Measure.restrict_apply measurableSet_Ico.compl, Set.compl_inter_self, measure_empty]

/-- The draw of an atom by a uniform variable in `[0,1)` lands in the support. -/
lemma drawBy_ne_zero {T : Type*} [Encodable T] (ν : PMF T) {r : ℝ}
    (hr : r ∈ Set.Ico (0 : ℝ) 1) : ν (drawBy ν r) ≠ 0 := by
  have h := (drawBy_eq_iff ν hr (drawBy ν r)).mp rfl
  have h2 := (drawNat_eq_iff (tsum_encMass ν) hr).mp h
  rw [cumMass_succ (tsum_encMass ν), encMass_encode] at h2
  intro h0
  rw [h0, ENNReal.toReal_zero, add_zero] at h2
  exact absurd h2.2 (not_lt.mpr h2.1)

/-- The conditional draw by a uniform variable in `[0,1)` lands in the support of the
coupling, once the condition carries mass. -/
lemma condDraw_ne_zero {T : Type*} [Encodable T] (π : PMF (T × T)) {σ : T}
    (h : margFstT π σ ≠ 0) {r : ℝ} (hr : r ∈ Set.Ico (0 : ℝ) 1) :
    π (σ, condDraw π σ r) ≠ 0 := by
  rw [condDraw, dif_pos h]
  have := drawBy_ne_zero (condPMF π σ h) hr
  rw [condPMF_apply] at this
  intro h0
  apply this
  rw [h0, ENNReal.zero_div]

/-- **Every partner is comparable to its shape almost surely**: on the labelled space the
pair of the shape and its partner lies in the support of the coupling at every skeleton
vertex, so `thm:relabel` makes them `9D³`-comparable. -/
theorem ae_partner_comparable (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') {D : ℝ} (π : GCouplings θ')
    (hπ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
      IsGShapeCoupling D (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν) (gMixPMF θ hJN hq hq0 hs1)
        (π κ hκ hν)) :
    ∀ᵐ ω ∂labelMeasure (N' := N') θ', ∀ u, u ∈ sample (gArityAt ω.1) →
      MarkedQI (9 * D ^ 3) (gShapeSpace (gShapeAt ω.1 u)) (gShapeSpace (gPartner π ω u)) := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  filter_upwards [ae_of_fst (ν := uniformField (GWord N'))
      (ae_skeleton_good θ' hJN' hq' hq0' hJ2' hθJ'),
    ae_of_snd (μ := survivalMeasure (N := N') θ') (ae_uniform_mem_Ico (GWord N'))] with ω h1 h2
  intro u hu
  obtain ⟨⟨hκ2, hκJ⟩, hmass⟩ := h1 u hu
  have hν : 0 < reducedWeight θ' (gArityAt ω.1 u) :=
    reducedWeight_pos θ' hq' hq0' hJ2' hθJ' hκ2 hκJ
  have hdraw : gPartner π ω u
      = condDraw (π (gArityAt ω.1 u) hκ2 hν) (gShapeAt ω.1 u) (ω.2 u) := by
    rw [gPartner, gDraw, dif_pos ⟨hκ2, hν⟩]
  have hmarg : margFstT (π (gArityAt ω.1 u) hκ2 hν) (gShapeAt ω.1 u) ≠ 0 := by
    rw [(hπ _ hκ2 hν).marg₁, gCondPMF_apply]
    exact hmass
  rw [hdraw]
  exact (hπ _ hκ2 hν).qi _ (condDraw_ne_zero _ hmarg (h2 u))

end AlmostSure

/-! ### The rate and the almost sure statement for arbitrary bounded supports -/

section Rate

variable {J J' : ℕ}

/-- **The matching event is measurable**: the intersection over the heights of the
preimages of countable sets. -/
lemma measurableSet_engine_match (θ : Offspring J) (θ' : Offspring J') {D : ℝ}
    (π₁ : GCouplings θ) (π₂ : GCouplings θ') (exc1 exc2 : Profile.Family) :
    MeasurableSet {ω : ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) |
      GraphMarkovMatching.InfMatch (GraphMatching.compat (gNetGraph D))
        (fun n => Profile.encodedStates exc1 (gLab D π₁ ω.1) (gArityAt ω.1.1) 0 n)
        (fun n => Profile.encodedStates exc2 (gLab D π₂ ω.2) (gArityAt ω.2.1) 0 n)} := by
  set R := GraphMatching.compat (gNetGraph D) with hR
  have hset : {ω : ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) |
        GraphMarkovMatching.InfMatch R
          (fun n => Profile.encodedStates exc1 (gLab D π₁ ω.1) (gArityAt ω.1.1) 0 n)
          (fun n => Profile.encodedStates exc2 (gLab D π₂ ω.2) (gArityAt ω.2.1) 0 n)}
      = ⋂ n, (fun ω : ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) =>
          (Profile.encodedStates exc1 (gLab D π₁ ω.1) (gArityAt ω.1.1) 0 n,
            Profile.encodedStates exc2 (gLab D π₂ ω.2) (gArityAt ω.2.1) 0 n)) ⁻¹'
          {p | GraphMarkovMatching.Support.fullSimK R 1 0 n p.1 p.2} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    exact GraphMarkovMatching.Support.infMatchK_iff_forall_level R 1 0 _ _
      (fun n => Profile.restrict_encodedStates exc1 _ _ 0 n) (fun n => Profile.restrict_encodedStates exc2 _ _ 0 n)
  rw [hset]
  refine MeasurableSet.iInter fun n => ?_
  exact (((measurable_profile_encoding D π₁ exc1 0 n).comp measurable_fst).prodMk
    ((measurable_profile_encoding D π₂ exc2 0 n).comp measurable_snd))
    ((Set.to_countable _).measurableSet)

/-- **The couplings of `thm:relabel` exist at every arity past one threshold**: the
thresholds of the finitely many arities of positive reduced weight are dominated by
their maximum. -/
lemma exists_gCouplings_all (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (h0 : 0 < θ 0) (hθJ : 0 < θ J) (hJ2 : 2 ≤ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (h0' : 0 < θ' 0)
    (hθJ' : 0 < θ' J') :
    ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D → ∃ π : GCouplings θ',
      ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
        IsGShapeCoupling (D : ℝ) (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν)
          (gMixPMF θ hJN hq hq0 hs1) (π κ hκ hν) := by
  have hκJ : ∀ κ, 0 < reducedWeight θ' κ → κ ≤ J' := fun κ hν => by
    by_contra h
    rw [reducedWeight_eq_zero_of_gt θ' (not_le.mp h)] at hν
    exact lt_irrefl _ hν
  have hex : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ), ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D →
      ∃ π : PMF (GShape × GShape), IsGShapeCoupling (D : ℝ) (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν)
        (gMixPMF θ hJN hq hq0 hs1) π := fun κ hκ hν =>
    exists_gShapeCoupling_cond_mix θ hJN hq hq0 hs1 h0 hθJ hJ2 θ' hJN' hq' hq0' hs1' h0' hθJ'
      hκ hν (hκJ κ hν)
  choose thr hthr using hex
  set f : ℕ → ℕ := fun κ => if h : 2 ≤ κ ∧ 0 < reducedWeight θ' κ then thr κ h.1 h.2 else 0
    with hf
  refine ⟨(Finset.Icc 2 J').sup f, fun D hD => ?_⟩
  have hD' : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ), thr κ hκ hν ≤ D := by
    intro κ hκ hν
    have hmem : κ ∈ Finset.Icc 2 J' := Finset.mem_Icc.mpr ⟨hκ, hκJ κ hν⟩
    have := Finset.le_sup (f := f) hmem
    rw [hf] at this
    simp only [dif_pos (And.intro hκ hν)] at this
    exact this.trans hD
  choose π hπ using fun κ hκ hν => hthr κ hκ hν D (hD' κ hκ hν)
  exact ⟨π, hπ⟩

/-- **`thm:hairy-general` for arbitrary bounded supports, the rate**: past a threshold depending on the
two laws alone, two independent labelled samples fail to be
`⌈216 J J'² (3·(3¹⁵D¹⁶)²)²⌉`-quasi-isometric with probability at most `Ke^{-cD²}`. -/
theorem hairy_general_rate (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (h0 : 0 < θ 0) (hθJ : 0 < θ J) (hJ2 : 2 ≤ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (h0' : 0 < θ' 0)
    (hθJ' : 0 < θ' J') (hJ2' : 2 ≤ J') :
    ∃ (D₆ : ℕ) (K c : ℝ), 0 < c ∧ ∀ D : ℕ, D₆ ≤ D →
      twoLabelMeasure (N := N) (N' := N') θ θ'
        {ω | ¬ ∃ F : {v : GWord N // v ∈ sample ω.1.1} → {v : GWord N' // v ∈ sample ω.2.1},
          BranchingProcess.IsQIWith ⌈216 * J * J' ^ 2 * (3 * (14348907 * (D : ℝ) ^ 16) ^ 2) ^ 2⌉₊
            (wordGraphN (· ∈ sample ω.1.1)) (wordGraphN (· ∈ sample ω.2.1)) F}
        ≤ ENNReal.ofReal (K * Real.exp (-(c * (D : ℝ) ^ 2))) := by
  obtain ⟨D₆, K, c, hc, hmatch⟩ :=
    exists_profile_match θ hJN hq hq0 hs1 h0 hθJ hJ2 θ' hJN' hq' hq0' hs1' hθJ' hJ2'
  obtain ⟨D₁, hD₁⟩ := exists_gCouplings_all θ hJN hq hq0 hs1 h0 hθJ hJ2 θ hJN hq hq0 hs1 h0 hθJ
  obtain ⟨D₂, hD₂⟩ := exists_gCouplings_all θ hJN hq hq0 hs1 h0 hθJ hJ2 θ' hJN' hq' hq0' hs1'
    h0' hθJ'
  refine ⟨max (max D₆ D₁) (max D₂ 1), K, c, hc, fun D hD => ?_⟩
  have hD6 : D₆ ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hD
  have hD1 : D₁ ≤ D := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hD
  have hD2 : D₂ ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hD
  have hD1' : 1 ≤ D := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hD
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1'
  obtain ⟨π₁, hπ₁⟩ := hD₁ D hD1
  obtain ⟨π₂, hπ₂⟩ := hD₂ D hD2
  have hbound := hmatch D hD6 π₁ hπ₁ π₂ hπ₂
  have _ := isProbabilityMeasure_twoLabelMeasure (N := N) (N' := N') θ hJN hq θ' hJN' hq'
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  have _ := isProbabilityMeasure_labelMeasure (N' := N) θ hJN hq
  have _ := isProbabilityMeasure_labelMeasure (N' := N') θ' hJN' hq'
  -- the matching event fails with probability at most `K e^{-cD²}`
  set M := {ω : ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) |
    GraphMarkovMatching.InfMatch (GraphMatching.compat (gNetGraph D))
      (fun n => Profile.encodedStates balancedFamily (gLab D π₁ ω.1) (gArityAt ω.1.1) 0 n)
      (fun n => Profile.encodedStates balancedFamily (gLab D π₂ ω.2) (gArityAt ω.2.1) 0 n)} with hM
  have hfail : twoLabelMeasure (N := N) (N' := N') θ θ' Mᶜ
      ≤ ENNReal.ofReal (K * Real.exp (-(c * (D : ℝ) ^ 2))) := by
    rw [prob_compl_eq_one_sub (measurableSet_engine_match θ θ' π₁ π₂ _ _)]
    have h1 := tsub_le_iff_right.mp hbound
    rw [add_comm] at h1
    exact tsub_le_iff_right.mpr h1
  -- the good event
  have hgood₁ : ∀ᵐ ω ∂labelMeasure (N' := N) θ, IsGHairySample ω.1 ∧
      SkelBounded J (gArityAt ω.1) ∧ ∀ u, u ∈ sample (gArityAt ω.1) →
        MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShapeAt ω.1 u))
          (gShapeSpace (gPartner π₁ ω u)) := by
    filter_upwards [ae_of_fst (ν := uniformField (GWord N)) (ae_isGHairySample θ hJN hq hs1),
      ae_of_fst (ν := uniformField (GWord N)) (ae_skeleton_good θ hJN hq hq0 hJ2 hθJ),
      ae_partner_comparable θ hJN hq hq0 hs1 θ hJN hq hq0 hs1 hJ2 hθJ π₁ hπ₁] with ω h1 h2 h3
    exact ⟨h1, fun u hu => (h2 u hu).1, h3⟩
  have hgood₂ : ∀ᵐ ω ∂labelMeasure (N' := N') θ', IsGHairySample ω.1 ∧
      SkelBounded J' (gArityAt ω.1) ∧ ∀ u, u ∈ sample (gArityAt ω.1) →
        MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShapeAt ω.1 u))
          (gShapeSpace (gPartner π₂ ω u)) := by
    filter_upwards [ae_of_fst (ν := uniformField (GWord N')) (ae_isGHairySample θ' hJN' hq' hs1'),
      ae_of_fst (ν := uniformField (GWord N')) (ae_skeleton_good θ' hJN' hq' hq0' hJ2' hθJ'),
      ae_partner_comparable θ hJN hq hq0 hs1 θ' hJN' hq' hq0' hs1' hJ2' hθJ' π₂ hπ₂] with ω h1 h2 h3
    exact ⟨h1, fun u hu => (h2 u hu).1, h3⟩
  have hgood : ∀ᵐ ω ∂twoLabelMeasure (N := N) (N' := N') θ θ', (IsGHairySample ω.1.1 ∧
      SkelBounded J (gArityAt ω.1.1) ∧ ∀ u, u ∈ sample (gArityAt ω.1.1) →
        MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShapeAt ω.1.1 u))
          (gShapeSpace (gPartner π₁ ω.1 u))) ∧ (IsGHairySample ω.2.1 ∧
      SkelBounded J' (gArityAt ω.2.1) ∧ ∀ u, u ∈ sample (gArityAt ω.2.1) →
        MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShapeAt ω.2.1 u))
          (gShapeSpace (gPartner π₂ ω.2 u))) := by
    filter_upwards [ae_of_fst (ν := labelMeasure (N' := N') θ') hgood₁,
      ae_of_snd (μ := labelMeasure (N' := N) θ) hgood₂] with ω h1 h2
    exact ⟨h1, h2⟩
  -- on the good matching event the samples are quasi-isometric
  have hsub : {ω : ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) |
        ¬ ∃ F : {v : GWord N // v ∈ sample ω.1.1} → {v : GWord N' // v ∈ sample ω.2.1},
          BranchingProcess.IsQIWith ⌈216 * J * J' ^ 2 * (3 * (14348907 * (D : ℝ) ^ 16) ^ 2) ^ 2⌉₊
            (wordGraphN (· ∈ sample ω.1.1)) (wordGraphN (· ∈ sample ω.2.1)) F}
      ⊆ Mᶜ ∪ {ω | ¬ ((IsGHairySample ω.1.1 ∧
      SkelBounded J (gArityAt ω.1.1) ∧ ∀ u, u ∈ sample (gArityAt ω.1.1) →
        MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShapeAt ω.1.1 u))
          (gShapeSpace (gPartner π₁ ω.1 u))) ∧ (IsGHairySample ω.2.1 ∧
      SkelBounded J' (gArityAt ω.2.1) ∧ ∀ u, u ∈ sample (gArityAt ω.2.1) →
        MarkedQI (9 * (D : ℝ) ^ 3) (gShapeSpace (gShapeAt ω.2.1 u))
          (gShapeSpace (gPartner π₂ ω.2 u))))} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨hm, ⟨hc, hs, hτ⟩, ⟨hc', hs', hτ'⟩⟩ := hcon
    apply hω
    exact Profile.sample_qi_of_profile_match balancedFamily balancedFamily hc hc' hs hs'
      (by omega) (by omega) hDR (fun u _ => rfl) (fun u _ => rfl) hτ hτ' hm
  calc twoLabelMeasure (N := N) (N' := N') θ θ' _
      ≤ twoLabelMeasure (N := N) (N' := N') θ θ' (Mᶜ ∪ _) := measure_mono hsub
    _ ≤ twoLabelMeasure (N := N) (N' := N') θ θ' Mᶜ
        + twoLabelMeasure (N := N) (N' := N') θ θ' _ := measure_union_le _ _
    _ = twoLabelMeasure (N := N) (N' := N') θ θ' Mᶜ + 0 := by rw [ae_iff.mp hgood]
    _ ≤ ENNReal.ofReal (K * Real.exp (-(c * (D : ℝ) ^ 2))) := by rw [add_zero]; exact hfail

/-- **`thm:hairy-general` for arbitrary bounded supports, the almost sure statement on the labelled
space**: the failure rates `Ke^{-cD²}` fall below every threshold, so almost surely some
scale succeeds. -/
theorem hairy_general_labelled_ae (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (h0 : 0 < θ 0) (hθJ : 0 < θ J) (hJ2 : 2 ≤ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (h0' : 0 < θ' 0)
    (hθJ' : 0 < θ' J') (hJ2' : 2 ≤ J') :
    ∀ᵐ ω ∂twoLabelMeasure (N := N) (N' := N') θ θ',
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1.1))
        (wordGraphN (· ∈ sample ω.2.1)) := by
  obtain ⟨D₆, K, c, hc, hrate⟩ := hairy_general_rate θ hJN hq hq0 hs1 h0 hθJ hJ2 θ' hJN' hq'
    hq0' hs1' h0' hθJ' hJ2'
  rw [ae_iff]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  have hεpos : (0 : ℝ) < ε := hε
  have hKpos : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨D₀, hD₀⟩ := hairy_rate_to_one hc (ε := 16 * ε / max K 1) (by positivity)
  set D := max D₀ D₆ with hD
  have hsmall : K * Real.exp (-(c * (D : ℝ) ^ 2)) ≤ ε := by
    have h1 := hD₀ D (le_max_left _ _)
    have h2 : K ≤ max K 1 := le_max_left _ _
    have h3 : 0 < Real.exp (-(c * (D : ℝ) ^ 2)) := Real.exp_pos _
    rw [lt_div_iff₀ hKpos] at h1
    nlinarith
  have hsub : {ω : ((GWord N → ℕ) × (GWord N → ℝ)) × ((GWord N' → ℕ) × (GWord N' → ℝ)) |
        ¬ BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1.1))
          (wordGraphN (· ∈ sample ω.2.1))}
      ⊆ {ω | ¬ ∃ F : {v : GWord N // v ∈ sample ω.1.1} → {v : GWord N' // v ∈ sample ω.2.1},
          BranchingProcess.IsQIWith ⌈216 * J * J' ^ 2 * (3 * (14348907 * (D : ℝ) ^ 16) ^ 2) ^ 2⌉₊
            (wordGraphN (· ∈ sample ω.1.1)) (wordGraphN (· ∈ sample ω.2.1)) F} := by
    rintro ω hω ⟨F, hF⟩
    exact hω ⟨_, F, hF⟩
  calc twoLabelMeasure (N := N) (N' := N') θ θ' _
      ≤ twoLabelMeasure (N := N) (N' := N') θ θ' _ := measure_mono hsub
    _ ≤ ENNReal.ofReal (K * Real.exp (-(c * (D : ℝ) ^ 2))) := hrate D (le_max_right _ _)
    _ ≤ (ε : ℝ≥0∞) := ENNReal.ofReal_le_of_le_toReal (by simpa using hsmall)
    _ = 0 + (ε : ℝ≥0∞) := (zero_add _).symm

/-- **`thm:hairy-general` for arbitrary bounded supports**: two independent samples conditioned on
survival are almost surely quasi-isometric, the uniform fields integrated out. -/
theorem hairy_general_ae_at_parameters (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (h0 : 0 < θ 0) (hθJ : 0 < θ J) (hJ2 : 2 ≤ J)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (h0' : 0 < θ' 0)
    (hθJ' : 0 < θ' J') (hJ2' : 2 ≤ J') :
    ∀ᵐ cc ∂((survivalMeasure (N := N) θ).prod (survivalMeasure (N := N') θ')),
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample cc.1))
        (wordGraphN (· ∈ sample cc.2)) := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  have h := hairy_general_labelled_ae θ hJN hq hq0 hs1 h0 hθJ hJ2 θ' hJN' hq' hq0' hs1' h0' hθJ'
    hJ2'
  exact ae_prod_fst_fst (μ := survivalMeasure (N := N) θ) (ν := uniformField (GWord N))
    (μ' := survivalMeasure (N := N') θ') (ν' := uniformField (GWord N')) h

end Rate


/-- **`thm:qi-transitive` at general arity**: almost sure quasi-isometry of independent
samples composes through the triple product. -/
theorem gSampleQI_trans {N₀ N₁ N₂ : ℕ} {μ₀ : Measure (GWord N₀ → ℕ)} {μ₁ : Measure (GWord N₁ → ℕ)}
    {μ₂ : Measure (GWord N₂ → ℕ)} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂]
    (h01 : ∀ᵐ ω ∂(μ₀.prod μ₁), BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
      (wordGraphN (· ∈ sample ω.2)))
    (h12 : ∀ᵐ ω ∂(μ₁.prod μ₂), BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
      (wordGraphN (· ∈ sample ω.2))) :
    ∀ᵐ ω ∂(μ₀.prod μ₂), BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
      (wordGraphN (· ∈ sample ω.2)) := by
  have hlift01 := ae_pair_fst (τ := μ₂) h01
  have hlift12 : ∀ᵐ ω ∂(μ₀.prod (μ₁.prod μ₂)),
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.2.1))
        (wordGraphN (· ∈ sample ω.2.2)) := ae_of_snd h12
  have htrip : ∀ᵐ ω ∂(μ₀.prod (μ₁.prod μ₂)),
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
        (wordGraphN (· ∈ sample ω.2.2)) := by
    filter_upwards [hlift01, hlift12] with ω h1 h2
    exact QuasiIsometric.trans (wordGraphN_connected (prefixClosedN_sample _)
      ⟨⟨[], BranchingProcess.nil_mem_sample _⟩⟩) h1 h2
  exact ae_pair_outer (p := fun z : (GWord N₀ → ℕ) × (GWord N₂ → ℕ) =>
    BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample z.1)) (wordGraphN (· ∈ sample z.2)))
    htrip

/-- An almost sure property of a product, read through the swap. -/
lemma ae_prod_swap {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {p : α × β → Prop}
    (h : ∀ᵐ ω ∂(ν.prod μ), p ω.swap) : ∀ᵐ ω ∂(μ.prod ν), p ω := by
  rw [← Measure.prod_swap] at h
  have := ae_of_ae_map measurable_swap.aemeasurable h
  simpa using this

/-- Almost sure quasi-isometry of independent samples is symmetric. -/
theorem gSampleQI_symm {N₀ N₁ : ℕ} {μ₀ : Measure (GWord N₀ → ℕ)} {μ₁ : Measure (GWord N₁ → ℕ)}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (h : ∀ᵐ ω ∂(μ₁.prod μ₀), BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
      (wordGraphN (· ∈ sample ω.2))) :
    ∀ᵐ ω ∂(μ₀.prod μ₁), BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample ω.1))
      (wordGraphN (· ∈ sample ω.2)) := by
  refine ae_prod_swap ?_
  filter_upwards [h] with ω hω
  exact QuasiIsometric.symm (wordGraphN_connected (prefixClosedN_sample _)
    ⟨⟨[], BranchingProcess.nil_mem_sample _⟩⟩) hω



/-- Two bounded supercritical bushy laws give almost surely quasi-isometric independent
samples, conditioned on survival. -/
theorem hairy_general_ae {J J' : ℕ} (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (h0 : 0 < θ 0) (hθJ : 0 < θ J)
    (hJ2 : 2 ≤ J) (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h0' : 0 < θ' 0) (hθJ' : 0 < θ' J') (hJ2' : 2 ≤ J') :
    ∀ᵐ cc ∂((survivalMeasure (N := N) θ).prod (survivalMeasure (N := N') θ')),
      BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample cc.1))
        (wordGraphN (· ∈ sample cc.2)) := by
  exact hairy_general_ae_at_parameters θ hJN hq hq0
    (skeletonWeight_one_lt_one_of θ hq hq0 hJ2 hθJ) h0 hθJ hJ2 θ' hJN' hq' hq0'
    (skeletonWeight_one_lt_one_of θ' hq' hq0' hJ2' hθJ') h0' hθJ' hJ2'

end ChainClasses
