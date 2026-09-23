import ChainClasses.Universality.StarSeparation
import ChainClasses.Universality.GeneralTrichotomy
import Mathlib.Probability.Independence.ZeroOne

/-!
The probabilistic layer of `thm:chain-separation` (`prelims.tex`) and the discharge of
the hypothesis `ChainSeparation` of `GeneralTrichotomy.lean`: the star lemma of Step 2,
anchored along the deterministic first-child ray, supplies the stars that
`StarSeparation.lean` consumes, and the sphere hypotheses hold almost surely on the
other sample.

This is an implementation module.  The hypothesis-free classification is exported under
reader-facing names by `ChainClasses.Classification.Complete`.

* `survivalMeasure_eq_sampleMeasure`: at `θ₀ = 0` the conditioning is trivial.
* `patXi`, `patFinset`, `patEvent`: the coordinate pattern of Step 2 as a cylinder
  event, with `patEvent_pattern` and `sampleMeasure_patEvent_ne_zero`.
* `map_ambSub_zw`, `sampleMeasure_patEvent_inter`: the descent along the ray preserves
  the law and is independent of the pattern.
* `ae_pattern_anchors`: **the star lemma**, patterns at anchors beyond every depth,
  almost surely, simultaneously for every line length.
* `ae_forall_support`: the offspring values lie in the support, almost surely.
* `chainSeparation`: **`thm:chain-separation`**, discharging the hypothesis.
* `trichotomy_ae_iff`: the eventwise form of the complete classification.
* `trichotomy_not_ray`: the one-sample corollary outside the ray class.
* `GRegime.ofExact`, `trichotomy_exact_ae_iff`, `trichotomy_exact_not_ray`: the raw-law
  interface, for offspring laws written with their true top support.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (Offspring sample sampleMeasure survivalMeasure Survives coord)

variable {J N : ℕ}

/-! ### The conditioning is trivial in the chain regime -/

/-- At `θ₀ = 0` survival is sure and the conditioned law is the sample law. -/
theorem survivalMeasure_eq_sampleMeasure (θ : Offspring J) (hJN : J ≤ N)
    (h0 : θ 0 = 0) : survivalMeasure (N := N) θ = sampleMeasure (N := N) θ := by
  have hq : θ.extinction = 0 := θ.extinction_eq_zero_iff.mpr h0
  have hS : sampleMeasure (N := N) θ {c : GWord N → ℕ | Survives c} = 1 := by
    rw [BranchingProcess.sampleMeasure_survives θ hJN, hq]
    simp
  have hSc : sampleMeasure (N := N) θ {c : GWord N → ℕ | ¬ Survives c} = 0 := by
    rw [BranchingProcess.sampleMeasure_not_survives θ hJN, hq]
    simp
  refine Measure.ext fun t ht => ?_
  rw [BranchingProcess.survivalMeasure_apply, hS, inv_one, one_mul]
  refine le_antisymm (measure_mono Set.inter_subset_right) ?_
  have hsub : t ⊆ ({c : GWord N → ℕ | Survives c} ∩ t)
      ∪ {c : GWord N → ℕ | ¬ Survives c} := by
    intro c hc
    by_cases hs : Survives c
    · exact Or.inl ⟨hs, hc⟩
    · exact Or.inr hs
  calc sampleMeasure (N := N) θ t
      ≤ sampleMeasure (N := N) θ (({c : GWord N → ℕ | Survives c} ∩ t)
          ∪ {c : GWord N → ℕ | ¬ Survives c}) := measure_mono hsub
    _ ≤ sampleMeasure (N := N) θ ({c : GWord N → ℕ | Survives c} ∩ t)
          + sampleMeasure (N := N) θ {c : GWord N → ℕ | ¬ Survives c} :=
        measure_union_le _ _
    _ = sampleMeasure (N := N) θ ({c : GWord N → ℕ | Survives c} ∩ t) := by
        rw [hSc, add_zero]

/-! ### The pattern as a cylinder event -/

section Event

variable (hN : 0 < N) (ks : List ℕ) (L : ℕ)

/-- The prescribed offspring value at a pattern vertex: the stack arity on the stack,
one everywhere else. -/
def patXi (v : GWord N) : ℕ :=
  if v = zw hN v.length ∧ L ≤ v.length ∧ v.length < L + ks.length then
    ks.getD (v.length - L) 0
  else 1

/-- The pattern vertices: the ancestors, the stack, and the leaving lines, anchored
at the root. -/
def patFinset : Finset (GWord N) :=
  ((Finset.range L).image (zw hN))
    ∪ ((Finset.range ks.length).image (fun i => zw hN (L + i)))
    ∪ ((((Finset.range ks.length) ×ˢ (Finset.univ : Finset (Fin N)))
          ×ˢ Finset.range L).filter
        (fun p => (p.1.2 : ℕ) < ks.getD p.1.1 0
          ∧ (0 < (p.1.2 : ℕ) ∨ p.1.1 + 1 = ks.length))).image
        (fun p => lineW hN 0 L p.1.1 p.1.2 p.2)

/-- The pattern event: every pattern vertex carries its prescribed value. -/
def patEvent : Set (GWord N → ℕ) :=
  ⋂ v ∈ patFinset hN ks L, (coord v) ⁻¹' {patXi hN ks L v}

lemma measurableSet_patEvent : MeasurableSet (patEvent hN ks L) :=
  MeasurableSet.biInter (Finset.countable_toSet _) fun v _ =>
    BranchingProcess.measurable_coord v (measurableSet_singleton _)

lemma patXi_ray {s : ℕ} (hs : s < L) : patXi hN ks L (zw hN s) = 1 := by
  rw [patXi, ite_eq_right]
  rintro ⟨-, h2, -⟩
  rw [zw_length] at h2
  omega

lemma patXi_stack {i : ℕ} (_hi : i < ks.length) :
    patXi hN ks L (zw hN (L + i)) = ks.getD i 0 := by
  rw [patXi, ite_eq_left]
  · rw [zw_length]
    congr 1
    omega
  · refine ⟨by rw [zw_length], by rw [zw_length]; omega, by rw [zw_length]; omega⟩

/-- A line through the zero letter at stack depth `i` is a ray vertex. -/
lemma lineW_zero' {a i : ℕ} (t : ℕ) :
    lineW hN a L i (⟨0, hN⟩ : Fin N) t = zw hN (a + L + i + 1 + t) := by
  rw [lineW, zw, zw, show (⟨0, hN⟩ : Fin N) :: List.replicate t (⟨0, hN⟩ : Fin N)
    = List.replicate (t + 1) ⟨0, hN⟩ from (List.replicate_succ).symm,
    ← List.replicate_add]
  congr 1
  omega

lemma patXi_line {i : ℕ} (_hi : i < ks.length) {j : Fin N}
    (hv : 0 < (j : ℕ) ∨ i + 1 = ks.length) (t : ℕ) :
    patXi hN ks L (lineW hN 0 L i j t) = 1 := by
  by_cases hj0 : (j : ℕ) = 0
  · have hlast : i + 1 = ks.length := by
      rcases hv with h | h
      · omega
      · exact h
    rw [eq_zero_letter (hN := hN) hj0, lineW_zero' hN, patXi, ite_eq_right]
    rintro ⟨-, -, h3⟩
    rw [zw_length] at h3
    omega
  · rw [patXi, ite_eq_right]
    rintro ⟨h1, -, -⟩
    have hjmem : j ∈ lineW hN 0 L i j t := by
      rw [lineW]
      exact List.mem_append_right _ List.mem_cons_self
    rw [h1, zw] at hjmem
    exact hj0 (by rw [List.eq_of_mem_replicate hjmem])

lemma ray_mem_patFinset {s : ℕ} (hs : s < L) : zw hN s ∈ patFinset hN ks L :=
  Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hs, rfl⟩))

lemma stack_mem_patFinset {i : ℕ} (hi : i < ks.length) :
    zw hN (L + i) ∈ patFinset hN ks L :=
  Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩))

lemma line_mem_patFinset {i : ℕ} (hi : i < ks.length) {j : Fin N}
    (hj : (j : ℕ) < ks.getD i 0) (hv : 0 < (j : ℕ) ∨ i + 1 = ks.length) {t : ℕ}
    (ht : t < L) : lineW hN 0 L i j t ∈ patFinset hN ks L :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨((i, j), t),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_univ j⟩,
        Finset.mem_range.mpr ht⟩, hj, hv⟩, rfl⟩)

/-- **The event realises the pattern.** -/
lemma patEvent_pattern {c : GWord N → ℕ} (hc : c ∈ patEvent hN ks L) :
    PatternAt hN c ks 0 L := by
  have hval : ∀ v ∈ patFinset hN ks L, c v = patXi hN ks L v := by
    intro v hv
    exact Set.mem_iInter₂.mp hc v hv
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    rw [Nat.zero_add, hval _ (ray_mem_patFinset hN ks L hs), patXi_ray hN ks L hs]
  · intro i hi
    rw [Nat.zero_add, hval _ (stack_mem_patFinset hN ks L hi), patXi_stack hN ks L hi]
  · intro i hi j hj hv t ht
    rw [hval _ (line_mem_patFinset hN ks L hi hj hv ht), patXi_line hN ks L hi hv t]

/-- **The pattern has positive probability.** -/
lemma sampleMeasure_patEvent_ne_zero (θ : Offspring J) (h1 : 0 < θ 1)
    (hθks : ∀ k ∈ ks, 0 < θ k) :
    sampleMeasure (N := N) θ (patEvent hN ks L) ≠ 0 := by
  have hprod := (BranchingProcess.coord_iIndepFun
    (ι := GWord N) θ.law).measure_inter_preimage_eq_mul (patFinset hN ks L)
    (sets := fun v => {patXi hN ks L v}) (fun v _ => measurableSet_singleton _)
  rw [patEvent, show (sampleMeasure (N := N) θ)
    = BranchingProcess.fieldMeasure θ.law from rfl, hprod, Finset.prod_ne_zero_iff]
  intro v hv
  have hcoord : BranchingProcess.fieldMeasure (ι := GWord N) θ.law
      ((coord v) ⁻¹' {patXi hN ks L v})
      = ENNReal.ofReal (θ (patXi hN ks L v)) :=
    BranchingProcess.sampleMeasure_coord θ v (patXi hN ks L v)
  rw [hcoord]
  refine (ENNReal.ofReal_pos.mpr ?_).ne'
  rw [patXi]
  split_ifs with hcond
  · refine hθks _ ?_
    obtain ⟨-, h2, h3⟩ := hcond
    rw [List.getD_eq_getElem ks 0 (by omega)]
    exact List.getElem_mem _
  · exact h1

end Event

section Shift

variable (hN : 0 < N) (ks : List ℕ) (L : ℕ)

/-- The window length of the pattern. -/
def patW (ks : List ℕ) (L : ℕ) : ℕ := 2 * L + ks.length + 1

/-- Every pattern vertex lies strictly inside the window. -/
lemma patFinset_length_lt {v : GWord N} (hv : v ∈ patFinset hN ks L) :
    v.length < patW ks L := by
  rw [patW]
  rcases Finset.mem_union.mp hv with hv | hv
  · rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
      rw [Finset.mem_range] at hs
      rw [zw_length]
      omega
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      rw [Finset.mem_range] at hi
      rw [zw_length]
      omega
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    rw [Finset.mem_filter] at hp
    obtain ⟨hmem, -, -⟩ := hp
    rw [Finset.mem_product] at hmem
    obtain ⟨hmem1, ht⟩ := hmem
    rw [Finset.mem_product] at hmem1
    obtain ⟨hi, -⟩ := hmem1
    rw [Finset.mem_range] at hi ht
    rw [lineW_length]
    omega

/-- **The descent along the ray preserves the law.** -/
lemma map_ambSub_zw (θ : Offspring J) (u : GWord N) :
    (sampleMeasure (N := N) θ).map (fun c => ambSub c u) = sampleMeasure (N := N) θ := by
  show (Measure.infinitePi fun _ : GWord N => θ.law).map (fun c w => c (u ++ w))
    = Measure.infinitePi fun _ : GWord N => θ.law
  exact Measure.map_infinitePi_infinitePi_of_inj fun w w' h => List.append_cancel_left h

lemma preimage_ambSub (θ : Offspring J) (u : GWord N) {A : Set (GWord N → ℕ)}
    (hA : MeasurableSet A) :
    sampleMeasure (N := N) θ ((fun c => ambSub c u) ⁻¹' A)
      = sampleMeasure (N := N) θ A := by
  rw [← Measure.map_apply (measurable_ambSub u) hA, map_ambSub_zw]

/-- **The pattern is independent of the descended field.** -/
lemma sampleMeasure_patEvent_inter (θ : Offspring J) {A : Set (GWord N → ℕ)}
    (hA : MeasurableSet A) :
    sampleMeasure (N := N) θ (patEvent hN ks L
        ∩ (fun c => ambSub c (zw hN (patW ks L))) ⁻¹' A)
      = sampleMeasure (N := N) θ (patEvent hN ks L)
        * sampleMeasure (N := N) θ A := by
  have hindep : Indep
      (⨆ v ∈ (↑(patFinset hN ks L) : Set (GWord N)),
        MeasurableSpace.comap (coord v) inferInstance)
      (⨆ v ∈ (↑(patFinset hN ks L) : Set (GWord N))ᶜ,
        MeasurableSpace.comap (coord v) inferInstance)
      (sampleMeasure (N := N) θ) :=
    ProbabilityTheory.indep_biSup_compl (fun v => (BranchingProcess.measurable_coord v).comap_le)
      (BranchingProcess.coord_iIndepFun θ.law) _
  have hDmeas : MeasurableSet[⨆ v ∈ (↑(patFinset hN ks L) : Set (GWord N)),
      MeasurableSpace.comap (coord v) inferInstance] (patEvent hN ks L) := by
    refine MeasurableSet.biInter (Finset.countable_toSet _) fun v hv => ?_
    have hle : MeasurableSpace.comap (coord (α := ℕ) v) inferInstance
        ≤ ⨆ v ∈ (↑(patFinset hN ks L) : Set (GWord N)),
          MeasurableSpace.comap (coord v) inferInstance :=
      le_iSup₂ (f := fun (v : GWord N)
        (_ : v ∈ (↑(patFinset hN ks L) : Set (GWord N))) =>
          MeasurableSpace.comap (coord v) inferInstance) v hv
    exact hle _ ⟨{patXi hN ks L v}, measurableSet_singleton _, rfl⟩
  have hAmeas : MeasurableSet[⨆ v ∈ (↑(patFinset hN ks L) : Set (GWord N))ᶜ,
      MeasurableSpace.comap (coord v) inferInstance]
      ((fun c => ambSub c (zw hN (patW ks L))) ⁻¹' A) := by
    have hcomap : MeasurableSpace.comap
        (fun c : GWord N → ℕ => ambSub c (zw hN (patW ks L))) MeasurableSpace.pi
        ≤ ⨆ v ∈ (↑(patFinset hN ks L) : Set (GWord N))ᶜ,
          MeasurableSpace.comap (coord v) inferInstance := by
      rw [show (MeasurableSpace.pi : MeasurableSpace (GWord N → ℕ))
          = ⨆ w : GWord N, MeasurableSpace.comap (fun c => c w) inferInstance from rfl,
        MeasurableSpace.comap_iSup]
      refine iSup_le fun w => ?_
      rw [MeasurableSpace.comap_comp]
      refine le_trans (le_of_eq rfl) (le_iSup₂ (f := fun (v : GWord N)
        (_ : v ∈ (↑(patFinset hN ks L) : Set (GWord N))ᶜ) =>
          MeasurableSpace.comap (coord v) inferInstance) (zw hN (patW ks L) ++ w) ?_)
      intro hmem
      have hlen := patFinset_length_lt hN ks L (Finset.mem_coe.mp hmem)
      rw [List.length_append, zw_length] at hlen
      omega
    exact hcomap _ ⟨A, hA, rfl⟩
  rw [(Indep_iff _ _ _).mp hindep _ _ hDmeas hAmeas, preimage_ambSub θ _ hA]

/-- The iterates of the descent are the descents to the multiples. -/
lemma iterate_ambSub_zw (c : GWord N → ℕ) :
    ∀ k, (fun c => ambSub c (zw hN (patW ks L)))^[k] c
      = ambSub c (zw hN (k * patW ks L))
  | 0 => by simp [zw]
  | k + 1 => by
      rw [Function.iterate_succ_apply', iterate_ambSub_zw c k, ambSub_ambSub]
      congr 1
      rw [zw, zw, zw, ← List.replicate_add]
      congr 1
      ring

/-- The pattern of a descended field is the pattern at the descent anchor. -/
lemma pattern_of_ambSub {c : GWord N → ℕ} {A : ℕ}
    (h : PatternAt hN (ambSub c (zw hN A)) ks 0 L) : PatternAt hN c ks A L := by
  obtain ⟨h1, h2, h3⟩ := h
  have hzz : ∀ n, zw hN A ++ zw hN n = zw hN (A + n) := fun n => by
    rw [zw, zw, zw, ← List.replicate_add]
  have hline : ∀ i (j : Fin N) t, zw hN A ++ lineW hN 0 L i j t
      = lineW hN A L i j t := by
    intro i j t
    rw [lineW, lineW, ← List.append_assoc, hzz]
    congr 2
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hc := h1 s hs
    rw [Nat.zero_add, ambSub_apply, hzz] at hc
    exact hc
  · intro i hi
    have hc := h2 i hi
    rw [Nat.zero_add, ambSub_apply, hzz, ← Nat.add_assoc] at hc
    exact hc
  · intro i hi j hj hv t ht
    have hc := h3 i hi j hj hv t ht
    rw [ambSub_apply, hline] at hc
    exact hc

end Shift

/-! ### The star lemma -/

section StarLemma

variable (hN : 0 < N) (ks : List ℕ)

/-- **The star lemma, `thm:chain-separation` Step 2**: almost surely the pattern
appears at anchors beyond every depth, simultaneously for every line length. -/
theorem ae_pattern_anchors (θ : Offspring J) (h1 : 0 < θ 1)
    (hθks : ∀ k ∈ ks, 0 < θ k) :
    ∀ᵐ c ∂ sampleMeasure (N := N) θ, ∀ L A₀ : ℕ, ∃ A, A₀ ≤ A ∧ PatternAt hN c ks A L := by
  rw [ae_all_iff]
  intro L
  rw [ae_all_iff]
  intro A₀
  have hae := ae_exists_iterate_mem (μ := sampleMeasure (N := N) θ)
    (Φ := fun c => ambSub c (zw hN (patW ks L))) (D := patEvent hN ks L)
    (measurable_ambSub _) (fun A hA => preimage_ambSub θ _ hA)
    (measurableSet_patEvent hN ks L)
    (fun A hA => sampleMeasure_patEvent_inter hN ks L θ hA)
    (sampleMeasure_patEvent_ne_zero hN ks L θ h1 hθks)
  have hiterpres : ∀ (S : Set (GWord N → ℕ)), MeasurableSet S → ∀ l,
      sampleMeasure (N := N) θ
        (((fun c => ambSub c (zw hN (patW ks L)))^[l]) ⁻¹' S)
      = sampleMeasure (N := N) θ S := by
    intro S hS l
    induction l with
    | zero => simp
    | succ l ih =>
        rw [Function.iterate_succ, Set.preimage_comp,
          preimage_ambSub θ _ ((Measurable.iterate (measurable_ambSub _) l) hS)]
        exact ih
  have hEmeas : MeasurableSet {c : GWord N → ℕ |
      ¬ ∃ k, (fun c => ambSub c (zw hN (patW ks L)))^[k] c ∈ patEvent hN ks L} := by
    have hset : {c : GWord N → ℕ |
        ∃ k, (fun c => ambSub c (zw hN (patW ks L)))^[k] c ∈ patEvent hN ks L}
        = ⋃ k, ((fun c => ambSub c (zw hN (patW ks L)))^[k]) ⁻¹' patEvent hN ks L := by
      ext c
      simp
    have h1' : MeasurableSet {c : GWord N → ℕ |
        ∃ k, (fun c => ambSub c (zw hN (patW ks L)))^[k] c ∈ patEvent hN ks L} := by
      rw [hset]
      exact MeasurableSet.iUnion fun k =>
        (Measurable.iterate (measurable_ambSub _) k) (measurableSet_patEvent hN ks L)
    exact h1'.compl
  have hnull : sampleMeasure (N := N) θ {c : GWord N → ℕ |
      ¬ ∃ k, (fun c => ambSub c (zw hN (patW ks L)))^[k] c ∈ patEvent hN ks L} = 0 :=
    ae_iff.mp hae
  have hae2 : ∀ᵐ c ∂ sampleMeasure (N := N) θ, ∃ k,
      (fun c => ambSub c (zw hN (patW ks L)))^[k]
        ((fun c => ambSub c (zw hN (patW ks L)))^[A₀] c) ∈ patEvent hN ks L := by
    rw [ae_iff]
    have := (hiterpres _ hEmeas A₀).trans hnull
    exact this
  filter_upwards [hae2] with c hc
  obtain ⟨k, hk⟩ := hc
  rw [← Function.iterate_add_apply] at hk
  rw [iterate_ambSub_zw hN ks L c (k + A₀)] at hk
  refine ⟨(k + A₀) * patW ks L, ?_,
    pattern_of_ambSub hN ks L (patEvent_pattern hN ks L hk)⟩
  have hW : 1 ≤ patW ks L := by rw [patW]; omega
  calc A₀ ≤ (k + A₀) * 1 := by omega
    _ ≤ (k + A₀) * patW ks L := Nat.mul_le_mul_left _ hW

end StarLemma

/-! ### The support of the offspring values -/

/-- Almost surely every offspring value carries positive mass. -/
lemma ae_forall_mass_pos (θ : Offspring J) :
    ∀ᵐ c ∂ sampleMeasure (N := N) θ, ∀ v : GWord N, θ (c v) ≠ 0 := by
  rw [ae_all_iff]
  intro v
  rw [ae_iff]
  have hsub : {c : GWord N → ℕ | ¬ θ (c v) ≠ 0}
      ⊆ ⋃ k ∈ {k : ℕ | θ k = 0}, {c : GWord N → ℕ | c v = k} := by
    intro c hc
    simp only [Set.mem_ofPred_eq, not_not] at hc
    exact Set.mem_biUnion hc rfl
  refine measure_mono_null hsub
    ((measure_biUnion_null_iff (Set.to_countable {k : ℕ | θ k = 0})).mpr
      fun k hk => ?_)
  have hco := BranchingProcess.sampleMeasure_coord (N := N) θ v k
  rw [hco, Set.mem_ofPred_eq.mp hk]
  simp

/-- The mono step for quasi-isometry constants. -/
lemma isQIWith_mono {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}
    {f : V → V'} {D D' : ℕ} (h : D ≤ D')
    (hf : BranchingProcess.IsQIWith D G G' f) :
    BranchingProcess.IsQIWith D' G G' f := by
  refine ⟨fun x y => ?_, fun x y => ?_, fun y => ?_⟩
  · exact le_trans (hf.upper x y) (Nat.add_le_add (Nat.mul_le_mul_right _ h) h)
  · exact le_trans (hf.lower x y)
      (Nat.add_le_add (Nat.mul_le_mul_right _ h) (Nat.mul_le_mul h h))
  · obtain ⟨x, hx⟩ := hf.dense y
    exact ⟨x, le_trans hx h⟩

/-! ### The separation -/

/-- The centre of the pattern star. -/
lemma patternStar_ctr {a L m : ℕ} {c : GWord N → ℕ} {ks : List ℕ} (hN : 0 < N)
    (hpos : ∀ v, 1 ≤ c v) (hpat : PatternAt hN c ks a L) (hks2 : ∀ k ∈ ks, 2 ≤ k)
    (hksN : ∀ k ∈ ks, k ≤ N) (hne : ks ≠ [])
    (hsum : (ks.map (fun k => k - 1)).sum = m) (hL : 1 ≤ L) :
    (patternStar hN hpos hpat hks2 hksN hne hsum hL).ctr = zw hN (a + L) := rfl

/-- **`thm:chain-separation`, one side**: distinct branching semigroups witnessed by an
excess in the first semigroup rule out quasi-isometry almost surely. -/
lemma chainSeparation_side {J J' N N' : ℕ} (θ : Offspring J) (θ' : Offspring J')
    (hJN : J ≤ N) (hθ0 : θ 0 = 0) (hθ1 : 0 < θ 1)
    (hJN' : J' ≤ N') (hθ0' : θ' 0 = 0)
    {m : ℕ} (hmθ : m ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ))
    (hmθ' : m ∉ AddSubmonoid.closure (shiftSupp θ' : Set ℕ)) :
    ∀ᵐ cc ∂((survivalMeasure (N := N) θ).prod (survivalMeasure (N := N') θ')),
      ¬ BranchingProcess.QuasiIsometric (wordGraphN (· ∈ sample cc.1))
        (wordGraphN (· ∈ sample cc.2)) := by
  have hN : 0 < N := pos_of_zero θ hJN hθ0
  have hN' : 0 < N' := pos_of_zero θ' hJN' hθ0'
  obtain ⟨l, hl, hlsum⟩ := AddSubmonoid.exists_list_of_mem_closure hmθ
  have hlne : l ≠ [] := by
    intro hcon
    rw [hcon] at hlsum
    simp only [List.sum_nil] at hlsum
    exact hmθ' (hlsum ▸ AddSubmonoid.zero_mem _)
  have hks2 : ∀ k ∈ l.map (fun y => y + 1), 2 ≤ k := by
    intro k hk
    rw [List.mem_map] at hk
    obtain ⟨y, hy, rfl⟩ := hk
    have := shiftSupp_one_le θ y (hl y hy)
    omega
  have hksN : ∀ k ∈ l.map (fun y => y + 1), k ≤ N := by
    intro k hk
    rw [List.mem_map] at hk
    obtain ⟨y, hy, rfl⟩ := hk
    have h1 := shiftSupp_le θ y (hl y hy)
    have h2 := shiftSupp_one_le θ y (hl y hy)
    omega
  have hθks : ∀ k ∈ l.map (fun y => y + 1), 0 < θ k := by
    intro k hk
    rw [List.mem_map] at hk
    obtain ⟨y, hy, rfl⟩ := hk
    have := ((mem_shiftSupp θ).mp (hl y hy)).2
    rw [show y + 1 = 1 + y from by omega]
    exact lt_of_le_of_ne (θ.nonneg _) (Ne.symm this)
  have hsum : ((l.map (fun y => y + 1)).map (fun k => k - 1)).sum = m := by
    rw [List.map_map, show ((fun k => k - 1) ∘ fun y => y + 1) = id from by
      funext y
      simp, List.map_id, hlsum]
  have hne : l.map (fun y => y + 1) ≠ [] := by
    simpa using hlne
  rw [survivalMeasure_eq_sampleMeasure θ hJN hθ0,
    survivalMeasure_eq_sampleMeasure θ' hJN' hθ0']
  filter_upwards [ae_of_fst (ν := sampleMeasure (N := N') θ')
      ((ae_pattern_anchors hN (l.map (fun y => y + 1)) θ hθ1 hθks).and
        (ae_forall_mass_pos θ)),
    ae_of_snd (μ := sampleMeasure (N := N) θ) (ae_forall_mass_pos θ')]
    with cc h1 h2
  obtain ⟨hanchor, hmass1⟩ := h1
  have hpos1 : ∀ v, 1 ≤ cc.1 v := by
    intro v
    by_contra hcon
    exact hmass1 v (by rw [show cc.1 v = 0 from by omega, hθ0])
  have hpos2 : ∀ v, 1 ≤ cc.2 v := by
    intro v
    by_contra hcon
    exact h2 v (by rw [show cc.2 v = 0 from by omega, hθ0'])
  have hbdd2 : ∀ v, cc.2 v ≤ N' := by
    intro v
    by_contra hcon
    exact h2 v (θ'.vanishing _ (by omega))
  have hsupp2 : ∀ v, cc.2 v - 1 ∈ AddSubmonoid.closure (shiftSupp θ' : Set ℕ) := by
    intro v
    rcases Nat.lt_or_ge (cc.2 v) 2 with hlt | hge
    · rw [show cc.2 v - 1 = 0 from by omega]
      exact AddSubmonoid.zero_mem _
    · refine AddSubmonoid.subset_closure (Finset.mem_coe.mpr
        ((mem_shiftSupp θ').mpr ⟨by omega, ?_⟩))
      rw [show 1 + (cc.2 v - 1) = cc.2 v from by omega]
      exact h2 v
  intro hqi
  obtain ⟨D₀, f, hf₀⟩ := hqi
  have hf := isQIWith_mono (Nat.le_succ D₀) hf₀
  have hD : 1 ≤ D₀ + 1 := by omega
  have hL1 : 1 ≤ sepL (D₀ + 1) m := by rw [sepL]; omega
  obtain ⟨A₁, -, hpat₁⟩ := hanchor (sepL (D₀ + 1) m) 0
  obtain ⟨A₂, hA₂, hpat₂⟩ := hanchor (sepL (D₀ + 1) m) (A₁ + sepR (D₀ + 1) m)
  have hfar : sepR (D₀ + 1) m ≤ BranchingProcess.treeDist
      (patternStar hN hpos1 hpat₁ hks2 hksN hne hsum hL1).ctr
      (patternStar hN hpos1 hpat₂ hks2 hksN hne hsum hL1).ctr := by
    rw [patternStar_ctr, patternStar_ctr,
      treeDist_zw_zw hN (by omega : A₁ + sepL (D₀ + 1) m ≤ A₂ + sepL (D₀ + 1) m)]
    omega
  exact star_pair_no_qi (prefixClosedN_sample cc.1) hD
    (patternStar hN hpos1 hpat₁ hks2 hksN hne hsum hL1)
    (patternStar hN hpos1 hpat₂ hks2 hksN hne hsum hL1)
    hfar hmθ' hN' hpos2 hbdd2 hsupp2 hf

/-- **`thm:chain-separation` discharges the separation hypothesis**: `ChainSeparation`
holds. -/
theorem chainSeparation : ChainSeparation := by
  intro J J' N N' θ hJN hθ0 hθ1 hθ1' hJ2 hθJ θ' hJN' hθ0' hθ1'₀ hθ1'' hJ2' hθJ' hsem
  have := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN
    (extinction_lt_one_of_chain θ hθ0)
  have := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN'
    (extinction_lt_one_of_chain θ' hθ0')
  by_cases hside : ∃ m, m ∈ AddSubmonoid.closure (shiftSupp θ : Set ℕ)
      ∧ m ∉ AddSubmonoid.closure (shiftSupp θ' : Set ℕ)
  · obtain ⟨m, hm1, hm2⟩ := hside
    exact chainSeparation_side θ θ' hJN hθ0 hθ1 hJN' hθ0' hm1 hm2
  · push Not at hside
    have hexists : ∃ m, m ∈ AddSubmonoid.closure (shiftSupp θ' : Set ℕ)
        ∧ m ∉ AddSubmonoid.closure (shiftSupp θ : Set ℕ) := by
      by_contra hcon
      push Not at hcon
      exact hsem (AddSubmonoid.ext fun x => ⟨fun h => hside x h, fun h => hcon x h⟩)
    obtain ⟨m, hm1, hm2⟩ := hexists
    refine ae_prod_swap ?_
    filter_upwards [chainSeparation_side θ' θ hJN' hθ0' hθ1'₀ hJN hθ0 hm1 hm2]
      with ω hω hqi
    exact hω (QuasiIsometric.symm (wordGraphN_connected (prefixClosedN_sample ω.1)
      ⟨⟨[], BranchingProcess.nil_mem_sample ω.1⟩⟩) hqi)

/-! ### The classification, hypothesis-free -/

/-- **`thm:chain-separation`**: regime (C) against itself across branching semigroups,
with no hypothesis. -/
theorem gChain_gChain_sep_ae' {J N J' N' : ℕ} (θ : Offspring J) (θ' : Offspring J')
    (hJN : J ≤ N) (h0 : θ 0 = 0) (h1 : 0 < θ 1) (h1' : θ 1 < 1) (hJ2 : 2 ≤ J)
    (hθJ : 0 < θ J) (hJN' : J' ≤ N') (h0' : θ' 0 = 0) (h1'₀ : 0 < θ' 1)
    (h1'' : θ' 1 < 1) (hJ2' : 2 ≤ J') (hθJ' : 0 < θ' J')
    (hsem : AddSubmonoid.closure (shiftSupp θ : Set ℕ)
      ≠ AddSubmonoid.closure (shiftSupp θ' : Set ℕ)) :
    ∀ᵐ ω ∂((gChainLaw θ hJN h0).law.prod (gChainLaw (N := N') θ' hJN' h0').law),
      ¬ GPairQI (gChainLaw θ hJN h0) (gChainLaw θ' hJN' h0') ω :=
  gChain_gChain_sep_ae θ θ' chainSeparation hJN h0 h1 h1' hJ2 hθJ hJN' h0' h1'₀ h1''
    hJ2' hθJ' hsem

/-- **The eventwise form of the complete classification in `thm:trichotomy`**: for almost every
pair of samples, quasi-isometry is equivalent to equality of the class invariant, namely the
coarse regime together with the branching semigroup in the chain regime; the negative
conclusion is almost sure when the invariants differ. -/
theorem trichotomy_ae_iff (R R' : GRegime) :
    ∀ᵐ ω ∂(R.sampleLaw.law.prod R'.sampleLaw.law),
      GPairQI R.sampleLaw R'.sampleLaw ω ↔
        (R.kind = R'.kind ∧
          (R.IsChain → R'.IsChain → R.semigroup = R'.semigroup)) := by
  by_cases hInv : R.kind = R'.kind ∧
      (R.IsChain → R'.IsChain → R.semigroup = R'.semigroup)
  · filter_upwards [same_gRegime_ae' R R' hInv.1 hInv.2] with omega hqi
    exact iff_of_true hqi hInv
  · have hdiff : R.kind ≠ R'.kind ∨
        (R.IsChain ∧ R'.IsChain ∧ R.semigroup ≠ R'.semigroup) := by
      by_cases hk : R.kind = R'.kind
      · right
        have hsem : ¬ (R.IsChain → R'.IsChain → R.semigroup = R'.semigroup) :=
          fun h => hInv ⟨hk, h⟩
        obtain ⟨hR, hsem⟩ := Classical.not_imp.mp hsem
        obtain ⟨hR', hsem⟩ := Classical.not_imp.mp hsem
        exact ⟨hR, hR', hsem⟩
      · exact Or.inl hk
    filter_upwards [diff_gRegime_ae chainSeparation R R' hdiff] with omega hnqi
    exact iff_of_false hnqi hInv

/-- A one-sample corollary of the different-class clause of **`thm:trichotomy`**: outside the ray
class, a sample is almost surely not quasi-isometric to the ray. -/
theorem trichotomy_not_ray (R : GRegime) (hR : R.kind ≠ 0) :
    ∀ᵐ omega ∂R.sampleLaw.law,
      ¬ BranchingProcess.QuasiIsometric (R.sampleLaw.graph omega)
        BranchingProcess.rayGraph :=
  not_ray_gRegime_ae R hR

/-! ### The classification for raw offspring laws -/

/-- The raw regime of an offspring law: ray, full, chain, or bushy. -/
noncomputable def offspringRegimeKind {J : ℕ} (θ : Offspring J) : ℕ :=
  if θ 1 = 1 then 0 else if θ 0 = 0 then if θ 1 = 0 then 1 else 2 else 3

/-- The chain regime read directly from the masses. -/
def offspringIsChain {J : ℕ} (θ : Offspring J) : Prop :=
  θ 0 = 0 ∧ θ 1 ≠ 0 ∧ θ 1 ≠ 1

/-- The mass formulation of `offspringIsChain`. -/
theorem offspringIsChain_iff {J : ℕ} (θ : Offspring J) :
    offspringIsChain θ ↔ θ 0 = 0 ∧ 0 < θ 1 ∧ θ 1 < 1 := by
  constructor
  · rintro ⟨h0, h10, h11⟩
    exact ⟨h0, lt_of_le_of_ne (θ.nonneg 1) (Ne.symm h10),
      lt_of_le_of_ne (θ.mass_le_one 1) h11⟩
  · rintro ⟨h0, h10, h11⟩
    exact ⟨h0, h10.ne', h11.ne⟩

/-- Two raw offspring laws have the invariant prescribed by the classification. -/
def SameOffspringClass {J J' : ℕ} (θ : Offspring J) (θ' : Offspring J') : Prop :=
  offspringRegimeKind θ = offspringRegimeKind θ' ∧
    (offspringIsChain θ → offspringIsChain θ' →
      AddSubmonoid.closure (shiftSupp θ : Set ℕ) =
        AddSubmonoid.closure (shiftSupp θ' : Set ℕ))

/-- The invariant `SameOffspringClass` expanded into the classes (R), (F),
`(C_Λ)`, and (B) of `thm:trichotomy`. -/
theorem sameOffspringClass_iff {J J' : ℕ} (θ : Offspring J) (θ' : Offspring J') :
    SameOffspringClass θ θ' ↔
      (θ 1 = 1 ∧ θ' 1 = 1) ∨
      (θ 0 = 0 ∧ θ 1 = 0 ∧ θ' 0 = 0 ∧ θ' 1 = 0) ∨
      ((θ 0 = 0 ∧ 0 < θ 1 ∧ θ 1 < 1) ∧
        (θ' 0 = 0 ∧ 0 < θ' 1 ∧ θ' 1 < 1) ∧
        AddSubmonoid.closure (shiftSupp θ : Set ℕ) =
          AddSubmonoid.closure (shiftSupp θ' : Set ℕ)) ∨
      (0 < θ 0 ∧ 0 < θ' 0) := by
  rw [SameOffspringClass, offspringIsChain_iff θ, offspringIsChain_iff θ']
  have hpos0 : θ 0 ≠ 0 ↔ 0 < θ 0 :=
    ⟨fun h => lt_of_le_of_ne (θ.nonneg 0) (Ne.symm h), fun h => h.ne'⟩
  have hpos0' : θ' 0 ≠ 0 ↔ 0 < θ' 0 :=
    ⟨fun h => lt_of_le_of_ne (θ'.nonneg 0) (Ne.symm h), fun h => h.ne'⟩
  have hpos1 : θ 1 ≠ 0 ↔ 0 < θ 1 :=
    ⟨fun h => lt_of_le_of_ne (θ.nonneg 1) (Ne.symm h), fun h => h.ne'⟩
  have hpos1' : θ' 1 ≠ 0 ↔ 0 < θ' 1 :=
    ⟨fun h => lt_of_le_of_ne (θ'.nonneg 1) (Ne.symm h), fun h => h.ne'⟩
  have hlt1 : θ 1 ≠ 1 ↔ θ 1 < 1 :=
    ⟨fun h => lt_of_le_of_ne (θ.mass_le_one 1) h, fun h => h.ne⟩
  have hlt1' : θ' 1 ≠ 1 ↔ θ' 1 < 1 :=
    ⟨fun h => lt_of_le_of_ne (θ'.mass_le_one 1) h, fun h => h.ne⟩
  rw [← hpos0, ← hpos0', ← hpos1, ← hpos1', ← hlt1, ← hlt1']
  have hzero := zero_of_one θ
  have hzero' := zero_of_one θ'
  unfold offspringRegimeKind
  split_ifs <;> simp_all

/-- Package a valid offspring law, written with its true top support, into its regime.
For the ray law the first alternative of `htop` avoids an artificial top-support index. -/
noncomputable def GRegime.ofExact {J N : ℕ} (θ : Offspring J) (hJN : J ≤ N)
    (hvalid : θ.IsSupercritical ∨ θ 1 = 1)
    (htop : θ 1 = 1 ∨ (2 ≤ J ∧ 0 < θ J)) : GRegime := by
  classical
  by_cases h1 : θ 1 = 1
  · exact .ray θ hJN h1
  have hsuper : θ.IsSupercritical := hvalid.resolve_right h1
  have htop' : 2 ≤ J ∧ 0 < θ J := htop.resolve_left h1
  by_cases h0 : θ 0 = 0
  · by_cases h10 : θ 1 = 0
    · exact .full θ hJN h0 h10
    · exact .chain θ hJN h0
        (lt_of_le_of_ne (θ.nonneg 1) (Ne.symm h10))
        (lt_of_le_of_ne (θ.mass_le_one 1) h1) htop'.1 htop'.2
  · exact .bushy θ hJN (θ.extinction_lt_one_of_supercritical hsuper)
      (lt_of_le_of_ne (θ.nonneg 0) (Ne.symm h0)) htop'.1 htop'.2

/-- `GRegime.ofExact` carries exactly the invariant read directly from the masses. -/
theorem GRegime.ofExact_invariant_iff {J J' N N' : ℕ}
    (θ : Offspring J) (hJN : J ≤ N)
    (hvalid : θ.IsSupercritical ∨ θ 1 = 1)
    (htop : θ 1 = 1 ∨ (2 ≤ J ∧ 0 < θ J))
    (θ' : Offspring J') (hJN' : J' ≤ N')
    (hvalid' : θ'.IsSupercritical ∨ θ' 1 = 1)
    (htop' : θ' 1 = 1 ∨ (2 ≤ J' ∧ 0 < θ' J')) :
    let R := GRegime.ofExact θ hJN hvalid htop
    let R' := GRegime.ofExact θ' hJN' hvalid' htop'
    (R.kind = R'.kind ∧
      (R.IsChain → R'.IsChain → R.semigroup = R'.semigroup)) ↔
      SameOffspringClass θ θ' := by
  classical
  simp only
  unfold GRegime.ofExact
  split_ifs <;> simp_all [GRegime.kind, GRegime.IsChain, GRegime.semigroup,
    SameOffspringClass, offspringRegimeKind, offspringIsChain]

/-- **The raw-law eventwise form of `thm:trichotomy`.** Every non-ray law is written
with its largest supported offspring number as `J`; this is the second alternative of
`htop`. The conclusion is expressed directly through the masses and branching semigroups. -/
theorem trichotomy_exact_ae_iff {J J' N N' : ℕ}
    (θ : Offspring J) (hJN : J ≤ N)
    (hvalid : θ.IsSupercritical ∨ θ 1 = 1)
    (htop : θ 1 = 1 ∨ (2 ≤ J ∧ 0 < θ J))
    (θ' : Offspring J') (hJN' : J' ≤ N')
    (hvalid' : θ'.IsSupercritical ∨ θ' 1 = 1)
    (htop' : θ' 1 = 1 ∨ (2 ≤ J' ∧ 0 < θ' J')) :
    let R := GRegime.ofExact θ hJN hvalid htop
    let R' := GRegime.ofExact θ' hJN' hvalid' htop'
    ∀ᵐ omega ∂(R.sampleLaw.law.prod R'.sampleLaw.law),
      GPairQI R.sampleLaw R'.sampleLaw omega ↔
        (θ 1 = 1 ∧ θ' 1 = 1) ∨
        (θ 0 = 0 ∧ θ 1 = 0 ∧ θ' 0 = 0 ∧ θ' 1 = 0) ∨
        ((θ 0 = 0 ∧ 0 < θ 1 ∧ θ 1 < 1) ∧
          (θ' 0 = 0 ∧ 0 < θ' 1 ∧ θ' 1 < 1) ∧
          AddSubmonoid.closure (shiftSupp θ : Set ℕ) =
            AddSubmonoid.closure (shiftSupp θ' : Set ℕ)) ∨
        (0 < θ 0 ∧ 0 < θ' 0) := by
  dsimp only
  filter_upwards [trichotomy_ae_iff
    (GRegime.ofExact θ hJN hvalid htop)
    (GRegime.ofExact θ' hJN' hvalid' htop')] with omega homega
  exact homega.trans ((GRegime.ofExact_invariant_iff θ hJN hvalid htop
    θ' hJN' hvalid' htop').trans (sameOffspringClass_iff θ θ'))

/-- **The raw-law form of the one-sample corollary to `thm:trichotomy`.** A valid exact-support
law outside the ray class is almost surely not quasi-isometric to the ray. -/
theorem trichotomy_exact_not_ray {J N : ℕ}
    (θ : Offspring J) (hJN : J ≤ N)
    (hvalid : θ.IsSupercritical ∨ θ 1 = 1)
    (htop : θ 1 = 1 ∨ (2 ≤ J ∧ 0 < θ J)) (h1 : θ 1 ≠ 1) :
    let R := GRegime.ofExact θ hJN hvalid htop
    ∀ᵐ omega ∂R.sampleLaw.law,
      ¬ BranchingProcess.QuasiIsometric (R.sampleLaw.graph omega)
        BranchingProcess.rayGraph := by
  dsimp only
  apply trichotomy_not_ray
  unfold GRegime.ofExact
  split_ifs <;> simp_all [GRegime.kind]

end ChainClasses
