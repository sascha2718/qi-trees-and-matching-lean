/-
`thm:hairy-cross` and `thm:qi-transitive` of `trichotomy.tex`, the law level:
the bushy-regime pair of reduced laws sits inside the hypotheses of
`thm:composite-matching` at `J' ≤ 2J - 1`, and almost sure quasi-isometry
composes across independent samples.

* `hairyCross_chart`: **the chart of
  `thm:hairy-cross`\labelcref{it:hairy-cross-core}**: the exceptional arities
  are `{J+1, …, J'}`, each carrying the composite pair `(z + 1 - J, J)` in the
  core `{2, …, J}`, with no chart below `J + 1`.
* `hairyCross_core_charged`, `hairyCross_pair_floor`: **the full-support
  clauses**: both reduced laws charge every core arity by `thm:full-support`,
  and every composite pair carries a positive tilt floor depending on the two
  laws alone.
* the composition `QuasiIsometric.trans` lives in `Trichotomy.lean` with the
  reflexivity and the quasi-inverse.
* `pairQI_trans`: **`thm:qi-transitive`**, the composition step: if two
  independent samples of `P₀, P₁` are almost surely quasi-isometric and
  likewise for `P₁, P₂`, then so are two independent samples of `P₀, P₂`,
  realised through the triple product and one Fubini slice.

The label-law half of `thm:cross-relabel` is the scalar layer of `Relabel`
(`relabel_law`, `product_of_constant_conditional`); its comparability clause
waits on the metric realisation of general shapes, as the plan records.
-/
import ChainClasses.Trichotomy
import ChainClasses.GeneralHarris

namespace ChainClasses

/-! ### The chart of the bushy cross-law -/

/-- **The chart of `thm:hairy-cross`**: at `J' ≤ 2J - 1` the exceptional
arities `{J+1, …, J'}` carry the composite pairs `(z + 1 - J, J)`, both
components in the core `{2, …, J}`, and nothing else is charted. -/
theorem hairyCross_chart {J J' : ℕ} (hJ2 : 2 ≤ J)
    (hJ'2 : J' ≤ 2 * J - 1) :
    ∃ exc : ℕ → Option (ℕ × ℕ),
      (∀ j, j ≤ J → exc j = none) ∧
      (∀ z p, exc z = some p →
        p.1 = z + 1 - J ∧ p.2 = J ∧ 2 ≤ p.1 ∧ p.1 ≤ J ∧ 2 ≤ p.2 ∧ p.2 ≤ J ∧
          p.1 + p.2 - 1 = z) ∧
      (∀ z, exc z ≠ none ↔ J + 1 ≤ z ∧ z ≤ J') := by
  classical
  refine ⟨fun z ↦ if h : J + 1 ≤ z ∧ z ≤ J' then some (z + 1 - J, J) else none,
    ?_, ?_, ?_⟩
  · intro j hj
    exact dif_neg fun hcon ↦ absurd hcon.1 (by omega)
  · intro z p hp
    by_cases h : J + 1 ≤ z ∧ z ≤ J'
    · have hp' : (if h' : J + 1 ≤ z ∧ z ≤ J' then some ((z + 1 - J, J) : ℕ × ℕ)
          else none) = some p := hp
      rw [dif_pos h] at hp'
      have hpair := Option.some.inj hp'
      have hpa : p.1 = z + 1 - J := by rw [← hpair]
      have hpb : p.2 = J := by rw [← hpair]
      exact ⟨hpa, hpb, by omega, by omega, by omega, by omega, by omega⟩
    · have hp' : (if h' : J + 1 ≤ z ∧ z ≤ J' then some ((z + 1 - J, J) : ℕ × ℕ)
          else none) = some p := hp
      rw [dif_neg h] at hp'
      simp at hp'
  · intro z
    by_cases h : J + 1 ≤ z ∧ z ≤ J'
    · constructor
      · intro _
        exact h
      · intro _
        show (if h' : J + 1 ≤ z ∧ z ≤ J' then some ((z + 1 - J, J) : ℕ × ℕ)
          else none) ≠ none
        rw [dif_pos h]
        exact Option.some_ne_none _
    · constructor
      · intro hne
        exact absurd (dif_neg h) hne
      · intro hcon
        exact absurd hcon h

/-- **The common core is charged by both reduced laws**, by
`thm:full-support`. -/
theorem hairyCross_core_charged {J J' : ℕ} (θ θ' : ℕ → ℝ) {q q' : ℝ}
    (hnn : ∀ j, 0 ≤ θ j) (hnn' : ∀ j, 0 ≤ θ' j)
    (hJ : 0 < θ J) (hJ' : 0 < θ' J')
    (hq0 : 0 < q) (hq1 : q < 1) (hq'0 : 0 < q') (hq'1 : q' < 1)
    (hsub : genDeriv J θ q < 1) (hsub' : genDeriv J' θ' q' < 1)
    (hJJ' : J ≤ J') {k : ℕ} (hk2 : 2 ≤ k) (hkJ : k ≤ J) :
    0 < reducedLaw J θ q k ∧ 0 < reducedLaw J' θ' q' k :=
  ⟨reducedLaw_pos J θ hnn hJ hq0 hq1 hsub (by omega) hkJ,
    reducedLaw_pos J' θ' hnn' hJ' hq'0 hq'1 hsub' (by omega) (by omega)⟩

/-- **The floor of a composite pair of `thm:hairy-cross`**: the tilt floor
`(1/2) ν̃'_{z+1-J} ν̃'_J` is positive and depends on the two laws alone. -/
theorem hairyCross_pair_floor {J J' : ℕ} (θ' : ℕ → ℝ) {q' : ℝ}
    (hnn' : ∀ j, 0 ≤ θ' j) (hJ' : 0 < θ' J')
    (hq'0 : 0 < q') (hq'1 : q' < 1) (hsub' : genDeriv J' θ' q' < 1)
    (hJ2 : 2 ≤ J) (hJJ' : J ≤ J')
    {z : ℕ} (hz1 : J + 1 ≤ z) (hz2 : z ≤ J') :
    0 < (1 / 2) * (reducedLaw J' θ' q' (z + 1 - J) * reducedLaw J' θ' q' J) := by
  have h1 : 0 < reducedLaw J' θ' q' (z + 1 - J) :=
    reducedLaw_pos J' θ' hnn' hJ' hq'0 hq'1 hsub' (by omega) (by omega)
  have h2 : 0 < reducedLaw J' θ' q' J :=
    reducedLaw_pos J' θ' hnn' hJ' hq'0 hq'1 hsub' (by omega) (by omega)
  positivity

/-! ### Transitivity across independent samples -/

open MeasureTheory
open BranchingProcess (QuasiIsometric IsQIWith)

/-- An almost sure property of the first two coordinates lifts to the triple
product. -/
lemma ae_pair_fst {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {τ : Measure γ}
    [SFinite μ] [SFinite ν] [IsProbabilityMeasure τ] {p : α × β → Prop}
    (h : ∀ᵐ ω ∂(μ.prod ν), p ω) :
    ∀ᵐ ω ∂(μ.prod (ν.prod τ)), p (ω.1, ω.2.1) := by
  rw [ae_iff] at h ⊢
  obtain ⟨T, hsub, hmeas, hnull⟩ := exists_measurable_superset_of_null h
  refine measure_mono_null (t := (fun ω : α × β × γ ↦ (ω.1, ω.2.1)) ⁻¹' T)
    (fun ω hω ↦ Set.mem_preimage.mpr (hsub hω)) ?_
  show μ.prod (ν.prod τ) ((fun ω : α × β × γ ↦ (ω.1, ω.2.1)) ⁻¹' T) = 0
  have hpre : (MeasurableEquiv.prodAssoc ⁻¹'
      ((fun ω : α × β × γ ↦ (ω.1, ω.2.1)) ⁻¹' T)) = T ×ˢ (Set.univ : Set γ) := by
    ext ⟨⟨a, b⟩, c⟩
    simp [MeasurableEquiv.prodAssoc]
  have hmp := (measurePreserving_prodAssoc μ ν τ).map_eq
  rw [← hmp, MeasurableEquiv.map_apply, hpre, Measure.prod_prod, hnull, zero_mul]

/-- An almost sure property of the outer two coordinates of the triple product
descends to their product, through one Fubini slice in the middle
coordinate. -/
lemma ae_pair_outer {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {τ : Measure γ}
    [SFinite μ] [SFinite ν] [SFinite τ] [IsProbabilityMeasure ν] {p : α × γ → Prop}
    (h : ∀ᵐ ω ∂(μ.prod (ν.prod τ)), p (ω.1, ω.2.2)) :
    ∀ᵐ ω ∂(μ.prod τ), p ω := by
  rw [ae_iff] at h ⊢
  obtain ⟨T, hsub, hmeas, hnull⟩ := exists_measurable_superset_of_null h
  -- move the middle coordinate to the front
  have hmpInv : MeasurePreserving (fun ω : β × α × γ ↦ (ω.2.1, (ω.1, ω.2.2)))
      (ν.prod (μ.prod τ)) (μ.prod (ν.prod τ)) := by
    have mp1 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm)
        (ν.prod (μ.prod τ)) ((ν.prod μ).prod τ) :=
      (measurePreserving_prodAssoc ν μ τ).symm MeasurableEquiv.prodAssoc
    have mp2 : MeasurePreserving (Prod.map Prod.swap (id : γ → γ))
        ((ν.prod μ).prod τ) ((μ.prod ν).prod τ) :=
      (Measure.measurePreserving_swap (μ := ν) (ν := μ)).prod (MeasurePreserving.id τ)
    have mp3 : MeasurePreserving (MeasurableEquiv.prodAssoc)
        ((μ.prod ν).prod τ) (μ.prod (ν.prod τ)) :=
      measurePreserving_prodAssoc μ ν τ
    exact (mp3.comp mp2).comp mp1
  set T' : Set (β × α × γ) := (fun ω : β × α × γ ↦ (ω.2.1, (ω.1, ω.2.2))) ⁻¹' T
    with hT'
  have hT'meas : MeasurableSet T' := hmpInv.measurable hmeas
  have hT'null : ν.prod (μ.prod τ) T' = 0 := by
    rw [hT', hmpInv.measure_preimage hmeas.nullMeasurableSet, hnull]
  have hsec := (Measure.measure_prod_null hT'meas).mp hT'null
  have hexists : ∃ b : β, μ.prod τ (Prod.mk b ⁻¹' T') = 0 := by
    have hne : ν ≠ 0 := IsProbabilityMeasure.ne_zero ν
    have : (MeasureTheory.ae ν).NeBot := ae_neBot.mpr hne
    exact hsec.exists
  obtain ⟨b, hb⟩ := hexists
  refine measure_mono_null (fun ac hac ↦ ?_) hb
  show (b, ac) ∈ T'
  rw [hT']
  exact Set.mem_preimage.mpr (hsub hac)

/-- **`thm:qi-transitive`**, the composition step: almost sure quasi-isometry
of independent samples composes through the triple product. -/
theorem pairQI_trans (L0 L1 L2 : SampleLaw)
    (h01 : ∀ᵐ ω ∂(L0.law.prod L1.law), PairQI L0 L1 ω)
    (h12 : ∀ᵐ ω ∂(L1.law.prod L2.law), PairQI L1 L2 ω) :
    ∀ᵐ ω ∂(L0.law.prod L2.law), PairQI L0 L2 ω := by
  have hlift01 := ae_pair_fst (τ := L2.law) h01
  have hlift12 : ∀ᵐ ω ∂(L0.law.prod (L1.law.prod L2.law)), PairQI L1 L2 ω.2 :=
    ae_of_snd h12
  have htrip : ∀ᵐ ω ∂(L0.law.prod (L1.law.prod L2.law)),
      PairQI L0 L2 (ω.1, ω.2.2) := by
    filter_upwards [hlift01, hlift12] with ω h1 h2
    exact QuasiIsometric.trans
      (wordGraph_connected (L2.prefixClosed ω.2.2) ⟨⟨[], L2.root ω.2.2⟩⟩) h1 h2
  exact ae_pair_outer htrip

end ChainClasses
