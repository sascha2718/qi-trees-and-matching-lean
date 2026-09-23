import ChainClasses.Chain.Coupling
import ChainClasses.TwoValue
import ChainClasses.Chain.TransferReal

/-!
`thm:cross-law` of `gw_classes_simple.tex`, assembled as in `thm:cross-law`:
two independent samples of two different two-value offspring laws are
quasi-isometric with high probability, at the rate `eq:rate-cross`.

* `uniField`, `crossMeasure`: the extra uniform variable of
  `thm:chain-coupling` at every vertex, and the law of the whole experiment,
  the first sample, the second sample and the uniform field.
* `markLab`: the coupled class `ℓ'(λ'(w), U(w))` of the second sample.
* `chainMeasure_label_map`, `chainMeasure_class_lintegral`,
  `markedMeasure_class_prod`, `markedMeasure_class_marginal`,
  `markedMeasure_class_iIndepFun`: the coupled classes of the second sample are
  i.i.d. with the class law `p^{(D)}` of the first. The joint law over a
  finite set of vertices factorises into the class masses, which gives the
  marginal at one vertex, clause (ii) of `thm:chain-coupling`, and the
  independence of the family.
* `crossMeasure_map`: the level-`h` projections of the two quantised fields
  are two independent `μ_h`-labellings, the `hlaw` hypothesis of the i.i.d.
  matching theorem.
* `crossMatchEvent`, `cross_matching_prob_ge`: the matching event at scale `D`
  and its probability, the potential bound of `thm:eta-bound` supplying the
  hypothesis; `portrait_of_crossMatchEvent` reads a portrait off it.
* `gammaStar`, `crossConst`, `cross_comparable`, `qi_of_cross_matching`: the
  factor `γ_* = max(1,γ)/min(1,γ/2)`, the integer scale `⌈γ_* D²⌉`, the
  comparison of the two chain lengths at matched classes, and the
  deterministic core producing a `(⌈γ_* D²⌉+3)`-quasi-isometry.
* `crosslaw_rate`, `crosslaw_ae`, and their `InTree` forms
  `crosslaw_rate_tree`, `crosslaw_ae_tree`.

The four largeness conditions `eq:d0-conditions` are carried as hypotheses, and
alongside them the condition `γ(D-1) ≥ 1` of `thm:chain-coupling`.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory GraphMatching
open scoped ENNReal

variable {a b t t' : ℝ}

/-! ### The uniform field

One uniform variable on `[0,1)` at every vertex, independent of everything
else: the randomisation that `thm:chain-coupling` feeds to the class map of the
second law. -/

/-- The uniform law on `[0,1)` is a probability measure. -/
instance isProbabilityMeasure_uniform_Ico :
    IsProbabilityMeasure (volume.restrict (Set.Ico (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ico]; simp⟩

/-- The field of independent uniform variables, one at each vertex. -/
noncomputable def uniField : Measure (Word → ℝ) :=
  BranchingProcess.fieldMeasure (volume.restrict (Set.Ico (0 : ℝ) 1))

instance isProbabilityMeasure_uniField : IsProbabilityMeasure uniField :=
  inferInstanceAs (IsProbabilityMeasure
    (BranchingProcess.fieldMeasure (volume.restrict (Set.Ico (0 : ℝ) 1))))

/-- The uniform field factorises over a finite set of vertices. -/
lemma uniField_iInter (S : Finset Word) (A : Word → Set ℝ) (hA : ∀ w ∈ S, MeasurableSet (A w)) :
    uniField (⋂ w ∈ S, (BranchingProcess.coord w : (Word → ℝ) → ℝ) ⁻¹' A w)
      = ∏ w ∈ S, (volume.restrict (Set.Ico (0 : ℝ) 1)) (A w) := by
  rw [uniField, (BranchingProcess.coord_iIndepFun
    (volume.restrict (Set.Ico (0 : ℝ) 1))).measure_inter_preimage_eq_mul S hA]
  exact Finset.prod_congr rfl fun w hw ↦
    BranchingProcess.coord_law (volume.restrict (Set.Ico (0 : ℝ) 1)) w (hA w hw)

/-! ### The cross-law space -/

/-- The law of the second sample together with its uniform field. -/
noncomputable def markedMeasure (ht' : 0 < t') (ht1' : t' ≤ 1) :
    Measure ((Word → Bool) × (Word → ℝ)) :=
  (chainMeasure ht' ht1').prod uniField

instance isProbabilityMeasure_markedMeasure (ht' : 0 < t') (ht1' : t' ≤ 1) :
    IsProbabilityMeasure (markedMeasure ht' ht1') :=
  inferInstanceAs (IsProbabilityMeasure ((chainMeasure ht' ht1').prod uniField))

/-- **The cross-law space**: the first sample, the second sample drawn from the
other two-value law, and the uniform field, all independent. -/
noncomputable def crossMeasure (ht : 0 < t) (ht1 : t ≤ 1) (ht' : 0 < t') (ht1' : t' ≤ 1) :
    Measure ((Word → Bool) × (Word → Bool) × (Word → ℝ)) :=
  (chainMeasure ht ht1).prod (markedMeasure ht' ht1')

instance isProbabilityMeasure_crossMeasure (ht : 0 < t) (ht1 : t ≤ 1) (ht' : 0 < t')
    (ht1' : t' ≤ 1) : IsProbabilityMeasure (crossMeasure ht ht1 ht' ht1') :=
  inferInstanceAs (IsProbabilityMeasure ((chainMeasure ht ht1).prod (markedMeasure ht' ht1')))

/-- The label field of the first sample. -/
noncomputable def labCFst (ω : (Word → Bool) × (Word → Bool) × (Word → ℝ)) : Word → ℕ :=
  labAux ω.1

/-- The label field of the second sample. -/
noncomputable def labCSnd (ω : (Word → Bool) × (Word → Bool) × (Word → ℝ)) : Word → ℕ :=
  labAux ω.2.1

/-! ### The coupled classes of the second sample -/

/-- The coupled class of the second sample at a vertex: the class map `ℓ'` of
`thm:chain-coupling` applied to the chain length there and to the uniform
variable sitting at the same vertex. -/
noncomputable def markLab (a b : ℝ) (D : ℕ) (p : (Word → Bool) × (Word → ℝ)) (w : Word) : ℕ :=
  ellQ a b D (labAux p.1 w) (p.2 w)

/-- The class events of the second sample are measurable. -/
lemma measurableSet_markLab_fibre (a b : ℝ) (D : ℕ) (w : Word) (k : ℕ) :
    MeasurableSet {p : (Word → Bool) × (Word → ℝ) | markLab a b D p w = k} := by
  have hset : {p : (Word → Bool) × (Word → ℝ) | markLab a b D p w = k}
      = ⋃ m : ℕ, {χ : Word → Bool | labAux χ w = m}
          ×ˢ {u : Word → ℝ | ellQ a b D m (u w) = k} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, markLab]
    constructor
    · intro h
      exact ⟨labAux p.1 w, rfl, h⟩
    · rintro ⟨m, h1, h2⟩
      have hm : labAux p.1 w = m := h1
      rw [hm]
      exact h2
  rw [hset]
  refine MeasurableSet.iUnion fun m ↦ (measurableSet_chain_labAux w m).prod ?_
  exact (BranchingProcess.measurable_coord w) (ellQ_section_measurable a b D m k)

/-- The coupled class at a vertex is a measurable function. -/
lemma measurable_markLab (a b : ℝ) (D : ℕ) (w : Word) :
    Measurable fun p : (Word → Bool) × (Word → ℝ) ↦ markLab a b D p w :=
  measurable_to_countable' fun k ↦ measurableSet_markLab_fibre a b D w k

/-- The pair of a chain length and a uniform variable has a measurable class
event, the set entering clause (ii) of `thm:chain-coupling`. -/
lemma measurableSet_ellQ_pair (a b : ℝ) (D k : ℕ) :
    MeasurableSet {p : ℕ × ℝ | ellQ a b D p.1 p.2 = k} := by
  have hset : {p : ℕ × ℝ | ellQ a b D p.1 p.2 = k}
      = ⋃ n : ℕ, ({n} : Set ℕ) ×ˢ {u : ℝ | ellQ a b D n u = k} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨p.1, rfl, h⟩
    · rintro ⟨n, h1, h2⟩
      rw [h1]
      exact h2
  rw [hset]
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_singleton n).prod (ellQ_section_measurable a b D n k)

/-- The chain length of the second sample has the geometric law `ℙ(λ' = m) =
(θ₁')^{m-1}(1 - θ₁')` packaged by `geomPMF`. -/
lemma chainMeasure_label_map (ht' : 0 < t') (ht1' : t' ≤ 1) (hb : (0 : ℝ) < 1 - t')
    (hb1 : (1 : ℝ) - t' < 1) (w : Word) :
    (chainMeasure ht' ht1').map (fun χ : Word → Bool ↦ labAux χ w)
      = (geomPMF hb hb1).toMeasure := by
  refine Measure.ext_of_singleton fun m ↦ ?_
  rw [Measure.map_apply (measurable_chain_labAux w) (measurableSet_singleton m),
    PMF.toMeasure_apply_singleton _ m (measurableSet_singleton m), geomPMF_apply]
  have hpre : (fun χ : Word → Bool ↦ labAux χ w) ⁻¹' {m}
      = {χ : Word → Bool | labAux χ w = m} := rfl
  rw [hpre]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [chainMeasure_labAux_zero ht' ht1' w, show gmass (1 - t') 0 = 0 from rfl,
      ENNReal.ofReal_zero]
  · rw [chainMeasure_label_marginal ht' ht1' w hm]
    congr 1
    unfold gmass
    rw [ite_eq_right (by omega : ¬ m = 0)]
    ring

/-- **Clause (ii) of `thm:chain-coupling` at one vertex**: averaging the
`u`-measure of the class over the chain length gives the class mass `p^{(D)}_k`. -/
lemma chainMeasure_class_lintegral (ht' : 0 < t') (ht1' : t' ≤ 1) (ha : (0 : ℝ) < 1 - t)
    (ha1 : (1 : ℝ) - t < 1) (hb : (0 : ℝ) < 1 - t') (hb1 : (1 : ℝ) - t' < 1) {D : ℕ}
    (hD : 2 ≤ D) (hgD : 1 ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1)) (w : Word) (k : ℕ) :
    ∫⁻ χ : Word → Bool, (volume.restrict (Set.Ico (0 : ℝ) 1))
        {u : ℝ | ellQ (1 - t) (1 - t') D (labAux χ w) u = k} ∂(chainMeasure ht' ht1')
      = ENNReal.ofReal (qF (1 - t) D k) := by
  have hcl := coupling_law ha ha1 hb hb1 hD hgD k
  rw [Measure.prod_apply (measurableSet_ellQ_pair (1 - t) (1 - t') D k)] at hcl
  have hmap : ∫⁻ m : ℕ, (volume.restrict (Set.Ico (0 : ℝ) 1))
        {u : ℝ | ellQ (1 - t) (1 - t') D m u = k}
        ∂((chainMeasure ht' ht1').map (fun χ : Word → Bool ↦ labAux χ w))
      = ∫⁻ χ : Word → Bool, (volume.restrict (Set.Ico (0 : ℝ) 1))
        {u : ℝ | ellQ (1 - t) (1 - t') D (labAux χ w) u = k} ∂(chainMeasure ht' ht1') :=
    lintegral_map measurable_from_top (measurable_chain_labAux w)
  rw [← hmap, chainMeasure_label_map ht' ht1' hb hb1 w]
  exact hcl

/-- **The independence clause across the coupling**: the coupled classes of the
second sample factorise over a finite set of vertices into the class masses of
`p^{(D)}`. The uniform field factorises at fixed chain lengths, and the chain
lengths themselves are independent. -/
theorem markedMeasure_class_prod (ht' : 0 < t') (ht1' : t' ≤ 1) (ha : (0 : ℝ) < 1 - t)
    (ha1 : (1 : ℝ) - t < 1) (hb : (0 : ℝ) < 1 - t') (hb1 : (1 : ℝ) - t' < 1) {D : ℕ}
    (hD : 2 ≤ D) (hgD : 1 ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1)) (S : Finset Word)
    (n : Word → ℕ) :
    markedMeasure ht' ht1'
        (⋂ w ∈ S, {p : (Word → Bool) × (Word → ℝ) | markLab (1 - t) (1 - t') D p w = n w})
      = ∏ w ∈ S, ENNReal.ofReal (qF (1 - t) D (n w)) := by
  have hE : MeasurableSet
      (⋂ w ∈ S, {p : (Word → Bool) × (Word → ℝ) | markLab (1 - t) (1 - t') D p w = n w}) :=
    MeasurableSet.iInter fun w ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_markLab_fibre (1 - t) (1 - t') D w (n w)
  have hfib : ∀ χ : Word → Bool,
      uniField (Prod.mk χ ⁻¹'
          (⋂ w ∈ S, {p : (Word → Bool) × (Word → ℝ) | markLab (1 - t) (1 - t') D p w = n w}))
        = ∏ w ∈ S, (volume.restrict (Set.Ico (0 : ℝ) 1))
            {u : ℝ | ellQ (1 - t) (1 - t') D (labAux χ w) u = n w} := by
    intro χ
    have hslice : Prod.mk χ ⁻¹'
        (⋂ w ∈ S, {p : (Word → Bool) × (Word → ℝ) | markLab (1 - t) (1 - t') D p w = n w})
        = ⋂ w ∈ S, (BranchingProcess.coord w : (Word → ℝ) → ℝ) ⁻¹'
            {u : ℝ | ellQ (1 - t) (1 - t') D (labAux χ w) u = n w} := by
      ext u
      simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq, markLab,
        BranchingProcess.coord]
    rw [hslice, uniField_iInter S _
      fun w _ ↦ ellQ_section_measurable (1 - t) (1 - t') D (labAux χ w) (n w)]
  have hFmeas : ∀ w : Word, Measurable fun χ : Word → Bool ↦
      (volume.restrict (Set.Ico (0 : ℝ) 1))
        {u : ℝ | ellQ (1 - t) (1 - t') D (labAux χ w) u = n w} :=
    fun w ↦ (measurable_from_top (f := fun m : ℕ ↦ (volume.restrict (Set.Ico (0 : ℝ) 1))
      {u : ℝ | ellQ (1 - t) (1 - t') D m u = n w})).comp (measurable_chain_labAux w)
  have hFindep : iIndepFun (fun (w : Word) (χ : Word → Bool) ↦
      (volume.restrict (Set.Ico (0 : ℝ) 1))
        {u : ℝ | ellQ (1 - t) (1 - t') D (labAux χ w) u = n w}) (chainMeasure ht' ht1') :=
    (chainMeasure_label_iIndepFun ht' ht1').comp
      (fun w : Word ↦ fun m : ℕ ↦ (volume.restrict (Set.Ico (0 : ℝ) 1))
        {u : ℝ | ellQ (1 - t) (1 - t') D m u = n w}) fun _ ↦ measurable_from_top
  rw [markedMeasure, Measure.prod_apply hE, lintegral_congr hfib,
    lintegral_prod_eq_prod_lintegral_of_indepFun S _ hFindep hFmeas]
  exact Finset.prod_congr rfl fun w _ ↦
    chainMeasure_class_lintegral ht' ht1' ha ha1 hb hb1 hD hgD w (n w)

/-- **The marginal clause across the coupling**: the coupled class of the
second sample at a vertex has the class masses `p^{(D)}_k` of the first. -/
theorem markedMeasure_class_marginal (ht' : 0 < t') (ht1' : t' ≤ 1) (ha : (0 : ℝ) < 1 - t)
    (ha1 : (1 : ℝ) - t < 1) (hb : (0 : ℝ) < 1 - t') (hb1 : (1 : ℝ) - t' < 1) {D : ℕ}
    (hD : 2 ≤ D) (hgD : 1 ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1)) (w : Word) (k : ℕ) :
    markedMeasure ht' ht1'
        {p : (Word → Bool) × (Word → ℝ) | markLab (1 - t) (1 - t') D p w = k}
      = ENNReal.ofReal (qF (1 - t) D k) := by
  have h := markedMeasure_class_prod ht' ht1' ha ha1 hb hb1 hD hgD {w} (fun _ ↦ k)
  rwa [Finset.set_biInter_singleton, Finset.prod_singleton] at h

/-- The π-system of coupled-class events at a vertex. -/
private def classPi (a b : ℝ) (D : ℕ) (w : Word) : Set (Set ((Word → Bool) × (Word → ℝ))) :=
  {A | ∃ k : ℕ, A = (fun p ↦ markLab a b D p w) ⁻¹' {k}}

/-- The class events at a vertex are closed under intersection. -/
private lemma classPi_isPiSystem (a b : ℝ) (D : ℕ) (w : Word) :
    IsPiSystem (classPi a b D w) := by
  rintro A ⟨k, rfl⟩ B ⟨k', rfl⟩ hAB
  obtain ⟨p, hp, hp'⟩ := hAB
  have hk : k = k' := by
    have h1 : markLab a b D p w = k := hp
    have h2 : markLab a b D p w = k' := hp'
    omega
  subst hk
  rw [Set.inter_self]
  exact ⟨k, rfl⟩

/-- The class events generate the σ-algebra of the coupled class at a vertex. -/
private lemma comap_markLab_eq (a b : ℝ) (D : ℕ) (w : Word) :
    MeasurableSpace.comap (fun p : (Word → Bool) × (Word → ℝ) ↦ markLab a b D p w) inferInstance
      = MeasurableSpace.generateFrom (classPi a b D w) := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · rw [MeasurableSpace.le_def]
    rintro A ⟨S, -, rfl⟩
    have hdecomp : (fun p : (Word → Bool) × (Word → ℝ) ↦ markLab a b D p w) ⁻¹' S
        = ⋃ k ∈ S, (fun p : (Word → Bool) × (Word → ℝ) ↦ markLab a b D p w) ⁻¹' {k} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨fun h ↦ ⟨_, h, rfl⟩, by rintro ⟨k, hk, rfl⟩; exact hk⟩
    rw [hdecomp]
    exact MeasurableSet.biUnion (Set.to_countable S) fun k _ ↦
      MeasurableSpace.measurableSet_generateFrom ⟨k, rfl⟩
  · rintro A ⟨k, rfl⟩
    exact ⟨{k}, measurableSet_singleton k, rfl⟩

/-- **The coupled classes are i.i.d.**: the class field of the second sample is
an independent family, and by `markedMeasure_class_marginal` each member has
the class law `p^{(D)}` of the first sample. -/
theorem markedMeasure_class_iIndepFun (ht' : 0 < t') (ht1' : t' ≤ 1) (ha : (0 : ℝ) < 1 - t)
    (ha1 : (1 : ℝ) - t < 1) (hb : (0 : ℝ) < 1 - t') (hb1 : (1 : ℝ) - t' < 1) {D : ℕ}
    (hD : 2 ≤ D) (hgD : 1 ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1)) :
    iIndepFun (fun (w : Word) (p : (Word → Bool) × (Word → ℝ)) ↦
      markLab (1 - t) (1 - t') D p w) (markedMeasure ht' ht1') := by
  rw [iIndepFun_iff_iIndep]
  refine iIndepSets.iIndep
    (fun w ↦ (measurable_markLab (1 - t) (1 - t') D w).comap_le)
    (classPi (1 - t) (1 - t') D) (fun w ↦ classPi_isPiSystem _ _ D w)
    (fun w ↦ comap_markLab_eq _ _ D w) ?_
  rw [iIndepSets_iff]
  intro S f hf
  have hf' : ∀ w : Word, ∃ k : ℕ, w ∈ S →
      f w = (fun p : (Word → Bool) × (Word → ℝ) ↦ markLab (1 - t) (1 - t') D p w) ⁻¹' {k} := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨k, hk⟩ := hf w hw
      exact ⟨k, fun _ ↦ hk⟩
    · exact ⟨0, fun h ↦ absurd h hw⟩
  choose n hn using hf'
  have hset : ∀ w, w ∈ S →
      f w = {p : (Word → Bool) × (Word → ℝ) | markLab (1 - t) (1 - t') D p w = n w} :=
    fun w hw ↦ hn w hw
  rw [Set.iInter₂_congr hset, markedMeasure_class_prod ht' ht1' ha ha1 hb hb1 hD hgD S n]
  refine (Finset.prod_congr rfl fun w hw ↦ ?_).symm
  rw [hset w hw]
  exact markedMeasure_class_marginal ht' ht1' ha ha1 hb hb1 hD hgD w (n w)

/-! ### The level projections of the two quantised fields -/

/-- The level-`h` projection of the quantised label field of the first sample. -/
noncomputable def cqX (D h : ℕ) (ω : (Word → Bool) × (Word → Bool) × (Word → ℝ)) :
    FullLab ℕ h :=
  readLab (fun s ↦ levelMap D (labAux ω.1 s)) h

/-- The level-`h` projection of the coupled class field of the second sample. -/
noncomputable def cqY (a b : ℝ) (D h : ℕ) (ω : (Word → Bool) × (Word → Bool) × (Word → ℝ)) :
    FullLab ℕ h :=
  readLab (fun s ↦ markLab a b D ω.2 s) h

/-- The projections are compatible: dropping the deepest level of `cqX` at
height `h+1` gives `cqX` at height `h`. -/
lemma restrictLab_cqX (D h : ℕ) (ω : (Word → Bool) × (Word → Bool) × (Word → ℝ)) :
    restrictLab h (cqX D (h + 1) ω) = cqX D h ω :=
  restrictLab_readLab h _

/-- The same for the second sample. -/
lemma restrictLab_cqY (a b : ℝ) (D h : ℕ) (ω : (Word → Bool) × (Word → Bool) × (Word → ℝ)) :
    restrictLab h (cqY a b D (h + 1) ω) = cqY a b D h ω :=
  restrictLab_readLab h _

/-- The pair of level-`h` projections is measurable. -/
lemma measurable_cqXY (a b : ℝ) (D h : ℕ) :
    Measurable fun ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) ↦
      (cqX D h ω, cqY a b D h ω) := by
  have hfst : Measurable fun ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) ↦
      fun s : Word ↦ levelMap D (labAux ω.1 s) :=
    Measurable.of_eval fun s ↦
      (measurable_from_top (f := levelMap D)).comp
        ((measurable_chain_labAux s).comp measurable_fst)
  have hsnd : Measurable fun ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) ↦
      fun s : Word ↦ markLab a b D ω.2 s :=
    Measurable.of_eval fun s ↦ (measurable_markLab a b D s).comp measurable_snd
  exact ((measurable_readLab h).comp hfst).prodMk ((measurable_readLab h).comp hsnd)

/-- The level-`h` projection of the coupled class field has the i.i.d. law
`μ_h` of the quantised geometric law of the **first** sample. -/
lemma markedMeasure_readLab (ht : 0 < t) (ht1 : t ≤ 1) (ht' : 0 < t') (ht1' : t' ≤ 1)
    (ha : (0 : ℝ) < 1 - t) (ha1 : (1 : ℝ) - t < 1) (hb : (0 : ℝ) < 1 - t')
    (hb1 : (1 : ℝ) - t' < 1) {D : ℕ} (hD : 2 ≤ D)
    (hgD : 1 ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1)) (h : ℕ) (y : FullLab ℕ h) :
    markedMeasure ht' ht1'
        {p : (Word → Bool) × (Word → ℝ) | readLab (fun s ↦ markLab (1 - t) (1 - t') D p s) h = y}
      = fullMu (chainQPMF ht ht1 hD) h y := by
  have hset : {p : (Word → Bool) × (Word → ℝ) |
        readLab (fun s ↦ markLab (1 - t) (1 - t') D p s) h = y}
      = ⋂ s ∈ Vtx h, {p : (Word → Bool) × (Word → ℝ) |
          markLab (1 - t) (1 - t') D p s = GraphMatching.coord h y s} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact readLab_eq_iff h _ y
  rw [hset, markedMeasure_class_prod ht' ht1' ha ha1 hb hb1 hD hgD (Vtx h)
      (fun s ↦ GraphMatching.coord h y s), fullMu_apply_prod]
  exact Finset.prod_congr rfl fun s _ ↦ rfl

/-- **The cross-law two-sample law**: the pair of level-`h` projections of the
quantised label field and of the coupled class field is distributed as two
independent `μ_h`-labellings. This is the `hlaw` hypothesis of
`infinite_tree_matching_prob_of_law`. -/
lemma crossMeasure_map (ht : 0 < t) (ht1 : t ≤ 1) (ht' : 0 < t') (ht1' : t' ≤ 1)
    (ha : (0 : ℝ) < 1 - t) (ha1 : (1 : ℝ) - t < 1) (hb : (0 : ℝ) < 1 - t')
    (hb1 : (1 : ℝ) - t' < 1) {D : ℕ} (hD : 2 ≤ D)
    (hgD : 1 ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1)) (h : ℕ) :
    (crossMeasure ht ht1 ht' ht1').map (fun ω ↦ (cqX D h ω, cqY (1 - t) (1 - t') D h ω))
      = (prodPMF (fullMu (chainQPMF ht ht1 hD) h)
          (fullMu (chainQPMF ht ht1 hD) h)).toMeasure := by
  refine Measure.ext_of_singleton fun z ↦ ?_
  obtain ⟨x, y⟩ := z
  rw [Measure.map_apply (measurable_cqXY (1 - t) (1 - t') D h) (measurableSet_singleton _)]
  have hpre : (fun ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) ↦
        (cqX D h ω, cqY (1 - t) (1 - t') D h ω)) ⁻¹' {(x, y)}
      = {χ : Word → Bool | readLab (fun s ↦ levelMap D (labAux χ s)) h = x}
        ×ˢ {p : (Word → Bool) × (Word → ℝ) |
          readLab (fun s ↦ markLab (1 - t) (1 - t') D p s) h = y} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Set.mem_ofPred_eq,
      Prod.mk.injEq, cqX, cqY]
  rw [hpre, crossMeasure, Measure.prod_prod, chainMeasure_readLab ht ht1 hD,
    markedMeasure_readLab ht ht1 ht' ht1' ha ha1 hb hb1 hD hgD,
    PMF.toMeasure_apply_singleton _ (x, y) (measurableSet_singleton _), prodPMF_apply]

/-! ### The matching event -/

/-- **The cross-law matching event at scale `D`**: a single automorphism of the
infinite binary tree matches the quantised label field of the first sample with
the coupled class field of the second, so that the matched levels differ by at
most one. -/
def crossMatchEvent (a b : ℝ) (D : ℕ) : Set ((Word → Bool) × (Word → Bool) × (Word → ℝ)) :=
  {ω | InfMatch (compat pathGraph) (fun h ↦ cqX D h ω) (fun h ↦ cqY a b D h ω)}

/-- The matching event is the intersection of the level-`h` matching events, so
it is measurable. -/
lemma measurableSet_crossMatchEvent (a b : ℝ) (D : ℕ) :
    MeasurableSet (crossMatchEvent a b D) := by
  have hset : crossMatchEvent a b D
      = ⋂ h : ℕ, {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) |
          fullSim (compat pathGraph) h (cqX D h ω) (cqY a b D h ω)} := by
    ext ω
    simp only [crossMatchEvent, Set.mem_ofPred_eq, Set.mem_iInter]
    exact infMatch_iff_forall_level (compat pathGraph) _ _ (fun h ↦ restrictLab_cqX D h ω)
      (fun h ↦ restrictLab_cqY a b D h ω)
  rw [hset]
  refine MeasurableSet.iInter fun h ↦ ?_
  exact measurable_cqXY a b D h
    ((Set.to_countable {p : FullLab ℕ h × FullLab ℕ h |
      fullSim (compat pathGraph) h p.1 p.2}).measurableSet)

/-- **The cross-law matching bound**: under the largeness conditions
`eq:d0-conditions` and `γ(D-1) ≥ 1` the matching event at scale `D` has
probability at least `1 - 256 θ₁^{D(D-5/2)}`. The potential estimate of
`thm:eta-bound` supplies the hypothesis of the i.i.d. matching theorem, and the
coupling identifies the two level projections with two independent
`μ_h`-labellings. -/
theorem cross_matching_prob_ge (ht : 0 < t) (ht1 : t < 1) (ht' : 0 < t') (ht1' : t' < 1)
    {D : ℕ} (hD : 5 ≤ D) (hgD : 1 ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1))
    (h1 : (1 - t) ^ (D - 1) ≤ 1 / 10) (h2 : (1 - t) ^ (D ^ 2 - D) ≤ 1 / 2)
    (h3 : 36 * (1 - t) ^ (5 * D - 2) ≤ 1) (h4 : 16 * qBound (1 - t) D ≤ 1 / 10000) :
    1 - ENNReal.ofReal (256 * qBound (1 - t) D)
      ≤ crossMeasure ht ht1.le ht' ht1'.le (crossMatchEvent (1 - t) (1 - t') D) := by
  have ha : (0 : ℝ) < 1 - t := by linarith
  have ha1 : (1 : ℝ) - t < 1 := by linarith
  have hb : (0 : ℝ) < 1 - t' := by linarith
  have hb1 : (1 : ℝ) - t' < 1 := by linarith
  have hD2 : 2 ≤ D := by omega
  have heta : etaP (chainQPMF ht ht1.le hD2) ≤ ENNReal.ofReal (16 * qBound (1 - t) D) :=
    quantised_eta_le ha ha1 hD h1 h2 h3
  have hPhi : Phi (chainQPMF ht ht1.le hD2) (compat pathGraph) ≤ 1 / 10000 := by
    rw [← etaG_eq_Phi]
    refine le_trans heta ?_
    rw [show (1 : ℝ≥0∞) / 10000 = ENNReal.ofReal (1 / 10000) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]]
    exact ENNReal.ofReal_le_ofReal h4
  have hmain := infinite_tree_matching_prob_of_law (crossMeasure ht ht1.le ht' ht1'.le)
    (chainQPMF ht ht1.le hD2) (compat pathGraph) (compat_refl pathGraph) (compat_symm pathGraph)
    hPhi (fun h ω ↦ cqX D h ω) (fun h ω ↦ cqY (1 - t) (1 - t') D h ω)
    (fun h ω ↦ restrictLab_cqX D h ω) (fun h ω ↦ restrictLab_cqY (1 - t) (1 - t') D h ω)
    (fun h ↦ measurable_cqXY (1 - t) (1 - t') D h)
    (fun h ↦ crossMeasure_map ht ht1.le ht' ht1'.le ha ha1 hb hb1 hD2 hgD h)
  have hconst : (16 : ℝ≥0∞) * ENNReal.ofReal (16 * qBound (1 - t) D)
      = ENNReal.ofReal (256 * qBound (1 - t) D) := by
    rw [show (256 : ℝ) * qBound (1 - t) D = 16 * (16 * qBound (1 - t) D) from by ring,
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 16 by norm_num) (q := 16 * qBound (1 - t) D),
      ENNReal.ofReal_ofNat]
  refine le_trans (tsub_le_tsub_left ?_ 1) hmain
  rw [← etaG_eq_Phi, ← hconst]
  gcongr
  exact heta

/-- On the matching event a single portrait matches the quantised label field
of the first sample with the coupled class field of the second, to within one
level. -/
theorem portrait_of_crossMatchEvent {D : ℕ} {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ)}
    (hω : ω ∈ crossMatchEvent a b D) :
    ∃ σ : Word → Bool ≃ Bool, ∀ w : Word,
      compat pathGraph (levelMap D (labAux ω.1 w)) (markLab a b D ω.2 (autOf σ w)) :=
  exists_portrait_of_infMatch (compat pathGraph)
    (fun s ↦ levelMap D (labAux ω.1 s)) (fun s ↦ markLab a b D ω.2 s) hω

/-! ### The deterministic core -/

/-- The distortion factor `γ_* = max(1,γ)/min(1,γ/2)` of `thm:cross-law`: the
allowance that clause (iii) of `thm:chain-coupling` makes for the rounding of
the crossing points. -/
noncomputable def gammaStar (a b : ℝ) : ℝ := max 1 (cgamma a b) / min 1 (cgamma a b / 2)

/-- The distortion factor is at least one. -/
lemma one_le_gammaStar (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    1 ≤ gammaStar a b := by
  have hγ := cgamma_pos ha ha1 hb hb1
  have hc : 0 < min 1 (cgamma a b / 2) := lt_min one_pos (by linarith)
  rw [gammaStar, le_div_iff₀ hc, one_mul]
  exact le_trans (min_le_left _ _) (le_max_left _ _)

/-- The integer distortion `⌈γ_* D²⌉` of `thm:cross-law`, the constant fed to
the Transfer lemma. -/
noncomputable def crossConst (a b : ℝ) (D : ℕ) : ℕ := ⌈gammaStar a b * (D : ℝ) ^ 2⌉₊

/-- The integer distortion is at least one. -/
lemma one_le_crossConst (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) {D : ℕ}
    (hD : 2 ≤ D) : 1 ≤ crossConst a b D := by
  have hG := one_le_gammaStar ha ha1 hb hb1
  have hDR : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hpos : 0 < gammaStar a b * (D : ℝ) ^ 2 := by nlinarith
  exact Nat.ceil_pos.mpr hpos

/-- **The comparison at matched classes**: if the level of a chain length of
the first law and the coupled class of a chain length of the second differ by
at most one, then the two lengths agree up to the factor `⌈γ_* D²⌉`. The level
of the first pins the length between consecutive powers `D^k`, clause (i) of
`thm:chain-coupling` pins the second between consecutive crossing points, and
clause (iii) compares the crossing points with the powers. -/
lemma cross_comparableR (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) {D : ℕ}
    (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) {m m' : ℕ} (u : ℝ) (hm : 1 ≤ m)
    (hm' : 1 ≤ m') (hclose : levelMap D m ≤ ellQ a b D m' u + 1)
    (hclose' : ellQ a b D m' u ≤ levelMap D m + 1) :
    (m : ℝ) ≤ gammaStar a b * (D : ℝ) ^ 2 * m'
      ∧ (m' : ℝ) ≤ gammaStar a b * (D : ℝ) ^ 2 * m := by
  have hγ := cgamma_pos ha ha1 hb hb1
  set c₁ := min 1 (cgamma a b / 2) with hc₁def
  set c₂ := max 1 (cgamma a b) with hc₂def
  have hc₁pos : 0 < c₁ := lt_min one_pos (by linarith)
  have hc₁le : c₁ ≤ 1 := min_le_left _ _
  have hc₂ge : (1 : ℝ) ≤ c₂ := le_max_left _ _
  have hG : gammaStar a b = c₂ / c₁ := rfl
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by
    have : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  set k := levelMap D m with hk
  set k' := ellQ a b D m' u with hk'
  obtain ⟨hlow, hhigh⟩ := (level_eq_iff hD hm).mp hk.symm
  obtain ⟨hlow', hhigh'⟩ := ellQ_sandwich_upper ha ha1 hb hb1 hD hgD hm' hk'.symm
  have hDQ0 := DQ_ratio ha ha1 hb hb1 hD k'
  have hDQ1 := DQ_ratio ha ha1 hb hb1 hD (k' + 1)
  have hcast1 : (D : ℝ) ^ k ≤ (m : ℝ) := by exact_mod_cast hlow
  have hcast2 : (m : ℝ) ≤ (D : ℝ) ^ (k + 1) := by exact_mod_cast hhigh.le
  have hcast3 : ((DQ a b D k' : ℕ) : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hlow'
  have hcast4 : (m' : ℝ) ≤ ((DQ a b D (k' + 1) : ℕ) : ℝ) := by exact_mod_cast hhigh'
  have hstep1 : (m' : ℝ) ≤ gammaStar a b * ((D : ℝ) ^ 2 * (m : ℝ)) := by
    have hc : c₂ ≤ gammaStar a b := by
      rw [hG, le_div_iff₀ hc₁pos]
      nlinarith
    have e1 : (D : ℝ) ^ (k' + 1) ≤ (D : ℝ) ^ 2 * (D : ℝ) ^ k :=
      calc (D : ℝ) ^ (k' + 1) ≤ (D : ℝ) ^ (k + 2) := pow_le_pow_right₀ hD1 (by omega)
        _ = (D : ℝ) ^ 2 * (D : ℝ) ^ k := by ring
    have e2 : (D : ℝ) ^ 2 * (D : ℝ) ^ k ≤ (D : ℝ) ^ 2 * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hcast1 (by positivity)
    calc (m' : ℝ) ≤ ((DQ a b D (k' + 1) : ℕ) : ℝ) := hcast4
      _ ≤ c₂ * (D : ℝ) ^ (k' + 1) := hDQ1.2
      _ ≤ c₂ * ((D : ℝ) ^ 2 * (m : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_trans e1 e2) (by linarith)
      _ ≤ gammaStar a b * ((D : ℝ) ^ 2 * (m : ℝ)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
  have hstep2 : (m : ℝ) ≤ gammaStar a b * ((D : ℝ) ^ 2 * (m' : ℝ)) := by
    have hX0 : (0 : ℝ) ≤ (D : ℝ) ^ 2 * (m' : ℝ) := by positivity
    have key : c₁ * (m : ℝ) ≤ (D : ℝ) ^ 2 * (m' : ℝ) := by
      have e1 : (m : ℝ) ≤ (D : ℝ) ^ 2 * (D : ℝ) ^ k' :=
        calc (m : ℝ) ≤ (D : ℝ) ^ (k + 1) := hcast2
          _ ≤ (D : ℝ) ^ (k' + 2) := pow_le_pow_right₀ hD1 (by omega)
          _ = (D : ℝ) ^ 2 * (D : ℝ) ^ k' := by ring
      have e2 : c₁ * (D : ℝ) ^ k' ≤ (m' : ℝ) := le_trans hDQ0.1 hcast3
      have h1 := mul_le_mul_of_nonneg_left e1 hc₁pos.le
      have h2 := mul_le_mul_of_nonneg_left e2 (show (0 : ℝ) ≤ (D : ℝ) ^ 2 by positivity)
      linarith
    have h3 : (0 : ℝ) ≤ (c₂ - 1) * ((D : ℝ) ^ 2 * (m' : ℝ)) := mul_nonneg (by linarith) hX0
    rw [hG, div_mul_eq_mul_div, le_div_iff₀ hc₁pos]
    linarith
  refine ⟨?_, ?_⟩
  · calc (m : ℝ) ≤ gammaStar a b * ((D : ℝ) ^ 2 * (m' : ℝ)) := hstep2
      _ = gammaStar a b * (D : ℝ) ^ 2 * m' := by ring
  · calc (m' : ℝ) ≤ gammaStar a b * ((D : ℝ) ^ 2 * (m : ℝ)) := hstep1
      _ = gammaStar a b * (D : ℝ) ^ 2 * m := by ring

/-- The comparison at matched classes, rounded to the integer constant that the integer
Transfer lemma takes. -/
lemma cross_comparable (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) {D : ℕ}
    (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) {m m' : ℕ} (u : ℝ) (hm : 1 ≤ m)
    (hm' : 1 ≤ m') (hclose : levelMap D m ≤ ellQ a b D m' u + 1)
    (hclose' : ellQ a b D m' u ≤ levelMap D m + 1) :
    m ≤ crossConst a b D * m' ∧ m' ≤ crossConst a b D * m := by
  obtain ⟨hstep2, hstep1⟩ := cross_comparableR ha ha1 hb hb1 hD hgD u hm hm' hclose hclose'
  have hceil : ∀ p q : ℕ, (p : ℝ) ≤ gammaStar a b * (D : ℝ) ^ 2 * q →
      p ≤ crossConst a b D * q := by
    intro p q hpq
    have h := mul_le_mul_of_nonneg_right (Nat.le_ceil (gammaStar a b * (D : ℝ) ^ 2))
      (show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q)
    have hR : (p : ℝ) ≤ ((crossConst a b D * q : ℕ) : ℝ) := by
      push_cast [crossConst]
      nlinarith
    exact_mod_cast hR
  exact ⟨hceil m m' hstep2, hceil m' m hstep1⟩

/-- **The deterministic core of `thm:cross-law`**: if a portrait matches the
quantised labelling `ℓ_D ∘ λ` of the first sample with the coupled class field
`ℓ'(λ', U)` of the second to within one level, then the two associated trees
admit a `(⌈γ_* D²⌉+3)`-quasi-isometry. The matched classes force length ratios
within `⌈γ_* D²⌉`, the Transfer lemma turns that into a quasi-isometry onto the
tree of the relabelled labelling, and `thm:isometry` identifies that tree with
the tree of `λ'`. -/
theorem qi_of_cross_matching (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) {D : ℕ}
    (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) (σ : Word → Bool ≃ Bool)
    {lam lam' : Word → ℕ} {u : Word → ℝ} (hlam : ∀ w, 1 ≤ lam w) (hlam' : ∀ w, 1 ≤ lam' w)
    (hmatch : ∀ w, compat pathGraph (levelMap D (lam w))
      (ellQ a b D (lam' (autOf σ w)) (u (autOf σ w)))) :
    ∃ f : Word → Word, IsQIWith (crossConst a b D + 3) (InAssoc lam) (InAssoc lam') f := by
  have hcomp : ∀ v, lam v ≤ crossConst a b D * lam' (autOf σ v) ∧
      lam' (autOf σ v) ≤ crossConst a b D * lam v := by
    intro v
    have h := hmatch v
    rw [compat_pathGraph] at h
    exact cross_comparable ha ha1 hb hb1 hD hgD (u (autOf σ v)) (hlam v) (hlam' _)
      (by omega) (by omega)
  have hqi : IsQIWith (crossConst a b D + 3) (InAssoc lam) (InAssoc fun w ↦ lam' (autOf σ w))
      (psi lam fun w ↦ lam' (autOf σ w)) :=
    transfer hlam (fun w ↦ hlam' _) (one_le_crossConst ha ha1 hb hb1 hD) hcomp
  obtain ⟨g, hg1, hg2, hg3⟩ :
      ∃ g : Word → Word,
        (∀ x, InAssoc (fun w ↦ lam' (autOf σ w)) x → InAssoc lam' (g x)) ∧
        (∀ y, InAssoc lam' y → ∃ x, InAssoc (fun w ↦ lam' (autOf σ w)) x ∧ g x = y) ∧
        (∀ x y, InAssoc (fun w ↦ lam' (autOf σ w)) x → InAssoc (fun w ↦ lam' (autOf σ w)) y →
          treeDist (g x) (g y) = treeDist x y) :=
    isometry_of_relabel σ (fun w ↦ hlam' _) hlam' fun _ ↦ rfl
  exact ⟨fun x ↦ g (psi lam (fun w ↦ lam' (autOf σ w)) x), hqi.comp_isometry hg1 hg2 hg3⟩

/-- **The deterministic core of `thm:cross-law` at the real constant**: the matched
classes force length ratios within `γ_* D²`, and the Transfer lemma at a real constant
turns that into a `(γ_* D² + 3)`-quasi-isometry, the constant of `eq:rate-cross` with no
rounding. -/
theorem qi_of_cross_matchingR (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) {D : ℕ}
    (hD : 2 ≤ D) (hgD : 1 ≤ cgamma a b * ((D : ℝ) - 1)) (σ : Word → Bool ≃ Bool)
    {lam lam' : Word → ℕ} {u : Word → ℝ} (hlam : ∀ w, 1 ≤ lam w) (hlam' : ∀ w, 1 ≤ lam' w)
    (hmatch : ∀ w, compat pathGraph (levelMap D (lam w))
      (ellQ a b D (lam' (autOf σ w)) (u (autOf σ w)))) :
    ∃ f : Word → Word,
      IsQIWithR (gammaStar a b * (D : ℝ) ^ 2 + 3) (InAssoc lam) (InAssoc lam') f := by
  have hC1 : (1 : ℝ) ≤ gammaStar a b * (D : ℝ) ^ 2 := by
    have hG := one_le_gammaStar ha ha1 hb hb1
    have hDR : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    nlinarith
  have hcompR : ∀ v, (lam v : ℝ) ≤ gammaStar a b * (D : ℝ) ^ 2 * lam' (autOf σ v) ∧
      (lam' (autOf σ v) : ℝ) ≤ gammaStar a b * (D : ℝ) ^ 2 * lam v := by
    intro v
    have h := hmatch v
    rw [compat_pathGraph] at h
    exact cross_comparableR ha ha1 hb hb1 hD hgD (u (autOf σ v)) (hlam v) (hlam' _)
      (by omega) (by omega)
  have hqi : IsQIWithR (gammaStar a b * (D : ℝ) ^ 2 + 3) (InAssoc lam)
      (InAssoc fun w ↦ lam' (autOf σ w)) (psi lam fun w ↦ lam' (autOf σ w)) :=
    transferR hlam (fun w ↦ hlam' _) hC1 hcompR
  obtain ⟨g, hg1, hg2, hg3⟩ :
      ∃ g : Word → Word,
        (∀ x, InAssoc (fun w ↦ lam' (autOf σ w)) x → InAssoc lam' (g x)) ∧
        (∀ y, InAssoc lam' y → ∃ x, InAssoc (fun w ↦ lam' (autOf σ w)) x ∧ g x = y) ∧
        (∀ x y, InAssoc (fun w ↦ lam' (autOf σ w)) x → InAssoc (fun w ↦ lam' (autOf σ w)) y →
          treeDist (g x) (g y) = treeDist x y) :=
    isometry_of_relabel σ (fun w ↦ hlam' _) hlam' fun _ ↦ rfl
  exact ⟨fun x ↦ g (psi lam (fun w ↦ lam' (autOf σ w)) x), hqi.comp_isometry hg1 hg2 hg3⟩

/-! ### The good event -/

/-- A sample with a non-terminating chain in either of the two offspring fields
is a null event. -/
lemma crossMeasure_not_chains (ht : 0 < t) (ht1 : t ≤ 1) (ht' : 0 < t') (ht1' : t' ≤ 1) :
    crossMeasure ht ht1 ht' ht1'
      {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ (Chains ω.1 ∧ Chains ω.2.1)} = 0 := by
  have hbadsub : {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) |
        ¬ (Chains ω.1 ∧ Chains ω.2.1)}
      ⊆ ({χ : Word → Bool | ¬ Chains χ} ×ˢ (Set.univ : Set ((Word → Bool) × (Word → ℝ))))
        ∪ ((Set.univ : Set (Word → Bool)) ×ˢ
            ({χ : Word → Bool | ¬ Chains χ} ×ˢ (Set.univ : Set (Word → ℝ)))) := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, Set.mem_ofPred_eq, and_true, true_and]
    by_cases hc : Chains ω.1
    · exact Or.inr fun hc2 ↦ hω ⟨hc, hc2⟩
    · exact Or.inl hc
  refine measure_mono_null hbadsub (measure_union_null ?_ ?_)
  · rw [crossMeasure, Measure.prod_prod, chainMeasure_not_chains ht ht1, zero_mul]
  · rw [crossMeasure, Measure.prod_prod, markedMeasure, Measure.prod_prod,
      chainMeasure_not_chains ht' ht1', zero_mul, mul_zero]

/-! ### `thm:cross-law` -/

/-- **`eq:rate-cross`, the cross-law rate.** Under the largeness conditions
`eq:d0-conditions` and `γ(D-1) ≥ 1`, outside an event of probability at most
`256 θ₁^{D(D-5/2)}` the trees of two independent samples of the two two-value
offspring laws admit a `(⌈γ_* D²⌉+3)`-quasi-isometry. -/
theorem crosslaw_rate (ht : 0 < t) (ht1 : t < 1) (ht' : 0 < t') (ht1' : t' < 1) {D : ℕ}
    (hD : 5 ≤ D) (hgD : 1 ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1))
    (h1 : (1 - t) ^ (D - 1) ≤ 1 / 10) (h2 : (1 - t) ^ (D ^ 2 - D) ≤ 1 / 2)
    (h3 : 36 * (1 - t) ^ (5 * D - 2) ≤ 1) (h4 : 16 * qBound (1 - t) D ≤ 1 / 10000) :
    crossMeasure ht ht1.le ht' ht1'.le
        {ω | ¬ ∃ f : Word → Word, IsQIWith (crossConst (1 - t) (1 - t') D + 3)
          (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
      ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
  have ha : (0 : ℝ) < 1 - t := by linarith
  have ha1 : (1 : ℝ) - t < 1 := by linarith
  have hb : (0 : ℝ) < 1 - t' := by linarith
  have hb1 : (1 : ℝ) - t' < 1 := by linarith
  have hD2 : 2 ≤ D := by omega
  have hqb : (0 : ℝ) ≤ qBound (1 - t) D := qBound_nonneg _ _
  have hc1 : ENNReal.ofReal (256 * qBound (1 - t) D) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (by nlinarith)
  have hmc : crossMeasure ht ht1.le ht' ht1'.le (crossMatchEvent (1 - t) (1 - t') D)ᶜ
      ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
    rw [prob_compl_eq_one_sub (measurableSet_crossMatchEvent (1 - t) (1 - t') D)]
    calc (1 : ℝ≥0∞) - crossMeasure ht ht1.le ht' ht1'.le (crossMatchEvent (1 - t) (1 - t') D)
        ≤ 1 - (1 - ENNReal.ofReal (256 * qBound (1 - t) D)) :=
          tsub_le_tsub_left (cross_matching_prob_ge ht ht1 ht' ht1' hD hgD h1 h2 h3 h4) 1
      _ = ENNReal.ofReal (256 * qBound (1 - t) D) :=
          ENNReal.sub_sub_cancel ENNReal.one_ne_top hc1
  have hsub : {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ ∃ f : Word → Word,
        IsQIWith (crossConst (1 - t) (1 - t') D + 3)
          (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
      ⊆ (crossMatchEvent (1 - t) (1 - t') D)ᶜ
        ∪ {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ (Chains ω.1 ∧ Chains ω.2.1)} := by
    intro ω hω
    by_cases hM : ω ∈ crossMatchEvent (1 - t) (1 - t') D
    · refine Or.inr fun hch ↦ hω ?_
      obtain ⟨σ, hσ⟩ := portrait_of_crossMatchEvent hM
      exact qi_of_cross_matching ha ha1 hb hb1 hD2 hgD σ (one_le_labAux hch.1)
        (one_le_labAux hch.2) hσ
    · exact Or.inl hM
  calc crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ ∃ f : Word → Word,
          IsQIWith (crossConst (1 - t) (1 - t') D + 3)
            (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
      ≤ crossMeasure ht ht1.le ht' ht1'.le ((crossMatchEvent (1 - t) (1 - t') D)ᶜ
          ∪ {ω | ¬ (Chains ω.1 ∧ Chains ω.2.1)}) := measure_mono hsub
    _ ≤ crossMeasure ht ht1.le ht' ht1'.le (crossMatchEvent (1 - t) (1 - t') D)ᶜ
        + crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ (Chains ω.1 ∧ Chains ω.2.1)} :=
          measure_union_le _ _
    _ ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
        rw [crossMeasure_not_chains ht ht1.le ht' ht1'.le, add_zero]
        exact hmc

/-- **`eq:d0-conditions` together with `γ(D-1) ≥ 1`.**  `exists_scale` is asked
for a scale past `1/γ + 1`, which is what the extra condition needs. -/
theorem exists_scale_cross (ht : 0 < t) (ht1 : t < 1) (ht' : 0 < t') (ht1' : t' < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ, 5 ≤ D ∧ 1 ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1) ∧
      (1 - t) ^ (D - 1) ≤ 1 / 10 ∧ (1 - t) ^ (D ^ 2 - D) ≤ 1 / 2 ∧
      36 * (1 - t) ^ (5 * D - 2) ≤ 1 ∧ 16 * qBound (1 - t) D ≤ 1 / 10000 ∧
      256 * qBound (1 - t) D < ε := by
  have ha0 : (0 : ℝ) < 1 - t := by linarith
  have ha1 : (1 : ℝ) - t < 1 := by linarith
  have hg : 0 < cgamma (1 - t) (1 - t') :=
    cgamma_pos ha0 ha1 (by linarith) (by linarith)
  obtain ⟨D, hD5, hDM, h1, h2, h3, h4, hlt⟩ :=
    exists_scale ha0 ha1 hε (⌈(1 : ℝ) / cgamma (1 - t) (1 - t')⌉₊ + 1)
  refine ⟨D, hD5, ?_, h1, h2, h3, h4, hlt⟩
  have hceil : (1 : ℝ) / cgamma (1 - t) (1 - t')
      ≤ (⌈(1 : ℝ) / cgamma (1 - t) (1 - t')⌉₊ : ℝ) := Nat.le_ceil _
  have hcast : ((⌈(1 : ℝ) / cgamma (1 - t) (1 - t')⌉₊ : ℕ) : ℝ) + 1 ≤ (D : ℝ) := by
    exact_mod_cast hDM
  have hle : (1 : ℝ) / cgamma (1 - t) (1 - t') ≤ (D : ℝ) - 1 := by linarith
  have hmul : cgamma (1 - t) (1 - t') * ((1 : ℝ) / cgamma (1 - t) (1 - t'))
      ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1) := mul_le_mul_of_nonneg_left hle hg.le
  rwa [mul_one_div, div_self hg.ne'] at hmul

/-- **`thm:cross-law`, the almost sure statement**: almost surely the trees
associated with two independent samples of the two two-value offspring laws are
quasi-isometric, for some constant.  The largeness conditions are met at some
scale by `exists_scale_cross`. -/
theorem crosslaw_ae (ht : 0 < t) (ht1 : t < 1) (ht' : 0 < t') (ht1' : t' < 1) :
    crossMeasure ht ht1.le ht' ht1'.le
        {ω | ¬ ∃ (K : ℕ) (f : Word → Word),
          IsQIWith K (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f} = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) zero_le
  obtain ⟨D, hD, hgD, h1, h2, h3, h4, hlt⟩ :=
    exists_scale_cross ht ht1 ht' ht1' (NNReal.coe_pos.mpr hε)
  have hsub : {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ ∃ (K : ℕ) (f : Word → Word),
        IsQIWith K (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
      ⊆ {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ ∃ f : Word → Word,
        IsQIWith (crossConst (1 - t) (1 - t') D + 3)
          (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f} := by
    rintro ω hω ⟨f, hf⟩
    exact hω ⟨crossConst (1 - t) (1 - t') D + 3, f, hf⟩
  calc crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ ∃ (K : ℕ) (f : Word → Word),
          IsQIWith K (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
      ≤ crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ ∃ f : Word → Word,
          IsQIWith (crossConst (1 - t) (1 - t') D + 3)
            (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f} := measure_mono hsub
    _ ≤ ENNReal.ofReal (256 * qBound (1 - t) D) :=
        crosslaw_rate ht ht1 ht' ht1' hD hgD h1 h2 h3 h4
    _ ≤ (ε : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hlt.le
    _ = 0 + (ε : ℝ≥0∞) := (zero_add _).symm

/-- **`thm:cross-law`, `eq:rate-cross` on the sample trees.** The failure
event differs from the one of `crosslaw_rate` only inside the null event that
some chain fails to terminate, where `thm:chains` identifies the sample tree
with the associated tree. -/
theorem crosslaw_rate_tree (ht : 0 < t) (ht1 : t < 1) (ht' : 0 < t') (ht1' : t' < 1) {D : ℕ}
    (hD : 5 ≤ D) (hgD : 1 ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1))
    (h1 : (1 - t) ^ (D - 1) ≤ 1 / 10) (h2 : (1 - t) ^ (D ^ 2 - D) ≤ 1 / 2)
    (h3 : 36 * (1 - t) ^ (5 * D - 2) ≤ 1) (h4 : 16 * qBound (1 - t) D ≤ 1 / 10000) :
    crossMeasure ht ht1.le ht' ht1'.le
        {ω | ¬ ∃ f : Word → Word, IsQIWith (crossConst (1 - t) (1 - t') D + 3)
          (InTree ω.1) (InTree ω.2.1) f}
      ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
  have hsub : {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ ∃ f : Word → Word,
        IsQIWith (crossConst (1 - t) (1 - t') D + 3) (InTree ω.1) (InTree ω.2.1) f}
      ⊆ {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ ∃ f : Word → Word,
          IsQIWith (crossConst (1 - t) (1 - t') D + 3)
            (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
        ∪ {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ (Chains ω.1 ∧ Chains ω.2.1)} := by
    intro ω hω
    by_cases hch : Chains ω.1 ∧ Chains ω.2.1
    · refine Or.inl fun hcon ↦ hω ?_
      rwa [inTree_eq_inAssoc hch.1, inTree_eq_inAssoc hch.2]
    · exact Or.inr hch
  calc crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ ∃ f : Word → Word,
          IsQIWith (crossConst (1 - t) (1 - t') D + 3) (InTree ω.1) (InTree ω.2.1) f}
      ≤ crossMeasure ht ht1.le ht' ht1'.le ({ω | ¬ ∃ f : Word → Word,
            IsQIWith (crossConst (1 - t) (1 - t') D + 3)
              (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
          ∪ {ω | ¬ (Chains ω.1 ∧ Chains ω.2.1)}) := measure_mono hsub
    _ ≤ crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ ∃ f : Word → Word,
            IsQIWith (crossConst (1 - t) (1 - t') D + 3)
              (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
        + crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ (Chains ω.1 ∧ Chains ω.2.1)} :=
          measure_union_le _ _
    _ ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
        rw [crossMeasure_not_chains ht ht1.le ht' ht1'.le, add_zero]
        exact crosslaw_rate ht ht1 ht' ht1' hD hgD h1 h2 h3 h4

/-- **`thm:cross-law` on the sample trees**: almost surely the two sampled
Galton-Watson trees are quasi-isometric, for some constant. -/
theorem crosslaw_ae_tree (ht : 0 < t) (ht1 : t < 1) (ht' : 0 < t') (ht1' : t' < 1) :
    crossMeasure ht ht1.le ht' ht1'.le
        {ω | ¬ ∃ (K : ℕ) (f : Word → Word), IsQIWith K (InTree ω.1) (InTree ω.2.1) f} = 0 := by
  have hsub : {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ ∃ (K : ℕ) (f : Word → Word),
        IsQIWith K (InTree ω.1) (InTree ω.2.1) f}
      ⊆ {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ ∃ (K : ℕ) (f : Word → Word),
          IsQIWith K (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
        ∪ {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ (Chains ω.1 ∧ Chains ω.2.1)} := by
    intro ω hω
    by_cases hch : Chains ω.1 ∧ Chains ω.2.1
    · refine Or.inl fun hcon ↦ hω ?_
      rwa [inTree_eq_inAssoc hch.1, inTree_eq_inAssoc hch.2]
    · exact Or.inr hch
  refine le_antisymm ?_ zero_le
  calc crossMeasure ht ht1.le ht' ht1'.le
        {ω | ¬ ∃ (K : ℕ) (f : Word → Word), IsQIWith K (InTree ω.1) (InTree ω.2.1) f}
      ≤ crossMeasure ht ht1.le ht' ht1'.le ({ω | ¬ ∃ (K : ℕ) (f : Word → Word),
            IsQIWith K (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
          ∪ {ω | ¬ (Chains ω.1 ∧ Chains ω.2.1)}) := measure_mono hsub
    _ ≤ crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ ∃ (K : ℕ) (f : Word → Word),
            IsQIWith K (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
        + crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ (Chains ω.1 ∧ Chains ω.2.1)} :=
          measure_union_le _ _
    _ = 0 := by
        rw [crosslaw_ae ht ht1 ht' ht1',
          crossMeasure_not_chains ht ht1.le ht' ht1'.le, add_zero]

/-! ### `eq:rate-cross` at the real constant -/

/-- **`eq:rate-cross` at the real constant**: outside an event of probability at most
`256 θ₁^{D(D-5/2)}` the two associated trees admit a `(γ_* D² + 3)`-quasi-isometry, the
constant of the paper with no rounding. -/
theorem crosslaw_rateR (ht : 0 < t) (ht1 : t < 1) (ht' : 0 < t') (ht1' : t' < 1) {D : ℕ}
    (hD : 5 ≤ D) (hgD : 1 ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1))
    (h1 : (1 - t) ^ (D - 1) ≤ 1 / 10) (h2 : (1 - t) ^ (D ^ 2 - D) ≤ 1 / 2)
    (h3 : 36 * (1 - t) ^ (5 * D - 2) ≤ 1) (h4 : 16 * qBound (1 - t) D ≤ 1 / 10000) :
    crossMeasure ht ht1.le ht' ht1'.le
        {ω | ¬ ∃ f : Word → Word,
          IsQIWithR (gammaStar (1 - t) (1 - t') * (D : ℝ) ^ 2 + 3)
            (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
      ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
  have ha : (0 : ℝ) < 1 - t := by linarith
  have ha1 : (1 : ℝ) - t < 1 := by linarith
  have hb : (0 : ℝ) < 1 - t' := by linarith
  have hb1 : (1 : ℝ) - t' < 1 := by linarith
  have hD2 : 2 ≤ D := by omega
  have hqb : (0 : ℝ) ≤ qBound (1 - t) D := qBound_nonneg _ _
  have hc1 : ENNReal.ofReal (256 * qBound (1 - t) D) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (by nlinarith)
  have hmc : crossMeasure ht ht1.le ht' ht1'.le (crossMatchEvent (1 - t) (1 - t') D)ᶜ
      ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
    rw [prob_compl_eq_one_sub (measurableSet_crossMatchEvent (1 - t) (1 - t') D)]
    calc (1 : ℝ≥0∞) - crossMeasure ht ht1.le ht' ht1'.le (crossMatchEvent (1 - t) (1 - t') D)
        ≤ 1 - (1 - ENNReal.ofReal (256 * qBound (1 - t) D)) :=
          tsub_le_tsub_left (cross_matching_prob_ge ht ht1 ht' ht1' hD hgD h1 h2 h3 h4) 1
      _ = ENNReal.ofReal (256 * qBound (1 - t) D) :=
          ENNReal.sub_sub_cancel ENNReal.one_ne_top hc1
  have hsub : {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ ∃ f : Word → Word,
        IsQIWithR (gammaStar (1 - t) (1 - t') * (D : ℝ) ^ 2 + 3)
          (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
      ⊆ (crossMatchEvent (1 - t) (1 - t') D)ᶜ
        ∪ {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ (Chains ω.1 ∧ Chains ω.2.1)} := by
    intro ω hω
    by_cases hM : ω ∈ crossMatchEvent (1 - t) (1 - t') D
    · refine Or.inr fun hch ↦ hω ?_
      obtain ⟨σ, hσ⟩ := portrait_of_crossMatchEvent hM
      exact qi_of_cross_matchingR ha ha1 hb hb1 hD2 hgD σ (one_le_labAux hch.1)
        (one_le_labAux hch.2) hσ
    · exact Or.inl hM
  calc crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ ∃ f : Word → Word,
          IsQIWithR (gammaStar (1 - t) (1 - t') * (D : ℝ) ^ 2 + 3)
            (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
      ≤ crossMeasure ht ht1.le ht' ht1'.le ((crossMatchEvent (1 - t) (1 - t') D)ᶜ
          ∪ {ω | ¬ (Chains ω.1 ∧ Chains ω.2.1)}) := measure_mono hsub
    _ ≤ crossMeasure ht ht1.le ht' ht1'.le (crossMatchEvent (1 - t) (1 - t') D)ᶜ
        + crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ (Chains ω.1 ∧ Chains ω.2.1)} :=
          measure_union_le _ _
    _ ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
        rw [crossMeasure_not_chains ht ht1.le ht' ht1'.le, add_zero]
        exact hmc

/-- **`eq:rate-cross` at the real constant, on the sample trees.** -/
theorem crosslaw_rate_treeR (ht : 0 < t) (ht1 : t < 1) (ht' : 0 < t') (ht1' : t' < 1) {D : ℕ}
    (hD : 5 ≤ D) (hgD : 1 ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1))
    (h1 : (1 - t) ^ (D - 1) ≤ 1 / 10) (h2 : (1 - t) ^ (D ^ 2 - D) ≤ 1 / 2)
    (h3 : 36 * (1 - t) ^ (5 * D - 2) ≤ 1) (h4 : 16 * qBound (1 - t) D ≤ 1 / 10000) :
    crossMeasure ht ht1.le ht' ht1'.le
        {ω | ¬ ∃ f : Word → Word, IsQIWithR (gammaStar (1 - t) (1 - t') * (D : ℝ) ^ 2 + 3)
          (InTree ω.1) (InTree ω.2.1) f}
      ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
  have hsub : {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ ∃ f : Word → Word,
        IsQIWithR (gammaStar (1 - t) (1 - t') * (D : ℝ) ^ 2 + 3) (InTree ω.1) (InTree ω.2.1) f}
      ⊆ {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ ∃ f : Word → Word,
          IsQIWithR (gammaStar (1 - t) (1 - t') * (D : ℝ) ^ 2 + 3)
            (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
        ∪ {ω : (Word → Bool) × (Word → Bool) × (Word → ℝ) | ¬ (Chains ω.1 ∧ Chains ω.2.1)} := by
    intro ω hω
    by_cases hch : Chains ω.1 ∧ Chains ω.2.1
    · refine Or.inl fun hcon ↦ hω ?_
      rwa [inTree_eq_inAssoc hch.1, inTree_eq_inAssoc hch.2]
    · exact Or.inr hch
  calc crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ ∃ f : Word → Word,
          IsQIWithR (gammaStar (1 - t) (1 - t') * (D : ℝ) ^ 2 + 3) (InTree ω.1) (InTree ω.2.1) f}
      ≤ crossMeasure ht ht1.le ht' ht1'.le ({ω | ¬ ∃ f : Word → Word,
            IsQIWithR (gammaStar (1 - t) (1 - t') * (D : ℝ) ^ 2 + 3)
              (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
          ∪ {ω | ¬ (Chains ω.1 ∧ Chains ω.2.1)}) := measure_mono hsub
    _ ≤ crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ ∃ f : Word → Word,
            IsQIWithR (gammaStar (1 - t) (1 - t') * (D : ℝ) ^ 2 + 3)
              (InAssoc (labCFst ω)) (InAssoc (labCSnd ω)) f}
        + crossMeasure ht ht1.le ht' ht1'.le {ω | ¬ (Chains ω.1 ∧ Chains ω.2.1)} :=
          measure_union_le _ _
    _ ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
        rw [crossMeasure_not_chains ht ht1.le ht' ht1'.le, add_zero]
        exact crosslaw_rateR ht ht1 ht' ht1' hD hgD h1 h2 h3 h4

/-- **`eq:rate-cross` past one threshold**: there is `D₁ = D₁(θ₁, θ₁')` such that for
every `D ≥ D₁` the two sampled Galton-Watson trees admit a `(γ_* D² + 3)`-quasi-isometry
outside an event of probability at most `256·θ₁^{D(D-5/2)}`. -/
theorem exists_crosslaw_rate_tree (ht : 0 < t) (ht1 : t < 1) (ht' : 0 < t') (ht1' : t' < 1) :
    ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D →
      crossMeasure ht ht1.le ht' ht1'.le
          {ω | ¬ ∃ f : Word → Word, IsQIWithR (gammaStar (1 - t) (1 - t') * (D : ℝ) ^ 2 + 3)
            (InTree ω.1) (InTree ω.2.1) f}
        ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
  have ha0 : (0 : ℝ) < 1 - t := by linarith
  have ha1 : (1 : ℝ) - t < 1 := by linarith
  have hg : 0 < cgamma (1 - t) (1 - t') :=
    cgamma_pos ha0 ha1 (by linarith) (by linarith)
  obtain ⟨D₀, hD₀⟩ := forall_scale ha0 ha1
  refine ⟨max D₀ (⌈(1 : ℝ) / cgamma (1 - t) (1 - t')⌉₊ + 1), fun D hD ↦ ?_⟩
  obtain ⟨hD5, h1, h2, h3, h4⟩ := hD₀ D (le_trans (le_max_left _ _) hD)
  have hgD : 1 ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1) := by
    have hceil : (1 : ℝ) / cgamma (1 - t) (1 - t')
        ≤ (⌈(1 : ℝ) / cgamma (1 - t) (1 - t')⌉₊ : ℝ) := Nat.le_ceil _
    have hcast : ((⌈(1 : ℝ) / cgamma (1 - t) (1 - t')⌉₊ : ℕ) : ℝ) + 1 ≤ (D : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hD
    have hle : (1 : ℝ) / cgamma (1 - t) (1 - t') ≤ (D : ℝ) - 1 := by linarith
    have hmul : cgamma (1 - t) (1 - t') * ((1 : ℝ) / cgamma (1 - t) (1 - t'))
        ≤ cgamma (1 - t) (1 - t') * ((D : ℝ) - 1) := mul_le_mul_of_nonneg_left hle hg.le
    rwa [mul_one_div, div_self hg.ne'] at hmul
  exact crosslaw_rate_treeR ht ht1 ht' ht1' hD5 hgD h1 h2 h3 h4

end ChainClasses
