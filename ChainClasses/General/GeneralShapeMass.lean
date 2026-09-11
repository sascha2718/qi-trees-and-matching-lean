import ChainClasses.General.GeneralBushPoint
import ChainClasses.General.GeneralShapeIID
import ChainClasses.General.GeneralNeck

/-!
`thm:mass-uniform` and `thm:conditional-explicit` of `matching_classes_general.tex`:
the conditional shape laws and their mixture as probability laws on `𝒮`, with the
point-mass half of the uniform bounds.

The joint masses of `GeneralShapeIID` normalise by the partition of the arity event
over the shapes: summing `gPairMass θ κ` over `𝒮` gives the reduced weight `ν̃_κ`, so
`μ_κ = gCondMass θ κ` is a probability law, and summing the arities out gives the
mixture `μ = ∑_κ ν̃_κ μ_κ` of `thm:conditional-explicit`, the marginal law of the shape
at the root.  The point clause of `thm:mass-uniform` is one factor per vertex: a neck
or split factor is at least `pminOff θ` against the window `q^J(1-q)^J`, and a bush
factor carries `pminOff θ` per vertex by `GeneralBushPoint`, so a charged shape has
mass at least `gPointBase θ` to its size, under every `μ_κ` charging it and under the
mixture.

* `survivalMeasure_gShapeArity`, `survivalMeasure_gArity_eq`: the root laws with the
  subtrees unconstrained.
* `tsum_gPairMass`, `gCondPMF`: **`def:conditional-laws` as probability laws**.
* `gMixMass`, `gMixMass_eq_measure`, `tsum_gMixMass`, `gMixPMF`: **the mixture clause
  of `thm:conditional-explicit`**, the marginal shape law `μ = ∑_κ ν̃_κ μ_κ`.
* `reducedWeight_le_one`, `gPairMass_le_gMixMass`, `gPairMass_le_gCondMass`: the
  mixture dominates each weighted conditional law.
* `GShape.ChargedG`, `gPointBase`: charged shapes, and the base of the point bound.
* `ofReal_pow_le_gPairMass`, `ofReal_pow_le_gCondMass`, `ofReal_pow_le_gMixMass`:
  **`thm:mass-uniform`, the point clause**, `μ_κ(σ) ≥ e^{-C|σ|}` with
  `C = log gPointBase⁻¹`, uniformly over the arities.
-/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal
open BranchingProcess (sample Survives skeletonDegree Offspring sampleMeasure
  survivalMeasure bushMeasure)

variable {J N : ℕ}

/-! ### The root laws with the subtrees unconstrained -/

lemma gSplitBush_box_univ (κ : ℕ) :
    {c : GWord N → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ (Set.univ : Set (GWord N → ℕ))}
      = Set.univ := by
  ext c
  simp

/-- The joint mass of a shape and an arity is the mass of the corresponding root
event. -/
lemma survivalMeasure_gShapeArity (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (σ : GShape) {κ : ℕ} (hκ : 2 ≤ κ) :
    survivalMeasure (N := N) θ
        ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | gArity c = κ})
      = gPairMass (N := N) θ κ σ := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  have h := survivalMeasure_gShapePair θ hJN hq hq0 σ hκ
    (A := fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ)
  rw [gSplitBush_box_univ, Set.inter_univ] at h
  simpa using h

/-- The mass of an arity is the reduced weight. -/
lemma survivalMeasure_gArity_eq (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1) {κ : ℕ} (hκ : 2 ≤ κ) :
    survivalMeasure (N := N) θ {c : GWord N → ℕ | gArity c = κ}
      = ENNReal.ofReal (reducedWeight θ κ) := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  have h := survivalMeasure_gArityPair θ hJN hq hs1 hκ
    (A := fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ)
  rw [gSplitBush_box_univ, Set.inter_univ] at h
  simpa using h

/-! ### The conditional laws are probability laws -/

/-- **`def:conditional-laws`, the normalisation**: the joint masses at one arity sum to
the reduced weight. -/
theorem tsum_gPairMass (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {κ : ℕ} (hκ : 2 ≤ κ) :
    ∑' σ : GShape, gPairMass (N := N) θ κ σ = ENNReal.ofReal (reducedWeight θ κ) := by
  have hdisj : Pairwise (Function.onFun Disjoint fun σ : GShape ↦
      ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | gArity c = κ})) := by
    intro σ σ' hne
    refine Set.disjoint_left.mpr fun c hc hc' ↦ hne ?_
    rw [← hc.1, ← hc'.1]
  have hmeas : ∀ σ : GShape, MeasurableSet
      ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | gArity c = κ}) :=
    fun σ ↦ (fibreMeasurableG_gShapeRoot σ).inter (fibreMeasurableG_gArity κ)
  have hcover : (⋃ σ : GShape,
        ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | gArity c = κ}))
      = {c : GWord N → ℕ | gArity c = κ} := by
    ext c
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun ⟨σ, _, h⟩ ↦ h, fun h ↦ ⟨gShapeRoot c, rfl, h⟩⟩
  calc ∑' σ : GShape, gPairMass (N := N) θ κ σ
      = ∑' σ : GShape, survivalMeasure (N := N) θ
          ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | gArity c = κ}) :=
        (tsum_congr fun σ ↦ survivalMeasure_gShapeArity θ hJN hq hq0 σ hκ).symm
    _ = survivalMeasure (N := N) θ (⋃ σ : GShape,
          ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | gArity c = κ})) :=
        (measure_iUnion hdisj hmeas).symm
    _ = survivalMeasure (N := N) θ {c : GWord N → ℕ | gArity c = κ} := by rw [hcover]
    _ = ENNReal.ofReal (reducedWeight θ κ) := survivalMeasure_gArity_eq θ hJN hq hs1 hκ

/-- **`def:conditional-laws` as probability laws**: the conditional shape law `μ_κ`. -/
noncomputable def gCondPMF (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {κ : ℕ} (hκ : 2 ≤ κ)
    (hν : 0 < reducedWeight θ κ) : PMF GShape :=
  ⟨fun σ ↦ gCondMass (N := N) θ κ σ, by
    have htotal : ∑' σ : GShape, gCondMass (N := N) θ κ σ = 1 := by
      have hc : ∀ σ : GShape, gCondMass (N := N) θ κ σ
          = gPairMass (N := N) θ κ σ * (ENNReal.ofReal (reducedWeight θ κ))⁻¹ :=
        fun σ ↦ by rw [gCondMass_def, div_eq_mul_inv]
      rw [tsum_congr hc, ENNReal.tsum_mul_right, tsum_gPairMass θ hJN hq hq0 hs1 hκ,
        ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hν).ne' ENNReal.ofReal_ne_top]
    exact htotal ▸ ENNReal.summable.hasSum⟩

@[simp] lemma gCondPMF_apply (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {κ : ℕ} (hκ : 2 ≤ κ)
    (hν : 0 < reducedWeight θ κ) (σ : GShape) :
    gCondPMF θ hJN hq hq0 hs1 hκ hν σ = gCondMass (N := N) θ κ σ := rfl

/-! ### The mixture -/

/-- **The mixture `μ = ∑_κ ν̃_κ μ_κ` of `thm:conditional-explicit`**, in mass form: the
joint masses with the arity summed out. -/
noncomputable def gMixMass (θ : Offspring J) (σ : GShape) : ℝ≥0∞ :=
  ∑' j : ℕ, gPairMass (N := N) θ (j + 2) σ

/-- The mixture dominates each joint mass. -/
lemma gPairMass_le_gMixMass (θ : Offspring J) {κ : ℕ} (hκ : 2 ≤ κ) (σ : GShape) :
    gPairMass (N := N) θ κ σ ≤ gMixMass (N := N) θ σ := by
  have h : κ = (κ - 2) + 2 := by omega
  calc gPairMass (N := N) θ κ σ
      = gPairMass (N := N) θ ((κ - 2) + 2) σ := by rw [← h]
    _ ≤ gMixMass (N := N) θ σ := ENNReal.le_tsum (κ - 2)

/-- **The mixture is the marginal shape law**: the mass of a shape against a genuine
split. -/
theorem gMixMass_eq_measure (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (σ : GShape) :
    gMixMass (N := N) θ σ
      = survivalMeasure (N := N) θ
          ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | 2 ≤ gArity c}) := by
  have hdisj : Pairwise (Function.onFun Disjoint fun j : ℕ ↦
      ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | gArity c = j + 2})) := by
    intro j j' hne
    refine Set.disjoint_left.mpr fun c hc hc' ↦ hne ?_
    have h1 := hc.2
    have h2 := hc'.2
    simp only [Set.mem_setOf_eq] at h1 h2
    omega
  have hmeas : ∀ j : ℕ, MeasurableSet
      ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | gArity c = j + 2}) :=
    fun j ↦ (fibreMeasurableG_gShapeRoot σ).inter (fibreMeasurableG_gArity (j + 2))
  have hcover : (⋃ j : ℕ,
        ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | gArity c = j + 2}))
      = {c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | 2 ≤ gArity c} := by
    ext c
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, hs, ha⟩
      exact ⟨hs, by omega⟩
    · rintro ⟨hs, ha⟩
      exact ⟨gArity c - 2, hs, by omega⟩
  calc gMixMass (N := N) θ σ
      = ∑' j : ℕ, survivalMeasure (N := N) θ
          ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | gArity c = j + 2}) :=
        tsum_congr fun j ↦
          (survivalMeasure_gShapeArity θ hJN hq hq0 σ (by omega)).symm
    _ = survivalMeasure (N := N) θ (⋃ j : ℕ,
          ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | gArity c = j + 2})) :=
        (measure_iUnion hdisj hmeas).symm
    _ = _ := by rw [hcover]

/-- A genuine split is almost sure. -/
lemma survivalMeasure_two_le_gArity (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1) :
    survivalMeasure (N := N) θ {c : GWord N → ℕ | 2 ≤ gArity c} = 1 := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  have hnull : survivalMeasure (N := N) θ {c : GWord N → ℕ | 2 ≤ gArity c}ᶜ = 0 := by
    refine measure_mono_null (fun c hc ↦ ?_)
      (measure_union_null (survivalMeasure_gArity_eq_one θ hJN hq hs1)
        (survivalMeasure_compl_survives θ hJN hq))
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hc
    by_cases hsurv : Survives c
    · have h1 := one_le_gArity_of_survives hsurv
      exact Or.inl (show gArity c = 1 by omega)
    · exact Or.inr hsurv
  have hle : survivalMeasure (N := N) θ {c : GWord N → ℕ | 2 ≤ gArity c} ≤ 1 :=
    prob_le_one
  refine le_antisymm hle ?_
  have hunion : (1 : ℝ≥0∞) = survivalMeasure (N := N) θ
      ({c : GWord N → ℕ | 2 ≤ gArity c} ∪ {c : GWord N → ℕ | 2 ≤ gArity c}ᶜ) := by
    rw [Set.union_compl_self]
    exact measure_univ.symm
  calc (1 : ℝ≥0∞) = _ := hunion
    _ ≤ survivalMeasure (N := N) θ {c : GWord N → ℕ | 2 ≤ gArity c}
        + survivalMeasure (N := N) θ {c : GWord N → ℕ | 2 ≤ gArity c}ᶜ :=
      measure_union_le _ _
    _ = survivalMeasure (N := N) θ {c : GWord N → ℕ | 2 ≤ gArity c} := by
      rw [hnull, add_zero]

/-- **The mixture is a probability law.** -/
theorem tsum_gMixMass (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) :
    ∑' σ : GShape, gMixMass (N := N) θ σ = 1 := by
  have hdisj : Pairwise (Function.onFun Disjoint fun σ : GShape ↦
      ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | 2 ≤ gArity c})) := by
    intro σ σ' hne
    refine Set.disjoint_left.mpr fun c hc hc' ↦ hne ?_
    rw [← hc.1, ← hc'.1]
  have hmeas : ∀ σ : GShape, MeasurableSet
      ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | 2 ≤ gArity c}) :=
    fun σ ↦ (fibreMeasurableG_gShapeRoot σ).inter
      (fibreMeasurableG_gArity.preimage {k : ℕ | 2 ≤ k})
  have hcover : (⋃ σ : GShape,
        ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | 2 ≤ gArity c}))
      = {c : GWord N → ℕ | 2 ≤ gArity c} := by
    ext c
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun ⟨σ, _, h⟩ ↦ h, fun h ↦ ⟨gShapeRoot c, rfl, h⟩⟩
  calc ∑' σ : GShape, gMixMass (N := N) θ σ
      = ∑' σ : GShape, survivalMeasure (N := N) θ
          ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | 2 ≤ gArity c}) :=
        tsum_congr fun σ ↦ gMixMass_eq_measure θ hJN hq hq0 σ
    _ = survivalMeasure (N := N) θ (⋃ σ : GShape,
          ({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | 2 ≤ gArity c})) :=
        (measure_iUnion hdisj hmeas).symm
    _ = survivalMeasure (N := N) θ {c : GWord N → ℕ | 2 ≤ gArity c} := by rw [hcover]
    _ = 1 := survivalMeasure_two_le_gArity θ hJN hq hs1

/-- **The mixture as a probability law on `𝒮`.** -/
noncomputable def gMixPMF (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) : PMF GShape :=
  ⟨fun σ ↦ gMixMass (N := N) θ σ,
    (tsum_gMixMass θ hJN hq hq0 hs1) ▸ ENNReal.summable.hasSum⟩

@[simp] lemma gMixPMF_apply (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) (σ : GShape) :
    gMixPMF θ hJN hq hq0 hs1 σ = gMixMass (N := N) θ σ := rfl

/-! ### The reduced weight is at most one -/

lemma skeletonWeight_eq_zero_of_gt (θ : Offspring J) {κ : ℕ} (hκ0 : κ ≠ 0)
    (hκJ : J < κ) : θ.skeletonWeight κ = 0 := by
  rw [BranchingProcess.Offspring.skeletonWeight_of_ne_zero θ hκ0,
    θ.surviveWeight_vanishing hκJ, zero_div]

lemma reducedWeight_le_one (θ : Offspring J) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) {κ : ℕ} (hκ : 2 ≤ κ) : reducedWeight θ κ ≤ 1 := by
  rw [reducedWeight_def]
  rcases le_or_gt κ J with hκJ | hκJ
  · have hsum := BranchingProcess.Offspring.sum_skeletonWeight θ hq
    have hnonneg : ∀ j ∈ Finset.range (J + 1), 0 ≤ θ.skeletonWeight j := fun j _ ↦
      θ.skeletonWeight_nonneg hq j
    have hsub : ({1, κ} : Finset ℕ) ⊆ Finset.range (J + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j hj _ ↦ hnonneg j hj
    rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ κ)] at hle
    rw [div_le_one (by linarith)]
    linarith
  · rw [skeletonWeight_eq_zero_of_gt θ (by omega) hκJ, zero_div]
    norm_num

/-- The joint mass sits below the weighted conditional mass. -/
lemma gPairMass_le_gCondMass (θ : Offspring J) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) {κ : ℕ} (hκ : 2 ≤ κ) (σ : GShape) :
    gPairMass (N := N) θ κ σ ≤ gCondMass (N := N) θ κ σ := by
  rw [gCondMass_def]
  have hone : ENNReal.ofReal (reducedWeight θ κ) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (reducedWeight_le_one θ hq hs1 hκ)
  calc gPairMass (N := N) θ κ σ
      = gPairMass (N := N) θ κ σ * 1 := (mul_one _).symm
    _ ≤ gPairMass (N := N) θ κ σ * (ENNReal.ofReal (reducedWeight θ κ))⁻¹ :=
        mul_le_mul' le_rfl (ENNReal.one_le_inv.mpr hone)
    _ = gPairMass (N := N) θ κ σ / ENNReal.ofReal (reducedWeight θ κ) :=
        (div_eq_mul_inv _ _).symm

/-! ### Charged shapes and the base of the point bound -/

/-- **A charged shape at an arity**: every neck list length, the bouquet size at the
arity, and every bush degree carry positive mass. -/
def GShape.ChargedG (θ : Offspring J) (κ : ℕ) (σ : GShape) : Prop :=
  (∀ β ∈ σ.neckList, 0 < θ (1 + β.length) ∧ ∀ t ∈ β, RTree.ChargedT θ t)
    ∧ (0 < θ (κ + σ.bouquet.length) ∧ ∀ t ∈ σ.bouquet, RTree.ChargedT θ t)

/-- **The base of the point bound**: the least positive mass against the window
`q^J (1-q)^J`. -/
noncomputable def gPointBase (θ : Offspring J) : ℝ :=
  pminOff θ * θ.extinction ^ J * (1 - θ.extinction) ^ J

lemma gPointBase_pos (θ : Offspring J) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) : 0 < gPointBase θ := by
  have h1 : (0 : ℝ) < 1 - θ.extinction := by linarith
  have h2 := pminOff_pos θ
  rw [gPointBase]
  positivity

lemma gPointBase_le_pminOff (θ : Offspring J) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) : gPointBase θ ≤ pminOff θ := by
  have h1 : (0 : ℝ) ≤ 1 - θ.extinction := by linarith
  have hq1 : θ.extinction ≤ 1 := θ.extinction_le_one
  have h2 : θ.extinction ^ J ≤ 1 := pow_le_one₀ θ.extinction_nonneg hq1
  have h3 : (1 - θ.extinction) ^ J ≤ 1 := pow_le_one₀ h1 (by linarith [θ.extinction_nonneg])
  have h4 := pminOff_pos θ
  calc gPointBase θ
      ≤ pminOff θ * θ.extinction ^ J * 1 := by
        rw [gPointBase]
        refine mul_le_mul_of_nonneg_left h3 ?_
        positivity
    _ = pminOff θ * θ.extinction ^ J := mul_one _
    _ ≤ pminOff θ * 1 := mul_le_mul_of_nonneg_left h2 h4.le
    _ = pminOff θ := mul_one _

/-- **The point bound of a decoration factor**: any charged count with a positive
number of survivors carries at least the base. -/
lemma gPointBase_le_decFactor (θ : Offspring J) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) {j k : ℕ} (hj : 0 < θ j) (hkj : k ≤ j) (hk1 : 1 ≤ k) :
    gPointBase θ
      ≤ θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k * θ.extinction ^ (j - k)
        / (1 - θ.extinction) := by
  have hq1 : (0 : ℝ) < 1 - θ.extinction := by linarith
  have hqle : θ.extinction ≤ 1 := θ.extinction_le_one
  have h1qle : 1 - θ.extinction ≤ 1 := by linarith [θ.extinction_nonneg]
  have hjJ : j ≤ J := by
    by_contra hgt
    rw [θ.vanishing j (by omega)] at hj
    exact lt_irrefl 0 hj
  have hpm : pminOff θ ≤ θ j := pminOff_le hj
  have hqk : θ.extinction ^ J ≤ θ.extinction ^ (j - k) :=
    pow_le_pow_of_le_one θ.extinction_nonneg hqle (by omega)
  have h1k : (1 - θ.extinction) ^ J ≤ (1 - θ.extinction) ^ k :=
    pow_le_pow_of_le_one hq1.le h1qle (by omega)
  have hch : (1 : ℝ) ≤ (j.choose k : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos hkj).ne'
  have hB : gPointBase θ ≤ θ j * θ.extinction ^ (j - k) * (1 - θ.extinction) ^ k := by
    rw [gPointBase]
    refine mul_le_mul (mul_le_mul hpm hqk (by positivity) (θ.nonneg j)) h1k
      (by positivity) ?_
    have := θ.nonneg j
    positivity
  have hB2 : θ j * θ.extinction ^ (j - k) * (1 - θ.extinction) ^ k
      ≤ θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k * θ.extinction ^ (j - k) := by
    have hnn : (0 : ℝ) ≤ θ j * (1 - θ.extinction) ^ k * θ.extinction ^ (j - k) := by
      have := θ.nonneg j
      positivity
    nlinarith
  have hdiv : θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k * θ.extinction ^ (j - k)
      ≤ θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k * θ.extinction ^ (j - k)
        / (1 - θ.extinction) := by
    rw [le_div_iff₀ hq1]
    have hnn : (0 : ℝ)
        ≤ θ j * (j.choose k : ℝ) * (1 - θ.extinction) ^ k * θ.extinction ^ (j - k) := by
      have h0 := θ.nonneg j
      have h1 : (0 : ℝ) ≤ (j.choose k : ℝ) := Nat.cast_nonneg _
      positivity
    nlinarith
  linarith

/-! ### The point bound of the masses -/

/-- The sizes of a forest, summed by position. -/
lemma RTree.sizeF_eq_sum_getD : ∀ β : List RTree,
    RTree.sizeF β = ∑ m ∈ Finset.range β.length, (β.getD m (.node [])).size
  | [] => by simp [RTree.sizeF]
  | c :: cs => by
      rw [RTree.sizeF, RTree.sizeF_eq_sum_getD cs, List.length_cons,
        Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      exact Nat.add_comm _ _

/-- **The point bound of a neck decoration**: one factor of the base per vertex, the
neck vertex included. -/
lemma le_gDecMass (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) {β : List RTree} (hj : 0 < θ (1 + β.length))
    (hall : ∀ t ∈ β, RTree.ChargedT θ t) :
    ENNReal.ofReal (gPointBase θ) ^ (1 + RTree.sizeF β) ≤ gDecMass (N := N) θ β := by
  have hbush : ENNReal.ofReal (gPointBase θ) ^ RTree.sizeF β
      ≤ ∏ m ∈ Finset.range β.length, bushMeasure (N := N) θ (listSets β m) := by
    have hstep : ∀ m ∈ Finset.range β.length,
        ENNReal.ofReal (gPointBase θ) ^ (β.getD m (.node [])).size
          ≤ bushMeasure (N := N) θ (listSets β m) := by
      intro m hm
      have hm' : m < β.length := Finset.mem_range.mp hm
      rw [bushMeasure_listSets hm', List.getD_eq_getElem β _ hm']
      calc ENNReal.ofReal (gPointBase θ) ^ (β[m]'hm').size
          ≤ ENNReal.ofReal (pminOff θ) ^ (β[m]'hm').size := by
            gcongr
            exact gPointBase_le_pminOff θ hq hq0
        _ = ENNReal.ofReal (pminOff θ ^ (β[m]'hm').size) := by
            rw [ENNReal.ofReal_pow (pminOff_pos θ).le]
        _ ≤ bushMassR (N := N) θ (β[m]'hm') :=
            ofReal_pow_le_bushMassR θ hJN (hall _ (β.getElem_mem hm'))
    calc ENNReal.ofReal (gPointBase θ) ^ RTree.sizeF β
        = ∏ m ∈ Finset.range β.length,
            ENNReal.ofReal (gPointBase θ) ^ (β.getD m (.node [])).size := by
          rw [Finset.prod_pow_eq_pow_sum, RTree.sizeF_eq_sum_getD]
      _ ≤ _ := Finset.prod_le_prod' hstep
  rw [gDecMass_def, BranchingProcess.decorationMass]
  have hr : 1 + β.length - 1 = β.length := by omega
  rw [hr, pow_add, pow_one]
  refine mul_le_mul' ?_ hbush
  refine ENNReal.ofReal_le_ofReal ?_
  have h := gPointBase_le_decFactor θ hq hq0 hj (by omega : 1 ≤ 1 + β.length) le_rfl
  rwa [hr] at h

/-- **The point bound of the terminating split**: one factor of the base per vertex of
the split and its bouquet. -/
lemma le_gSplitMass (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) {κ : ℕ} (hκ1 : 1 ≤ κ) {β : List RTree}
    (hj : 0 < θ (κ + β.length)) (hall : ∀ t ∈ β, RTree.ChargedT θ t) :
    ENNReal.ofReal (gPointBase θ) ^ (1 + RTree.sizeF β) ≤ gSplitMass (N := N) θ κ β := by
  have hbush : ENNReal.ofReal (gPointBase θ) ^ RTree.sizeF β
      ≤ ∏ m ∈ Finset.range β.length, bushMeasure (N := N) θ (listSets β m) := by
    have hstep : ∀ m ∈ Finset.range β.length,
        ENNReal.ofReal (gPointBase θ) ^ (β.getD m (.node [])).size
          ≤ bushMeasure (N := N) θ (listSets β m) := by
      intro m hm
      have hm' : m < β.length := Finset.mem_range.mp hm
      rw [bushMeasure_listSets hm', List.getD_eq_getElem β _ hm']
      calc ENNReal.ofReal (gPointBase θ) ^ (β[m]'hm').size
          ≤ ENNReal.ofReal (pminOff θ) ^ (β[m]'hm').size := by
            gcongr
            exact gPointBase_le_pminOff θ hq hq0
        _ = ENNReal.ofReal (pminOff θ ^ (β[m]'hm').size) := by
            rw [ENNReal.ofReal_pow (pminOff_pos θ).le]
        _ ≤ bushMassR (N := N) θ (β[m]'hm') :=
            ofReal_pow_le_bushMassR θ hJN (hall _ (β.getElem_mem hm'))
    calc ENNReal.ofReal (gPointBase θ) ^ RTree.sizeF β
        = ∏ m ∈ Finset.range β.length,
            ENNReal.ofReal (gPointBase θ) ^ (β.getD m (.node [])).size := by
          rw [Finset.prod_pow_eq_pow_sum, RTree.sizeF_eq_sum_getD]
      _ ≤ _ := Finset.prod_le_prod' hstep
  rw [gSplitMass_def, BranchingProcess.decorationMass]
  have hr : κ + β.length - κ = β.length := by omega
  rw [hr, pow_add, pow_one]
  refine mul_le_mul' ?_ hbush
  refine ENNReal.ofReal_le_ofReal ?_
  have h := gPointBase_le_decFactor θ hq hq0 hj (by omega : κ ≤ κ + β.length) hκ1
  rwa [hr] at h

/-- The neck lists carry one factor of the base per vertex of the neck. -/
lemma le_prod_map_gDecMass (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) : ∀ {L : List (List RTree)},
    (∀ β ∈ L, 0 < θ (1 + β.length) ∧ ∀ t ∈ β, RTree.ChargedT θ t) →
    ENNReal.ofReal (gPointBase θ) ^ (L.length + (L.map RTree.sizeF).sum)
      ≤ (L.map (gDecMass (N := N) θ)).prod := by
  intro L
  induction L with
  | nil => simp
  | cons β L ih =>
      intro hch
      simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons]
      have hexp : L.length + 1 + (RTree.sizeF β + (L.map RTree.sizeF).sum)
          = (1 + RTree.sizeF β) + (L.length + (L.map RTree.sizeF).sum) := by omega
      rw [hexp, pow_add]
      exact mul_le_mul'
        (le_gDecMass θ hJN hq hq0 (hch β (by simp)).1 (hch β (by simp)).2)
        (ih fun β' hβ' ↦ hch β' (List.mem_cons_of_mem _ hβ'))

/-- **`thm:mass-uniform`, the point clause for the joint mass**: a charged shape
carries at least the base to its size, against the reduced weight of its arity. -/
theorem ofReal_pow_le_gPairMass (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) {κ : ℕ} (hκ1 : 1 ≤ κ) {σ : GShape}
    (hch : GShape.ChargedG θ κ σ) :
    ENNReal.ofReal (gPointBase θ ^ σ.size) ≤ gPairMass (N := N) θ κ σ := by
  obtain ⟨hneck, hbq⟩ := hch
  have hsize : σ.size = (σ.neckList.length + (σ.neckList.map RTree.sizeF).sum)
      + (1 + RTree.sizeF σ.bouquet) := by
    have h := σ.size_eq
    have hdecs : σ.decs = σ.neckList ++ [σ.bouquet] := σ.decs_eq_append
    rw [hdecs, List.map_append, List.sum_append] at h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
    have hlen : σ.neckList.length = σ.necks := by
      rw [GShape.neckList, List.length_ofFn]
    rw [GShape.neckLen] at h
    omega
  rw [ENNReal.ofReal_pow (gPointBase_pos θ hq hq0).le, hsize, pow_add, gPairMass_def]
  exact mul_le_mul' (le_prod_map_gDecMass θ hJN hq hq0 hneck)
    (le_gSplitMass θ hJN hq hq0 hκ1 hbq.1 hbq.2)

/-- **`thm:mass-uniform`, the point clause for the conditional laws**: uniformly over
the arities, a charged shape carries at least the base to its size. -/
theorem ofReal_pow_le_gCondMass (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1) {κ : ℕ} (hκ : 2 ≤ κ)
    {σ : GShape} (hch : GShape.ChargedG θ κ σ) :
    ENNReal.ofReal (gPointBase θ ^ σ.size) ≤ gCondMass (N := N) θ κ σ :=
  le_trans (ofReal_pow_le_gPairMass θ hJN hq hq0 (by omega) hch)
    (gPairMass_le_gCondMass θ hq hs1 hκ σ)

/-- **`thm:mass-uniform`, the point clause for the mixture**: a shape charged at any
arity carries at least the base to its size under the mixture. -/
theorem ofReal_pow_le_gMixMass (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) {κ : ℕ} (hκ : 2 ≤ κ) {σ : GShape}
    (hch : GShape.ChargedG θ κ σ) :
    ENNReal.ofReal (gPointBase θ ^ σ.size) ≤ gMixMass (N := N) θ σ :=
  le_trans (ofReal_pow_le_gPairMass θ hJN hq hq0 (by omega) hch)
    (gPairMass_le_gMixMass θ hκ σ)

end ChainClasses
