import ChainClasses.Regime.UniformField
import ChainClasses.General.GeneralShapeCoupling

/-!
`thm:relabel` (`it:relabel-law`), `thm:product-form` of
`matching_classes_general.tex` and `thm:hairy-cross` (`it:hairy-cross-product`)
of `trichotomy.tex`: the labelled reduced skeleton, over the constructed space.

The sample of `θ'` is paired with the uniform field of `UniformField`, one uniform
variable at every reduced-skeleton address, and every address `w` draws a partner shape
from the coupling `π_{k(w)}` of the conditional law `μ_{k(w)}` of `θ'` with the mixture
`μ` of `θ`, conditioned on the observed shape `S(w)` and realised by the uniform
variable `U(w)`; the label is the class `rep_D` of the partner.  The conditional
independence `thm:conditional-iid` of the shapes given the arities, the conditional
draw of the coupling and the product formula of `UniformField` make the partners i.i.d.
with the mixture law and independent of the arity field, and the classes inherit the
product law `Q = μ_D ⊗ ν̃`.  The mixture side `θ` and the labelled side `θ'` are two
laws throughout: with `θ' = θ` this is `thm:relabel` and `thm:product-form`, with two
laws coupled to the one mixture it is `thm:hairy-cross` (`it:hairy-cross-product`).

* `gShapeEquivNat`, `GShape.instEncodable`: `𝒮` as an encodable type, through the
  enumeration of `GeneralShapeMetric`.
* `labelMeasure`, `GCouplings`, `gDraw`, `gPartner`, `gLab`: **the labelled space**, the
  family of couplings, the conditional draw at one address, the partner field and the
  label field.
* `measurableSet_gDraw_fibre`, `measurableSet_gPartner_fibre`, `measurableSet_gLab_fibre`:
  the fields are measurable on the labelled space.
* `labelMeasure_partner_pattern`: **`thm:relabel` (`it:relabel-law`)**, the
  partners over a prefix-closed probe are i.i.d. with the mixture law and independent
  of the arities.
* `gClassMass`, `gClassMass_eq_tsum_ite`: the mass of a class under `μ_D`.
* `labelMeasure_label_pattern`: **`thm:product-form` and
  `thm:hairy-cross` (`it:hairy-cross-product`)**, the pairs of a label and an
  arity over a prefix-closed probe are i.i.d. with the product law `μ_D ⊗ ν̃`.
* `labelMeasure_label_marginal`: the marginal of the label at the root is `μ_D`.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
open BranchingProcess (Offspring survivalMeasure)

variable {J N J' N' : ℕ}

/-! ### The shapes as an encodable type -/

/-- The enumeration of `𝒮` as an equivalence with `ℕ`, `gShapeIdx` forward and
`gShapeEnum` backward. -/
noncomputable def gShapeEquivNat : GShape ≃ ℕ :=
  (Equiv.ofBijective gShapeEnum ⟨gShapeEnum_injective, gShapeEnum_surjective⟩).symm

@[simp] lemma gShapeEquivNat_apply (σ : GShape) : gShapeEquivNat σ = gShapeIdx σ := rfl

@[simp] lemma gShapeEquivNat_symm_apply (n : ℕ) : gShapeEquivNat.symm n = gShapeEnum n := rfl

/-- `𝒮` is encodable through its enumeration, which is what the draw of a partner
shape by a uniform variable consumes. -/
noncomputable instance GShape.instEncodable : Encodable GShape :=
  Encodable.ofEquiv ℕ gShapeEquivNat

/-! ### The labelled space -/

/-- **The labelled space**: the sample of `θ'` conditioned on survival against the
uniform field over the reduced-skeleton addresses. -/
noncomputable def labelMeasure (θ' : Offspring J') :
    Measure ((GWord N' → ℕ) × (GWord N' → ℝ)) :=
  (survivalMeasure (N := N') θ').prod (uniformField (GWord N'))

theorem isProbabilityMeasure_labelMeasure (θ' : Offspring J') (hJN' : J' ≤ N')
    (hq' : θ'.extinction < 1) : IsProbabilityMeasure (labelMeasure (N' := N') θ') := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  exact inferInstanceAs (IsProbabilityMeasure
    ((survivalMeasure (N := N') θ').prod (uniformField (GWord N'))))

/-- A family of couplings, one at every arity of positive reduced weight: the data of
`thm:relabel`, `π_κ` coupling `μ_κ` with the mixture. -/
abbrev GCouplings (θ' : Offspring J') : Type :=
  ∀ κ : ℕ, 2 ≤ κ → 0 < reducedWeight θ' κ → PMF (GShape × GShape)

/-- **The conditional draw at one address**: the partner of the shape `σ` at arity `κ`
drawn from `π_κ(·|σ)` by the uniform variable `r`, with the trivial shape where the
arity carries no coupling. -/
noncomputable def gDraw {θ' : Offspring J'} (π : GCouplings θ') (κ : ℕ) (σ : GShape)
    (r : ℝ) : GShape :=
  if h : 2 ≤ κ ∧ 0 < reducedWeight θ' κ then condDraw (π κ h.1 h.2) σ r else gOne

/-- **The partner field**: at every reduced-skeleton address the partner of the
observed shape at the observed arity, drawn by the uniform variable there. -/
noncomputable def gPartner {θ' : Offspring J'} (π : GCouplings θ')
    (ω : (GWord N' → ℕ) × (GWord N' → ℝ)) (u : GWord N') : GShape :=
  gDraw π (gArityAt ω.1 u) (gShapeAt ω.1 u) (ω.2 u)

/-- **The label field** `x(w) = rep_D(partner)`: the class of the partner shape. -/
noncomputable def gLab (D : ℝ) {θ' : Offspring J'} (π : GCouplings θ')
    (ω : (GWord N' → ℕ) × (GWord N' → ℝ)) (u : GWord N') : ℕ :=
  gNetLab D (gPartner π ω u)

/-! ### Measurability -/

lemma measurableSet_gDraw_fibre {θ' : Offspring J'} (π : GCouplings θ') (κ : ℕ)
    (σ τ : GShape) : MeasurableSet {r : ℝ | gDraw π κ σ r = τ} := by
  by_cases h : 2 ≤ κ ∧ 0 < reducedWeight θ' κ
  · simp only [gDraw, dif_pos h]
    exact measurableSet_condDraw_fibre _ σ τ
  · simp only [gDraw, dif_neg h]
    exact MeasurableSet.const _

/-- The partner field is measurable on the labelled space. -/
lemma measurableSet_gPartner_fibre {θ' : Offspring J'} (π : GCouplings θ') (u : GWord N')
    (τ : GShape) :
    MeasurableSet {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gPartner π ω u = τ} := by
  have hset : {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gPartner π ω u = τ}
      = ⋃ p : GShape × ℕ,
          ({c : GWord N' → ℕ | gShapeAt c u = p.1} ∩ {c : GWord N' → ℕ | gArityAt c u = p.2})
            ×ˢ {U : GWord N' → ℝ | gDraw π p.2 p.1 (U u) = τ} := by
    ext ⟨c, U⟩
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_inter_iff, gPartner,
      Prod.exists]
    constructor
    · intro h
      exact ⟨_, _, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨σ, κ, ⟨h1, h2⟩, h⟩
      rw [h1, h2]
      exact h
  rw [hset]
  exact MeasurableSet.iUnion fun p ↦
    ((fibreMeasurableG_gShapeAt u p.1).inter (fibreMeasurableG_gArityAt u p.2)).prod
      (BranchingProcess.measurable_coord (α := ℝ) u (measurableSet_gDraw_fibre π p.2 p.1 τ))

/-- The label field is measurable on the labelled space. -/
lemma measurableSet_gLab_fibre (D : ℝ) {θ' : Offspring J'} (π : GCouplings θ')
    (u : GWord N') (a : ℕ) :
    MeasurableSet {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gLab D π ω u = a} := by
  have hset : {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gLab D π ω u = a}
      = ⋃ τ : {τ : GShape // gNetLab D τ = a},
          {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gPartner π ω u = τ} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, gLab, Subtype.exists, exists_prop]
    exact ⟨fun h ↦ ⟨_, h, rfl⟩, by rintro ⟨τ, hτ, rfl⟩; exact hτ⟩
  rw [hset]
  exact MeasurableSet.iUnion fun τ ↦ measurableSet_gPartner_fibre π u τ

/-! ### The partners are i.i.d. with the mixture law -/

/-- **`thm:relabel` (`it:relabel-law`), over the constructed space**: with a
family of couplings of the conditional laws of `θ'` with the mixture of `θ`, the
partners over a prefix-closed probe of the reduced skeleton are independent with the
mixture law, independently of the arity field.  The coupling enters through its second
marginal only, which is how the partner law does not see the arity. -/
theorem labelMeasure_partner_pattern (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') {D : ℝ} (π : GCouplings θ')
    (hπ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
      IsGShapeCoupling D (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν) (gMixPMF θ hJN hq hq0 hs1)
        (π κ hκ hν))
    (F : Finset (GWord N')) (hpc : ∀ u ∈ F, ∀ p : GWord N', p <+: u → p ∈ F)
    (τ : GWord N' → GShape) (k : GWord N' → ℕ) (hk2 : ∀ u ∈ F, 2 ≤ k u)
    (hkJ : ∀ u ∈ F, k u ≤ J')
    (hcomp : ∀ u ∈ F, ∀ i : Fin N', u ++ [i] ∈ F → (i : ℕ) < k u) :
    labelMeasure θ'
        (⋂ u ∈ F, ({ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gPartner π ω u = τ u}
          ∩ {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gArityAt ω.1 u = k u}))
      = (∏ u ∈ F, gMixMass (N := N) θ (τ u))
          * survivalMeasure (N := N') θ'
              (⋂ u ∈ F, {c : GWord N' → ℕ | gArityAt c u = k u}) := by
  have hν : ∀ u : ↥F, 0 < reducedWeight θ' (k u) := fun u ↦
    reducedWeight_pos θ' hq' hq0' hJ2' hθJ' (hk2 u u.2) (hkJ u u.2)
  -- the event as a probe of the labels `lab u (X u) (U u)`
  set X : (GWord N' → ℕ) → GWord N' → GShape × ℕ :=
    fun c u ↦ (gShapeAt c u, gArityAt c u) with hX
  set lab : GWord N' → GShape × ℕ → ℝ → GShape × ℕ :=
    fun _ p r ↦ (gDraw π p.2 p.1 r, p.2) with hlab
  set a : GWord N' → GShape × ℕ := fun u ↦ (τ u, k u) with ha
  have hevent : (⋂ u ∈ F, ({ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gPartner π ω u = τ u}
        ∩ {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gArityAt ω.1 u = k u}))
      = ⋂ u ∈ F, {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | lab u (X ω.1 u) (ω.2 u) = a u} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, hlab, hX, ha, gPartner,
      Prod.mk.injEq]
  have hXm : ∀ u (t : GShape × ℕ), MeasurableSet {c : GWord N' → ℕ | X c u = t} := by
    intro u t
    have : {c : GWord N' → ℕ | X c u = t}
        = {c : GWord N' → ℕ | gShapeAt c u = t.1} ∩ {c : GWord N' → ℕ | gArityAt c u = t.2} := by
      ext c
      simp [hX, Prod.ext_iff]
    rw [this]
    exact (fibreMeasurableG_gShapeAt u t.1).inter (fibreMeasurableG_gArityAt u t.2)
  have hlabm : ∀ u (t v : GShape × ℕ), MeasurableSet {r : ℝ | lab u t r = v} := by
    intro u t v
    by_cases h : t.2 = v.2
    · have : {r : ℝ | lab u t r = v} = {r : ℝ | gDraw π t.2 t.1 r = v.1} := by
        ext r
        simp [hlab, Prod.ext_iff, h]
      rw [this]
      exact measurableSet_gDraw_fibre π t.2 t.1 v.1
    · have : {r : ℝ | lab u t r = v} = ∅ := by
        ext r
        simp [hlab, Prod.ext_iff, h]
      rw [this]
      exact MeasurableSet.empty
  rw [hevent, labelMeasure,
    prod_uniformField_pattern (survivalMeasure (N := N') θ') X hXm lab hlabm F a]
  -- only the patterns with the prescribed arities contribute
  set emb : (↥F → GShape) → (↥F → GShape × ℕ) := fun g u ↦ (g u, k u) with hemb
  have hemb_inj : Function.Injective emb := by
    intro g g' h
    funext u
    have := congrFun h u
    simp only [hemb, Prod.mk.injEq] at this
    exact this.1
  set G : (↥F → GShape × ℕ) → ℝ≥0∞ := fun f ↦
    survivalMeasure (N := N') θ' (⋂ u : ↥F, {c : GWord N' → ℕ | X c u = f u})
      * ∏ u : ↥F, volume {r ∈ Set.Ico (0 : ℝ) 1 | lab u (f u) r = a u} with hG
  have hsupp : Function.support G ⊆ Set.range emb := by
    intro f hf
    refine ⟨fun u ↦ (f u).1, ?_⟩
    by_contra hne
    apply hf
    have hu : ∃ u : ↥F, (f u).2 ≠ k u := by
      by_contra hall
      push Not at hall
      apply hne
      funext u
      simp only [hemb]
      exact Prod.ext rfl (hall u).symm
    obtain ⟨u, hu⟩ := hu
    have hzero : volume {r ∈ Set.Ico (0 : ℝ) 1 | lab u (f u) r = a u} = 0 := by
      have : {r ∈ Set.Ico (0 : ℝ) 1 | lab u (f u) r = a u} = ∅ := by
        ext r
        simp [hlab, ha, Prod.ext_iff, hu]
      rw [this, measure_empty]
    simp only [hG]
    rw [Finset.prod_eq_zero (Finset.mem_univ u) hzero, mul_zero]
  rw [← hemb_inj.tsum_eq hsupp]
  -- each pattern: the conditional masses cancel against the conditional draws
  set gext : (↥F → GShape) → GWord N' → GShape :=
    fun g u ↦ if h : u ∈ F then g ⟨u, h⟩ else gOne with hgext
  have hgext_apply : ∀ (g : ↥F → GShape) (u : ↥F), gext g u = g u := by
    intro g u
    simp only [hgext, dif_pos u.2]
  have hterm : ∀ g : ↥F → GShape, G (emb g)
      = survivalMeasure (N := N') θ' (⋂ u ∈ F, {c : GWord N' → ℕ | gArityAt c u = k u})
          * ∏ u : ↥F, (π (k u) (hk2 u u.2) (hν u)) (g u, τ u) := by
    intro g
    have hXset : (⋂ u : ↥F, {c : GWord N' → ℕ | X c u = emb g u})
        = ⋂ u ∈ F, ({c : GWord N' → ℕ | gShapeAt c u = gext g u}
            ∩ {c : GWord N' → ℕ | gArityAt c u = k u}) := by
      ext c
      simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, hX, hemb, Prod.mk.injEq]
      constructor
      · intro h u hu
        obtain ⟨h1, h2⟩ := h ⟨u, hu⟩
        exact ⟨by rw [h1, hgext_apply g ⟨u, hu⟩], h2⟩
      · intro h u
        obtain ⟨h1, h2⟩ := h u u.2
        exact ⟨by rw [h1, hgext_apply g u], h2⟩
    have hvol : ∀ u : ↥F, volume {r ∈ Set.Ico (0 : ℝ) 1 | lab u (emb g u) r = a u}
        = volume {r ∈ Set.Ico (0 : ℝ) 1 |
            condDraw (π (k u) (hk2 u u.2) (hν u)) (g u) r = τ u} := by
      intro u
      congr 1
      ext r
      simp only [Set.mem_setOf_eq, hlab, hemb, ha, Prod.mk.injEq, and_true, gDraw,
        dif_pos (And.intro (hk2 u u.2) (hν u))]
    have hfac : ∀ u : ↥F, gCondMass (N := N') θ' (k u) (g u)
        * volume {r ∈ Set.Ico (0 : ℝ) 1 |
            condDraw (π (k u) (hk2 u u.2) (hν u)) (g u) r = τ u}
        = (π (k u) (hk2 u u.2) (hν u)) (g u, τ u) := by
      intro u
      have hm := (hπ (k u) (hk2 u u.2) (hν u)).marg₁ (g u)
      rw [gCondPMF_apply] at hm
      rw [← hm]
      exact margFstT_mul_volume_condDraw_fibre _ _ _
    simp only [hG]
    rw [hXset, conditional_iid θ' hJN' hq' hq0' hJ2' hθJ' F hpc (gext g) k hk2 hkJ hcomp,
      Finset.prod_congr rfl fun u _ ↦ hvol u, ← Finset.prod_coe_sort F,
      mul_comm (∏ _, _) _, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun u _ ↦ ?_
    rw [hgext_apply g u]
    exact hfac u
  -- sum the patterns: the second marginals of the couplings are the mixture
  rw [tsum_congr hterm, ENNReal.tsum_mul_left,
    tsum_pi_prod fun (u : ↥F) (σ : GShape) ↦ (π (k u) (hk2 u u.2) (hν u)) (σ, τ u),
    mul_comm]
  congr 1
  rw [← Finset.prod_coe_sort F]
  refine Finset.prod_congr rfl fun u _ ↦ ?_
  have hm := (hπ (k u) (hk2 u u.2) (hν u)).marg₂ (τ u)
  rw [gMixPMF_apply] at hm
  rw [← hm]
  rfl

/-! ### The labels are i.i.d. with the class law -/

/-- **The mass of a class under `μ_D`**: the mixture mass of the shapes in the class. -/
noncomputable def gClassMass (θ : Offspring J) (D : ℝ) (a : ℕ) : ℝ≥0∞ :=
  ∑' σ : {σ : GShape // gNetLab D σ = a}, gMixMass (N := N) θ σ

lemma gClassMass_eq_tsum_ite (θ : Offspring J) (D : ℝ) (a : ℕ) :
    gClassMass (N := N) θ D a
      = ∑' σ : GShape, if gNetLab D σ = a then gMixMass (N := N) θ σ else 0 := by
  show ∑' σ : ↥{σ : GShape | gNetLab D σ = a}, gMixMass (N := N) θ σ = _
  rw [tsum_subtype {σ : GShape | gNetLab D σ = a} (gMixMass (N := N) θ)]
  refine tsum_congr fun σ ↦ ?_
  simp [Set.indicator_apply]

/-- **`thm:product-form` and `thm:hairy-cross` (`it:hairy-cross-product`), over
the constructed space**: the pairs of a label and an arity over a prefix-closed probe
of the reduced skeleton are independent with the product law `Q = μ_D ⊗ ν̃`, the class
masses of the mixture of `θ` against the reduced weights of `θ'`. -/
theorem labelMeasure_label_pattern (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') {D : ℝ} (π : GCouplings θ')
    (hπ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
      IsGShapeCoupling D (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν) (gMixPMF θ hJN hq hq0 hs1)
        (π κ hκ hν))
    (F : Finset (GWord N')) (hpc : ∀ u ∈ F, ∀ p : GWord N', p <+: u → p ∈ F)
    (a : GWord N' → ℕ) (k : GWord N' → ℕ) (hk2 : ∀ u ∈ F, 2 ≤ k u)
    (hkJ : ∀ u ∈ F, k u ≤ J')
    (hcomp : ∀ u ∈ F, ∀ i : Fin N', u ++ [i] ∈ F → (i : ℕ) < k u) :
    labelMeasure θ'
        (⋂ u ∈ F, ({ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gLab D π ω u = a u}
          ∩ {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gArityAt ω.1 u = k u}))
      = (∏ u ∈ F, gClassMass (N := N) θ D (a u))
          * ∏ u ∈ F, ENNReal.ofReal (reducedWeight θ' (k u)) := by
  set gext : (↥F → GShape) → GWord N' → GShape :=
    fun g u ↦ if h : u ∈ F then g ⟨u, h⟩ else gOne with hgext
  have hgext_apply : ∀ (g : ↥F → GShape) (u : ↥F), gext g u = g u := by
    intro g u
    simp only [hgext, dif_pos u.2]
  set S : Set (↥F → GShape) := {g | ∀ u : ↥F, gNetLab D (g u) = a u} with hS
  set E : (↥F → GShape) → Set ((GWord N' → ℕ) × (GWord N' → ℝ)) := fun g ↦
    ⋂ u ∈ F, ({ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gPartner π ω u = gext g u}
      ∩ {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gArityAt ω.1 u = k u}) with hE
  have hcover : (⋂ u ∈ F, ({ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gLab D π ω u = a u}
        ∩ {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gArityAt ω.1 u = k u}))
      = ⋃ g : ↥S, E g := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, gLab, hE,
      hS, Subtype.exists, exists_prop]
    constructor
    · intro h
      refine ⟨fun u ↦ gPartner π ω u, fun u ↦ (h u u.2).1, fun u hu ↦ ⟨?_, (h u hu).2⟩⟩
      simp only [hgext, dif_pos hu]
    · rintro ⟨g, hgS, hg⟩ u hu
      obtain ⟨h1, h2⟩ := hg u hu
      refine ⟨?_, h2⟩
      rw [h1]
      simp only [hgext, dif_pos hu]
      exact hgS ⟨u, hu⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun g : ↥S ↦ E g) := by
    intro g g' hne
    refine Set.disjoint_left.mpr fun ω hω hω' ↦ hne (Subtype.ext (funext fun u ↦ ?_))
    simp only [hE, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hω hω'
    have e1 := (hω u u.2).1
    have e2 := (hω' u u.2).1
    rw [hgext_apply] at e1 e2
    rw [← e1, ← e2]
  have hmeas : ∀ g : ↥S, MeasurableSet (E g) := fun g ↦
    MeasurableSet.biInter F.countable_toSet fun u _ ↦
      (measurableSet_gPartner_fibre π u _).inter
        (measurable_fst (fibreMeasurableG_gArityAt u (k u)))
  rw [hcover, measure_iUnion hdisj hmeas,
    tsum_congr fun g : ↥S ↦ labelMeasure_partner_pattern θ hJN hq hq0 hs1 θ' hJN' hq' hq0'
      hs1' hJ2' hθJ' π hπ F hpc (gext g) k hk2 hkJ hcomp,
    survivalMeasure_gArities θ' hJN' hq' hs1' F hpc k hk2 hcomp, ENNReal.tsum_mul_right]
  congr 1
  have h1 : ∀ g : ↥F → GShape, (∏ u ∈ F, gMixMass (N := N) θ (gext g u))
      = ∏ u : ↥F, gMixMass (N := N) θ (g u) := by
    intro g
    rw [← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun u _ ↦ by rw [hgext_apply g u]
  have h2 : ∀ g : ↥S, (∏ u ∈ F, gMixMass (N := N) θ (gext g u))
      = ∏ u : ↥F, (if gNetLab D ((g : ↥F → GShape) u) = a u
          then gMixMass (N := N) θ ((g : ↥F → GShape) u) else 0) := by
    intro g
    rw [h1]
    exact Finset.prod_congr rfl fun u _ ↦ by rw [if_pos (g.2 u)]
  rw [tsum_congr h2]
  rw [tsum_subtype_eq_of_support_subset (s := S) (f := fun g : ↥F → GShape ↦
    ∏ u : ↥F, if gNetLab D (g u) = a u then gMixMass (N := N) θ (g u) else 0) ?_]
  · rw [tsum_pi_prod fun (u : ↥F) (σ : GShape) ↦
        if gNetLab D σ = a u then gMixMass (N := N) θ σ else 0, ← Finset.prod_coe_sort F]
    exact Finset.prod_congr rfl fun u _ ↦ (gClassMass_eq_tsum_ite θ D (a u)).symm
  · intro g hg
    by_contra hgS
    apply hg
    simp only [hS, Set.mem_setOf_eq, not_forall] at hgS
    obtain ⟨u, hu⟩ := hgS
    exact Finset.prod_eq_zero (Finset.mem_univ u) (if_neg hu)

/-! ### The marginal at the root -/

/-- The arity event at the root, on the labelled space, carries the reduced weight. -/
lemma labelMeasure_root_arity (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hs1' : θ'.skeletonWeight 1 < 1) {κ : ℕ} (hκ : 2 ≤ κ) :
    labelMeasure θ' {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gArityAt ω.1 [] = κ}
      = ENNReal.ofReal (reducedWeight θ' κ) := by
  have hset : {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gArityAt ω.1 [] = κ}
      = {c : GWord N' → ℕ | gArity c = κ} ×ˢ (Set.univ : Set (GWord N' → ℝ)) := by
    ext ω
    simp [gArityAt]
  rw [labelMeasure, hset, Measure.prod_prod, measure_univ, mul_one,
    survivalMeasure_gArity_eq θ' hJN' hq' hs1' hκ]

/-- The arity events at the root outside the reduced support are null. -/
lemma labelMeasure_root_arity_null (θ' : Offspring J') (hJN' : J' ≤ N')
    (hq' : θ'.extinction < 1) (hs1' : θ'.skeletonWeight 1 < 1) {κ : ℕ}
    (hκ : ¬ (2 ≤ κ ∧ κ ≤ J')) :
    labelMeasure θ' {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gArityAt ω.1 [] = κ} = 0 := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N') θ' hJN' hq'
  by_cases h2 : 2 ≤ κ
  · have hJ : J' < κ := by
      by_contra hc
      exact hκ ⟨h2, not_lt.mp hc⟩
    rw [labelMeasure_root_arity θ' hJN' hq' hs1' h2, reducedWeight_def,
      skeletonWeight_eq_zero_of_gt θ' (by omega) hJ, zero_div, ENNReal.ofReal_zero]
  · have hset : {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gArityAt ω.1 [] = κ}
        = {c : GWord N' → ℕ | gArity c = κ} ×ˢ (Set.univ : Set (GWord N' → ℝ)) := by
      ext ω
      simp [gArityAt]
    rw [labelMeasure, hset, Measure.prod_prod, measure_univ, mul_one]
    refine measure_mono_null (t := {c : GWord N' → ℕ | 2 ≤ gArity c}ᶜ) (fun c hc ↦ ?_) ?_
    · simp only [Set.mem_setOf_eq] at hc
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hc]
      exact h2
    · have hm : MeasurableSet {c : GWord N' → ℕ | 2 ≤ gArity c} :=
        fibreMeasurableG_gArity.preimage {k : ℕ | 2 ≤ k}
      rw [measure_compl hm (measure_ne_top _ _),
        survivalMeasure_two_le_gArity θ' hJN' hq' hs1', measure_univ, tsub_self]

/-- **The marginal of the label at the root is `μ_D`**: the arity summed out of
`thm:product-form`. -/
theorem labelMeasure_label_marginal (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (hs1 : θ.skeletonWeight 1 < 1)
    (θ' : Offspring J') (hJN' : J' ≤ N') (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (hs1' : θ'.skeletonWeight 1 < 1) (hJ2' : 2 ≤ J')
    (hθJ' : 0 < θ' J') {D : ℝ} (π : GCouplings θ')
    (hπ : ∀ (κ : ℕ) (hκ : 2 ≤ κ) (hν : 0 < reducedWeight θ' κ),
      IsGShapeCoupling D (gCondPMF θ' hJN' hq' hq0' hs1' hκ hν) (gMixPMF θ hJN hq hq0 hs1)
        (π κ hκ hν))
    (a : ℕ) :
    labelMeasure θ' {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gLab D π ω [] = a}
      = gClassMass (N := N) θ D a := by
  have _ := isProbabilityMeasure_labelMeasure θ' hJN' hq'
  set A : ℕ → Set ((GWord N' → ℕ) × (GWord N' → ℝ)) := fun κ ↦
    {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gArityAt ω.1 [] = κ} with hA
  have hAmeas : ∀ κ, MeasurableSet (A κ) := fun κ ↦
    measurable_fst (fibreMeasurableG_gArityAt [] κ)
  have hAdisj : Pairwise (Function.onFun Disjoint A) := by
    intro κ κ' hne
    refine Set.disjoint_left.mpr fun ω hω hω' ↦ hne ?_
    simp only [hA, Set.mem_setOf_eq] at hω hω'
    rw [← hω, ← hω']
  have hAcover : (⋃ κ, A κ) = Set.univ := by
    ext ω
    simp [hA]
  have hcover : {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gLab D π ω [] = a}
      = ⋃ κ, ({ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gLab D π ω [] = a} ∩ A κ) := by
    rw [← Set.inter_iUnion, hAcover, Set.inter_univ]
  have hdisj : Pairwise (Function.onFun Disjoint fun κ ↦
      {ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gLab D π ω [] = a} ∩ A κ) := fun κ κ' hne ↦
    (hAdisj hne).mono Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ κ, MeasurableSet
      ({ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gLab D π ω [] = a} ∩ A κ) := fun κ ↦
    (measurableSet_gLab_fibre D π [] a).inter (hAmeas κ)
  have hterm : ∀ κ, labelMeasure θ'
      ({ω : (GWord N' → ℕ) × (GWord N' → ℝ) | gLab D π ω [] = a} ∩ A κ)
        = gClassMass (N := N) θ D a * labelMeasure θ' (A κ) := by
    intro κ
    by_cases hκ : 2 ≤ κ ∧ κ ≤ J'
    · have h := labelMeasure_label_pattern θ hJN hq hq0 hs1 θ' hJN' hq' hq0' hs1' hJ2' hθJ'
        π hπ {[]} (by simp) (fun _ ↦ a) (fun _ ↦ κ) (fun _ _ ↦ hκ.1) (fun _ _ ↦ hκ.2)
        (by simp)
      simp only [Finset.set_biInter_singleton, Finset.prod_singleton] at h
      rw [h, labelMeasure_root_arity θ' hJN' hq' hs1' hκ.1]
    · have hnull := labelMeasure_root_arity_null θ' hJN' hq' hs1' hκ
      rw [hnull, mul_zero]
      exact measure_mono_null Set.inter_subset_right hnull
  rw [hcover, measure_iUnion hdisj hmeas, tsum_congr hterm, ENNReal.tsum_mul_left,
    ← measure_iUnion hAdisj hAmeas, hAcover, measure_univ, mul_one]

end ChainClasses
