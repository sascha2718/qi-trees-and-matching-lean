import ChainClasses.Bushy.HairyUniversality

/-!
`sec:shape-harris` of `matching_classes_simple.tex` and `sec:hairy` of
`gw_classes_simple.tex`: the shape law is a probability law, the label law it pushes
forward along a label map, and the product form of the label field that `thm:hairy`
consumes.

`thm:shape-iid` gives the mass `shapeMass` of a shape and the product formula for the
shape field over a prefix-closed finite set of copies.  What is missing before that law
can be pushed forward is that it is a law at all: its masses sum to one.  They do,
because the fibres of the shape at the root partition the sample space, and the
factorisation over the whole of a prefix-closed set then hands the marginal at every
copy and the product form of the labels.

The label field is transported to the two-sample space by the same partition: over a
prefix-closed finite set of copies the label event is the disjoint union, over the shape
fields on that set, of a shape event times a uniform event.  `thm:shape-iid` factorises
the first, independence of the uniform field the second, and `tsum_pi_finset` exchanges
the sum over the shape fields with the product over the copies.

Two of the four hypotheses `thm:hairy` carries for `thm:shape-coupling` are discharged
here for every measurable label map, the product law and the measurability of the
sections.  The potential bound and the coupling of the second law to the first remain
hypotheses.

* `tsum_pi_fin`, `tsum_pi_finset`: summing a product of weights over all functions on a
  finite index multiplies the sums, the exchange the factorisations below are read
  through.
* `shapeExt`, `shapeEvent`, `shapeEvent_eq_iInter`, `survivalMeasure_shapeEvent`,
  `iUnion_shapeEvent`, `pairwise_shapeEvent`: the shape field read on a finite set of
  copies, its mass, and the partition of the sample space by it.
* `tsum_shapeMass`: **`thm:shape-iid`, the total mass**, the shape law is a probability
  law.
* `labMass`, `tsum_uniform_fibres`, `tsum_labMass`, `labPMF`: **the label law `q` of
  `thm:shape-coupling` (`it:shape-coupling-law`)**, the shape law pushed forward
  along a label map against the uniform variable, and its total mass.
* `hairyMeasure_shapeLab_prod`: **`thm:shape-coupling` (`it:shape-coupling-law`),
  the product form**, the labels of a prefix-closed finite set of copies are independent
  with the law `q`.
* `shapeIdx`: the index of a shape in the enumeration `shapeEnum`, with
  `shapeFamily_shapeIdx`.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory GraphMatching
open BranchingProcess (sample survivalMeasure Offspring)
open scoped ENNReal

/-! ### Products of sums over a finite index -/

/-- Summing a product of weights over all functions on `Fin n` multiplies the sums. -/
lemma tsum_pi_fin {α : Type*} : ∀ (n : ℕ) (g : Fin n → α → ℝ≥0∞),
    ∑' f : Fin n → α, ∏ i, g i (f i) = ∏ i, ∑' a, g i a := by
  intro n
  induction n with
  | zero =>
      intro g
      simp
  | succ n ih =>
      intro g
      have hcons : ∀ p : α × (Fin n → α),
          ∏ i, g i (Fin.consEquiv (fun _ ↦ α) p i) = g 0 p.1 * ∏ i, g i.succ (p.2 i) := by
        intro p
        rw [Fin.prod_univ_succ]
        simp [Fin.consEquiv]
      calc ∑' f : Fin (n + 1) → α, ∏ i, g i (f i)
          = ∑' p : α × (Fin n → α), ∏ i, g i (Fin.consEquiv (fun _ ↦ α) p i) :=
            (Equiv.tsum_eq (Fin.consEquiv fun _ ↦ α) fun f ↦ ∏ i, g i (f i)).symm
        _ = ∑' p : α × (Fin n → α), g 0 p.1 * ∏ i, g i.succ (p.2 i) := tsum_congr hcons
        _ = ∑' a : α, ∑' f' : Fin n → α, g 0 a * ∏ i, g i.succ (f' i) := ENNReal.tsum_prod'
        _ = ∑' a : α, g 0 a * ∑' f' : Fin n → α, ∏ i, g i.succ (f' i) :=
            tsum_congr fun _ ↦ ENNReal.tsum_mul_left
        _ = (∑' a : α, g 0 a) * ∑' f' : Fin n → α, ∏ i, g i.succ (f' i) :=
            ENNReal.tsum_mul_right
        _ = (∑' a : α, g 0 a) * ∏ i : Fin n, ∑' a : α, g i.succ a := by rw [ih]
        _ = ∏ i, ∑' a : α, g i a :=
            (Fin.prod_univ_succ fun i : Fin (n + 1) ↦ ∑' a : α, g i a).symm

/-- Summing a product of weights over all functions on a finite set multiplies the
sums. -/
lemma tsum_pi_finset {ι α : Type*} (s : Finset ι) (g : ι → α → ℝ≥0∞) :
    ∑' f : (↥s → α), ∏ w ∈ s.attach, g w.1 (f w) = ∏ w ∈ s, ∑' a : α, g w a := by
  classical
  set e := s.equivFin with he
  have key := tsum_pi_fin (α := α) s.card fun i a ↦ g (e.symm i).1 a
  have hL : ∑' f : (↥s → α), ∏ w ∈ s.attach, g w.1 (f w)
      = ∑' h : Fin s.card → α, ∏ i, g (e.symm i).1 (h i) := by
    refine Eq.trans (tsum_congr fun f ↦ ?_)
      (Equiv.tsum_eq (Equiv.arrowCongr e (Equiv.refl α))
        fun h : Fin s.card → α ↦ ∏ i, g (e.symm i).1 (h i))
    rw [← Finset.univ_eq_attach]
    exact (Equiv.prod_comp e.symm fun w : ↥s ↦ g w.1 (f w)).symm
  have hR : ∏ i, (∑' a : α, g (e.symm i).1 a) = ∏ w ∈ s, ∑' a : α, g w a := by
    rw [Equiv.prod_comp e.symm fun w : ↥s ↦ ∑' a : α, g w.1 a, Finset.univ_eq_attach,
      Finset.prod_attach s fun w ↦ ∑' a : α, g w a]
  rw [hL, key, hR]

/-! ### The shape field on a finite set of copies -/

/-- A shape field prescribed on a finite set of copies, read as a field on all copies. -/
noncomputable def shapeExt (S : Finset Word) (f : ↥S → Shape) (w : Word) : Shape :=
  if h : w ∈ S then f ⟨w, h⟩ else Shape.ofList []

lemma shapeExt_mem {S : Finset Word} (f : ↥S → Shape) (w : ↥S) :
    shapeExt S f w.1 = f w := by
  rw [shapeExt, dif_pos w.2]

/-- **The shape field on a finite set of copies**: the samples whose shapes at the copies
of `S` are the prescribed ones. -/
def shapeEvent (S : Finset Word) (f : ↥S → Shape) : Set (Amb → ℕ) :=
  {c : Amb → ℕ | ∀ w : ↥S, shapeAt c w.1 = f w}

lemma shapeEvent_eq_iInter (S : Finset Word) (f : ↥S → Shape) :
    shapeEvent S f = ⋂ w ∈ S, {c : Amb → ℕ | shapeAt c w = shapeExt S f w} := by
  ext c
  simp only [shapeEvent, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro h w hw
    have := h ⟨w, hw⟩
    simpa [shapeExt_mem f ⟨w, hw⟩] using this
  · intro h w
    have := h w.1 w.2
    simpa [shapeExt_mem f w] using this

lemma measurableSet_shapeEvent (S : Finset Word) (f : ↥S → Shape) :
    MeasurableSet (shapeEvent S f) := by
  rw [shapeEvent_eq_iInter]
  exact measurableSet_shapes S (shapeExt S f)

/-- **`thm:shape-iid` on a finite set of copies**: the mass of a prescribed shape field
is the product of the masses. -/
lemma survivalMeasure_shapeEvent (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (S : Finset Word)
    (hS : ∀ w ∈ S, ∀ p, p <+: w → p ∈ S) (f : ↥S → Shape) :
    survivalMeasure (N := 2) θ (shapeEvent S f)
      = ∏ w ∈ S.attach, shapeMass θ (f w) := by
  rw [shapeEvent_eq_iInter, survivalMeasure_shapes θ hq hq0 h2 S hS (shapeExt S f),
    ← Finset.prod_attach S fun w ↦ shapeMass θ (shapeExt S f w)]
  exact Finset.prod_congr rfl fun w _ ↦ by rw [shapeExt_mem f w]

/-- The shape field on a finite set of copies exhausts the sample space. -/
lemma iUnion_shapeEvent (S : Finset Word) :
    (⋃ f : ↥S → Shape, shapeEvent S f) = Set.univ := by
  ext c
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨fun w ↦ shapeAt c w.1, fun _ ↦ rfl⟩

/-- Distinct shape fields on a finite set of copies are incompatible. -/
lemma pairwise_shapeEvent (S : Finset Word) :
    Pairwise (Function.onFun Disjoint (shapeEvent S)) := by
  intro f f' hff
  refine Set.disjoint_left.mpr fun c hc hc' ↦ hff ?_
  funext w
  rw [← hc w, ← hc' w]

/-! ### The total mass and the marginal at a copy -/

/-- **`thm:shape-iid`, the total mass**: the shape law is a probability law.  The fibres
of the shape at the root partition the sample space. -/
theorem tsum_shapeMass (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) : ∑' σ : Shape, shapeMass θ σ = 1 := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure θ le_rfl hq
  have hdisj : Pairwise
      (Function.onFun Disjoint fun σ : Shape ↦ {c : Amb → ℕ | shapeAt c [] = σ}) := by
    intro σ τ hst
    exact Set.disjoint_left.mpr fun c hc hc' ↦ hst (hc.symm.trans hc')
  have hcover : (⋃ σ : Shape, {c : Amb → ℕ | shapeAt c [] = σ}) = Set.univ := by
    ext c
    simp
  calc ∑' σ : Shape, shapeMass θ σ
      = ∑' σ : Shape, survivalMeasure (N := 2) θ {c : Amb → ℕ | shapeAt c [] = σ} :=
        tsum_congr fun σ ↦ (survivalMeasure_shapeAt_nil θ hq hq0 h2 σ).symm
    _ = survivalMeasure (N := 2) θ (⋃ σ : Shape, {c : Amb → ℕ | shapeAt c [] = σ}) :=
        (measure_iUnion hdisj fun σ ↦ measurableSet_shapeAt_eq [] σ).symm
    _ = 1 := by rw [hcover]; exact measure_univ

/-! ### The law of a label -/

variable {V : Type*}

/-- **The label law `q` of `thm:shape-coupling` (`it:shape-coupling-law`)**: the
shape law pushed forward along the label map against the uniform variable. -/
noncomputable def labMass (θ : Offspring 2) (ℓ : Shape → ℝ → V) (x : V) : ℝ≥0∞ :=
  ∑' τ : Shape, shapeMass θ τ * (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | ℓ τ u = x}

/-- The label map splits the uniform variable into its fibres. -/
lemma tsum_uniform_fibres [MeasurableSpace V] [Countable V] {ℓ : Shape → ℝ → V}
    (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v}) (τ : Shape) :
    ∑' x : V, (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | ℓ τ u = x} = 1 := by
  have _ := isProbabilityMeasure_uniform_Ico
  have hdisj : Pairwise (Function.onFun Disjoint fun x : V ↦ {u : ℝ | ℓ τ u = x}) := by
    intro x y hxy
    exact Set.disjoint_left.mpr fun u hu hu' ↦ hxy (hu.symm.trans hu')
  have hcover : (⋃ x : V, {u : ℝ | ℓ τ u = x}) = Set.univ := by
    ext u
    simp
  rw [← measure_iUnion hdisj fun x ↦ hℓ τ x, hcover]
  exact measure_univ

/-- **The label law is a probability law**: the shape law is one and the label map splits
the uniform variable. -/
theorem tsum_labMass [MeasurableSpace V] [Countable V] (θ : Offspring 2)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) {ℓ : Shape → ℝ → V}
    (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v}) :
    ∑' x : V, labMass θ ℓ x = 1 := by
  calc ∑' x : V, labMass θ ℓ x
      = ∑' (x : V) (τ : Shape),
          shapeMass θ τ * (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | ℓ τ u = x} := rfl
    _ = ∑' (τ : Shape) (x : V),
          shapeMass θ τ * (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | ℓ τ u = x} :=
        ENNReal.tsum_comm
    _ = ∑' τ : Shape, shapeMass θ τ
          * ∑' x : V, (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | ℓ τ u = x} :=
        tsum_congr fun _ ↦ ENNReal.tsum_mul_left
    _ = ∑' τ : Shape, shapeMass θ τ := by
        exact tsum_congr fun τ ↦ by rw [tsum_uniform_fibres hℓ τ, mul_one]
    _ = 1 := tsum_shapeMass θ hq hq0 h2

/-- **The label law `q`** as a law on the labels. -/
noncomputable def labPMF [MeasurableSpace V] [Countable V] (θ : Offspring 2)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) {ℓ : Shape → ℝ → V}
    (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v}) : PMF V :=
  ⟨labMass θ ℓ, (tsum_labMass θ hq hq0 h2 hℓ) ▸ ENNReal.summable.hasSum⟩

@[simp] lemma labPMF_apply [MeasurableSpace V] [Countable V] (θ : Offspring 2)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) {ℓ : Shape → ℝ → V}
    (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v}) (x : V) :
    labPMF θ hq hq0 h2 hℓ x = labMass θ ℓ x := rfl

/-! ### The product form of the label field -/

/-- **`thm:shape-coupling` (`it:shape-coupling-law`), the product form**: over a
prefix-closed finite set of copies the labels are independent with the law `q`.  The
shapes factorise by `thm:shape-iid` and the uniform variables by independence, and the
two products are exchanged with the sum over the shape fields. -/
theorem hairyMeasure_shapeLab_prod [MeasurableSpace V] (θ : Offspring 2)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) {ℓ : Shape → ℝ → V}
    (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v}) (S : Finset Word)
    (hS : ∀ w ∈ S, ∀ p, p <+: w → p ∈ S) (v : Word → V) :
    hairyMeasure θ (⋂ w ∈ S, {ω : HairySample | shapeLab ℓ ω w = v w})
      = ∏ w ∈ S, labMass θ ℓ (v w) := by
  classical
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure θ le_rfl hq
  set A : (↥S → Shape) → Word → Set ℝ := fun f w ↦ {u : ℝ | ℓ (shapeExt S f w) u = v w}
    with hA
  set B : (↥S → Shape) → Set (Word → ℝ) :=
    fun f ↦ ⋂ w ∈ S, (BranchingProcess.coord w : (Word → ℝ) → ℝ) ⁻¹' A f w with hB
  have hAmeas : ∀ (f : ↥S → Shape) (w : Word), MeasurableSet (A f w) := fun f w ↦ hℓ _ _
  have hBmeas : ∀ f : ↥S → Shape, MeasurableSet (B f) := by
    intro f
    exact MeasurableSet.biInter (Set.to_countable _) fun w _ ↦
      (BranchingProcess.measurable_coord w) (hAmeas f w)
  have hdecomp : (⋂ w ∈ S, {ω : HairySample | shapeLab ℓ ω w = v w})
      = ⋃ f : ↥S → Shape, shapeEvent S f ×ˢ B f := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, hB, hA,
      shapeEvent, Set.mem_preimage, BranchingProcess.coord]
    constructor
    · intro hω
      refine ⟨fun x ↦ shapeAt ω.1 x.1, fun _ ↦ rfl, ?_⟩
      intro w hw
      have hext : shapeExt S (fun x : ↥S ↦ shapeAt ω.1 x.1) w = shapeAt ω.1 w :=
        shapeExt_mem (S := S) (fun x : ↥S ↦ shapeAt ω.1 x.1) ⟨w, hw⟩
      rw [hext]
      exact hω w hw
    · rintro ⟨f, hf, hu⟩ w hw
      have hext : shapeExt S f w = f ⟨w, hw⟩ := shapeExt_mem f ⟨w, hw⟩
      have hmem := hu w hw
      rw [hext] at hmem
      rw [shapeLab, hf ⟨w, hw⟩]
      exact hmem
  have hdisj : Pairwise
      (Function.onFun Disjoint fun f : ↥S → Shape ↦ shapeEvent S f ×ˢ B f) := by
    intro f f' hff
    refine Set.disjoint_left.mpr fun ω hω hω' ↦ ?_
    exact Set.disjoint_left.mp (pairwise_shapeEvent S hff) hω.1 hω'.1
  have hterm : ∀ f : ↥S → Shape, hairyMeasure θ (shapeEvent S f ×ˢ B f)
      = ∏ x ∈ S.attach, shapeMass θ (f x)
          * (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | ℓ (f x) u = v x.1} := by
    intro f
    rw [hairyMeasure, Measure.prod_prod, survivalMeasure_shapeEvent θ hq hq0 h2 S hS f, hB,
      uniField_iInter S (A f) (fun w _ ↦ hAmeas f w), Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.prod_attach S fun w ↦ (volume.restrict (Set.Ico (0 : ℝ) 1)) (A f w)]
    exact Finset.prod_congr rfl fun x _ ↦ by rw [hA]; simp only [shapeExt_mem f x]
  calc hairyMeasure θ (⋂ w ∈ S, {ω : HairySample | shapeLab ℓ ω w = v w})
      = ∑' f : ↥S → Shape, hairyMeasure θ (shapeEvent S f ×ˢ B f) := by
        rw [hdecomp, measure_iUnion hdisj fun f ↦ (measurableSet_shapeEvent S f).prod (hBmeas f)]
    _ = ∑' f : ↥S → Shape, ∏ x ∈ S.attach, shapeMass θ (f x)
          * (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | ℓ (f x) u = v x.1} :=
        tsum_congr hterm
    _ = ∏ w ∈ S, ∑' τ : Shape, shapeMass θ τ
          * (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | ℓ τ u = v w} :=
        tsum_pi_finset S fun w τ ↦
          shapeMass θ τ * (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | ℓ τ u = v w}
    _ = ∏ w ∈ S, labMass θ ℓ (v w) := rfl

/-! ### The net on the shapes as a label graph -/

/-- The index of a shape in the enumeration the net is built on. -/
noncomputable def shapeIdx (σ : Shape) : ℕ :=
  (Equiv.ofBijective shapeEnum ⟨shapeEnum_injective, shapeEnum_surjective⟩).symm σ

@[simp] lemma shapeEnum_shapeIdx (σ : Shape) : shapeEnum (shapeIdx σ) = σ :=
  (Equiv.ofBijective shapeEnum ⟨shapeEnum_injective, shapeEnum_surjective⟩).apply_symm_apply σ

@[simp] lemma shapeFamily_shapeIdx (σ : Shape) : shapeFamily (shapeIdx σ) = shapeSpace σ := by
  rw [shapeFamily, shapeEnum_shapeIdx]

end ChainClasses
