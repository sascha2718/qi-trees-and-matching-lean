/-
`sec:shape-harris` of `matching_classes_simple.tex` and `sec:hairy-universality` of
`gw_classes_simple.tex`: the shape law is a probability law, the label law it pushes
forward along a label map, the product form of the label field that `thm:hairy`
consumes, and the net on the shapes as the label graph of `thm:shape-coupling`.

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
sections, and a third for the labels given by the net: matched classes give comparable
shapes.  The potential bound and the coupling of the second law to the first remain
hypotheses.

* `tsum_pi_fin`, `tsum_pi_finset`: summing a product of weights over all functions on a
  finite index multiplies the sums, the exchange the factorisations below are read
  through.
* `shapeExt`, `shapeEvent`, `shapeEvent_eq_iInter`, `survivalMeasure_shapeEvent`,
  `iUnion_shapeEvent`, `pairwise_shapeEvent`: the shape field read on a finite set of
  copies, its mass, and the partition of the sample space by it.
* `tsum_shapeMass`: **`thm:shape-iid`, the total mass**, the shape law is a probability
  law; `shapeMassPMF` packages it.
* `survivalMeasure_shapeAt`: **`thm:shape-iid`, the marginal**, the shape at any copy
  has the law `μ`.
* `labMass`, `tsum_uniform_fibres`, `tsum_labMass`, `labPMF`: **the label law `q` of
  `thm:shape-coupling`\labelcref{it:shape-coupling-law}**, the shape law pushed forward
  along a label map against the uniform variable, and its total mass.
* `hairyMeasure_shapeLab_prod`: **`thm:shape-coupling`\labelcref{it:shape-coupling-law},
  the product form**, the labels of a prefix-closed finite set of copies are independent
  with the law `q`; `hairyMeasure_shapeLab` is the marginal at one copy.
* `shapeIdx`, `netGraph`, `netLab`, `measurableSet_netLab_fibre`, `IsNetLabel`,
  `isNetLabel_netLab`: **the label graph `𝖰`**, the net on the shapes, the class map that
  labels a shape by its representative, and the label maps into the net.
* `markedQI_of_compat`: **`thm:shape-coupling`\labelcref{it:shape-coupling-qi}**, matched
  labels give comparable shapes, at the scale `59049D¹¹` that the composition of the three
  comparisons produces.
* `netPMF`, `hairyMeasure_netLab_prod`, `hairyMeasure_coupled_prod`, `hairy_rate_net`,
  `hairy_rate_net_tree`, `hairy_rate_net_tree_self`, `hairy_ae_net_tree`: **`thm:hairy`
  over the net**, `eq:hairy-rate` for the assemblies and for the samples, the one-law
  case where the class map is its own coupling, and the almost sure statement.
-/
import ChainClasses.HairyUniversality

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

/-- **The shape law `μ` of `thm:shape-iid`** as a law on the shapes. -/
noncomputable def shapeMassPMF (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) : PMF Shape :=
  ⟨shapeMass θ, (tsum_shapeMass θ hq hq0 h2) ▸ ENNReal.summable.hasSum⟩

@[simp] lemma shapeMassPMF_apply (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (σ : Shape) :
    shapeMassPMF θ hq hq0 h2 σ = shapeMass θ σ := rfl

/-- The prefixes of a copy, a prefix-closed finite set of copies containing it. -/
def prefixSet (w : Word) : Finset Word := w.inits.toFinset

@[simp] lemma mem_prefixSet {v w : Word} : v ∈ prefixSet w ↔ v <+: w := by
  simp [prefixSet, List.mem_inits]

lemma self_mem_prefixSet (w : Word) : w ∈ prefixSet w := by simp

lemma prefixClosed_prefixSet (w : Word) :
    ∀ v ∈ prefixSet w, ∀ p, p <+: v → p ∈ prefixSet w := by
  intro v hv p hp
  rw [mem_prefixSet] at hv ⊢
  exact hp.trans hv

/-- **`thm:shape-iid`, the marginal**: conditioned on survival the shape at any copy has
the law `μ`.  The copies of a prefix-closed set carrying the other shapes are summed out
against the total mass. -/
theorem survivalMeasure_shapeAt (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (w : Word) (σ : Shape) :
    survivalMeasure (N := 2) θ {c : Amb → ℕ | shapeAt c w = σ} = shapeMass θ σ := by
  classical
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure θ le_rfl hq
  set S : Finset Word := prefixSet w with hSdef
  have hw : w ∈ S := self_mem_prefixSet w
  set E : Set (Amb → ℕ) := {c : Amb → ℕ | shapeAt c w = σ} with hE
  have hEmeas : MeasurableSet E := measurableSet_shapeAt_eq w σ
  set g : Word → Shape → ℝ≥0∞ :=
    fun x τ ↦ if x = w then (if τ = σ then shapeMass θ τ else 0) else shapeMass θ τ with hg
  have hterm : ∀ f : ↥S → Shape,
      survivalMeasure (N := 2) θ (shapeEvent S f ∩ E) = ∏ x ∈ S.attach, g x.1 (f x) := by
    intro f
    by_cases hfw : f ⟨w, hw⟩ = σ
    · have hsub : shapeEvent S f ∩ E = shapeEvent S f := by
        refine Set.inter_eq_left.mpr fun c hc ↦ ?_
        have hcw := hc ⟨w, hw⟩
        rw [hE, Set.mem_setOf_eq, hcw, hfw]
      rw [hsub, survivalMeasure_shapeEvent θ hq hq0 h2 S (prefixClosed_prefixSet w) f]
      refine Finset.prod_congr rfl fun x _ ↦ ?_
      by_cases hx : x.1 = w
      · have hfx : f x = σ := by
          rw [show x = (⟨w, hw⟩ : ↥S) from Subtype.ext hx]
          exact hfw
        simp only [hg, if_pos hx, if_pos hfx]
      · simp only [hg, if_neg hx]
    · have hempty : shapeEvent S f ∩ E = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun c hc ↦ hfw ?_
        rw [← hc.1 ⟨w, hw⟩]
        exact hc.2
      rw [hempty, measure_empty]
      refine (Finset.prod_eq_zero (Finset.mem_attach S ⟨w, hw⟩) ?_).symm
      simp only [hg, if_pos rfl, if_neg hfw]
  have hdisj : Pairwise (Function.onFun Disjoint fun f : ↥S → Shape ↦ shapeEvent S f ∩ E) :=
    fun f f' hff ↦ Disjoint.mono Set.inter_subset_left Set.inter_subset_left
      (pairwise_shapeEvent S hff)
  calc survivalMeasure (N := 2) θ E
      = survivalMeasure (N := 2) θ (⋃ f : ↥S → Shape, shapeEvent S f ∩ E) := by
        rw [← Set.iUnion_inter, iUnion_shapeEvent, Set.univ_inter]
    _ = ∑' f : ↥S → Shape, survivalMeasure (N := 2) θ (shapeEvent S f ∩ E) :=
        measure_iUnion hdisj fun f ↦ (measurableSet_shapeEvent S f).inter hEmeas
    _ = ∑' f : ↥S → Shape, ∏ x ∈ S.attach, g x.1 (f x) := tsum_congr hterm
    _ = ∏ x ∈ S, ∑' τ : Shape, g x τ := tsum_pi_finset S g
    _ = shapeMass θ σ := by
        rw [Finset.prod_eq_single_of_mem w hw ?_]
        · refine Eq.trans (tsum_eq_single σ fun τ hτ ↦ ?_) ?_
          · simp only [hg, if_pos rfl, if_neg hτ]
          · simp [hg]
        · intro x _ hxw
          simp only [hg, if_neg hxw]
          exact tsum_shapeMass θ hq hq0 h2

/-! ### The law of a label -/

variable {V : Type*}

/-- **The label law `q` of `thm:shape-coupling`\labelcref{it:shape-coupling-law}**: the
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

/-- **`thm:shape-coupling`\labelcref{it:shape-coupling-law}, the product form**: over a
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

/-- **The marginal of a label**: at every copy the label has the law `q`. -/
theorem hairyMeasure_shapeLab [MeasurableSpace V] (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) {ℓ : Shape → ℝ → V}
    (hℓ : ∀ (τ : Shape) (v : V), MeasurableSet {u : ℝ | ℓ τ u = v}) (w : Word) (x : V) :
    hairyMeasure θ {ω : HairySample | shapeLab ℓ ω w = x} = labMass θ ℓ x := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure θ le_rfl hq
  have hset : {ω : HairySample | shapeLab ℓ ω w = x}
      = ⋃ τ : Shape, {c : Amb → ℕ | shapeAt c w = τ}
          ×ˢ ((BranchingProcess.coord w : (Word → ℝ) → ℝ) ⁻¹' {u : ℝ | ℓ τ u = x}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_preimage,
      BranchingProcess.coord, shapeLab]
    constructor
    · intro h
      exact ⟨shapeAt ω.1 w, rfl, h⟩
    · rintro ⟨τ, h1, h2'⟩
      have hτ : shapeAt ω.1 w = τ := h1
      rw [hτ]
      exact h2'
  have hdisj : Pairwise (Function.onFun Disjoint fun τ : Shape ↦
      {c : Amb → ℕ | shapeAt c w = τ}
        ×ˢ ((BranchingProcess.coord w : (Word → ℝ) → ℝ) ⁻¹' {u : ℝ | ℓ τ u = x})) := by
    intro τ τ' hττ
    refine Set.disjoint_left.mpr fun ω hω hω' ↦ hττ ?_
    exact (hω.1).symm.trans hω'.1
  have hcoord : ∀ τ : Shape,
      uniField ((BranchingProcess.coord w : (Word → ℝ) → ℝ) ⁻¹' {u : ℝ | ℓ τ u = x})
        = (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | ℓ τ u = x} := by
    intro τ
    have h := uniField_iInter {w} (fun _ ↦ {u : ℝ | ℓ τ u = x}) (fun _ _ ↦ hℓ τ x)
    simpa using h
  rw [hset, measure_iUnion hdisj fun τ ↦
    (measurableSet_shapeAt_eq w τ).prod ((BranchingProcess.measurable_coord w) (hℓ τ x))]
  refine tsum_congr fun τ ↦ ?_
  rw [hairyMeasure, Measure.prod_prod, survivalMeasure_shapeAt θ hq hq0 h2 w τ, hcoord τ]

/-! ### The net on the shapes as a label graph -/

/-- The index of a shape in the enumeration the net is built on. -/
noncomputable def shapeIdx (σ : Shape) : ℕ :=
  (Equiv.ofBijective shapeEnum ⟨shapeEnum_injective, shapeEnum_surjective⟩).symm σ

@[simp] lemma shapeEnum_shapeIdx (σ : Shape) : shapeEnum (shapeIdx σ) = σ :=
  (Equiv.ofBijective shapeEnum ⟨shapeEnum_injective, shapeEnum_surjective⟩).apply_symm_apply σ

@[simp] lemma shapeFamily_shapeIdx (σ : Shape) : shapeFamily (shapeIdx σ) = shapeSpace σ := by
  rw [shapeFamily, shapeEnum_shapeIdx]

/-- **The label graph `𝖰` of `thm:shape-coupling`**: the net on the shapes, two classes
linked when they are `27D⁴`-comparable. -/
def netGraph (Dq : ℝ) : SimpleGraph ℕ := SimpleGraph.fromRel (NetAdj shapeFamily Dq)

/-- **The label map of the first law of `thm:shape-coupling`**: the class of the shape in
the net, which the uniform variable does not enter. -/
noncomputable def netLab (Dq : ℝ) (σ : Shape) (_u : ℝ) : ℕ :=
  repIdx shapeFamily Dq (shapeIdx σ)

/-- The sections of the class map are measurable, being trivial. -/
lemma measurableSet_netLab_fibre (Dq : ℝ) (τ : Shape) (x : ℕ) :
    MeasurableSet {u : ℝ | netLab Dq τ u = x} := by
  by_cases h : repIdx shapeFamily Dq (shapeIdx τ) = x
  · have hset : {u : ℝ | netLab Dq τ u = x} = Set.univ := by
      ext u
      simp [netLab, h]
    rw [hset]
    exact MeasurableSet.univ
  · have hset : {u : ℝ | netLab Dq τ u = x} = ∅ := by
      ext u
      simp [netLab, h]
    rw [hset]
    exact MeasurableSet.empty

/-- **A label map into the net**: a measurable map sending a shape to a class the shape
is `D`-comparable to.  The class map of one law is one, and
`thm:shape-coupling` asks the coupled map of the other law to be another. -/
structure IsNetLabel (Dq : ℝ) (ℓ : Shape → ℝ → ℕ) : Prop where
  /-- The sections of the label map are measurable. -/
  meas : ∀ (τ : Shape) (x : ℕ), MeasurableSet {u : ℝ | ℓ τ u = x}
  /-- A shape is comparable to the class it is labelled by. -/
  qi : ∀ (τ : Shape) (u : ℝ), MarkedQI Dq (shapeSpace τ) (shapeFamily (ℓ τ u))

/-- The class map is a label map into the net. -/
lemma isNetLabel_netLab {Dq : ℝ} (hD : 1 ≤ Dq) : IsNetLabel Dq (netLab Dq) where
  meas := measurableSet_netLab_fibre Dq
  qi := by
    intro τ u
    have h := markedQI_repIdx shapeFamily Dq hD (shapeIdx τ)
    rwa [shapeFamily_shapeIdx] at h

/-- **`thm:shape-coupling`\labelcref{it:shape-coupling-qi}**: matched labels give
comparable shapes.  Each shape is comparable to its class, the two classes are linked in
the net, and the three comparisons compose. -/
theorem markedQI_of_compat {Dq : ℝ} (hD : 1 ≤ Dq) {ℓ ℓ' : Shape → ℝ → ℕ}
    (hℓ : IsNetLabel Dq ℓ) (hℓ' : IsNetLabel Dq ℓ') (τ τ' : Shape) (u u' : ℝ)
    (h : compat (netGraph Dq) (ℓ τ u) (ℓ' τ' u')) :
    MarkedQI (59049 * Dq ^ 11) (shapeSpace τ) (shapeSpace τ') := by
  have hD0 : (0 : ℝ) ≤ Dq := le_trans zero_le_one hD
  have h4 : (1 : ℝ) ≤ Dq ^ 4 := one_le_pow₀ hD
  have h27 : (1 : ℝ) ≤ 27 * Dq ^ 4 := by nlinarith
  have hsq : (1 : ℝ) ≤ 3 * (27 * Dq ^ 4) ^ 2 := by nlinarith
  have hmid : MarkedQI (3 * (27 * Dq ^ 4) ^ 2)
      (shapeFamily (ℓ τ u)) (shapeFamily (ℓ' τ' u')) := by
    rcases h with heq | hadj
    · rw [heq]
      exact markedQI_id hsq _
    · rw [netGraph, SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with hab | hba
      · exact hab.2.2.2.mono (by linarith) (by nlinarith)
      · exact markedQI_symm h27 hba.2.2.2
  have h1 : MarkedQI Dq (shapeSpace τ) (shapeFamily (ℓ τ u)) := hℓ.qi τ u
  have h3 : MarkedQI (3 * Dq ^ 2) (shapeFamily (ℓ' τ' u')) (shapeSpace τ') :=
    markedQI_symm hD (hℓ'.qi τ' u')
  have h12 := markedQI_comp hD hsq h1 hmid
  have hall := markedQI_comp (by nlinarith) (by nlinarith) h12 h3
  have hconst : 3 * (3 * Dq * (3 * (27 * Dq ^ 4) ^ 2)) * (3 * Dq ^ 2) = 59049 * Dq ^ 11 := by
    ring
  rwa [hconst] at hall

/-! ### `thm:hairy` over the net -/

/-- **The label law `q` of `thm:shape-coupling`**: the shape law read through the class
map of the net. -/
noncomputable def netPMF (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) (Dq : ℝ) : PMF ℕ :=
  labPMF θ hq hq0 h2 (measurableSet_netLab_fibre Dq)

/-- The classes of the copies of a prefix-closed finite set are independent with the law
`q`. -/
lemma hairyMeasure_netLab_prod (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (Dq : ℝ) (S : Finset Word)
    (hS : ∀ w ∈ S, ∀ p, p <+: w → p ∈ S) (v : Word → ℕ) :
    hairyMeasure θ (⋂ w ∈ S, {ω : HairySample | shapeLab (netLab Dq) ω w = v w})
      = ∏ w ∈ S, netPMF θ hq hq0 h2 Dq (v w) :=
  hairyMeasure_shapeLab_prod θ hq hq0 h2 (measurableSet_netLab_fibre Dq) S hS v

/-- A coupled label map of the second law carries the same product law. -/
lemma hairyMeasure_coupled_prod (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) {Dq : ℝ} {ℓ' : Shape → ℝ → ℕ}
    (hℓ' : IsNetLabel Dq ℓ') (hlaw : ∀ x : ℕ, labMass θ' ℓ' x = labMass θ (netLab Dq) x)
    (S : Finset Word) (hS : ∀ w ∈ S, ∀ p, p <+: w → p ∈ S) (v : Word → ℕ) :
    hairyMeasure θ' (⋂ w ∈ S, {ω : HairySample | shapeLab ℓ' ω w = v w})
      = ∏ w ∈ S, netPMF θ hq hq0 h2 Dq (v w) := by
  rw [hairyMeasure_shapeLab_prod θ' hq' hq0' h2' hℓ'.meas S hS v]
  exact Finset.prod_congr rfl fun w _ ↦ hlaw (v w)

/-- **`eq:hairy-rate` for the assemblies**: with the classes of the net as labels and a
coupled label map for the second law, the failure probability of the quasi-isometry
between the two assemblies is bounded by the potential of the label law. -/
theorem hairy_rate_net (θ θ' : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) (hq' : θ'.extinction < 1) (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2)
    {Dq : ℝ} (hD : 1 ≤ Dq) {ℓ' : Shape → ℝ → ℕ} (hℓ' : IsNetLabel Dq ℓ')
    (hlaw : ∀ x : ℕ, labMass θ' ℓ' x = labMass θ (netLab Dq) x)
    (hη : etaG (netPMF θ hq hq0 h2 Dq) (netGraph Dq) ≤ 1 / 10000) :
    twoHairyMeasure θ θ'
        {ω | ¬ ∃ f : Assembly (shapeAt ω.1.1) → Assembly (shapeAt ω.2.1),
          IsQIMap (8 * (59049 * Dq ^ 11) ^ 2) f}
      ≤ 16 * etaG (netPMF θ hq hq0 h2 Dq) (netGraph Dq) := by
  have hD0 : (0 : ℝ) ≤ Dq := le_trans zero_le_one hD
  have h11 : (1 : ℝ) ≤ Dq ^ 11 := one_le_pow₀ hD
  exact hairy_rate θ θ' hq hq' (netPMF θ hq hq0 h2 Dq) (netGraph Dq) (by nlinarith)
    (measurableSet_netLab_fibre Dq) hℓ'.meas
    (hairyMeasure_netLab_prod θ hq hq0 h2 Dq)
    (hairyMeasure_coupled_prod θ θ' hq hq0 h2 hq' hq0' h2' hℓ' hlaw)
    (markedQI_of_compat hD (isNetLabel_netLab hD) hℓ') hη

/-- **`eq:hairy-rate`**: the same bound for the two sampled trees. -/
theorem hairy_rate_net_tree (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) {Dq : ℝ} (hD : 1 ≤ Dq)
    {ℓ' : Shape → ℝ → ℕ} (hℓ' : IsNetLabel Dq ℓ')
    (hlaw : ∀ x : ℕ, labMass θ' ℓ' x = labMass θ (netLab Dq) x)
    (hη : etaG (netPMF θ hq hq0 h2 Dq) (netGraph Dq) ≤ 1 / 10000) :
    twoHairyMeasure θ θ'
        {ω | ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
          IsSampleQI (8 * (59049 * Dq ^ 11) ^ 2) F}
      ≤ 16 * etaG (netPMF θ hq hq0 h2 Dq) (netGraph Dq) := by
  have hD0 : (0 : ℝ) ≤ Dq := le_trans zero_le_one hD
  have h11 : (1 : ℝ) ≤ Dq ^ 11 := one_le_pow₀ hD
  exact hairy_rate_tree θ θ' hq hq' h2 h2' (netPMF θ hq hq0 h2 Dq) (netGraph Dq)
    (by nlinarith) (measurableSet_netLab_fibre Dq) hℓ'.meas
    (hairyMeasure_netLab_prod θ hq hq0 h2 Dq)
    (hairyMeasure_coupled_prod θ θ' hq hq0 h2 hq' hq0' h2' hℓ' hlaw)
    (markedQI_of_compat hD (isNetLabel_netLab hD) hℓ') hη

/-- **`eq:hairy-rate` for one law**: two independent samples of the same offspring law,
where the class map of the net is its own coupling. -/
theorem hairy_rate_net_tree_self (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) {Dq : ℝ} (hD : 1 ≤ Dq)
    (hη : etaG (netPMF θ hq hq0 h2 Dq) (netGraph Dq) ≤ 1 / 10000) :
    twoHairyMeasure θ θ
        {ω | ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
          IsSampleQI (8 * (59049 * Dq ^ 11) ^ 2) F}
      ≤ 16 * etaG (netPMF θ hq hq0 h2 Dq) (netGraph Dq) :=
  hairy_rate_net_tree θ θ hq hq0 h2 hq hq0 h2 hD (isNetLabel_netLab hD) (fun _ ↦ rfl) hη

/-- **The almost sure statement of `thm:hairy`**: if the net can be taken at scales whose
potential is arbitrarily small, then almost surely the two sampled trees are
quasi-isometric. -/
theorem hairy_ae_net_tree (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2)
    (hscale : ∀ ε : ℝ≥0∞, 0 < ε → ∃ Dq : ℝ, ∃ _ : 1 ≤ Dq, ∃ ℓ' : Shape → ℝ → ℕ,
      ∃ _ : IsNetLabel Dq ℓ', (∀ x : ℕ, labMass θ' ℓ' x = labMass θ (netLab Dq) x) ∧
        etaG (netPMF θ hq hq0 h2 Dq) (netGraph Dq) ≤ 1 / 10000 ∧
        16 * etaG (netPMF θ hq hq0 h2 Dq) (netGraph Dq) ≤ ε) :
    twoHairyMeasure θ θ'
      {ω | ¬ ∃ (L : ℝ) (F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1}),
        IsSampleQI L F} = 0 := by
  refine hairy_ae_tree θ θ' fun ε hε ↦ ?_
  obtain ⟨Dq, hD, ℓ', hℓ', hlaw, hη, hsmall⟩ := hscale ε hε
  exact ⟨8 * (59049 * Dq ^ 11) ^ 2,
    le_trans (hairy_rate_net_tree θ θ' hq hq0 h2 hq' hq0' h2' hD hℓ' hlaw hη) hsmall⟩

end ChainClasses
