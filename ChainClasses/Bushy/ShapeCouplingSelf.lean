import ChainClasses.Bushy.ShapeLabelLaw
import ChainClasses.Shape.ShapeShrink

/-!
`sec:shape-coupling` and `thm:hairy` of `gw_classes_simple.tex`: the label
graph of `thm:shape-coupling` for one law, and `thm:hairy` over it.

The labels are the shapes themselves, as `thm:shape-coupling` builds them: the label of a
shape is the shape, corrected to the support by the fix of
`thm:shape-shrink` (`it:shape-fix`), which is the identity on the support.  For one
law the coupling of `thm:shape-coupling` (`it:shape-coupling-law`) is the diagonal,
so both label fields carry the same law without further work, and the label of a shape is
comparable to the shape at scale `1`.  The vertices of the graph are therefore shapes and
the edge condition of `def:shape-net` is read between them directly.

`Shape` carries the discrete measurable structure, every set measurable, which is what a
countable label type in `thm:matching` asks for and which the label field of
`thm:hairy` makes unavoidable once the label carries the shape.

* `instMeasurableSpaceShape`, `instMeasurableSingletonClassShape`: the discrete structure
  on the labels.
* `shapeLabel`, `measurableSet_shapeLabel_fibre`: **the label map of
  `thm:shape-coupling`**, the support fix, and its measurable sections.
* `shapeNet`: **the label graph `𝖰`**, distinct shapes linked when they are
  `27D⁴`-comparable both ways, which is the edge condition of `def:shape-net` read on the
  four cross comparisons of one law.
* `markedQI_of_compat_shapeLabel`: **`thm:shape-coupling` (`it:shape-coupling-qi`)**,
  matched labels give comparable shapes, at the scale `729D⁴` that the composition and
  inversion bounds of `thm:shape-net` yield from the three legs `1`, `27D⁴`, `3`.
* `shapePMF`, `bushyMeasure_shapeLabel_prod`: **the label law `q`**, the shape law pushed
  forward along the fix, and its product form.
* `bushy_rate_shape_tree_self`, `bushy_ae_shape_tree_self`: **`thm:hairy` for one law**,
  `eq:hairy-rate` for the samples at the scale `8·729²D⁸`, and the almost sure statement,
  over the potential bound of
  `thm:shape-coupling` (`it:shape-coupling-eta`).
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory GraphMatching
open BranchingProcess (sample survivalMeasure Offspring)
open scoped ENNReal

/-! ### The shapes as labels -/

/-- The labels of `thm:shape-coupling` are the shapes, with the discrete measurable
structure. -/
instance instMeasurableSpaceShape : MeasurableSpace Shape := ⊤

instance instMeasurableSingletonClassShape : MeasurableSingletonClass Shape :=
  ⟨fun _ ↦ trivial⟩

/-- **The label map of `thm:shape-coupling`**: a shape is labelled by itself, corrected to
the support by the fix, which the uniform variable does not enter. -/
def shapeLabel (σ : Shape) (_u : ℝ) : Shape := σ.fix

@[simp] lemma shapeLabel_apply (σ : Shape) (u : ℝ) : shapeLabel σ u = σ.fix := rfl

/-- The sections of the label map are measurable, being trivial. -/
lemma measurableSet_shapeLabel_fibre (τ : Shape) (x : Shape) :
    MeasurableSet {u : ℝ | shapeLabel τ u = x} := by
  by_cases h : τ.fix = x
  · have hset : {u : ℝ | shapeLabel τ u = x} = Set.univ := by
      ext u
      simp [h]
    rw [hset]
    exact MeasurableSet.univ
  · have hset : {u : ℝ | shapeLabel τ u = x} = ∅ := by
      ext u
      simp [h]
    rw [hset]
    exact MeasurableSet.empty

/-- **The label graph `𝖰` of `thm:shape-coupling`**: distinct shapes are linked when they
are comparable at the scale `27D⁴` of `def:shape-net`, in both directions as the four
cross comparisons of the edge condition ask. -/
def shapeNet (Dq : ℝ) : SimpleGraph Shape where
  Adj σ τ := σ ≠ τ ∧ MarkedQI (27 * Dq ^ 4) (shapeSpace σ) (shapeSpace τ)
    ∧ MarkedQI (27 * Dq ^ 4) (shapeSpace τ) (shapeSpace σ)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- **`thm:shape-coupling` (`it:shape-coupling-qi`)**: matched labels give
comparable shapes.  A shape is `1`-comparable to its fix, the two fixes are equal or
linked in the net, and the fix of the second shape is `3`-comparable back to it. -/
theorem markedQI_of_compat_shapeLabel {Dq : ℝ} (hD : 1 ≤ Dq) (τ τ' : Shape) (u u' : ℝ)
    (h : compat (shapeNet Dq) (shapeLabel τ u) (shapeLabel τ' u')) :
    MarkedQI (729 * Dq ^ 4) (shapeSpace τ) (shapeSpace τ') := by
  have hD0 : (0 : ℝ) ≤ Dq := le_trans zero_le_one hD
  have h4 : (1 : ℝ) ≤ Dq ^ 4 := one_le_pow₀ hD
  have h27 : (1 : ℝ) ≤ 27 * Dq ^ 4 := by nlinarith
  have hfix : MarkedQI 1 (shapeSpace τ) (shapeSpace τ.fix) := markedQI_shape_fix τ
  have hfix' : MarkedQI 3 (shapeSpace τ'.fix) (shapeSpace τ') := by
    have h := markedQI_symm (le_refl (1 : ℝ)) (markedQI_shape_fix τ')
    norm_num at h
    exact h
  have hmid : MarkedQI (27 * Dq ^ 4) (shapeSpace τ.fix) (shapeSpace τ'.fix) := by
    rcases h with heq | hadj
    · rw [shapeLabel_apply, shapeLabel_apply] at heq
      rw [heq]
      exact markedQI_id h27 _
    · exact hadj.2.1
  have h12 := markedQI_comp (le_refl (1 : ℝ)) h27 hfix hmid
  have hall := markedQI_comp (by nlinarith) (by norm_num) h12 hfix'
  have hconst : 3 * (3 * 1 * (27 * Dq ^ 4)) * 3 = 729 * Dq ^ 4 := by ring
  rwa [hconst] at hall

/-! ### `thm:hairy` for one law -/

/-- **The label law `q` of `thm:shape-coupling`**: the shape law pushed forward along the
fix. -/
noncomputable def shapePMF (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) : PMF Shape :=
  labPMF θ hq hq0 h2 measurableSet_shapeLabel_fibre

/-- The labels of the copies of a prefix-closed finite set are independent with the law
`q`. -/
lemma bushyMeasure_shapeLabel_prod (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (S : Finset Word)
    (hS : ∀ w ∈ S, ∀ p, p <+: w → p ∈ S) (v : Word → Shape) :
    bushyMeasure θ (⋂ w ∈ S, {ω : BushySample | shapeLab shapeLabel ω w = v w})
      = ∏ w ∈ S, shapePMF θ hq hq0 h2 (v w) :=
  bushyMeasure_shapeLab_prod θ hq hq0 h2 measurableSet_shapeLabel_fibre S hS v

/-- **`eq:hairy-rate`, one law**: the same bound for the two sampled trees, at the scale
`8·729²D⁸`. -/
theorem bushy_rate_shape_tree_self (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) {Dq : ℝ} (hD : 1 ≤ Dq)
    (hη : etaG (shapePMF θ hq hq0 h2) (shapeNet Dq) ≤ 1 / 10000) :
    twoBushyMeasure θ θ
        {ω | ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
          IsSampleQI (8 * 729 ^ 2 * Dq ^ 8) F}
      ≤ 16 * etaG (shapePMF θ hq hq0 h2) (shapeNet Dq) := by
  have hD0 : (0 : ℝ) ≤ Dq := le_trans zero_le_one hD
  have h4 : (1 : ℝ) ≤ Dq ^ 4 := one_le_pow₀ hD
  have hmain := bushy_rate_tree θ θ hq hq h2 h2 (shapePMF θ hq hq0 h2) (shapeNet Dq)
    (K := 729 * Dq ^ 4) (by nlinarith)
    measurableSet_shapeLabel_fibre measurableSet_shapeLabel_fibre
    (bushyMeasure_shapeLabel_prod θ hq hq0 h2) (bushyMeasure_shapeLabel_prod θ hq hq0 h2)
    (markedQI_of_compat_shapeLabel hD) hη
  have hconst : 8 * (729 * Dq ^ 4) ^ 2 = 8 * 729 ^ 2 * Dq ^ 8 := by ring
  rwa [hconst] at hmain

/-- **The almost sure statement of `thm:hairy`, one law**: if the net can be taken at
scales whose potential is arbitrarily small, then almost surely the two sampled trees are
quasi-isometric. -/
theorem bushy_ae_shape_tree_self (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2)
    (hscale : ∀ ε : ℝ≥0∞, 0 < ε → ∃ Dq : ℝ, ∃ _ : 1 ≤ Dq,
      etaG (shapePMF θ hq hq0 h2) (shapeNet Dq) ≤ 1 / 10000 ∧
        16 * etaG (shapePMF θ hq hq0 h2) (shapeNet Dq) ≤ ε) :
    twoBushyMeasure θ θ
      {ω | ¬ ∃ (L : ℝ) (F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1}),
        IsSampleQI L F} = 0 := by
  refine bushy_ae_tree θ θ fun ε hε ↦ ?_
  obtain ⟨Dq, hD, hη, hsmall⟩ := hscale ε hε
  exact ⟨8 * 729 ^ 2 * Dq ^ 8,
    le_trans (bushy_rate_shape_tree_self θ hq hq0 h2 hD hη) hsmall⟩

end ChainClasses
