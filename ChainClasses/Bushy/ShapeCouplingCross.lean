import ChainClasses.Bushy.ShapeEtaSelf

/-!
`sec:shape-coupling` and the bushy-universality proposition labelled
`thm:hairy` in `gw_classes_simple.tex`: the label graph of
`thm:shape-coupling` across two laws, and bushy universality over it.

The labels are the pairs of a coupling `π` of the two shape laws, as `thm:shape-coupling`
builds them: a shape of the first law is labelled by the pair consisting of its support fix
and a partner drawn from the conditional law of `π` given that fix, a shape of the second
law by the mirror pair, and the label graph joins two positive-mass pairs when all four
cross comparisons hold.  Both label fields then have law `π`.  In declaration names,
`charged` abbreviates "has nonzero mass under `π`".

The coupling itself enters as the hypothesis `IsShapeCoupling`: its two marginals are the
two shape laws and it gives positive mass only to `9D³`-comparable pairs.  Everything the
bushy-universality proposition `thm:hairy` asks for is read off it here.  The potential is
not estimated again: a positive-mass pair sees, in the label graph, every positive-mass
pair whose first component is a neighbour of its
own in `def:shape-net`, so the ball of a pair is at least as heavy as the ball of its first
component and `eq:shape-eta` for the first law alone bounds the potential of `π`.  The
scale of the label graph pays for that comparison: the cross comparison of two charged
pairs composes an edge of `def:shape-net` at `27D⁴` with the comparability `9D³` of a
charged pair, so the edge scale is `729D⁷`, matched labels give a `19683D⁷`-marked
quasi-isometry of the two shapes, and the gluing is an `8·19683²D¹⁴`-quasi-isometry.

* `slotW`, `drawW`: **the conditional draw**, the splitting of `[0,1)` into intervals of
  the conditional masses along the enumeration of the shapes, with its measurable sections
  `measurableSet_fibre_drawW` and its law `volume_fibre_drawW`.
* `margFst`, `margSnd`, `IsShapeCoupling`: **the coupling of `thm:shape-coupling`**, its
  two marginals and the comparability of the pairs it charges.
* `pairNet`: **the label graph `𝖰`**, distinct charged pairs linked when the four cross
  comparisons hold at `729D⁷`, and everything linked to a pair the coupling does not
  charge, which no label ever takes.
* `pairLab`, `pairLab'`: **the two label maps**, with `labMass_pairLab` and
  `labMass_pairLab'` **`thm:shape-coupling` (`it:shape-coupling-law`)**, their
  common law `π`, and `bushyMeasure_pairLab_prod`, `bushyMeasure_pairLab'_prod` its product
  form.
* `markedQI_of_compat_pairLab`: **`thm:shape-coupling` (`it:shape-coupling-qi`)**,
  matched labels give comparable shapes at the scale `19683D⁷`.
* `etaG_le_of_proj`, `gdeg_shapeNet_le_gdeg_pairNet`, `etaG_pairNet_le`:
  **`thm:shape-coupling` (`it:shape-coupling-eta`)**, the ball of a pair contains the
  ball of its first component and the fibres of the first projection carry the first
  marginal, so the potential of `π` is at most the potential of the first shape law over
  `def:shape-net`.
* `bushy_rate_shape_tree_cross`: **`thm:hairy` across two laws**, `eq:hairy-rate` at the
  scale `8·19683²D¹⁴`.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory GraphMatching
open BranchingProcess (sample survivalMeasure Offspring)
open scoped ENNReal Classical

/-! ### The enumeration of the shapes -/

/-- The enumeration transports a sum over the shapes to a sum over the indices. -/
lemma tsum_shapeEnum (w : Shape → ℝ≥0∞) : ∑' i : ℕ, w (shapeEnum i) = ∑' b : Shape, w b :=
  (Equiv.ofBijective shapeEnum ⟨shapeEnum_injective, shapeEnum_surjective⟩).tsum_eq w

/-! ### Splitting the uniform variable along a weight family -/

/-- The cumulative weight of the first `n` shapes in the enumeration. -/
noncomputable def cumW (w : Shape → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range n, w (shapeEnum i)

lemma cumW_succ (w : Shape → ℝ≥0∞) (n : ℕ) :
    cumW w (n + 1) = cumW w n + w (shapeEnum n) := Finset.sum_range_succ _ n

lemma cumW_mono (w : Shape → ℝ≥0∞) : Monotone (cumW w) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hmn)

lemma cumW_le_tsum (w : Shape → ℝ≥0∞) (n : ℕ) : cumW w n ≤ ∑' b : Shape, w b := by
  rw [← tsum_shapeEnum w]
  exact ENNReal.sum_le_tsum (Finset.range n)

lemma cumW_le_one {w : Shape → ℝ≥0∞} (hw : ∑' b : Shape, w b = 1) (n : ℕ) :
    cumW w n ≤ 1 := hw ▸ cumW_le_tsum w n

lemma cumW_ne_top {w : Shape → ℝ≥0∞} (hw : ∑' b : Shape, w b = 1) (n : ℕ) :
    cumW w n ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (cumW_le_one hw n)

/-- **The slot of a shape**: the interval of `[0,1)` of length `w b` allotted to it. -/
noncomputable def slotW (w : Shape → ℝ≥0∞) (b : Shape) : Set ℝ :=
  Set.Ico (cumW w (shapeIdx b)).toReal (cumW w (shapeIdx b + 1)).toReal

lemma measurableSet_slotW (w : Shape → ℝ≥0∞) (b : Shape) : MeasurableSet (slotW w b) :=
  measurableSet_Ico

lemma slotW_subset {w : Shape → ℝ≥0∞} (hw : ∑' b : Shape, w b = 1) (b : Shape) :
    slotW w b ⊆ Set.Ico (0 : ℝ) 1 := by
  intro u hu
  obtain ⟨h1, h2⟩ := hu
  have h0 : (0 : ℝ) ≤ (cumW w (shapeIdx b)).toReal := ENNReal.toReal_nonneg
  have h1' : (cumW w (shapeIdx b + 1)).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (cumW_le_one hw (shapeIdx b + 1))
    simpa using this
  exact ⟨by linarith, by linarith⟩

/-- The slot of a shape has the mass the family gives it. -/
lemma volume_slotW {w : Shape → ℝ≥0∞} (hw : ∑' b : Shape, w b = 1) (b : Shape) :
    volume (slotW w b) = w b := by
  have hwb : w b ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← hw]
    exact ENNReal.le_tsum b
  have hsucc : cumW w (shapeIdx b + 1) = cumW w (shapeIdx b) + w b := by
    rw [cumW_succ, shapeEnum_shapeIdx]
  have hdiff : (cumW w (shapeIdx b + 1)).toReal - (cumW w (shapeIdx b)).toReal
      = (w b).toReal := by
    rw [hsucc, ENNReal.toReal_add (cumW_ne_top hw _) hwb]
    ring
  rw [slotW, Real.volume_Ico, hdiff, ENNReal.ofReal_toReal hwb]

/-- Distinct shapes have disjoint slots. -/
lemma slotW_disjoint {w : Shape → ℝ≥0∞} (hw : ∑' b : Shape, w b = 1) {b b' : Shape}
    (hbb : b ≠ b') {u : ℝ} (hu : u ∈ slotW w b) (hu' : u ∈ slotW w b') : False := by
  have hidx : shapeIdx b ≠ shapeIdx b' := by
    intro h
    exact hbb (by rw [← shapeEnum_shapeIdx b, ← shapeEnum_shapeIdx b', h])
  have key : ∀ i j : ℕ, i < j → u ∈ Set.Ico (cumW w i).toReal (cumW w (i + 1)).toReal →
      u ∈ Set.Ico (cumW w j).toReal (cumW w (j + 1)).toReal → False := by
    intro i j hij h1 h2
    have hmono : (cumW w (i + 1)).toReal ≤ (cumW w j).toReal :=
      ENNReal.toReal_mono (cumW_ne_top hw j) (cumW_mono w hij)
    exact absurd h1.2 (not_lt.mpr (le_trans hmono h2.1))
  rcases lt_or_gt_of_ne hidx with h | h
  · exact key _ _ h hu hu'
  · exact key _ _ h hu' hu

/-- **The conditional draw**: the shape whose slot contains the uniform variable, and a
default shape outside the slots. -/
noncomputable def drawW (w : Shape → ℝ≥0∞) (dflt : Shape) (u : ℝ) : Shape :=
  if h : ∃ b : Shape, u ∈ slotW w b then h.choose else dflt

lemma drawW_of_mem {w : Shape → ℝ≥0∞} (hw : ∑' b : Shape, w b = 1) (dflt : Shape)
    {u : ℝ} {b : Shape} (hu : u ∈ slotW w b) : drawW w dflt u = b := by
  have hex : ∃ b : Shape, u ∈ slotW w b := ⟨b, hu⟩
  rw [drawW, dite_eq_left hex]
  by_contra hne
  exact slotW_disjoint hw hne hex.choose_spec hu

lemma drawW_of_not_mem {w : Shape → ℝ≥0∞} (dflt : Shape) {u : ℝ}
    (hu : ¬ ∃ b : Shape, u ∈ slotW w b) : drawW w dflt u = dflt := by
  rw [drawW, dite_eq_right hu]

/-- Off the default the fibre of the draw is exactly the slot. -/
lemma fibre_drawW_of_ne {w : Shape → ℝ≥0∞} (hw : ∑' b : Shape, w b = 1) {dflt b : Shape}
    (hb : b ≠ dflt) : {u : ℝ | drawW w dflt u = b} = slotW w b := by
  ext u
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    by_cases hex : ∃ b' : Shape, u ∈ slotW w b'
    · rw [drawW_of_mem hw dflt hex.choose_spec] at h
      rw [← h]
      exact hex.choose_spec
    · rw [drawW_of_not_mem dflt hex] at h
      exact absurd h.symm hb
  · intro h
    exact drawW_of_mem hw dflt h

/-- At the default the fibre of the draw is the slot together with the leftover. -/
lemma fibre_drawW_dflt {w : Shape → ℝ≥0∞} (hw : ∑' b : Shape, w b = 1) (dflt : Shape) :
    {u : ℝ | drawW w dflt u = dflt} = slotW w dflt ∪ (⋃ b : Shape, slotW w b)ᶜ := by
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
  constructor
  · intro h
    by_cases hex : ∃ b' : Shape, u ∈ slotW w b'
    · rw [drawW_of_mem hw dflt hex.choose_spec] at h
      exact Or.inl (h ▸ hex.choose_spec)
    · exact Or.inr fun b hb => hex ⟨b, hb⟩
  · rintro (h | h)
    · exact drawW_of_mem hw dflt h
    · exact drawW_of_not_mem dflt fun ⟨b, hb⟩ => h b hb

lemma measurableSet_fibre_drawW {w : Shape → ℝ≥0∞} (hw : ∑' b : Shape, w b = 1)
    (dflt b : Shape) : MeasurableSet {u : ℝ | drawW w dflt u = b} := by
  by_cases hb : b = dflt
  · subst hb
    rw [fibre_drawW_dflt hw b]
    exact (measurableSet_slotW w b).union
      (MeasurableSet.compl (MeasurableSet.iUnion fun b' => measurableSet_slotW w b'))
  · rw [fibre_drawW_of_ne hw hb]
    exact measurableSet_slotW w b

/-- The slots fill `[0,1)` up to a null set. -/
lemma volume_compl_iUnion_slotW {w : Shape → ℝ≥0∞} (hw : ∑' b : Shape, w b = 1) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) (⋃ b : Shape, slotW w b)ᶜ = 0 := by
  have _ := isProbabilityMeasure_uniform_Ico
  have hdisj : Pairwise (Function.onFun Disjoint (slotW w)) := by
    intro b b' hbb
    exact Set.disjoint_left.mpr fun u hu hu' => slotW_disjoint hw hbb hu hu'
  have hmeas : MeasurableSet (⋃ b : Shape, slotW w b) :=
    MeasurableSet.iUnion fun b => measurableSet_slotW w b
  have hfull : (volume.restrict (Set.Ico (0 : ℝ) 1)) (⋃ b : Shape, slotW w b) = 1 := by
    rw [measure_iUnion hdisj fun b => measurableSet_slotW w b, ← hw]
    refine tsum_congr fun b => ?_
    rw [Measure.restrict_apply (measurableSet_slotW w b),
      Set.inter_eq_self_of_subset_left (slotW_subset hw b), volume_slotW hw b]
  rw [prob_compl_eq_one_sub hmeas, hfull, tsub_self]

/-- **The law of the conditional draw**: the draw picks a shape with the weight the
family gives it. -/
lemma volume_fibre_drawW {w : Shape → ℝ≥0∞} (hw : ∑' b : Shape, w b = 1) (dflt b : Shape) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | drawW w dflt u = b} = w b := by
  have hslot : (volume.restrict (Set.Ico (0 : ℝ) 1)) (slotW w b) = w b := by
    rw [Measure.restrict_apply (measurableSet_slotW w b),
      Set.inter_eq_self_of_subset_left (slotW_subset hw b), volume_slotW hw b]
  by_cases hb : b = dflt
  · subst hb
    rw [fibre_drawW_dflt hw b]
    refine le_antisymm ?_ ?_
    · refine le_trans (measure_union_le _ _) ?_
      rw [hslot, volume_compl_iUnion_slotW hw, add_zero]
    · exact hslot ▸ measure_mono Set.subset_union_left
  · rw [fibre_drawW_of_ne hw hb, hslot]

/-- The draw only ever picks a shape the family charges. -/
lemma weight_drawW_ne_zero {w : Shape → ℝ≥0∞} (hw : ∑' b : Shape, w b = 1) {dflt : Shape}
    (hdflt : w dflt ≠ 0) (u : ℝ) : w (drawW w dflt u) ≠ 0 := by
  by_cases hex : ∃ b : Shape, u ∈ slotW w b
  · obtain ⟨b, hb⟩ := hex
    rw [drawW_of_mem hw dflt hb]
    intro hzero
    have : slotW w b = ∅ := by
      have hvol : volume (slotW w b) = 0 := by rw [volume_slotW hw b, hzero]
      by_contra hne
      obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have hlt : (cumW w (shapeIdx b)).toReal < (cumW w (shapeIdx b + 1)).toReal :=
        lt_of_le_of_lt hv.1 hv.2
      rw [slotW, Real.volume_Ico, ENNReal.ofReal_eq_zero] at hvol
      linarith
    rw [this] at hb
    exact hb
  · rw [drawW_of_not_mem dflt hex]
    exact hdflt

/-! ### The coupling of `thm:shape-coupling` -/

/-- The first marginal of a law on pairs. -/
noncomputable def margFst (π : PMF (Shape × Shape)) (a : Shape) : ℝ≥0∞ := ∑' b : Shape, π (a, b)

/-- The second marginal of a law on pairs. -/
noncomputable def margSnd (π : PMF (Shape × Shape)) (b : Shape) : ℝ≥0∞ := ∑' a : Shape, π (a, b)

lemma margFst_le_one (π : PMF (Shape × Shape)) (a : Shape) : margFst π a ≤ 1 := by
  refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective (f := fun b : Shape => (a, b))
    (fun b b' h => (Prod.mk.injEq _ _ _ _ ▸ h).2) π) ?_
  exact le_of_eq π.tsum_coe

lemma margSnd_le_one (π : PMF (Shape × Shape)) (b : Shape) : margSnd π b ≤ 1 := by
  refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective (f := fun a : Shape => (a, b))
    (fun a a' h => (Prod.mk.injEq _ _ _ _ ▸ h).1) π) ?_
  exact le_of_eq π.tsum_coe

lemma margFst_ne_top (π : PMF (Shape × Shape)) (a : Shape) : margFst π a ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (margFst_le_one π a)

lemma margSnd_ne_top (π : PMF (Shape × Shape)) (b : Shape) : margSnd π b ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (margSnd_le_one π b)

lemma le_margFst (π : PMF (Shape × Shape)) (a b : Shape) : π (a, b) ≤ margFst π a :=
  ENNReal.le_tsum (f := fun b : Shape ↦ π (a, b)) b

lemma le_margSnd (π : PMF (Shape × Shape)) (a b : Shape) : π (a, b) ≤ margSnd π b :=
  ENNReal.le_tsum (f := fun a : Shape ↦ π (a, b)) a

/-- **The coupling of `thm:shape-coupling`**: a law on pairs whose marginals are the two
shape laws and which charges only pairs of `9D³`-comparable shapes. -/
structure IsShapeCoupling (Dq : ℝ) (q₁ q₂ : PMF Shape) (π : PMF (Shape × Shape)) : Prop where
  /-- The first marginal is the shape law of the first offspring law. -/
  marg₁ : ∀ a : Shape, margFst π a = q₁ a
  /-- The second marginal is the shape law of the second offspring law. -/
  marg₂ : ∀ b : Shape, margSnd π b = q₂ b
  /-- A charged pair is comparable. -/
  qi : ∀ p : Shape × Shape, π p ≠ 0 →
    MarkedQI (9 * Dq ^ 3) (shapeSpace p.1) (shapeSpace p.2)
  /-- A charged pair is comparable the other way. -/
  qi' : ∀ p : Shape × Shape, π p ≠ 0 →
    MarkedQI (9 * Dq ^ 3) (shapeSpace p.2) (shapeSpace p.1)

/-! ### The label graph on the pairs -/

/-- **The label graph `𝖰` of `thm:shape-coupling`**: distinct pairs the coupling charges
are linked when all four cross comparisons between their components hold, at the scale
`729D⁷` that the composition of the edge scale of `def:shape-net` with the comparability of
a charged pair produces.  A pair the coupling does not charge, which no label ever takes, is
linked to everything, so that it carries no weight in `eq:etaG`. -/
def pairNet (π : PMF (Shape × Shape)) (Dq : ℝ) : SimpleGraph (Shape × Shape) where
  Adj p p' := p ≠ p' ∧ (π p = 0 ∨ π p' = 0 ∨
    (MarkedQI (729 * Dq ^ 7) (shapeSpace p.1) (shapeSpace p'.2) ∧
      MarkedQI (729 * Dq ^ 7) (shapeSpace p'.2) (shapeSpace p.1) ∧
      MarkedQI (729 * Dq ^ 7) (shapeSpace p'.1) (shapeSpace p.2) ∧
      MarkedQI (729 * Dq ^ 7) (shapeSpace p.2) (shapeSpace p'.1)))
  symm := by
    refine ⟨fun p p' h => ⟨h.1.symm, ?_⟩⟩
    rcases h.2 with h0 | h0 | ⟨h1, h2, h3, h4⟩
    · exact Or.inr (Or.inl h0)
    · exact Or.inl h0
    · exact Or.inr (Or.inr ⟨h3, h4, h1, h2⟩)
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A pair the coupling does not charge is compatible with everything, so its ball carries
the whole mass. -/
lemma gdeg_pairNet_of_zero (π : PMF (Shape × Shape)) (Dq : ℝ) {v : Shape × Shape}
    (hv : π v = 0) : gdeg π (pairNet π Dq) v = 1 := by
  have h : rE π (compat (pairNet π Dq)) v = 1 := by
    rw [rE]
    calc ∑' y : Shape × Shape, (if compat (pairNet π Dq) v y then π y else 0)
        = ∑' y : Shape × Shape, π y := by
          refine tsum_congr fun y => ite_eq_left ?_
          by_cases hy : y = v
          · exact Or.inl hy.symm
          · exact Or.inr ⟨fun h => hy h.symm, Or.inl hv⟩
      _ = 1 := π.tsum_coe
  rw [gdeg, h, ENNReal.toReal_one]

section Scales

variable {Dq : ℝ}

/-- The comparability scale of a pair the coupling charges. -/
lemma one_le_coupScale (hD : 1 ≤ Dq) : (1 : ℝ) ≤ 9 * Dq ^ 3 := by
  have h3 : (1 : ℝ) ≤ Dq ^ 3 := one_le_pow₀ hD
  linarith

/-- The edge scale of `def:shape-net`. -/
lemma one_le_netScale (hD : 1 ≤ Dq) : (1 : ℝ) ≤ 27 * Dq ^ 4 := by
  have h4 : (1 : ℝ) ≤ Dq ^ 4 := one_le_pow₀ hD
  linarith

/-- The edge scale of the label graph on the pairs. -/
lemma one_le_pairScale (hD : 1 ≤ Dq) : (1 : ℝ) ≤ 729 * Dq ^ 7 := by
  have h7 : (1 : ℝ) ≤ Dq ^ 7 := one_le_pow₀ hD
  linarith

/-- The scale of the pair graph absorbs the scale of a charged pair. -/
lemma coupScale_le_pairScale (hD : 1 ≤ Dq) : 9 * Dq ^ 3 ≤ 729 * Dq ^ 7 := by
  have h0 : (0 : ℝ) ≤ Dq := le_trans zero_le_one hD
  have h3 : (1 : ℝ) ≤ Dq ^ 3 := one_le_pow₀ hD
  nlinarith [pow_le_pow_right₀ hD (show 3 ≤ 7 by norm_num)]

/-- Composing a comparison at the edge scale with a comparison of a charged pair lands at
the scale of the pair graph. -/
lemma markedQI_comp_net_coup (hD : 1 ≤ Dq) {X Y Z : MarkedSpace}
    (h : MarkedQI (27 * Dq ^ 4) X Y) (h' : MarkedQI (9 * Dq ^ 3) Y Z) :
    MarkedQI (729 * Dq ^ 7) X Z := by
  have hcomp := markedQI_comp (one_le_netScale hD) (one_le_coupScale hD) h h'
  have hconst : 3 * (27 * Dq ^ 4) * (9 * Dq ^ 3) = 729 * Dq ^ 7 := by ring
  rwa [hconst] at hcomp

lemma markedQI_comp_coup_net (hD : 1 ≤ Dq) {X Y Z : MarkedSpace}
    (h : MarkedQI (9 * Dq ^ 3) X Y) (h' : MarkedQI (27 * Dq ^ 4) Y Z) :
    MarkedQI (729 * Dq ^ 7) X Z := by
  have hcomp := markedQI_comp (one_le_coupScale hD) (one_le_netScale hD) h h'
  have hconst : 3 * (9 * Dq ^ 3) * (27 * Dq ^ 4) = 729 * Dq ^ 7 := by ring
  rwa [hconst] at hcomp

end Scales

/-- Compatibility in `def:shape-net` of the first components carries two charged pairs into
compatibility in the label graph: each cross comparison runs through one component of a
charged pair. -/
theorem compat_pairNet_of_compat_shapeNet {Dq : ℝ} (hD : 1 ≤ Dq) {q₁ q₂ : PMF Shape}
    {π : PMF (Shape × Shape)} (hπ : IsShapeCoupling Dq q₁ q₂ π) {p p' : Shape × Shape}
    (hp : π p ≠ 0) (hp' : π p' ≠ 0) (h : compat (shapeNet Dq) p.1 p'.1) :
    compat (pairNet π Dq) p p' := by
  by_cases hpp : p = p'
  · exact Or.inl hpp
  have hac : MarkedQI (27 * Dq ^ 4) (shapeSpace p.1) (shapeSpace p'.1) := by
    rcases h with heq | hadj
    · rw [heq]; exact markedQI_id (one_le_netScale hD) _
    · exact hadj.2.1
  have hca : MarkedQI (27 * Dq ^ 4) (shapeSpace p'.1) (shapeSpace p.1) := by
    rcases h with heq | hadj
    · rw [heq]; exact markedQI_id (one_le_netScale hD) _
    · exact hadj.2.2
  exact Or.inr ⟨hpp, Or.inr (Or.inr ⟨markedQI_comp_net_coup hD hac (hπ.qi p' hp'),
    markedQI_comp_coup_net hD (hπ.qi' p' hp') hca,
    markedQI_comp_net_coup hD hca (hπ.qi p hp),
    markedQI_comp_coup_net hD (hπ.qi' p hp) hac⟩)⟩

/-- **The cross comparison of the label graph**: two charged pairs at graph distance at
most one have the first component of the one comparable to the second component of the
other. -/
theorem markedQI_of_compat_pairNet {Dq : ℝ} (hD : 1 ≤ Dq) {q₁ q₂ : PMF Shape}
    {π : PMF (Shape × Shape)} (hπ : IsShapeCoupling Dq q₁ q₂ π) {p p' : Shape × Shape}
    (hp : π p ≠ 0) (hp' : π p' ≠ 0) (h : compat (pairNet π Dq) p p') :
    MarkedQI (729 * Dq ^ 7) (shapeSpace p.1) (shapeSpace p'.2) := by
  rcases h with heq | hadj
  · rw [← heq]
    exact (hπ.qi p hp).mono (by linarith [one_le_coupScale hD]) (coupScale_le_pairScale hD)
  · rcases hadj.2 with h0 | h0 | ⟨h1, _, _, _⟩
    · exact absurd h0 hp
    · exact absurd h0 hp'
    · exact h1

/-! ### The two label maps -/

/-- **The conditional law of the partner of a first component**, a point mass at the
one-vertex shape where the marginal vanishes. -/
noncomputable def condFst (π : PMF (Shape × Shape)) (a b : Shape) : ℝ≥0∞ :=
  if margFst π a = 0 then (if b = Shape.ofList [] then 1 else 0) else π (a, b) / margFst π a

/-- **The conditional law of the partner of a second component**. -/
noncomputable def condSnd (π : PMF (Shape × Shape)) (b a : Shape) : ℝ≥0∞ :=
  if margSnd π b = 0 then (if a = Shape.ofList [] then 1 else 0) else π (a, b) / margSnd π b

lemma tsum_condFst (π : PMF (Shape × Shape)) (a : Shape) : ∑' b : Shape, condFst π a b = 1 := by
  by_cases h : margFst π a = 0
  · simp only [condFst, ite_eq_left h]
    simp
  · have hterm : ∀ b : Shape, condFst π a b = π (a, b) * (margFst π a)⁻¹ := by
      intro b
      rw [condFst, ite_eq_right h, div_eq_mul_inv]
    rw [tsum_congr hterm, ENNReal.tsum_mul_right]
    exact ENNReal.mul_inv_cancel h (margFst_ne_top π a)

lemma tsum_condSnd (π : PMF (Shape × Shape)) (b : Shape) : ∑' a : Shape, condSnd π b a = 1 := by
  by_cases h : margSnd π b = 0
  · simp only [condSnd, ite_eq_left h]
    simp
  · have hterm : ∀ a : Shape, condSnd π b a = π (a, b) * (margSnd π b)⁻¹ := by
      intro a
      rw [condSnd, ite_eq_right h, div_eq_mul_inv]
    rw [tsum_congr hterm, ENNReal.tsum_mul_right]
    exact ENNReal.mul_inv_cancel h (margSnd_ne_top π b)

/-- A partner the coupling charges, where there is one. -/
noncomputable def partnerFst (π : PMF (Shape × Shape)) (a : Shape) : Shape :=
  if h : ∃ b : Shape, π (a, b) ≠ 0 then h.choose else Shape.ofList []

/-- A partner the coupling charges, on the other side. -/
noncomputable def partnerSnd (π : PMF (Shape × Shape)) (b : Shape) : Shape :=
  if h : ∃ a : Shape, π (a, b) ≠ 0 then h.choose else Shape.ofList []

lemma condFst_partnerFst_ne_zero (π : PMF (Shape × Shape)) (a : Shape) :
    condFst π a (partnerFst π a) ≠ 0 := by
  by_cases h : margFst π a = 0
  · have hno : ¬ ∃ b : Shape, π (a, b) ≠ 0 := by
      rintro ⟨b, hb⟩
      exact hb (nonpos_iff_eq_zero.mp (h ▸ le_margFst π a b))
    rw [partnerFst, dite_eq_right hno, condFst, ite_eq_left h, ite_eq_left rfl]
    exact one_ne_zero
  · have hex : ∃ b : Shape, π (a, b) ≠ 0 := by
      by_contra hno
      exact h (ENNReal.tsum_eq_zero.mpr fun b => not_not.mp fun hb => hno ⟨b, hb⟩)
    rw [partnerFst, dite_eq_left hex, condFst, ite_eq_right h, Ne, ENNReal.div_eq_zero_iff]
    rintro (h1 | h1)
    · exact hex.choose_spec h1
    · exact margFst_ne_top π a h1

lemma condSnd_partnerSnd_ne_zero (π : PMF (Shape × Shape)) (b : Shape) :
    condSnd π b (partnerSnd π b) ≠ 0 := by
  by_cases h : margSnd π b = 0
  · have hno : ¬ ∃ a : Shape, π (a, b) ≠ 0 := by
      rintro ⟨a, ha⟩
      exact ha (nonpos_iff_eq_zero.mp (h ▸ le_margSnd π a b))
    rw [partnerSnd, dite_eq_right hno, condSnd, ite_eq_left h, ite_eq_left rfl]
    exact one_ne_zero
  · have hex : ∃ a : Shape, π (a, b) ≠ 0 := by
      by_contra hno
      exact h (ENNReal.tsum_eq_zero.mpr fun a => not_not.mp fun ha => hno ⟨a, ha⟩)
    rw [partnerSnd, dite_eq_left hex, condSnd, ite_eq_right h, Ne, ENNReal.div_eq_zero_iff]
    rintro (h1 | h1)
    · exact hex.choose_spec h1
    · exact margSnd_ne_top π b h1

/-- **The label map of the first law**: the support fix of the shape together with a
partner drawn from the conditional law of the coupling. -/
noncomputable def pairLab (π : PMF (Shape × Shape)) (σ : Shape) (u : ℝ) : Shape × Shape :=
  (σ.fix, drawW (condFst π σ.fix) (partnerFst π σ.fix) u)

/-- **The label map of the second law**: the mirror pair. -/
noncomputable def pairLab' (π : PMF (Shape × Shape)) (σ : Shape) (u : ℝ) : Shape × Shape :=
  (drawW (condSnd π σ.fix) (partnerSnd π σ.fix) u, σ.fix)

lemma measurableSet_pairLab_fibre (π : PMF (Shape × Shape)) (τ : Shape) (x : Shape × Shape) :
    MeasurableSet {u : ℝ | pairLab π τ u = x} := by
  by_cases h : τ.fix = x.1
  · have hset : {u : ℝ | pairLab π τ u = x}
        = {u : ℝ | drawW (condFst π τ.fix) (partnerFst π τ.fix) u = x.2} := by
      ext u
      simp only [pairLab, Set.mem_ofPred_eq, Prod.ext_iff, h, true_and]
    rw [hset]
    exact measurableSet_fibre_drawW (tsum_condFst π τ.fix) _ _
  · have hset : {u : ℝ | pairLab π τ u = x} = (∅ : Set ℝ) := by
      ext u
      simp only [pairLab, Set.mem_ofPred_eq, Prod.ext_iff, Set.mem_empty_iff_false, iff_false]
      tauto
    rw [hset]
    exact MeasurableSet.empty

lemma measurableSet_pairLab'_fibre (π : PMF (Shape × Shape)) (τ : Shape) (x : Shape × Shape) :
    MeasurableSet {u : ℝ | pairLab' π τ u = x} := by
  by_cases h : τ.fix = x.2
  · have hset : {u : ℝ | pairLab' π τ u = x}
        = {u : ℝ | drawW (condSnd π τ.fix) (partnerSnd π τ.fix) u = x.1} := by
      ext u
      simp only [pairLab', Set.mem_ofPred_eq, Prod.ext_iff, h, and_true]
    rw [hset]
    exact measurableSet_fibre_drawW (tsum_condSnd π τ.fix) _ _
  · have hset : {u : ℝ | pairLab' π τ u = x} = (∅ : Set ℝ) := by
      ext u
      simp only [pairLab', Set.mem_ofPred_eq, Prod.ext_iff, Set.mem_empty_iff_false, iff_false]
      tauto
    rw [hset]
    exact MeasurableSet.empty

/-! ### The common law of the two label fields -/

/-- The support fix of a shape carries positive mass: it is a shape of the support, where
`thm:shape-mass` (`it:shape-mass-point`) bounds the mass below. -/
lemma shapePMF_fix_ne_zero (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) (τ : Shape) : shapePMF θ hq hq0 h2 τ.fix ≠ 0 := by
  have hp := shapeWeight_pos θ hq hq0 h2
  have hmass : ENNReal.ofReal (shapeWeight θ ^ τ.fix.size) ≤ shapePMF θ hq hq0 h2 τ.fix :=
    (ofReal_pow_size_le_shapeMass_of_supported θ hq hq0 h2 (supported_fix τ)).trans
      (shapeMass_le_shapePMF θ hq hq0 h2 (supported_fix τ))
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (shapeWeight θ ^ τ.fix.size) :=
    ENNReal.ofReal_pos.mpr (pow_pos hp _)
  exact (lt_of_lt_of_le hpos hmass).ne'

/-- **The label of a shape is a pair the coupling charges**: the partner is drawn from the
conditional law, which only charges partners the coupling charges. -/
lemma pairLab_ne_zero (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) (π : PMF (Shape × Shape))
    (hm : ∀ a : Shape, margFst π a = shapePMF θ hq hq0 h2 a) (τ : Shape) (u : ℝ) :
    π (τ.fix, drawW (condFst π τ.fix) (partnerFst π τ.fix) u) ≠ 0 := by
  have hpos : margFst π τ.fix ≠ 0 := by
    rw [hm]
    exact shapePMF_fix_ne_zero θ hq hq0 h2 τ
  have hne := weight_drawW_ne_zero (tsum_condFst π τ.fix)
    (condFst_partnerFst_ne_zero π τ.fix) u
  intro hzero
  rw [condFst, ite_eq_right hpos, hzero, ENNReal.zero_div] at hne
  exact hne rfl

/-- The mirror statement for the second law. -/
lemma pairLab'_ne_zero (θ' : Offspring 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) (π : PMF (Shape × Shape))
    (hm' : ∀ b : Shape, margSnd π b = shapePMF θ' hq' hq0' h2' b) (τ : Shape) (u : ℝ) :
    π (drawW (condSnd π τ.fix) (partnerSnd π τ.fix) u, τ.fix) ≠ 0 := by
  have hpos : margSnd π τ.fix ≠ 0 := by
    rw [hm']
    exact shapePMF_fix_ne_zero θ' hq' hq0' h2' τ
  have hne := weight_drawW_ne_zero (tsum_condSnd π τ.fix)
    (condSnd_partnerSnd_ne_zero π τ.fix) u
  intro hzero
  rw [condSnd, ite_eq_right hpos, hzero, ENNReal.zero_div] at hne
  exact hne rfl

/-- **`thm:shape-coupling` (`it:shape-coupling-law`) for the first law**: the label
of a shape drawn from the first law has the law of the coupling. -/
theorem labMass_pairLab (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) (π : PMF (Shape × Shape))
    (hm : ∀ a : Shape, margFst π a = shapePMF θ hq hq0 h2 a) (x : Shape × Shape) :
    labMass θ (pairLab π) x = π x := by
  have hvol : ∀ τ : Shape,
      (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | pairLab π τ u = x}
        = (if τ.fix = x.1 then condFst π x.1 x.2 else 0) := by
    intro τ
    by_cases h : τ.fix = x.1
    · have hset : {u : ℝ | pairLab π τ u = x}
          = {u : ℝ | drawW (condFst π τ.fix) (partnerFst π τ.fix) u = x.2} := by
        ext u
        simp only [pairLab, Set.mem_ofPred_eq, Prod.ext_iff, h, true_and]
      rw [hset, volume_fibre_drawW (tsum_condFst π τ.fix), ite_eq_left h, h]
    · have hset : {u : ℝ | pairLab π τ u = x} = (∅ : Set ℝ) := by
        ext u
        simp only [pairLab, Set.mem_ofPred_eq, Prod.ext_iff, Set.mem_empty_iff_false, iff_false]
        tauto
      rw [hset, measure_empty, ite_eq_right h]
  have hterm : ∀ τ : Shape,
      shapeMass θ τ * (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | pairLab π τ u = x}
        = (if τ.fix = x.1 then shapeMass θ τ else 0) * condFst π x.1 x.2 := by
    intro τ
    rw [hvol τ]
    by_cases h : τ.fix = x.1 <;> simp [h]
  rw [labMass, tsum_congr hterm, ENNReal.tsum_mul_right,
    ← shapePMF_eq_tsum θ hq hq0 h2, ← hm x.1]
  by_cases h0 : margFst π x.1 = 0
  · rw [condFst, ite_eq_left (by rw [hm] at h0 ⊢; exact h0), h0, zero_mul]
    exact (nonpos_iff_eq_zero.mp (h0 ▸ le_margFst π x.1 x.2)).symm
  · rw [condFst, ite_eq_right h0]
    exact ENNReal.mul_div_cancel' (fun h => absurd h h0)
      (fun h => absurd h (margFst_ne_top π x.1))

/-- **`thm:shape-coupling` (`it:shape-coupling-law`) for the second law**: the same
law for the mirror label map. -/
theorem labMass_pairLab' (θ' : Offspring 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) (π : PMF (Shape × Shape))
    (hm' : ∀ b : Shape, margSnd π b = shapePMF θ' hq' hq0' h2' b) (x : Shape × Shape) :
    labMass θ' (pairLab' π) x = π x := by
  have hvol : ∀ τ : Shape,
      (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | pairLab' π τ u = x}
        = (if τ.fix = x.2 then condSnd π x.2 x.1 else 0) := by
    intro τ
    by_cases h : τ.fix = x.2
    · have hset : {u : ℝ | pairLab' π τ u = x}
          = {u : ℝ | drawW (condSnd π τ.fix) (partnerSnd π τ.fix) u = x.1} := by
        ext u
        simp only [pairLab', Set.mem_ofPred_eq, Prod.ext_iff, h, and_true]
      rw [hset, volume_fibre_drawW (tsum_condSnd π τ.fix), ite_eq_left h, h]
    · have hset : {u : ℝ | pairLab' π τ u = x} = (∅ : Set ℝ) := by
        ext u
        simp only [pairLab', Set.mem_ofPred_eq, Prod.ext_iff, Set.mem_empty_iff_false, iff_false]
        tauto
      rw [hset, measure_empty, ite_eq_right h]
  have hterm : ∀ τ : Shape,
      shapeMass θ' τ * (volume.restrict (Set.Ico (0 : ℝ) 1)) {u : ℝ | pairLab' π τ u = x}
        = (if τ.fix = x.2 then shapeMass θ' τ else 0) * condSnd π x.2 x.1 := by
    intro τ
    rw [hvol τ]
    by_cases h : τ.fix = x.2 <;> simp [h]
  rw [labMass, tsum_congr hterm, ENNReal.tsum_mul_right,
    ← shapePMF_eq_tsum θ' hq' hq0' h2', ← hm' x.2]
  by_cases h0 : margSnd π x.2 = 0
  · rw [condSnd, ite_eq_left (by rw [hm'] at h0 ⊢; exact h0), h0, zero_mul]
    exact (nonpos_iff_eq_zero.mp (h0 ▸ le_margSnd π x.1 x.2)).symm
  · rw [condSnd, ite_eq_right h0]
    exact ENNReal.mul_div_cancel' (fun h => absurd h h0)
      (fun h => absurd h (margSnd_ne_top π x.2))

/-! ### Matched labels give comparable shapes -/

/-- **`thm:shape-coupling` (`it:shape-coupling-qi`)**: matched labels give
comparable shapes.  A shape is `1`-comparable to its fix, the fixes of the two shapes are
the first and the second component of two pairs the coupling charges at graph distance at
most one, and the fix of the second shape is `3`-comparable back to it. -/
theorem markedQI_of_compat_pairLab {Dq : ℝ} (hD : 1 ≤ Dq) (θ θ' : Offspring 2)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2)
    (hq' : θ'.extinction < 1) (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2)
    {q₁ q₂ : PMF Shape} {π : PMF (Shape × Shape)} (hπ : IsShapeCoupling Dq q₁ q₂ π)
    (hm : ∀ a : Shape, margFst π a = shapePMF θ hq hq0 h2 a)
    (hm' : ∀ b : Shape, margSnd π b = shapePMF θ' hq' hq0' h2' b)
    (τ τ' : Shape) (u u' : ℝ)
    (h : compat (pairNet π Dq) (pairLab π τ u) (pairLab' π τ' u')) :
    MarkedQI (19683 * Dq ^ 7) (shapeSpace τ) (shapeSpace τ') := by
  have hp : π (pairLab π τ u) ≠ 0 := pairLab_ne_zero θ hq hq0 h2 π hm τ u
  have hp' : π (pairLab' π τ' u') ≠ 0 := pairLab'_ne_zero θ' hq' hq0' h2' π hm' τ' u'
  have hmid : MarkedQI (729 * Dq ^ 7) (shapeSpace τ.fix) (shapeSpace τ'.fix) :=
    markedQI_of_compat_pairNet hD hπ hp hp' h
  have hlamb : (1 : ℝ) ≤ 729 * Dq ^ 7 := one_le_pairScale hD
  have hfix : MarkedQI 1 (shapeSpace τ) (shapeSpace τ.fix) := markedQI_shape_fix τ
  have hfix' : MarkedQI 3 (shapeSpace τ'.fix) (shapeSpace τ') := by
    have hs := markedQI_symm (le_refl (1 : ℝ)) (markedQI_shape_fix τ')
    norm_num at hs
    exact hs
  have h12 := markedQI_comp (le_refl (1 : ℝ)) hlamb hfix hmid
  have hall := markedQI_comp (by nlinarith) (by norm_num) h12 hfix'
  have hconst : 3 * (3 * 1 * (729 * Dq ^ 7)) * 3 = 19683 * Dq ^ 7 := by ring
  rwa [hconst] at hall

/-! ### The product form of the two label fields -/

/-- The labels of the copies of a prefix-closed finite set are independent with the law of
the coupling. -/
lemma bushyMeasure_pairLab_prod (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (π : PMF (Shape × Shape))
    (hm : ∀ a : Shape, margFst π a = shapePMF θ hq hq0 h2 a) (S : Finset Word)
    (hS : ∀ w ∈ S, ∀ p, p <+: w → p ∈ S) (v : Word → Shape × Shape) :
    bushyMeasure θ (⋂ w ∈ S, {ω : BushySample | shapeLab (pairLab π) ω w = v w})
      = ∏ w ∈ S, π (v w) := by
  rw [bushyMeasure_shapeLab_prod θ hq hq0 h2 (measurableSet_pairLab_fibre π) S hS v]
  exact Finset.prod_congr rfl fun w _ => labMass_pairLab θ hq hq0 h2 π hm (v w)

/-- The same for the second law. -/
lemma bushyMeasure_pairLab'_prod (θ' : Offspring 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) (π : PMF (Shape × Shape))
    (hm' : ∀ b : Shape, margSnd π b = shapePMF θ' hq' hq0' h2' b) (S : Finset Word)
    (hS : ∀ w ∈ S, ∀ p, p <+: w → p ∈ S) (v : Word → Shape × Shape) :
    bushyMeasure θ' (⋂ w ∈ S, {ω : BushySample | shapeLab (pairLab' π) ω w = v w})
      = ∏ w ∈ S, π (v w) := by
  rw [bushyMeasure_shapeLab_prod θ' hq' hq0' h2' (measurableSet_pairLab'_fibre π) S hS v]
  exact Finset.prod_congr rfl fun w _ => labMass_pairLab' θ' hq' hq0' h2' π hm' (v w)

/-! ### The potential of the law on pairs -/

/-- A sum over a type grouped by the fibres of a map. -/
lemma tsum_fiber_proj {V W : Type*} (f : V → ℝ≥0∞) (pr : V → W) :
    ∑' v : V, f v = ∑' a : W, ∑' v : {v : V // pr v = a}, f (v : V) := by
  rw [← (Equiv.sigmaFiberEquiv pr).tsum_eq f, ENNReal.tsum_sigma']
  rfl

/-- **The potential along a projection**: if the ball of every vertex is at least as heavy
as the ball of its projection, and the mass of every fibre is at most the mass of its
image, then the potential of `eq:etaG` drops.  The one-site weight decreases in the ball
mass, and the fibres are summed out against the image law. -/
theorem etaG_le_of_proj {V : Type*} (μ : PMF V) (G : SimpleGraph V) (q₁ : PMF Shape)
    (G₁ : SimpleGraph Shape) (pr : V → Shape)
    (hpos : ∀ v : V, 0 < gdeg q₁ G₁ (pr v))
    (hdom : ∀ v : V, gdeg q₁ G₁ (pr v) ≤ gdeg μ G v)
    (hfib : ∀ a : Shape, ∑' v : {v : V // pr v = a}, μ (v : V) ≤ q₁ a) :
    etaG μ G ≤ etaG q₁ G₁ := by
  rw [etaG_eq_tsum_wgt, etaG_eq_tsum_wgt]
  have hstep : ∀ v : V, μ v * ENNReal.ofReal (wgt (gdeg μ G v))
      ≤ μ v * ENNReal.ofReal (wgt (gdeg q₁ G₁ (pr v))) := by
    intro v
    gcongr
    exact wgt_le_wgt_of_le (hpos v) (hdom v) (gdeg_le_one μ G v)
  calc ∑' v : V, μ v * ENNReal.ofReal (wgt (gdeg μ G v))
      ≤ ∑' v : V, μ v * ENNReal.ofReal (wgt (gdeg q₁ G₁ (pr v))) := ENNReal.tsum_le_tsum hstep
    _ = ∑' a : Shape, ∑' v : {v : V // pr v = a},
          μ (v : V) * ENNReal.ofReal (wgt (gdeg q₁ G₁ a)) := by
        rw [tsum_fiber_proj (fun v : V => μ v * ENNReal.ofReal (wgt (gdeg q₁ G₁ (pr v)))) pr]
        exact tsum_congr fun a => tsum_congr fun v => by rw [v.2]
    _ = ∑' a : Shape, (∑' v : {v : V // pr v = a}, μ (v : V))
          * ENNReal.ofReal (wgt (gdeg q₁ G₁ a)) := tsum_congr fun a => ENNReal.tsum_mul_right
    _ ≤ ∑' a : Shape, q₁ a * ENNReal.ofReal (wgt (gdeg q₁ G₁ a)) :=
        ENNReal.tsum_le_tsum fun a => by gcongr; exact hfib a

/-- The fibre of the first projection over a shape is a copy of the shapes. -/
def fibreFstEquiv (a : Shape) : Shape ≃ {v : Shape × Shape // v.1 = a} where
  toFun b := ⟨(a, b), rfl⟩
  invFun v := (v : Shape × Shape).2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨x, y⟩, hx⟩
    cases hx
    rfl

/-- The fibre of the first projection over a shape carries the first marginal. -/
lemma tsum_fibre_fst (π : PMF (Shape × Shape)) (a : Shape) :
    ∑' v : {v : Shape × Shape // v.1 = a}, π (v : Shape × Shape) = margFst π a :=
  Eq.trans ((fibreFstEquiv a).tsum_eq fun v : {v : Shape × Shape // v.1 = a} =>
    π (v : Shape × Shape)).symm rfl

/-- **The ball of a pair contains the ball of its first component**: a pair the coupling
charges is compatible with every charged pair whose first component is compatible with
its own, and the charged pairs above a shape carry the mass of the shape. -/
theorem gdeg_shapeNet_le_gdeg_pairNet {Dq : ℝ} (hD : 1 ≤ Dq) {q₁ q₂ : PMF Shape}
    {π : PMF (Shape × Shape)} (hπ : IsShapeCoupling Dq q₁ q₂ π) {p : Shape × Shape}
    (hp : π p ≠ 0) : gdeg q₁ (shapeNet Dq) p.1 ≤ gdeg π (pairNet π Dq) p := by
  have hstep : ∀ c : Shape, (if compat (shapeNet Dq) p.1 c then q₁ c else 0)
      = ∑' d : Shape, (if compat (shapeNet Dq) (p.1, d).1 c then π (c, d) else 0) := by
    intro c
    by_cases hc : compat (shapeNet Dq) p.1 c
    · simp only [ite_eq_left hc]
      rw [← hπ.marg₁ c]
      rfl
    · simp only [ite_eq_right hc, tsum_zero]
  have hprod : ∑' z : Shape × Shape, (if compat (shapeNet Dq) p.1 z.1 then π z else 0)
      = ∑' c : Shape, ∑' d : Shape,
          (if compat (shapeNet Dq) (p.1, d).1 c then π (c, d) else 0) := ENNReal.tsum_prod'
  have hle : rE q₁ (compat (shapeNet Dq)) p.1 ≤ rE π (compat (pairNet π Dq)) p := by
    rw [rE, rE, tsum_congr hstep, ← hprod]
    refine ENNReal.tsum_le_tsum fun z => ?_
    by_cases hz : π z = 0
    · simp [hz]
    · by_cases hc : compat (shapeNet Dq) p.1 z.1
      · rw [ite_eq_left hc, ite_eq_left (compat_pairNet_of_compat_shapeNet hD hπ hp hz hc)]
      · rw [ite_eq_right hc]
        exact zero_le
  exact ENNReal.toReal_mono (rE_ne_top (μ := π) (R := compat (pairNet π Dq)) (x := p)) hle

/-- Every ball of `def:shape-net` is charged: the shrinking lands in the support, where
`thm:shape-mass` (`it:shape-mass-point`) bounds the mass below. -/
lemma gdeg_shapeNet_pos (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) {D : ℕ} (hD : 30 ≤ D) (a : Shape) :
    0 < gdeg (shapePMF θ hq hq0 h2) (shapeNet (D : ℝ)) a := by
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
  have hs : 1 ≤ D / 30 := by omega
  have hs0 : (0 : ℝ) ≤ ((D / 30 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hs30 : 30 * ((D / 30 : ℕ) : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast (by omega : 30 * (D / 30) ≤ D)
  have hsD : 2592 * ((D / 30 : ℕ) : ℝ) ^ 2 ≤ 3 * (D : ℝ) ^ 2 := by nlinarith
  exact lt_of_lt_of_le (pow_pos (shapeWeight_pos θ hq hq0 h2) _)
    (pow_le_gdeg_shapeNet θ hq hq0 h2 hDR hs hsD a)

/-- **`thm:shape-coupling` (`it:shape-coupling-eta`)**: the potential of the law on
pairs is at most the potential of the shape law of the first offspring law over
`def:shape-net`, which `eq:shape-eta` bounds. -/
theorem etaG_pairNet_le (θ : Offspring 2) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (h2 : 0 < θ 2) {D : ℕ} (hD : 30 ≤ D) {q₂ : PMF Shape} {π : PMF (Shape × Shape)}
    (hπ : IsShapeCoupling (D : ℝ) (shapePMF θ hq hq0 h2) q₂ π) :
    etaG π (pairNet π (D : ℝ)) ≤ etaG (shapePMF θ hq hq0 h2) (shapeNet (D : ℝ)) := by
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
  refine etaG_le_of_proj π (pairNet π (D : ℝ)) (shapePMF θ hq hq0 h2) (shapeNet (D : ℝ))
    Prod.fst (fun v => gdeg_shapeNet_pos θ hq hq0 h2 hD v.1) (fun v => ?_) (fun a => ?_)
  · by_cases hv : π v = 0
    · rw [gdeg_pairNet_of_zero π (D : ℝ) hv]
      exact gdeg_le_one _ _ _
    · exact gdeg_shapeNet_le_gdeg_pairNet hDR hπ hv
  · rw [tsum_fibre_fst]
    exact le_of_eq (hπ.marg₁ a)

/-! ### `thm:hairy` across two laws -/

/-- **`eq:hairy-rate` across two laws**: over a coupling at scale `D` the failure
probability of the quasi-isometry between the two sampled trees at the scale
`8·19683²D¹⁴` is bounded by the potential of the shape law of the first law over
`def:shape-net`. -/
theorem bushy_rate_shape_tree_cross (θ θ' : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hq' : θ'.extinction < 1)
    (hq0' : 0 < θ'.extinction) (h2' : 0 < θ' 2) {D : ℕ} (hD : 30 ≤ D)
    {π : PMF (Shape × Shape)}
    (hπ : IsShapeCoupling (D : ℝ) (shapePMF θ hq hq0 h2) (shapePMF θ' hq' hq0' h2') π)
    (hη : etaG (shapePMF θ hq hq0 h2) (shapeNet (D : ℝ)) ≤ 1 / 10000) :
    twoBushyMeasure θ θ'
        {ω | ¬ ∃ F : {v : Amb // v ∈ sample ω.1.1} → {v : Amb // v ∈ sample ω.2.1},
          IsSampleQI (8 * 19683 ^ 2 * (D : ℝ) ^ 14) F}
      ≤ 16 * etaG (shapePMF θ hq hq0 h2) (shapeNet (D : ℝ)) := by
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 1 ≤ D)
  have h7 : (1 : ℝ) ≤ (D : ℝ) ^ 7 := one_le_pow₀ hDR
  have hK : (1 : ℝ) ≤ 19683 * (D : ℝ) ^ 7 := by nlinarith
  have hle := etaG_pairNet_le θ hq hq0 h2 hD hπ
  have hmain := bushy_rate_tree θ θ' hq hq' h2 h2' π (pairNet π (D : ℝ)) hK
    (measurableSet_pairLab_fibre π) (measurableSet_pairLab'_fibre π)
    (bushyMeasure_pairLab_prod θ hq hq0 h2 π hπ.marg₁)
    (bushyMeasure_pairLab'_prod θ' hq' hq0' h2' π hπ.marg₂)
    (markedQI_of_compat_pairLab hDR θ θ' hq hq0 h2 hq' hq0' h2' hπ hπ.marg₁ hπ.marg₂)
    (le_trans hle hη)
  have hconst : 8 * (19683 * (D : ℝ) ^ 7) ^ 2 = 8 * 19683 ^ 2 * (D : ℝ) ^ 14 := by ring
  rw [hconst] at hmain
  exact hmain.trans (by gcongr)

end ChainClasses
