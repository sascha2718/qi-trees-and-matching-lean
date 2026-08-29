/-
`sec:shape-harris` of `matching_classes_simple.tex`: **`thm:shape-iid`** in full.

The pieces are in place: `ShapeSplitLaw` has the law of the shape at the root jointly
with the two subtrees below its split, and the identification of the shape at a copy
below the root with the shape of that copy read in the subtree the split hands it.  What
is left is the induction over the copies, and it is the one of `eq:exploration`: over a
prefix-closed finite set of copies, which contains the root and cuts into the copies
below each of the two letters, the mass factorises into the mass of the root shape and
the masses of the two subtrees, and the subtrees are independent copies of the
conditioned law.  Every step is taken modulo the event `IsHairySample`, of full measure
by `ae_isHairySample_of_pos`.

Independence is stated as the product formula over prefix-closed finite sets, as
`eq:exploration` is for the chain labels, rather than through `iIndepFun`: the shapes
carry no measurable structure, and the events `{shapeAt c w = σ}` are what the rest of
the section consumes.  The marginal at a copy other than the root would follow by summing
the prefixes out, as `label_prod` does for the chain labels.

* `subTree`, `mem_subTree`, `prefixClosed_subTree`, `length_subTree`,
  `nil_mem_of_nonempty`: the copies below a letter, and what a prefix-closed set of
  copies hands them.
* `finset_decomp`, `prod_decomp`: **the copies split at the root**, and the product over
  them.
* `shapeMass`: **the law `μ` of `thm:shape-iid`**, one decoration factor per neck vertex
  and the split weight `θ̃₂` at the end.
* `survivalMeasure_shapes_aux`, `survivalMeasure_shapes`: **`thm:shape-iid`, the i.i.d.
  clause**, the product formula over a prefix-closed finite set of copies.
* `shape_decomposition`: **`thm:shape-iid`**, the i.i.d. clause together with the
  isometry of a sample with the assembly of its own shapes.
-/
import ChainClasses.ShapeSplitLaw

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (sample Survives survivors skeletonDegree Offspring sampleMeasure
  survivalMeasure bushMeasure bushAt)

/-! ### The copies below a letter -/

/-- The copies below the first letter `j`: the words `w` with `jw` a copy of `s`. -/
noncomputable def subTree (j : Bool) (s : Finset Word) : Finset Word :=
  s.preimage (fun w ↦ j :: w) (fun a _ b _ h ↦ by simpa using h)

@[simp] lemma mem_subTree {j : Bool} {s : Finset Word} {w : Word} :
    w ∈ subTree j s ↔ j :: w ∈ s := by
  simp [subTree]

/-- Prefix closure passes to the copies below a letter. -/
lemma prefixClosed_subTree {s : Finset Word} (hs : ∀ w ∈ s, ∀ p, p <+: w → p ∈ s)
    (j : Bool) : ∀ w ∈ subTree j s, ∀ p, p <+: w → p ∈ subTree j s := by
  intro w hw p hp
  rw [mem_subTree] at hw ⊢
  exact hs _ hw _ (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)

/-- The copies below a letter are shorter. -/
lemma length_subTree {s : Finset Word} {n : ℕ} (hlen : ∀ w ∈ s, w.length ≤ n + 1)
    (j : Bool) : ∀ w ∈ subTree j s, w.length ≤ n := by
  intro w hw
  rw [mem_subTree] at hw
  have := hlen _ hw
  simp only [List.length_cons] at this
  omega

/-- A nonempty prefix-closed set of copies contains the root. -/
lemma nil_mem_of_nonempty {s : Finset Word} (hs : ∀ w ∈ s, ∀ p, p <+: w → p ∈ s)
    (hne : s.Nonempty) : ([] : Word) ∈ s := by
  obtain ⟨w, hw⟩ := hne
  exact hs w hw [] List.nil_prefix

/-- **The copies split at the root**: a prefix-closed set of copies is the root together
with the copies below each of the two letters. -/
lemma finset_decomp {s : Finset Word} (h : ([] : Word) ∈ s) :
    s = insert ([] : Word)
      ((subTree false s).image (fun w ↦ false :: w)
        ∪ (subTree true s).image (fun w ↦ true :: w)) := by
  ext w
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, mem_subTree]
  cases w with
  | nil => simpa using h
  | cons j w =>
      cases j with
      | false => simp
      | true => simp

/-- The product over a prefix-closed set of copies splits at the root. -/
lemma prod_decomp {M : Type*} [CommMonoid M] {s : Finset Word} (h : ([] : Word) ∈ s)
    (g : Word → M) :
    ∏ w ∈ s, g w
      = g [] * (∏ w ∈ subTree false s, g (false :: w))
          * ∏ w ∈ subTree true s, g (true :: w) := by
  classical
  have hnot : ([] : Word) ∉ (subTree false s).image (fun w ↦ false :: w)
      ∪ (subTree true s).image (fun w ↦ true :: w) := by
    simp
  have hdisj : Disjoint ((subTree false s).image (fun w ↦ false :: w))
      ((subTree true s).image (fun w ↦ true :: w)) := by
    refine Finset.disjoint_left.mpr fun w hw hw' ↦ ?_
    simp only [Finset.mem_image] at hw hw'
    obtain ⟨a, -, rfl⟩ := hw
    obtain ⟨b, -, hb⟩ := hw'
    simp at hb
  conv_lhs => rw [finset_decomp h]
  rw [Finset.prod_insert hnot, Finset.prod_union hdisj,
    Finset.prod_image (fun a _ b _ hab ↦ by simpa using hab),
    Finset.prod_image (fun a _ b _ hab ↦ by simpa using hab), mul_assoc]

/-! ### The law of the shape field -/

/-- **`thm:shape-iid`, the law `μ`**: the mass of a shape, one decoration factor per
neck vertex and the split weight `θ̃₂` at the end. -/
noncomputable def shapeMass (θ : Offspring 2) (σ : Shape) : ENNReal :=
  (σ.decs.map (decMass θ)).prod * ENNReal.ofReal (θ.skeletonWeight 2)

/-- The shape at a copy is an event. -/
lemma measurableSet_shapes (s : Finset Word) (f : Word → Shape) :
    MeasurableSet (⋂ w ∈ s, {c : Amb → ℕ | shapeAt c w = f w}) := by
  refine MeasurableSet.biInter (Set.to_countable _) fun w _ ↦ ?_
  exact fibreMeasurable_shapeAt w (f w)

/-- **`thm:shape-iid`, the i.i.d. clause**: conditioned on survival the shapes of a
prefix-closed finite set of copies are independent with the law `μ`.  The recursion is
the root decomposition: the shape of the root, and below its split two independent copies
of the conditioned law carrying the shape fields of the two subtrees. -/
theorem survivalMeasure_shapes_aux (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) : ∀ (n : ℕ) (s : Finset Word),
    (∀ w ∈ s, w.length ≤ n) → (∀ w ∈ s, ∀ p, p <+: w → p ∈ s) → ∀ f : Word → Shape,
    survivalMeasure (N := 2) θ (⋂ w ∈ s, {c : Amb → ℕ | shapeAt c w = f w})
      = ∏ w ∈ s, shapeMass θ (f w) := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure θ le_rfl hq
  have hnull : survivalMeasure (N := 2) θ {c : Amb → ℕ | IsHairySample c}ᶜ = 0 := by
    have hae := ae_isHairySample_of_pos θ hq h2
    rw [ae_iff] at hae
    exact hae
  have hempty : ∀ f : Word → Shape,
      survivalMeasure (N := 2) θ (⋂ w ∈ (∅ : Finset Word), {c : Amb → ℕ | shapeAt c w = f w})
        = ∏ w ∈ (∅ : Finset Word), shapeMass θ (f w) := by
    intro f
    simp
  have hroot : ∀ f : Word → Shape,
      survivalMeasure (N := 2) θ (⋂ w ∈ ({[]} : Finset Word), {c : Amb → ℕ | shapeAt c w = f w})
        = ∏ w ∈ ({[]} : Finset Word), shapeMass θ (f w) := by
    intro f
    rw [Finset.prod_singleton, shapeMass]
    have hset : (⋂ w ∈ ({[]} : Finset Word), {c : Amb → ℕ | shapeAt c w = f w})
        = {c : Amb → ℕ | shapeAt c [] = f []} := by
      ext c
      simp
    rw [hset, survivalMeasure_shapeAt_nil θ hq hq0 h2]
  intro n
  induction n with
  | zero =>
      intro s hlen hs f
      rcases s.eq_empty_or_nonempty with rfl | hne
      · exact hempty f
      · have hsing : s = {[]} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨nil_mem_of_nonempty hs hne, ?_⟩
          intro w hw
          have := hlen w hw
          exact List.eq_nil_of_length_eq_zero (by omega)
        rw [hsing]
        exact hroot f
  | succ n ih =>
      intro s hlen hs f
      rcases s.eq_empty_or_nonempty with rfl | hne
      · exact hempty f
      have hnil : ([] : Word) ∈ s := nil_mem_of_nonempty hs hne
      set E₀ : Set (Amb → ℕ) :=
        ⋂ w ∈ subTree false s, {d : Amb → ℕ | shapeAt d w = f (false :: w)} with hE₀
      set E₁ : Set (Amb → ℕ) :=
        ⋂ w ∈ subTree true s, {d : Amb → ℕ | shapeAt d w = f (true :: w)} with hE₁
      have hmeas₀ : MeasurableSet E₀ := measurableSet_shapes _ _
      have hmeas₁ : MeasurableSet E₁ := measurableSet_shapes _ _
      have hinter : (⋂ w ∈ s, {c : Amb → ℕ | shapeAt c w = f w})
            ∩ {c : Amb → ℕ | IsHairySample c}
          = ({c : Amb → ℕ | shapeAt c [] = f []}
              ∩ ({c : Amb → ℕ | splitBush c 0 ∈ E₀} ∩ {c : Amb → ℕ | splitBush c 1 ∈ E₁}))
            ∩ {c : Amb → ℕ | IsHairySample c} := by
        ext c
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, hE₀, hE₁]
        constructor
        · rintro ⟨hall, hc⟩
          refine ⟨⟨hall [] hnil, fun w hw ↦ ?_, fun w hw ↦ ?_⟩, hc⟩
          · have hval := hall (false :: w) (mem_subTree.mp hw)
            rwa [shapeAt_cons hc false w] at hval
          · have hval := hall (true :: w) (mem_subTree.mp hw)
            rwa [shapeAt_cons hc true w] at hval
        · rintro ⟨⟨hr, h₀, h₁⟩, hc⟩
          refine ⟨fun w hw ↦ ?_, hc⟩
          cases w with
          | nil => exact hr
          | cons j w =>
              cases j with
              | false =>
                  rw [shapeAt_cons hc false w]
                  exact h₀ w (mem_subTree.mpr hw)
              | true =>
                  rw [shapeAt_cons hc true w]
                  exact h₁ w (mem_subTree.mpr hw)
      have hsub₀ := ih (subTree false s) (length_subTree hlen false)
        (prefixClosed_subTree hs false) (fun w ↦ f (false :: w))
      have hsub₁ := ih (subTree true s) (length_subTree hlen true)
        (prefixClosed_subTree hs true) (fun w ↦ f (true :: w))
      rw [measure_eq_of_inter_ae hnull hinter,
        survivalMeasure_shapeAt_nil_split θ hq hq0 h2 hmeas₀ hmeas₁ (f []),
        hE₀, hE₁, hsub₀, hsub₁, prod_decomp hnil (fun w ↦ shapeMass θ (f w)), shapeMass]

/-- **`thm:shape-iid`, the i.i.d. clause.** -/
theorem survivalMeasure_shapes (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (s : Finset Word)
    (hs : ∀ w ∈ s, ∀ p, p <+: w → p ∈ s) (f : Word → Shape) :
    survivalMeasure (N := 2) θ (⋂ w ∈ s, {c : Amb → ℕ | shapeAt c w = f w})
      = ∏ w ∈ s, shapeMass θ (f w) := by
  refine survivalMeasure_shapes_aux θ hq hq0 h2 (s.sup List.length) s (fun w hw ↦ ?_) hs f
  exact Finset.le_sup (f := List.length) hw

/-- **`thm:shape-iid`**: conditioned on survival the shapes of the copies are
independent with the law `μ`, and the sample is isometric to the assembly of its own
shapes. -/
theorem shape_decomposition (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) :
    (∀ s : Finset Word, (∀ w ∈ s, ∀ p, p <+: w → p ∈ s) → ∀ f : Word → Shape,
        survivalMeasure (N := 2) θ (⋂ w ∈ s, {c : Amb → ℕ | shapeAt c w = f w})
          = ∏ w ∈ s, shapeMass θ (f w))
      ∧ ∀ᵐ c ∂(survivalMeasure (N := 2) θ),
          ∃ Φ : Assembly (shapeAt c) → {v : Amb // v ∈ sample c}, Function.Bijective Φ ∧
            ∀ x y : Assembly (shapeAt c),
              (BranchingProcess.treeDist (Φ x).1 (Φ y).1 : ℝ) = dist x y :=
  ⟨fun s hs f ↦ survivalMeasure_shapes θ hq hq0 h2 s hs f,
    ae_assembly_isometric_sample θ hq h2⟩

end ChainClasses
