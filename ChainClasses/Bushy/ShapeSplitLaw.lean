import ChainClasses.Bushy.ShapeRootLaw

/-!
`sec:shape-harris` of `matching_classes_simple.tex`: the shape at the root jointly with
the two subtrees below its split, and the shape field of those subtrees.

`ShapeRootLaw` has the law of the shape at the root.  The i.i.d. clause of
`thm:shape-iid` needs that law jointly with what the sample carries below the split
ending the chain of the root, since the copies at `w1` and `w2` and everything under them
live there.  The recursion is the one of `ShapeRootLaw` with the two subtrees carried
along: they are unchanged by a neck step, so they pass through the induction untouched,
and at the split, where the chain ends, they are the two surviving subtrees of
`survivalMeasure_skeletonDegree_bushes` at `k = 2`, independent copies of the conditioned
law.

The last section is the deterministic half of the induction over the index tree: the
shape at a copy below the root is the shape of the same copy read in the subtree the
split hands it, so the shape field of a sample is its root shape together with the two
shape fields below.

* `splitVert`, `splitField`, `splitBush`: the split ending the chain of the root and the
  two subtrees below it, with `measurable_splitBush`.
* `splitField_bushAt`, `splitBush_bushAt`: a neck step leaves them unchanged.
* `splitDepth_eq_zero_iff`, `splitField_of_splitDepth_zero`: a chain of one vertex is a
  split, and then the root is its own split vertex.
* `shapeSplitEvent`, `survivalMeasure_shapeSplitEvent` and
  `survivalMeasure_shapeAt_nil_split`: **the root decomposition**, the mass of
  `thm:shape-iid` for the root shape times the conditioned masses of the two subtrees.
* `splitDepth_shift`, `entryV_foldl`, `entryV_cons`, `bushAt_of_deg_two`: the entry map
  read in a subtree, and the two children of a split.
* `shapeAt_cons`: **the shape field below the split**, `shapeAt c (j :: w)` read in the
  subtree the split hands to `j`.  With the root decomposition this is what an induction
  over finite prefix-closed sets of copies consumes.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (sample Survives survivors skeletonDegree Offspring sampleMeasure
  survivalMeasure bushMeasure bushAt)

/-! ### The subtrees below the split -/

/-- The vertex ending the chain of the root: the first split along its neck ray. -/
noncomputable def splitVert (c : Amb → ℕ) : Amb := neckRay c [] (splitDepth c [])

/-- The field of the subtree at that split. -/
noncomputable def splitField (c : Amb → ℕ) : Amb → ℕ := shift c (splitVert c)

/-- **The two subtrees below the split ending the chain of the root**: the copies the
assembly plants at `w1` and `w2`. -/
noncomputable def splitBush (c : Amb → ℕ) (m : ℕ) : Amb → ℕ := bushAt (splitField c) m

/-- Shifting to a countably valued vertex is measurable. -/
lemma measurable_shift_of_fibreMeasurable {g : (Amb → ℕ) → Amb} (hg : FibreMeasurable g) :
    Measurable (fun c ↦ shift c (g c)) := by
  intro T hT
  have he : (fun c ↦ shift c (g c)) ⁻¹' T
      = ⋃ v : Amb, ({c : Amb → ℕ | g c = v} ∩ (fun c : Amb → ℕ ↦ shift c v) ⁻¹' T) := by
    ext c
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun h ↦ ⟨g c, rfl, h⟩, by rintro ⟨v, rfl, h⟩; exact h⟩
  rw [he]
  exact MeasurableSet.iUnion fun v ↦ (hg v).inter (measurable_shiftMap v hT)

lemma fibreMeasurable_splitVert : FibreMeasurable splitVert :=
  FibreMeasurable.comp (h := fun n c ↦ neckRay c [] n) (fibreMeasurable_splitDepth [])
    fun n ↦ fibreMeasurable_neckRay [] n

lemma measurable_splitField : Measurable (splitField : (Amb → ℕ) → Amb → ℕ) :=
  measurable_shift_of_fibreMeasurable fibreMeasurable_splitVert

lemma measurable_splitBush (m : ℕ) : Measurable (fun c : Amb → ℕ ↦ splitBush c m) :=
  (BranchingProcess.measurable_bushAt m).comp measurable_splitField

/-- At a neck vertex the split ending the chain is the split ending the chain of the
surviving subtree. -/
lemma splitField_bushAt {c : Amb → ℕ} (hc : IsBushySample c) (hdeg : skeletonDegree c = 1) :
    splitField c = splitField (bushAt c 0) := by
  rw [splitField, splitField, splitVert, splitVert, splitDepth_bushAt hc hdeg,
    shift_neckRay_succ hdeg]

lemma splitBush_bushAt {c : Amb → ℕ} (hc : IsBushySample c) (hdeg : skeletonDegree c = 1)
    (m : ℕ) : splitBush c m = splitBush (bushAt c 0) m := by
  rw [splitBush, splitBush, splitField_bushAt hc hdeg]

/-- A root that splits at once is its own split vertex. -/
lemma splitField_of_splitDepth_zero {c : Amb → ℕ} (h : splitDepth c [] = 0) :
    splitField c = c := by
  rw [splitField, splitVert, h, neckRay_zero, shift_nil]

/-- On the hypotheses of `sec:shapes` a chain of one vertex is a split. -/
lemma splitDepth_eq_zero_iff {c : Amb → ℕ} (hc : IsBushySample c) :
    splitDepth c [] = 0 ↔ skeletonDegree c = 2 := by
  have hroot : Survives (shift c []) := by simpa using hc.survives
  constructor
  · intro h
    have hmem : 2 ≤ skeletonDegree (shift c (neckRay c [] (splitDepth c []))) :=
      Nat.sInf_mem (hc.splits [] hroot)
    rw [h, neckRay_zero, shift_nil] at hmem
    have := skeletonDegree_le_two c
    omega
  · intro h
    have hmem : (0 : ℕ) ∈ {k | 2 ≤ skeletonDegree (shift c (neckRay c [] k))} := by
      simp only [Set.mem_setOf_eq, neckRay_zero, shift_nil, h]
      omega
    exact Nat.le_zero.mp (Nat.sInf_le hmem)

/-! ### The shape at the root and the two subtrees below it -/

variable {A₀ A₁ : Set (Amb → ℕ)}

/-- The event that the root carries the decoration list `l` and the two subtrees below
its split lie in `A₀` and `A₁`. -/
def shapeSplitEvent (A₀ A₁ : Set (Amb → ℕ)) (l : List (Option Tri)) : Set (Amb → ℕ) :=
  {c : Amb → ℕ | (shapeAt c []).decs = l}
    ∩ ({c : Amb → ℕ | splitBush c 0 ∈ A₀} ∩ {c : Amb → ℕ | splitBush c 1 ∈ A₁})

lemma measurableSet_shapeSplitEvent (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (l : List (Option Tri)) : MeasurableSet (shapeSplitEvent A₀ A₁ l) :=
  (measurableSet_decs_shapeAt_nil l).inter
    ((measurable_splitBush 0 hA₀).inter (measurable_splitBush 1 hA₁))

/-- **The root decomposition**: conditioned on survival, the shape of the root carries
the mass of `thm:shape-iid` and the two subtrees below its split are independent copies
of the conditioned law. -/
theorem survivalMeasure_shapeSplitEvent (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (l : List (Option Tri)) :
    survivalMeasure (N := 2) θ (shapeSplitEvent A₀ A₁ l)
      = (l.map (decMass θ)).prod * ENNReal.ofReal (θ.skeletonWeight 2)
          * survivalMeasure (N := 2) θ A₀ * survivalMeasure (N := 2) θ A₁ := by
  have hnull : survivalMeasure (N := 2) θ {c : Amb → ℕ | IsBushySample c}ᶜ = 0 := by
    have hae := ae_isBushySample_of_pos θ hq h2
    rw [ae_iff] at hae
    exact hae
  induction l with
  | nil =>
      set A : ℕ → Set (Amb → ℕ) :=
        fun m ↦ if m = 0 then A₀ else if m = 1 then A₁ else Set.univ with hAdef
      have hAmeas : ∀ m, MeasurableSet (A m) := by
        intro m
        rw [hAdef]
        by_cases h0 : m = 0
        · simp only [if_pos h0]
          exact hA₀
        · by_cases h1 : m = 1
          · simp only [if_neg h0, if_pos h1]
            exact hA₁
          · simp only [if_neg h0, if_neg h1]
            exact MeasurableSet.univ
      have hset : shapeSplitEvent A₀ A₁ [] ∩ {c : Amb → ℕ | IsBushySample c}
          = ({c : Amb → ℕ | skeletonDegree c = 2}
              ∩ {c : Amb → ℕ | ∀ m : ℕ, m < 2 → bushAt c m ∈ A m})
            ∩ {c : Amb → ℕ | IsBushySample c} := by
        ext c
        simp only [shapeSplitEvent, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨hdecs, hb₀, hb₁⟩, hc⟩
          have hzero : splitDepth c [] = 0 := by
            have hlen := congrArg List.length hdecs
            rw [decs_shapeAt_nil, List.length_ofFn] at hlen
            simpa using hlen
          have hfield : splitField c = c := splitField_of_splitDepth_zero hzero
          rw [splitBush, hfield] at hb₀ hb₁
          refine ⟨⟨(splitDepth_eq_zero_iff hc).mp hzero, fun m hm ↦ ?_⟩, hc⟩
          interval_cases m
          · rw [hAdef]
            simpa using hb₀
          · rw [hAdef]
            simpa using hb₁
        · rintro ⟨⟨hdeg, hbush⟩, hc⟩
          have hzero : splitDepth c [] = 0 := (splitDepth_eq_zero_iff hc).mpr hdeg
          have hfield : splitField c = c := splitField_of_splitDepth_zero hzero
          have hdecs : (shapeAt c []).decs = [] := by
            have hlen : (shapeAt c []).decs.length = 0 := by
              rw [decs_shapeAt_nil, List.length_ofFn, hzero]
            exact List.eq_nil_of_length_eq_zero hlen
          have hb₀ := hbush 0 (by omega)
          have hb₁ := hbush 1 (by omega)
          simp only [hAdef] at hb₀ hb₁
          norm_num at hb₀ hb₁
          refine ⟨⟨hdecs, ?_, ?_⟩, hc⟩
          · rw [splitBush, hfield]
            exact hb₀
          · rw [splitBush, hfield]
            exact hb₁
      have hprod : ∏ m ∈ Finset.range 2, survivalMeasure (N := 2) θ (A m)
          = survivalMeasure (N := 2) θ A₀ * survivalMeasure (N := 2) θ A₁ := by
        rw [Finset.prod_range_succ, Finset.prod_range_one, hAdef]
        simp
      rw [measure_eq_of_inter_ae hnull hset,
        BranchingProcess.survivalMeasure_skeletonDegree_bushes θ le_rfl hq 2 hAmeas, hprod]
      simp only [List.map_nil, List.prod_nil, one_mul]
      ring
  | cons o l ih =>
      have hset : shapeSplitEvent A₀ A₁ (o :: l) ∩ {c : Amb → ℕ | IsBushySample c}
          = (({c : Amb → ℕ | skeletonDegree c = 1} ∩ {c : Amb → ℕ | decAt c [] = o})
              ∩ {c : Amb → ℕ | bushAt c 0 ∈ shapeSplitEvent A₀ A₁ l})
            ∩ {c : Amb → ℕ | IsBushySample c} := by
        ext c
        simp only [shapeSplitEvent, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨hdecs, hb₀, hb₁⟩, hc⟩
          obtain ⟨hdeg, hdec, htail⟩ := (decs_shapeAt_nil_cons hc o l).mp hdecs
          refine ⟨⟨⟨hdeg, hdec⟩, htail, ?_, ?_⟩, hc⟩
          · rwa [← splitBush_bushAt hc hdeg]
          · rwa [← splitBush_bushAt hc hdeg]
        · rintro ⟨⟨⟨hdeg, hdec⟩, htail, hb₀, hb₁⟩, hc⟩
          refine ⟨⟨(decs_shapeAt_nil_cons hc o l).mpr ⟨hdeg, hdec, htail⟩, ?_, ?_⟩, hc⟩
          · rwa [splitBush_bushAt hc hdeg]
          · rwa [splitBush_bushAt hc hdeg]
      rw [measure_eq_of_inter_ae hnull hset,
        survivalMeasure_neck_step θ hq hq0 h2 o (measurableSet_shapeSplitEvent hA₀ hA₁ l), ih,
        List.map_cons, List.prod_cons]
      ring

/-- **The root decomposition**, read off the shape itself. -/
theorem survivalMeasure_shapeAt_nil_split (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (σ : Shape) :
    survivalMeasure (N := 2) θ
        ({c : Amb → ℕ | shapeAt c [] = σ}
          ∩ ({c : Amb → ℕ | splitBush c 0 ∈ A₀} ∩ {c : Amb → ℕ | splitBush c 1 ∈ A₁}))
      = (σ.decs.map (decMass θ)).prod * ENNReal.ofReal (θ.skeletonWeight 2)
          * survivalMeasure (N := 2) θ A₀ * survivalMeasure (N := 2) θ A₁ := by
  have he : {c : Amb → ℕ | shapeAt c [] = σ} = {c : Amb → ℕ | (shapeAt c []).decs = σ.decs} := by
    ext c
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h ↦ by rw [h], fun h ↦ Shape.eq_of_decs h⟩
  rw [he]
  exact survivalMeasure_shapeSplitEvent θ hq hq0 h2 hA₀ hA₁ σ.decs

/-! ### The shape field below the split -/

/-- The chain length of a vertex is read in the subtree it sits in. -/
lemma splitDepth_shift (c : Amb → ℕ) (u v : Amb) :
    splitDepth c (u ++ v) = splitDepth (shift c u) v := by
  have hset : {k | 2 ≤ skeletonDegree (shift c (neckRay c (u ++ v) k))}
      = {k | 2 ≤ skeletonDegree (shift (shift c u) (neckRay (shift c u) v k))} := by
    ext k
    simp only [Set.mem_setOf_eq, ← neckRay_shift_base c u v k, shift_shift]
  rw [splitDepth, splitDepth, hset]

lemma splitDepth_shift_nil (c : Amb → ℕ) (u : Amb) :
    splitDepth c u = splitDepth (shift c u) [] := by
  have h := splitDepth_shift c u []
  rwa [List.append_nil] at h

/-- The entry vertex of a copy below the root, read in the subtree the copy sits in. -/
lemma entryV_foldl : ∀ (w : Word) (c : Amb → ℕ) (u : Amb),
    w.foldl (fun v j ↦ neckRay c v (splitDepth c v) ++ [letterOf j]) u
      = u ++ entryV (shift c u) w
  | [], c, u => by simp [entryV]
  | j :: w, c, u => by
      have hnr : neckRay c u (splitDepth c u)
          = u ++ neckRay (shift c u) [] (splitDepth (shift c u) []) := by
        rw [splitDepth_shift_nil c u]
        exact neckRay_shift c u _
      have hstep : neckRay c u (splitDepth c u) ++ [letterOf j]
          = u ++ (neckRay (shift c u) [] (splitDepth (shift c u) []) ++ [letterOf j]) := by
        rw [hnr, List.append_assoc]
      have hrhs : entryV (shift c u) (j :: w)
          = (neckRay (shift c u) [] (splitDepth (shift c u) []) ++ [letterOf j])
            ++ entryV (shift (shift c u)
                (neckRay (shift c u) [] (splitDepth (shift c u) []) ++ [letterOf j])) w := by
        rw [entryV, List.foldl_cons, entryV_foldl w (shift c u)
          (neckRay (shift c u) [] (splitDepth (shift c u) []) ++ [letterOf j])]
      rw [List.foldl_cons, hstep, entryV_foldl w c
        (u ++ (neckRay (shift c u) [] (splitDepth (shift c u) []) ++ [letterOf j])),
        hrhs, ← shift_shift, List.append_assoc]

/-- The recursion of the entry map at the first letter. -/
lemma entryV_cons (c : Amb → ℕ) (j : Bool) (w : Word) :
    entryV c (j :: w)
      = (splitVert c ++ [letterOf j])
        ++ entryV (shift c (splitVert c ++ [letterOf j])) w := by
  rw [entryV, List.foldl_cons, entryV_foldl w c _]
  rfl

/-- At a split the surviving subtrees are the two children. -/
lemma bushAt_of_deg_two {d : Amb → ℕ} (h : skeletonDegree d = 2) (i : Fin 2) :
    bushAt d (i : ℕ) = shift d [i] := by
  have huniv : survivors d = Finset.univ := survivors_eq_univ h
  have hcard : ((i : ℕ)) < (survivors d).card := by
    rw [huniv]
    simpa using i.isLt
  have hval : (survivors d).orderEmbOfFin rfl ⟨(i : ℕ), hcard⟩ = i := by
    set x := (survivors d).orderEmbOfFin rfl ⟨(i : ℕ), hcard⟩ with hx
    have h1 : BranchingProcess.rankOf (survivors d) x = (i : ℕ) :=
      BranchingProcess.rankOf_orderEmbOfFin _ rfl _
    have h2 : BranchingProcess.rankOf (survivors d) x
        = BranchingProcess.rankOf Finset.univ x :=
      congrArg (fun S ↦ BranchingProcess.rankOf S x) huniv
    rw [h2, BranchingProcess.rankOf_univ] at h1
    exact Fin.ext h1
  rw [BranchingProcess.bushAt_of_lt hcard]
  funext w
  rw [shift_apply, hval]
  rfl

/-- **The shape field below the split**: the shapes of the copies under the first letter
are the shapes of the subtree the split hands them. -/
theorem shapeAt_cons {c : Amb → ℕ} (hc : IsBushySample c) (j : Bool) (w : Word) :
    shapeAt c (j :: w) = shapeAt (splitBush c (letterOf j : ℕ)) w := by
  have hroot : Survives (shift c []) := by simpa using hc.survives
  have hdeg : skeletonDegree (splitField c) = 2 := splitDepth_spec hc hroot
  have hbush : splitBush c (letterOf j : ℕ) = shift c (splitVert c ++ [letterOf j]) := by
    rw [splitBush, bushAt_of_deg_two hdeg (letterOf j), splitField, shift_shift]
  set u := splitVert c ++ [letterOf j] with hu
  set d := shift c u with hd
  have hentry : entryV c (j :: w) = u ++ entryV d w := entryV_cons c j w
  rw [hbush]
  refine Shape.eq_of_decs ?_
  rw [shapeAt_decs, shapeAt_decs, hentry, splitDepth_shift]
  exact congrArg List.ofFn (funext fun i : Fin (splitDepth d (entryV d w)) ↦ by
    rw [← neckRay_shift_base c u (entryV d w) i, decAt_shift])

end ChainClasses
