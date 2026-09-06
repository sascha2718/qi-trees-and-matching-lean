import ChainClasses.General.GeneralDecomposition
import ChainClasses.Bushy.ShapeRootLaw

/-!
`sec:general-relabel` of `matching_classes_general.tex`: the law of the shape at the
root of the reduced skeleton, jointly with the arity of its terminating split and the
subtrees below it.

The recursion is the one of `ShapeRootLaw` at general support, with the joint root step
of `BranchingProcess.Harris` in place of the hand-rolled two-letter case analysis: the
event that the root carries a prescribed skeleton degree and a prescribed list of dying
subtrees is exactly a decoration event, so `survivalMeasure_root_decorated` factors one
neck or split step off in one stroke.  A neck step carries `decorationMass` at one
survivor and hands the rest of the shape to the surviving subtree; the split step at
arity `κ` carries the exit bouquet and hands the `κ` subtrees below the split to the
constraint sets.  Junk is excluded by the events themselves: the arity clause `2 ≤ κ`
certifies the split, so the only almost-sure input is survival.

* `listSets`, `measurableSet_listSets`: a list of bushes as a rank-indexed family of
  constraint sets.
* `gDecList_eq_iff`, `gDecEvent_eq`: the bush list of the root as a decoration event.
* `survivalMeasure_gDec_step`: **the decorated step**, at any survivor count; above the
  alphabet bound both sides vanish.
* `gDecMass`, `gSplitMass`: the masses of a neck decoration and of a terminating split
  with its exit bouquet.
* `survivalMeasure_compl_survives`: survival is almost sure under the conditioned law.
* `measurableSet_decs_gShapeRoot`, `measurableSet_gSplitBush_box`: the events of the
  recursion are measurable.
* `survivalMeasure_gShapeSplit`: **the root law**: the shape of the root, its arity,
  and independent conditioned copies below the terminating split.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BranchingProcess (Survives skeletonDegree Offspring sampleMeasure survivalMeasure
  bushMeasure bushAt dyingAt decorationEvent decorationMass)

variable {J N : ℕ}

/-! ### A list of bushes as constraint sets -/

/-- The rank-indexed family of constraint sets reading a list of bushes: the `m`-th
dying subtree realises the `m`-th bush, and beyond the list nothing is asked. -/
def listSets (β : List RTree) : ℕ → Set (GWord N → ℕ) := fun m ↦
  if h : m < β.length then {d : GWord N → ℕ | bushRTree d = β[m]} else Set.univ

lemma measurableSet_listSets (β : List RTree) (m : ℕ) :
    MeasurableSet (listSets (N := N) β m) := by
  rw [listSets]
  split
  · exact fibreMeasurableG_bushRTree _
  · exact MeasurableSet.univ

/-- The bush list of the root, read entrywise. -/
lemma gDecList_eq_iff {c : GWord N → ℕ} {β : List RTree} :
    gDecList c = β
      ↔ c [] - skeletonDegree c = β.length
          ∧ ∀ (m : ℕ) (hm : m < β.length), bushRTree (dyingAt c m) = β[m] := by
  constructor
  · rintro rfl
    refine ⟨(length_gDecList c).symm, ?_⟩
    intro m hm
    exact (getElem_gDecList c hm).symm
  · rintro ⟨hlen, hval⟩
    refine List.ext_getElem (by rw [length_gDecList, hlen]) ?_
    intro m h1 h2
    exact (getElem_gDecList c h1).trans (hval m h2)

/-- **The bush list of the root is a decoration event**: prescribing the skeleton degree
and the dying subtrees of the root prescribes its offspring count, and the constraints
are the rank-indexed family of the list. -/
lemma gDecEvent_eq (k : ℕ) (β : List RTree) :
    ({c : GWord N → ℕ | skeletonDegree c = k} ∩ {c : GWord N → ℕ | gDecList c = β})
      = decorationEvent (N := N) (k + β.length) k (listSets (N := N) β) := by
  ext c
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, decorationEvent]
  constructor
  · rintro ⟨hdeg, hdec⟩
    obtain ⟨hlen, hval⟩ := gDecList_eq_iff.mp hdec
    have hle : skeletonDegree c ≤ c [] := skeletonDegree_le_root c
    have hroot : c [] = k + β.length := by omega
    refine ⟨⟨hroot, hdeg⟩, ?_⟩
    intro m hm
    have hm' : m < β.length := by omega
    rw [listSets, dif_pos hm']
    exact hval m hm'
  · rintro ⟨⟨hroot, hdeg⟩, hdy⟩
    refine ⟨hdeg, gDecList_eq_iff.mpr ⟨by omega, ?_⟩⟩
    intro m hm
    have hmem := hdy m (by omega)
    rwa [listSets, dif_pos hm] at hmem

/-! ### The decorated step -/

/-- **The decorated step**: conditioned on survival, the root has `k` surviving
children with the dying subtrees realising `β` at the mass of the decoration, and the
surviving subtrees are independent conditioned samples.  Above the alphabet bound both
sides vanish. -/
theorem survivalMeasure_gDec_step (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) {k : ℕ} (hk : k ≠ 0) (β : List RTree)
    {A : ℕ → Set (GWord N → ℕ)} (hA : ∀ m, MeasurableSet (A m)) :
    survivalMeasure (N := N) θ
        (({c : GWord N → ℕ | skeletonDegree c = k} ∩ {c : GWord N → ℕ | gDecList c = β})
          ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < k → bushAt c m ∈ A m})
      = decorationMass (N := N) θ (k + β.length) k (listSets (N := N) β)
          * ∏ m ∈ Finset.range k, survivalMeasure (N := N) θ (A m) := by
  rw [gDecEvent_eq]
  by_cases hjN : k + β.length ≤ N
  · exact BranchingProcess.survivalMeasure_root_decorated θ hJN hq hq0 hjN hk hA
      (measurableSet_listSets β)
  · have hLHS : survivalMeasure (N := N) θ
        (decorationEvent (k + β.length) k (listSets β)
          ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < k → bushAt c m ∈ A m}) = 0 := by
      refine measure_mono_null (fun c hc ↦ ?_)
        (BranchingProcess.survivalMeasure_coord_gt θ hJN [])
      have hroot : c [] = k + β.length := hc.1.1.1
      rw [Set.mem_setOf_eq, hroot]
      omega
    have hmass : decorationMass (N := N) θ (k + β.length) k (listSets β) = 0 := by
      rw [decorationMass, θ.vanishing (k + β.length) (by omega)]
      simp
    rw [hLHS, hmass, zero_mul]

/-! ### The masses of the shape -/

/-- **The mass of a neck decoration**: one survivor, and the dying subtrees realise the
bush list. -/
noncomputable def gDecMass (θ : Offspring J) (β : List RTree) : ℝ≥0∞ :=
  decorationMass (N := N) θ (1 + β.length) 1 (listSets β)

lemma gDecMass_def (θ : Offspring J) (β : List RTree) :
    gDecMass (N := N) θ β
      = decorationMass (N := N) θ (1 + β.length) 1 (listSets (N := N) β) := rfl

/-- **The mass of a terminating split**: `κ` survivors, and the dying subtrees realise
the exit bouquet. -/
noncomputable def gSplitMass (θ : Offspring J) (κ : ℕ) (β : List RTree) : ℝ≥0∞ :=
  decorationMass (N := N) θ (κ + β.length) κ (listSets β)

lemma gSplitMass_def (θ : Offspring J) (κ : ℕ) (β : List RTree) :
    gSplitMass (N := N) θ κ β
      = decorationMass (N := N) θ (κ + β.length) κ (listSets (N := N) β) := rfl

/-- Survival is almost sure under the conditioned law. -/
lemma survivalMeasure_compl_survives (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) :
    survivalMeasure (N := N) θ {c : GWord N → ℕ | Survives c}ᶜ = 0 := by
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  rw [measure_compl BranchingProcess.measurableSet_survives (measure_ne_top _ _),
    BranchingProcess.survivalMeasure_survives θ hJN hq, measure_univ, tsub_self]

/-! ### The events of the recursion are measurable -/

lemma measurableSet_decs_gShapeRoot (D : List (List RTree)) :
    MeasurableSet {c : GWord N → ℕ | (gShapeRoot c).decs = D} :=
  fibreMeasurableG_gShapeRoot.preimage {σ : GShape | σ.decs = D}

lemma measurableSet_gSplitBush_box {κ : ℕ} {A : ℕ → Set (GWord N → ℕ)}
    (hA : ∀ m, MeasurableSet (A m)) :
    MeasurableSet {c : GWord N → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m} := by
  have he : {c : GWord N → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m}
      = ⋂ m ∈ Finset.range κ, (fun c : GWord N → ℕ ↦ gSplitBush c m) ⁻¹' (A m) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
  rw [he]
  exact MeasurableSet.biInter (Set.to_countable _)
    fun m _ ↦ measurable_gSplitBush m (hA m)

/-! ### The root law -/

/-- **The root law**: conditioned on survival, the shape of the root carries one
decoration mass per neck vertex and the split mass of its exit bouquet at the
prescribed arity, and the subtrees below the terminating split are independent copies
of the conditioned law. -/
theorem survivalMeasure_gShapeSplit (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (L : List (List RTree))
    (β : List RTree) {κ : ℕ} (hκ : 2 ≤ κ) {A : ℕ → Set (GWord N → ℕ)}
    (hA : ∀ m, MeasurableSet (A m)) :
    survivalMeasure (N := N) θ
        (({c : GWord N → ℕ | (gShapeRoot c).decs = L ++ [β]}
            ∩ {c : GWord N → ℕ | gArity c = κ})
          ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m})
      = (L.map (gDecMass (N := N) θ)).prod * gSplitMass (N := N) θ κ β
          * ∏ m ∈ Finset.range κ, survivalMeasure (N := N) θ (A m) := by
  induction L with
  | nil =>
      have hset : (({c : GWord N → ℕ | (gShapeRoot c).decs = [] ++ [β]}
            ∩ {c : GWord N → ℕ | gArity c = κ})
          ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m})
          = (({c : GWord N → ℕ | skeletonDegree c = κ}
              ∩ {c : GWord N → ℕ | gDecList c = β})
            ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < κ → bushAt c m ∈ A m}) := by
        ext c
        simp only [List.nil_append, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨hdecs, harity⟩, hbush⟩
          obtain ⟨hdeg, hdec⟩ := (gShapeRoot_split_iff hκ).mp ⟨hdecs, harity⟩
          have hzero : gSplitDepth c = 0 := gSplitDepth_eq_zero (by omega)
          refine ⟨⟨hdeg, hdec⟩, fun m hm ↦ ?_⟩
          have hmem := hbush m hm
          rwa [gSplitBush, gSplitField_of_depth_zero hzero] at hmem
        · rintro ⟨⟨hdeg, hdec⟩, hbush⟩
          obtain ⟨hdecs, harity⟩ := (gShapeRoot_split_iff hκ).mpr ⟨hdeg, hdec⟩
          have hzero : gSplitDepth c = 0 := gSplitDepth_eq_zero (by omega)
          refine ⟨⟨hdecs, harity⟩, fun m hm ↦ ?_⟩
          rw [gSplitBush, gSplitField_of_depth_zero hzero]
          exact hbush m hm
      rw [hset, survivalMeasure_gDec_step θ hJN hq hq0 (by omega) β hA]
      rw [List.map_nil, List.prod_nil, one_mul, gSplitMass_def]
  | cons β' L ih =>
      have hnull := survivalMeasure_compl_survives θ hJN hq
      set E : Set (GWord N → ℕ) :=
        (({c : GWord N → ℕ | (gShapeRoot c).decs = L ++ [β]}
            ∩ {c : GWord N → ℕ | gArity c = κ})
          ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m}) with hE
      have hEmeas : MeasurableSet E :=
        ((measurableSet_decs_gShapeRoot (L ++ [β])).inter
          (fibreMeasurableG_gArity κ)).inter (measurableSet_gSplitBush_box hA)
      have hAmeas : ∀ m : ℕ,
          MeasurableSet (if m = 0 then E else (Set.univ : Set (GWord N → ℕ))) := by
        intro m
        split
        · exact hEmeas
        · exact MeasurableSet.univ
      have hM : L ++ [β] ≠ [] := by
        cases L <;> simp
      have hset : ((({c : GWord N → ℕ | (gShapeRoot c).decs = (β' :: L) ++ [β]}
              ∩ {c : GWord N → ℕ | gArity c = κ})
            ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m})
          ∩ {c : GWord N → ℕ | Survives c})
          = ((({c : GWord N → ℕ | skeletonDegree c = 1}
                ∩ {c : GWord N → ℕ | gDecList c = β'})
              ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < 1 → bushAt c m
                  ∈ (if m = 0 then E else Set.univ)})
            ∩ {c : GWord N → ℕ | Survives c}) := by
        ext c
        simp only [List.cons_append, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨⟨hdecs, harity⟩, hbush⟩, hsurv⟩
          obtain ⟨hdeg, hdec, hin⟩ := (gShapeRoot_neck_iff hsurv hM hκ A).mp
            ⟨hdecs, harity, hbush⟩
          refine ⟨⟨⟨hdeg, hdec⟩, ?_⟩, hsurv⟩
          intro m hm
          have hm0 : m = 0 := by omega
          subst hm0
          rw [if_pos rfl, hE]
          exact ⟨⟨hin.1, hin.2.1⟩, hin.2.2⟩
        · rintro ⟨⟨⟨hdeg, hdec⟩, hbush⟩, hsurv⟩
          have hmem := hbush 0 (by omega)
          rw [if_pos rfl, hE] at hmem
          obtain ⟨⟨hdecs', harity'⟩, hbush'⟩ := hmem
          obtain ⟨hdecs, harity, hbushA⟩ := (gShapeRoot_neck_iff hsurv hM hκ A).mpr
            ⟨hdeg, hdec, hdecs', harity', hbush'⟩
          exact ⟨⟨⟨hdecs, harity⟩, hbushA⟩, hsurv⟩
      rw [measure_eq_of_inter_ae hnull hset,
        survivalMeasure_gDec_step θ hJN hq hq0 one_ne_zero β' hAmeas,
        Finset.prod_range_one, if_pos rfl, hE, ih, List.map_cons, List.prod_cons,
        ← gDecMass_def]
      ring

end ChainClasses
