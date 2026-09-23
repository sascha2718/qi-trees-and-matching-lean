import ChainClasses.General.GeneralShapeLaw

/-!
`sec:general-relabel` of `matching_classes_general.tex`: **`thm:conditional-iid`** in
full, over the constructed space.

The root law of `GeneralShapeLaw` is iterated over a prefix-closed finite set of
reduced-skeleton addresses, as `ShapeIID` iterates the `N = 2` root law over the copies:
probing every address with a shape and an arity, the mass factorises into one
`gPairMass` per address.  Summing the neck length out of the same recursion gives the
arity field alone: the arities are independent with the reduced law `ν̃` of
`thm:harris-general`, the geometric neck series folding into the weight
`θ̃_κ/(1-θ̃₁)`.  Dividing the two identities is the paper's statement: conditioned on
the arity field, the shapes are independent with `S(w) ∼ μ_{k(w)}`.

* `gPairMass`, `survivalMeasure_gShapePair`: the joint mass of a shape and an arity,
  and the root law read off the shape itself.
* `survivalMeasure_gShapes`: **the joint product formula**, shapes and arities over a
  prefix-closed probe.
* `gArityDepthEvent` with its recursion and mass: the arity probe at a fixed neck
  length.
* `reducedWeight`, `survivalMeasure_gArityPair`: the reduced law `ν̃` at the root, by
  the geometric series over the neck length.
* `survivalMeasure_gArities`: **the arity field is i.i.d. `ν̃`**,
  `thm:harris-general` (`it:harris-general-reduced`) over reduced-skeleton
  probes.
* `skeletonWeight_pos`, `skeletonWeight_one_lt_one_of`, `reducedWeight_pos`:
  `thm:full-support` on the constructed space.
* `gCondMass`, `conditional_iid`: **`thm:conditional-iid`**, the conditional shape
  laws `μ_κ` and the conditional independence given the arity field.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BranchingProcess (Survives skeletonDegree Offspring sampleMeasure survivalMeasure
  bushMeasure bushAt consSub mem_consSub prod_cons_decomp)

variable {J N : ℕ}

/-! ### The joint mass of a shape and an arity -/

/-- **The joint mass of a shape and an arity**: one decoration mass per neck vertex and
the split mass of the exit bouquet at the arity. -/
noncomputable def gPairMass (θ : Offspring J) (κ : ℕ) (σ : GShape) : ℝ≥0∞ :=
  (σ.neckList.map (gDecMass (N := N) θ)).prod * gSplitMass (N := N) θ κ σ.bouquet

lemma gPairMass_def (θ : Offspring J) (κ : ℕ) (σ : GShape) :
    gPairMass (N := N) θ κ σ
      = (σ.neckList.map (gDecMass (N := N) θ)).prod
          * gSplitMass (N := N) θ κ σ.bouquet := rfl

/-- **The root law, read off the shape itself**: the shape of the root and the arity of
its terminating split carry the joint mass, and the subtrees below the split are
independent conditioned samples. -/
theorem survivalMeasure_gShapePair (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) (σ : GShape) {κ : ℕ} (hκ : 2 ≤ κ)
    {A : ℕ → Set (GWord N → ℕ)} (hA : ∀ m, MeasurableSet (A m)) :
    survivalMeasure (N := N) θ
        (({c : GWord N → ℕ | gShapeRoot c = σ} ∩ {c : GWord N → ℕ | gArity c = κ})
          ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m})
      = gPairMass (N := N) θ κ σ
          * ∏ m ∈ Finset.range κ, survivalMeasure (N := N) θ (A m) := by
  have he : {c : GWord N → ℕ | gShapeRoot c = σ}
      = {c : GWord N → ℕ | (gShapeRoot c).decs = σ.decs} := by
    ext c
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h ↦ by rw [h], fun h ↦ GShape.eq_of_decs h⟩
  rw [he, show σ.decs = σ.neckList ++ [σ.bouquet] from σ.decs_eq_append,
    survivalMeasure_gShapeSplit θ hJN hq hq0 σ.neckList σ.bouquet hκ hA, gPairMass_def]

/-! ### The joint product formula -/

/-- **`thm:conditional-iid`, the joint product formula**: probed on a prefix-closed
finite set of reduced-skeleton addresses whose letters respect the prescribed arities,
the shapes and arities are independent, one `gPairMass` per address. -/
theorem survivalMeasure_gShapes_aux (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction) :
    ∀ (n : ℕ) (F : Finset (GWord N)), (∀ u ∈ F, u.length ≤ n) →
      (∀ u ∈ F, ∀ p : GWord N, p <+: u → p ∈ F) →
      ∀ (f : GWord N → GShape) (k : GWord N → ℕ),
        (∀ u ∈ F, 2 ≤ k u) →
        (∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < k u) →
        survivalMeasure (N := N) θ
            (⋂ u ∈ F, ({c : GWord N → ℕ | gShapeAt c u = f u}
              ∩ {c : GWord N → ℕ | gArityAt c u = k u}))
          = ∏ u ∈ F, gPairMass (N := N) θ (k u) (f u) := by
  classical
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  intro n
  induction n with
  | zero =>
      intro F hlen hpc f k hk2 hcomp
      rcases F.eq_empty_or_nonempty with rfl | hne
      · simp
      · obtain ⟨v, hv⟩ := hne
        have hroot : ([] : GWord N) ∈ F := hpc v hv [] List.nil_prefix
        have hF : F = {[]} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hroot, fun v' hv' ↦ ?_⟩
          exact List.length_eq_zero_iff.mp (Nat.le_zero.mp (hlen v' hv'))
        subst hF
        have hset : (⋂ u ∈ ({[]} : Finset (GWord N)),
              ({c : GWord N → ℕ | gShapeAt c u = f u}
                ∩ {c : GWord N → ℕ | gArityAt c u = k u}))
            = (({c : GWord N → ℕ | gShapeRoot c = f []}
                ∩ {c : GWord N → ℕ | gArity c = k []})
              ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < k [] →
                  gSplitBush c m ∈ (Set.univ : Set (GWord N → ℕ))}) := by
          ext c
          simp
        rw [hset, survivalMeasure_gShapePair θ hJN hq hq0 (f []) (hk2 [] hroot)
          (fun _ ↦ MeasurableSet.univ), Finset.prod_singleton]
        simp
  | succ n ih =>
      intro F hlen hpc f k hk2 hcomp
      rcases F.eq_empty_or_nonempty with rfl | hne
      · simp
      · obtain ⟨v, hv⟩ := hne
        have hroot : ([] : GWord N) ∈ F := hpc v hv [] List.nil_prefix
        set E : Fin N → Set (GWord N → ℕ) := fun i ↦
          ⋂ u ∈ consSub i F,
            ({d : GWord N → ℕ | gShapeAt d u = f (i :: u)}
              ∩ {d : GWord N → ℕ | gArityAt d u = k (i :: u)}) with hE
        have hconsEmpty : ∀ i : Fin N, k [] ≤ (i : ℕ) → consSub i F = ∅ := by
          intro i hi
          rw [Finset.eq_empty_iff_forall_notMem]
          intro u hu
          have h1 : [i] ∈ F := hpc _ (mem_consSub.mp hu) [i] ⟨u, rfl⟩
          have h2 := hcomp [] hroot i (by simpa using h1)
          omega
        set A : ℕ → Set (GWord N → ℕ) :=
          fun m ↦ if h : m < N then E ⟨m, h⟩ else Set.univ with hA
        have hAmeas : ∀ m, MeasurableSet (A m) := by
          intro m
          simp only [hA]
          split
          · exact MeasurableSet.biInter (consSub _ F).countable_toSet fun u _ ↦
              (fibreMeasurableG_gShapeAt u _).inter (fibreMeasurableG_gArityAt u _)
          · exact MeasurableSet.univ
        have hset : (⋂ u ∈ F, ({c : GWord N → ℕ | gShapeAt c u = f u}
              ∩ {c : GWord N → ℕ | gArityAt c u = k u}))
            = (({c : GWord N → ℕ | gShapeRoot c = f []}
                ∩ {c : GWord N → ℕ | gArity c = k []})
              ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < k [] → gSplitBush c m ∈ A m}) := by
          ext c
          simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq]
          constructor
          · intro h
            obtain ⟨hs0, ha0⟩ := h [] hroot
            refine ⟨⟨hs0, ha0⟩, fun m hm ↦ ?_⟩
            simp only [hA]
            split
            · rename_i hmN
              simp only [hE, Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq]
              intro u hu
              exact h (⟨m, hmN⟩ :: u) (mem_consSub.mp hu)
            · exact Set.mem_univ _
          · rintro ⟨⟨hs0, ha0⟩, hrest⟩ u hu
            cases u with
            | nil => exact ⟨hs0, ha0⟩
            | cons i u =>
                by_cases hik : (i : ℕ) < k []
                · have hm := hrest (i : ℕ) hik
                  simp only [hA] at hm
                  rw [dite_eq_left i.isLt, Fin.eta] at hm
                  simp only [hE, Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq] at hm
                  exact hm u (mem_consSub.mpr hu)
                · exact absurd (mem_consSub.mpr hu)
                    (by rw [hconsEmpty i (not_lt.mp hik)]; exact Finset.notMem_empty u)
        have hstep := survivalMeasure_gShapePair θ hJN hq hq0 (f []) (hk2 [] hroot) hAmeas
        set G : ℕ → ℝ≥0∞ := fun m ↦ if h : m < N then
            ∏ u ∈ consSub ⟨m, h⟩ F, gPairMass (N := N) θ (k (⟨m, h⟩ :: u)) (f (⟨m, h⟩ :: u))
          else 1 with hGdef
        have hrec : ∀ m : ℕ, survivalMeasure (N := N) θ (A m) = G m := by
          intro m
          simp only [hA, hGdef]
          split
          · rename_i hmN
            simp only [hE]
            refine ih (consSub ⟨m, hmN⟩ F) (fun u hu ↦ ?_) (fun u hu p hp ↦ ?_)
              (fun u ↦ f (⟨m, hmN⟩ :: u)) (fun u ↦ k (⟨m, hmN⟩ :: u))
              (fun _ hu ↦ hk2 _ (mem_consSub.mp hu)) (fun u hu i hi ↦ ?_)
            · have := hlen _ (mem_consSub.mp hu)
              simpa using this
            · exact mem_consSub.mpr
                (hpc _ (mem_consSub.mp hu) _ (List.cons_prefix_cons.mpr ⟨rfl, hp⟩))
            · exact hcomp _ (mem_consSub.mp hu) i (mem_consSub.mp hi)
          · exact measure_univ
        have hG : ∀ i : Fin N,
            ∏ u ∈ consSub i F, gPairMass (N := N) θ (k (i :: u)) (f (i :: u))
              = G (i : ℕ) := by
          intro i
          simp only [hGdef, dite_eq_left i.isLt, Fin.eta]
        have hGone : ∀ m : ℕ, k [] ≤ m → G m = 1 := by
          intro m hm
          simp only [hGdef]
          split
          · rename_i h
            rw [hconsEmpty ⟨m, h⟩ hm, Finset.prod_empty]
          · rfl
        rw [hset, hstep, prod_cons_decomp hroot]
        refine congrArg _ ?_
        rw [Finset.prod_congr rfl fun i _ ↦ hG i, Fin.prod_univ_eq_prod_range G N,
          Finset.prod_congr rfl fun m _ ↦ hrec m]
        rcases le_total (k []) N with hkN | hNk
        · exact Finset.prod_subset
            (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
            fun m _ hm' ↦ hGone m (not_lt.mp fun hc ↦ hm' (Finset.mem_range.mpr hc))
        · have hsub : Finset.range N ⊆ Finset.range (k []) := by
            intro x hx
            simp only [Finset.mem_range] at hx ⊢
            omega
          have hone : ∀ m ∈ Finset.range (k []), m ∉ Finset.range N → G m = 1 := by
            intro m _ hm'
            simp only [hGdef]
            exact dite_eq_right fun hc ↦ hm' (Finset.mem_range.mpr hc)
          exact (Finset.prod_subset hsub hone).symm

/-- **`thm:conditional-iid`, the joint product formula**, at any prefix-closed probe. -/
theorem survivalMeasure_gShapes (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (F : Finset (GWord N))
    (hpc : ∀ u ∈ F, ∀ p : GWord N, p <+: u → p ∈ F) (f : GWord N → GShape)
    (k : GWord N → ℕ) (hk2 : ∀ u ∈ F, 2 ≤ k u)
    (hcomp : ∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < k u) :
    survivalMeasure (N := N) θ
        (⋂ u ∈ F, ({c : GWord N → ℕ | gShapeAt c u = f u}
          ∩ {c : GWord N → ℕ | gArityAt c u = k u}))
      = ∏ u ∈ F, gPairMass (N := N) θ (k u) (f u) :=
  survivalMeasure_gShapes_aux θ hJN hq hq0 (F.sup List.length) F
    (fun _ hu ↦ Finset.le_sup (f := List.length) hu) hpc f k hk2 hcomp

/-! ### The arity probe at a fixed neck length -/

/-- The arity probe at a fixed neck length: the descent splits after `n` steps, at the
prescribed arity, with the subtrees below the split constrained. -/
def gArityDepthEvent (κ n : ℕ) (A : ℕ → Set (GWord N → ℕ)) : Set (GWord N → ℕ) :=
  ({c : GWord N → ℕ | gSplitDepth c = n} ∩ {c : GWord N → ℕ | gArity c = κ})
    ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m}

lemma gArityDepthEvent_zero {κ : ℕ} (hκ : 2 ≤ κ) (A : ℕ → Set (GWord N → ℕ)) :
    gArityDepthEvent (N := N) κ 0 A
      = ({c : GWord N → ℕ | skeletonDegree c = κ}
          ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < κ → bushAt c m ∈ A m}) := by
  ext c
  simp only [gArityDepthEvent, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hd, ha⟩, hb⟩
    have hf : gSplitField c = c := gSplitField_of_depth_zero hd
    rw [gArity, hf] at ha
    refine ⟨ha, fun m hm ↦ ?_⟩
    have hmem := hb m hm
    rwa [gSplitBush, hf] at hmem
  · rintro ⟨hdeg, hb⟩
    have hd : gSplitDepth c = 0 := gSplitDepth_eq_zero (by omega)
    have hf : gSplitField c = c := gSplitField_of_depth_zero hd
    refine ⟨⟨hd, by rw [gArity, hf, hdeg]⟩, fun m hm ↦ ?_⟩
    rw [gSplitBush, hf]
    exact hb m hm

lemma gArityDepthEvent_succ_inter {κ n : ℕ} (hκ : 2 ≤ κ) (A : ℕ → Set (GWord N → ℕ)) :
    gArityDepthEvent (N := N) κ (n + 1) A ∩ {c : GWord N → ℕ | Survives c}
      = (({c : GWord N → ℕ | skeletonDegree c = 1}
          ∩ {c : GWord N → ℕ | bushAt c 0 ∈ gArityDepthEvent (N := N) κ n A})
        ∩ {c : GWord N → ℕ | Survives c}) := by
  ext c
  simp only [gArityDepthEvent, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨⟨hd, ha⟩, hb⟩, hsurv⟩
    have hdne : gSplitDepth c ≠ 0 := by omega
    have hSne := splitSet_nonempty_of_ne_zero hdne
    have h0 : ¬ 2 ≤ skeletonDegree c := by
      intro h2
      have := gSplitDepth_eq_zero h2
      omega
    have hne0 : skeletonDegree c ≠ 0 :=
      BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp hsurv
    have hdeg1 : skeletonDegree c = 1 := by omega
    have hne' := splitSet_nonempty_down hdeg1 hSne
    have hd' : gSplitDepth (bushAt c 0) = n := by
      have := gSplitDepth_succ hdeg1 hne'
      omega
    refine ⟨⟨hdeg1, ⟨⟨hd', ?_⟩, ?_⟩⟩, hsurv⟩
    · rw [← gArity_step hdeg1 hne']
      exact ha
    · intro m hm
      rw [← gSplitBush_step hdeg1 hne' m]
      exact hb m hm
  · rintro ⟨⟨hdeg1, ⟨⟨hd', ha'⟩, hb'⟩⟩, hsurv⟩
    have hne' : {j : ℕ | 2 ≤ skeletonDegree (neckIter (bushAt c 0) j)}.Nonempty :=
      splitSet_nonempty_of_arity (by omega)
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hsurv⟩
    · rw [gSplitDepth_succ hdeg1 hne', hd']
    · rw [gArity_step hdeg1 hne']
      exact ha'
    · intro m hm
      rw [gSplitBush_step hdeg1 hne' m]
      exact hb' m hm

/-- **The neck series**: the arity probe at neck length `n` carries `θ̃₁ⁿ` against the
split weight. -/
theorem survivalMeasure_gArityDepthEvent (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) {κ : ℕ} (hκ : 2 ≤ κ) {A : ℕ → Set (GWord N → ℕ)}
    (hA : ∀ m, MeasurableSet (A m)) : ∀ n : ℕ,
    survivalMeasure (N := N) θ (gArityDepthEvent (N := N) κ n A)
      = ENNReal.ofReal (θ.skeletonWeight 1) ^ n
          * (ENNReal.ofReal (θ.skeletonWeight κ)
            * ∏ m ∈ Finset.range κ, survivalMeasure (N := N) θ (A m)) := by
  intro n
  induction n with
  | zero =>
      rw [gArityDepthEvent_zero hκ A,
        BranchingProcess.survivalMeasure_skeletonDegree_bushes θ hJN hq κ hA, pow_zero,
        one_mul]
  | succ n ih =>
      have hnull := survivalMeasure_compl_survives θ hJN hq
      have hEmeas : MeasurableSet (gArityDepthEvent (N := N) κ n A) :=
        ((fibreMeasurableG_gSplitDepth n).inter (fibreMeasurableG_gArity κ)).inter
          (measurableSet_gSplitBush_box hA)
      have hAmeas' : ∀ m : ℕ,
          MeasurableSet (if m = 0 then gArityDepthEvent (N := N) κ n A
            else (Set.univ : Set (GWord N → ℕ))) := by
        intro m
        split
        · exact hEmeas
        · exact MeasurableSet.univ
      have hkey := BranchingProcess.survivalMeasure_skeletonDegree_bushes θ hJN hq 1
        (A := fun m ↦ if m = 0 then gArityDepthEvent (N := N) κ n A else Set.univ) hAmeas'
      have hbox : {c : GWord N → ℕ | ∀ m : ℕ, m < 1 → bushAt c m
            ∈ (if m = 0 then gArityDepthEvent (N := N) κ n A else Set.univ)}
          = {c : GWord N → ℕ | bushAt c 0 ∈ gArityDepthEvent (N := N) κ n A} := by
        ext c
        simp only [Set.mem_ofPred_eq, Nat.lt_one_iff]
        constructor
        · intro h
          have hc := h 0 rfl
          rwa [ite_eq_left rfl] at hc
        · rintro h m rfl
          rwa [ite_eq_left rfl]
      rw [hbox] at hkey
      rw [measure_eq_of_inter_ae hnull (gArityDepthEvent_succ_inter hκ A), hkey,
        Finset.prod_range_one, ite_eq_left rfl, ih, pow_succ]
      ring

/-! ### The reduced law at the root -/

/-- **`eq:reduced-law`**: the weight `ν̃_κ = θ̃_κ/(1-θ̃₁)` of the reduced offspring
law. -/
noncomputable def reducedWeight (θ : Offspring J) (κ : ℕ) : ℝ :=
  θ.skeletonWeight κ / (1 - θ.skeletonWeight 1)

lemma reducedWeight_def (θ : Offspring J) (κ : ℕ) :
    reducedWeight θ κ = θ.skeletonWeight κ / (1 - θ.skeletonWeight 1) := rfl

/-- **The reduced law at the root**: the arity of the terminating split carries the
weight `ν̃_κ`, the geometric neck series folded, and the subtrees below the split are
independent conditioned samples. -/
theorem survivalMeasure_gArityPair (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1) {κ : ℕ} (hκ : 2 ≤ κ)
    {A : ℕ → Set (GWord N → ℕ)} (hA : ∀ m, MeasurableSet (A m)) :
    survivalMeasure (N := N) θ
        ({c : GWord N → ℕ | gArity c = κ}
          ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m})
      = ENNReal.ofReal (reducedWeight θ κ)
          * ∏ m ∈ Finset.range κ, survivalMeasure (N := N) θ (A m) := by
  have hdisj : Pairwise (Function.onFun Disjoint
      fun n : ℕ ↦ gArityDepthEvent (N := N) κ n A) := by
    intro n n' hnn
    refine Set.disjoint_left.mpr fun c hc hc' ↦ hnn ?_
    rw [← hc.1.1, ← hc'.1.1]
  have hmeas : ∀ n : ℕ, MeasurableSet (gArityDepthEvent (N := N) κ n A) := fun n ↦
    ((fibreMeasurableG_gSplitDepth n).inter (fibreMeasurableG_gArity κ)).inter
      (measurableSet_gSplitBush_box hA)
  have hcover : {c : GWord N → ℕ | gArity c = κ}
        ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m}
      = ⋃ n : ℕ, gArityDepthEvent (N := N) κ n A := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, gArityDepthEvent]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨gSplitDepth c, ⟨rfl, ha⟩, hb⟩
    · rintro ⟨n, ⟨-, ha⟩, hb⟩
      exact ⟨ha, hb⟩
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  have h1a : 0 < 1 - θ.skeletonWeight 1 := by linarith
  rw [hcover, measure_iUnion hdisj hmeas,
    tsum_congr (fun n ↦ survivalMeasure_gArityDepthEvent θ hJN hq hκ hA n),
    ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 ha0, ← ENNReal.ofReal_inv_of_pos h1a, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_eq_div, ← reducedWeight_def]

/-! ### The arity field is i.i.d. with the reduced law -/

/-- **The arity field is i.i.d. `ν̃`**,
`thm:harris-general` (`it:harris-general-reduced`) probed on the reduced
skeleton: over a prefix-closed finite set of addresses whose letters respect the
prescribed arities, the arities are independent with the reduced law. -/
theorem survivalMeasure_gArities_aux (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1) :
    ∀ (n : ℕ) (F : Finset (GWord N)), (∀ u ∈ F, u.length ≤ n) →
      (∀ u ∈ F, ∀ p : GWord N, p <+: u → p ∈ F) →
      ∀ k : GWord N → ℕ,
        (∀ u ∈ F, 2 ≤ k u) →
        (∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < k u) →
        survivalMeasure (N := N) θ
            (⋂ u ∈ F, {c : GWord N → ℕ | gArityAt c u = k u})
          = ∏ u ∈ F, ENNReal.ofReal (reducedWeight θ (k u)) := by
  classical
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  intro n
  induction n with
  | zero =>
      intro F hlen hpc k hk2 hcomp
      rcases F.eq_empty_or_nonempty with rfl | hne
      · simp
      · obtain ⟨v, hv⟩ := hne
        have hroot : ([] : GWord N) ∈ F := hpc v hv [] List.nil_prefix
        have hF : F = {[]} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hroot, fun v' hv' ↦ ?_⟩
          exact List.length_eq_zero_iff.mp (Nat.le_zero.mp (hlen v' hv'))
        subst hF
        have hset : (⋂ u ∈ ({[]} : Finset (GWord N)),
              {c : GWord N → ℕ | gArityAt c u = k u})
            = ({c : GWord N → ℕ | gArity c = k []}
              ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < k [] →
                  gSplitBush c m ∈ (Set.univ : Set (GWord N → ℕ))}) := by
          ext c
          simp
        rw [hset, survivalMeasure_gArityPair θ hJN hq hs1 (hk2 [] hroot)
          (fun _ ↦ MeasurableSet.univ), Finset.prod_singleton]
        simp
  | succ n ih =>
      intro F hlen hpc k hk2 hcomp
      rcases F.eq_empty_or_nonempty with rfl | hne
      · simp
      · obtain ⟨v, hv⟩ := hne
        have hroot : ([] : GWord N) ∈ F := hpc v hv [] List.nil_prefix
        set E : Fin N → Set (GWord N → ℕ) := fun i ↦
          ⋂ u ∈ consSub i F, {d : GWord N → ℕ | gArityAt d u = k (i :: u)} with hE
        have hconsEmpty : ∀ i : Fin N, k [] ≤ (i : ℕ) → consSub i F = ∅ := by
          intro i hi
          rw [Finset.eq_empty_iff_forall_notMem]
          intro u hu
          have h1 : [i] ∈ F := hpc _ (mem_consSub.mp hu) [i] ⟨u, rfl⟩
          have h2 := hcomp [] hroot i (by simpa using h1)
          omega
        set A : ℕ → Set (GWord N → ℕ) :=
          fun m ↦ if h : m < N then E ⟨m, h⟩ else Set.univ with hA
        have hAmeas : ∀ m, MeasurableSet (A m) := by
          intro m
          simp only [hA]
          split
          · exact MeasurableSet.biInter (consSub _ F).countable_toSet fun u _ ↦
              fibreMeasurableG_gArityAt u _
          · exact MeasurableSet.univ
        have hset : (⋂ u ∈ F, {c : GWord N → ℕ | gArityAt c u = k u})
            = ({c : GWord N → ℕ | gArity c = k []}
              ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < k [] → gSplitBush c m ∈ A m}) := by
          ext c
          simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq]
          constructor
          · intro h
            refine ⟨h [] hroot, fun m hm ↦ ?_⟩
            simp only [hA]
            split
            · rename_i hmN
              simp only [hE, Set.mem_iInter, Set.mem_ofPred_eq]
              intro u hu
              exact h (⟨m, hmN⟩ :: u) (mem_consSub.mp hu)
            · exact Set.mem_univ _
          · rintro ⟨ha0, hrest⟩ u hu
            cases u with
            | nil => exact ha0
            | cons i u =>
                by_cases hik : (i : ℕ) < k []
                · have hm := hrest (i : ℕ) hik
                  simp only [hA] at hm
                  rw [dite_eq_left i.isLt, Fin.eta] at hm
                  simp only [hE, Set.mem_iInter, Set.mem_ofPred_eq] at hm
                  exact hm u (mem_consSub.mpr hu)
                · exact absurd (mem_consSub.mpr hu)
                    (by rw [hconsEmpty i (not_lt.mp hik)]; exact Finset.notMem_empty u)
        have hstep := survivalMeasure_gArityPair θ hJN hq hs1 (hk2 [] hroot) hAmeas
        set G : ℕ → ℝ≥0∞ := fun m ↦ if h : m < N then
            ∏ u ∈ consSub ⟨m, h⟩ F, ENNReal.ofReal (reducedWeight θ (k (⟨m, h⟩ :: u)))
          else 1 with hGdef
        have hrec : ∀ m : ℕ, survivalMeasure (N := N) θ (A m) = G m := by
          intro m
          simp only [hA, hGdef]
          split
          · rename_i hmN
            simp only [hE]
            refine ih (consSub ⟨m, hmN⟩ F) (fun u hu ↦ ?_) (fun u hu p hp ↦ ?_)
              (fun u ↦ k (⟨m, hmN⟩ :: u)) (fun _ hu ↦ hk2 _ (mem_consSub.mp hu))
              (fun u hu i hi ↦ ?_)
            · have := hlen _ (mem_consSub.mp hu)
              simpa using this
            · exact mem_consSub.mpr
                (hpc _ (mem_consSub.mp hu) _ (List.cons_prefix_cons.mpr ⟨rfl, hp⟩))
            · exact hcomp _ (mem_consSub.mp hu) i (mem_consSub.mp hi)
          · exact measure_univ
        have hG : ∀ i : Fin N,
            ∏ u ∈ consSub i F, ENNReal.ofReal (reducedWeight θ (k (i :: u)))
              = G (i : ℕ) := by
          intro i
          simp only [hGdef, dite_eq_left i.isLt, Fin.eta]
        have hGone : ∀ m : ℕ, k [] ≤ m → G m = 1 := by
          intro m hm
          simp only [hGdef]
          split
          · rename_i h
            rw [hconsEmpty ⟨m, h⟩ hm, Finset.prod_empty]
          · rfl
        rw [hset, hstep, prod_cons_decomp hroot]
        refine congrArg _ ?_
        rw [Finset.prod_congr rfl fun i _ ↦ hG i, Fin.prod_univ_eq_prod_range G N,
          Finset.prod_congr rfl fun m _ ↦ hrec m]
        rcases le_total (k []) N with hkN | hNk
        · exact Finset.prod_subset
            (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
            fun m _ hm' ↦ hGone m (not_lt.mp fun hc ↦ hm' (Finset.mem_range.mpr hc))
        · have hsub : Finset.range N ⊆ Finset.range (k []) := by
            intro x hx
            simp only [Finset.mem_range] at hx ⊢
            omega
          have hone : ∀ m ∈ Finset.range (k []), m ∉ Finset.range N → G m = 1 := by
            intro m _ hm'
            simp only [hGdef]
            exact dite_eq_right fun hc ↦ hm' (Finset.mem_range.mpr hc)
          exact (Finset.prod_subset hsub hone).symm

/-- **The arity field is i.i.d. `ν̃`**, at any prefix-closed probe. -/
theorem survivalMeasure_gArities (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) (F : Finset (GWord N))
    (hpc : ∀ u ∈ F, ∀ p : GWord N, p <+: u → p ∈ F) (k : GWord N → ℕ)
    (hk2 : ∀ u ∈ F, 2 ≤ k u)
    (hcomp : ∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < k u) :
    survivalMeasure (N := N) θ (⋂ u ∈ F, {c : GWord N → ℕ | gArityAt c u = k u})
      = ∏ u ∈ F, ENNReal.ofReal (reducedWeight θ (k u)) :=
  survivalMeasure_gArities_aux θ hJN hq hs1 (F.sup List.length) F
    (fun _ hu ↦ Finset.le_sup (f := List.length) hu) hpc k hk2 hcomp

/-! ### The reduced law has full support -/

/-- **`thm:full-support` on the constructed space**: in the bushy regime the skeleton
weight of every arity up to the support bound is positive. -/
lemma skeletonWeight_pos (θ : Offspring J) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hθJ : 0 < θ J) {κ : ℕ} (hκ1 : 1 ≤ κ) (hκJ : κ ≤ J) :
    0 < θ.skeletonWeight κ := by
  have h1q : (0 : ℝ) < 1 - θ.extinction := by linarith
  have hchoose : (0 : ℝ) < (J.choose κ : ℝ) := by
    exact_mod_cast Nat.choose_pos hκJ
  have hterm : (0 : ℝ) < θ J * (J.choose κ : ℝ) * (1 - θ.extinction) ^ κ
      * θ.extinction ^ (J - κ) := by
    positivity
  have hnonneg : ∀ j ∈ Finset.range (J + 1),
      (0 : ℝ) ≤ θ j * (j.choose κ : ℝ) * (1 - θ.extinction) ^ κ
        * θ.extinction ^ (j - κ) := by
    intro j _
    have h1 := θ.nonneg j
    have h2 := θ.extinction_nonneg
    positivity
  have hsum : θ J * (J.choose κ : ℝ) * (1 - θ.extinction) ^ κ * θ.extinction ^ (J - κ)
      ≤ θ.surviveWeight κ := by
    rw [BranchingProcess.Offspring.surviveWeight]
    exact Finset.single_le_sum hnonneg (Finset.self_mem_range_succ J)
  rw [BranchingProcess.Offspring.skeletonWeight_of_ne_zero θ (by omega)]
  exact div_pos (lt_of_lt_of_le hterm hsum) h1q

/-- **The chain of necks is not everything**: with a split of positive weight the neck
weight is below one. -/
lemma skeletonWeight_one_lt_one_of (θ : Offspring J) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) :
    θ.skeletonWeight 1 < 1 := by
  have hsum := BranchingProcess.Offspring.sum_skeletonWeight θ hq
  have hJpos := skeletonWeight_pos θ hq hq0 hθJ (by omega : 1 ≤ J) le_rfl
  have hnonneg : ∀ j ∈ Finset.range (J + 1), 0 ≤ θ.skeletonWeight j := fun j _ ↦
    θ.skeletonWeight_nonneg hq j
  have hsub : ({1, J} : Finset ℕ) ⊆ Finset.range (J + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun j hj _ ↦ hnonneg j hj)
  rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ J)] at hle
  linarith

/-- **`thm:full-support` for the reduced law**: `ν̃_κ > 0` for every `2 ≤ κ ≤ J`. -/
lemma reducedWeight_pos (θ : Offspring J) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) {κ : ℕ} (hκ2 : 2 ≤ κ)
    (hκJ : κ ≤ J) : 0 < reducedWeight θ κ := by
  rw [reducedWeight_def]
  have h1 := skeletonWeight_one_lt_one_of θ hq hq0 hJ2 hθJ
  exact div_pos (skeletonWeight_pos θ hq hq0 hθJ (by omega) hκJ) (by linarith)

/-! ### `thm:conditional-iid` -/

/-- **`def:conditional-laws`**: the mass of a shape under the conditional law `μ_κ`,
the joint mass against the reduced weight of the arity. -/
noncomputable def gCondMass (θ : Offspring J) (κ : ℕ) (σ : GShape) : ℝ≥0∞ :=
  gPairMass (N := N) θ κ σ / ENNReal.ofReal (reducedWeight θ κ)

lemma gCondMass_def (θ : Offspring J) (κ : ℕ) (σ : GShape) :
    gCondMass (N := N) θ κ σ
      = gPairMass (N := N) θ κ σ / ENNReal.ofReal (reducedWeight θ κ) := rfl

/-- **`thm:conditional-iid`**: conditioned on the arity field of the reduced skeleton,
the shapes are independent with the conditional laws `μ_{k(w)}`: over any prefix-closed
probe, the joint mass of shapes and arities is the product of one conditional mass per
address against the mass of the arity probe alone. -/
theorem conditional_iid (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) (F : Finset (GWord N))
    (hpc : ∀ u ∈ F, ∀ p : GWord N, p <+: u → p ∈ F) (f : GWord N → GShape)
    (k : GWord N → ℕ) (hk2 : ∀ u ∈ F, 2 ≤ k u) (hkJ : ∀ u ∈ F, k u ≤ J)
    (hcomp : ∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < k u) :
    survivalMeasure (N := N) θ
        (⋂ u ∈ F, ({c : GWord N → ℕ | gShapeAt c u = f u}
          ∩ {c : GWord N → ℕ | gArityAt c u = k u}))
      = (∏ u ∈ F, gCondMass (N := N) θ (k u) (f u))
          * survivalMeasure (N := N) θ
              (⋂ u ∈ F, {c : GWord N → ℕ | gArityAt c u = k u}) := by
  have hs1 : θ.skeletonWeight 1 < 1 := skeletonWeight_one_lt_one_of θ hq hq0 hJ2 hθJ
  rw [survivalMeasure_gShapes θ hJN hq hq0 F hpc f k hk2 hcomp,
    survivalMeasure_gArities θ hJN hq hs1 F hpc k hk2 hcomp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun u hu ↦ ?_
  have hpos : 0 < reducedWeight θ (k u) :=
    reducedWeight_pos θ hq hq0 hJ2 hθJ (hk2 u hu) (hkJ u hu)
  rw [gCondMass_def]
  exact (ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr hpos).ne'
    ENNReal.ofReal_ne_top).symm

end ChainClasses
