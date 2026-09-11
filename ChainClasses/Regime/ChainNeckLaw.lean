import ChainClasses.General.GeneralShapeIID

/-! Joint laws of the original reduced neck lengths and arities. The argument only
requires positive survival probability and therefore includes zero-extinction laws. -/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal
open BranchingProcess (Offspring survivalMeasure consSub mem_consSub prod_cons_decomp)

variable {J N : ℕ}

/-- The unary neck length at a reduced-skeleton address. -/
noncomputable def neckAt (c : GWord N → ℕ) (u : GWord N) : ℕ :=
  gSplitDepth (redSub c u)

@[simp] lemma neckAt_nil (c : GWord N → ℕ) : neckAt c [] = gSplitDepth c := rfl

lemma neckAt_cons (c : GWord N → ℕ) (i : Fin N) (u : GWord N) :
    neckAt c (i :: u) = neckAt (gSplitBush c (i : ℕ)) u := rfl

theorem fibreMeasurableG_neckAt (u : GWord N) :
    FibreMeasurableG (fun c : GWord N → ℕ ↦ neckAt c u) := fun n ↦
  measurable_redSub u (fibreMeasurableG_gSplitDepth n)

/-- Joint mass of a unary neck and its terminating reduced arity. -/
noncomputable def neckPairMass (θ : Offspring J) (κ n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (θ.skeletonWeight 1) ^ n * ENNReal.ofReal (θ.skeletonWeight κ)

/-- The neck and arity at the root are independent of the reduced descendant trees. -/
theorem survivalMeasure_neckPair (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (n : ℕ) {κ : ℕ} (hκ : 2 ≤ κ)
    {A : ℕ → Set (GWord N → ℕ)} (hA : ∀ m, MeasurableSet (A m)) :
    survivalMeasure (N := N) θ
        (({c : GWord N → ℕ | gSplitDepth c = n} ∩ {c : GWord N → ℕ | gArity c = κ})
          ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m})
      = neckPairMass θ κ n * ∏ m ∈ Finset.range κ, survivalMeasure (N := N) θ (A m) := by
  rw [show (({c : GWord N → ℕ | gSplitDepth c = n} ∩ {c : GWord N → ℕ | gArity c = κ})
      ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m})
      = gArityDepthEvent κ n A from rfl, survivalMeasure_gArityDepthEvent θ hJN hq hκ hA]
  exact (mul_assoc _ _ _).symm

/-- Neck lengths and arities have the product of their joint masses on every finite
prefix-closed pattern whose addresses respect the prescribed arities. -/
theorem survivalMeasure_neckArity_aux (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) :
    ∀ (n : ℕ) (F : Finset (GWord N)), (∀ u ∈ F, u.length ≤ n) →
      (∀ u ∈ F, ∀ p : GWord N, p <+: u → p ∈ F) →
      ∀ (f : GWord N → ℕ) (k : GWord N → ℕ),
        (∀ u ∈ F, 2 ≤ k u) →
        (∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < k u) →
        survivalMeasure (N := N) θ
            (⋂ u ∈ F, ({c : GWord N → ℕ | neckAt c u = f u}
              ∩ {c : GWord N → ℕ | gArityAt c u = k u}))
          = ∏ u ∈ F, neckPairMass θ (k u) (f u) := by
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
              ({c : GWord N → ℕ | neckAt c u = f u}
                ∩ {c : GWord N → ℕ | gArityAt c u = k u}))
            = (({c : GWord N → ℕ | gSplitDepth c = f []}
                ∩ {c : GWord N → ℕ | gArity c = k []})
              ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < k [] →
                  gSplitBush c m ∈ (Set.univ : Set (GWord N → ℕ))}) := by
          ext c
          simp
        rw [hset, survivalMeasure_neckPair θ hJN hq (f []) (hk2 [] hroot)
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
            ({d : GWord N → ℕ | neckAt d u = f (i :: u)}
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
              (fibreMeasurableG_neckAt u _).inter (fibreMeasurableG_gArityAt u _)
          · exact MeasurableSet.univ
        have hset : (⋂ u ∈ F, ({c : GWord N → ℕ | neckAt c u = f u}
              ∩ {c : GWord N → ℕ | gArityAt c u = k u}))
            = (({c : GWord N → ℕ | gSplitDepth c = f []}
                ∩ {c : GWord N → ℕ | gArity c = k []})
              ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < k [] → gSplitBush c m ∈ A m}) := by
          ext c
          simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
          constructor
          · intro h
            obtain ⟨hs0, ha0⟩ := h [] hroot
            refine ⟨⟨hs0, ha0⟩, fun m hm ↦ ?_⟩
            simp only [hA]
            split
            · rename_i hmN
              simp only [hE, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
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
                  rw [dif_pos i.isLt, Fin.eta] at hm
                  simp only [hE, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hm
                  exact hm u (mem_consSub.mpr hu)
                · exact absurd (mem_consSub.mpr hu)
                    (by rw [hconsEmpty i (not_lt.mp hik)]; exact Finset.notMem_empty u)
        have hstep := survivalMeasure_neckPair θ hJN hq (f []) (hk2 [] hroot) hAmeas
        set G : ℕ → ℝ≥0∞ := fun m ↦ if h : m < N then
            ∏ u ∈ consSub ⟨m, h⟩ F, neckPairMass θ (k (⟨m, h⟩ :: u)) (f (⟨m, h⟩ :: u))
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
            ∏ u ∈ consSub i F, neckPairMass θ (k (i :: u)) (f (i :: u))
              = G (i : ℕ) := by
          intro i
          simp only [hGdef, dif_pos i.isLt, Fin.eta]
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
            exact dif_neg fun hc ↦ hm' (Finset.mem_range.mpr hc)
          exact (Finset.prod_subset hsub hone).symm

/-- **`thm:conditional-iid`, the joint product formula**, at any prefix-closed probe. -/
theorem survivalMeasure_neckArity (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (F : Finset (GWord N))
    (hpc : ∀ u ∈ F, ∀ p : GWord N, p <+: u → p ∈ F) (f : GWord N → ℕ)
    (k : GWord N → ℕ) (hk2 : ∀ u ∈ F, 2 ≤ k u)
    (hcomp : ∀ u ∈ F, ∀ i : Fin N, u ++ [i] ∈ F → (i : ℕ) < k u) :
    survivalMeasure (N := N) θ
        (⋂ u ∈ F, ({c : GWord N → ℕ | neckAt c u = f u}
          ∩ {c : GWord N → ℕ | gArityAt c u = k u}))
      = ∏ u ∈ F, neckPairMass θ (k u) (f u) :=
  survivalMeasure_neckArity_aux θ hJN hq (F.sup List.length) F
    (fun _ hu ↦ Finset.le_sup (f := List.length) hu) hpc f k hk2 hcomp


end ChainClasses
