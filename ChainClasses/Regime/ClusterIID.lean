import ChainClasses.Regime.ClusterRoot
import ChainClasses.Regime.ChainRegime

/-!
`sec:general-chain` of `matching_classes_general.tex`: **the i.i.d. clause of
`thm:cluster-law`** over the presented skeleton, on the constructed space.

The coin field decomposes a probe: the rule reads only the coins at the prefixes of the
probed addresses, so over a prefix-closed probe the event is a finite disjoint union of
rectangles, one per coin pattern, and the product measure evaluates each rectangle as a
sample factor against a coin factor.  At a fixed coin field the sample factor is an
induction over the probe whose root step is `ClusterRoot`; summing the coin patterns
back swaps the finite sum with the product, and each vertex contributes the averaged
mass of its coin.

* `consSubN`, `prodN_cons_decomp`: a prefix-closed finite set of presented addresses
  decomposed at the root, over the letters `ℕ` of the presented alphabet.
* `survivalMeasure_clusterC`: **the fixed-coin product formula**: at a fixed coin field
  the presented pairs are independent, one mass per address, each mass read at the coin
  of its address.
* `clusterMeasure`, `bernoulliField_pattern`: the sample against the Bernoulli coin
  field, and the mass of a coin pattern.
* `cluster_iid`: **`thm:cluster-law`, the i.i.d. clause**: over the sample against the
  coin field, the presented neck lengths and presented arities are independent over any
  prefix-closed probe of the presented skeleton, the neck geometric and the arity
  carrying the averaged mass of one absorption.
-/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal
open BranchingProcess (Survives skeletonDegree Offspring sampleMeasure survivalMeasure
  bushAt)

variable {J N : ℕ}

/-! ### A prefix-closed probe decomposed at the root -/

/-- The presented addresses continuing a first letter. -/
noncomputable def consSubN (i : ℕ) (F : Finset (List ℕ)) : Finset (List ℕ) :=
  F.preimage (i :: ·) (List.cons_injective.injOn)

@[simp] lemma mem_consSubN {i : ℕ} {F : Finset (List ℕ)} {u : List ℕ} :
    u ∈ consSubN i F ↔ i :: u ∈ F := Finset.mem_preimage

/-- A prefix-closed finite set of presented addresses containing the root, with its
first letters bounded, is the root together with its continuations. -/
lemma finsetN_cons_decomp [DecidableEq (List ℕ)] {F : Finset (List ℕ)}
    (h : ([] : List ℕ) ∈ F) {K : ℕ}
    (hK : ∀ (i : ℕ) (u : List ℕ), (i :: u) ∈ F → i < K) :
    F = insert []
      ((Finset.range K).biUnion fun i ↦ (consSubN i F).image (i :: ·)) := by
  ext v
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    mem_consSubN]
  constructor
  · intro hv
    cases v with
    | nil => exact Or.inl rfl
    | cons i u => exact Or.inr ⟨i, hK i u hv, u, hv, rfl⟩
  · rintro (rfl | ⟨i, -, u, hu, rfl⟩)
    · exact h
    · exact hu

/-- The product over a prefix-closed set of presented addresses splits at the root. -/
lemma prodN_cons_decomp {M : Type*} [CommMonoid M] {F : Finset (List ℕ)}
    (h : ([] : List ℕ) ∈ F) {K : ℕ}
    (hK : ∀ (i : ℕ) (u : List ℕ), (i :: u) ∈ F → i < K) (g : List ℕ → M) :
    ∏ u ∈ F, g u = g [] * ∏ i ∈ Finset.range K, ∏ u ∈ consSubN i F, g (i :: u) := by
  classical
  have hdisj : ((Finset.range K : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun i : ℕ ↦ (consSubN i F).image (i :: ·)) := by
    intro i _ i' _ hii
    refine Finset.disjoint_left.mpr fun v hv hv' ↦ ?_
    simp only [Finset.mem_image, mem_consSubN] at hv hv'
    obtain ⟨u, -, rfl⟩ := hv
    obtain ⟨u', -, heq⟩ := hv'
    exact hii ((List.cons_eq_cons.mp heq).1.symm)
  have hnotmem : ([] : List ℕ)
      ∉ (Finset.range K).biUnion fun i : ℕ ↦ (consSubN i F).image (i :: ·) := by
    intro hmem
    rw [Finset.mem_biUnion] at hmem
    obtain ⟨i, -, hmem2⟩ := hmem
    rw [Finset.mem_image] at hmem2
    obtain ⟨u, -, hcons⟩ := hmem2
    exact List.cons_ne_nil i u hcons
  conv_lhs => rw [finsetN_cons_decomp h hK]
  rw [Finset.prod_insert hnotmem, Finset.prod_biUnion hdisj]
  refine congrArg _ (Finset.prod_congr rfl fun i _ ↦ ?_)
  exact Finset.prod_image fun u _ u' _ heq ↦ (List.cons_eq_cons.mp heq).2

/-! ### The fixed-coin product formula -/

/-- The pair-eta form of a presented child: the sample part with the shifted coins. -/
lemma clSubC_eta (R : ℕ) (c : GWord N → ℕ) (b : List ℕ → Bool) (i : ℕ) :
    clSubC R (c, b) i = ((clSubC R (c, b) i).1, fun w ↦ b (i :: w)) := by
  rw [Prod.ext_iff]
  exact ⟨rfl, clSubC_snd R (c, b) i⟩

/-- **The fixed-coin product formula**: at a fixed coin field the presented pairs over
a prefix-closed probe are independent, one mass per address, the coin of the mass read
at the address. -/
theorem survivalMeasure_clusterC_aux (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1) (R : ℕ) :
    ∀ (n : ℕ) (F : Finset (List ℕ)), (∀ u ∈ F, u.length ≤ n) →
      (∀ u ∈ F, ∀ p : List ℕ, p <+: u → p ∈ F) →
      ∀ (b : List ℕ → Bool) (r j : List ℕ → ℕ),
        (∀ u ∈ F, 2 ≤ j u) →
        (∀ u ∈ F, ∀ i : ℕ, u ++ [i] ∈ F → i < j u) →
        survivalMeasure (N := N) θ
            (⋂ u ∈ F, ({c : GWord N → ℕ | clNeckAtC R (c, b) u = r u}
              ∩ {c : GWord N → ℕ | clArityAtC R (c, b) u = j u}))
          = ∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u)
              * clCoinMassE (θ := θ) R (b u) (j u) := by
  classical
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  intro n
  induction n with
  | zero =>
      intro F hlen hpc b r j hj2 hcomp
      rcases F.eq_empty_or_nonempty with rfl | hne
      · simp
      · obtain ⟨v, hv⟩ := hne
        have hroot : ([] : List ℕ) ∈ F := hpc v hv [] List.nil_prefix
        have hF : F = {[]} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hroot, fun v' hv' ↦ ?_⟩
          exact List.length_eq_zero_iff.mp (Nat.le_zero.mp (hlen v' hv'))
        subst hF
        have hset : (⋂ u ∈ ({[]} : Finset (List ℕ)),
              ({c : GWord N → ℕ | clNeckAtC R (c, b) u = r u}
                ∩ {c : GWord N → ℕ | clArityAtC R (c, b) u = j u}))
            = (({c : GWord N → ℕ | gSplitDepth c = r []}
                ∩ {c : GWord N → ℕ | clArityC R (c, b) = j []})
              ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < j [] →
                  (clSubC R (c, b) m).1 ∈ (Set.univ : Set (GWord N → ℕ))}) := by
          ext c
          simp
        rw [hset]
        cases hb0 : b [] with
        | false =>
            rw [cluster_root_coin_false θ hJN hq hb0 (hj2 [] hroot)
              (fun _ ↦ MeasurableSet.univ), Finset.prod_singleton, hb0]
            simp
        | true =>
            rw [cluster_root_coin_true θ hJN hq hs1 hb0 (hj2 [] hroot)
              (fun _ ↦ MeasurableSet.univ), Finset.prod_singleton, hb0]
            simp
  | succ n ih =>
      intro F hlen hpc b r j hj2 hcomp
      rcases F.eq_empty_or_nonempty with rfl | hne
      · simp
      · obtain ⟨v, hv⟩ := hne
        have hroot : ([] : List ℕ) ∈ F := hpc v hv [] List.nil_prefix
        set E : ℕ → Set (GWord N → ℕ) := fun m ↦
          ⋂ u ∈ consSubN m F,
            ({d : GWord N → ℕ | clNeckAtC R (d, fun w ↦ b (m :: w)) u = r (m :: u)}
              ∩ {d : GWord N → ℕ | clArityAtC R (d, fun w ↦ b (m :: w)) u = j (m :: u)})
          with hE
        have hconsEmpty : ∀ m : ℕ, j [] ≤ m → consSubN m F = ∅ := by
          intro m hm
          rw [Finset.eq_empty_iff_forall_notMem]
          intro u hu
          have h1 : [m] ∈ F := hpc _ (mem_consSubN.mp hu) [m] ⟨u, rfl⟩
          have h2 := hcomp [] hroot m (by simpa using h1)
          omega
        have hEmeas : ∀ m : ℕ, MeasurableSet (E m) := by
          intro m
          rw [hE]
          exact MeasurableSet.biInter (Finset.countable_toSet _) fun u _ ↦
            (measurableSet_clNeckAtC_eq R _ u (r (m :: u))).inter
              (measurableSet_clArityAtC_eq R _ u (j (m :: u)))
        have hset : (⋂ u ∈ F, ({c : GWord N → ℕ | clNeckAtC R (c, b) u = r u}
              ∩ {c : GWord N → ℕ | clArityAtC R (c, b) u = j u}))
            = (({c : GWord N → ℕ | gSplitDepth c = r []}
                ∩ {c : GWord N → ℕ | clArityC R (c, b) = j []})
              ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < j [] → (clSubC R (c, b) m).1 ∈ E m}) := by
          ext c
          simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
          constructor
          · intro h
            obtain ⟨hn0, ha0⟩ := h [] hroot
            refine ⟨⟨hn0, ha0⟩, fun m hm ↦ ?_⟩
            rw [hE]
            simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
            intro u hu
            obtain ⟨hnu, hau⟩ := h (m :: u) (mem_consSubN.mp hu)
            rw [clNeckAtC_cons, clSubC_eta] at hnu
            rw [clArityAtC_cons, clSubC_eta] at hau
            exact ⟨hnu, hau⟩
          · rintro ⟨⟨hn0, ha0⟩, hrest⟩ u hu
            cases u with
            | nil => exact ⟨hn0, ha0⟩
            | cons m u =>
                have hm : m < j [] := by
                  have h1 : [m] ∈ F := hpc _ hu [m] ⟨u, rfl⟩
                  exact hcomp [] hroot m (by simpa using h1)
                have hmem := hrest m hm
                rw [hE] at hmem
                simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hmem
                obtain ⟨hnu, hau⟩ := hmem u (mem_consSubN.mpr hu)
                rw [clNeckAtC_cons, clSubC_eta]
                exact ⟨hnu, hau⟩
        have hrec : ∀ m : ℕ, m < j [] →
            survivalMeasure (N := N) θ (E m)
              = ∏ u ∈ consSubN m F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (r (m :: u))
                  * clCoinMassE (θ := θ) R (b (m :: u)) (j (m :: u)) := by
          intro m _
          rw [hE]
          exact ih (consSubN m F)
            (fun u hu ↦ by
              have := hlen _ (mem_consSubN.mp hu)
              simpa using this)
            (fun u hu p hp ↦ mem_consSubN.mpr
              (hpc _ (mem_consSubN.mp hu) _ (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)))
            (fun w ↦ b (m :: w)) (fun u ↦ r (m :: u)) (fun u ↦ j (m :: u))
            (fun u hu ↦ hj2 _ (mem_consSubN.mp hu))
            (fun u hu i hi ↦ hcomp _ (mem_consSubN.mp hu) i (mem_consSubN.mp hi))
        have hK : ∀ (i : ℕ) (u : List ℕ), (i :: u) ∈ F → i < j [] := by
          intro i u hu
          have h1 : [i] ∈ F := hpc _ hu [i] ⟨u, rfl⟩
          exact hcomp [] hroot i (by simpa using h1)
        rw [hset]
        have hstep : survivalMeasure (N := N) θ
            ((({c : GWord N → ℕ | gSplitDepth c = r []}
                ∩ {c : GWord N → ℕ | clArityC R (c, b) = j []})
              ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < j [] → (clSubC R (c, b) m).1 ∈ E m}))
            = ENNReal.ofReal (θ.skeletonWeight 1) ^ (r [])
                * (clCoinMassE (θ := θ) R (b []) (j [])
                  * ∏ m ∈ Finset.range (j []), survivalMeasure (N := N) θ (E m)) := by
          cases hb0 : b [] with
          | false =>
              rw [cluster_root_coin_false θ hJN hq hb0 (hj2 [] hroot) hEmeas, hb0]
          | true =>
              rw [cluster_root_coin_true θ hJN hq hs1 hb0 (hj2 [] hroot) hEmeas, hb0]
        rw [hstep, prodN_cons_decomp hroot hK, Finset.prod_congr rfl
          (fun m hm ↦ hrec m (Finset.mem_range.mp hm))]
        ring

/-- **The fixed-coin product formula**, at any prefix-closed probe. -/
theorem survivalMeasure_clusterC (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1) (R : ℕ)
    (F : Finset (List ℕ)) (hpc : ∀ u ∈ F, ∀ p : List ℕ, p <+: u → p ∈ F)
    (b : List ℕ → Bool) (r j : List ℕ → ℕ) (hj2 : ∀ u ∈ F, 2 ≤ j u)
    (hcomp : ∀ u ∈ F, ∀ i : ℕ, u ++ [i] ∈ F → i < j u) :
    survivalMeasure (N := N) θ
        (⋂ u ∈ F, ({c : GWord N → ℕ | clNeckAtC R (c, b) u = r u}
          ∩ {c : GWord N → ℕ | clArityAtC R (c, b) u = j u}))
      = ∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u)
          * clCoinMassE (θ := θ) R (b u) (j u) :=
  survivalMeasure_clusterC_aux θ hJN hq hs1 R (F.sup List.length) F
    (fun _ hu ↦ Finset.le_sup (f := List.length) hu) hpc b r j hj2 hcomp


/-! ### The coin field -/

lemma bernoulliLaw_apply_false {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    BranchingProcess.bernoulliLaw hβ0 hβ1 {false} = ENNReal.ofReal (1 - β) := by
  have hcompl : ({false} : Set Bool) = ({true} : Set Bool)ᶜ := by
    ext x
    cases x <;> simp
  rw [hcompl, measure_compl (measurableSet_singleton true) (measure_ne_top _ _),
    BranchingProcess.bernoulliLaw_apply_true, measure_univ, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 hβ0]

/-- The mass of a coin pattern over a finite set of presented addresses. -/
lemma bernoulliField_pattern {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (S : Finset (List ℕ))
    (ε : List ℕ → Bool) :
    BranchingProcess.bernoulliField (ι := List ℕ) hβ0 hβ1
        (⋂ u ∈ S, {b : List ℕ → Bool | b u = ε u})
      = ∏ u ∈ S, (if ε u then ENNReal.ofReal β else ENNReal.ofReal (1 - β)) := by
  have he : (⋂ u ∈ S, {b : List ℕ → Bool | b u = ε u})
      = ⋂ u ∈ S, (BranchingProcess.coord u : (List ℕ → Bool) → Bool) ⁻¹' {ε u} := by
    ext b
    simp [BranchingProcess.coord]
  rw [he, (BranchingProcess.bernoulliField_iIndepFun hβ0
      hβ1).measure_inter_preimage_eq_mul S (fun u _ ↦ measurableSet_singleton (ε u))]
  refine Finset.prod_congr rfl fun u _ ↦ ?_
  rw [show BranchingProcess.bernoulliField (ι := List ℕ) hβ0 hβ1
      = BranchingProcess.fieldMeasure (BranchingProcess.bernoulliLaw hβ0 hβ1) from rfl,
    BranchingProcess.coord_law _ u (measurableSet_singleton (ε u))]
  cases hε : ε u with
  | true =>
      rw [BranchingProcess.bernoulliLaw_apply_true]
      simp
  | false =>
      rw [bernoulliLaw_apply_false hβ0 hβ1]
      simp

/-! ### The i.i.d. clause of `thm:cluster-law` -/

/-- **The sample against the coin field**: the constructed space of the cluster
presentation, one Bernoulli coin per presented address, independent of the sample. -/
noncomputable def clusterMeasure (θ : Offspring J) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    Measure ((GWord N → ℕ) × (List ℕ → Bool)) :=
  (survivalMeasure (N := N) θ).prod (BranchingProcess.bernoulliField hβ0 hβ1)

/-- **`thm:cluster-law`, the i.i.d. clause**: over the sample against the coin field,
probed on a prefix-closed finite set of presented addresses whose letters respect the
presented arities, the presented pairs are independent: each address carries the
geometric neck mass against the coin-averaged arity mass. -/
theorem cluster_iid (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (R : ℕ)
    (F : Finset (List ℕ)) (hpc : ∀ u ∈ F, ∀ p : List ℕ, p <+: u → p ∈ F)
    (r j : List ℕ → ℕ) (hj2 : ∀ u ∈ F, 2 ≤ j u)
    (hcomp : ∀ u ∈ F, ∀ i : ℕ, u ++ [i] ∈ F → i < j u) :
    clusterMeasure (N := N) θ hβ0 hβ1
        (⋂ u ∈ F, ({ω : (GWord N → ℕ) × (List ℕ → Bool) | clNeckAtC R ω u = r u}
          ∩ {ω : (GWord N → ℕ) × (List ℕ → Bool) | clArityAtC R ω u = j u}))
      = ∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u)
          * (ENNReal.ofReal (1 - β) * clCoinMassE (θ := θ) R false (j u)
            + ENNReal.ofReal β * clCoinMassE (θ := θ) R true (j u)) := by
  classical
  set pext : (↥F → Bool) → (List ℕ → Bool) :=
    fun ε u ↦ if h : u ∈ F then ε ⟨u, h⟩ else false with hpext
  set CPart : (↥F → Bool) → Set (GWord N → ℕ) := fun ε ↦
    ⋂ u ∈ F, ({c : GWord N → ℕ | clNeckAtC R (c, pext ε) u = r u}
      ∩ {c : GWord N → ℕ | clArityAtC R (c, pext ε) u = j u}) with hCPart
  set BPart : (↥F → Bool) → Set (List ℕ → Bool) := fun ε ↦
    ⋂ u ∈ F, {b : List ℕ → Bool | b u = pext ε u} with hBPart
  have hcover : (⋂ u ∈ F, ({ω : (GWord N → ℕ) × (List ℕ → Bool) | clNeckAtC R ω u = r u}
        ∩ {ω : (GWord N → ℕ) × (List ℕ → Bool) | clArityAtC R ω u = j u}))
      = ⋃ ε : ↥F → Bool, CPart ε ×ˢ BPart ε := by
    ext ω
    obtain ⟨c, b⟩ := ω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_prod, hCPart, hBPart]
    constructor
    · intro h
      refine ⟨fun u ↦ b u.1, fun u hu ↦ ?_, fun u hu ↦ ?_⟩
      · have hpref : ∀ p : List ℕ, p <+: u → pext (fun v ↦ b v.1) p = b p := by
          intro p hp
          have hpF : p ∈ F := hpc u hu p hp
          simp only [hpext]
          rw [dif_pos hpF]
        obtain ⟨hn, ha⟩ := h u hu
        exact ⟨by rw [clNeckAtC_congr R u c _ _ hpref]; exact hn,
          by rw [clArityAtC_congr R u c _ _ hpref]; exact ha⟩
      · simp only [hpext]
        rw [dif_pos hu]
    · rintro ⟨ε, hc, hb⟩ u hu
      have hpref : ∀ p : List ℕ, p <+: u → b p = pext ε p := by
        intro p hp
        exact hb p (hpc u hu p hp)
      obtain ⟨hn, ha⟩ := hc u hu
      exact ⟨by rw [clNeckAtC_congr R u c _ _ hpref]; exact hn,
        by rw [clArityAtC_congr R u c _ _ hpref]; exact ha⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun ε : ↥F → Bool ↦
      CPart ε ×ˢ BPart ε) := by
    intro ε ε' hne
    refine Set.disjoint_left.mpr fun ω hω hω' ↦ hne ?_
    funext u
    have h1 := hω.2
    have h2 := hω'.2
    simp only [hBPart, Set.mem_iInter, Set.mem_setOf_eq] at h1 h2
    have e1 := h1 u.1 u.2
    have e2 := h2 u.1 u.2
    simp only [hpext] at e1 e2
    rw [dif_pos u.2] at e1 e2
    exact e1.symm.trans e2
  have hmeas : ∀ ε : ↥F → Bool, MeasurableSet (CPart ε ×ˢ BPart ε) := by
    intro ε
    refine MeasurableSet.prod ?_ ?_
    · exact MeasurableSet.biInter (Finset.countable_toSet _) fun u _ ↦
        (measurableSet_clNeckAtC_eq R _ u (r u)).inter
          (measurableSet_clArityAtC_eq R _ u (j u))
    · exact MeasurableSet.biInter (Finset.countable_toSet _) fun u _ ↦
        BranchingProcess.measurable_coord u (measurableSet_singleton _)
  rw [hcover, measure_iUnion hdisj hmeas, tsum_fintype]
  have hterm : ∀ ε : ↥F → Bool,
      clusterMeasure (N := N) θ hβ0 hβ1 (CPart ε ×ˢ BPart ε)
        = ∏ u ∈ F.attach,
            ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u.1)
              * clCoinMassE (θ := θ) R (ε u) (j u.1)
              * (if ε u then ENNReal.ofReal β else ENNReal.ofReal (1 - β)) := by
    intro ε
    rw [clusterMeasure, Measure.prod_prod, hCPart, hBPart,
      survivalMeasure_clusterC θ hJN hq hs1 R F hpc (pext ε) r j hj2 hcomp,
      bernoulliField_pattern hβ0 hβ1 F (pext ε), ← Finset.prod_mul_distrib,
      ← Finset.prod_attach F (fun u ↦
        ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u)
          * clCoinMassE (θ := θ) R (pext ε u) (j u)
          * (if pext ε u then ENNReal.ofReal β else ENNReal.ofReal (1 - β)))]
    refine Finset.prod_congr rfl fun u _ ↦ ?_
    simp only [hpext]
    rw [dif_pos u.2]
  rw [Finset.sum_congr rfl fun ε _ ↦ hterm ε]
  have hattach : F.attach = (Finset.univ : Finset ↥F) :=
    Finset.eq_univ_of_forall (Finset.mem_attach F)
  have hswap := Finset.prod_univ_sum
    (t := fun _ : ↥F ↦ (Finset.univ : Finset Bool))
    (f := fun (u : ↥F) (b0 : Bool) ↦
      ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u.1)
        * clCoinMassE (θ := θ) R b0 (j u.1)
        * (if b0 then ENNReal.ofReal β else ENNReal.ofReal (1 - β)))
  rw [Fintype.piFinset_univ] at hswap
  calc ∑ ε : ↥F → Bool, ∏ u ∈ F.attach,
        ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u.1)
          * clCoinMassE (θ := θ) R (ε u) (j u.1)
          * (if ε u then ENNReal.ofReal β else ENNReal.ofReal (1 - β))
      = ∏ u ∈ (Finset.univ : Finset ↥F), ∑ b0 ∈ (Finset.univ : Finset Bool),
          ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u.1)
            * clCoinMassE (θ := θ) R b0 (j u.1)
            * (if b0 then ENNReal.ofReal β else ENNReal.ofReal (1 - β)) := by
        rw [hswap]
        refine Finset.sum_congr rfl fun ε _ ↦ ?_
        rw [hattach]
    _ = ∏ u ∈ F.attach, (fun v : List ℕ ↦
          ENNReal.ofReal (θ.skeletonWeight 1) ^ (r v)
            * (ENNReal.ofReal (1 - β) * clCoinMassE (θ := θ) R false (j v)
              + ENNReal.ofReal β * clCoinMassE (θ := θ) R true (j v))) u.1 := by
        rw [hattach]
        refine Finset.prod_congr rfl fun u _ ↦ ?_
        rw [Fintype.sum_bool, if_pos rfl, if_neg Bool.false_ne_true]
        ring
    _ = ∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u)
          * (ENNReal.ofReal (1 - β) * clCoinMassE (θ := θ) R false (j u)
            + ENNReal.ofReal β * clCoinMassE (θ := θ) R true (j u)) :=
      Finset.prod_attach F (fun v : List ℕ ↦
        ENNReal.ofReal (θ.skeletonWeight 1) ^ (r v)
          * (ENNReal.ofReal (1 - β) * clCoinMassE (θ := θ) R false (j v)
            + ENNReal.ofReal β * clCoinMassE (θ := θ) R true (j v)))


/-! ### The presented arity law is `eq:cluster-law` -/

/-- The reduced law as a mass function on `ℕ`, vanishing below arity two. -/
noncomputable def redNu (θ : Offspring J) : ℕ → ℝ :=
  fun k ↦ if k = 1 then 0 else reducedWeight θ k

lemma redNu_one (θ : Offspring J) : redNu θ 1 = 0 := by
  rw [redNu, if_pos rfl]

lemma redNu_zero (θ : Offspring J) : redNu θ 0 = 0 := by
  rw [redNu, if_neg (by omega), reducedWeight_def, θ.skeletonWeight_zero, zero_div]

/-- **The coin-averaged arity mass is `eq:cluster-law`**: averaging the two coins gives
`(1-θ̃₁)ν_t` with `ν_t = (1-t)ν̃ + t(ν̃ ⊛ ν̃)` at `t = β(1-θ̃₁^R)`. -/
theorem clusterMass_eq_clusterLaw (θ : Offspring J) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (R : ℕ)
    {j : ℕ} (hj : 2 ≤ j) :
    ENNReal.ofReal (1 - β) * clCoinMassE (θ := θ) R false j
        + ENNReal.ofReal β * clCoinMassE (θ := θ) R true j
      = ENNReal.ofReal ((1 - θ.skeletonWeight 1)
          * clusterLaw (β * (1 - θ.skeletonWeight 1 ^ R)) (redNu θ) j) := by
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  have h1a : (0 : ℝ) < 1 - θ.skeletonWeight 1 := by linarith
  have hane : (1 : ℝ) - θ.skeletonWeight 1 ≠ 0 := ne_of_gt h1a
  have hnn : ∀ k, 0 ≤ θ.skeletonWeight k := θ.skeletonWeight_nonneg hq
  -- the true coin in real form
  have htrue : clCoinMassE (θ := θ) R true j
      = ENNReal.ofReal ((∑ d ∈ Finset.range R, θ.skeletonWeight 1 ^ d)
          * (∑ p ∈ Finset.Icc 2 (j - 1),
              θ.skeletonWeight p * θ.skeletonWeight (j + 1 - p))
        + θ.skeletonWeight 1 ^ R * θ.skeletonWeight j) := by
    rw [clCoinMassE_true]
    have hgeom : ∑ d ∈ Finset.range R, ENNReal.ofReal (θ.skeletonWeight 1) ^ d
        = ENNReal.ofReal (∑ d ∈ Finset.range R, θ.skeletonWeight 1 ^ d) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun d _ ↦ pow_nonneg ha0 d]
      exact Finset.sum_congr rfl fun d _ ↦ (ENNReal.ofReal_pow ha0 d).symm
    have hconv : ∑ p ∈ Finset.Icc 2 (j - 1),
          ENNReal.ofReal (θ.skeletonWeight p) * ENNReal.ofReal (θ.skeletonWeight (j + 1 - p))
        = ENNReal.ofReal (∑ p ∈ Finset.Icc 2 (j - 1),
            θ.skeletonWeight p * θ.skeletonWeight (j + 1 - p)) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun p _ ↦ mul_nonneg (hnn p) (hnn _)]
      exact Finset.sum_congr rfl fun p _ ↦ (ENNReal.ofReal_mul (hnn p)).symm
    rw [hgeom, hconv, ← ENNReal.ofReal_mul (Finset.sum_nonneg fun d _ ↦ pow_nonneg ha0 d),
      ← ENNReal.ofReal_pow ha0, ← ENNReal.ofReal_mul (pow_nonneg ha0 R),
      ← ENNReal.ofReal_add
        (mul_nonneg (Finset.sum_nonneg fun d _ ↦ pow_nonneg ha0 d)
          (Finset.sum_nonneg fun p _ ↦ mul_nonneg (hnn p) (hnn _)))
        (mul_nonneg (pow_nonneg ha0 R) (hnn j))]
  rw [clCoinMassE_false, htrue, ← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ 1 - β),
    ← ENNReal.ofReal_mul hβ0,
    ← ENNReal.ofReal_add (mul_nonneg (by linarith) (hnn j))
      (mul_nonneg hβ0 (add_nonneg
        (mul_nonneg (Finset.sum_nonneg fun d _ ↦ pow_nonneg ha0 d)
          (Finset.sum_nonneg fun p _ ↦ mul_nonneg (hnn p) (hnn _)))
        (mul_nonneg (pow_nonneg ha0 R) (hnn j))))]
  congr 1
  -- the geometric window
  have hgeom : ∑ d ∈ Finset.range R, θ.skeletonWeight 1 ^ d
      = (1 - θ.skeletonWeight 1 ^ R) / (1 - θ.skeletonWeight 1) := by
    rw [geom_sum_eq (by linarith : θ.skeletonWeight 1 ≠ 1) R]
    rw [div_eq_div_iff (by linarith) hane]
    ring
  -- the shifted convolution of the reduced law
  have hconv : shiftConv (redNu θ) j
      = (∑ p ∈ Finset.Icc 2 (j - 1),
          θ.skeletonWeight p * θ.skeletonWeight (j + 1 - p))
        / ((1 - θ.skeletonWeight 1) * (1 - θ.skeletonWeight 1)) := by
    rw [shiftConv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hsub : Finset.Icc 2 (j - 1) ⊆ Finset.range (j + 1 + 1) := by
      intro p hp
      rw [Finset.mem_Icc] at hp
      rw [Finset.mem_range]
      omega
    have hvanish : ∀ p ∈ Finset.range (j + 1 + 1), p ∉ Finset.Icc 2 (j - 1) →
        redNu θ p * redNu θ (j + 1 - p) = 0 := by
      intro p hp hpn
      rw [Finset.mem_range] at hp
      rw [Finset.mem_Icc] at hpn
      rcases (by omega : p = 0 ∨ p = 1 ∨ j ≤ p) with rfl | rfl | hpj
      · rw [redNu_zero, zero_mul]
      · rw [redNu_one, zero_mul]
      · rcases (by omega : j + 1 - p = 0 ∨ j + 1 - p = 1) with h1 | h1
        · rw [h1, redNu_zero, mul_zero]
        · rw [h1, redNu_one, mul_zero]
    rw [← Finset.sum_subset hsub hvanish, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [Finset.mem_Icc] at hp
    rw [redNu, if_neg (by omega), redNu, if_neg (by omega), reducedWeight_def,
      reducedWeight_def]
    field_simp
  -- assemble
  rw [clusterLaw, hgeom, hconv, redNu, if_neg (by omega), reducedWeight_def]
  field_simp
  ring

/-- **`thm:cluster-law`, the i.i.d. clause with the presented law `eq:cluster-law`**:
each probed address carries the geometric neck mass `θ̃₁^r(1-θ̃₁)` against the presented
arity law `ν_t` at `t = β(1-θ̃₁^R)`. -/
theorem cluster_iid_clusterLaw (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (R : ℕ)
    (F : Finset (List ℕ)) (hpc : ∀ u ∈ F, ∀ p : List ℕ, p <+: u → p ∈ F)
    (r j : List ℕ → ℕ) (hj2 : ∀ u ∈ F, 2 ≤ j u)
    (hcomp : ∀ u ∈ F, ∀ i : ℕ, u ++ [i] ∈ F → i < j u) :
    clusterMeasure (N := N) θ hβ0 hβ1
        (⋂ u ∈ F, ({ω : (GWord N → ℕ) × (List ℕ → Bool) | clNeckAtC R ω u = r u}
          ∩ {ω : (GWord N → ℕ) × (List ℕ → Bool) | clArityAtC R ω u = j u}))
      = ∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight 1 ^ (r u)
          * ((1 - θ.skeletonWeight 1)
            * clusterLaw (β * (1 - θ.skeletonWeight 1 ^ R)) (redNu θ) (j u))) := by
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  rw [cluster_iid θ hJN hq hs1 hβ0 hβ1 R F hpc r j hj2 hcomp]
  refine Finset.prod_congr rfl fun u hu ↦ ?_
  rw [clusterMass_eq_clusterLaw θ hq hs1 hβ0 hβ1 R (hj2 u hu),
    ← ENNReal.ofReal_pow ha0, ← ENNReal.ofReal_mul (pow_nonneg ha0 _)]


/-! ### The chain regime: the transform is the identity -/

/-- **The chain regime of `thm:harris-general`**: with no extinction the transform is
the identity, so every skeleton weight is the offspring mass itself. -/
lemma skeletonWeight_of_extinction_zero (θ : Offspring J) (h0 : θ.extinction = 0)
    (hθ0 : θ 0 = 0) (k : ℕ) : θ.skeletonWeight k = θ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [θ.skeletonWeight_zero, hθ0]
  · rw [BranchingProcess.Offspring.skeletonWeight_of_ne_zero θ (by omega),
      BranchingProcess.Offspring.surviveWeight, h0]
    have hterm : ∀ j ∈ Finset.range (J + 1),
        θ j * (j.choose k : ℝ) * (1 - 0) ^ k * (0 : ℝ) ^ (j - k)
          = if j = k then θ k else 0 := by
      intro j _
      rcases lt_trichotomy j k with hjk | rfl | hjk
      · rw [Nat.choose_eq_zero_of_lt hjk, if_neg (by omega)]
        simp
      · simp
      · rw [if_neg (by omega), zero_pow (by omega : j - k ≠ 0)]
        ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (J + 1)) k
      (fun _ ↦ θ k)]
    by_cases hkJ : k ∈ Finset.range (J + 1)
    · rw [if_pos hkJ]
      simp
    · rw [if_neg hkJ, θ.vanishing k (by
        rw [Finset.mem_range] at hkJ
        omega)]
      simp

/-- **`thm:cluster-law` in the chain regime**: with `θ₀ = 0` and `θ₁ < 1`, over the
sample against the coin field the presented pairs are i.i.d., the presented neck depth
carries `θ₁^r(1-θ₁)` and the presented arity the law `ν_t` of `eq:cluster-law` at
`t = β(1-θ₁^R)`, the reduced law being `ν̃_j = θ_j/(1-θ₁)`. -/
theorem cluster_iid_chain (θ : Offspring J) (hJN : J ≤ N) (h0 : θ.extinction = 0)
    (hθ0 : θ 0 = 0) (hθ1 : θ 1 < 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (R : ℕ)
    (F : Finset (List ℕ)) (hpc : ∀ u ∈ F, ∀ p : List ℕ, p <+: u → p ∈ F)
    (r j : List ℕ → ℕ) (hj2 : ∀ u ∈ F, 2 ≤ j u)
    (hcomp : ∀ u ∈ F, ∀ i : ℕ, u ++ [i] ∈ F → i < j u) :
    clusterMeasure (N := N) θ hβ0 hβ1
        (⋂ u ∈ F, ({ω : (GWord N → ℕ) × (List ℕ → Bool) | clNeckAtC R ω u = r u}
          ∩ {ω : (GWord N → ℕ) × (List ℕ → Bool) | clArityAtC R ω u = j u}))
      = ∏ u ∈ F, ENNReal.ofReal (θ 1 ^ (r u)
          * ((1 - θ 1)
            * clusterLaw (β * (1 - θ 1 ^ R)) (redNu θ) (j u))) := by
  have hq : θ.extinction < 1 := by
    rw [h0]
    norm_num
  have hs1 : θ.skeletonWeight 1 < 1 := by
    rw [skeletonWeight_of_extinction_zero θ h0 hθ0 1]
    exact hθ1
  rw [cluster_iid_clusterLaw θ hJN hq hs1 hβ0 hβ1 R F hpc r j hj2 hcomp]
  refine Finset.prod_congr rfl fun u _ ↦ ?_
  rw [skeletonWeight_of_extinction_zero θ h0 hθ0 1]

end ChainClasses
