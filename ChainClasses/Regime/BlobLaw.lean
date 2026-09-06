import ChainClasses.Regime.BlobRoot
import ChainClasses.Regime.ClusterIID

/-!
`sec:general-chain` of `matching_classes_general.tex`: **the adapted-stopping clause of
`thm:blob-law`** over the presented skeleton, on the constructed space.

The rule's randomisation is one coin per presented address, drawn from a finite type
with an arbitrary law, which carries every rule of `def:blob` at bounded support: the
number of decisions inside one blob is bounded by the stopping bound, so a finite coin
realises any adapted randomised stopping.  The coin field decomposes a prefix-closed
probe into rectangles as in `ClusterIID`, the fixed-coin factor is an induction over
the probe whose root step is `BlobRoot`, and summing the coin patterns back gives the
presented pairs i.i.d., the neck geometric against the coin-averaged rule mass.

`bRuleMass` is the machine's form of the stopped sum of `thm:blob-law`: one summand per
rule-consistent trace, the split weight of the root against one window factor per
absorbed split and one `θ̃₁^R` factor per spent exit.  The misses are what
`eq:reach-mix` ignores: `bRuleMass_pos` shows every arity of the reduced support is
charged by every rule, so the exact mixtures with a vanishing first coefficient are not
reachable and the containment clause of `thm:blob-law` holds only up to the miss mass.
`bRuleMass_stopRule` is the sanity identification: the rule that always stops presents
the reduced law itself.

* `survivalMeasure_blobC`: **the fixed-coin product formula** over prefix-closed
  probes.
* `blobMeasure`, `coinField_pattern`: the sample against the coin field, and the mass
  of a coin pattern.
* `blob_iid`: **`thm:blob-law`, the i.i.d. clause**: over the sample against the coin
  field the presented pairs are independent, the presented neck geometric and the
  presented arity carrying the averaged rule mass.
* `missRun`, `bRuleMass_pos`: every arity of the reduced support is charged by every
  rule, the witness that the exact mixtures of `eq:reach-mix` are out of reach.
* `stopRule`, `bRuleMass_stopRule`: the rule that always stops presents `θ̃`.
-/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal
open BranchingProcess (Survives skeletonDegree Offspring sampleMeasure survivalMeasure
  bushAt)

variable {J N : ℕ} {σ : Type*}

/-! ### The fixed-coin product formula -/

/-- **The fixed-coin product formula**: at a fixed coin field the presented pairs over
a prefix-closed probe are independent, one geometric neck mass against one rule mass
per address, the coin of the mass read at the address. -/
theorem survivalMeasure_blobC_aux (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1) (R : ℕ) (ρr : BRule σ) :
    ∀ (n : ℕ) (F : Finset (List ℕ)), (∀ u ∈ F, u.length ≤ n) →
      (∀ u ∈ F, ∀ p : List ℕ, p <+: u → p ∈ F) →
      ∀ (b : List ℕ → σ) (r j : List ℕ → ℕ),
        (∀ u ∈ F, ∀ i : ℕ, u ++ [i] ∈ F → i < j u) →
        survivalMeasure (N := N) θ
            (⋂ u ∈ F, ({c : GWord N → ℕ | bNeckAtC R ρr (c, b) u = r u}
              ∩ {c : GWord N → ℕ | bArityAtC R ρr (c, b) u = j u}))
          = ∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u)
              * bRuleMass θ R ρr (b u) (j u) := by
  classical
  have _ := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  intro n
  induction n with
  | zero =>
      intro F hlen hpc b r j hcomp
      rcases F.eq_empty_or_nonempty with rfl | hne
      · simp
      · obtain ⟨v, hv⟩ := hne
        have hroot : ([] : List ℕ) ∈ F := hpc v hv [] List.nil_prefix
        have hF : F = {[]} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hroot, fun v' hv' ↦ ?_⟩
          exact List.length_eq_zero_iff.mp (Nat.le_zero.mp (hlen v' hv'))
        subst hF
        have hset : (⋂ u ∈ ({[]} : Finset (List ℕ)),
              ({c : GWord N → ℕ | bNeckAtC R ρr (c, b) u = r u}
                ∩ {c : GWord N → ℕ | bArityAtC R ρr (c, b) u = j u}))
            = (({c : GWord N → ℕ | gSplitDepth c = r []}
                ∩ {c : GWord N → ℕ | bArityC R ρr (c, b) = j []})
              ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < j [] →
                  (bSubC R ρr (c, b) m).1 ∈ (Set.univ : Set (GWord N → ℕ))}) := by
          ext c
          simp
        rw [hset, blob_root_fixed θ hJN hq hs1 R ρr b (fun _ ↦ MeasurableSet.univ),
          Finset.prod_singleton]
        simp
  | succ n ih =>
      intro F hlen hpc b r j hcomp
      rcases F.eq_empty_or_nonempty with rfl | hne
      · simp
      · obtain ⟨v, hv⟩ := hne
        have hroot : ([] : List ℕ) ∈ F := hpc v hv [] List.nil_prefix
        set E : ℕ → Set (GWord N → ℕ) := fun m ↦
          ⋂ u ∈ consSubN m F,
            ({d : GWord N → ℕ | bNeckAtC R ρr (d, fun w ↦ b (m :: w)) u = r (m :: u)}
              ∩ {d : GWord N → ℕ |
                  bArityAtC R ρr (d, fun w ↦ b (m :: w)) u = j (m :: u)})
          with hE
        have hEmeas : ∀ m : ℕ, MeasurableSet (E m) := by
          intro m
          rw [hE]
          exact MeasurableSet.biInter (Finset.countable_toSet _) fun u _ ↦
            (measurableSet_bNeckAtC_eq R ρr _ u (r (m :: u))).inter
              (measurableSet_bArityAtC_eq R ρr _ u (j (m :: u)))
        have hset : (⋂ u ∈ F, ({c : GWord N → ℕ | bNeckAtC R ρr (c, b) u = r u}
              ∩ {c : GWord N → ℕ | bArityAtC R ρr (c, b) u = j u}))
            = (({c : GWord N → ℕ | gSplitDepth c = r []}
                ∩ {c : GWord N → ℕ | bArityC R ρr (c, b) = j []})
              ∩ {c : GWord N → ℕ | ∀ m : ℕ, m < j [] →
                  (bSubC R ρr (c, b) m).1 ∈ E m}) := by
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
            rw [bNeckAtC_cons, bSubC_eta] at hnu
            rw [bArityAtC_cons, bSubC_eta] at hau
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
                rw [bNeckAtC_cons, bSubC_eta]
                exact ⟨hnu, hau⟩
        have hrec : ∀ m : ℕ, m < j [] →
            survivalMeasure (N := N) θ (E m)
              = ∏ u ∈ consSubN m F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (r (m :: u))
                  * bRuleMass θ R ρr (b (m :: u)) (j (m :: u)) := by
          intro m _
          rw [hE]
          exact ih (consSubN m F)
            (fun u hu ↦ by
              have := hlen _ (mem_consSubN.mp hu)
              simpa using this)
            (fun u hu p hp ↦ mem_consSubN.mpr
              (hpc _ (mem_consSubN.mp hu) _ (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)))
            (fun w ↦ b (m :: w)) (fun u ↦ r (m :: u)) (fun u ↦ j (m :: u))
            (fun u hu i hi ↦ hcomp _ (mem_consSubN.mp hu) i (mem_consSubN.mp hi))
        have hK : ∀ (i : ℕ) (u : List ℕ), (i :: u) ∈ F → i < j [] := by
          intro i u hu
          have h1 : [i] ∈ F := hpc _ hu [i] ⟨u, rfl⟩
          exact hcomp [] hroot i (by simpa using h1)
        rw [hset, blob_root_fixed θ hJN hq hs1 R ρr b hEmeas,
          prodN_cons_decomp hroot hK, Finset.prod_congr rfl
            (fun m hm ↦ hrec m (Finset.mem_range.mp hm))]
        ring

/-- **The fixed-coin product formula**, at any prefix-closed probe. -/
theorem survivalMeasure_blobC (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) (R : ℕ) (ρr : BRule σ) (F : Finset (List ℕ))
    (hpc : ∀ u ∈ F, ∀ p : List ℕ, p <+: u → p ∈ F) (b : List ℕ → σ)
    (r j : List ℕ → ℕ) (hcomp : ∀ u ∈ F, ∀ i : ℕ, u ++ [i] ∈ F → i < j u) :
    survivalMeasure (N := N) θ
        (⋂ u ∈ F, ({c : GWord N → ℕ | bNeckAtC R ρr (c, b) u = r u}
          ∩ {c : GWord N → ℕ | bArityAtC R ρr (c, b) u = j u}))
      = ∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u)
          * bRuleMass θ R ρr (b u) (j u) :=
  survivalMeasure_blobC_aux θ hJN hq hs1 R ρr (F.sup List.length) F
    (fun _ hu ↦ Finset.le_sup (f := List.length) hu) hpc b r j hcomp

/-! ### The coin field -/

variable [MeasurableSpace σ] [MeasurableSingletonClass σ]

/-- The mass of a coin pattern over a finite set of presented addresses. -/
lemma coinField_pattern (ρ : Measure σ) [IsProbabilityMeasure ρ] (S : Finset (List ℕ))
    (ε : List ℕ → σ) :
    BranchingProcess.fieldMeasure (ι := List ℕ) ρ
        (⋂ u ∈ S, {b : List ℕ → σ | b u = ε u})
      = ∏ u ∈ S, ρ {ε u} := by
  have he : (⋂ u ∈ S, {b : List ℕ → σ | b u = ε u})
      = ⋂ u ∈ S, (BranchingProcess.coord u : (List ℕ → σ) → σ) ⁻¹' {ε u} := by
    ext b
    simp [BranchingProcess.coord]
  rw [he, (BranchingProcess.coord_iIndepFun (ι := List ℕ)
      ρ).measure_inter_preimage_eq_mul S (fun u _ ↦ measurableSet_singleton (ε u))]
  exact Finset.prod_congr rfl fun u _ ↦
    BranchingProcess.coord_law ρ u (measurableSet_singleton (ε u))

/-- **The sample against the coin field**: the constructed space of the blob
presentation, one coin per presented address, independent of the sample. -/
noncomputable def blobMeasure (θ : Offspring J) (ρ : Measure σ)
    [IsProbabilityMeasure ρ] : Measure ((GWord N → ℕ) × (List ℕ → σ)) :=
  (survivalMeasure (N := N) θ).prod (BranchingProcess.fieldMeasure ρ)

/-! ### The i.i.d. clause -/

/-- **`thm:blob-law`, the i.i.d. clause**: over the sample against the coin field,
probed on a prefix-closed finite set of presented addresses whose letters respect the
presented arities, the presented pairs are independent: each address carries the
geometric neck mass against the coin-averaged rule mass. -/
theorem blob_iid (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) [Fintype σ] [Inhabited σ] (ρ : Measure σ)
    [IsProbabilityMeasure ρ] (R : ℕ) (ρr : BRule σ) (F : Finset (List ℕ))
    (hpc : ∀ u ∈ F, ∀ p : List ℕ, p <+: u → p ∈ F) (r j : List ℕ → ℕ)
    (hcomp : ∀ u ∈ F, ∀ i : ℕ, u ++ [i] ∈ F → i < j u) :
    blobMeasure (N := N) θ ρ
        (⋂ u ∈ F, ({ω : (GWord N → ℕ) × (List ℕ → σ) | bNeckAtC R ρr ω u = r u}
          ∩ {ω : (GWord N → ℕ) × (List ℕ → σ) | bArityAtC R ρr ω u = j u}))
      = ∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u)
          * ∑ s : σ, ρ {s} * bRuleMass θ R ρr s (j u) := by
  classical
  set pext : (↥F → σ) → (List ℕ → σ) :=
    fun ε u ↦ if h : u ∈ F then ε ⟨u, h⟩ else default with hpext
  set CPart : (↥F → σ) → Set (GWord N → ℕ) := fun ε ↦
    ⋂ u ∈ F, ({c : GWord N → ℕ | bNeckAtC R ρr (c, pext ε) u = r u}
      ∩ {c : GWord N → ℕ | bArityAtC R ρr (c, pext ε) u = j u}) with hCPart
  set BPart : (↥F → σ) → Set (List ℕ → σ) := fun ε ↦
    ⋂ u ∈ F, {b : List ℕ → σ | b u = pext ε u} with hBPart
  have hcover : (⋂ u ∈ F,
        ({ω : (GWord N → ℕ) × (List ℕ → σ) | bNeckAtC R ρr ω u = r u}
          ∩ {ω : (GWord N → ℕ) × (List ℕ → σ) | bArityAtC R ρr ω u = j u}))
      = ⋃ ε : ↥F → σ, CPart ε ×ˢ BPart ε := by
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
        exact ⟨by rw [bNeckAtC_congr R ρr u c _ _ hpref]; exact hn,
          by rw [bArityAtC_congr R ρr u c _ _ hpref]; exact ha⟩
      · simp only [hpext]
        rw [dif_pos hu]
    · rintro ⟨ε, hc, hb⟩ u hu
      have hpref : ∀ p : List ℕ, p <+: u → b p = pext ε p := by
        intro p hp
        exact hb p (hpc u hu p hp)
      obtain ⟨hn, ha⟩ := hc u hu
      exact ⟨by rw [bNeckAtC_congr R ρr u c _ _ hpref]; exact hn,
        by rw [bArityAtC_congr R ρr u c _ _ hpref]; exact ha⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun ε : ↥F → σ ↦
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
  have hmeas : ∀ ε : ↥F → σ, MeasurableSet (CPart ε ×ˢ BPart ε) := by
    intro ε
    refine MeasurableSet.prod ?_ ?_
    · exact MeasurableSet.biInter (Finset.countable_toSet _) fun u _ ↦
        (measurableSet_bNeckAtC_eq R ρr _ u (r u)).inter
          (measurableSet_bArityAtC_eq R ρr _ u (j u))
    · exact MeasurableSet.biInter (Finset.countable_toSet _) fun u _ ↦
        BranchingProcess.measurable_coord u (measurableSet_singleton _)
  rw [hcover, measure_iUnion hdisj hmeas, tsum_fintype]
  have hterm : ∀ ε : ↥F → σ,
      blobMeasure (N := N) θ ρ (CPart ε ×ˢ BPart ε)
        = ∏ u ∈ F.attach,
            ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u.1)
              * bRuleMass θ R ρr (ε u) (j u.1) * ρ {ε u} := by
    intro ε
    rw [blobMeasure, Measure.prod_prod, hCPart, hBPart,
      survivalMeasure_blobC θ hJN hq hs1 R ρr F hpc (pext ε) r j hcomp,
      coinField_pattern ρ F (pext ε), ← Finset.prod_mul_distrib,
      ← Finset.prod_attach F (fun u ↦
        ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u)
          * bRuleMass θ R ρr (pext ε u) (j u) * ρ {pext ε u})]
    refine Finset.prod_congr rfl fun u _ ↦ ?_
    simp only [hpext]
    rw [dif_pos u.2]
  rw [Finset.sum_congr rfl fun ε _ ↦ hterm ε]
  have hattach : F.attach = (Finset.univ : Finset ↥F) :=
    Finset.eq_univ_of_forall (Finset.mem_attach F)
  have hswap := Finset.prod_univ_sum
    (t := fun _ : ↥F ↦ (Finset.univ : Finset σ))
    (f := fun (u : ↥F) (s : σ) ↦
      ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u.1)
        * bRuleMass θ R ρr s (j u.1) * ρ {s})
  rw [Fintype.piFinset_univ] at hswap
  calc ∑ ε : ↥F → σ, ∏ u ∈ F.attach,
        ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u.1)
          * bRuleMass θ R ρr (ε u) (j u.1) * ρ {ε u}
      = ∏ u ∈ (Finset.univ : Finset ↥F), ∑ s ∈ (Finset.univ : Finset σ),
          ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u.1)
            * bRuleMass θ R ρr s (j u.1) * ρ {s} := by
        rw [hswap]
        refine Finset.sum_congr rfl fun ε _ ↦ ?_
        rw [hattach]
    _ = ∏ u ∈ F.attach, (ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u.1)
            * ∑ s : σ, ρ {s} * bRuleMass θ R ρr s (j u.1)) := by
        rw [hattach]
        refine Finset.prod_congr rfl fun u _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        ring
    _ = ∏ u ∈ F, ENNReal.ofReal (θ.skeletonWeight 1) ^ (r u)
          * ∑ s : σ, ρ {s} * bRuleMass θ R ρr s (j u) :=
      Finset.prod_attach F (fun v : List ℕ ↦
        ENNReal.ofReal (θ.skeletonWeight 1) ^ (r v)
          * ∑ s : σ, ρ {s} * bRuleMass θ R ρr s (j v))

/-! ### Every arity of the reduced support is charged -/

/-- The zero-hit run of a rule: skip once stopped, spend an exit otherwise. -/
noncomputable def missRun (dec : List (Option ℕ) → Bool) :
    ℕ → Bool × List (Option ℕ) → List BTrace
  | 0, _ => []
  | k + 1, (stopped, evs) =>
      if stopped = true ∨ dec evs = false then
        .skip :: missRun dec k (true, evs)
      else .miss :: missRun dec k (false, evs ++ [none])

lemma missRun_zero (dec : List (Option ℕ) → Bool) (st : Bool × List (Option ℕ)) :
    missRun dec 0 st = [] := by
  obtain ⟨b, evs⟩ := st
  rw [missRun.eq_def]

lemma missRun_succ (dec : List (Option ℕ) → Bool) (k : ℕ) (stopped : Bool)
    (evs : List (Option ℕ)) :
    missRun dec (k + 1) (stopped, evs)
      = if stopped = true ∨ dec evs = false then
          BTrace.skip :: missRun dec k (true, evs)
        else BTrace.miss :: missRun dec k (false, evs ++ [none]) := by
  rw [missRun.eq_def]

lemma missRun_length (dec : List (Option ℕ) → Bool) :
    ∀ (k : ℕ) (st : Bool × List (Option ℕ)), (missRun dec k st).length = k
  | 0, st => by rw [missRun_zero]; rfl
  | k + 1, (stopped, evs) => by
      rw [missRun_succ]
      by_cases h : stopped = true ∨ dec evs = false
      · rw [if_pos h]
        simp [missRun_length dec k (true, evs)]
      · rw [if_neg h]
        simp [missRun_length dec k (false, evs ++ [none])]

lemma missRun_bConsL (dec : List (Option ℕ) → Bool) :
    ∀ (k : ℕ) (st : Bool × List (Option ℕ)), bConsL dec (missRun dec k st) st
  | 0, st => by
      rw [missRun_zero]
      exact bConsL_nil
  | k + 1, (stopped, evs) => by
      rw [missRun_succ]
      by_cases h : stopped = true ∨ dec evs = false
      · rw [if_pos h, bConsL_cons]
        refine ⟨bCons_skip.mpr h, ?_⟩
        rw [bThread1_skip]
        exact missRun_bConsL dec k (true, evs)
      · rw [if_neg h]
        have hst : stopped = false := by
          cases stopped with
          | false => rfl
          | true => exact absurd (Or.inl rfl) h
        have hdec : dec evs = true := by
          cases hb : dec evs with
          | false => exact absurd (Or.inr hb) h
          | true => rfl
        subst hst
        rw [bConsL_cons]
        refine ⟨bCons_miss.mpr ⟨rfl, hdec⟩, ?_⟩
        rw [bThread1_miss]
        exact missRun_bConsL dec k (false, evs ++ [none])

lemma missRun_flat (dec : List (Option ℕ) → Bool) :
    ∀ (k : ℕ) (st : Bool × List (Option ℕ)),
      ∀ t ∈ missRun dec k st, t = BTrace.skip ∨ t = BTrace.miss
  | 0, st => by
      rw [missRun_zero]
      intro t ht
      exact absurd ht (List.not_mem_nil)
  | k + 1, (stopped, evs) => by
      rw [missRun_succ]
      by_cases h : stopped = true ∨ dec evs = false
      · rw [if_pos h]
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Or.inl rfl
        · exact missRun_flat dec k (true, evs) t ht
      · rw [if_neg h]
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Or.inr rfl
        · exact missRun_flat dec k (false, evs ++ [none]) t ht

lemma missRun_BOkL (dec : List (Option ℕ) → Bool) (k : ℕ)
    (st : Bool × List (Option ℕ)) : BOkL (missRun dec k st) := by
  intro t ht
  rcases missRun_flat dec k st t ht with rfl | rfl
  · exact BOk_skip
  · exact BOk_miss

lemma missRun_bShiftL (dec : List (Option ℕ) → Bool) (k : ℕ)
    (st : Bool × List (Option ℕ)) : bShiftL (missRun dec k st) = 0 := by
  have hall : ∀ t ∈ missRun dec k st, bShift t = 0 := by
    intro t ht
    rcases missRun_flat dec k st t ht with rfl | rfl
    · exact bShift_skip
    · exact bShift_miss
  rw [bShiftL, List.map_congr_left hall]
  simp

lemma missRun_traceMassL_pos (θ : Offspring J) (R : ℕ)
    (hs0 : 0 < θ.skeletonWeight 1) (dec : List (Option ℕ) → Bool) :
    ∀ (k : ℕ) (st : Bool × List (Option ℕ)), 0 < traceMassL θ R (missRun dec k st)
  | 0, st => by
      rw [missRun_zero, traceMassL_nil]
      exact zero_lt_one
  | k + 1, (stopped, evs) => by
      rw [missRun_succ]
      by_cases h : stopped = true ∨ dec evs = false
      · rw [if_pos h, traceMassL_cons, traceMass_skip, one_mul]
        exact missRun_traceMassL_pos θ R hs0 dec k (true, evs)
      · rw [if_neg h, traceMassL_cons, traceMass_miss]
        refine ENNReal.mul_pos ?_
          (missRun_traceMassL_pos θ R hs0 dec k (false, evs ++ [none])).ne'
        exact (ENNReal.pow_pos (ENNReal.ofReal_pos.mpr hs0) R).ne'

omit [MeasurableSpace σ] [MeasurableSingletonClass σ] in
/-- **Every arity of the reduced support is charged by every rule**: the zero-hit run
already carries the split weight against the spent exits.  This is the witness that the
exact mixtures of `eq:reach-mix` with a vanishing first coefficient are not reachable:
they give the least presented arity no mass, while every rule presents it. -/
theorem bRuleMass_pos (θ : Offspring J) (R : ℕ) (ρr : BRule σ) (s : σ)
    (hs0 : 0 < θ.skeletonWeight 1) {k₀ : ℕ} (hk₀ : 2 ≤ k₀)
    (hsk : 0 < θ.skeletonWeight k₀) : 0 < bRuleMass θ R ρr s k₀ := by
  set ts₀ : List BTrace :=
    missRun (fun evs ↦ ρr.decide (k₀ - 1) evs s) k₀ (false, []) with hts₀
  have hlen : ts₀.length = k₀ := missRun_length _ k₀ _
  have hatom : BAtom ρr s k₀ ts₀ := by
    refine ⟨?_, missRun_BOkL _ k₀ _, by omega, ?_⟩
    · rw [hlen]
      exact missRun_bConsL _ k₀ _
    · rw [hlen, missRun_bShiftL]
      omega
  have hterm : 0 < ENNReal.ofReal (θ.skeletonWeight ts₀.length)
      * traceMassL θ R ts₀ := by
    rw [hlen]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hsk).ne'
      (missRun_traceMassL_pos θ R hs0 _ k₀ _).ne'
  refine lt_of_lt_of_le hterm ?_
  exact ENNReal.le_tsum (f := fun ts : {ts : List BTrace // BAtom ρr s k₀ ts} ↦
    ENNReal.ofReal (θ.skeletonWeight ts.val.length) * traceMassL θ R ts.val)
    ⟨ts₀, hatom⟩

/-! ### The rule that always stops presents the reduced law -/

/-- The rule that always stops: the blob is one split and the presentation is the
identity. -/
def stopRule (σ : Type*) : BRule σ where
  T := 0
  decide := fun _ _ _ ↦ false
  stop := fun _ _ _ _ ↦ rfl

omit [MeasurableSpace σ] [MeasurableSingletonClass σ] in
lemma stopRule_atom_eq {s : σ} {j : ℕ} {ts : List BTrace}
    (h : BAtom (stopRule σ) s j ts) : ts = List.replicate j BTrace.skip := by
  obtain ⟨hcons, -, hlen2, harity⟩ := h
  have hskip : ∀ (ts' : List BTrace) (st : Bool × List (Option ℕ)),
      bConsL (fun evs ↦ (stopRule σ).decide (ts.length - 1) evs s) ts' st →
      ts' = List.replicate ts'.length BTrace.skip := by
    intro ts'
    induction ts' with
    | nil => intro st _; rfl
    | cons t ts'' ih =>
        intro st hc
        obtain ⟨hct, hcts⟩ := bConsL_cons.mp hc
        have ht : t = BTrace.skip := by
          match t with
          | BTrace.skip => rfl
          | BTrace.miss =>
              obtain ⟨st1, st2⟩ := st
              have := (bCons_miss.mp hct).2
              simp [stopRule] at this
          | BTrace.hit l =>
              obtain ⟨st1, st2⟩ := st
              have := (bCons_hit.mp hct).2.1
              simp [stopRule] at this
        subst ht
        rw [List.length_cons, List.replicate_succ]
        congr 1
        exact ih _ hcts
  have hts := hskip ts (false, []) hcons
  have hshift : bShiftL ts = 0 := by
    rw [hts]
    have : ∀ t ∈ List.replicate ts.length BTrace.skip, bShift t = 0 := by
      intro t ht
      rw [List.eq_of_mem_replicate ht]
      exact bShift_skip
    rw [bShiftL, List.map_congr_left this]
    simp
  have hlen : ts.length = j := by omega
  rw [hts, hlen]

omit [MeasurableSpace σ] [MeasurableSingletonClass σ] in
/-- **The rule that always stops presents the reduced law**: the presented arity mass
is the split weight itself. -/
theorem bRuleMass_stopRule (θ : Offspring J) (R : ℕ) (s : σ) {j : ℕ} (hj : 2 ≤ j) :
    bRuleMass θ R (stopRule σ) s j = ENNReal.ofReal (θ.skeletonWeight j) := by
  have hatom : BAtom (stopRule σ) s j (List.replicate j BTrace.skip) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : ∀ (k : ℕ) (st : Bool × List (Option ℕ)),
          bConsL (fun evs ↦ (stopRule σ).decide
            ((List.replicate j BTrace.skip).length - 1) evs s)
            (List.replicate k BTrace.skip) st := by
        intro k
        induction k with
        | zero => intro st; simp [List.replicate]
        | succ k ih =>
            intro st
            rw [List.replicate_succ, bConsL_cons]
            obtain ⟨st1, st2⟩ := st
            exact ⟨bCons_skip.mpr (Or.inr rfl), by rw [bThread1_skip]; exact ih _⟩
      exact this j (false, [])
    · intro t ht
      rw [List.eq_of_mem_replicate ht]
      exact BOk_skip
    · simpa using hj
    · have : bShiftL (List.replicate j BTrace.skip) = 0 := by
        have hall : ∀ t ∈ List.replicate j BTrace.skip, bShift t = 0 := by
          intro t ht
          rw [List.eq_of_mem_replicate ht]
          exact bShift_skip
        rw [bShiftL, List.map_congr_left hall]
        simp
      simp [this]
  have hmass : ENNReal.ofReal
        (θ.skeletonWeight (List.replicate j BTrace.skip).length)
      * traceMassL θ R (List.replicate j BTrace.skip)
      = ENNReal.ofReal (θ.skeletonWeight j) := by
    have hm : ∀ k : ℕ, traceMassL θ R (List.replicate k BTrace.skip) = 1 := by
      intro k
      induction k with
      | zero => simp [List.replicate, traceMassL_nil]
      | succ k ih =>
          rw [List.replicate_succ, traceMassL_cons, traceMass_skip, one_mul, ih]
    rw [hm j]
    simp
  rw [bRuleMass]
  rw [tsum_eq_single (⟨List.replicate j BTrace.skip, hatom⟩ :
      {ts : List BTrace // BAtom (stopRule σ) s j ts}) ?_]
  · exact hmass
  · intro ts hne
    exact absurd (Subtype.ext (stopRule_atom_eq ts.property)) hne

end ChainClasses
