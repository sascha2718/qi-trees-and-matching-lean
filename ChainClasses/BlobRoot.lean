/-
`sec:general-chain` of `matching_classes_general.tex`: the root step of `thm:blob-law`
at a fixed coin.

A trace of the blob automaton is an atom: the event that the sample realises it
factorises down the revealed splits, one window factor per hit sweeping the revealing
window, one `θ̃₁^R` factor per miss by the memorylessness of the neck, and the handed
subfields are independent conditioned samples.  The root event decomposes over the
fibres of the trace, each fibre agreeing with its trace atom modulo the null events of
`ClusterRoot`, and the masses sum to `bRuleMass`, the presented arity mass of the rule
at the coin.

* `traceEvent`, `traceSlots`, `traceMass`, `traceMassL`: the atom of a trace, its slot
  sets, and its mass.
* `survivalMeasure_traceEvent`, `survivalMeasure_traceSlots_prod`: **the atom
  factorises**, one mass per trace and one conditioned sample per handed subfield.
* `bMatch_box_iff`, `bMatchL_box_iff`: the automaton's reveal conditions with the
  handed constraints are exactly the atom, on surviving subfields.
* `BOk_of_bMatch`, `BOkL_of_bMatchL`: realised traces are valid.
* `BAtom`, `bRuleMass`: the atoms of a presented arity and their total mass.
* `blob_root_fixed`: **the root step at a fixed coin**: the presented neck and arity
  carry `θ̃₁^r` against the rule mass, and the presented children are independent
  conditioned samples.
-/
import ChainClasses.BlobField

namespace ChainClasses

open MeasureTheory
open scoped ENNReal
open BranchingProcess (Survives skeletonDegree Offspring sampleMeasure survivalMeasure
  bushAt)

variable {J N : ℕ} {σ : Type*}

/-! ### The atom of a trace -/

mutual

/-- **The atom of a trace** at one exit's subfield: a skip constrains the subfield
itself, a miss reveals `R` neck vertices and constrains the residual, and a hit sweeps
the revealing window with one slot per child of the absorbed split. -/
def traceEvent (R : ℕ) : BTrace → (ℕ → Set (GWord N → ℕ)) → Set (GWord N → ℕ)
  | .skip, Es => Es 0
  | .miss, Es => missEvent R (Es 0)
  | .hit l, Es => hitInner R l.length (traceSlots R l Es)

/-- The slot sets of a queue of traces: the `i`-th child carries the `i`-th trace, its
handed constraints read off the chunk the earlier counts leave. -/
def traceSlots (R : ℕ) : List BTrace → (ℕ → Set (GWord N → ℕ)) → ℕ → Set (GWord N → ℕ)
  | [], _ => fun _ ↦ Set.univ
  | t :: ts, Es => fun i ↦
      if i = 0 then traceEvent R t Es
      else traceSlots R ts (fun m ↦ Es (bCount t + m)) (i - 1)

end

lemma traceEvent_skip (R : ℕ) (Es : ℕ → Set (GWord N → ℕ)) :
    traceEvent R .skip Es = Es 0 := by
  rw [traceEvent.eq_def]

lemma traceEvent_miss (R : ℕ) (Es : ℕ → Set (GWord N → ℕ)) :
    traceEvent R .miss Es = missEvent R (Es 0) := by
  rw [traceEvent.eq_def]

lemma traceEvent_hit (R : ℕ) (l : List BTrace) (Es : ℕ → Set (GWord N → ℕ)) :
    traceEvent R (.hit l) Es = hitInner R l.length (traceSlots R l Es) := by
  rw [traceEvent.eq_def]

lemma traceSlots_nil (R : ℕ) (Es : ℕ → Set (GWord N → ℕ)) (i : ℕ) :
    traceSlots R ([] : List BTrace) Es i = Set.univ := by
  rw [traceSlots.eq_def]

lemma traceSlots_cons_zero (R : ℕ) (t : BTrace) (ts : List BTrace)
    (Es : ℕ → Set (GWord N → ℕ)) : traceSlots R (t :: ts) Es 0 = traceEvent R t Es := by
  rw [traceSlots.eq_def]
  simp

lemma traceSlots_cons_succ (R : ℕ) (t : BTrace) (ts : List BTrace)
    (Es : ℕ → Set (GWord N → ℕ)) (i : ℕ) :
    traceSlots R (t :: ts) Es (i + 1)
      = traceSlots R ts (fun m ↦ Es (bCount t + m)) i := by
  rw [traceSlots.eq_def]
  simp

mutual

/-- The atoms are measurable. -/
lemma measurableSet_traceEvent (R : ℕ) : ∀ (t : BTrace) (Es : ℕ → Set (GWord N → ℕ)),
    (∀ m, MeasurableSet (Es m)) → MeasurableSet (traceEvent R t Es)
  | .skip, Es, hEs => by
      rw [traceEvent_skip]
      exact hEs 0
  | .miss, Es, hEs => by
      rw [traceEvent_miss]
      exact measurableSet_missEvent R (hEs 0)
  | .hit l, Es, hEs => by
      rw [traceEvent_hit, hitInner]
      exact MeasurableSet.biUnion (Set.to_countable _) fun d₁ _ ↦
        measurableSet_gArityDepthEvent (measurableSet_traceSlots R l Es hEs)

lemma measurableSet_traceSlots (R : ℕ) :
    ∀ (ts : List BTrace) (Es : ℕ → Set (GWord N → ℕ)),
      (∀ m, MeasurableSet (Es m)) → ∀ i, MeasurableSet (traceSlots R ts Es i)
  | [], Es, _, i => by
      rw [traceSlots_nil]
      exact MeasurableSet.univ
  | t :: ts, Es, hEs, 0 => by
      rw [traceSlots_cons_zero]
      exact measurableSet_traceEvent R t Es hEs
  | t :: ts, Es, hEs, i + 1 => by
      rw [traceSlots_cons_succ]
      exact measurableSet_traceSlots R ts _ (fun m ↦ hEs _) i

end

/-! ### The mass of a trace -/

mutual

/-- **The mass of a trace**: one geometric window against the split weight per hit, and
`θ̃₁^R` per miss. -/
noncomputable def traceMass (θ : Offspring J) (R : ℕ) : BTrace → ℝ≥0∞
  | .skip => 1
  | .miss => ENNReal.ofReal (θ.skeletonWeight 1) ^ R
  | .hit l =>
      (∑ d ∈ Finset.range R, ENNReal.ofReal (θ.skeletonWeight 1) ^ d)
        * ENNReal.ofReal (θ.skeletonWeight l.length) * traceMassL θ R l

/-- The mass of a queue of traces. -/
noncomputable def traceMassL (θ : Offspring J) (R : ℕ) : List BTrace → ℝ≥0∞
  | [] => 1
  | t :: ts => traceMass θ R t * traceMassL θ R ts

end

lemma traceMass_skip (θ : Offspring J) (R : ℕ) : traceMass θ R .skip = 1 := by
  rw [traceMass.eq_def]

lemma traceMass_miss (θ : Offspring J) (R : ℕ) :
    traceMass θ R .miss = ENNReal.ofReal (θ.skeletonWeight 1) ^ R := by
  rw [traceMass.eq_def]

lemma traceMass_hit (θ : Offspring J) (R : ℕ) (l : List BTrace) :
    traceMass θ R (.hit l)
      = (∑ d ∈ Finset.range R, ENNReal.ofReal (θ.skeletonWeight 1) ^ d)
          * ENNReal.ofReal (θ.skeletonWeight l.length) * traceMassL θ R l := by
  rw [traceMass.eq_def]

lemma traceMassL_nil (θ : Offspring J) (R : ℕ) : traceMassL θ R [] = 1 := by
  rw [traceMassL.eq_def]

lemma traceMassL_cons (θ : Offspring J) (R : ℕ) (t : BTrace) (ts : List BTrace) :
    traceMassL θ R (t :: ts) = traceMass θ R t * traceMassL θ R ts := by
  rw [traceMassL.eq_def]

/-! ### The atom factorises -/

mutual

/-- **The atom of a trace factorises**: its mass against one conditioned sample per
handed subfield. -/
theorem survivalMeasure_traceEvent (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (R : ℕ) :
    ∀ (t : BTrace), BOk t → ∀ (Es : ℕ → Set (GWord N → ℕ)),
      (∀ m, MeasurableSet (Es m)) →
      survivalMeasure (N := N) θ (traceEvent R t Es)
        = traceMass θ R t
            * ∏ m ∈ Finset.range (bCount t), survivalMeasure (N := N) θ (Es m)
  | .skip, _, Es, hEs => by
      rw [traceEvent_skip, traceMass_skip, bCount_skip, Finset.prod_range_one, one_mul]
  | .miss, _, Es, hEs => by
      rw [traceEvent_miss, traceMass_miss, bCount_miss, Finset.prod_range_one,
        survivalMeasure_missEvent θ hJN hq R (hEs 0)]
  | .hit l, hok, Es, hEs => by
      obtain ⟨hlen, hall⟩ := BOk_hit.mp hok
      rw [traceEvent_hit, traceMass_hit, bCount_hit,
        survivalMeasure_hitInner θ hJN hq hlen (measurableSet_traceSlots R l Es hEs),
        survivalMeasure_traceSlots_prod θ hJN hq R l hall Es hEs]
      ring

/-- The slots of a queue of traces factorise, the chunks of the handed constraints
regrouped. -/
theorem survivalMeasure_traceSlots_prod (θ : Offspring J) (hJN : J ≤ N)
    (hq : θ.extinction < 1) (R : ℕ) :
    ∀ (ts : List BTrace), BOkL ts → ∀ (Es : ℕ → Set (GWord N → ℕ)),
      (∀ m, MeasurableSet (Es m)) →
      (∏ i ∈ Finset.range ts.length,
          survivalMeasure (N := N) θ (traceSlots R ts Es i))
        = traceMassL θ R ts
            * ∏ m ∈ Finset.range (bCountL ts), survivalMeasure (N := N) θ (Es m)
  | [], _, Es, hEs => by
      rw [traceMassL_nil]
      simp
  | t :: ts, hok, Es, hEs => by
      have hokt : BOk t := hok t (by simp)
      have hokts : BOkL ts := fun t' ht' ↦ hok t' (by simp [ht'])
      rw [List.length_cons, Finset.prod_range_succ']
      have h0 : traceSlots R (t :: ts) Es 0 = traceEvent R t Es :=
        traceSlots_cons_zero R t ts Es
      have hsucc : ∀ i ∈ Finset.range ts.length,
          survivalMeasure (N := N) θ (traceSlots R (t :: ts) Es (i + 1))
            = survivalMeasure (N := N) θ
                (traceSlots R ts (fun m ↦ Es (bCount t + m)) i) := by
        intro i _
        rw [traceSlots_cons_succ]
      rw [h0, Finset.prod_congr rfl hsucc,
        survivalMeasure_traceEvent θ hJN hq R t hokt Es hEs,
        survivalMeasure_traceSlots_prod θ hJN hq R ts hokts _ (fun m ↦ hEs _),
        traceMassL_cons, bCountL_cons, Finset.prod_range_add]
      ring

end

/-! ### The reveal conditions are the atom -/

/-- The children of a genuine split survive along their indices. -/
lemma survives_gSplitBush_of_lt {d : GWord N → ℕ} {k : ℕ} (h : k < gArity d) :
    Survives (gSplitBush d k) :=
  BranchingProcess.survives_bushAt h

mutual

/-- A realised trace is valid: every absorbed split is genuine. -/
lemma BOk_of_bMatch (R : ℕ) : ∀ (t : BTrace) (d : GWord N → ℕ), bMatch R t d → BOk t
  | .skip, _, _ => BOk_skip
  | .miss, _, _ => BOk_miss
  | .hit l, d, h => by
      obtain ⟨hhit, hlen, hml⟩ := bMatch_hit.mp h
      refine BOk_hit.mpr ⟨?_, BOkL_of_bMatchL R l (bChildren d) hml⟩
      rw [← hlen]
      exact two_le_gArity_of_bHit hhit
  termination_by t _ _ => sizeOf t
  decreasing_by
    simp only [BTrace.hit.sizeOf_spec]
    omega

lemma BOkL_of_bMatchL (R : ℕ) :
    ∀ (ts : List BTrace) (ds : List (GWord N → ℕ)), bMatchL R ts ds → BOkL ts
  | [], _, _ => fun t ht ↦ absurd ht (List.not_mem_nil)
  | t :: ts, ds, h => by
      obtain ⟨hh, hts⟩ := bMatchL_cons.mp h
      have h1 : BOk t := BOk_of_bMatch R t _ hh
      have h2 : BOkL ts := BOkL_of_bMatchL R ts ds.tail hts
      intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact h1
      · exact h2 t' ht'
  termination_by ts _ _ => sizeOf ts
  decreasing_by
    all_goals
      simp only [List.cons.sizeOf_spec]
      omega

end

/-- The head of a dropped mapped list, read at the index. -/
lemma headD_drop_map {α β : Type*} (f : α → β) (b : β) :
    ∀ (l : List α) (k : ℕ) (hk : k < l.length),
      ((l.map f).drop k).headD b = f (l[k]'hk)
  | x :: xs, 0, _ => by simp
  | x :: xs, k + 1, hk => by
      simp only [List.map_cons, List.drop_succ_cons, List.getElem_cons_succ]
      exact headD_drop_map f b xs k (by simpa using hk)

/-- The children past an index, as the automaton's queue hands them. -/
lemma bChildren_drop_headD {d : GWord N → ℕ} {k : ℕ} (h : k < gArity d) :
    ((bChildren d).drop k).headD bJunk = gSplitBush d k := by
  rw [bChildren, headD_drop_map (gSplitBush d) bJunk (List.range (gArity d)) k
    (by simpa using h)]
  congr 1
  exact List.getElem_range _

lemma bChildren_drop_tail (d : GWord N → ℕ) (k : ℕ) :
    ((bChildren d).drop k).tail = (bChildren d).drop (k + 1) := by
  rw [List.tail_drop]

mutual

/-- **The reveal conditions with the handed constraints are the atom**, at one
surviving exit. -/
theorem bMatch_box_iff (R : ℕ) : ∀ (t : BTrace) (d : GWord N → ℕ),
    BOk t → Survives d →
    ∀ (Es : ℕ → Set (GWord N → ℕ)),
    ((bMatch R t d ∧ ∀ m, m < bCount t → bFollow R d (bPath t m) ∈ Es m)
      ↔ d ∈ traceEvent R t Es)
  | .skip, d, _, _, Es => by
      rw [traceEvent_skip]
      constructor
      · rintro ⟨-, hbox⟩
        have := hbox 0 (by rw [bCount_skip]; omega)
        rwa [bPath_skip, bFollow] at this
      · intro hd
        refine ⟨bMatch_skip, fun m hm ↦ ?_⟩
        rw [bCount_skip] at hm
        have hm0 : m = 0 := by omega
        subst hm0
        rwa [bPath_skip, bFollow]
  | .miss, d, _, hsurv, Es => by
      rw [traceEvent_miss, missEvent]
      constructor
      · rintro ⟨hmat, hbox⟩
        have hnb := bMatch_miss.mp hmat
        have hbox0 := hbox 0 (by rw [bCount_miss]; omega)
        rw [bPath_miss, bFollow] at hbox0
        simp only at hbox0
        refine ⟨?_, hbox0⟩
        intro n hn
        exact deg_eq_one_of_no_split hsurv (fun m hm h2 ↦ hnb ⟨m, hm, h2⟩) n hn
      · rintro ⟨hneck, hres⟩
        refine ⟨bMatch_miss.mpr ?_, fun m hm ↦ ?_⟩
        · rintro ⟨n, hnR, h2⟩
          have := hneck n hnR
          omega
        · rw [bCount_miss] at hm
          have hm0 : m = 0 := by omega
          subst hm0
          rw [bPath_miss, bFollow]
          simpa using hres
  | .hit l, d, hok, hsurv, Es => by
      obtain ⟨hlen2, hall⟩ := BOk_hit.mp hok
      rw [traceEvent_hit, hitInner]
      constructor
      · rintro ⟨hmat, hbox⟩
        obtain ⟨hhit, hlen, hml⟩ := bMatch_hit.mp hmat
        simp only [Set.mem_iUnion, Finset.mem_range, exists_prop, gArityDepthEvent,
          Set.mem_inter_iff, Set.mem_setOf_eq]
        refine ⟨gSplitDepth d, gSplitDepth_lt_of_bHit hhit, ⟨rfl, hlen⟩, ?_⟩
        have hbox' : ∀ m, m < bCountL l → bFollow R d (bPathL 0 l m) ∈ Es m := by
          intro m hm
          have := hbox m (by rwa [bCount_hit])
          rwa [bPath_hit] at this
        have hconv := (bMatchL_box_iff R l d 0 hall (by omega : 0 + l.length ≤ gArity d)
          Es).mp ⟨by simpa using hml, hbox'⟩
        intro i hi
        have := hconv i hi
        simpa using this
      · intro hmem
        simp only [Set.mem_iUnion, Finset.mem_range, exists_prop, gArityDepthEvent,
          Set.mem_inter_iff, Set.mem_setOf_eq] at hmem
        obtain ⟨d₁, hd₁R, ⟨hdep, hlen⟩, hslots⟩ := hmem
        have hhit : bHit R d := bHit_of_depth_lt (by omega) (by omega)
        have hconv := (bMatchL_box_iff R l d 0 hall (by omega : 0 + l.length ≤ gArity d)
          Es).mpr (by
            intro i hi
            have := hslots i hi
            simpa using this)
        refine ⟨bMatch_hit.mpr ⟨hhit, hlen, by simpa using hconv.1⟩, fun m hm ↦ ?_⟩
        rw [bCount_hit] at hm
        rw [bPath_hit]
        exact hconv.2 m hm

/-- The reveal conditions along a queue of exits, from an index on. -/
theorem bMatchL_box_iff (R : ℕ) : ∀ (ts : List BTrace) (d : GWord N → ℕ) (k : ℕ),
    BOkL ts → k + ts.length ≤ gArity d →
    ∀ (Es : ℕ → Set (GWord N → ℕ)),
    ((bMatchL R ts ((bChildren d).drop k)
        ∧ ∀ m, m < bCountL ts → bFollow R d (bPathL k ts m) ∈ Es m)
      ↔ ∀ i, i < ts.length → gSplitBush d (k + i) ∈ traceSlots R ts Es i)
  | [], d, k, _, _, Es => by
      constructor
      · rintro ⟨-, -⟩ i hi
        simp at hi
      · intro h
        refine ⟨bMatchL_nil, fun m hm ↦ ?_⟩
        rw [bCountL_nil] at hm
        omega
  | t :: ts, d, k, hok, hle, Es => by
      have hokt : BOk t := hok t (by simp)
      have hokts : BOkL ts := fun t' ht' ↦ hok t' (by simp [ht'])
      have hk : k < gArity d := by
        simp only [List.length_cons] at hle
        omega
      have hsurvk : Survives (gSplitBush d k) := survives_gSplitBush_of_lt hk
      have hsingle := bMatch_box_iff R t (gSplitBush d k) hokt hsurvk Es
      have hlist := bMatchL_box_iff R ts d (k + 1) hokts
        (by
          simp only [List.length_cons] at hle
          omega) (fun m ↦ Es (bCount t + m))
      constructor
      · rintro ⟨hml, hbox⟩
        obtain ⟨hh, hts⟩ := bMatchL_cons.mp hml
        rw [bChildren_drop_headD hk] at hh
        rw [bChildren_drop_tail] at hts
        intro i hi
        match i with
        | 0 =>
            rw [traceSlots_cons_zero]
            refine hsingle.mp ⟨hh, fun m hm ↦ ?_⟩
            have hbm := hbox m (by rw [bCountL_cons]; omega)
            rw [bPathL_cons, if_pos hm, bFollow_cons] at hbm
            exact hbm
        | i + 1 =>
            rw [traceSlots_cons_succ]
            have := hlist.mp ⟨hts, ?_⟩
            · have h2 := this i (by simpa using hi)
              have hidx : k + (i + 1) = k + 1 + i := by omega
              rwa [hidx]
            · intro m hm
              have hbm := hbox (bCount t + m) (by rw [bCountL_cons]; omega)
              rw [bPathL_cons, if_neg (by omega)] at hbm
              have hidx : bCount t + m - bCount t = m := by omega
              rwa [hidx] at hbm
      · intro hslots
        have h0 := hslots 0 (by simp)
        rw [traceSlots_cons_zero] at h0
        have hsing := hsingle.mpr (by simpa using h0)
        have hrest := hlist.mpr (by
          intro i hi
          have := hslots (i + 1) (by simpa using Nat.succ_lt_succ hi)
          rw [traceSlots_cons_succ] at this
          have hidx : k + 1 + i = k + (i + 1) := by omega
          rwa [hidx])
        refine ⟨bMatchL_cons.mpr ⟨?_, ?_⟩, ?_⟩
        · rw [bChildren_drop_headD hk]
          exact hsing.1
        · rw [bChildren_drop_tail]
          exact hrest.1
        · intro m hm
          rw [bPathL_cons]
          by_cases hmt : m < bCount t
          · rw [if_pos hmt, bFollow_cons]
            exact hsing.2 m hmt
          · rw [if_neg hmt]
            have := hrest.2 (m - bCount t) (by
              rw [bCountL_cons] at hm
              omega)
            have hidx : bCount t + (m - bCount t) = m := by omega
            rwa [hidx] at this

end


/-! ### The atoms of a presented arity and the root law -/

/-- **The atoms of a presented arity**: the valid, rule-consistent traces whose root
split and accumulated shift present the arity. -/
def BAtom (ρr : BRule σ) (s : σ) (j : ℕ) (ts : List BTrace) : Prop :=
  bConsL (fun evs ↦ ρr.decide (ts.length - 1) evs s) ts (false, [])
    ∧ BOkL ts ∧ 2 ≤ ts.length ∧ ts.length + bShiftL ts = j

/-- **The presented arity mass of the rule at a coin**: the split weight of the root
against the trace mass, summed over the atoms. -/
noncomputable def bRuleMass (θ : Offspring J) (R : ℕ) (ρr : BRule σ) (s : σ) (j : ℕ) :
    ℝ≥0∞ :=
  ∑' ts : {ts : List BTrace // BAtom ρr s j ts},
    ENNReal.ofReal (θ.skeletonWeight ts.val.length) * traceMassL θ R ts.val

/-- The fibre of a trace inside the root event. -/
def bFib (R : ℕ) (ρr : BRule σ) (b : List ℕ → σ) (r j : ℕ) (ts : List BTrace)
    (E : ℕ → Set (GWord N → ℕ)) : Set (GWord N → ℕ) :=
  ({c : GWord N → ℕ | bTraceF R ρr c (b []) = ts}
      ∩ {c : GWord N → ℕ | gSplitDepth c = r})
    ∩ {c : GWord N → ℕ | ∀ m, m < j → (bSubC R ρr (c, b) m).1 ∈ E m}

lemma measurableSet_bFib (R : ℕ) (ρr : BRule σ) (b : List ℕ → σ) (r j : ℕ)
    (ts : List BTrace) {E : ℕ → Set (GWord N → ℕ)} (hE : ∀ m, MeasurableSet (E m)) :
    MeasurableSet (bFib R ρr b r j ts E) := by
  refine MeasurableSet.inter (MeasurableSet.inter ?_ (fibreMeasurableG_gSplitDepth r)) ?_
  · exact fibreMeasurableG_bTraceF R ρr (b []) ts
  · have he : {c : GWord N → ℕ | ∀ m, m < j → (bSubC R ρr (c, b) m).1 ∈ E m}
        = ⋂ m ∈ Finset.range j,
            (fun c : GWord N → ℕ ↦ (bSubC R ρr (c, b) m).1) ⁻¹' (E m) := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
    rw [he]
    exact MeasurableSet.biInter (Set.to_countable _) fun m _ ↦
      measurable_bSubC_fst R ρr b m (hE m)

/-- The bridge specialised to the root: the trace of the blob against its data. -/
lemma bTraceF_eq_iff (R : ℕ) (ρr : BRule σ) (s : σ) (c : GWord N → ℕ)
    (ts : List BTrace) :
    bTraceF R ρr c s = ts
      ↔ ts.length = gArity c
          ∧ bConsL (fun evs ↦ ρr.decide (gArity c - 1) evs s) ts (false, [])
          ∧ bMatchL R ts (bChildren c) := by
  have hT : ∀ evs : List (Option ℕ), ρr.T ≤ evs.length →
      (fun evs ↦ ρr.decide (gArity c - 1) evs s) evs = false := fun evs h ↦
    ρr.stop _ evs s h
  have h := bExplore_eq_iff R hT (ρr.T + 1) (bChildren c) false [] ts (by simp)
  rw [bTraceF, h, bChildren_length]

/-- **The fibre of an atom is its trace atom**, on survival with a genuine root
split. -/
lemma bFib_inter_eq (R : ℕ) (ρr : BRule σ) (b : List ℕ → σ) {r j : ℕ}
    {ts : List BTrace} (hatom : BAtom ρr (b []) j ts)
    (E : ℕ → Set (GWord N → ℕ)) :
    bFib R ρr b r j ts E
        ∩ ({c : GWord N → ℕ | Survives c} ∩ {c : GWord N → ℕ | gArity c = 1}ᶜ)
      = gArityDepthEvent (N := N) ts.length r (traceSlots R ts E)
        ∩ ({c : GWord N → ℕ | Survives c} ∩ {c : GWord N → ℕ | gArity c = 1}ᶜ) := by
  obtain ⟨hcons, hok, hlen2, harity⟩ := hatom
  have hcount : bCountL ts = j := by
    rw [bCountL_eq_of_ok ts hok, harity]
  ext c
  simp only [bFib, gArityDepthEvent, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_compl_iff]
  constructor
  · rintro ⟨⟨⟨htr, hdep⟩, hbox⟩, hsurv, hne1⟩
    obtain ⟨hlen, hcons', hmatch⟩ := (bTraceF_eq_iff R ρr (b []) c ts).mp htr
    have hconv := (bMatchL_box_iff R ts c 0 hok (by omega) E).mp
      ⟨by simpa using hmatch, ?_⟩
    · refine ⟨⟨⟨hdep, hlen.symm⟩, fun m hm ↦ ?_⟩, hsurv, hne1⟩
      have := hconv m (by omega)
      simpa using this
    · intro m hm
      have hb := hbox m (by omega)
      rw [bSubC, htr] at hb
      exact hb
  · rintro ⟨⟨⟨hdep, har⟩, hslots⟩, hsurv, hne1⟩
    have hconv := (bMatchL_box_iff R ts c 0 hok (by omega) E).mpr (by
      intro i hi
      have := hslots i (by omega)
      simpa using this)
    have htr : bTraceF R ρr c (b []) = ts := by
      refine (bTraceF_eq_iff R ρr (b []) c ts).mpr ⟨har.symm, ?_, by simpa using hconv.1⟩
      have hfun : (fun evs ↦ ρr.decide (gArity c - 1) evs (b []))
          = fun evs ↦ ρr.decide (ts.length - 1) evs (b []) := by
        rw [har]
      rw [hfun]
      exact hcons
    refine ⟨⟨⟨htr, hdep⟩, fun m hm ↦ ?_⟩, hsurv, hne1⟩
    rw [bSubC, htr]
    exact hconv.2 m (by omega)

/-- **The root event decomposes over the atoms**, on survival with a genuine root
split. -/
lemma blob_root_cover (R : ℕ) (ρr : BRule σ) (b : List ℕ → σ) (r j : ℕ)
    (E : ℕ → Set (GWord N → ℕ)) :
    (({c : GWord N → ℕ | gSplitDepth c = r}
        ∩ {c : GWord N → ℕ | bArityC R ρr (c, b) = j})
      ∩ {c : GWord N → ℕ | ∀ m, m < j → (bSubC R ρr (c, b) m).1 ∈ E m})
        ∩ ({c : GWord N → ℕ | Survives c} ∩ {c : GWord N → ℕ | gArity c = 1}ᶜ)
      = (⋃ ts : {ts : List BTrace // BAtom ρr (b []) j ts},
          bFib R ρr b r j ts.val E)
        ∩ ({c : GWord N → ℕ | Survives c} ∩ {c : GWord N → ℕ | gArity c = 1}ᶜ) := by
  ext c
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion,
    bFib]
  constructor
  · rintro ⟨⟨⟨hdep, har⟩, hbox⟩, hsurv, hne1⟩
    set ts := bTraceF R ρr c (b []) with hts
    obtain ⟨hlen, hcons, hmatch⟩ := (bTraceF_eq_iff R ρr (b []) c ts).mp rfl
    have hga : 1 ≤ gArity c := one_le_gArity_of_survives hsurv
    have hga2 : 2 ≤ gArity c := by
      rcases Nat.lt_or_ge (gArity c) 2 with h | h
      · exact absurd (by omega : gArity c = 1) hne1
      · exact h
    have hatom : BAtom ρr (b []) j ts := by
      refine ⟨?_, BOkL_of_bMatchL R ts (bChildren c) hmatch, by omega, ?_⟩
      · have hfun : (fun evs ↦ ρr.decide (ts.length - 1) evs (b []))
            = fun evs ↦ ρr.decide (gArity c - 1) evs (b []) := by
          rw [hlen]
        rw [hfun]
        exact hcons
      · rw [bArityC] at har
        rw [hlen]
        rw [← hts] at har
        omega
    exact ⟨⟨⟨ts, hatom⟩, ⟨⟨rfl, hdep⟩, hbox⟩⟩, hsurv, hne1⟩
  · rintro ⟨⟨⟨ts, hatom⟩, ⟨⟨htr, hdep⟩, hbox⟩⟩, hsurv, hne1⟩
    have hlen : ts.length = gArity c :=
      ((bTraceF_eq_iff R ρr (b []) c ts).mp htr).1
    refine ⟨⟨⟨hdep, ?_⟩, hbox⟩, hsurv, hne1⟩
    rw [bArityC, htr]
    show gArity c + bShiftL ts = j
    have := hatom.2.2.2
    omega

/-- **The root step at a fixed coin**: the presented neck and arity carry `θ̃₁^r`
against the rule mass at the coin, and the presented children are independent
conditioned samples. -/
theorem blob_root_fixed (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) (R : ℕ) (ρr : BRule σ) (b : List ℕ → σ) {r j : ℕ}
    {E : ℕ → Set (GWord N → ℕ)} (hE : ∀ m, MeasurableSet (E m)) :
    survivalMeasure (N := N) θ
        ((({c : GWord N → ℕ | gSplitDepth c = r}
            ∩ {c : GWord N → ℕ | bArityC R ρr (c, b) = j})
          ∩ {c : GWord N → ℕ | ∀ m, m < j → (bSubC R ρr (c, b) m).1 ∈ E m}))
      = ENNReal.ofReal (θ.skeletonWeight 1) ^ r
          * (bRuleMass θ R ρr (b []) j
            * ∏ m ∈ Finset.range j, survivalMeasure (N := N) θ (E m)) := by
  have hnull : survivalMeasure (N := N) θ
      ({c : GWord N → ℕ | Survives c} ∩ {c : GWord N → ℕ | gArity c = 1}ᶜ)ᶜ = 0 := by
    rw [Set.compl_inter, compl_compl]
    exact measure_union_null (survivalMeasure_compl_survives θ hJN hq)
      (survivalMeasure_gArity_eq_one θ hJN hq hs1)
  rw [measure_eq_of_inter_ae hnull (blob_root_cover R ρr b r j E)]
  have hdisj : Pairwise (Function.onFun Disjoint
      fun ts : {ts : List BTrace // BAtom ρr (b []) j ts} ↦
        bFib (N := N) R ρr b r j ts.val E) := by
    intro ts ts' hne
    refine Set.disjoint_left.mpr fun c hc hc' ↦ hne ?_
    refine Subtype.ext ?_
    rw [← hc.1.1, ← hc'.1.1]
  have hmeas : ∀ ts : {ts : List BTrace // BAtom ρr (b []) j ts},
      MeasurableSet (bFib (N := N) R ρr b r j ts.val E) := fun ts ↦
    measurableSet_bFib R ρr b r j ts.val hE
  rw [measure_iUnion hdisj hmeas]
  have hterm : ∀ ts : {ts : List BTrace // BAtom ρr (b []) j ts},
      survivalMeasure (N := N) θ (bFib R ρr b r j ts.val E)
        = ENNReal.ofReal (θ.skeletonWeight 1) ^ r
            * (ENNReal.ofReal (θ.skeletonWeight ts.val.length)
              * traceMassL θ R ts.val
              * ∏ m ∈ Finset.range j, survivalMeasure (N := N) θ (E m)) := by
    intro ts
    rw [measure_eq_of_inter_ae hnull (bFib_inter_eq R ρr b ts.property E),
      survivalMeasure_gArityDepthEvent θ hJN hq ts.property.2.2.1
        (measurableSet_traceSlots R ts.val E hE) r,
      survivalMeasure_traceSlots_prod θ hJN hq R ts.val ts.property.2.1 E hE]
    have hcount : bCountL ts.val = j := by
      rw [bCountL_eq_of_ok ts.val ts.property.2.1, ts.property.2.2.2]
    rw [hcount]
    ring
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, bRuleMass, ← ENNReal.tsum_mul_right]

end ChainClasses
