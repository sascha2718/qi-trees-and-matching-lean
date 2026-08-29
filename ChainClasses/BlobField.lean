/-
`sec:general-chain` of `matching_classes_general.tex`: the deterministic layer of the
blob presentation of `def:blob`, read off the skeleton recursion of
`GeneralDecomposition`.

The rule of `def:blob` is carried as a decision function of the revealed transcript: at
each step it either stops or descends the first unspent exit, the exits held in a
depth-first queue, so the choices of the rule are exactly the adapted choices of the
prose and the exit named is canonical.  A descent tests the absorption condition of
`ClusterField` at the exit's subfield: a hit absorbs the split below it, whose children
join the head of the queue, and a miss absorbs the revealed neck and spends the exit.
The transcript records one event per descent, a hit with its shift or a miss, and the
rule consumes the transcript together with the arity of the root's split.  A fuel
bounds the recursion; the rule's stopping bound `T` makes the fuel `T + 1` exact, so
the exhaustion branch is junk that the law never sees.

The whole run of one blob is recorded as a list of traces, one per exit of the root's
split: `skip` for an exit left unspent, `miss` for a spent exit, and `hit` with the
traces of the absorbed split's children.  The run is recovered from the trace by the
threading `bThread`, which is what aligns the automaton with the trace atoms of
`BlobRoot`.

* `bHit` with its readings: the absorption test at an exit's subfield.
* `BTrace` with `bShift`, `bCount`, `bShiftL`, `bCountL` and `bCount_eq_of_ok`: the
  trace of one exit, its accumulated shift and its handed count, equal to one plus the
  shift on valid traces.
* `bExplore`, `bExplore_fst_length`, `bExplore_snd_eq`, `bThread`: **`def:blob`**, the
  depth-first automaton, its per-exit output, and the state recovered from the trace.
* `bCons`, `bConsL`, `bMatch`, `bMatchL`, `bExplore_eq_iff`: **the run as an atom**:
  the automaton produces a trace exactly when the rule's decisions along its flattening
  agree with the coin and the sample realises its reveals.
* `bTrace`, `bArity`, `bHand`, `bHandRoot`, `bSubC`, `bAtC`, `bNeckAtC`, `bArityAtC`:
  the presented data: the trace of the root, the presented arity, the handed subfields
  in queue order, and the presented fields along a presented address.
* `bNeckAtC_congr`, `bArityAtC_congr`: the rule reads only the coins at the prefixes
  of the address.
* `fibreMeasurableG_bTraceF`, `measurable_bAtC_fst`, `measurableSet_bNeckAtC_eq`,
  `measurableSet_bArityAtC_eq`: at a fixed coin field the presented fields are
  measurable in the sample.
-/
import ChainClasses.ClusterRoot

namespace ChainClasses

open MeasureTheory
open BranchingProcess (Survives skeletonDegree Offspring sampleMeasure survivalMeasure
  bushAt)

variable {N : ℕ}

/-! ### The absorption test at an exit -/

/-- **The absorption test of `def:blob`** at an exit's subfield: a genuine split within
the revealing depth.  This is `m(v) ≤ R`, reading `m(v) = ∞` when the descent never
splits; `clHitCond R c` is `bHit R` at the first exit of the root's split. -/
def bHit (R : ℕ) (d : GWord N → ℕ) : Prop :=
  ∃ n, n < R ∧ 2 ≤ skeletonDegree (neckIter d n)

lemma gSplitDepth_lt_of_bHit {R : ℕ} {d : GWord N → ℕ} (h : bHit R d) :
    gSplitDepth d < R := by
  obtain ⟨n, hnR, hn⟩ := h
  exact lt_of_le_of_lt (Nat.sInf_le hn) hnR

lemma two_le_gArity_of_bHit {R : ℕ} {d : GWord N → ℕ} (h : bHit R d) :
    2 ≤ gArity d := by
  obtain ⟨n, hnR, hn⟩ := h
  have hne : {m | 2 ≤ skeletonDegree (neckIter d m)}.Nonempty := ⟨n, hn⟩
  exact Nat.sInf_mem hne

lemma bHit_of_depth_lt {R : ℕ} {d : GWord N → ℕ} (hd : gSplitDepth d < R)
    (ha : 2 ≤ gArity d) : bHit R d := by
  have hne := splitSet_nonempty_of_arity ha
  exact ⟨gSplitDepth d, hd, Nat.sInf_mem hne⟩

noncomputable instance (R : ℕ) (d : GWord N → ℕ) : Decidable (bHit R d) :=
  decidable_of_iff
    (∃ n ∈ Finset.range R, 2 ≤ skeletonDegree (neckIter d n)) (by simp [bHit])

lemma measurableSet_bHit (R : ℕ) : MeasurableSet {d : GWord N → ℕ | bHit R d} := by
  have he : {d : GWord N → ℕ | bHit R d}
      = ⋃ n ∈ Finset.range R,
          (fun d : GWord N → ℕ ↦ neckIter d n) ⁻¹'
            {e : GWord N → ℕ | 2 ≤ skeletonDegree e} := by
    ext d
    simp [bHit]
  rw [he]
  exact MeasurableSet.biUnion (Set.to_countable _) fun n _ ↦
    measurable_neckIter n (fibreMeasurableG_skeletonDegree.preimage {m : ℕ | 2 ≤ m})

/-! ### Traces -/

/-- **The trace of one exit of a blob**: left unspent, spent by a miss, or a hit
carrying the traces of the absorbed split's children. -/
inductive BTrace where
  | skip : BTrace
  | miss : BTrace
  | hit : List BTrace → BTrace

namespace BTrace

/-- A prefix-free code of a trace as a rose tree, giving countability. -/
def code : BTrace → RTree
  | .skip => .node []
  | .miss => .node [.node []]
  | .hit l => .node (.node [.node []] :: l.map code)

@[simp] lemma code_skip : code .skip = .node [] := by rw [code]

@[simp] lemma code_miss : code .miss = .node [.node []] := by rw [code]

@[simp] lemma code_hit (l : List BTrace) :
    code (.hit l) = .node (.node [.node []] :: l.map code) := by rw [code]

mutual

lemma code_inj : ∀ t t' : BTrace, code t = code t' → t = t'
  | .skip, .skip, _ => rfl
  | .skip, .miss, h => by simp at h
  | .skip, .hit l', h => by simp at h
  | .miss, .skip, h => by simp at h
  | .miss, .miss, _ => rfl
  | .miss, .hit l', h => by
      simp only [code_miss, code_hit, RTree.node.injEq] at h
      have hlen := congrArg List.length h
      simp only [List.length_cons, List.length_map, List.length_nil] at hlen
      have hhead := congrArg List.head? h
      simp at hhead
  | .hit l, .skip, h => by simp at h
  | .hit l, .miss, h => by
      simp only [code_miss, code_hit, RTree.node.injEq] at h
      have hhead := congrArg List.head? h
      simp at hhead
  | .hit l, .hit l', h => by
      simp only [code_hit, RTree.node.injEq, List.cons.injEq, true_and] at h
      rw [codeL_inj l l' h]

lemma codeL_inj : ∀ l l' : List BTrace, l.map code = l'.map code → l = l'
  | [], [], _ => rfl
  | [], t' :: l', h => by simp at h
  | t :: l, [], h => by simp at h
  | t :: l, t' :: l', h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [code_inj t t' h.1, codeL_inj l l' h.2]

end

instance : Countable BTrace :=
  Function.Injective.countable (f := code) fun t t' ↦ code_inj t t'

end BTrace

/-- The accumulated shift of a trace: each hit contributes the shift of its split. -/
def bShift : BTrace → ℕ
  | .skip => 0
  | .miss => 0
  | .hit l => (l.length - 1) + (l.map bShift).sum

/-- The shifts of a list of traces. -/
def bShiftL (ts : List BTrace) : ℕ := (ts.map bShift).sum

/-- The handed count of a trace: how many next cluster roots the exit contributes. -/
def bCount : BTrace → ℕ
  | .skip => 1
  | .miss => 1
  | .hit l => (l.map bCount).sum

/-- The handed counts of a list of traces. -/
def bCountL (ts : List BTrace) : ℕ := (ts.map bCount).sum

@[simp] lemma bShift_skip : bShift .skip = 0 := by rw [bShift]

@[simp] lemma bShift_miss : bShift .miss = 0 := by rw [bShift]

lemma bShift_hit (l : List BTrace) :
    bShift (.hit l) = (l.length - 1) + bShiftL l := by
  rw [bShift, bShiftL]

@[simp] lemma bCount_skip : bCount .skip = 1 := by rw [bCount]

@[simp] lemma bCount_miss : bCount .miss = 1 := by rw [bCount]

lemma bCount_hit (l : List BTrace) : bCount (.hit l) = bCountL l := by
  rw [bCount, bCountL]

@[simp] lemma bShiftL_nil : bShiftL [] = 0 := rfl

@[simp] lemma bShiftL_cons (t : BTrace) (ts : List BTrace) :
    bShiftL (t :: ts) = bShift t + bShiftL ts := by
  simp [bShiftL]

@[simp] lemma bCountL_nil : bCountL [] = 0 := rfl

@[simp] lemma bCountL_cons (t : BTrace) (ts : List BTrace) :
    bCountL (t :: ts) = bCount t + bCountL ts := by
  simp [bCountL]

/-- **Validity of a trace**: every absorbed split is genuine, with at least two
children. -/
def BOk : BTrace → Prop
  | .skip => True
  | .miss => True
  | .hit l => 2 ≤ l.length ∧ ∀ t ∈ l, BOk t

/-- Validity of a list of traces. -/
def BOkL (ts : List BTrace) : Prop := ∀ t ∈ ts, BOk t

@[simp] lemma BOk_skip : BOk .skip := by rw [BOk]; trivial

@[simp] lemma BOk_miss : BOk .miss := by rw [BOk]; trivial

lemma BOk_hit {l : List BTrace} : BOk (.hit l) ↔ 2 ≤ l.length ∧ ∀ t ∈ l, BOk t := by
  rw [BOk]

/-- **The exits balance the shifts**: on valid traces the handed counts are the lengths
plus the accumulated shifts, so the presented children fill exactly the presented
arity. -/
lemma bCountL_eq_of_ok : ∀ ts : List BTrace, BOkL ts →
    bCountL ts = ts.length + bShiftL ts
  | [], _ => by simp
  | .skip :: ts, h => by
      have ih := bCountL_eq_of_ok ts (fun t ht ↦ h t (by simp [ht]))
      simp [ih]
      omega
  | .miss :: ts, h => by
      have ih := bCountL_eq_of_ok ts (fun t ht ↦ h t (by simp [ht]))
      simp [ih]
      omega
  | .hit l :: ts, h => by
      have hok := BOk_hit.mp (h (BTrace.hit l) (by simp))
      have ihl := bCountL_eq_of_ok l hok.2
      have ih := bCountL_eq_of_ok ts (fun t ht ↦ h t (by simp [ht]))
      simp only [bCountL_cons, bShiftL_cons, bCount_hit, bShift_hit, ih, ihl,
        List.length_cons]
      have h2 := hok.1
      omega
  termination_by ts => sizeOf ts
  decreasing_by
    all_goals
      simp only [List.cons.sizeOf_spec, BTrace.hit.sizeOf_spec]
      omega

lemma bCount_eq_of_ok {t : BTrace} (h : BOk t) : bCount t = 1 + bShift t := by
  have := bCountL_eq_of_ok [t] (by intro t' ht'; simp at ht'; rwa [ht'])
  simpa using this

/-! ### The automaton -/

/-- The junk subfield, read only off the good events. -/
def bJunk : GWord N → ℕ := fun _ ↦ 0

/-- The exits of a revealed split: its children in the reduced skeleton, in order. -/
noncomputable def bChildren (d : GWord N → ℕ) : List (GWord N → ℕ) :=
  (List.range (gArity d)).map (gSplitBush d)

@[simp] lemma bChildren_length (d : GWord N → ℕ) : (bChildren d).length = gArity d := by
  simp [bChildren]

/-- **The blob automaton of `def:blob`**: one exit at a time from the head of the
queue.  A stopped run or a stop decision skips the exit and everything after it; a
descent tests the absorption condition, a hit absorbing the split below with its
children explored first, a miss spending the exit.  The transcript grows by one event
per descent and the fuel bounds the hit nesting. -/
noncomputable def bExplore (R : ℕ) (dec : List (Option ℕ) → Bool) :
    ℕ → List (GWord N → ℕ) → Bool × List (Option ℕ) →
      List BTrace × (Bool × List (Option ℕ))
  | _, [], st => ([], st)
  | fuel, d :: rest, (stopped, evs) =>
      if stopped = true ∨ dec evs = false then
        let o := bExplore R dec fuel rest (true, evs)
        (.skip :: o.1, o.2)
      else
        if bHit R d then
          match fuel with
          | 0 =>
              let o := bExplore R dec 0 rest (true, evs)
              (.skip :: o.1, o.2)
          | fuel' + 1 =>
              let i := bExplore R dec fuel' (bChildren d)
                (false, evs ++ [some (gArity d - 1)])
              let o := bExplore R dec (fuel' + 1) rest i.2
              (.hit i.1 :: o.1, o.2)
        else
          let o := bExplore R dec fuel rest (false, evs ++ [none])
          (.miss :: o.1, o.2)
  termination_by fuel ds _ => (fuel, ds.length)
  decreasing_by
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.left _ _ (by omega)
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.right _ (by simp)

@[simp] lemma bExplore_nil (R : ℕ) (dec : List (Option ℕ) → Bool) (fuel : ℕ)
    (st : Bool × List (Option ℕ)) : bExplore (N := N) R dec fuel [] st = ([], st) := by
  obtain ⟨b, evs⟩ := st
  rw [bExplore.eq_def]

/-- The automaton at a skipped head: the run is stopped or the rule stops. -/
lemma bExplore_cons_stop (R : ℕ) (dec : List (Option ℕ) → Bool) (fuel : ℕ)
    (d : GWord N → ℕ) (rest : List (GWord N → ℕ)) {stopped : Bool}
    {evs : List (Option ℕ)} (h : stopped = true ∨ dec evs = false) :
    bExplore R dec fuel (d :: rest) (stopped, evs)
      = ((.skip :: (bExplore R dec fuel rest (true, evs)).1),
          (bExplore R dec fuel rest (true, evs)).2) := by
  rw [bExplore.eq_def]
  simp only [if_pos h]

/-- The automaton at a missed head. -/
lemma bExplore_cons_miss (R : ℕ) (dec : List (Option ℕ) → Bool) (fuel : ℕ)
    {d : GWord N → ℕ} (rest : List (GWord N → ℕ)) {stopped : Bool}
    {evs : List (Option ℕ)} (h : ¬ (stopped = true ∨ dec evs = false))
    (hd : ¬ bHit R d) :
    bExplore R dec fuel (d :: rest) (stopped, evs)
      = ((.miss :: (bExplore R dec fuel rest (false, evs ++ [none])).1),
          (bExplore R dec fuel rest (false, evs ++ [none])).2) := by
  rw [bExplore.eq_def]
  simp only [if_neg h, if_neg hd]

/-- The automaton at a hit head, with fuel. -/
lemma bExplore_cons_hit (R : ℕ) (dec : List (Option ℕ) → Bool) (fuel' : ℕ)
    {d : GWord N → ℕ} (rest : List (GWord N → ℕ)) {stopped : Bool}
    {evs : List (Option ℕ)} (h : ¬ (stopped = true ∨ dec evs = false))
    (hd : bHit R d) :
    bExplore R dec (fuel' + 1) (d :: rest) (stopped, evs)
      = ((.hit (bExplore R dec fuel' (bChildren d)
            (false, evs ++ [some (gArity d - 1)])).1
          :: (bExplore R dec (fuel' + 1) rest
            (bExplore R dec fuel' (bChildren d)
              (false, evs ++ [some (gArity d - 1)])).2).1),
          (bExplore R dec (fuel' + 1) rest
            (bExplore R dec fuel' (bChildren d)
              (false, evs ++ [some (gArity d - 1)])).2).2) := by
  rw [bExplore.eq_def]
  simp only [if_neg h, if_pos hd]

/-- The automaton at a hit head with the fuel exhausted: junk, skipped. -/
lemma bExplore_cons_hit_zero (R : ℕ) (dec : List (Option ℕ) → Bool)
    {d : GWord N → ℕ} (rest : List (GWord N → ℕ)) {stopped : Bool}
    {evs : List (Option ℕ)} (h : ¬ (stopped = true ∨ dec evs = false))
    (hd : bHit R d) :
    bExplore R dec 0 (d :: rest) (stopped, evs)
      = ((.skip :: (bExplore R dec 0 rest (true, evs)).1),
          (bExplore R dec 0 rest (true, evs)).2) := by
  rw [bExplore.eq_def]
  simp only [if_neg h, if_pos hd]

/-- The automaton answers one trace per exit. -/
lemma bExplore_fst_length (R : ℕ) (dec : List (Option ℕ) → Bool) :
    ∀ (fuel : ℕ) (ds : List (GWord N → ℕ)) (st : Bool × List (Option ℕ)),
      (bExplore R dec fuel ds st).1.length = ds.length
  | _, [], _ => by simp
  | fuel, d :: rest, (stopped, evs) => by
      by_cases h : stopped = true ∨ dec evs = false
      · rw [bExplore_cons_stop R dec fuel d rest h]
        simp [bExplore_fst_length R dec fuel rest (true, evs)]
      · by_cases hd : bHit R d
        · match fuel with
          | 0 =>
              rw [bExplore_cons_hit_zero R dec rest h hd]
              simp [bExplore_fst_length R dec 0 rest (true, evs)]
          | fuel' + 1 =>
              rw [bExplore_cons_hit R dec fuel' rest h hd]
              simp [bExplore_fst_length R dec (fuel' + 1) rest _]
        · rw [bExplore_cons_miss R dec fuel rest h hd]
          simp [bExplore_fst_length R dec fuel rest (false, evs ++ [none])]
  termination_by fuel ds _ => (fuel, ds.length)
  decreasing_by
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.right _ (by simp)

/-! ### The state recovered from the trace -/

mutual

/-- The state after one exit, recovered from its trace. -/
def bThread1 : Bool × List (Option ℕ) → BTrace → Bool × List (Option ℕ)
  | (_, evs), .skip => (true, evs)
  | (_, evs), .miss => (false, evs ++ [none])
  | (_, evs), .hit l => bThreadL (false, evs ++ [some (l.length - 1)]) l

/-- The state after a queue of exits, recovered from their traces. -/
def bThreadL : Bool × List (Option ℕ) → List BTrace → Bool × List (Option ℕ)
  | st, [] => st
  | st, t :: ts => bThreadL (bThread1 st t) ts

end

@[simp] lemma bThread1_skip (st : Bool × List (Option ℕ)) :
    bThread1 st .skip = (true, st.2) := by
  obtain ⟨b, evs⟩ := st
  rw [bThread1.eq_def]

@[simp] lemma bThread1_miss (st : Bool × List (Option ℕ)) :
    bThread1 st .miss = (false, st.2 ++ [none]) := by
  obtain ⟨b, evs⟩ := st
  rw [bThread1.eq_def]

lemma bThread1_hit (st : Bool × List (Option ℕ)) (l : List BTrace) :
    bThread1 st (.hit l) = bThreadL (false, st.2 ++ [some (l.length - 1)]) l := by
  obtain ⟨b, evs⟩ := st
  rw [bThread1.eq_def]

lemma bThread1_hit' (b₀ : Bool) (evs : List (Option ℕ)) (l : List BTrace) :
    bThread1 (b₀, evs) (.hit l) = bThreadL (false, evs ++ [some (l.length - 1)]) l :=
  bThread1_hit (b₀, evs) l

@[simp] lemma bThreadL_nil (st : Bool × List (Option ℕ)) : bThreadL st [] = st := by
  rw [bThreadL.eq_def]

lemma bThreadL_cons (st : Bool × List (Option ℕ)) (t : BTrace) (ts : List BTrace) :
    bThreadL st (t :: ts) = bThreadL (bThread1 st t) ts := by
  rw [bThreadL.eq_def]

/-- **The state of a run is a function of its trace**: threading the trace recovers the
automaton's final state. -/
lemma bExplore_snd_eq (R : ℕ) (dec : List (Option ℕ) → Bool) :
    ∀ (fuel : ℕ) (ds : List (GWord N → ℕ)) (st : Bool × List (Option ℕ)),
      (bExplore R dec fuel ds st).2 = bThreadL st (bExplore R dec fuel ds st).1
  | _, [], _ => by simp
  | fuel, d :: rest, (stopped, evs) => by
      by_cases h : stopped = true ∨ dec evs = false
      · rw [bExplore_cons_stop R dec fuel d rest h, bThreadL_cons, bThread1_skip]
        exact bExplore_snd_eq R dec fuel rest (true, evs)
      · by_cases hd : bHit R d
        · match fuel with
          | 0 =>
              rw [bExplore_cons_hit_zero R dec rest h hd]
              simp only [bThreadL_cons, bThread1_skip]
              exact bExplore_snd_eq R dec 0 rest (true, evs)
          | fuel' + 1 =>
              rw [bExplore_cons_hit R dec fuel' rest h hd, bThreadL_cons, bThread1_hit]
              have hlen : (bExplore R dec fuel' (bChildren d)
                  (false, evs ++ [some (gArity d - 1)])).1.length = gArity d := by
                rw [bExplore_fst_length]
                exact bChildren_length d
              have hinner := bExplore_snd_eq R dec fuel' (bChildren d)
                (false, evs ++ [some (gArity d - 1)])
              have houter := bExplore_snd_eq R dec (fuel' + 1) rest
                (bExplore R dec fuel' (bChildren d)
                  (false, evs ++ [some (gArity d - 1)])).2
              rw [houter]
              congr 1
              rw [hinner, hlen]
        · rw [bExplore_cons_miss R dec fuel rest h hd, bThreadL_cons, bThread1_miss]
          exact bExplore_snd_eq R dec fuel rest (false, evs ++ [none])
  termination_by fuel ds _ => (fuel, ds.length)
  decreasing_by
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.left _ _ (by omega)
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.right _ (by simp)


/-! ### Consistency and match: the run as an atom -/

mutual

/-- **Rule-consistency of a trace**: the decisions of the rule along the depth-first
flattening are the ones the trace records. -/
def bCons (dec : List (Option ℕ) → Bool) : BTrace → Bool × List (Option ℕ) → Prop
  | .skip, (stopped, evs) => stopped = true ∨ dec evs = false
  | .miss, (stopped, evs) => stopped = false ∧ dec evs = true
  | .hit l, (stopped, evs) =>
      stopped = false ∧ dec evs = true
        ∧ bConsL dec l (false, evs ++ [some (l.length - 1)])

/-- Rule-consistency of a queue of traces, threading the state. -/
def bConsL (dec : List (Option ℕ) → Bool) : List BTrace → Bool × List (Option ℕ) → Prop
  | [], _ => True
  | t :: ts, st => bCons dec t st ∧ bConsL dec ts (bThread1 st t)

end

@[simp] lemma bCons_skip {dec : List (Option ℕ) → Bool} {stopped : Bool}
    {evs : List (Option ℕ)} :
    bCons dec .skip (stopped, evs) ↔ (stopped = true ∨ dec evs = false) := by
  rw [bCons.eq_def]

@[simp] lemma bCons_miss {dec : List (Option ℕ) → Bool} {stopped : Bool}
    {evs : List (Option ℕ)} :
    bCons dec .miss (stopped, evs) ↔ (stopped = false ∧ dec evs = true) := by
  rw [bCons.eq_def]

lemma bCons_hit {dec : List (Option ℕ) → Bool} {stopped : Bool}
    {evs : List (Option ℕ)} {l : List BTrace} :
    bCons dec (.hit l) (stopped, evs)
      ↔ (stopped = false ∧ dec evs = true
          ∧ bConsL dec l (false, evs ++ [some (l.length - 1)])) := by
  rw [bCons.eq_def]

@[simp] lemma bConsL_nil {dec : List (Option ℕ) → Bool}
    {st : Bool × List (Option ℕ)} : bConsL dec [] st := by
  rw [bConsL.eq_def]
  trivial

lemma bConsL_cons {dec : List (Option ℕ) → Bool} {t : BTrace} {ts : List BTrace}
    {st : Bool × List (Option ℕ)} :
    bConsL dec (t :: ts) st ↔ bCons dec t st ∧ bConsL dec ts (bThread1 st t) := by
  rw [bConsL.eq_def]

mutual

/-- **The sample realises a trace**: a miss finds no split within the window, and a hit
finds one whose arity the trace records, its children realising the child traces. -/
def bMatch (R : ℕ) : BTrace → (GWord N → ℕ) → Prop
  | .skip, _ => True
  | .miss, d => ¬ bHit R d
  | .hit l, d => bHit R d ∧ gArity d = l.length ∧ bMatchL R l (bChildren d)

/-- A queue of subfields realising a queue of traces. -/
def bMatchL (R : ℕ) : List BTrace → List (GWord N → ℕ) → Prop
  | [], _ => True
  | t :: ts, ds => bMatch R t (ds.headD bJunk) ∧ bMatchL R ts ds.tail

end

@[simp] lemma bMatch_skip {R : ℕ} {d : GWord N → ℕ} : bMatch R .skip d := by
  rw [bMatch.eq_def]
  trivial

@[simp] lemma bMatch_miss {R : ℕ} {d : GWord N → ℕ} :
    bMatch R .miss d ↔ ¬ bHit R d := by
  rw [bMatch.eq_def]

lemma bMatch_hit {R : ℕ} {d : GWord N → ℕ} {l : List BTrace} :
    bMatch R (.hit l) d
      ↔ bHit R d ∧ gArity d = l.length ∧ bMatchL R l (bChildren d) := by
  rw [bMatch.eq_def]

@[simp] lemma bMatchL_nil {R : ℕ} {ds : List (GWord N → ℕ)} : bMatchL R [] ds := by
  rw [bMatchL.eq_def]
  trivial

lemma bMatchL_cons {R : ℕ} {t : BTrace} {ts : List BTrace}
    {ds : List (GWord N → ℕ)} :
    bMatchL R (t :: ts) ds ↔ bMatch R t (ds.headD bJunk) ∧ bMatchL R ts ds.tail := by
  rw [bMatchL.eq_def]

mutual

/-- Threading only appends events. -/
lemma le_length_bThread1 : ∀ (t : BTrace) (st : Bool × List (Option ℕ)),
    st.2.length ≤ (bThread1 st t).2.length
  | .skip, st => by simp
  | .miss, st => by simp
  | .hit l, st => by
      rw [bThread1_hit]
      have h := le_length_bThreadL l (false, st.2 ++ [some (l.length - 1)])
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      omega

lemma le_length_bThreadL : ∀ (ts : List BTrace) (st : Bool × List (Option ℕ)),
    st.2.length ≤ (bThreadL st ts).2.length
  | [], st => by simp
  | t :: ts, st => by
      rw [bThreadL_cons]
      exact le_trans (le_length_bThread1 t st) (le_length_bThreadL ts (bThread1 st t))

end


/-- **The run as an atom**: with the fuel above the stopping bound, the automaton
produces a trace exactly when the rule's decisions along its flattening agree with the
transcript and the sample realises its reveals. -/
theorem bExplore_eq_iff (R : ℕ) {dec : List (Option ℕ) → Bool} {T : ℕ}
    (hT : ∀ evs : List (Option ℕ), T ≤ evs.length → dec evs = false) :
    ∀ (fuel : ℕ) (ds : List (GWord N → ℕ)) (stopped : Bool) (evs : List (Option ℕ))
      (ts : List BTrace), T + 1 ≤ fuel + evs.length →
      ((bExplore R dec fuel ds (stopped, evs)).1 = ts
        ↔ ts.length = ds.length ∧ bConsL dec ts (stopped, evs) ∧ bMatchL R ts ds)
  | fuel, [], stopped, evs, ts, hfe => by
      simp only [bExplore_nil]
      constructor
      · rintro rfl
        simp
      · rintro ⟨hlen, -, -⟩
        rw [List.length_nil] at hlen
        exact (List.length_eq_zero_iff.mp hlen).symm
  | fuel, d :: rest, stopped, evs, ts, hfe => by
      by_cases h : stopped = true ∨ dec evs = false
      · rw [bExplore_cons_stop R dec fuel d rest h]
        constructor
        · rintro rfl
          refine ⟨by simp [bExplore_fst_length], ?_, ?_⟩
          · rw [bConsL_cons]
            refine ⟨by simpa using h, ?_⟩
            rw [bThread1_skip]
            exact ((bExplore_eq_iff R hT fuel rest true evs _ hfe).mp rfl).2.1
          · rw [bMatchL_cons]
            refine ⟨by simp, ?_⟩
            exact ((bExplore_eq_iff R hT fuel rest true evs _ hfe).mp rfl).2.2
        · rintro ⟨hlen, hcons, hmatch⟩
          match ts with
          | [] => simp at hlen
          | t :: ts' =>
              rw [bConsL_cons] at hcons
              rw [bMatchL_cons] at hmatch
              have ht : t = .skip := by
                match t with
                | .skip => rfl
                | .miss =>
                    rw [bCons_miss] at hcons
                    rcases h with h | h
                    · rw [hcons.1.1] at h
                      exact absurd h (by simp)
                    · rw [hcons.1.2] at h
                      exact absurd h (by simp)
                | .hit l =>
                    rw [bCons_hit] at hcons
                    rcases h with h | h
                    · rw [hcons.1.1] at h
                      exact absurd h (by simp)
                    · rw [hcons.1.2.1] at h
                      exact absurd h (by simp)
              subst ht
              have hrec : (bExplore R dec fuel rest (true, evs)).1 = ts' := by
                refine (bExplore_eq_iff R hT fuel rest true evs ts' hfe).mpr ?_
                refine ⟨by simpa using hlen, ?_, by simpa using hmatch.2⟩
                have := hcons.2
                rwa [bThread1_skip] at this
              show BTrace.skip :: (bExplore R dec fuel rest (true, evs)).1
                  = BTrace.skip :: ts'
              rw [hrec]
      · have hst : stopped = false := by
          cases stopped with
          | false => rfl
          | true => exact absurd (Or.inl rfl) h
        have hdec : dec evs = true := by
          cases hb : dec evs with
          | false => exact absurd (Or.inr hb) h
          | true => rfl
        subst hst
        by_cases hd : bHit R d
        · match fuel with
          | 0 =>
              exfalso
              have := hT evs (by omega)
              rw [this] at hdec
              exact absurd hdec (by simp)
          | fuel' + 1 =>
              rw [bExplore_cons_hit R dec fuel' rest (by simp [hdec]) hd]
              set X := (bExplore R dec fuel' (bChildren d)
                (false, evs ++ [some (gArity d - 1)])) with hX
              have hlen1 : X.1.length = gArity d := by
                rw [hX, bExplore_fst_length, bChildren_length]
              have hsnd : X.2 = bThreadL (false, evs ++ [some (gArity d - 1)]) X.1 := by
                rw [hX]
                exact bExplore_snd_eq R dec fuel' (bChildren d) _
              have hfe1 : T + 1 ≤ fuel' + (evs ++ [some (gArity d - 1)]).length := by
                simp only [List.length_append, List.length_cons, List.length_nil]
                omega
              have hinner := fun ts₀ ↦ bExplore_eq_iff R hT fuel' (bChildren d) false
                (evs ++ [some (gArity d - 1)]) ts₀ hfe1
              constructor
              · rintro rfl
                have hin := (hinner X.1).mp (by rw [hX])
                have hfe2 : T + 1 ≤ (fuel' + 1) + X.2.2.length := by
                  rw [hsnd]
                  have := le_length_bThreadL X.1 (false, evs ++ [some (gArity d - 1)])
                  simp only [List.length_append, List.length_cons, List.length_nil] at this
                  omega
                have hout := (bExplore_eq_iff R hT (fuel' + 1) rest X.2.1 X.2.2
                  (bExplore R dec (fuel' + 1) rest X.2).1 hfe2).mp
                  (by rw [Prod.mk.eta])
                refine ⟨by simp [bExplore_fst_length], ?_, ?_⟩
                · rw [bConsL_cons, bCons_hit]
                  refine ⟨⟨rfl, hdec, by rw [hlen1]; exact hin.2.1⟩, ?_⟩
                  rw [bThread1_hit', hlen1, ← hsnd]
                  have h := hout.2.1
                  rwa [Prod.mk.eta] at h
                · rw [bMatchL_cons]
                  refine ⟨?_, by simpa using hout.2.2⟩
                  show bMatch R (.hit X.1) d
                  rw [bMatch_hit]
                  exact ⟨hd, hlen1.symm, hin.2.2⟩
              · rintro ⟨hlen, hcons, hmatch⟩
                match ts with
                | [] => simp at hlen
                | t :: ts' =>
                    rw [bConsL_cons] at hcons
                    rw [bMatchL_cons] at hmatch
                    have ht : ∃ l, t = .hit l := by
                      match t with
                      | .skip =>
                          rw [bCons_skip] at hcons
                          rcases hcons.1 with h1 | h1
                          · exact absurd h1 (by simp)
                          · rw [h1] at hdec
                            exact absurd hdec (by simp)
                      | .miss =>
                          have := bMatch_miss.mp (by simpa using hmatch.1)
                          exact absurd hd this
                      | .hit l => exact ⟨l, rfl⟩
                    obtain ⟨l, rfl⟩ := ht
                    rw [bCons_hit] at hcons
                    have hmat := bMatch_hit.mp (by simpa using hmatch.1)
                    have hll : l.length = gArity d := hmat.2.1.symm
                    have hinnerl : X.1 = l := by
                      rw [hX]
                      refine (hinner l).mpr ?_
                      refine ⟨by rw [hll, bChildren_length], ?_, hmat.2.2⟩
                      have := hcons.1.2.2
                      rwa [hll] at this
                    have hfe2 : T + 1 ≤ (fuel' + 1) + X.2.2.length := by
                      rw [hsnd]
                      have := le_length_bThreadL X.1 (false, evs ++ [some (gArity d - 1)])
                      simp only [List.length_append, List.length_cons, List.length_nil]
                        at this
                      omega
                    have hrec : (bExplore R dec (fuel' + 1) rest X.2).1 = ts' := by
                      have := (bExplore_eq_iff R hT (fuel' + 1) rest X.2.1 X.2.2 ts'
                        hfe2).mpr ?_
                      · rwa [Prod.mk.eta] at this
                      refine ⟨by simpa using hlen, ?_, by simpa using hmatch.2⟩
                      have hth := hcons.2
                      rw [bThread1_hit', hll] at hth
                      rwa [Prod.mk.eta, hsnd, hinnerl]
                    show BTrace.hit X.1 :: (bExplore R dec (fuel' + 1) rest X.2).1
                        = BTrace.hit l :: ts'
                    rw [hinnerl, hrec]
        · rw [bExplore_cons_miss R dec fuel rest (by simp [hdec]) hd]
          have hfe1 : T + 1 ≤ fuel + (evs ++ [none]).length := by
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          constructor
          · rintro rfl
            refine ⟨by simp [bExplore_fst_length], ?_, ?_⟩
            · rw [bConsL_cons, bCons_miss]
              refine ⟨⟨rfl, hdec⟩, ?_⟩
              rw [bThread1_miss]
              exact ((bExplore_eq_iff R hT fuel rest false (evs ++ [none]) _
                hfe1).mp rfl).2.1
            · rw [bMatchL_cons]
              refine ⟨by simpa using hd, ?_⟩
              exact ((bExplore_eq_iff R hT fuel rest false (evs ++ [none]) _
                hfe1).mp rfl).2.2
          · rintro ⟨hlen, hcons, hmatch⟩
            match ts with
            | [] => simp at hlen
            | t :: ts' =>
                rw [bConsL_cons] at hcons
                rw [bMatchL_cons] at hmatch
                have ht : t = .miss := by
                  match t with
                  | .skip =>
                      rw [bCons_skip] at hcons
                      rcases hcons.1 with h1 | h1
                      · exact absurd h1 (by simp)
                      · rw [h1] at hdec
                        exact absurd hdec (by simp)
                  | .miss => rfl
                  | .hit l =>
                      have := bMatch_hit.mp (by simpa using hmatch.1)
                      exact absurd this.1 hd
                subst ht
                have hrec : (bExplore R dec fuel rest (false, evs ++ [none])).1 = ts' := by
                  refine (bExplore_eq_iff R hT fuel rest false (evs ++ [none]) ts'
                    hfe1).mpr ?_
                  refine ⟨by simpa using hlen, ?_, by simpa using hmatch.2⟩
                  have := hcons.2
                  rwa [bThread1_miss] at this
                show BTrace.miss :: (bExplore R dec fuel rest (false, evs ++ [none])).1
                    = BTrace.miss :: ts'
                rw [hrec]
  termination_by fuel ds _ _ _ _ => (fuel, ds.length)
  decreasing_by
    all_goals first
      | exact Prod.Lex.right _ (by simp)
      | exact Prod.Lex.left _ _ (by omega)


/-! ### The rule and the presented data -/

/-- **The rule of `def:blob`**: a stopping bound and a decision function of the root
shift, the transcript, and the coin at the blob's presented address. -/
structure BRule (σ : Type*) where
  T : ℕ
  decide : ℕ → List (Option ℕ) → σ → Bool
  stop : ∀ x evs s, T ≤ evs.length → decide x evs s = false

variable {σ : Type*}

/-- **The trace of the root's blob**: the automaton run on the exits of the root's
split, at fuel one above the stopping bound. -/
noncomputable def bTraceF (R : ℕ) (ρr : BRule σ) (c : GWord N → ℕ) (s : σ) :
    List BTrace :=
  (bExplore R (fun evs ↦ ρr.decide (gArity c - 1) evs s) (ρr.T + 1) (bChildren c)
    (false, [])).1

/-- **`def:blob`, the presented arity**: one plus the accumulated shift, the root split
included. -/
noncomputable def bArityC (R : ℕ) (ρr : BRule σ) (ω : (GWord N → ℕ) × (List ℕ → σ)) :
    ℕ :=
  gArity ω.1 + bShiftL (bTraceF R ρr ω.1 (ω.2 []))

/-! ### The handed subfields, by paths -/

mutual

/-- The path of the `i`-th handed subfield of one exit: the child indices through the
revealed splits, and whether the exit was spent. -/
def bPath : BTrace → ℕ → List ℕ × Bool
  | .skip, _ => ([], false)
  | .miss, _ => ([], true)
  | .hit l, i => bPathL 0 l i

/-- The path through a queue of exits, the accumulator naming the child index. -/
def bPathL : ℕ → List BTrace → ℕ → List ℕ × Bool
  | _, [], _ => ([], false)
  | k, t :: ts, i =>
      if i < bCount t then (k :: (bPath t i).1, (bPath t i).2)
      else bPathL (k + 1) ts (i - bCount t)

end

@[simp] lemma bPath_skip (i : ℕ) : bPath .skip i = ([], false) := by rw [bPath.eq_def]

@[simp] lemma bPath_miss (i : ℕ) : bPath .miss i = ([], true) := by rw [bPath.eq_def]

lemma bPath_hit (l : List BTrace) (i : ℕ) : bPath (.hit l) i = bPathL 0 l i := by
  rw [bPath.eq_def]

@[simp] lemma bPathL_nil (k i : ℕ) : bPathL k [] i = ([], false) := by
  rw [bPathL.eq_def]

lemma bPathL_cons (k : ℕ) (t : BTrace) (ts : List BTrace) (i : ℕ) :
    bPathL k (t :: ts) i
      = if i < bCount t then (k :: (bPath t i).1, (bPath t i).2)
        else bPathL (k + 1) ts (i - bCount t) := by
  rw [bPathL.eq_def]

/-- Following a path: child indices through the splits, then the revealed neck of a
spent exit. -/
noncomputable def bFollow (R : ℕ) (c : GWord N → ℕ) (q : List ℕ × Bool) :
    GWord N → ℕ :=
  if q.2 then neckIter (q.1.foldl gSplitBush c) R else q.1.foldl gSplitBush c

lemma bFollow_cons (R : ℕ) (c : GWord N → ℕ) (k : ℕ) (p : List ℕ) (sp : Bool) :
    bFollow R c (k :: p, sp) = bFollow R (gSplitBush c k) (p, sp) := by
  rw [bFollow, bFollow]
  simp

/-- **The presented children**: the `i`-th handed subfield, reached along its path,
with the coins shifted by the letter. -/
noncomputable def bSubC (R : ℕ) (ρr : BRule σ) (ω : (GWord N → ℕ) × (List ℕ → σ))
    (i : ℕ) : (GWord N → ℕ) × (List ℕ → σ) :=
  (bFollow R ω.1 (bPathL 0 (bTraceF R ρr ω.1 (ω.2 [])) i), fun w ↦ ω.2 (i :: w))

lemma bSubC_snd (R : ℕ) (ρr : BRule σ) (ω : (GWord N → ℕ) × (List ℕ → σ)) (i : ℕ) :
    (bSubC R ρr ω i).2 = fun w ↦ ω.2 (i :: w) := rfl

lemma bSubC_eta (R : ℕ) (ρr : BRule σ) (c : GWord N → ℕ) (b : List ℕ → σ) (i : ℕ) :
    bSubC R ρr (c, b) i = ((bSubC R ρr (c, b) i).1, fun w ↦ b (i :: w)) := by
  rw [Prod.ext_iff]
  exact ⟨rfl, bSubC_snd R ρr (c, b) i⟩

/-- The presented field at a presented address. -/
noncomputable def bAtC (R : ℕ) (ρr : BRule σ) :
    (GWord N → ℕ) × (List ℕ → σ) → List ℕ → (GWord N → ℕ) × (List ℕ → σ)
  | ω, [] => ω
  | ω, i :: u => bAtC R ρr (bSubC R ρr ω i) u

@[simp] lemma bAtC_nil (R : ℕ) (ρr : BRule σ) (ω : (GWord N → ℕ) × (List ℕ → σ)) :
    bAtC R ρr ω [] = ω := rfl

lemma bAtC_cons (R : ℕ) (ρr : BRule σ) (ω : (GWord N → ℕ) × (List ℕ → σ)) (i : ℕ)
    (u : List ℕ) : bAtC R ρr ω (i :: u) = bAtC R ρr (bSubC R ρr ω i) u := rfl

/-- **The presented neck at an address**: the depth of the split terminating the neck
of the cluster root, the paper's `m(w) - 1`. -/
noncomputable def bNeckAtC (R : ℕ) (ρr : BRule σ) (ω : (GWord N → ℕ) × (List ℕ → σ))
    (u : List ℕ) : ℕ :=
  gSplitDepth (bAtC R ρr ω u).1

/-- **The presented arity at an address.** -/
noncomputable def bArityAtC (R : ℕ) (ρr : BRule σ)
    (ω : (GWord N → ℕ) × (List ℕ → σ)) (u : List ℕ) : ℕ :=
  bArityC R ρr (bAtC R ρr ω u)

@[simp] lemma bNeckAtC_nil (R : ℕ) (ρr : BRule σ) (ω : (GWord N → ℕ) × (List ℕ → σ)) :
    bNeckAtC R ρr ω [] = gSplitDepth ω.1 := rfl

@[simp] lemma bArityAtC_nil (R : ℕ) (ρr : BRule σ)
    (ω : (GWord N → ℕ) × (List ℕ → σ)) : bArityAtC R ρr ω [] = bArityC R ρr ω := rfl

lemma bNeckAtC_cons (R : ℕ) (ρr : BRule σ) (ω : (GWord N → ℕ) × (List ℕ → σ)) (i : ℕ)
    (u : List ℕ) : bNeckAtC R ρr ω (i :: u) = bNeckAtC R ρr (bSubC R ρr ω i) u := rfl

lemma bArityAtC_cons (R : ℕ) (ρr : BRule σ) (ω : (GWord N → ℕ) × (List ℕ → σ)) (i : ℕ)
    (u : List ℕ) : bArityAtC R ρr ω (i :: u) = bArityAtC R ρr (bSubC R ρr ω i) u := rfl

/-! ### The rule reads only the coins at the prefixes -/

lemma bArityC_congr_coin {R : ℕ} {ρr : BRule σ} {c : GWord N → ℕ}
    {b b' : List ℕ → σ} (h : b [] = b' []) :
    bArityC R ρr (c, b) = bArityC R ρr (c, b') := by
  rw [bArityC, bArityC]
  simp only [h]

lemma bSubC_fst_congr {R : ℕ} {ρr : BRule σ} {c : GWord N → ℕ} {b b' : List ℕ → σ}
    (h : b [] = b' []) (i : ℕ) :
    (bSubC R ρr (c, b) i).1 = (bSubC R ρr (c, b') i).1 := by
  rw [bSubC, bSubC]
  simp only [h]

/-- The presented neck at an address reads only the coins at its proper prefixes. -/
lemma bNeckAtC_congr (R : ℕ) (ρr : BRule σ) :
    ∀ (u : List ℕ) (c : GWord N → ℕ) (b b' : List ℕ → σ),
      (∀ p : List ℕ, p <+: u → b p = b' p) →
      bNeckAtC R ρr (c, b) u = bNeckAtC R ρr (c, b') u
  | [], c, b, b', _ => rfl
  | i :: u, c, b, b', h => by
      rw [bNeckAtC_cons, bNeckAtC_cons]
      have hnil : b [] = b' [] := h [] List.nil_prefix
      have hfst := bSubC_fst_congr (ρr := ρr) (R := R) (c := c) hnil i
      have hb : ∀ p : List ℕ, p <+: u → b (i :: p) = b' (i :: p) := fun p hp ↦
        h (i :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
      calc bNeckAtC R ρr (bSubC R ρr (c, b) i) u
          = bNeckAtC R ρr ((bSubC R ρr (c, b) i).1, fun w ↦ b (i :: w)) u := rfl
        _ = bNeckAtC R ρr ((bSubC R ρr (c, b') i).1, fun w ↦ b' (i :: w)) u := by
            rw [hfst]
            exact bNeckAtC_congr R ρr u _ _ _ hb
        _ = bNeckAtC R ρr (bSubC R ρr (c, b') i) u := rfl

/-- The presented arity at an address reads only the coins at its prefixes. -/
lemma bArityAtC_congr (R : ℕ) (ρr : BRule σ) :
    ∀ (u : List ℕ) (c : GWord N → ℕ) (b b' : List ℕ → σ),
      (∀ p : List ℕ, p <+: u → b p = b' p) →
      bArityAtC R ρr (c, b) u = bArityAtC R ρr (c, b') u
  | [], c, b, b', h => by
      rw [bArityAtC_nil, bArityAtC_nil]
      exact bArityC_congr_coin (h [] List.nil_prefix)
  | i :: u, c, b, b', h => by
      rw [bArityAtC_cons, bArityAtC_cons]
      have hnil : b [] = b' [] := h [] List.nil_prefix
      have hfst := bSubC_fst_congr (ρr := ρr) (R := R) (c := c) hnil i
      have hb : ∀ p : List ℕ, p <+: u → b (i :: p) = b' (i :: p) := fun p hp ↦
        h (i :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
      calc bArityAtC R ρr (bSubC R ρr (c, b) i) u
          = bArityAtC R ρr ((bSubC R ρr (c, b) i).1, fun w ↦ b (i :: w)) u := rfl
        _ = bArityAtC R ρr ((bSubC R ρr (c, b') i).1, fun w ↦ b' (i :: w)) u := by
            rw [hfst]
            exact bArityAtC_congr R ρr u _ _ _ hb
        _ = bArityAtC R ρr (bSubC R ρr (c, b') i) u := rfl

/-! ### Measurability at a fixed coin field -/

/-- A measurable case split preserves fibre measurability. -/
lemma FibreMeasurableG.ite' {X : Type*} {p : (GWord N → ℕ) → Prop}
    [∀ c, Decidable (p c)] (hp : MeasurableSet {c : GWord N → ℕ | p c})
    {f g : (GWord N → ℕ) → X} (hf : FibreMeasurableG f) (hg : FibreMeasurableG g) :
    FibreMeasurableG (fun c ↦ if p c then f c else g c) := by
  intro x
  have he : {c : GWord N → ℕ | (if p c then f c else g c) = x}
      = ({c : GWord N → ℕ | p c} ∩ {c : GWord N → ℕ | f c = x})
        ∪ ({c : GWord N → ℕ | p c}ᶜ ∩ {c : GWord N → ℕ | g c = x}) := by
    ext c
    by_cases hc : p c <;> simp [hc]
  rw [he]
  exact (hp.inter (hf x)).union (hp.compl.inter (hg x))

/-- Reading a subfield-valued branch at a countably valued selector is measurable. -/
lemma measurable_comp_fibre {X : Type*} [Countable X] {g : (GWord N → ℕ) → X}
    {h : X → (GWord N → ℕ) → (GWord N → ℕ)} (hg : FibreMeasurableG g)
    (hh : ∀ x, Measurable (h x)) : Measurable (fun c ↦ h (g c) c) := by
  intro t ht
  have he : (fun c ↦ h (g c) c) ⁻¹' t
      = ⋃ x : X, ({c : GWord N → ℕ | g c = x} ∩ (h x) ⁻¹' t) := by
    ext c
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hc
      exact ⟨g c, rfl, hc⟩
    · rintro ⟨x, hx, hc⟩
      rwa [hx]
  rw [he]
  exact MeasurableSet.iUnion fun x ↦ (hg x).inter (hh x ht)

/-- **The automaton is measurable in the sample**, over any queue of measurable
subfield maps and any fixed decision function. -/
lemma fibreMeasurableG_bExploreF (R : ℕ) (dec : List (Option ℕ) → Bool) :
    ∀ (fuel : ℕ) (dsF : List ((GWord N → ℕ) → (GWord N → ℕ))),
      (∀ f ∈ dsF, Measurable f) → ∀ (st : Bool × List (Option ℕ)),
      FibreMeasurableG
        (fun c ↦ (bExplore R dec fuel (dsF.map (fun f ↦ f c)) st).1)
  | fuel, [], _, st => by
      refine (FibreMeasurableG.const ([] : List BTrace)).congr fun c ↦ ?_
      simp
  | fuel, f :: rest, hmeas, (stopped, evs) => by
      have hf : Measurable f := hmeas f (by simp)
      have hrest : ∀ f' ∈ rest, Measurable f' := fun f' hf' ↦ hmeas f' (by simp [hf'])
      by_cases h : stopped = true ∨ dec evs = false
      · have hrec := fibreMeasurableG_bExploreF R dec fuel rest hrest (true, evs)
        refine (hrec.map (fun l ↦ BTrace.skip :: l)).congr fun c ↦ ?_
        rw [List.map_cons, bExplore_cons_stop R dec fuel (f c) _ h]
      · have hmiss : FibreMeasurableG (fun c ↦
            BTrace.miss :: (bExplore R dec fuel (rest.map (fun f' ↦ f' c))
              (false, evs ++ [none])).1) :=
          (fibreMeasurableG_bExploreF R dec fuel rest hrest
            (false, evs ++ [none])).map (fun l ↦ BTrace.miss :: l)
        match fuel with
        | 0 =>
            have hskip : FibreMeasurableG (fun c ↦
                BTrace.skip :: (bExplore R dec 0 (rest.map (fun f' ↦ f' c))
                  (true, evs)).1) :=
              (fibreMeasurableG_bExploreF R dec 0 rest hrest (true, evs)).map
                (fun l ↦ BTrace.skip :: l)
            refine (FibreMeasurableG.ite' (p := fun c ↦ bHit R (f c))
              (hf (measurableSet_bHit R)) hskip hmiss).congr fun c ↦ ?_
            by_cases hc : bHit R (f c)
            · rw [if_pos hc, List.map_cons, bExplore_cons_hit_zero R dec _ h hc]
            · rw [if_neg hc, List.map_cons, bExplore_cons_miss R dec 0 _ h hc]
        | fuel' + 1 =>
            have hsel : FibreMeasurableG (fun c ↦ gArity (f c)) := fun k ↦
              hf (fibreMeasurableG_gArity k)
            have hbr : ∀ k : ℕ, FibreMeasurableG (fun c ↦
                BTrace.hit (bExplore R dec fuel'
                    ((List.range k).map (gSplitBush (f c)))
                    (false, evs ++ [some (k - 1)])).1
                  :: (bExplore R dec (fuel' + 1) (rest.map (fun f' ↦ f' c))
                    (bExplore R dec fuel'
                      ((List.range k).map (gSplitBush (f c)))
                      (false, evs ++ [some (k - 1)])).2).1) := by
              intro k
              have hinner : FibreMeasurableG (fun c ↦
                  (bExplore R dec fuel'
                    (((List.range k).map
                      (fun i ↦ fun c' ↦ gSplitBush (f c') i)).map (fun f' ↦ f' c))
                    (false, evs ++ [some (k - 1)])).1) :=
                fibreMeasurableG_bExploreF R dec fuel'
                  ((List.range k).map (fun i ↦ fun c' ↦ gSplitBush (f c') i))
                  (by
                    intro f' hf'
                    rw [List.mem_map] at hf'
                    obtain ⟨i, -, rfl⟩ := hf'
                    exact (measurable_gSplitBush i).comp hf)
                  (false, evs ++ [some (k - 1)])
              have hinner' : FibreMeasurableG (fun c ↦
                  (bExplore R dec fuel' ((List.range k).map (gSplitBush (f c)))
                    (false, evs ++ [some (k - 1)])).1) := by
                refine hinner.congr fun c ↦ ?_
                rw [List.map_map]
                rfl
              have hbr2 : ∀ l : List BTrace, FibreMeasurableG (fun c ↦
                  BTrace.hit l :: (bExplore R dec (fuel' + 1)
                    (rest.map (fun f' ↦ f' c))
                    (bThreadL (false, evs ++ [some (k - 1)]) l)).1) := fun l ↦
                (fibreMeasurableG_bExploreF R dec (fuel' + 1) rest hrest
                  (bThreadL (false, evs ++ [some (k - 1)]) l)).map
                  (fun l' ↦ BTrace.hit l :: l')
              refine (FibreMeasurableG.comp hinner' hbr2).congr fun c ↦ ?_
              rw [← bExplore_snd_eq R dec fuel' ((List.range k).map (gSplitBush (f c)))
                (false, evs ++ [some (k - 1)])]
            have hhit : FibreMeasurableG (fun c ↦
                BTrace.hit (bExplore R dec fuel'
                    ((List.range (gArity (f c))).map (gSplitBush (f c)))
                    (false, evs ++ [some (gArity (f c) - 1)])).1
                  :: (bExplore R dec (fuel' + 1) (rest.map (fun f' ↦ f' c))
                    (bExplore R dec fuel'
                      ((List.range (gArity (f c))).map (gSplitBush (f c)))
                      (false, evs ++ [some (gArity (f c) - 1)])).2).1) :=
              (FibreMeasurableG.comp hsel hbr).congr fun c ↦ rfl
            refine (FibreMeasurableG.ite' (p := fun c ↦ bHit R (f c))
              (hf (measurableSet_bHit R)) hhit hmiss).congr fun c ↦ ?_
            by_cases hc : bHit R (f c)
            · rw [if_pos hc, List.map_cons, bExplore_cons_hit R dec fuel' _ h hc]
              rfl
            · rw [if_neg hc, List.map_cons, bExplore_cons_miss R dec (fuel' + 1) _ h hc]
  termination_by fuel dsF _ _ => (fuel, dsF.length)
  decreasing_by
    all_goals first
      | exact Prod.Lex.right _ (by simp)
      | exact Prod.Lex.left _ _ (by omega)

/-- **The trace of the root's blob is measurable in the sample**, at a fixed coin. -/
lemma fibreMeasurableG_bTraceF (R : ℕ) (ρr : BRule σ) (s : σ) :
    FibreMeasurableG (fun c : GWord N → ℕ ↦ bTraceF R ρr c s) := by
  have hsel : FibreMeasurableG (gArity : (GWord N → ℕ) → ℕ) := fibreMeasurableG_gArity
  have hbr : ∀ k : ℕ, FibreMeasurableG (fun c : GWord N → ℕ ↦
      (bExplore R (fun evs ↦ ρr.decide (k - 1) evs s) (ρr.T + 1)
        ((List.range k).map (gSplitBush c)) (false, [])).1) := by
    intro k
    have h := fibreMeasurableG_bExploreF (N := N) R
      (fun evs ↦ ρr.decide (k - 1) evs s) (ρr.T + 1)
      ((List.range k).map (fun i ↦ fun c' : GWord N → ℕ ↦ gSplitBush c' i))
      (by
        intro f' hf'
        rw [List.mem_map] at hf'
        obtain ⟨i, -, rfl⟩ := hf'
        exact measurable_gSplitBush i) (false, [])
    refine h.congr fun c ↦ ?_
    rw [List.map_map]
    rfl
  exact (FibreMeasurableG.comp hsel hbr).congr fun c ↦ rfl

/-- The presented arity at the root is measurable at a fixed coin. -/
lemma fibreMeasurableG_bArityC (R : ℕ) (ρr : BRule σ) (b : List ℕ → σ) :
    FibreMeasurableG (fun c : GWord N → ℕ ↦ bArityC R ρr (c, b)) := by
  have h := FibreMeasurableG.prod (f := (gArity : (GWord N → ℕ) → ℕ))
    (g := fun c : GWord N → ℕ ↦ bTraceF R ρr c (b []))
    fibreMeasurableG_gArity (fibreMeasurableG_bTraceF R ρr (b []))
  exact (h.map fun p ↦ p.1 + bShiftL p.2).congr fun c ↦ rfl

/-- Following the split indices of a path is measurable. -/
lemma measurable_foldl_gSplitBush :
    ∀ p : List ℕ, Measurable (fun c : GWord N → ℕ ↦ p.foldl gSplitBush c)
  | [] => measurable_id
  | k :: p => by
      have hstep : (fun c : GWord N → ℕ ↦ (k :: p).foldl gSplitBush c)
          = (fun d : GWord N → ℕ ↦ p.foldl gSplitBush d)
            ∘ (fun c ↦ gSplitBush c k) := by
        funext c
        simp [Function.comp]
      rw [hstep]
      exact (measurable_foldl_gSplitBush p).comp (measurable_gSplitBush k)

/-- The presented children are measurable at a fixed coin. -/
lemma measurable_bSubC_fst (R : ℕ) (ρr : BRule σ) (b : List ℕ → σ) (i : ℕ) :
    Measurable (fun c : GWord N → ℕ ↦ (bSubC R ρr (c, b) i).1) := by
  refine measurable_comp_fibre (fibreMeasurableG_bTraceF R ρr (b []))
    (h := fun ts c ↦ bFollow R c (bPathL 0 ts i)) fun ts ↦ ?_
  by_cases hsp : (bPathL 0 ts i).2 = true
  · have he : (fun c : GWord N → ℕ ↦ bFollow R c (bPathL 0 ts i))
        = fun c ↦ neckIter ((bPathL 0 ts i).1.foldl gSplitBush c) R := by
      funext c
      rw [bFollow, if_pos hsp]
    rw [he]
    exact (measurable_neckIter R).comp (measurable_foldl_gSplitBush _)
  · have he : (fun c : GWord N → ℕ ↦ bFollow R c (bPathL 0 ts i))
        = fun c ↦ (bPathL 0 ts i).1.foldl gSplitBush c := by
      funext c
      rw [bFollow, if_neg hsp]
    rw [he]
    exact measurable_foldl_gSplitBush _

/-- The presented field along an address is measurable at a fixed coin. -/
lemma measurable_bAtC_fst (R : ℕ) (ρr : BRule σ) :
    ∀ (u : List ℕ) (b : List ℕ → σ),
      Measurable (fun c : GWord N → ℕ ↦ (bAtC R ρr (c, b) u).1)
  | [], _ => measurable_id
  | i :: u, b => by
      have he : (fun c : GWord N → ℕ ↦ (bAtC R ρr (c, b) (i :: u)).1)
          = (fun d : GWord N → ℕ ↦ (bAtC R ρr (d, fun w ↦ b (i :: w)) u).1)
            ∘ fun c ↦ (bSubC R ρr (c, b) i).1 := by
        funext c
        rw [Function.comp_apply, bAtC_cons, bSubC_eta]
      rw [he]
      exact (measurable_bAtC_fst R ρr u _).comp (measurable_bSubC_fst R ρr b i)

lemma measurableSet_bNeckAtC_eq (R : ℕ) (ρr : BRule σ) (b : List ℕ → σ) (u : List ℕ)
    (r : ℕ) :
    MeasurableSet {c : GWord N → ℕ | bNeckAtC R ρr (c, b) u = r} := by
  have he : {c : GWord N → ℕ | bNeckAtC R ρr (c, b) u = r}
      = (fun c : GWord N → ℕ ↦ (bAtC R ρr (c, b) u).1) ⁻¹'
          {d : GWord N → ℕ | gSplitDepth d = r} := rfl
  rw [he]
  exact measurable_bAtC_fst R ρr u b (fibreMeasurableG_gSplitDepth r)

lemma measurableSet_bArityAtC_eq (R : ℕ) (ρr : BRule σ) (b : List ℕ → σ) (u : List ℕ)
    (j : ℕ) :
    MeasurableSet {c : GWord N → ℕ | bArityAtC R ρr (c, b) u = j} := by
  have hb : ∀ c : GWord N → ℕ, bArityAtC R ρr (c, b) u
      = bArityC R ρr ((bAtC R ρr (c, b) u).1, fun w ↦ b (u ++ w)) := by
    intro c
    have hsnd : (bAtC R ρr (c, b) u).2 = fun w ↦ b (u ++ w) := by
      induction u generalizing c b with
      | nil => simp
      | cons i u ih =>
          rw [bAtC_cons, bSubC_eta, ih]
          funext w
          simp
    show bArityC R ρr (bAtC R ρr (c, b) u) = _
    have hpair : bAtC R ρr (c, b) u = ((bAtC R ρr (c, b) u).1, fun w ↦ b (u ++ w)) := by
      rw [Prod.ext_iff]
      exact ⟨rfl, hsnd⟩
    rw [hpair]
  have he : {c : GWord N → ℕ | bArityAtC R ρr (c, b) u = j}
      = (fun c : GWord N → ℕ ↦ (bAtC R ρr (c, b) u).1) ⁻¹'
          {d : GWord N → ℕ | bArityC R ρr (d, fun w ↦ b (u ++ w)) = j} := by
    ext c
    rw [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_setOf_eq, hb c]
  rw [he]
  exact measurable_bAtC_fst R ρr u b (fibreMeasurableG_bArityC R ρr _ j)

end ChainClasses
