import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ChainClasses.Regime.MatchedPresentation
import ChainClasses.Regime.BlobLaw

/-!
`thm:matched-presentation` (`it:matched-product`) of
`matching_classes_general.tex`: the matched presentation is a blob presentation
of `def:blob`, and its presented arity law on the constructed space is the law
`matchedShift` of `MatchedPresentation`.

The rule of `thm:matched-presentation` reads, beyond the revealed transcript,
one coin per presented address: the branch choice of mass `δ`, the simulated
increments of the other law, and the stopping bits of the free branch.  Here
the coin is a finite type carrying the product law, the rule is a `BRule` on it,
and the coin-averaged rule mass of `BlobLaw` is identified with the automaton
law of `MatchedPresentation`: a trace sum with continuation flattens the
depth-first trace tree of `BlobField` into the transcript automaton, the
transcript automaton at a fixed coin is the coupled or free automaton driven by
the coin's lists, and averaging the lists against the product law gives
`couple` and `free`.  `thm:blob-law`'s i.i.d. clause then reads, for the matched
rule, as the product formula with the neck geometric and the arity law
`matchedShift`, which is clause `it:matched-product`, and the law-level
clauses transfer to the presented law on `blobMeasure`.

* `traceSum`, `traceSum_succ`, `traceSum_comp`, `traceSum_succ_decomp`: **the
  trace sum with continuation** over rule-consistent valid traces, its head
  step, its composition over concatenated queues, and its root-step
  decomposition into a stop, a miss and one hit per revealed arity.
* `bRuleMass_eq_sum_traceSum`: `bRuleMass` is the trace sum over the root's
  arity.
* `MatchedCoin`, `coinMass`, `matchedCoinLaw`: **the coin** and its law.
* `matchedRule`: **the rule of `thm:matched-presentation` as a `BRule`**, the
  lagging-side comparison against the simulated walk fast-forwarded through
  the coin's increments, or the free branch stopping on the coin's bits.
* `coupleSeq`, `freeSeq`, `sum_coupleSeq_eq_couple`, `sum_freeSeq_eq_free`: the
  automata driven by explicit increment and bit lists, averaging to `couple`
  and `free`.
* `traceSum_coupledDec`, `traceSum_freeDec`: **the transcript automaton at a
  fixed coin** is the list-driven automaton.
* `coinRuleMass_matchedRule`: **the identification**: the coin-averaged rule
  mass at arity `1 + j` is `(1 - θ̃₁) matchedShift j`.
* `matched_iid`: **`thm:matched-presentation` (`it:matched-product`)**:
  over `blobMeasure` the presented pairs are i.i.d. over prefix-closed probes,
  the neck geometric with ratio `θ̃₁` and the presented shift carrying
  `matchedShift`.
* `presentedShift`, `presentedShift_eq`, `presentedShift_pos_iff`,
  `presentedShift_floor`, `presentedShift_bulk_close`,
  `presentedShift_window`: the presented shift law of the blob presentation on
  the constructed space and the clauses
  `it:matched-support`, `it:matched-mass`, `it:matched-bulk` for it.
-/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal
open BranchingProcess (Offspring survivalMeasure)

variable {J N : ℕ}

/-! ### Transcript arithmetic -/

/-- The accumulated shift of a transcript: the sum of the revealed shifts. -/
def shiftSum (evs : List (Option ℕ)) : ℕ := (evs.map fun o ↦ o.getD 0).sum

@[simp] lemma shiftSum_nil : shiftSum [] = 0 := rfl

@[simp] lemma shiftSum_append_none (evs : List (Option ℕ)) :
    shiftSum (evs ++ [none]) = shiftSum evs := by
  simp [shiftSum]

@[simp] lemma shiftSum_append_some (evs : List (Option ℕ)) (k : ℕ) :
    shiftSum (evs ++ [some k]) = shiftSum evs + k := by
  simp [shiftSum]

/-- The real total of a blob whose root split has shift `x` after the
transcript `evs`. -/
def rOf (x : ℕ) (evs : List (Option ℕ)) : ℕ := x + shiftSum evs

@[simp] lemma rOf_nil (x : ℕ) : rOf x [] = x := by simp [rOf]

@[simp] lemma rOf_append_none (x : ℕ) (evs : List (Option ℕ)) :
    rOf x (evs ++ [none]) = rOf x evs := by simp [rOf]

@[simp] lemma rOf_append_some (x : ℕ) (evs : List (Option ℕ)) (k : ℕ) :
    rOf x (evs ++ [some k]) = rOf x evs + k := by simp [rOf, Nat.add_assoc]

mutual

/-- Threading a trace adds its accumulated shift to the transcript's shift. -/
lemma shiftSum_bThread1 : ∀ (t : BTrace) (st : Bool × List (Option ℕ)),
    shiftSum (bThread1 st t).2 = shiftSum st.2 + bShift t
  | .skip, st => by simp
  | .miss, st => by simp
  | .hit l, st => by
      rw [bThread1_hit, shiftSum_bThreadL l, bShift_hit]
      simp only [shiftSum_append_some]
      omega

lemma shiftSum_bThreadL : ∀ (ts : List BTrace) (st : Bool × List (Option ℕ)),
    shiftSum (bThreadL st ts).2 = shiftSum st.2 + bShiftL ts
  | [], st => by simp
  | t :: ts, st => by
      rw [bThreadL_cons, shiftSum_bThreadL ts, shiftSum_bThread1 t, bShiftL_cons]
      omega

end

/-- The simulated walk fast-forwarded from the total `t` through the increments
`ys` until it reaches `r`. -/
def ffwd (r : ℕ) : ℕ → List ℕ → ℕ
  | t, [] => t
  | t, y :: ys => if r ≤ t then t else ffwd r (t + y) ys

/-- The fast-forward stops at once past `r`. -/
lemma ffwd_of_le {r t : ℕ} (h : r ≤ t) (ys : List ℕ) : ffwd r t ys = t := by
  cases ys with
  | nil => rfl
  | cons y ys => simp [ffwd, h]

lemma ffwd_cons_of_lt {r t : ℕ} (h : t < r) (y : ℕ) (ys : List ℕ) :
    ffwd r t (y :: ys) = ffwd r (t + y) ys := by
  simp [ffwd, Nat.not_le.mpr h]

/-- A consumed prefix all of whose proper partial sums lie below `r` is skipped by
the fast-forward. -/
lemma ffwd_append (r : ℕ) : ∀ (pre ys : List ℕ) (t : ℕ),
    (∀ k, k < pre.length → t + (pre.take k).sum < r) →
    ffwd r t (pre ++ ys) = ffwd r (t + pre.sum) ys
  | [], ys, t, _ => by simp
  | y :: pre, ys, t, h => by
      have h0 : t < r := by simpa using h 0 (by simp)
      rw [List.cons_append, ffwd_cons_of_lt h0, ffwd_append r pre ys (t + y) ?_]
      · simp only [List.sum_cons]
        congr 1
        omega
      · intro k hk
        have := h (k + 1) (by simp; omega)
        simpa [List.take_succ_cons, Nat.add_assoc] using this

/-! ### Sums over traces -/

/-- A sum over lists splits off the empty list and the head. -/
lemma list_tsum_cons {α : Type*} (g : List α → ℝ≥0∞) :
    ∑' ts : List α, g ts = g [] + ∑' p : α × List α, g (p.1 :: p.2) := by
  have hsplit : ∑' ts : List α, g ts
      = ∑' ts : List α, (if ts = [] then g ts else 0)
        + ∑' ts : List α, (if ts = [] then 0 else g ts) := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun ts ↦ ?_
    split_ifs <;> simp
  have h1 : ∑' ts : List α, (if ts = [] then g ts else 0) = g [] := by
    rw [tsum_eq_single ([] : List α)]
    · simp
    · intro ts hts
      rw [if_neg hts]
  have hinj : Function.Injective fun p : α × List α ↦ p.1 :: p.2 := by
    intro p q h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2
  have hsupp : Function.support (fun ts : List α ↦ if ts = [] then 0 else g ts)
      ⊆ Set.range fun p : α × List α ↦ p.1 :: p.2 := by
    intro ts hts
    cases ts with
    | nil => simp at hts
    | cons a l => exact ⟨(a, l), rfl⟩
  have h2 : ∑' ts : List α, (if ts = [] then 0 else g ts)
      = ∑' p : α × List α, g (p.1 :: p.2) := by
    calc ∑' ts : List α, (if ts = [] then 0 else g ts)
        = ∑' p : α × List α, (if p.1 :: p.2 = [] then 0 else g (p.1 :: p.2)) :=
          (hinj.tsum_eq hsupp).symm
      _ = ∑' p : α × List α, g (p.1 :: p.2) := tsum_congr fun p ↦ by simp
  rw [hsplit, h1, h2]

/-- A sum over traces splits into the skip, the miss, and the hits. -/
lemma btrace_tsum (g : BTrace → ℝ≥0∞) :
    ∑' t : BTrace, g t = g .skip + g .miss + ∑' l : List BTrace, g (.hit l) := by
  classical
  have hsplit : ∑' t : BTrace, g t
      = ∑' t : BTrace, (if t = BTrace.skip then g t else 0)
        + ∑' t : BTrace, (if t = BTrace.miss then g t else 0)
        + ∑' t : BTrace, (if t = BTrace.skip ∨ t = BTrace.miss then 0 else g t) := by
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun t ↦ ?_
    cases t <;> simp
  have h1 : ∑' t : BTrace, (if t = BTrace.skip then g t else 0) = g BTrace.skip := by
    rw [tsum_eq_single BTrace.skip]
    · simp
    · intro t ht
      rw [if_neg ht]
  have h2 : ∑' t : BTrace, (if t = BTrace.miss then g t else 0) = g BTrace.miss := by
    rw [tsum_eq_single BTrace.miss]
    · simp
    · intro t ht
      rw [if_neg ht]
  have hinj : Function.Injective BTrace.hit := fun l l' h ↦ BTrace.hit.inj h
  have hsupp : Function.support (fun t : BTrace ↦
      if t = BTrace.skip ∨ t = BTrace.miss then 0 else g t) ⊆ Set.range BTrace.hit := by
    intro t ht
    cases t with
    | skip => simp at ht
    | miss => simp at ht
    | hit l => exact ⟨l, rfl⟩
  have h3 : ∑' t : BTrace, (if t = BTrace.skip ∨ t = BTrace.miss then 0 else g t)
      = ∑' l : List BTrace, g (BTrace.hit l) := by
    calc ∑' t : BTrace, (if t = BTrace.skip ∨ t = BTrace.miss then 0 else g t)
        = ∑' l : List BTrace, (if BTrace.hit l = BTrace.skip ∨ BTrace.hit l = BTrace.miss
            then 0 else g (BTrace.hit l)) := (hinj.tsum_eq hsupp).symm
      _ = ∑' l : List BTrace, g (BTrace.hit l) := tsum_congr fun l ↦ by simp
  rw [hsplit, h1, h2, h3]

section TraceSum

variable (θ : Offspring J) (R : ℕ)

open Classical in
/-- **The trace sum with continuation**: over the valid traces of a queue of `n`
exits consistent with the rule from the state `st`, the trace mass against the
continuation read at the threaded state. -/
noncomputable def traceSum (dec : List (Option ℕ) → Bool) (st : Bool × List (Option ℕ))
    (n : ℕ) (f : Bool × List (Option ℕ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' ts : List BTrace,
    if ts.length = n ∧ bConsL dec ts st ∧ BOkL ts then
      traceMassL θ R ts * f (bThreadL st ts) else 0

variable {θ R}

/-- With no exit the continuation is read at once. -/
lemma traceSum_zero (dec : List (Option ℕ) → Bool) (st : Bool × List (Option ℕ))
    (f : Bool × List (Option ℕ) → ℝ≥0∞) : traceSum θ R dec st 0 f = f st := by
  classical
  rw [traceSum, tsum_eq_single ([] : List BTrace)]
  · have hok : BOkL ([] : List BTrace) := fun t ht ↦ absurd ht List.not_mem_nil
    rw [if_pos ⟨rfl, bConsL_nil, hok⟩, traceMassL_nil, bThreadL_nil, one_mul]
  · intro ts hts
    rw [if_neg]
    rintro ⟨hlen, -, -⟩
    exact hts (List.length_eq_zero_iff.mp hlen)

open Classical in
/-- **The head step** of the trace sum: one trace for the head exit against the
sum over the rest from the threaded state. -/
lemma traceSum_succ (dec : List (Option ℕ) → Bool) (st : Bool × List (Option ℕ))
    (n : ℕ) (f : Bool × List (Option ℕ) → ℝ≥0∞) :
    traceSum θ R dec st (n + 1) f
      = ∑' t : BTrace, if bCons dec t st ∧ BOk t then
          traceMass θ R t * traceSum θ R dec (bThread1 st t) n f else 0 := by
  rw [traceSum, list_tsum_cons]
  have h0 : (if ([] : List BTrace).length = n + 1 ∧ bConsL dec [] st ∧ BOkL [] then
      traceMassL θ R [] * f (bThreadL st []) else 0) = 0 := by
    rw [if_neg]
    rintro ⟨h, -⟩
    simp at h
  rw [h0, zero_add, ENNReal.tsum_prod']
  refine tsum_congr fun t ↦ ?_
  by_cases h : bCons dec t st ∧ BOk t
  · rw [if_pos h, traceSum, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun ts ↦ ?_
    by_cases hts : ts.length = n ∧ bConsL dec ts (bThread1 st t) ∧ BOkL ts
    · rw [if_pos hts, if_pos, traceMassL_cons, bThreadL_cons, mul_assoc]
      refine ⟨by simp [hts.1], bConsL_cons.mpr ⟨h.1, hts.2.1⟩, ?_⟩
      intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact h.2
      · exact hts.2.2 t' ht'
    · rw [if_neg hts, if_neg, mul_zero]
      rintro ⟨hlen, hcons, hok⟩
      exact hts ⟨by simpa using hlen, (bConsL_cons.mp hcons).2,
        fun t' ht' ↦ hok t' (List.mem_cons_of_mem t ht')⟩
  · rw [if_neg h]
    refine ENNReal.tsum_eq_zero.mpr fun ts ↦ ?_
    rw [if_neg]
    rintro ⟨-, hcons, hok⟩
    exact h ⟨(bConsL_cons.mp hcons).1, hok t List.mem_cons_self⟩

/-- From a stopped state every exit is skipped. -/
lemma traceSum_stopped (dec : List (Option ℕ) → Bool) (evs : List (Option ℕ)) :
    ∀ (n : ℕ) (f : Bool × List (Option ℕ) → ℝ≥0∞),
      traceSum θ R dec (true, evs) n f = f (true, evs) := by
  intro n
  induction n with
  | zero => intro f; exact traceSum_zero dec _ f
  | succ n ih =>
      intro f
      classical
      rw [traceSum_succ, tsum_eq_single BTrace.skip]
      · rw [if_pos ⟨bCons_skip.mpr (Or.inl rfl), BOk_skip⟩, traceMass_skip, one_mul,
          bThread1_skip]
        exact ih f
      · intro t ht
        rw [if_neg]
        rintro ⟨hc, -⟩
        cases t with
        | skip => exact ht rfl
        | miss => exact absurd (bCons_miss.mp hc).1 (by simp)
        | hit l => exact absurd (bCons_hit.mp hc).1 (by simp)

/-- **Composition**: exploring `k` exits and then `n` more is exploring `k + n`. -/
lemma traceSum_comp (dec : List (Option ℕ) → Bool) (n : ℕ)
    (f : Bool × List (Option ℕ) → ℝ≥0∞) :
    ∀ (k : ℕ) (st : Bool × List (Option ℕ)),
      traceSum θ R dec st (k + n) f
        = traceSum θ R dec st k (fun st' ↦ traceSum θ R dec st' n f) := by
  intro k
  induction k with
  | zero => intro st; rw [Nat.zero_add, traceSum_zero]
  | succ k ih =>
      intro st
      rw [Nat.succ_add, traceSum_succ, traceSum_succ]
      refine tsum_congr fun t ↦ ?_
      classical
      split_ifs with h
      · rw [ih]
      · rfl

/-- **The root-step decomposition** of the trace sum at an unstopped state with
at least one exit: a stop decision skips everything, and otherwise a miss spends
the exit with the mass `θ̃₁^R` and a hit of arity `k` absorbs a split with the
revealing-window mass against the split weight, pushing its `k` exits. -/
lemma traceSum_succ_decomp (dec : List (Option ℕ) → Bool)
    (evs : List (Option ℕ)) (m : ℕ) (f : Bool × List (Option ℕ) → ℝ≥0∞) :
    traceSum θ R dec (false, evs) (m + 1) f
      = if dec evs = false then f (true, evs)
        else ENNReal.ofReal (θ.skeletonWeight 1) ^ R
              * traceSum θ R dec (false, evs ++ [none]) m f
          + ∑ k ∈ Finset.range (J + 1), ENNReal.ofReal (θ.skeletonWeight k)
              * (if 2 ≤ k then
                  (∑ d ∈ Finset.range R, ENNReal.ofReal (θ.skeletonWeight 1) ^ d)
                    * traceSum θ R dec (false, evs ++ [some (k - 1)]) (k + m) f
                else 0) := by
  classical
  rw [traceSum_succ, btrace_tsum]
  by_cases hdec : dec evs = false
  · rw [if_pos hdec]
    have hskip : (if bCons dec BTrace.skip (false, evs) ∧ BOk BTrace.skip then
        traceMass θ R BTrace.skip
          * traceSum θ R dec (bThread1 (false, evs) BTrace.skip) m f else 0)
        = f (true, evs) := by
      rw [if_pos ⟨bCons_skip.mpr (Or.inr hdec), BOk_skip⟩, traceMass_skip, one_mul,
        bThread1_skip, traceSum_stopped]
    have hmiss : (if bCons dec BTrace.miss (false, evs) ∧ BOk BTrace.miss then
        traceMass θ R BTrace.miss
          * traceSum θ R dec (bThread1 (false, evs) BTrace.miss) m f else 0) = 0 := by
      rw [if_neg]
      rintro ⟨hc, -⟩
      rw [(bCons_miss.mp hc).2] at hdec
      exact absurd hdec (by simp)
    have hhit : ∑' l : List BTrace,
        (if bCons dec (BTrace.hit l) (false, evs) ∧ BOk (BTrace.hit l) then
          traceMass θ R (BTrace.hit l)
            * traceSum θ R dec (bThread1 (false, evs) (BTrace.hit l)) m f else 0) = 0 := by
      refine ENNReal.tsum_eq_zero.mpr fun l ↦ ?_
      rw [if_neg]
      rintro ⟨hc, -⟩
      rw [(bCons_hit.mp hc).2.1] at hdec
      exact absurd hdec (by simp)
    rw [hskip, hmiss, hhit, add_zero, add_zero]
  · rw [if_neg hdec]
    have hdec' : dec evs = true := by
      cases h : dec evs with
      | false => exact absurd h hdec
      | true => rfl
    have hskip : (if bCons dec BTrace.skip (false, evs) ∧ BOk BTrace.skip then
        traceMass θ R BTrace.skip
          * traceSum θ R dec (bThread1 (false, evs) BTrace.skip) m f else 0) = 0 := by
      rw [if_neg]
      rintro ⟨hc, -⟩
      rcases bCons_skip.mp hc with h | h
      · exact absurd h (by simp)
      · exact hdec h
    have hmiss : (if bCons dec BTrace.miss (false, evs) ∧ BOk BTrace.miss then
        traceMass θ R BTrace.miss
          * traceSum θ R dec (bThread1 (false, evs) BTrace.miss) m f else 0)
        = ENNReal.ofReal (θ.skeletonWeight 1) ^ R
            * traceSum θ R dec (false, evs ++ [none]) m f := by
      rw [if_pos ⟨bCons_miss.mpr ⟨rfl, hdec'⟩, BOk_miss⟩, traceMass_miss, bThread1_miss]
    rw [hskip, hmiss, zero_add]
    congr 1
    -- the hit sum, split by the revealed arity
    set G : ℝ≥0∞ := ∑ d ∈ Finset.range R, ENNReal.ofReal (θ.skeletonWeight 1) ^ d with hG
    have hterm : ∀ k ∈ Finset.range (J + 1),
        ENNReal.ofReal (θ.skeletonWeight k)
          * (if 2 ≤ k then G * traceSum θ R dec (false, evs ++ [some (k - 1)]) (k + m) f
              else 0)
        = ∑' l : List BTrace,
            if l.length = k ∧ 2 ≤ k ∧ bConsL dec l (false, evs ++ [some (k - 1)])
                ∧ BOkL l then
              G * ENNReal.ofReal (θ.skeletonWeight k) * traceMassL θ R l
                * traceSum θ R dec (bThreadL (false, evs ++ [some (k - 1)]) l) m f
            else 0 := by
      intro k _
      by_cases hk : 2 ≤ k
      · rw [if_pos hk, traceSum_comp, traceSum, ← ENNReal.tsum_mul_left,
          ← ENNReal.tsum_mul_left]
        refine tsum_congr fun l ↦ ?_
        by_cases hl : l.length = k ∧ bConsL dec l (false, evs ++ [some (k - 1)]) ∧ BOkL l
        · rw [if_pos hl, if_pos ⟨hl.1, hk, hl.2⟩]
          ring
        · rw [if_neg hl, if_neg]
          · simp
          · rintro ⟨h1, -, h2, h3⟩
            exact hl ⟨h1, h2, h3⟩
      · rw [if_neg hk, mul_zero]
        symm
        refine ENNReal.tsum_eq_zero.mpr fun l ↦ ?_
        rw [if_neg]
        rintro ⟨-, h, -⟩
        exact hk h
    rw [Finset.sum_congr rfl hterm, ← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
    refine tsum_congr fun l ↦ ?_
    by_cases hlJ : l.length ≤ J
    · rw [Finset.sum_eq_single l.length]
      · by_cases hl : 2 ≤ l.length ∧ bConsL dec l (false, evs ++ [some (l.length - 1)])
            ∧ BOkL l
        · rw [if_pos ⟨bCons_hit.mpr ⟨rfl, hdec', hl.2.1⟩, BOk_hit.mpr ⟨hl.1, hl.2.2⟩⟩,
            if_pos ⟨rfl, hl⟩, traceMass_hit, bThread1_hit']
        · rw [if_neg (c := l.length = l.length ∧ 2 ≤ l.length
              ∧ bConsL dec l (false, evs ++ [some (l.length - 1)]) ∧ BOkL l)
              (fun h ↦ hl h.2),
            if_neg (c := bCons dec (BTrace.hit l) (false, evs) ∧ BOk (BTrace.hit l))]
          rintro ⟨hc, hok⟩
          exact hl ⟨(BOk_hit.mp hok).1, (bCons_hit.mp hc).2.2, (BOk_hit.mp hok).2⟩
      · intro k _ hk
        rw [if_neg]
        rintro ⟨h, -⟩
        exact hk h.symm
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    · have hvan : θ.skeletonWeight l.length = 0 :=
        θ.skeletonWeight_vanishing (by omega)
      rw [Finset.sum_eq_zero]
      · split_ifs with h
        · rw [traceMass_hit, hvan, ENNReal.ofReal_zero, mul_zero, zero_mul, zero_mul]
        · rfl
      · intro k hk
        rw [if_neg]
        rintro ⟨h, -⟩
        rw [Finset.mem_range] at hk
        omega

/-- **`bRuleMass` is a trace sum**: at the presented arity `1 + j`, the split
weight of the root's arity `n` against the trace sum over the root's `n` exits
with the rule read at the root shift `n - 1`, stopped at the total `j`. -/
lemma bRuleMass_eq_sum_traceSum {σ : Type*} (ρr : BRule σ) (s : σ) (j : ℕ) :
    bRuleMass θ R ρr s (1 + j)
      = ∑ n ∈ Finset.range (J + 1), ENNReal.ofReal (θ.skeletonWeight n)
          * (if 2 ≤ n then
              traceSum θ R (fun evs ↦ ρr.decide (n - 1) evs s) (false, []) n
                (fun st ↦ if j = rOf (n - 1) st.2 then 1 else 0)
            else 0) := by
  classical
  have hsub := tsum_subtype {ts : List BTrace | BAtom ρr s (1 + j) ts}
    (fun ts ↦ ENNReal.ofReal (θ.skeletonWeight ts.length) * traceMassL θ R ts)
  rw [bRuleMass]
  refine hsub.trans ?_
  have hterm : ∀ n ∈ Finset.range (J + 1),
      ENNReal.ofReal (θ.skeletonWeight n)
        * (if 2 ≤ n then
            traceSum θ R (fun evs ↦ ρr.decide (n - 1) evs s) (false, []) n
              (fun st ↦ if j = rOf (n - 1) st.2 then 1 else 0)
          else 0)
      = ∑' ts : List BTrace,
          if ts.length = n ∧ BAtom ρr s (1 + j) ts then
            ENNReal.ofReal (θ.skeletonWeight n) * traceMassL θ R ts else 0 := by
    intro n _
    by_cases hn : 2 ≤ n
    · rw [if_pos hn, traceSum, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun ts ↦ ?_
      by_cases hlen : ts.length = n
      · subst hlen
        by_cases hc : bConsL (fun evs ↦ ρr.decide (ts.length - 1) evs s) ts (false, [])
            ∧ BOkL ts
        · rw [if_pos ⟨rfl, hc⟩]
          have hshift : rOf (ts.length - 1) (bThreadL (false, []) ts).2
              = ts.length - 1 + bShiftL ts := by
            rw [rOf, shiftSum_bThreadL]
            simp
          rw [hshift]
          by_cases hj : j = ts.length - 1 + bShiftL ts
          · rw [if_pos hj, mul_one, if_pos ⟨rfl, hc.1, hc.2, hn, by omega⟩]
          · rw [if_neg hj, mul_zero, mul_zero, if_neg]
            rintro ⟨-, -, -, -, h⟩
            exact hj (by omega)
        · rw [if_neg (fun h ↦ hc h.2), mul_zero, if_neg]
          rintro ⟨-, h1, h2, -, -⟩
          exact hc ⟨h1, h2⟩
      · rw [if_neg (fun h ↦ hlen h.1), mul_zero, if_neg (fun h ↦ hlen h.1)]
    · rw [if_neg hn, mul_zero]
      symm
      refine ENNReal.tsum_eq_zero.mpr fun ts ↦ ?_
      rw [if_neg]
      rintro ⟨hlen, -, -, h2, -⟩
      exact hn (hlen ▸ h2)
  rw [Finset.sum_congr rfl hterm, ← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
  refine tsum_congr fun ts ↦ ?_
  rw [Set.indicator_apply]
  by_cases hlJ : ts.length ≤ J
  · rw [Finset.sum_eq_single ts.length]
    · by_cases hatom : BAtom ρr s (1 + j) ts
      · rw [if_pos (c := ts.length = ts.length ∧ BAtom ρr s (1 + j) ts) ⟨rfl, hatom⟩,
          if_pos (show ts ∈ {ts : List BTrace | BAtom ρr s (1 + j) ts} from hatom)]
      · rw [if_neg (c := ts.length = ts.length ∧ BAtom ρr s (1 + j) ts) (fun h ↦ hatom h.2),
          if_neg (show ts ∉ {ts : List BTrace | BAtom ρr s (1 + j) ts} from hatom)]
    · intro n _ hn
      rw [if_neg (fun h ↦ hn h.1.symm)]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · have hvan : θ.skeletonWeight ts.length = 0 := θ.skeletonWeight_vanishing (by omega)
    rw [Finset.sum_eq_zero]
    · split_ifs
      · rw [hvan, ENNReal.ofReal_zero, zero_mul]
      · rfl
    · intro n hn
      rw [Finset.mem_range] at hn
      rw [if_neg (fun h ↦ by omega)]

/-- Reindexing a sum over the reduced arities by the shift: the arities `k ≥ 2`
with nonvanishing weight are exactly `1 + x` for `x` in the shifted support `A`. -/
lemma sum_arity_eq_sum_shift {A : Finset ℕ} (hA1 : ∀ x ∈ A, 1 ≤ x)
    (hAsupp : ∀ x, 1 ≤ x → θ.skeletonWeight (1 + x) ≠ 0 → x ∈ A) (g : ℕ → ℝ≥0∞) :
    ∑ k ∈ Finset.range (J + 1), ENNReal.ofReal (θ.skeletonWeight k)
        * (if 2 ≤ k then g (k - 1) else 0)
      = ∑ x ∈ A, ENNReal.ofReal (θ.skeletonWeight (1 + x)) * g x := by
  classical
  set S : Finset ℕ := (Finset.range J).filter fun x ↦ 1 ≤ x ∧ θ.skeletonWeight (1 + x) ≠ 0
    with hS
  have hL : ∑ k ∈ Finset.range (J + 1), ENNReal.ofReal (θ.skeletonWeight k)
        * (if 2 ≤ k then g (k - 1) else 0)
      = ∑ x ∈ S, ENNReal.ofReal (θ.skeletonWeight (1 + x)) * g x := by
    rw [Finset.sum_range_succ', hS, Finset.sum_filter]
    simp only [show ¬ (2 ≤ 0) by omega, if_false, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : 1 ≤ x
    · rw [if_pos (by omega), Nat.add_sub_cancel]
      by_cases hv : θ.skeletonWeight (1 + x) ≠ 0
      · rw [if_pos ⟨hx, hv⟩, Nat.add_comm]
      · have hv' : θ.skeletonWeight (1 + x) = 0 := not_not.mp hv
        rw [if_neg (fun h ↦ h.2 hv'), Nat.add_comm, hv', ENNReal.ofReal_zero, zero_mul]
    · rw [if_neg (by omega), if_neg (fun h ↦ hx h.1), mul_zero]
  have hR : ∑ x ∈ A, ENNReal.ofReal (θ.skeletonWeight (1 + x)) * g x
      = ∑ x ∈ S, ENNReal.ofReal (θ.skeletonWeight (1 + x)) * g x := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      rw [hS, Finset.mem_filter] at hx
      exact hAsupp x hx.2.1 hx.2.2
    · intro x hxA hxS
      rw [hS, Finset.mem_filter, Finset.mem_range] at hxS
      have hv : θ.skeletonWeight (1 + x) = 0 := by
        by_contra hne
        have hJ : x < J := by
          by_contra hle
          exact hne (θ.skeletonWeight_vanishing (by omega))
        exact hxS ⟨hJ, hA1 x hxA, hne⟩
      rw [hv, ENNReal.ofReal_zero, zero_mul]
  rw [hL, hR]

end TraceSum

/-! ### The coin and the rule -/

section Coin

variable (B : Finset ℕ) (T : ℕ)

/-- **The coin of the matched rule** at one presented address: the branch bit
(`true` for free exploration), `T` simulated increments of the other law, and
`T` stopping bits for the free branch (`true` to stop). -/
abbrev MatchedCoin : Type := Bool × (Fin T → B) × (Fin T → Bool)

variable {B T}

/-- The simulated increments of the coin as a list. -/
def oppList (s : MatchedCoin B T) : List ℕ := List.ofFn fun i ↦ (s.2.1 i).val

/-- The stopping bit of the coin read at the `m`-th decision; `true` past the
stopping bound. -/
def bitAt (β : Fin T → Bool) (m : ℕ) : Bool := if h : m < T then β ⟨m, h⟩ else true

/-- The mass of a coin: `δ` or `1 - δ` for the branch, the law `P'` on each
simulated increment, a fair bit each. -/
noncomputable def coinMass (δ : ℝ) (P' : ℕ → ℝ) (s : MatchedCoin B T) : ℝ :=
  (if s.1 then δ else 1 - δ) * (∏ i, P' (s.2.1 i).val) * (1 / 2) ^ T

/-- A sum over tuples of length `n + 1` splits off the first coordinate. -/
lemma sum_pi_succ {α M : Type*} [Fintype α] [AddCommMonoid M] (n : ℕ)
    (g : (Fin (n + 1) → α) → M) :
    ∑ o, g o = ∑ y : α, ∑ o' : Fin n → α, g (Fin.cons y o') := by
  rw [← (Fin.consEquiv fun _ ↦ α).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The product law of the simulated increments is a law. -/
lemma sum_pi_prod_eq_one {P' : ℕ → ℝ} (hP'1 : ∑ b ∈ B, P' b = 1) :
    ∀ n : ℕ, ∑ o : Fin n → B, ∏ i, P' (o i).val = 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_pi_succ]
      have hB : ∑ y : B, P' y.val = 1 := by
        rw [← hP'1]
        exact Finset.sum_coe_sort B fun y ↦ P' y
      calc ∑ y : B, ∑ o' : Fin n → B, ∏ i, P' ((Fin.cons y o' : Fin (n + 1) → B) i).val
          = ∑ y : B, P' y.val * ∑ o' : Fin n → B, ∏ i, P' (o' i).val := by
            refine Finset.sum_congr rfl fun y _ ↦ ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun o' _ ↦ ?_
            rw [Fin.prod_univ_succ]
            simp
        _ = 1 := by rw [ih]; simpa using hB

/-- The fair bits form a law. -/
lemma sum_pi_half_eq_one (n : ℕ) : ∑ _β : Fin n → Bool, ((1 : ℝ) / 2) ^ n = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [← mul_pow]
  norm_num

lemma coinMass_nonneg {δ : ℝ} {P' : ℕ → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hP' : ∀ b ∈ B, 0 ≤ P' b) (s : MatchedCoin B T) : 0 ≤ coinMass δ P' s := by
  rw [coinMass]
  refine mul_nonneg (mul_nonneg ?_ ?_) (by positivity)
  · split_ifs <;> linarith
  · exact Finset.prod_nonneg fun i _ ↦ hP' _ (s.2.1 i).property

lemma sum_coinMass_eq_one {δ : ℝ} {P' : ℕ → ℝ} (hP'1 : ∑ b ∈ B, P' b = 1) :
    ∑ s : MatchedCoin B T, coinMass δ P' s = 1 := by
  have h1 : ∀ b : Bool, ∑ p : (Fin T → B) × (Fin T → Bool), coinMass δ P' (b, p)
      = if b then δ else 1 - δ := by
    intro b
    rw [Fintype.sum_prod_type]
    simp only [coinMass]
    calc ∑ o : Fin T → B, ∑ _β : Fin T → Bool,
          (if b then δ else 1 - δ) * (∏ i, P' (o i).val) * (1 / 2) ^ T
        = ∑ o : Fin T → B, (if b then δ else 1 - δ) * (∏ i, P' (o i).val)
            * ∑ _β : Fin T → Bool, ((1 : ℝ) / 2) ^ T := by
          refine Finset.sum_congr rfl fun o _ ↦ ?_
          rw [Finset.mul_sum]
      _ = (if b then δ else 1 - δ) * ∑ o : Fin T → B, ∏ i, P' (o i).val := by
          rw [sum_pi_half_eq_one, Finset.mul_sum]
          simp only [mul_one]
      _ = if b then δ else 1 - δ := by rw [sum_pi_prod_eq_one hP'1, mul_one]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, h1, h1]
  simp

/-- **The law of the coin**: the product of the branch law, the simulated
increments' law and the fair bits. -/
noncomputable def matchedCoinLaw {δ : ℝ} {P' : ℕ → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hP' : ∀ b ∈ B, 0 ≤ P' b) (hP'1 : ∑ b ∈ B, P' b = 1) : Measure (MatchedCoin B T) :=
  (PMF.ofFintype (fun s ↦ ENNReal.ofReal (coinMass δ P' s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun s _ ↦ coinMass_nonneg hδ0 hδ1 hP' s,
      sum_coinMass_eq_one hP'1, ENNReal.ofReal_one])).toMeasure

instance {δ : ℝ} {P' : ℕ → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hP' : ∀ b ∈ B, 0 ≤ P' b) (hP'1 : ∑ b ∈ B, P' b = 1) :
    IsProbabilityMeasure (matchedCoinLaw (B := B) (T := T) hδ0 hδ1 hP' hP'1) := by
  rw [matchedCoinLaw]
  infer_instance

lemma matchedCoinLaw_singleton {δ : ℝ} {P' : ℕ → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hP' : ∀ b ∈ B, 0 ≤ P' b) (hP'1 : ∑ b ∈ B, P' b = 1) (s : MatchedCoin B T) :
    matchedCoinLaw hδ0 hδ1 hP' hP'1 {s} = ENNReal.ofReal (coinMass δ P' s) := by
  rw [matchedCoinLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton s),
    PMF.ofFintype_apply]

/-- The decision of the coupled branch at root shift `x` against the increment
list `ys`: continue while the real total is at most `L`, differs from the
simulated total fast-forwarded to it, and the stopping bound is not reached. -/
def coupledDec (L T x : ℕ) (ys : List ℕ) (evs : List (Option ℕ)) : Bool :=
  decide (¬ L < rOf x evs ∧ rOf x evs ≠ ffwd (rOf x evs) 0 ys ∧ evs.length < T)

/-- The decision of the free branch at root shift `x` on the bits `β`: continue
while the real total is at most `L`, the stopping bound is not reached, and the
bit at the current decision says so. -/
def freeDec (L T x : ℕ) (β : Fin T → Bool) (evs : List (Option ℕ)) : Bool :=
  decide (¬ L < rOf x evs ∧ evs.length < T ∧ bitAt β evs.length = false)

/-- **The rule of `thm:matched-presentation` as a rule of `def:blob`**: the free
branch on the coin's branch bit, the coupled branch otherwise. -/
def matchedRule (B : Finset ℕ) (L T : ℕ) : BRule (MatchedCoin B T) where
  T := T
  decide := fun x evs s ↦ if s.1 then freeDec L T x s.2.2 evs else coupledDec L T x (oppList s) evs
  stop := by
    intro x evs s h
    simp only [freeDec, coupledDec]
    split_ifs <;> simp <;> omega

end Coin

/-! ### The list-driven automata

The coupled and the free automata of `MatchedPresentation` with their random
inputs made explicit: the simulated increments as a list consumed by the
lagging-side rule, the stopping coins as a list of bits.  Averaging the lists
against the product law recovers `couple` and `free`. -/

namespace Matched

open Finset

section Seq

variable (A : Finset ℕ) (P : ℕ → ℝ) (L : ℕ) (φ : ℝ)

/-- The coupled automaton driven by an explicit list of simulated increments. -/
noncomputable def coupleSeq : ℕ → ℕ → ℕ → ℕ → List ℕ → ℕ → ℝ
  | 0, _, _, _, _, _ => 0
  | F + 1, r, t, e, ys, s =>
      if L < r ∨ r = t then (if s = r then 1 else 0)
      else if e = 0 then (if s = r then 1 else 0)
      else if r < t then
        φ * coupleSeq F r t (e - 1) ys s
          + (1 - φ) * ∑ x ∈ A, P x * coupleSeq F (r + x) t (e + x) ys s
      else match ys with
        | [] => 0
        | y :: ys' => coupleSeq F r (t + y) e ys' s

/-- The free automaton driven by an explicit list of stopping bits. -/
noncomputable def freeSeq : ℕ → ℕ → ℕ → List Bool → ℕ → ℝ
  | 0, _, _, _, _ => 0
  | F + 1, r, e, bits, s =>
      if L < r then (if s = r then 1 else 0)
      else if e = 0 then (if s = r then 1 else 0)
      else match bits with
        | [] => 0
        | b :: bits' =>
            if b then (if s = r then 1 else 0)
            else φ * freeSeq F r (e - 1) bits' s
              + (1 - φ) * ∑ x ∈ A, P x * freeSeq F (r + x) (e + x) bits' s

variable {A P L φ}

lemma coupleSeq_stop {F r t e s : ℕ} (ys : List ℕ) (h : L < r ∨ r = t) :
    coupleSeq A P L φ (F + 1) r t e ys s = if s = r then 1 else 0 := by
  cases ys <;> rw [coupleSeq, if_pos h]

lemma coupleSeq_exh {F r t s : ℕ} (ys : List ℕ) :
    coupleSeq A P L φ (F + 1) r t 0 ys s = if s = r then 1 else 0 := by
  by_cases h : L < r ∨ r = t
  · cases ys <;> rw [coupleSeq, if_pos h]
  · cases ys <;> rw [coupleSeq, if_neg h, if_pos rfl]

lemma coupleSeq_left {F r t e s : ℕ} (ys : List ℕ) (h : ¬ (L < r ∨ r = t)) (he : ¬ e = 0)
    (hrt : r < t) :
    coupleSeq A P L φ (F + 1) r t e ys s
      = φ * coupleSeq A P L φ F r t (e - 1) ys s
        + (1 - φ) * ∑ x ∈ A, P x * coupleSeq A P L φ F (r + x) t (e + x) ys s := by
  cases ys <;> rw [coupleSeq, if_neg h, if_neg he, if_pos hrt]

lemma coupleSeq_right {F r t e s : ℕ} (y : ℕ) (ys : List ℕ) (h : ¬ (L < r ∨ r = t))
    (he : ¬ e = 0) (hrt : ¬ r < t) :
    coupleSeq A P L φ (F + 1) r t e (y :: ys) s = coupleSeq A P L φ F r (t + y) e ys s := by
  rw [coupleSeq, if_neg h, if_neg he, if_neg hrt]

lemma freeSeq_stop {F r e s : ℕ} (bits : List Bool) (h : L < r) :
    freeSeq A P L φ (F + 1) r e bits s = if s = r then 1 else 0 := by
  cases bits <;> rw [freeSeq, if_pos h]

lemma freeSeq_exh {F r s : ℕ} (bits : List Bool) :
    freeSeq A P L φ (F + 1) r 0 bits s = if s = r then 1 else 0 := by
  by_cases h : L < r
  · cases bits <;> rw [freeSeq, if_pos h]
  · cases bits <;> rw [freeSeq, if_neg h, if_pos rfl]

lemma freeSeq_cons_true {F r e s : ℕ} (bits : List Bool) (h : ¬ L < r) (he : ¬ e = 0) :
    freeSeq A P L φ (F + 1) r e (true :: bits) s = if s = r then 1 else 0 := by
  rw [freeSeq, if_neg h, if_neg he]
  rfl

lemma freeSeq_cons_false {F r e s : ℕ} (bits : List Bool) (h : ¬ L < r) (he : ¬ e = 0) :
    freeSeq A P L φ (F + 1) r e (false :: bits) s
      = φ * freeSeq A P L φ F r (e - 1) bits s
        + (1 - φ) * ∑ x ∈ A, P x * freeSeq A P L φ F (r + x) (e + x) bits s := by
  rw [freeSeq, if_neg h, if_neg he]
  rfl

lemma coupleSeq_nonneg (hP : ∀ a ∈ A, 0 ≤ P a) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ F r t e ys s, 0 ≤ coupleSeq A P L φ F r t e ys s := by
  intro F
  induction F with
  | zero => intro r t e ys s; simp [coupleSeq]
  | succ F ih =>
      intro r t e ys s
      have h1 : 0 ≤ 1 - φ := by linarith
      have h2 : 0 ≤ ∑ x ∈ A, P x * coupleSeq A P L φ F (r + x) t (e + x) ys s :=
        Finset.sum_nonneg fun x hx ↦ mul_nonneg (hP x hx) (ih _ _ _ _ _)
      have h3 := ih r t (e - 1) ys s
      cases ys with
      | nil =>
          rw [coupleSeq]
          split_ifs <;> positivity
      | cons y ys' =>
          rw [coupleSeq]
          split_ifs <;> first
            | positivity
            | exact ih _ _ _ _ _

lemma freeSeq_nonneg (hP : ∀ a ∈ A, 0 ≤ P a) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ F r e bits s, 0 ≤ freeSeq A P L φ F r e bits s := by
  intro F
  induction F with
  | zero => intro r e bits s; simp [freeSeq]
  | succ F ih =>
      intro r e bits s
      have h1 : 0 ≤ 1 - φ := by linarith
      cases bits with
      | nil =>
          rw [freeSeq]
          split_ifs <;> positivity
      | cons b bits' =>
          have h2 : 0 ≤ ∑ x ∈ A, P x * freeSeq A P L φ F (r + x) (e + x) bits' s :=
            Finset.sum_nonneg fun x hx ↦ mul_nonneg (hP x hx) (ih _ _ _ _)
          have h3 := ih r (e - 1) bits' s
          rw [freeSeq]
          split_ifs <;> positivity

/-- The algebra of one real step under a weighted average. -/
lemma sum_mul_step {ι : Type*} (s : Finset ι) (w : ι → ℝ) (φ : ℝ) (c₁ : ι → ℝ)
    (A : Finset ℕ) (P : ℕ → ℝ) (c : ℕ → ι → ℝ) :
    ∑ o ∈ s, w o * (φ * c₁ o + (1 - φ) * ∑ x ∈ A, P x * c x o)
      = φ * ∑ o ∈ s, w o * c₁ o
        + (1 - φ) * ∑ x ∈ A, P x * ∑ o ∈ s, w o * c x o := by
  calc ∑ o ∈ s, w o * (φ * c₁ o + (1 - φ) * ∑ x ∈ A, P x * c x o)
      = ∑ o ∈ s, (φ * (w o * c₁ o) + ∑ x ∈ A, (1 - φ) * (P x * (w o * c x o))) := by
        refine Finset.sum_congr rfl fun o _ ↦ ?_
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun x _ ↦ by ring
    _ = φ * ∑ o ∈ s, w o * c₁ o
        + ∑ x ∈ A, ∑ o ∈ s, (1 - φ) * (P x * (w o * c x o)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
    _ = φ * ∑ o ∈ s, w o * c₁ o
        + (1 - φ) * ∑ x ∈ A, P x * ∑ o ∈ s, w o * c x o := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [Finset.mul_sum, Finset.mul_sum]

variable {B : Finset ℕ} {P' : ℕ → ℝ}

/-- **Averaging the simulated increments** against their product law recovers the
coupled automaton, once the list is at least as long as the fuel. -/
lemma sum_coupleSeq_eq_couple (hP'1 : ∑ b ∈ B, P' b = 1) :
    ∀ (F n r t e s : ℕ), F ≤ n →
      ∑ o : Fin n → B, (∏ i, P' (o i).val)
          * coupleSeq A P L φ F r t e (List.ofFn fun i ↦ (o i).val) s
        = couple A B P P' L φ F r t e s := by
  intro F
  induction F with
  | zero => intro n r t e s _; simp [coupleSeq, couple]
  | succ F ih =>
      intro n r t e s hFn
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hconst : ∀ c : ℝ, ∑ o : Fin (n' + 1) → B, (∏ i, P' (o i).val) * c = c := by
        intro c
        rw [← Finset.sum_mul, sum_pi_prod_eq_one hP'1, one_mul]
      by_cases h : L < r ∨ r = t
      · simp only [coupleSeq_stop _ h, couple_stop h]
        exact hconst _
      · by_cases he : e = 0
        · subst he
          simp only [coupleSeq_exh, couple_exh h rfl]
          exact hconst _
        · by_cases hrt : r < t
          · simp only [coupleSeq_left _ h he hrt, couple_left h he hrt]
            rw [sum_mul_step, ih (n' + 1) r t (e - 1) s (by omega)]
            congr 2
            refine Finset.sum_congr rfl fun x _ ↦ ?_
            rw [ih (n' + 1) (r + x) t (e + x) s (by omega)]
          · rw [couple_right h he hrt, sum_pi_succ (α := B) (M := ℝ) n']
            rw [← Finset.sum_coe_sort B fun y ↦ P' y * couple A B P P' L φ F r (t + y) e s]
            refine Finset.sum_congr rfl fun y _ ↦ ?_
            rw [← ih n' r (t + y.val) e s (by omega), Finset.mul_sum]
            refine Finset.sum_congr rfl fun o' _ ↦ ?_
            rw [Fin.prod_univ_succ, List.ofFn_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [coupleSeq_right _ _ h he hrt, mul_assoc]

/-- **Averaging the stopping bits** against the fair law recovers the free
automaton, once the list is at least as long as the fuel. -/
lemma sum_freeSeq_eq_free :
    ∀ (F n r e s : ℕ), F ≤ n →
      ∑ β : Fin n → Bool, ((1 : ℝ) / 2) ^ n * freeSeq A P L φ F r e (List.ofFn β) s
        = free A P L φ F r e s := by
  intro F
  induction F with
  | zero => intro n r e s _; simp [freeSeq, free]
  | succ F ih =>
      intro n r e s hFn
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hconst : ∀ c : ℝ, ∑ _β : Fin (n' + 1) → Bool, ((1 : ℝ) / 2) ^ (n' + 1) * c = c := by
        intro c
        rw [← Finset.sum_mul, sum_pi_half_eq_one, one_mul]
      by_cases h : L < r
      · simp only [freeSeq_stop _ h, free_stop h]
        exact hconst _
      · by_cases he : e = 0
        · subst he
          simp only [freeSeq_exh, free_exh h rfl]
          exact hconst _
        · rw [free_step h he, sum_pi_succ (α := Bool) (M := ℝ) n', Fintype.sum_bool]
          have hsplit : ∀ b : Bool, ∑ β' : Fin n' → Bool,
              ((1 : ℝ) / 2) ^ (n' + 1)
                * freeSeq A P L φ (F + 1) r e (List.ofFn (Fin.cons b β')) s
              = (1 / 2) * ∑ β' : Fin n' → Bool,
                  ((1 : ℝ) / 2) ^ n' * freeSeq A P L φ (F + 1) r e (b :: List.ofFn β') s := by
            intro b
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun β' _ ↦ ?_
            rw [List.ofFn_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            ring
          rw [hsplit, hsplit]
          simp only [freeSeq_cons_true _ h he, freeSeq_cons_false _ h he]
          rw [← Finset.sum_mul, sum_pi_half_eq_one, one_mul, sum_mul_step,
            ih n' r (e - 1) s (by omega)]
          congr 4
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [ih n' (r + x) (e + x) s (by omega)]

/-- The coupled automaton from the root: the first simulated increment is drawn
and the walk continues from the pair of root totals. -/
lemma couple_root (hP'1 : ∑ b ∈ B, P' b = 1) {F x s : ℕ} (hF : 1 ≤ F) (hx : 1 ≤ x) :
    couple A B P P' L φ (F + 1) x 0 (x + 1) s
      = ∑ y ∈ B, P' y * couple A B P P' L φ F x y (x + 1) s := by
  obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  by_cases hL : L < x
  · rw [couple_stop (Or.inl hL)]
    rw [Finset.sum_congr rfl fun y _ ↦ by rw [couple_stop (F := F) (t := y) (e := x + 1)
      (s := s) (Or.inl hL)], ← Finset.sum_mul, hP'1, one_mul]
  · rw [couple_right (by omega) (by omega) (by omega)]
    simp only [zero_add]

end Seq

/-! ### The transcript automaton at a fixed coin

At a fixed coin the trace sum from an unstopped state with `n` exits is the
list-driven automaton from the transcript's totals: the real total `rOf x₀ evs`,
the simulated total read off the consumed prefix of the coin's increments, and
`n` unspent exits.  The fuel is taken large enough for the automaton to stop
on its own and the stopping bound large enough never to cut the transcript. -/

section Fixed

variable {A : Finset ℕ} {L : ℕ}

/-- The revealing-window mass against the split weight is the failure
complement against the reduced weight: `(1 - θ̃₁^R) ν̃_k`. -/
lemma hit_factor (θ : Offspring J) (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1)
    (R k : ℕ) :
    ENNReal.ofReal (θ.skeletonWeight k)
        * ∑ d ∈ Finset.range R, ENNReal.ofReal (θ.skeletonWeight 1) ^ d
      = ENNReal.ofReal (1 - θ.skeletonWeight 1 ^ R) * ENNReal.ofReal (reducedWeight θ k) := by
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  have hk0 : 0 ≤ θ.skeletonWeight k := θ.skeletonWeight_nonneg hq k
  have hne : θ.skeletonWeight 1 ≠ 1 := ne_of_lt hs1
  have hne' : θ.skeletonWeight 1 - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hne'' : (1 : ℝ) - θ.skeletonWeight 1 ≠ 0 := sub_ne_zero.mpr hne.symm
  have hgeom : ∑ d ∈ Finset.range R, ENNReal.ofReal (θ.skeletonWeight 1) ^ d
      = ENNReal.ofReal (∑ d ∈ Finset.range R, θ.skeletonWeight 1 ^ d) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun d _ ↦ pow_nonneg ha0 d]
    exact Finset.sum_congr rfl fun d _ ↦ (ENNReal.ofReal_pow ha0 d).symm
  have hpow : 0 ≤ 1 - θ.skeletonWeight 1 ^ R := by
    have := pow_le_one₀ ha0 hs1.le (n := R)
    linarith
  rw [hgeom, ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul hpow, geom_sum_eq hne,
    reducedWeight_def]
  congr 1
  field_simp
  ring

variable (θ : Offspring J) (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1) (R : ℕ)
  {MA : ℕ} (hA1 : ∀ x ∈ A, 1 ≤ x)
  (hAsupp : ∀ x, 1 ≤ x → θ.skeletonWeight (1 + x) ≠ 0 → x ∈ A) (hMA : ∀ a ∈ A, a ≤ MA)

include hq hs1 hA1 hAsupp hMA

omit hMA in
/-- The common shape of one real step: the stop-or-continue decomposition of
the trace sum against the automaton's step, given the two induction
hypotheses. -/
lemma ofReal_step {F m : ℕ} {evs : List (Option ℕ)} {dec : List (Option ℕ) → Bool}
    {f : Bool × List (Option ℕ) → ℝ≥0∞} {c₁ : ℝ} {c : ℕ → ℝ}
    (hc₁ : 0 ≤ c₁) (hc : ∀ x ∈ A, 0 ≤ c x)
    (hmiss : traceSum θ R dec (false, evs ++ [none]) m f = ENNReal.ofReal c₁)
    (hhit : ∀ x ∈ A, traceSum θ R dec (false, evs ++ [some x]) (x + 1 + m) f
      = ENNReal.ofReal (c x)) :
    ENNReal.ofReal (θ.skeletonWeight 1) ^ R * traceSum θ R dec (false, evs ++ [none]) m f
        + ∑ k ∈ Finset.range (J + 1), ENNReal.ofReal (θ.skeletonWeight k)
            * (if 2 ≤ k then
                (∑ d ∈ Finset.range R, ENNReal.ofReal (θ.skeletonWeight 1) ^ d)
                  * traceSum θ R dec (false, evs ++ [some (k - 1)]) (k + m) f
              else 0)
      = ENNReal.ofReal (θ.skeletonWeight 1 ^ R * c₁
          + (1 - θ.skeletonWeight 1 ^ R)
            * ∑ x ∈ A, reducedWeight θ (1 + x) * c x) := by
  have _ := F
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  have hφ0 : 0 ≤ θ.skeletonWeight 1 ^ R := pow_nonneg ha0 R
  have hφ1 : 0 ≤ 1 - θ.skeletonWeight 1 ^ R := by
    have := pow_le_one₀ ha0 hs1.le (n := R)
    linarith
  have hPnn : ∀ x, 0 ≤ reducedWeight θ (1 + x) := fun x ↦ by
    rw [reducedWeight_def]
    exact div_nonneg (θ.skeletonWeight_nonneg hq _) (by linarith)
  set G : ℝ≥0∞ := ∑ d ∈ Finset.range R, ENNReal.ofReal (θ.skeletonWeight 1) ^ d with hG
  have hconv : ∑ k ∈ Finset.range (J + 1), ENNReal.ofReal (θ.skeletonWeight k)
        * (if 2 ≤ k then G * traceSum θ R dec (false, evs ++ [some (k - 1)]) (k + m) f else 0)
      = ∑ x ∈ A, ENNReal.ofReal (θ.skeletonWeight (1 + x))
          * (G * traceSum θ R dec (false, evs ++ [some x]) (x + 1 + m) f) := by
    rw [← sum_arity_eq_sum_shift hA1 hAsupp
      (fun x ↦ G * traceSum θ R dec (false, evs ++ [some x]) (x + 1 + m) f)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : 2 ≤ k
    · rw [if_pos hk, if_pos hk, show k - 1 + 1 + m = k + m by omega]
    · rw [if_neg hk, if_neg hk]
  rw [hconv, hmiss, ENNReal.ofReal_add (mul_nonneg hφ0 hc₁)
    (mul_nonneg hφ1 (Finset.sum_nonneg fun x hx ↦ mul_nonneg (hPnn x) (hc x hx))),
    ENNReal.ofReal_mul hφ0, ENNReal.ofReal_mul hφ1, ENNReal.ofReal_pow ha0,
    ENNReal.ofReal_sum_of_nonneg fun x hx ↦ mul_nonneg (hPnn x) (hc x hx), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [hhit x hx, ← mul_assoc, hit_factor θ hq hs1, ENNReal.ofReal_mul (hPnn x), mul_assoc]

omit hq hs1 hA1 hAsupp hMA in
/-- The continuation at a stop. -/
lemma ofReal_ite_stop (j r : ℕ) :
    (if j = r then (1 : ℝ≥0∞) else 0) = ENNReal.ofReal (if j = r then 1 else 0) := by
  split_ifs <;> simp

/-- **The coupled branch at a fixed coin**: from an unstopped state whose
transcript has real total `r` and whose consumed simulated prefix has total `t`,
the trace sum is the list-driven coupled automaton on the remaining increments,
at sufficient fuel and stopping bound. -/
lemma traceSum_coupledDec {MB : ℕ} {B : Finset ℕ} (hB0 : ∀ b ∈ B, 0 < b)
    (hMB : ∀ b ∈ B, b ≤ MB) (T x₀ j : ℕ) (ysAll : List ℕ) (hys : ∀ y ∈ ysAll, y ∈ B) :
    ∀ (F : ℕ) (evs : List (Option ℕ)) (n : ℕ) (pre ys' : List ℕ), ysAll = pre ++ ys' →
      (∀ k, k < pre.length → (pre.take k).sum < rOf x₀ evs) →
      rOf x₀ evs ≤ L + MA → pre.sum ≤ L + MB →
      3 * L + 2 * MA + MB + 1 + n ≤ F + 2 * rOf x₀ evs + pre.sum →
      evs.length + F ≤ T → pre.length + F ≤ ysAll.length →
      traceSum θ R (coupledDec L T x₀ ysAll) (false, evs) n
          (fun st ↦ if j = rOf x₀ st.2 then 1 else 0)
        = ENNReal.ofReal (coupleSeq A (fun x ↦ reducedWeight θ (1 + x)) L
            (θ.skeletonWeight 1 ^ R) F (rOf x₀ evs) pre.sum n ys' j) := by
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  have hφ0 : 0 ≤ θ.skeletonWeight 1 ^ R := pow_nonneg ha0 R
  have hφ1 : θ.skeletonWeight 1 ^ R ≤ 1 := pow_le_one₀ ha0 hs1.le
  have hPnn : ∀ x ∈ A, 0 ≤ reducedWeight θ (1 + x) := fun x _ ↦ by
    rw [reducedWeight_def]
    exact div_nonneg (θ.skeletonWeight_nonneg hq _) (by linarith)
  have hnn := coupleSeq_nonneg (A := A) (L := L) hPnn hφ0 hφ1
  intro F
  induction F with
  | zero => intro evs n pre ys' _ _ hr ht hF _ _; omega
  | succ F ih =>
      intro evs n pre ys' hall hpre hr ht hF hT hlen
      have hffwd : ffwd (rOf x₀ evs) 0 ysAll = ffwd (rOf x₀ evs) pre.sum ys' := by
        rw [hall, ffwd_append _ pre ys' 0 (by simpa using hpre), Nat.zero_add]
      rcases n with _ | m
      · rw [traceSum_zero, coupleSeq_exh]
        exact ofReal_ite_stop j _
      · by_cases hstop : L < rOf x₀ evs ∨ rOf x₀ evs = pre.sum
        · have hdec : coupledDec L T x₀ ysAll evs = false := by
            rw [coupledDec, decide_eq_false_iff_not]
            rintro ⟨h1, h2, -⟩
            rcases hstop with h | h
            · exact h1 h
            · rw [hffwd, ffwd_of_le h.le] at h2
              exact h2 h
          rw [traceSum_succ_decomp, if_pos hdec, coupleSeq_stop _ hstop]
          exact ofReal_ite_stop j _
        · by_cases hrt : rOf x₀ evs < pre.sum
          · have hdec : coupledDec L T x₀ ysAll evs = true := by
              rw [coupledDec, decide_eq_true_iff]
              refine ⟨fun h ↦ hstop (Or.inl h), ?_, by omega⟩
              rw [hffwd, ffwd_of_le hrt.le]
              omega
            rw [traceSum_succ_decomp, if_neg (by simp [hdec]),
              coupleSeq_left _ hstop (Nat.succ_ne_zero m) hrt]
            refine ofReal_step θ hq hs1 R hA1 hAsupp (F := F) (hnn _ _ _ _ _ _)
              (fun x _ ↦ hnn _ _ _ _ _ _) ?_ ?_
            · have := ih (evs ++ [none]) m pre ys' hall (by simpa using hpre)
                (by simpa using hr) ht (by simp only [rOf_append_none]; omega)
                (by simp only [List.length_append, List.length_singleton]; omega) (by omega)
              simpa only [rOf_append_none, Nat.succ_sub_one] using this
            · intro x hx
              have hx1 := hA1 x hx
              have hxM := hMA x hx
              have := ih (evs ++ [some x]) (x + 1 + m) pre ys' hall
                (fun k hk ↦ by rw [rOf_append_some]; have := hpre k hk; omega)
                (by rw [rOf_append_some]; omega) ht
                (by rw [rOf_append_some]; omega)
                (by simp only [List.length_append, List.length_singleton]; omega) (by omega)
              rw [this, rOf_append_some, show x + 1 + m = m + 1 + x by omega]
          · have htr : pre.sum < rOf x₀ evs := by omega
            obtain ⟨y, ys'', rfl⟩ : ∃ y ys'', ys' = y :: ys'' := by
              cases ys' with
              | nil =>
                  exfalso
                  have := congrArg List.length hall
                  simp at this
                  omega
              | cons y ys'' => exact ⟨y, ys'', rfl⟩
            rw [coupleSeq_right _ _ hstop (Nat.succ_ne_zero m) hrt]
            have hyB : y ∈ B := hys y (by rw [hall]; simp)
            have hy1 := hB0 y hyB
            have hyM := hMB y hyB
            have hrL : rOf x₀ evs ≤ L := by omega
            have := ih evs (m + 1) (pre ++ [y]) ys'' (by rw [hall, List.append_assoc]; rfl)
              ?_ hr ?_ ?_ (by omega) ?_
            · simpa only [List.sum_append, List.sum_singleton] using this
            · intro k hk
              simp only [List.length_append, List.length_singleton] at hk
              rcases Nat.lt_or_ge k pre.length with hk' | hk'
              · rw [List.take_append_of_le_length hk'.le]
                exact hpre k hk'
              · have hkeq : k = pre.length := by omega
                rw [hkeq, List.take_append_of_le_length le_rfl, List.take_length]
                exact htr
            · simp only [List.sum_append, List.sum_singleton]
              omega
            · simp only [List.sum_append, List.sum_singleton]
              omega
            · simp only [List.length_append, List.length_singleton]
              omega

/-- **The free branch at a fixed coin**: from an unstopped state whose transcript
has real total `r`, the trace sum is the list-driven free automaton on the
remaining bits, at sufficient fuel and stopping bound. -/
lemma traceSum_freeDec (T x₀ j : ℕ) (β : Fin T → Bool) :
    ∀ (F : ℕ) (evs : List (Option ℕ)) (n : ℕ),
      rOf x₀ evs ≤ L + MA → 2 * L + 2 * MA + 1 + n ≤ F + 2 * rOf x₀ evs →
      evs.length + F ≤ T →
      traceSum θ R (freeDec L T x₀ β) (false, evs) n
          (fun st ↦ if j = rOf x₀ st.2 then 1 else 0)
        = ENNReal.ofReal (freeSeq A (fun x ↦ reducedWeight θ (1 + x)) L
            (θ.skeletonWeight 1 ^ R) F (rOf x₀ evs) n ((List.ofFn β).drop evs.length) j) := by
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  have hφ0 : 0 ≤ θ.skeletonWeight 1 ^ R := pow_nonneg ha0 R
  have hφ1 : θ.skeletonWeight 1 ^ R ≤ 1 := pow_le_one₀ ha0 hs1.le
  have hPnn : ∀ x ∈ A, 0 ≤ reducedWeight θ (1 + x) := fun x _ ↦ by
    rw [reducedWeight_def]
    exact div_nonneg (θ.skeletonWeight_nonneg hq _) (by linarith)
  have hnn := freeSeq_nonneg (A := A) (L := L) hPnn hφ0 hφ1
  intro F
  induction F with
  | zero => intro evs n hr hF _; omega
  | succ F ih =>
      intro evs n hr hF hT
      rcases n with _ | m
      · rw [traceSum_zero, freeSeq_exh]
        exact ofReal_ite_stop j _
      · by_cases hL : L < rOf x₀ evs
        · have hdec : freeDec L T x₀ β evs = false := by
            rw [freeDec, decide_eq_false_iff_not]
            rintro ⟨h1, -⟩
            exact h1 hL
          rw [traceSum_succ_decomp, if_pos hdec, freeSeq_stop _ hL]
          exact ofReal_ite_stop j _
        · have hlt : evs.length < T := by omega
          have hdrop : (List.ofFn β).drop evs.length
              = bitAt β evs.length :: (List.ofFn β).drop (evs.length + 1) := by
            rw [List.drop_eq_getElem_cons (by simpa using hlt), List.getElem_ofFn, bitAt,
              dif_pos hlt]
          rw [hdrop]
          cases hb : bitAt β evs.length with
          | true =>
              have hdec : freeDec L T x₀ β evs = false := by
                rw [freeDec, decide_eq_false_iff_not]
                rintro ⟨-, -, h⟩
                rw [hb] at h
                exact absurd h (by simp)
              rw [traceSum_succ_decomp, if_pos hdec, freeSeq_cons_true _ hL (Nat.succ_ne_zero m)]
              exact ofReal_ite_stop j _
          | false =>
              have hdec : freeDec L T x₀ β evs = true := by
                rw [freeDec, decide_eq_true_iff]
                exact ⟨hL, hlt, hb⟩
              rw [traceSum_succ_decomp, if_neg (by simp [hdec]),
                freeSeq_cons_false _ hL (Nat.succ_ne_zero m)]
              refine ofReal_step θ hq hs1 R hA1 hAsupp (F := F) (hnn _ _ _ _ _)
                (fun x _ ↦ hnn _ _ _ _ _) ?_ ?_
              · have := ih (evs ++ [none]) m (by simpa using hr)
                  (by simp only [rOf_append_none]; omega)
                  (by simp only [List.length_append, List.length_singleton]; omega)
                simpa only [rOf_append_none, List.length_append, List.length_singleton,
                  Nat.succ_sub_one] using this
              · intro x hx
                have hx1 := hA1 x hx
                have hxM := hMA x hx
                have := ih (evs ++ [some x]) (x + 1 + m) (by rw [rOf_append_some]; omega)
                  (by rw [rOf_append_some]; omega)
                  (by simp only [List.length_append, List.length_singleton]; omega)
                rw [this, rOf_append_some, show x + 1 + m = m + 1 + x by omega]
                simp only [List.length_append, List.length_singleton]

end Fixed

/-! ### The identification -/

section Identify

variable {A B : Finset ℕ} {L : ℕ}

/-- The presented law against the split weights: `(1 - θ̃₁) matchedShift` as the
sum over the root shift of the split weight against the two branches. -/
lemma matchedShift_expand (θ : Offspring J) (hs1 : θ.skeletonWeight 1 < 1) {P' : ℕ → ℝ}
    {φ δ : ℝ} (F j : ℕ) :
    (1 - θ.skeletonWeight 1)
        * matchedShift A B (fun x ↦ reducedWeight θ (1 + x)) P' L φ δ F j
      = ∑ x ∈ A, θ.skeletonWeight (1 + x)
          * (δ * free A (fun x ↦ reducedWeight θ (1 + x)) L φ F x (x + 1) j
            + (1 - δ) * ∑ y ∈ B, P' y
                * couple A B (fun x ↦ reducedWeight θ (1 + x)) P' L φ F x y (x + 1) j) := by
  have hne : (1 : ℝ) - θ.skeletonWeight 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hs1).symm
  have hPx : ∀ x, θ.skeletonWeight (1 + x)
      = (1 - θ.skeletonWeight 1) * reducedWeight θ (1 + x) := fun x ↦ by
    rw [reducedWeight_def, mul_div_cancel₀ _ hne]
  have hcl : coupleLaw A B (fun x ↦ reducedWeight θ (1 + x)) P' L φ F j
      = ∑ x ∈ A, reducedWeight θ (1 + x) * ∑ y ∈ B, P' y
          * couple A B (fun x ↦ reducedWeight θ (1 + x)) P' L φ F x y (x + 1) j := by
    rw [coupleLaw]
    exact Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum ..).symm
  rw [matchedShift, freeLaw, hcl, Finset.mul_sum, Finset.mul_sum, mul_add, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [hPx x]
  ring

/-- The decision of the matched rule on a free coin is the free decision. -/
lemma matchedRule_decide_free (T x : ℕ) (o : Fin T → B) (β : Fin T → Bool) :
    (fun evs ↦ (matchedRule B L T).decide x evs (true, o, β)) = freeDec L T x β := by
  funext evs
  simp [matchedRule]

/-- The decision of the matched rule on a coupled coin is the coupled decision
against the coin's increments. -/
lemma matchedRule_decide_coupled (T x : ℕ) (o : Fin T → B) (β : Fin T → Bool) :
    (fun evs ↦ (matchedRule B L T).decide x evs (false, o, β))
      = coupledDec L T x (List.ofFn fun i ↦ (o i).val) := by
  funext evs
  simp [matchedRule, oppList]

/-- **The identification**: the coin-averaged rule mass of the matched rule at
the presented arity `1 + j` is the presented shift law `matchedShift j` against
the neck factor `1 - θ̃₁`, at fuel in the stable range and stopping bound past
the fuel. -/
theorem coinRuleMass_matchedRule (θ : Offspring J) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) (R : ℕ) {MA MB : ℕ} (hA1 : ∀ x ∈ A, 1 ≤ x)
    (hAsupp : ∀ x, 1 ≤ x → θ.skeletonWeight (1 + x) ≠ 0 → x ∈ A) (hMA : ∀ a ∈ A, a ≤ MA)
    (hB0 : ∀ b ∈ B, 0 < b) (hMB : ∀ b ∈ B, b ≤ MB) {P' : ℕ → ℝ} (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP'1 : ∑ b ∈ B, P' b = 1) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {F T : ℕ}
    (hF : 3 * L + 2 * MA + MB + 2 ≤ F) (hF' : 2 * L + 2 * MA + 2 ≤ F) (hT : F + 1 ≤ T)
    (j : ℕ) :
    ∑ s : MatchedCoin B T, matchedCoinLaw hδ0 hδ1 hP' hP'1 {s}
        * bRuleMass θ R (matchedRule B L T) s (1 + j)
      = ENNReal.ofReal ((1 - θ.skeletonWeight 1)
          * matchedShift A B (fun x ↦ reducedWeight θ (1 + x)) P' L
              (θ.skeletonWeight 1 ^ R) δ F j) := by
  classical
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  have hφ0 : 0 ≤ θ.skeletonWeight 1 ^ R := pow_nonneg ha0 R
  have hφ1 : θ.skeletonWeight 1 ^ R ≤ 1 := pow_le_one₀ ha0 hs1.le
  have hPnn : ∀ x ∈ A, 0 ≤ reducedWeight θ (1 + x) := fun x _ ↦ by
    rw [reducedWeight_def]
    exact div_nonneg (θ.skeletonWeight_nonneg hq _) (by linarith)
  set P : ℕ → ℝ := fun x ↦ reducedWeight θ (1 + x) with hP
  set φ : ℝ := θ.skeletonWeight 1 ^ R with hφ
  -- the rule mass at a coin as a sum over the root shift
  have hinner : ∀ s : MatchedCoin B T,
      bRuleMass θ R (matchedRule B L T) s (1 + j)
        = ∑ x ∈ A, ENNReal.ofReal (θ.skeletonWeight (1 + x))
            * traceSum θ R (fun evs ↦ (matchedRule B L T).decide x evs s) (false, []) (x + 1)
                (fun st ↦ if j = rOf x st.2 then 1 else 0) := by
    intro s
    rw [bRuleMass_eq_sum_traceSum, ← sum_arity_eq_sum_shift hA1 hAsupp
      (fun x ↦ traceSum θ R (fun evs ↦ (matchedRule B L T).decide x evs s) (false, []) (x + 1)
        (fun st ↦ if j = rOf x st.2 then 1 else 0))]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    by_cases hn : 2 ≤ n
    · rw [if_pos hn, if_pos hn, show n - 1 + 1 = n by omega]
    · rw [if_neg hn, if_neg hn]
  -- the coin average at a fixed root shift
  have hcoin : ∀ x ∈ A,
      ∑ s : MatchedCoin B T, ENNReal.ofReal (coinMass δ P' s)
          * traceSum θ R (fun evs ↦ (matchedRule B L T).decide x evs s) (false, []) (x + 1)
              (fun st ↦ if j = rOf x st.2 then 1 else 0)
        = ENNReal.ofReal (δ * free A P L φ F x (x + 1) j
            + (1 - δ) * ∑ y ∈ B, P' y * couple A B P P' L φ F x y (x + 1) j) := by
    intro x hx
    have hx1 := hA1 x hx
    have hxM := hMA x hx
    have hfree : ∀ (o : Fin T → B) (β : Fin T → Bool),
        traceSum θ R (fun evs ↦ (matchedRule B L T).decide x evs (true, o, β)) (false, [])
            (x + 1) (fun st ↦ if j = rOf x st.2 then 1 else 0)
          = ENNReal.ofReal (freeSeq A P L φ F x (x + 1) (List.ofFn β) j) := by
      intro o β
      rw [matchedRule_decide_free]
      have := traceSum_freeDec (A := A) (L := L) θ hq hs1 R hA1 hAsupp hMA T x j β F []
        (x + 1) (by simp; omega) (by simp; omega) (by simp; omega)
      simpa using this
    have hcouple : ∀ (o : Fin T → B) (β : Fin T → Bool),
        traceSum θ R (fun evs ↦ (matchedRule B L T).decide x evs (false, o, β)) (false, [])
            (x + 1) (fun st ↦ if j = rOf x st.2 then 1 else 0)
          = ENNReal.ofReal (coupleSeq A P L φ (F + 1) x 0 (x + 1)
              (List.ofFn fun i ↦ (o i).val) j) := by
      intro o β
      rw [matchedRule_decide_coupled]
      have := traceSum_coupledDec (A := A) (L := L) θ hq hs1 R hA1 hAsupp hMA hB0 hMB T x j
        (List.ofFn fun i ↦ (o i).val) (fun y hy ↦ by
          rw [List.mem_ofFn] at hy
          obtain ⟨i, rfl⟩ := hy
          exact (o i).property)
        (F + 1) [] (x + 1) [] (List.ofFn fun i ↦ (o i).val) (by simp)
        (fun k hk ↦ by simp at hk) (by simp; omega) (by simp) (by simp; omega)
        (by simp; omega) (by simp; omega)
      simpa using this
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [coinMass, if_true, Bool.false_eq_true, if_false]
    simp only [hfree, hcouple]
    have hhalf : ∑ _β : Fin T → Bool, ENNReal.ofReal (((1 : ℝ) / 2) ^ T) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity, sum_pi_half_eq_one,
        ENNReal.ofReal_one]
    have hprod : ∑ o : Fin T → B, ENNReal.ofReal (∏ i, P' (o i).val) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg fun o _ ↦
        Finset.prod_nonneg fun i _ ↦ hP' _ (o i).property, sum_pi_prod_eq_one hP'1,
        ENNReal.ofReal_one]
    have hfreeS : ∑ o : Fin T → B, ∑ β : Fin T → Bool,
        ENNReal.ofReal (δ * (∏ i, P' (o i).val) * (1 / 2) ^ T)
          * ENNReal.ofReal (freeSeq A P L φ F x (x + 1) (List.ofFn β) j)
        = ENNReal.ofReal (δ * free A P L φ F x (x + 1) j) := by
      have hfnn := freeSeq_nonneg (A := A) (L := L) hPnn hφ0 hφ1
      calc ∑ o : Fin T → B, ∑ β : Fin T → Bool,
            ENNReal.ofReal (δ * (∏ i, P' (o i).val) * (1 / 2) ^ T)
              * ENNReal.ofReal (freeSeq A P L φ F x (x + 1) (List.ofFn β) j)
          = ∑ o : Fin T → B, ENNReal.ofReal (∏ i, P' (o i).val)
              * (ENNReal.ofReal δ * ∑ β : Fin T → Bool,
                  ENNReal.ofReal ((1 / 2) ^ T * freeSeq A P L φ F x (x + 1) (List.ofFn β) j)) := by
            refine Finset.sum_congr rfl fun o _ ↦ ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun β _ ↦ ?_
            have hpr : 0 ≤ ∏ i, P' (o i).val :=
              Finset.prod_nonneg fun i _ ↦ hP' _ (o i).property
            rw [ENNReal.ofReal_mul (show 0 ≤ δ * ∏ i, P' (o i).val from mul_nonneg hδ0 hpr),
              ENNReal.ofReal_mul hδ0,
              ENNReal.ofReal_mul (show 0 ≤ ((1 : ℝ) / 2) ^ T by positivity)]
            ring
        _ = ENNReal.ofReal (δ * free A P L φ F x (x + 1) j) := by
            rw [← Finset.sum_mul, hprod, one_mul,
              ← ENNReal.ofReal_sum_of_nonneg fun β _ ↦ mul_nonneg (by positivity) (hfnn _ _ _ _ _),
              sum_freeSeq_eq_free F T x (x + 1) j (by omega), ENNReal.ofReal_mul hδ0]
    have hcoupleS : ∑ o : Fin T → B, ∑ _β : Fin T → Bool,
        ENNReal.ofReal ((1 - δ) * (∏ i, P' (o i).val) * (1 / 2) ^ T)
          * ENNReal.ofReal (coupleSeq A P L φ (F + 1) x 0 (x + 1)
              (List.ofFn fun i ↦ (o i).val) j)
        = ENNReal.ofReal ((1 - δ) * ∑ y ∈ B, P' y * couple A B P P' L φ F x y (x + 1) j) := by
      have hcnn := coupleSeq_nonneg (A := A) (L := L) hPnn hφ0 hφ1
      have hδ1' : 0 ≤ 1 - δ := by linarith
      calc ∑ o : Fin T → B, ∑ _β : Fin T → Bool,
            ENNReal.ofReal ((1 - δ) * (∏ i, P' (o i).val) * (1 / 2) ^ T)
              * ENNReal.ofReal (coupleSeq A P L φ (F + 1) x 0 (x + 1)
                  (List.ofFn fun i ↦ (o i).val) j)
          = ∑ o : Fin T → B, ENNReal.ofReal (1 - δ)
              * ENNReal.ofReal ((∏ i, P' (o i).val) * coupleSeq A P L φ (F + 1) x 0 (x + 1)
                  (List.ofFn fun i ↦ (o i).val) j)
              * ∑ _β : Fin T → Bool, ENNReal.ofReal (((1 : ℝ) / 2) ^ T) := by
            refine Finset.sum_congr rfl fun o _ ↦ ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun β _ ↦ ?_
            have hpr : 0 ≤ ∏ i, P' (o i).val :=
              Finset.prod_nonneg fun i _ ↦ hP' _ (o i).property
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hδ1',
              ENNReal.ofReal_mul hpr]
            ring
        _ = ENNReal.ofReal ((1 - δ) * ∑ y ∈ B, P' y * couple A B P P' L φ F x y (x + 1) j) := by
            simp only [hhalf, mul_one]
            rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg fun o _ ↦
              mul_nonneg (Finset.prod_nonneg fun i _ ↦ hP' _ (o i).property) (hcnn _ _ _ _ _ _),
              sum_coupleSeq_eq_couple hP'1 (F + 1) T x 0 (x + 1) j hT,
              couple_root hP'1 (by omega) hx1, ← ENNReal.ofReal_mul hδ1']
    rw [hfreeS, hcoupleS, ← ENNReal.ofReal_add (mul_nonneg hδ0 (free_nonneg hPnn hφ0 hφ1 _ _ _ _))
      (mul_nonneg (by linarith) (Finset.sum_nonneg fun y hy ↦
        mul_nonneg (hP' y hy) (couple_nonneg hPnn hP' hφ0 hφ1 _ _ _ _ _)))]
  -- assemble
  simp only [matchedCoinLaw_singleton, hinner]
  rw [matchedShift_expand θ hs1, ENNReal.ofReal_sum_of_nonneg fun x hx ↦
    mul_nonneg (θ.skeletonWeight_nonneg hq _) (add_nonneg
      (mul_nonneg hδ0 (free_nonneg hPnn hφ0 hφ1 _ _ _ _))
      (mul_nonneg (by linarith) (Finset.sum_nonneg fun y hy ↦
        mul_nonneg (hP' y hy) (couple_nonneg hPnn hP' hφ0 hφ1 _ _ _ _ _))))]
  calc ∑ s : MatchedCoin B T, ENNReal.ofReal (coinMass δ P' s)
        * ∑ x ∈ A, ENNReal.ofReal (θ.skeletonWeight (1 + x))
            * traceSum θ R (fun evs ↦ (matchedRule B L T).decide x evs s) (false, []) (x + 1)
                (fun st ↦ if j = rOf x st.2 then 1 else 0)
      = ∑ x ∈ A, ENNReal.ofReal (θ.skeletonWeight (1 + x))
          * ∑ s : MatchedCoin B T, ENNReal.ofReal (coinMass δ P' s)
            * traceSum θ R (fun evs ↦ (matchedRule B L T).decide x evs s) (false, []) (x + 1)
                (fun st ↦ if j = rOf x st.2 then 1 else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
        ring
    _ = ∑ x ∈ A, ENNReal.ofReal (θ.skeletonWeight (1 + x)
          * (δ * free A P L φ F x (x + 1) j
            + (1 - δ) * ∑ y ∈ B, P' y * couple A B P P' L φ F x y (x + 1) j)) := by
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        rw [hcoin x hx, ENNReal.ofReal_mul (θ.skeletonWeight_nonneg hq _)]

/-- The shifted reduced law is a law on the shifted support. -/
lemma sum_reducedWeight_shift (θ : Offspring J) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) (hA1 : ∀ x ∈ A, 1 ≤ x)
    (hAsupp : ∀ x, 1 ≤ x → θ.skeletonWeight (1 + x) ≠ 0 → x ∈ A) :
    ∑ x ∈ A, reducedWeight θ (1 + x) = 1 := by
  classical
  have hne : (1 : ℝ) - θ.skeletonWeight 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hs1).symm
  have hnn : ∀ k, 0 ≤ θ.skeletonWeight k := θ.skeletonWeight_nonneg hq
  -- the shifted sum in `ℝ≥0∞`, through the reindexing
  have hre := sum_arity_eq_sum_shift (θ := θ) hA1 hAsupp fun _ ↦ (1 : ℝ≥0∞)
  simp only [mul_one] at hre
  have hL : ∑ k ∈ Finset.range (J + 1), ENNReal.ofReal (θ.skeletonWeight k)
        * (if 2 ≤ k then (1 : ℝ≥0∞) else 0)
      = ENNReal.ofReal (∑ k ∈ Finset.range (J + 1),
          θ.skeletonWeight k * (if 2 ≤ k then 1 else 0)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ ↦ mul_nonneg (hnn k) (by split_ifs <;> norm_num)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [ENNReal.ofReal_mul (hnn k)]
    congr 1
    split_ifs <;> simp
  rw [hL, ← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hnn _] at hre
  have hreal : ∑ k ∈ Finset.range (J + 1), θ.skeletonWeight k * (if 2 ≤ k then 1 else 0)
      = ∑ x ∈ A, θ.skeletonWeight (1 + x) :=
    (ENNReal.ofReal_eq_ofReal_iff
      (Finset.sum_nonneg fun k _ ↦ mul_nonneg (hnn k) (by split_ifs <;> norm_num))
      (Finset.sum_nonneg fun x _ ↦ hnn _)).mp hre
  -- the arities at most one carry `θ̃₁`
  have hlow : ∑ k ∈ Finset.range (J + 1), θ.skeletonWeight k * (if k < 2 then 1 else 0)
      = θ.skeletonWeight 1 := by
    have h1 : ∑ k ∈ Finset.range (J + 1), θ.skeletonWeight k * (if k < 2 then 1 else 0)
        = ∑ k ∈ Finset.range (J + 2), θ.skeletonWeight k * (if k < 2 then 1 else 0) := by
      refine Finset.sum_subset (Finset.range_mono (by omega : J + 1 ≤ J + 2))
        fun k hk hk' ↦ ?_
      rw [Finset.mem_range] at hk hk'
      have hkJ : k = J + 1 := by omega
      rw [θ.skeletonWeight_vanishing (by omega), zero_mul]
    have h2 : ∑ k ∈ Finset.range 2, θ.skeletonWeight k * (if k < 2 then 1 else 0)
        = ∑ k ∈ Finset.range (J + 2), θ.skeletonWeight k * (if k < 2 then 1 else 0) := by
      refine Finset.sum_subset (Finset.range_mono (by omega : 2 ≤ J + 2))
        fun k hk hk' ↦ ?_
      rw [Finset.mem_range] at hk'
      rw [if_neg (by omega), mul_zero]
    rw [h1, ← h2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      θ.skeletonWeight_zero]
    simp
  have htot : ∑ k ∈ Finset.range (J + 1), θ.skeletonWeight k
      = ∑ k ∈ Finset.range (J + 1), θ.skeletonWeight k * (if 2 ≤ k then 1 else 0)
        + ∑ k ∈ Finset.range (J + 1), θ.skeletonWeight k * (if k < 2 then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : 2 ≤ k
    · rw [if_pos hk, if_neg (by omega)]; ring
    · rw [if_neg hk, if_pos (by omega)]; ring
  rw [θ.sum_skeletonWeight hq, hreal, hlow] at htot
  simp only [reducedWeight_def]
  rw [← Finset.sum_div, div_eq_one_iff_eq hne]
  linarith

/-- **The identification, normalised**: the coin-averaged rule mass at arity
`1 + j` over the neck factor is `matchedShift j`, the form of the presented arity
law `ν̂` of `thm:blob-law`. -/
theorem coinRuleMass_div_matchedRule (θ : Offspring J) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) (R : ℕ) {MA MB : ℕ} (hA1 : ∀ x ∈ A, 1 ≤ x)
    (hAsupp : ∀ x, 1 ≤ x → θ.skeletonWeight (1 + x) ≠ 0 → x ∈ A) (hMA : ∀ a ∈ A, a ≤ MA)
    (hB0 : ∀ b ∈ B, 0 < b) (hMB : ∀ b ∈ B, b ≤ MB) {P' : ℕ → ℝ} (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP'1 : ∑ b ∈ B, P' b = 1) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {F T : ℕ}
    (hF : 3 * L + 2 * MA + MB + 2 ≤ F) (hF' : 2 * L + 2 * MA + 2 ≤ F) (hT : F + 1 ≤ T)
    (j : ℕ) :
    (∑ s : MatchedCoin B T, matchedCoinLaw hδ0 hδ1 hP' hP'1 {s}
        * bRuleMass θ R (matchedRule B L T) s (1 + j))
        / ENNReal.ofReal (1 - θ.skeletonWeight 1)
      = ENNReal.ofReal (matchedShift A B (fun x ↦ reducedWeight θ (1 + x)) P' L
          (θ.skeletonWeight 1 ^ R) δ F j) := by
  have hpos : 0 < 1 - θ.skeletonWeight 1 := by linarith
  rw [coinRuleMass_matchedRule θ hq hs1 R hA1 hAsupp hMA hB0 hMB hP' hP'1 hδ0 hδ1 hF hF' hT j,
    ENNReal.ofReal_mul hpos.le, mul_comm,
    ENNReal.mul_div_cancel_right (by simpa using hpos) ENNReal.ofReal_ne_top]

end Identify

/-! ### `thm:matched-presentation` on the constructed space -/

section Presented

variable {A B : Finset ℕ}

/-- **`thm:matched-presentation` (`it:matched-product`)**: over the sample
against the coin field, the presented pairs of neck length and shift of the
matched blob presentation are i.i.d. over every prefix-closed compatible probe,
the neck geometric with ratio `θ̃₁` and the presented shift carrying
`matchedShift`. -/
theorem matched_iid (θ : Offspring J) (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) (R : ℕ) {MA MB : ℕ} (hA1 : ∀ x ∈ A, 1 ≤ x)
    (hAsupp : ∀ x, 1 ≤ x → θ.skeletonWeight (1 + x) ≠ 0 → x ∈ A) (hMA : ∀ a ∈ A, a ≤ MA)
    (hB : B.Nonempty) (hB0 : ∀ b ∈ B, 0 < b) (hMB : ∀ b ∈ B, b ≤ MB) {P' : ℕ → ℝ}
    (hP' : ∀ b ∈ B, 0 ≤ P' b) (hP'1 : ∑ b ∈ B, P' b = 1) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {L F T : ℕ} (hF : 3 * L + 2 * MA + MB + 2 ≤ F) (hF' : 2 * L + 2 * MA + 2 ≤ F)
    (hT : F + 1 ≤ T) (Fs : Finset (List ℕ))
    (hpc : ∀ u ∈ Fs, ∀ p : List ℕ, p <+: u → p ∈ Fs) (r j : List ℕ → ℕ)
    (hcomp : ∀ u ∈ Fs, ∀ i : ℕ, u ++ [i] ∈ Fs → i < 1 + j u) :
    blobMeasure (N := N) θ (matchedCoinLaw hδ0 hδ1 hP' hP'1)
        (⋂ u ∈ Fs, ({ω : (GWord N → ℕ) × (List ℕ → MatchedCoin B T) |
            bNeckAtC R (matchedRule B L T) ω u = r u}
          ∩ {ω : (GWord N → ℕ) × (List ℕ → MatchedCoin B T) |
            bArityAtC R (matchedRule B L T) ω u = 1 + j u}))
      = ∏ u ∈ Fs, ENNReal.ofReal (θ.skeletonWeight 1 ^ (r u)
          * ((1 - θ.skeletonWeight 1)
            * matchedShift A B (fun x ↦ reducedWeight θ (1 + x)) P' L
                (θ.skeletonWeight 1 ^ R) δ F (j u))) := by
  haveI : Inhabited B := ⟨⟨hB.choose, hB.choose_spec⟩⟩
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  refine (blob_iid θ hJN hq hs1 (matchedCoinLaw hδ0 hδ1 hP' hP'1) R (matchedRule B L T) Fs
    hpc r (fun u ↦ 1 + j u) hcomp).trans ?_
  refine Finset.prod_congr rfl fun u _ ↦ ?_
  rw [coinRuleMass_matchedRule θ hq hs1 R hA1 hAsupp hMA hB0 hMB hP' hP'1 hδ0 hδ1 hF hF' hT,
    ← ENNReal.ofReal_pow ha0, ← ENNReal.ofReal_mul (pow_nonneg ha0 _)]

/-- **The presented shift law of the matched blob presentation** on the
constructed space: the coin-averaged rule mass at arity `1 + j` over the neck
factor `1 - θ̃₁`, as a real number. -/
noncomputable def presentedShift (θ : Offspring J) (R L T : ℕ) {P' : ℕ → ℝ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hP' : ∀ b ∈ B, 0 ≤ P' b) (hP'1 : ∑ b ∈ B, P' b = 1)
    (j : ℕ) : ℝ :=
  ((∑ s : MatchedCoin B T, matchedCoinLaw hδ0 hδ1 hP' hP'1 {s}
      * bRuleMass θ R (matchedRule B L T) s (1 + j))
    / ENNReal.ofReal (1 - θ.skeletonWeight 1)).toReal

variable (θ : Offspring J) (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1) (R : ℕ)
  {MA MB : ℕ} (hA1 : ∀ x ∈ A, 1 ≤ x)
  (hAsupp : ∀ x, 1 ≤ x → θ.skeletonWeight (1 + x) ≠ 0 → x ∈ A) (hMA : ∀ a ∈ A, a ≤ MA)
  (hB0 : ∀ b ∈ B, 0 < b) (hMB : ∀ b ∈ B, b ≤ MB) {P' : ℕ → ℝ} (hP' : ∀ b ∈ B, 0 ≤ P' b)
  (hP'1 : ∑ b ∈ B, P' b = 1) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {L F T : ℕ}
  (hF : 3 * L + 2 * MA + MB + 2 ≤ F) (hF' : 2 * L + 2 * MA + 2 ≤ F) (hT : F + 1 ≤ T)

include hq hs1 hA1 hAsupp hMA hB0 hMB hF hF' hT

/-- **The presented shift law is `matchedShift`.** -/
theorem presentedShift_eq (j : ℕ) :
    presentedShift θ R L T hδ0 hδ1 hP' hP'1 j
      = matchedShift A B (fun x ↦ reducedWeight θ (1 + x)) P' L (θ.skeletonWeight 1 ^ R) δ F j := by
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  have hφ0 : 0 ≤ θ.skeletonWeight 1 ^ R := pow_nonneg ha0 R
  have hφ1 : θ.skeletonWeight 1 ^ R ≤ 1 := pow_le_one₀ ha0 hs1.le
  have hPnn : ∀ x ∈ A, 0 ≤ reducedWeight θ (1 + x) := fun x _ ↦ by
    rw [reducedWeight_def]
    exact div_nonneg (θ.skeletonWeight_nonneg hq _) (by linarith)
  rw [presentedShift, coinRuleMass_div_matchedRule θ hq hs1 R hA1 hAsupp hMA hB0 hMB hP' hP'1
    hδ0 hδ1 hF hF' hT j, ENNReal.toReal_ofReal]
  rw [matchedShift]
  exact add_nonneg (mul_nonneg hδ0 (freeLaw_nonneg hPnn hφ0 hφ1 F j))
    (mul_nonneg (by linarith) (coupleLaw_nonneg hPnn hP' hφ0 hφ1 F j))

/-- **`thm:matched-presentation` (`it:matched-support`)** on the
constructed space: the presented shifts are exactly `Λ ∩ (0, L + MA]`. -/
theorem presentedShift_pos_iff (hMAmem : MA ∈ A) (hMAL : MA ≤ L) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hPp : ∀ a ∈ A, p ≤ reducedWeight θ (1 + a))
    (hφh : θ.skeletonWeight 1 ^ R ≤ 1 / 2) (hδ0' : 0 < δ)
    (hwin : ∀ s' : ℕ, s' ∈ AddSubmonoid.closure (A : Set ℕ) → L < s' → s' ≤ L + MA →
      s' - MA ∈ AddSubmonoid.closure (A : Set ℕ)) {s : ℕ} :
    0 < presentedShift θ R L T hδ0 hδ1 hP' hP'1 s
      ↔ s ∈ AddSubmonoid.closure (A : Set ℕ) ∧ 0 < s ∧ s ≤ L + MA := by
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  have hPnn : ∀ x ∈ A, 0 ≤ reducedWeight θ (1 + x) := fun x _ ↦ by
    rw [reducedWeight_def]
    exact div_nonneg (θ.skeletonWeight_nonneg hq _) (by linarith)
  rw [presentedShift_eq θ hq hs1 R hA1 hAsupp hMA hB0 hMB hP' hP'1 hδ0 hδ1 hF hF' hT s]
  exact matchedShift_pos_iff hMAmem hMA hA1 hMAL hPnn hP' hp0 hp1 hPp (pow_nonneg ha0 R) hφh
    hδ0' hδ1 hwin (by omega)

/-- **`thm:matched-presentation` (`it:matched-mass`)** on the constructed
space: every presented shift carries mass at least `c δ`. -/
theorem presentedShift_floor (hMAmem : MA ∈ A) (hMAL : MA ≤ L) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hPp : ∀ a ∈ A, p ≤ reducedWeight θ (1 + a))
    (hwin : ∀ s' : ℕ, s' ∈ AddSubmonoid.closure (A : Set ℕ) → L < s' → s' ≤ L + MA →
      s' - MA ∈ AddSubmonoid.closure (A : Set ℕ)) {s : ℕ}
    (h1 : s ∈ AddSubmonoid.closure (A : Set ℕ)) (h2 : 0 < s) (h3 : s ≤ L + MA) :
    δ * ((1 / 2) * p * (p * (1 - θ.skeletonWeight 1 ^ R) / 2) ^ (L + MA))
      ≤ presentedShift θ R L T hδ0 hδ1 hP' hP'1 s := by
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  have hPnn : ∀ x ∈ A, 0 ≤ reducedWeight θ (1 + x) := fun x _ ↦ by
    rw [reducedWeight_def]
    exact div_nonneg (θ.skeletonWeight_nonneg hq _) (by linarith)
  rw [presentedShift_eq θ hq hs1 R hA1 hAsupp hMA hB0 hMB hP' hP'1 hδ0 hδ1 hF hF' hT s]
  exact matchedShift_floor hMAmem hA1 hMAL hPnn hP' hp0 hp1 hPp (pow_nonneg ha0 R)
    (pow_le_one₀ ha0 hs1.le) hδ0 hδ1 hwin (by omega) h1 h2 h3

/-- **`thm:matched-presentation` (`it:matched-bulk`), the window mass** on
the constructed space: the presented mass above `L` is at most
`δ + (1 - p^H)^k + 2(Fφ)²`. -/
theorem presentedShift_window
    (hsem : AddSubmonoid.closure (A : Set ℕ) = AddSubmonoid.closure (B : Set ℕ))
    {p : ℝ} (hp0 : 0 < p) (hAne : A.Nonempty)
    (hPp : ∀ a ∈ A, p ≤ reducedWeight θ (1 + a)) (hP'p : ∀ b ∈ B, p ≤ P' b) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ (W : Finset ℕ), (∀ s ∈ W, L < s) →
      ∀ k : ℕ, (k * H + 1) * MA ≤ L →
      ∑ s ∈ W, presentedShift θ R L T hδ0 hδ1 hP' hP'1 s
        ≤ δ + (1 - p ^ H) ^ k + 2 * (F * θ.skeletonWeight 1 ^ R) ^ 2 := by
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  have hPnn : ∀ x ∈ A, 0 ≤ reducedWeight θ (1 + x) := fun x _ ↦ by
    rw [reducedWeight_def]
    exact div_nonneg (θ.skeletonWeight_nonneg hq _) (by linarith)
  obtain ⟨H, hH1, hW⟩ := matchedShift_window (δ := δ) hMA hMB hA1 hB0 hPnn hP'
    (sum_reducedWeight_shift θ hq hs1 hA1 hAsupp) hP'1 hsem hp0 hAne hPp hP'p
    (pow_nonneg ha0 R) (pow_le_one₀ ha0 hs1.le) hδ0 hδ1 hF
  refine ⟨H, hH1, fun W hWL k hk ↦ ?_⟩
  rw [Finset.sum_congr rfl fun s _ ↦
    presentedShift_eq θ hq hs1 R hA1 hAsupp hMA hB0 hMB hP' hP'1 hδ0 hδ1 hF hF' hT s]
  exact hW W hWL k hk

end Presented

/-- **`thm:matched-presentation` (`it:matched-bulk`), the bulk agreement**
on the constructed space: the presented shift laws of the two matched blob
presentations, each run against the other's shifted reduced law, differ on the
bulk by at most `2δ` plus the two exhaustion masses. -/
theorem presentedShift_bulk_close {J' : ℕ} (θ : Offspring J) (θ' : Offspring J')
    (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1)
    (hq' : θ'.extinction < 1) (hs1' : θ'.skeletonWeight 1 < 1) (R R' : ℕ) {MA MB : ℕ}
    (hA1 : ∀ x ∈ A, 1 ≤ x) (hAsupp : ∀ x, 1 ≤ x → θ.skeletonWeight (1 + x) ≠ 0 → x ∈ A)
    (hMA : ∀ a ∈ A, a ≤ MA)
    (hB1 : ∀ x ∈ B, 1 ≤ x) (hBsupp : ∀ x, 1 ≤ x → θ'.skeletonWeight (1 + x) ≠ 0 → x ∈ B)
    (hMB : ∀ b ∈ B, b ≤ MB)
    (hP : ∀ a ∈ A, 0 ≤ reducedWeight θ (1 + a)) (hP1 : ∑ a ∈ A, reducedWeight θ (1 + a) = 1)
    (hP' : ∀ b ∈ B, 0 ≤ reducedWeight θ' (1 + b))
    (hP'1 : ∑ b ∈ B, reducedWeight θ' (1 + b) = 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {L F F' T T' : ℕ}
    (hF : 3 * L + 2 * MA + MB + 2 ≤ F) (hF2 : 2 * L + 2 * MA + 2 ≤ F) (hT : F + 1 ≤ T)
    (hF' : 3 * L + 2 * MB + MA + 2 ≤ F') (hF2' : 2 * L + 2 * MB + 2 ≤ F') (hT' : F' + 1 ≤ T')
    {Sb : Finset ℕ} (hSb : ∀ s ∈ Sb, s ≤ L) :
    ∑ s ∈ Sb, |presentedShift θ R L T hδ0 hδ1 hP' hP'1 s
        - presentedShift θ' R' L T' hδ0 hδ1 hP hP1 s|
      ≤ 2 * δ + 2 * (F * θ.skeletonWeight 1 ^ R) ^ 2
          + 2 * (F' * θ'.skeletonWeight 1 ^ R') ^ 2 := by
  have ha0 : 0 ≤ θ.skeletonWeight 1 := θ.skeletonWeight_nonneg hq 1
  have ha0' : 0 ≤ θ'.skeletonWeight 1 := θ'.skeletonWeight_nonneg hq' 1
  rw [Finset.sum_congr rfl fun s _ ↦ by
    rw [presentedShift_eq θ hq hs1 R hA1 hAsupp hMA hB1 hMB hP' hP'1 hδ0 hδ1 hF hF2 hT s,
      presentedShift_eq θ' hq' hs1' R' hB1 hBsupp hMB hA1 hMA hP hP1 hδ0 hδ1 hF' hF2' hT' s]]
  exact matchedShift_bulk_close hMA hMB hA1 hB1 hP hP' hP1 hP'1
    (pow_nonneg ha0 R) (pow_le_one₀ ha0 hs1.le) (pow_nonneg ha0' R')
    (pow_le_one₀ ha0' hs1'.le) hδ0 hδ1 hF hF' hSb

end Matched

end ChainClasses
