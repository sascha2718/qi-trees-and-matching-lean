/-
The concrete full-retention lag ledger for the four-point common core
`{3,5,7,9}` with exceptional arities `11` on the left and `13` on the
right.

The phase is the signed difference between unmatched left and right exits.
Only the lagging side is exposed.  Since the shifted increments are even,
bounded above by `10` on the left and `12` on the right, every nonzero lag
belongs to the nine-element type below.  The exhaustive transition table
therefore retains every offspring outcome.  It also keeps the exceptional
coefficient literally equal to `ε`; no inverse exceptional atom is formed.

The file additionally checks the complete correction chart from the prose:
after choosing any one of the four common increments, every phase has a
legal closing word of length at most four using only that common increment
and the exceptional outcome.  The common part of the literal ledger is not
nilpotent: common increment `8` gives the two-cycle `4 -> -4 -> 4`.
-/
import GraphMarkovMatching.Obstructions.FiniteZipper
import GraphMarkovMatching.Obstructions.HeavyCore

namespace GraphMarkovMatching

open scoped ENNReal Classical BigOperators

/-- The nine nonzero even lags strictly between `-12` and `10`. -/
inductive HeavyLagPhase where
  | n10 | n8 | n6 | n4 | n2
  | p2 | p4 | p6 | p8
  deriving DecidableEq, Fintype, Repr

/-- The four common shifted increments and the side-dependent exceptional
increment (`10` on a left exposure, `12` on a right exposure). -/
inductive HeavyLagOutcome where
  | c2 | c4 | c6 | c8 | exceptional
  deriving DecidableEq, Fintype, Repr

/-- The integer represented by a ledger phase. -/
def heavyLagValue : HeavyLagPhase → ℤ
  | .n10 => -10
  | .n8 => -8
  | .n6 => -6
  | .n4 => -4
  | .n2 => -2
  | .p2 => 2
  | .p4 => 4
  | .p6 => 6
  | .p8 => 8

/-- A common increment is independent of the side.  The exceptional
increment is `10` in a negative phase (left is lagging) and `12` in a
positive phase (right is lagging). -/
def heavyLagShift : HeavyLagPhase → HeavyLagOutcome → ℕ
  | _, .c2 => 2
  | _, .c4 => 4
  | _, .c6 => 6
  | _, .c8 => 8
  | .n10, .exceptional => 10
  | .n8, .exceptional => 10
  | .n6, .exceptional => 10
  | .n4, .exceptional => 10
  | .n2, .exceptional => 10
  | .p2, .exceptional => 12
  | .p4, .exceptional => 12
  | .p6, .exceptional => 12
  | .p8, .exceptional => 12

/-- Exhaustive lagging-side transition table.  `none` is the closed phase
`0`; every other outcome lands back in the nine-element phase alphabet. -/
def heavyLagNext : HeavyLagPhase → HeavyLagOutcome → Option HeavyLagPhase
  | .n10, .c2 => some .n8
  | .n10, .c4 => some .n6
  | .n10, .c6 => some .n4
  | .n10, .c8 => some .n2
  | .n10, .exceptional => none
  | .n8, .c2 => some .n6
  | .n8, .c4 => some .n4
  | .n8, .c6 => some .n2
  | .n8, .c8 => none
  | .n8, .exceptional => some .p2
  | .n6, .c2 => some .n4
  | .n6, .c4 => some .n2
  | .n6, .c6 => none
  | .n6, .c8 => some .p2
  | .n6, .exceptional => some .p4
  | .n4, .c2 => some .n2
  | .n4, .c4 => none
  | .n4, .c6 => some .p2
  | .n4, .c8 => some .p4
  | .n4, .exceptional => some .p6
  | .n2, .c2 => none
  | .n2, .c4 => some .p2
  | .n2, .c6 => some .p4
  | .n2, .c8 => some .p6
  | .n2, .exceptional => some .p8
  | .p2, .c2 => none
  | .p2, .c4 => some .n2
  | .p2, .c6 => some .n4
  | .p2, .c8 => some .n6
  | .p2, .exceptional => some .n10
  | .p4, .c2 => some .p2
  | .p4, .c4 => none
  | .p4, .c6 => some .n2
  | .p4, .c8 => some .n4
  | .p4, .exceptional => some .n8
  | .p6, .c2 => some .p4
  | .p6, .c4 => some .p2
  | .p6, .c6 => none
  | .p6, .c8 => some .n2
  | .p6, .exceptional => some .n6
  | .p8, .c2 => some .p6
  | .p8, .c4 => some .p4
  | .p8, .c6 => some .p2
  | .p8, .c8 => none
  | .p8, .exceptional => some .n4

/-- The table is exactly addition on negative phases and subtraction on
positive phases. -/
theorem heavyLagNext_value (i : HeavyLagPhase) (o : HeavyLagOutcome) :
    match heavyLagNext i o with
    | none =>
        if heavyLagValue i < 0 then
          heavyLagValue i + heavyLagShift i o = 0
        else
          heavyLagValue i - heavyLagShift i o = 0
    | some j =>
        if heavyLagValue i < 0 then
          heavyLagValue j = heavyLagValue i + heavyLagShift i o
        else
          heavyLagValue j = heavyLagValue i - heavyLagShift i o := by
  cases i <;> cases o <;>
    norm_num [heavyLagNext, heavyLagValue, heavyLagShift]

/-! ### The lag as an actual FIFO allocation of exit occurrences -/

/-- Result of pairing two ordered exit lists from the front.  The two
remainder lists are the exits which have not yet found a partner. -/
structure FifoAllocation (L R : Type) where
  pairs : List (L × R)
  left : List L
  right : List R

/-- Pair ordered exits until one side is exhausted.  This is the precise
"oldest unmatched exit first" operation used by the lag ledger. -/
def fifoAllocate {L R : Type} : List L → List R → FifoAllocation L R
  | [], ys => ⟨[], [], ys⟩
  | xs, [] => ⟨[], xs, []⟩
  | x :: xs, y :: ys =>
      let A := fifoAllocate xs ys
      ⟨(x, y) :: A.pairs, A.left, A.right⟩

/-- FIFO allocation uses every occurrence on each side exactly once: it is
either the corresponding projection of a produced pair or it remains in the
queue.  These are equalities of lists, so multiplicities are retained. -/
theorem fifoAllocate_coverage {L R : Type} :
    ∀ (xs : List L) (ys : List R),
      (fifoAllocate xs ys).pairs.map Prod.fst ++
          (fifoAllocate xs ys).left = xs ∧
        (fifoAllocate xs ys).pairs.map Prod.snd ++
          (fifoAllocate xs ys).right = ys := by
  intro xs ys
  induction xs generalizing ys with
  | nil => simp [fifoAllocate]
  | cons x xs ih =>
      cases ys with
      | nil => simp [fifoAllocate]
      | cons y ys =>
          simpa [fifoAllocate] using ih ys

/-- At most one side has unmatched exits after FIFO allocation. -/
theorem fifoAllocate_exclusive {L R : Type} (xs : List L) (ys : List R) :
    (fifoAllocate xs ys).left = [] ∨ (fifoAllocate xs ys).right = [] := by
  induction xs generalizing ys with
  | nil => simp [fifoAllocate]
  | cons x xs ih =>
      cases ys with
      | nil => simp [fifoAllocate]
      | cons y ys => simpa [fifoAllocate] using ih ys

/-- Pair removal preserves the signed difference of the two list lengths. -/
theorem fifoAllocate_signedLength {L R : Type} (xs : List L) (ys : List R) :
    ((fifoAllocate xs ys).left.length : ℤ) -
        (fifoAllocate xs ys).right.length =
      (xs.length : ℤ) - ys.length := by
  obtain ⟨hL, hR⟩ := fifoAllocate_coverage xs ys
  have hL' := congrArg List.length hL
  have hR' := congrArg List.length hR
  simp only [List.length_append, List.length_map] at hL' hR'
  omega

/-- A genuine labelled Hall allocation: the pair list covers both ordered
input lists, and every selected pair satisfies the label relation. -/
def IsHallExitAllocation {L R : Type} (Rel : L → R → Prop)
    (xs : List L) (ys : List R) (ps : List (L × R)) : Prop :=
  ps.map Prod.fst = xs ∧ ps.map Prod.snd = ys ∧
    ∀ p ∈ ps, Rel p.1 p.2

/-- When FIFO closes and its selected pairs are label-compatible, it is a
complete Hall allocation of the two exit lists.  The compatibility premise
is explicit: counter arithmetic alone cannot prove a statement about the
labels carried by the exits. -/
theorem fifoAllocate_isHallExitAllocation_of_closes {L R : Type}
    (Rel : L → R → Prop) (xs : List L) (ys : List R)
    (hclose : (fifoAllocate xs ys).left = [] ∧
      (fifoAllocate xs ys).right = [])
    (hrel : ∀ p ∈ (fifoAllocate xs ys).pairs, Rel p.1 p.2) :
    IsHallExitAllocation Rel xs ys (fifoAllocate xs ys).pairs := by
  obtain ⟨hL, hR⟩ := fifoAllocate_coverage xs ys
  exact ⟨by simpa [hclose.1] using hL, by simpa [hclose.2] using hR, hrel⟩

/-- Signed queue invariant represented by a nonzero lag phase. -/
def HeavyQueueInvariant {L R : Type} (i : HeavyLagPhase)
    (left : List L) (right : List R) : Prop :=
  (left = [] ∨ right = []) ∧
    (left.length : ℤ) - right.length = heavyLagValue i

/-- The closed phase has two empty queues; a live phase carries the signed
invariant above. -/
def HeavyQueueState {L R : Type} :
    Option HeavyLagPhase → List L → List R → Prop
  | none, left, right => left = [] ∧ right = []
  | some i, left, right => HeavyQueueInvariant i left right

/-- Newly exposed exits.  Exactly one list is nonempty: the left list in a
negative phase and the right list in a positive phase. -/
structure HeavyExitBatch (L R : Type) where
  left : List L
  right : List R

def HeavyExitBatch.Valid {L R : Type} (i : HeavyLagPhase)
    (o : HeavyLagOutcome) (B : HeavyExitBatch L R) : Prop :=
  if heavyLagValue i < 0 then
    B.left.length = heavyLagShift i o ∧ B.right = []
  else
    B.left = [] ∧ B.right.length = heavyLagShift i o

/-- One concrete queue exposure: append the new descendant exits on the
lagging side and perform the FIFO pairing on the complete pending lists. -/
def heavyQueueStep {L R : Type} (left : List L) (right : List R)
    (B : HeavyExitBatch L R) : FifoAllocation L R :=
  fifoAllocate (left ++ B.left) (right ++ B.right)

/-- **Queue realization of every table entry.**  For arbitrary actual exit
occurrences, every valid offspring batch realizes the advertised live phase,
or empties both queues exactly when the table closes. -/
theorem heavyQueueStep_state {L R : Type} (i : HeavyLagPhase)
    (o : HeavyLagOutcome) (left : List L) (right : List R)
    (B : HeavyExitBatch L R)
    (hstate : HeavyQueueInvariant i left right)
    (hB : B.Valid i o) :
    HeavyQueueState (heavyLagNext i o)
      (heavyQueueStep left right B).left
      (heavyQueueStep left right B).right := by
  let A := heavyQueueStep left right B
  have hexclusive : A.left = [] ∨ A.right = [] := by
    exact fifoAllocate_exclusive (left ++ B.left) (right ++ B.right)
  have hbalance : (A.left.length : ℤ) - A.right.length =
      ((left ++ B.left).length : ℤ) - (right ++ B.right).length := by
    exact fifoAllocate_signedLength (left ++ B.left) (right ++ B.right)
  by_cases hneg : heavyLagValue i < 0
  · have hB' : B.left.length = heavyLagShift i o ∧ B.right = [] := by
      simpa [HeavyExitBatch.Valid, hneg] using hB
    have hinput :
        ((left ++ B.left).length : ℤ) - (right ++ B.right).length =
          heavyLagValue i + heavyLagShift i o := by
      rcases hstate with ⟨_, hstate⟩
      simp only [List.length_append, hB'.2, List.length_nil, add_zero]
      omega
    cases hnext : heavyLagNext i o with
    | none =>
        have harith : heavyLagValue i + heavyLagShift i o = 0 := by
          simpa [hnext, hneg] using heavyLagNext_value i o
        have hz : (A.left.length : ℤ) - A.right.length = 0 := by
          omega
        change A.left = [] ∧ A.right = []
        rcases hexclusive with hL | hR
        · refine ⟨hL, ?_⟩
          have hlen : A.right.length = 0 := by
            have hleft : A.left.length = 0 := by simp [hL]
            omega
          exact List.eq_nil_of_length_eq_zero hlen
        · refine ⟨?_, hR⟩
          have hlen : A.left.length = 0 := by
            have hright : A.right.length = 0 := by simp [hR]
            omega
          exact List.eq_nil_of_length_eq_zero hlen
    | some j =>
        have harith : heavyLagValue j =
            heavyLagValue i + heavyLagShift i o := by
          simpa [hnext, hneg] using heavyLagNext_value i o
        change HeavyQueueInvariant j A.left A.right
        exact ⟨hexclusive, by omega⟩
  · have hB' : B.left = [] ∧
        B.right.length = heavyLagShift i o := by
      simpa [HeavyExitBatch.Valid, hneg] using hB
    have hinput :
        ((left ++ B.left).length : ℤ) - (right ++ B.right).length =
          heavyLagValue i - heavyLagShift i o := by
      rcases hstate with ⟨_, hstate⟩
      simp only [List.length_append, hB'.1, List.length_nil, add_zero]
      omega
    cases hnext : heavyLagNext i o with
    | none =>
        have harith : heavyLagValue i - heavyLagShift i o = 0 := by
          simpa [hnext, hneg] using heavyLagNext_value i o
        have hz : (A.left.length : ℤ) - A.right.length = 0 := by
          omega
        change A.left = [] ∧ A.right = []
        rcases hexclusive with hL | hR
        · refine ⟨hL, ?_⟩
          have hlen : A.right.length = 0 := by
            have hleft : A.left.length = 0 := by simp [hL]
            omega
          exact List.eq_nil_of_length_eq_zero hlen
        · refine ⟨?_, hR⟩
          have hlen : A.left.length = 0 := by
            have hright : A.right.length = 0 := by simp [hR]
            omega
          exact List.eq_nil_of_length_eq_zero hlen
    | some j =>
        have harith : heavyLagValue j =
            heavyLagValue i - heavyLagShift i o := by
          simpa [hnext, hneg] using heavyLagNext_value i o
        change HeavyQueueInvariant j A.left A.right
        exact ⟨hexclusive, by omega⟩

/-- Indexing of the common weights: `0,1,2,3` correspond to arities
`3,5,7,9`, hence shifted increments `2,4,6,8`. -/
def heavyLagOutcomeMass (w : Fin 4 → ℝ≥0∞) (ε : ℝ≥0∞) :
    HeavyLagOutcome → ℝ≥0∞
  | .c2 => w 0
  | .c4 => w 1
  | .c6 => w 2
  | .c8 => w 3
  | .exceptional => ε

lemma sum_heavyLagOutcome (f : HeavyLagOutcome → ℝ≥0∞) :
    (∑ o, f o) = f .c2 + f .c4 + f .c6 + f .c8 + f .exceptional := by
  rw [show (Finset.univ : Finset HeavyLagOutcome) =
      {.c2, .c4, .c6, .c8, .exceptional} by decide]
  simp [add_assoc]

lemma heavyLagOutcomeMass_sum (w : Fin 4 → ℝ≥0∞) (ε : ℝ≥0∞)
    (htotal : (∑ i, w i) + ε = 1) :
    ∑ o, heavyLagOutcomeMass w ε o = 1 := by
  rw [sum_heavyLagOutcome]
  simpa [heavyLagOutcomeMass, Fin.sum_univ_succ, add_assoc] using htotal

/-- The concrete micro-step zipper.  Its outcome law is the full offspring
law of whichever side is lagging. -/
noncomputable def heavyLagZipper (w : Fin 4 → ℝ≥0∞) (ε : ℝ≥0∞)
    (htotal : (∑ i, w i) + ε = 1) :
    FiniteZipper (ι := HeavyLagPhase) (Ω := HeavyLagOutcome) where
  mass := fun _ o => heavyLagOutcomeMass w ε o
  next := heavyLagNext
  mass_sum := fun _ => heavyLagOutcomeMass_sum w ε htotal

/-- The common part of the live kernel, with the original four weights. -/
noncomputable def heavyLagCommonKernel (w : Fin 4 → ℝ≥0∞) :
    HeavyLagPhase → HeavyLagPhase → ℝ≥0∞ :=
  fun i j =>
    (if heavyLagNext i .c2 = some j then w 0 else 0) +
    (if heavyLagNext i .c4 = some j then w 1 else 0) +
    (if heavyLagNext i .c6 = some j then w 2 else 0) +
    (if heavyLagNext i .c8 = some j then w 3 else 0)

/-- The exceptional live transition, with its coefficient removed. -/
noncomputable def heavyLagExceptionalKernel :
    HeavyLagPhase → HeavyLagPhase → ℝ≥0∞ :=
  fun i j => if heavyLagNext i .exceptional = some j then 1 else 0

/-- Exact entrywise decomposition of the live kernel.  In particular, the
exceptional coefficient has not been divided by an atom probability. -/
theorem heavyLag_liveKernel_eq_rareMatrix (w : Fin 4 → ℝ≥0∞) (ε : ℝ≥0∞)
    (htotal : (∑ i, w i) + ε = 1) :
    (heavyLagZipper w ε htotal).liveKernel =
      rareMatrix (heavyLagCommonKernel w) heavyLagExceptionalKernel ε := by
  funext i j
  cases i <;> cases j <;>
    simp [FiniteZipper.liveKernel, sum_heavyLagOutcome, heavyLagZipper,
      heavyLagOutcomeMass,
      heavyLagCommonKernel, heavyLagExceptionalKernel, rareMatrix, heavyLagNext]

/-- Arithmetic admissibility of a counter outcome.  Unlike the former
placeholder `True`, this records the exact signed queue update represented by
the destination phase (or equality to zero when the queue closes). -/
def heavyLagAdmissible (i : HeavyLagPhase) (o : HeavyLagOutcome) : Prop :=
  match heavyLagNext i o with
  | none =>
      if heavyLagValue i < 0 then
        heavyLagValue i + heavyLagShift i o = 0
      else
        heavyLagValue i - heavyLagShift i o = 0
  | some j =>
      if heavyLagValue i < 0 then
        heavyLagValue j = heavyLagValue i + heavyLagShift i o
      else
        heavyLagValue j = heavyLagValue i - heavyLagShift i o

theorem heavyLag_all_admissible (i : HeavyLagPhase) (o : HeavyLagOutcome) :
    heavyLagAdmissible i o := by
  exact heavyLagNext_value i o

theorem heavyLag_retainedMass_eq_one (w : Fin 4 → ℝ≥0∞) (ε : ℝ≥0∞)
    (htotal : (∑ i, w i) + ε = 1) (i : HeavyLagPhase) :
    (heavyLagZipper w ε htotal).retainedMass heavyLagAdmissible i = 1 := by
  apply FiniteZipper.retainedMass_eq_one_of_all
  exact heavyLag_all_admissible

theorem heavyLag_live_add_killed_eq_one (w : Fin 4 → ℝ≥0∞) (ε : ℝ≥0∞)
    (htotal : (∑ i, w i) + ε = 1) (i : HeavyLagPhase) :
    (∑ j, (heavyLagZipper w ε htotal).liveKernel i j) +
      (heavyLagZipper w ε htotal).killedMass i = 1 :=
  FiniteZipper.liveKernel_sum_add_killedMass _ _

/-- Four possible choices of a selected common shifted increment. -/
inductive HeavyLagChoice where
  | two | four | six | eight
  deriving DecidableEq, Fintype, Repr

def HeavyLagChoice.index : HeavyLagChoice → Fin 4
  | .two => 0
  | .four => 1
  | .six => 2
  | .eight => 3

def HeavyLagChoice.outcome : HeavyLagChoice → HeavyLagOutcome
  | .two => .c2
  | .four => .c4
  | .six => .c6
  | .eight => .c8

/-- Convert the heavy index selected in `Obstructions/HeavyCore.lean` to the
corresponding correction chart. -/
def heavyLagChoiceOfIndex (i : Fin 4) : HeavyLagChoice :=
  match i.1 with
  | 0 => .two
  | 1 => .four
  | 2 => .six
  | _ => .eight

theorem heavyLagChoiceOfIndex_index (i : Fin 4) :
    (heavyLagChoiceOfIndex i).index = i := by
  fin_cases i <;> rfl

/-- Execute a finite correction word; `none` remains closed. -/
def heavyLagRun : Option HeavyLagPhase → List HeavyLagOutcome → Option HeavyLagPhase
  | s, [] => s
  | none, _ :: os => heavyLagRun none os
  | some i, o :: os => heavyLagRun (heavyLagNext i o) os

/-- The complete correction table displayed in the manuscript. -/
def heavyLagCorrection : HeavyLagChoice → HeavyLagPhase → List HeavyLagOutcome
  | .two, .n10 => [.exceptional]
  | .two, .n8 => [.exceptional, .c2]
  | .two, .n6 => [.c2, .c2, .c2]
  | .two, .n4 => [.c2, .c2]
  | .two, .n2 => [.c2]
  | .two, .p2 => [.c2]
  | .two, .p4 => [.c2, .c2]
  | .two, .p6 => [.c2, .c2, .c2]
  | .two, .p8 => [.exceptional, .c2, .c2]
  | .four, .n10 => [.exceptional]
  | .four, .n8 => [.c4, .c4]
  | .four, .n6 => [.exceptional, .c4]
  | .four, .n4 => [.c4]
  | .four, .n2 => [.c4, .exceptional, .exceptional]
  | .four, .p2 => [.exceptional, .exceptional]
  | .four, .p4 => [.c4]
  | .four, .p6 => [.c4, .exceptional, .exceptional]
  | .four, .p8 => [.c4, .c4]
  | .six, .n10 => [.exceptional]
  | .six, .n8 => [.exceptional, .exceptional, .exceptional]
  | .six, .n6 => [.c6]
  | .six, .n4 => [.exceptional, .c6]
  | .six, .n2 => [.exceptional, .c6, .exceptional, .exceptional]
  | .six, .p2 => [.exceptional, .exceptional]
  | .six, .p4 => [.exceptional, .exceptional, .exceptional, .exceptional]
  | .six, .p6 => [.c6]
  | .six, .p8 => [.c6, .exceptional, .exceptional]
  | .eight, .n10 => [.exceptional]
  | .eight, .n8 => [.c8]
  | .eight, .n6 => [.c8, .exceptional, .exceptional]
  | .eight, .n4 => [.c8, .exceptional, .c8]
  | .eight, .n2 => [.exceptional, .c8]
  | .eight, .p2 => [.exceptional, .exceptional]
  | .eight, .p4 => [.exceptional, .c8]
  | .eight, .p6 => [.c8, .exceptional, .c8]
  | .eight, .p8 => [.c8]

theorem heavyLagCorrection_length_le_four (a : HeavyLagChoice)
    (i : HeavyLagPhase) : (heavyLagCorrection a i).length ≤ 4 := by
  cases a <;> cases i <;> decide

theorem heavyLagCorrection_closes (a : HeavyLagChoice) (i : HeavyLagPhase) :
    heavyLagRun (some i) (heavyLagCorrection a i) = none := by
  cases a <;> cases i <;> rfl

/-- A word is legal when the queue stays live before every listed exposure;
in particular, no suffix is silently read after an earlier closure. -/
def HeavyOutcomeWordValid :
    Option HeavyLagPhase → List HeavyLagOutcome → Prop
  | _, [] => True
  | none, _ :: _ => False
  | some i, o :: os => HeavyOutcomeWordValid (heavyLagNext i o) os

/-- Every correction word is legal at each intermediate sign, and closes
only on its final listed exposure. -/
theorem heavyLagCorrection_wordValid (a : HeavyLagChoice) (i : HeavyLagPhase) :
    HeavyOutcomeWordValid (some i) (heavyLagCorrection a i) := by
  cases a <;> cases i <;>
    simp [HeavyOutcomeWordValid, heavyLagCorrection, heavyLagNext]

/-! ### Whole-word allocation and the exact Hall boundary -/

/-- A FIFO ledger remembers all pairs already produced as well as the two
pending queues. -/
structure ExitLedger (L R : Type) where
  pairs : List (L × R)
  left : List L
  right : List R

/-- Add one offspring batch and allocate against the pending queue. -/
def ExitLedger.expose {L R : Type} (Q : ExitLedger L R)
    (B : HeavyExitBatch L R) : ExitLedger L R :=
  let A := heavyQueueStep Q.left Q.right B
  ⟨Q.pairs ++ A.pairs, A.left, A.right⟩

theorem ExitLedger.expose_left_coverage {L R : Type} (Q : ExitLedger L R)
    (B : HeavyExitBatch L R) :
    (Q.expose B).pairs.map Prod.fst ++ (Q.expose B).left =
      Q.pairs.map Prod.fst ++ Q.left ++ B.left := by
  have h := (fifoAllocate_coverage (Q.left ++ B.left)
    (Q.right ++ B.right)).1
  simp only [ExitLedger.expose, heavyQueueStep, List.map_append]
  simpa [List.append_assoc] using
    congrArg (fun zs => Q.pairs.map Prod.fst ++ zs) h

theorem ExitLedger.expose_right_coverage {L R : Type} (Q : ExitLedger L R)
    (B : HeavyExitBatch L R) :
    (Q.expose B).pairs.map Prod.snd ++ (Q.expose B).right =
      Q.pairs.map Prod.snd ++ Q.right ++ B.right := by
  have h := (fifoAllocate_coverage (Q.left ++ B.left)
    (Q.right ++ B.right)).2
  simp only [ExitLedger.expose, heavyQueueStep, List.map_append]
  simpa [List.append_assoc] using
    congrArg (fun zs => Q.pairs.map Prod.snd ++ zs) h

/-- An outcome together with the actual ordered exits exposed by it. -/
abbrev HeavyExitEvent (L R : Type) := HeavyLagOutcome × HeavyExitBatch L R

/-- The concatenated left occurrences exposed along an event word. -/
def heavyEventLefts {L R : Type} : List (HeavyExitEvent L R) → List L
  | [] => []
  | e :: es => e.2.left ++ heavyEventLefts es

/-- The concatenated right occurrences exposed along an event word. -/
def heavyEventRights {L R : Type} : List (HeavyExitEvent L R) → List R
  | [] => []
  | e :: es => e.2.right ++ heavyEventRights es

/-- Execute all concrete offspring batches through the FIFO ledger. -/
def ExitLedger.run {L R : Type} :
    ExitLedger L R → List (HeavyExitEvent L R) → ExitLedger L R
  | Q, [] => Q
  | Q, e :: es => (Q.expose e.2).run es

/-- Whole-run occurrence conservation on the left. -/
theorem ExitLedger.run_left_coverage {L R : Type} :
    ∀ (Q : ExitLedger L R) (es : List (HeavyExitEvent L R)),
      (Q.run es).pairs.map Prod.fst ++ (Q.run es).left =
        Q.pairs.map Prod.fst ++ Q.left ++ heavyEventLefts es := by
  intro Q es
  induction es generalizing Q with
  | nil => simp [ExitLedger.run, heavyEventLefts]
  | cons e es ih =>
      rw [ExitLedger.run, ih, heavyEventLefts,
        ExitLedger.expose_left_coverage]
      simp [List.append_assoc]

/-- Whole-run occurrence conservation on the right. -/
theorem ExitLedger.run_right_coverage {L R : Type} :
    ∀ (Q : ExitLedger L R) (es : List (HeavyExitEvent L R)),
      (Q.run es).pairs.map Prod.snd ++ (Q.run es).right =
        Q.pairs.map Prod.snd ++ Q.right ++ heavyEventRights es := by
  intro Q es
  induction es generalizing Q with
  | nil => simp [ExitLedger.run, heavyEventRights]
  | cons e es ih =>
      rw [ExitLedger.run, ih, heavyEventRights,
        ExitLedger.expose_right_coverage]
      simp [List.append_assoc]

/-- An event word follows the phase grammar and supplies exactly the number
of exit occurrences prescribed by each offspring outcome.  No event is
allowed after the queue has closed. -/
def HeavyEventsValid {L R : Type} :
    Option HeavyLagPhase → List (HeavyExitEvent L R) → Prop
  | _, [] => True
  | none, _ :: _ => False
  | some i, e :: es => e.2.Valid i e.1 ∧
      HeavyEventsValid (heavyLagNext i e.1) es

/-- Valid concrete event words preserve the exact phase/queue invariant. -/
theorem ExitLedger.run_queueState {L R : Type} :
    ∀ (s : Option HeavyLagPhase) (Q : ExitLedger L R)
      (es : List (HeavyExitEvent L R)),
      HeavyQueueState s Q.left Q.right → HeavyEventsValid s es →
      HeavyQueueState (heavyLagRun s (es.map Prod.fst))
        (Q.run es).left (Q.run es).right := by
  intro s Q es
  induction es generalizing s Q with
  | nil =>
      intro hstate _
      simpa [ExitLedger.run, heavyLagRun] using hstate
  | cons e es ih =>
      intro hstate hvalid
      rcases e with ⟨o, B⟩
      cases s with
      | none => simp [HeavyEventsValid] at hvalid
      | some i =>
          have hvalid' : B.Valid i o ∧
              HeavyEventsValid (heavyLagNext i o) es := by
            simpa [HeavyEventsValid] using hvalid
          have hstep : HeavyQueueState (heavyLagNext i o)
              (Q.expose B).left (Q.expose B).right := by
            have hInv : HeavyQueueInvariant i Q.left Q.right := hstate
            simpa [ExitLedger.expose] using
              heavyQueueStep_state i o Q.left Q.right B hInv hvalid'.1
          simpa [ExitLedger.run, heavyLagRun] using
            ih (heavyLagNext i o) (Q.expose B) hstep hvalid'.2

/-- A closed whole-word FIFO run is a complete labelled Hall allocation.
All counter/descendant occurrences are covered by the conclusion.  The sole
semantic premise is that the concrete pairs produced by the run satisfy the
requested label relation. -/
theorem ExitLedger.run_isHallExitAllocation_of_closes {L R : Type}
    (Rel : L → R → Prop) (Q : ExitLedger L R)
    (es : List (HeavyExitEvent L R))
    (hclose : (Q.run es).left = [] ∧ (Q.run es).right = [])
    (hrel : ∀ p ∈ (Q.run es).pairs, Rel p.1 p.2) :
    IsHallExitAllocation Rel
      (Q.pairs.map Prod.fst ++ Q.left ++ heavyEventLefts es)
      (Q.pairs.map Prod.snd ++ Q.right ++ heavyEventRights es)
      (Q.run es).pairs := by
  refine ⟨?_, ?_, hrel⟩
  · have h := Q.run_left_coverage es
    simpa [hclose.1] using h
  · have h := Q.run_right_coverage es
    simpa [hclose.2] using h

/-- **Complete correction-word allocation.**  Any actual descendant batches
whose outcomes are one of the 36 certified correction words, and whose sizes
are those prescribed by the offspring values, exhaust both pending queues.
If their produced pairs are label-compatible, they form a complete Hall
allocation of every exposed exit occurrence. -/
theorem heavyLagCorrection_isHallExitAllocation {L R : Type}
    (Rel : L → R → Prop) (a : HeavyLagChoice) (i : HeavyLagPhase)
    (Q : ExitLedger L R) (es : List (HeavyExitEvent L R))
    (hQ : HeavyQueueInvariant i Q.left Q.right)
    (houtcomes : es.map Prod.fst = heavyLagCorrection a i)
    (hvalid : HeavyEventsValid (some i) es)
    (hrel : ∀ p ∈ (Q.run es).pairs, Rel p.1 p.2) :
    IsHallExitAllocation Rel
      (Q.pairs.map Prod.fst ++ Q.left ++ heavyEventLefts es)
      (Q.pairs.map Prod.snd ++ Q.right ++ heavyEventRights es)
      (Q.run es).pairs := by
  have hstate := ExitLedger.run_queueState (some i) Q es hQ hvalid
  have hphase : heavyLagRun (some i) (es.map Prod.fst) = none := by
    rw [houtcomes]
    exact heavyLagCorrection_closes a i
  rw [hphase] at hstate
  exact ExitLedger.run_isHallExitAllocation_of_closes Rel Q es hstate hrel

/-- Counter-level version with no label premise: the correction word is a
complete structural allocation of all descendant-exit occurrences. -/
theorem heavyLagCorrection_isCompleteExitAllocation {L R : Type}
    (a : HeavyLagChoice) (i : HeavyLagPhase)
    (Q : ExitLedger L R) (es : List (HeavyExitEvent L R))
    (hQ : HeavyQueueInvariant i Q.left Q.right)
    (houtcomes : es.map Prod.fst = heavyLagCorrection a i)
    (hvalid : HeavyEventsValid (some i) es) :
    IsHallExitAllocation (fun _ _ => True)
      (Q.pairs.map Prod.fst ++ Q.left ++ heavyEventLefts es)
      (Q.pairs.map Prod.snd ++ Q.right ++ heavyEventRights es)
      (Q.run es).pairs := by
  apply heavyLagCorrection_isHallExitAllocation
    (Rel := fun _ _ => True) a i Q es hQ houtcomes hvalid
  simp

theorem heavyLagCorrection_mem (a : HeavyLagChoice) (i : HeavyLagPhase)
    {o : HeavyLagOutcome} (ho : o ∈ heavyLagCorrection a i) :
    o = a.outcome ∨ o = .exceptional := by
  cases a <;> cases i <;>
    simp_all [heavyLagCorrection, HeavyLagChoice.outcome] <;> aesop

/-- Probability of a correction word.  Since the exceptional mass is the
same on both sides, it depends only on the word, not on the intermediate
phase signs. -/
noncomputable def heavyLagWordMass (w : Fin 4 → ℝ≥0∞) (ε : ℝ≥0∞) :
    List HeavyLagOutcome → ℝ≥0∞
  | [] => 1
  | o :: os => heavyLagOutcomeMass w ε o * heavyLagWordMass w ε os

lemma pow_length_le_heavyLagWordMass {w : Fin 4 → ℝ≥0∞} {ε q : ℝ≥0∞}
    {os : List HeavyLagOutcome}
    (hmass : ∀ o ∈ os, q ≤ heavyLagOutcomeMass w ε o) :
    q ^ os.length ≤ heavyLagWordMass w ε os := by
  induction os with
  | nil => simp [heavyLagWordMass]
  | cons o os ih =>
      simpa [heavyLagWordMass, pow_succ', mul_comm] using
        mul_le_mul (hmass o (by simp))
          (ih (fun x hx => hmass x (by simp [hx]))) (by simp) (by simp)

/-- Every displayed correction cylinder has probability at least `q^4`
when `q` is below both the selected common mass and the exceptional mass. -/
theorem q_pow_four_le_heavyLagCorrectionMass
    (w : Fin 4 → ℝ≥0∞) (ε q : ℝ≥0∞) (a : HeavyLagChoice)
    (i : HeavyLagPhase) (hq1 : q ≤ 1)
    (hqCommon : q ≤ w a.index) (hqExceptional : q ≤ ε) :
    q ^ 4 ≤ heavyLagWordMass w ε (heavyLagCorrection a i) := by
  calc
    q ^ 4 ≤ q ^ (heavyLagCorrection a i).length :=
      pow_le_pow_right_of_le_one' hq1 (heavyLagCorrection_length_le_four a i)
    _ ≤ heavyLagWordMass w ε (heavyLagCorrection a i) := by
      apply pow_length_le_heavyLagWordMass
      intro o ho
      rcases heavyLagCorrection_mem a i ho with h | h
      · subst o
        cases a <;> simpa [HeavyLagChoice.outcome, HeavyLagChoice.index,
          heavyLagOutcomeMass] using hqCommon
      · subst o
        simpa [heavyLagOutcomeMass] using hqExceptional

/-- The executable correction table is also a closing word for the concrete
`FiniteZipper`, not merely for the standalone transition function. -/
theorem heavyLagCorrection_closes_zipper
    (w : Fin 4 → ℝ≥0∞) (ε : ℝ≥0∞)
    (htotal : (∑ i, w i) + ε = 1) (a : HeavyLagChoice)
    (i : HeavyLagPhase) :
    (heavyLagZipper w ε htotal).run (some i) (heavyLagCorrection a i) = none := by
  cases a <;> cases i <;> rfl

/-- Along a correction word, the generic zipper cylinder mass is exactly
the displayed product of original common and exceptional atom weights. -/
theorem heavyLagCorrection_pathMass
    (w : Fin 4 → ℝ≥0∞) (ε : ℝ≥0∞)
    (htotal : (∑ i, w i) + ε = 1) (a : HeavyLagChoice)
    (i : HeavyLagPhase) :
    (heavyLagZipper w ε htotal).pathMass (some i) (heavyLagCorrection a i) =
      heavyLagWordMass w ε (heavyLagCorrection a i) := by
  cases a <;> cases i <;> rfl

/-- Exact four-step killed-kernel estimate supplied by any lower bound `q`
on the chosen common atom and the exceptional atom. -/
theorem heavyLag_four_step_killing
    (w : Fin 4 → ℝ≥0∞) (ε q : ℝ≥0∞)
    (htotal : (∑ i, w i) + ε = 1) (a : HeavyLagChoice)
    (hq1 : q ≤ 1) (hqCommon : q ≤ w a.index)
    (hqExceptional : q ≤ ε) (i : HeavyLagPhase) :
    (mulVec (heavyLagZipper w ε htotal).liveKernel)^[4]
        (fun _ => 1) i ≤ 1 - q ^ 4 := by
  refine FiniteZipper.iterate_liveKernel_le_one_sub_of_closingWord
    (Z := heavyLagZipper w ε htotal) (n := 4) (q := q ^ 4) ?_
      i (heavyLagCorrection a i) ?_ ?_ ?_
  · simpa using pow_le_pow_left' hq1 4
  · exact heavyLagCorrection_length_le_four a i
  · exact heavyLagCorrection_closes_zipper w ε htotal a i
  · rw [heavyLagCorrection_pathMass]
    exact q_pow_four_le_heavyLagCorrectionMass w ε q a i
      hq1 hqCommon hqExceptional

/-- The manuscript's specialization `q = min(w_a, ε)`. -/
theorem heavyLag_four_step_killing_min
    (w : Fin 4 → ℝ≥0∞) (ε : ℝ≥0∞)
    (htotal : (∑ i, w i) + ε = 1) (a : HeavyLagChoice)
    (i : HeavyLagPhase) :
    (mulVec (heavyLagZipper w ε htotal).liveKernel)^[4]
        (fun _ => 1) i ≤ 1 - (min (w a.index) ε) ^ 4 := by
  have hw1 : w a.index ≤ 1 := by
    calc
      w a.index ≤ ∑ j, w j :=
        Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ a.index)
      _ ≤ (∑ j, w j) + ε := le_add_right le_rfl
      _ = 1 := htotal
  exact heavyLag_four_step_killing w ε (min (w a.index) ε) htotal a
    ((min_le_left _ _).trans hw1) (min_le_left _ _) (min_le_right _ _) i

/-- Specialization to the maximal common atom chosen by `heavyCoreIndex`.
The same theorem simultaneously records its uniform `1/8` lower bound. -/
theorem heavyCoreLag_four_step_killing
    (w : Fin 4 → ℝ≥0∞) (ε : ℝ≥0∞)
    (hε : ε ≤ 2⁻¹) (hsum : (∑ i, w i) = 1 - ε)
    (htotal : (∑ i, w i) + ε = 1) (i : HeavyLagPhase) :
    8⁻¹ ≤ w (heavyCoreIndex w) ∧
      (mulVec (heavyLagZipper w ε htotal).liveKernel)^[4]
          (fun _ => 1) i ≤
        1 - (min (w (heavyCoreIndex w)) ε) ^ 4 := by
  constructor
  · exact eighth_le_heavyCoreWeight w hε hsum
  · let a := heavyLagChoiceOfIndex (heavyCoreIndex w)
    have ha : a.index = heavyCoreIndex w := heavyLagChoiceOfIndex_index _
    simpa [a, ha] using heavyLag_four_step_killing_min w ε htotal a i

/-- Concrete full-retention removes the counter normalizer exactly. -/
theorem heavyLag_normalizedScreenKernel_eq_screenKernel
    (w : Fin 4 → ℝ≥0∞) (ε : ℝ≥0∞)
    (htotal : (∑ i, w i) + ε = 1) (α : ℝ)
    (labelTilt : HeavyLagPhase → ℝ≥0∞) :
    (heavyLagZipper w ε htotal).normalizedScreenKernel
        heavyLagAdmissible α labelTilt =
      (heavyLagZipper w ε htotal).screenKernel labelTilt := by
  apply FiniteZipper.normalizedScreenKernel_eq_screenKernel_of_all
  exact heavyLag_all_admissible

/-- Concrete form of the label-screen domination.  Its scalar contains no
offspring atom and in particular no inverse power of `ε`. -/
theorem heavyLag_integrated_screenKernel_le
    {X : Type} {α : ℝ} (hα : 1 ≤ α)
    (w : Fin 4 → ℝ≥0∞) (ε : ℝ≥0∞)
    (htotal : (∑ i, w i) + ε = 1)
    (source normalization : HeavyLagPhase → PMF X) (R : X → X → Prop)
    {M : ℝ≥0∞}
    (hM : ∀ i, PhiDres α (source i) (normalization i) R ≤ M)
    (i j : HeavyLagPhase) :
    (heavyLagZipper w ε htotal).screenKernel
        (FiniteZipper.integratedLabelTilt α source normalization R) i j ≤
      (1 + ENNReal.ofReal α * M) *
        (heavyLagZipper w ε htotal).liveKernel i j := by
  exact FiniteZipper.integrated_screenKernel_le hα
    (heavyLagZipper w ε htotal) source normalization R hM i j

/-- The common increment `8` gives the advertised two-cycle. -/
theorem heavyLag_common_eight_cycle :
    heavyLagNext .p4 .c8 = some .n4 ∧
      heavyLagNext .n4 .c8 = some .p4 := by
  decide

theorem heavyLagCommonKernel_p4_n4 (w : Fin 4 → ℝ≥0∞) :
    heavyLagCommonKernel w .p4 .n4 = w 3 := by
  simp [heavyLagCommonKernel, heavyLagNext]

theorem heavyLagCommonKernel_n4_p4 (w : Fin 4 → ℝ≥0∞) :
    heavyLagCommonKernel w .n4 .p4 = w 3 := by
  simp [heavyLagCommonKernel, heavyLagNext]

/-- The two common `8`-edges give a positive two-step contribution.  This
formally rules out a two-step nilpotence claim whenever `w 3` is nonzero. -/
theorem heavyLagCommonKernel_cycle_lower (w : Fin 4 → ℝ≥0∞) :
    w 3 * w 3 ≤
      (mulVec (heavyLagCommonKernel w))^[2] (fun _ => 1) .p4 := by
  rw [show (mulVec (heavyLagCommonKernel w))^[2] (fun _ => 1) .p4 =
      mulVec (heavyLagCommonKernel w)
        (mulVec (heavyLagCommonKernel w) (fun _ => 1)) .p4 by rfl]
  calc
    w 3 * w 3 = heavyLagCommonKernel w .p4 .n4 * w 3 := by
      rw [heavyLagCommonKernel_p4_n4]
    _ ≤ heavyLagCommonKernel w .p4 .n4 *
        mulVec (heavyLagCommonKernel w) (fun _ => 1) .n4 := by
      gcongr
      calc
        w 3 = heavyLagCommonKernel w .n4 .p4 * 1 := by
          rw [heavyLagCommonKernel_n4_p4, mul_one]
        _ ≤ ∑ j, heavyLagCommonKernel w .n4 j * 1 :=
          Finset.single_le_sum
            (f := fun j => heavyLagCommonKernel w .n4 j * 1)
            (fun _ _ => zero_le)
            (Finset.mem_univ HeavyLagPhase.p4)
        _ = mulVec (heavyLagCommonKernel w) (fun _ => 1) .n4 := rfl
    _ ≤ ∑ j, heavyLagCommonKernel w .p4 j *
        mulVec (heavyLagCommonKernel w) (fun _ => 1) j :=
      Finset.single_le_sum
        (f := fun j => heavyLagCommonKernel w .p4 j *
          mulVec (heavyLagCommonKernel w) (fun _ => 1) j)
        (fun _ _ => zero_le)
        (Finset.mem_univ HeavyLagPhase.n4)
    _ = mulVec (heavyLagCommonKernel w)
        (mulVec (heavyLagCommonKernel w) (fun _ => 1)) .p4 := rfl

theorem heavyLagCommonKernel_not_two_step_nilpotent (w : Fin 4 → ℝ≥0∞)
    (hw8 : w 3 ≠ 0) :
    (mulVec (heavyLagCommonKernel w))^[2] (fun _ => 1) .p4 ≠ 0 := by
  intro hzero
  have hsq : w 3 * w 3 = 0 :=
    nonpos_iff_eq_zero.mp ((heavyLagCommonKernel_cycle_lower w).trans_eq hzero)
  exact hw8 (mul_self_eq_zero.mp hsq)

/-- One traversal of the common two-cycle lower-bounds two kernel steps on
an arbitrary nonnegative input vector. -/
theorem heavyLagCommonKernel_cycle_step (w : Fin 4 → ℝ≥0∞)
    (x : HeavyLagPhase → ℝ≥0∞) :
    (w 3 * w 3) * x .p4 ≤
      (mulVec (heavyLagCommonKernel w))^[2] x .p4 := by
  rw [show (mulVec (heavyLagCommonKernel w))^[2] x .p4 =
      mulVec (heavyLagCommonKernel w)
        (mulVec (heavyLagCommonKernel w) x) .p4 by rfl]
  calc
    (w 3 * w 3) * x .p4 =
        heavyLagCommonKernel w .p4 .n4 * (w 3 * x .p4) := by
      rw [heavyLagCommonKernel_p4_n4]
      ac_rfl
    _ ≤ heavyLagCommonKernel w .p4 .n4 *
        mulVec (heavyLagCommonKernel w) x .n4 := by
      gcongr
      calc
        w 3 * x .p4 = heavyLagCommonKernel w .n4 .p4 * x .p4 := by
          rw [heavyLagCommonKernel_n4_p4]
        _ ≤ ∑ j, heavyLagCommonKernel w .n4 j * x j :=
          Finset.single_le_sum
            (f := fun j => heavyLagCommonKernel w .n4 j * x j)
            (fun _ _ => zero_le) (Finset.mem_univ HeavyLagPhase.p4)
        _ = mulVec (heavyLagCommonKernel w) x .n4 := rfl
    _ ≤ ∑ j, heavyLagCommonKernel w .p4 j *
        mulVec (heavyLagCommonKernel w) x j :=
      Finset.single_le_sum
        (f := fun j => heavyLagCommonKernel w .p4 j *
          mulVec (heavyLagCommonKernel w) x j)
        (fun _ _ => zero_le) (Finset.mem_univ HeavyLagPhase.n4)
    _ = mulVec (heavyLagCommonKernel w)
        (mulVec (heavyLagCommonKernel w) x) .p4 := rfl

/-- Repeating the cycle gives a nonzero contribution at every even power. -/
theorem heavyLagCommonKernel_cycle_iterate_lower (w : Fin 4 → ℝ≥0∞) :
    ∀ n, (w 3 * w 3) ^ n ≤
      (mulVec (heavyLagCommonKernel w))^[2 * n] (fun _ => 1) .p4 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      let f := mulVec (heavyLagCommonKernel w)
      have hstep := heavyLagCommonKernel_cycle_step w (f^[2 * n] (fun _ => 1))
      have hiter : f^[2 * (n + 1)] (fun _ => 1) =
          f^[2] (f^[2 * n] (fun _ => 1)) := by
        simpa [Nat.mul_succ, Nat.add_comm] using
          (Function.iterate_add_apply f 2 (2 * n) (fun _ => 1))
      rw [hiter]
      calc
        (w 3 * w 3) ^ (n + 1) =
            (w 3 * w 3) * (w 3 * w 3) ^ n := by
          rw [pow_succ, mul_comm]
        _ ≤ (w 3 * w 3) * (f^[2 * n] (fun _ => 1)) .p4 := by
          gcongr
        _ ≤ (f^[2] (f^[2 * n] (fun _ => 1))) .p4 := hstep

/-- Hence the literal common lag kernel is not nilpotent whenever common
increment `8` has positive mass. -/
theorem heavyLagCommonKernel_not_nilpotent (w : Fin 4 → ℝ≥0∞)
    (hw8 : w 3 ≠ 0) :
    ¬ ∃ r, (mulVec (heavyLagCommonKernel w))^[r] (fun _ => 1) = fun _ => 0 := by
  intro hnil
  obtain ⟨r, hr⟩ := hnil
  let f := mulVec (heavyLagCommonKernel w)
  have hzero : ∀ n, f^[n] (fun _ => 0) = fun _ => 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        funext i
        simp [f, mulVec]
  have heven : (f^[2 * r] (fun _ => 1)) .p4 = 0 := by
    have hadd : f^[r + r] (fun _ => 1) = f^[r] (f^[r] (fun _ => 1)) :=
      Function.iterate_add_apply f r r (fun _ => 1)
    rw [show 2 * r = r + r by omega, hadd, hr, hzero]
  have hlower := heavyLagCommonKernel_cycle_iterate_lower w r
  have hpow : (w 3 * w 3) ^ r ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero hw8 hw8)
  exact hpow (nonpos_iff_eq_zero.mp (hlower.trans_eq heven))

end GraphMarkovMatching
