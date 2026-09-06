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

/-- Four possible choices of a selected common shifted increment. -/
inductive HeavyLagChoice where
  | two | four | six | eight
  deriving DecidableEq, Fintype, Repr

def HeavyLagChoice.index : HeavyLagChoice → Fin 4
  | .two => 0
  | .four => 1
  | .six => 2
  | .eight => 3

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

/-- An outcome together with the actual ordered exits exposed by it. -/
abbrev HeavyExitEvent (L R : Type) := HeavyLagOutcome × HeavyExitBatch L R

/-- Execute all concrete offspring batches through the FIFO ledger. -/
def ExitLedger.run {L R : Type} :
    ExitLedger L R → List (HeavyExitEvent L R) → ExitLedger L R
  | Q, [] => Q
  | Q, e :: es => (Q.expose e.2).run es

end GraphMarkovMatching
