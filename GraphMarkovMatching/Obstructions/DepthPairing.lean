/-
The physical-depth obstruction to promoting the flat heavy-core FIFO ledger
to a binary-tree automorphism.

The queue in `Obstructions/ExitLedger.lean` remembers exit occurrences and
their multiplicity, but deliberately forgets their binary addresses.  A
rooted binary-tree automorphism preserves address length.  The first
asymmetric common-core comparison, counter `3` against counter `5`, already
makes the FIFO rule pair a depth-one fresh exit with a depth-three fresh
exit.  Since `ExitLedger.run` never revises an earlier pair, no later
correction word can repair this mismatch.

This is not a counterexample to the desired probabilistic matching theorem.
It is a counterexample to the proposed realization of the nine-phase flat
queue as a block of straight/crossed binary-tree pairings.  A successful
proof has to retain physical level and prefix information, for example in the
existing level-by-level cross-screen grammar.
-/
import GraphMarkovMatching.Obstructions.ExitLedger

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped Classical

/-- A vertex address in the rooted binary tree. -/
abbrev BinaryAddress := List Bool

/-- The action of a finite full binary-tree automorphism on an address.

Addresses longer than the height are left unchanged below the last available
swap.  The only fact used below is length preservation; on addresses of
length at most `n`, this is the usual action of `AutK 1 0 n`. -/
def mapBinaryAddress : (n : ℕ) → AutK 1 0 n → BinaryAddress → BinaryAddress
  | 0, _, u => u
  | _ + 1, _, [] => []
  | n + 1, π, b :: u =>
      (bif π.1 then !b else b) ::
        mapBinaryAddress n (bif b then π.2.2 else π.2.1) u

/-- Rooted binary-tree automorphisms preserve physical depth. -/
theorem mapBinaryAddress_length :
    ∀ (n : ℕ) (π : AutK 1 0 n) (u : BinaryAddress),
      (mapBinaryAddress n π u).length = u.length := by
  intro n
  induction n with
  | zero => intro π u; rfl
  | succ n ih =>
      intro π u
      cases u with
      | nil => rfl
      | cons b u => simp [mapBinaryAddress, ih]

/-- A list of address pairs is induced by one finite binary-tree
automorphism when the second address in every pair is the image of the first. -/
def AutRealizesAddressPairs (n : ℕ) (π : AutK 1 0 n)
    (ps : List (BinaryAddress × BinaryAddress)) : Prop :=
  ∀ p ∈ ps, mapBinaryAddress n π p.1 = p.2

/-- Every automorphism-realized address pair has equal physical depths. -/
theorem AutRealizesAddressPairs.depthCompatible {n : ℕ}
    {π : AutK 1 0 n} {ps : List (BinaryAddress × BinaryAddress)}
    (h : AutRealizesAddressPairs n π ps) :
    ∀ p ∈ ps, p.1.length = p.2.length := by
  intro p hp
  have himage := congrArg List.length (h p hp)
  simpa [mapBinaryAddress_length] using himage

/-- Prefix every address in a frontier by one binary direction. -/
def prefixFrontier (b : Bool) (F : List BinaryAddress) :
    List BinaryAddress := F.map (b :: ·)

/-- The complete fresh frontier of the balanced counter cascade.  This is the
address-valued counterpart of the kernel cases in `varyK` and of the depth
recursion `toFresh`: counters at most `2` emit two fresh children, counter `3`
emits a forced `2` on the left and a fresh child on the right, and larger
counters split into their floor/ceiling halves. -/
def counterFreshFrontier : ℕ → List BinaryAddress
  | 0 => [[false], [true]]
  | 1 => [[false], [true]]
  | 2 => [[false], [true]]
  | 3 => [[false, false], [false, true], [true]]
  | k + 4 =>
      prefixFrontier false (counterFreshFrontier ((k + 4) / 2)) ++
        prefixFrontier true
          (counterFreshFrontier (k + 4 - (k + 4) / 2))
decreasing_by all_goals omega

/-- The fresh frontier produced by the balanced counter-`3` cascade. -/
def counterThreeFreshFrontier : List BinaryAddress :=
  counterFreshFrontier 3

/-- The fresh frontier produced by the balanced counter-`5` cascade. -/
def counterFiveFreshFrontier : List BinaryAddress :=
  counterFreshFrontier 5

@[simp] theorem counterFreshFrontier_three :
    counterFreshFrontier 3 =
      [[false, false], [false, true], [true]] := by
  simp [counterFreshFrontier]

@[simp] theorem counterFreshFrontier_five :
    counterFreshFrontier 5 =
      [[false, false], [false, true],
        [true, false, false], [true, false, true], [true, true]] := by
  simp [counterFreshFrontier, prefixFrontier]

/-- For counter `3`, the physical depths of the address frontier are exactly
the return depths computed by the pre-existing kernel recursion `toFresh`. -/
theorem counterThreeFreshFrontier_depthSet :
    (counterThreeFreshFrontier.map List.length).toFinset = toFresh 3 := by
  rw [toFresh_three]
  ext d
  simp [counterThreeFreshFrontier, or_comm]

/-- The same explicit bridge to the kernel depth recursion for counter `5`. -/
theorem counterFiveFreshFrontier_depthSet :
    (counterFiveFreshFrontier.map List.length).toFinset = toFresh 5 := by
  rw [rareCore_toFresh_five]
  ext d
  simp [counterFiveFreshFrontier, or_comm]

/-- The FIFO allocation of the two concrete cascade frontiers is already in
lag phase `-2`, the phase predicted by the shifted increments
`(3-1)-(5-1)=-2`. -/
theorem counterThreeFive_fifo_phase :
    HeavyQueueInvariant .n2
      (fifoAllocate counterThreeFreshFrontier
        counterFiveFreshFrontier).left
      (fifoAllocate counterThreeFreshFrontier
        counterFiveFreshFrontier).right := by
  simp [HeavyQueueInvariant, counterThreeFreshFrontier,
    counterFiveFreshFrontier, fifoAllocate, heavyLagValue]

/-- The flat FIFO allocation pairs the depth-one fresh exit of counter `3`
with a depth-three fresh exit of counter `5`. -/
theorem counterThreeFive_fifo_not_depthCompatible :
    ¬ ∀ p ∈ (fifoAllocate counterThreeFreshFrontier
        counterFiveFreshFrontier).pairs,
      p.1.length = p.2.length := by
  simp [counterThreeFreshFrontier, counterFiveFreshFrontier, fifoAllocate]

/-- Consequently the first `3`-versus-`5` FIFO allocation is not the action
of any rooted binary-tree automorphism, at any height. -/
theorem counterThreeFive_fifo_not_autRealizable (n : ℕ)
    (π : AutK 1 0 n) :
    ¬ AutRealizesAddressPairs n π
      (fifoAllocate counterThreeFreshFrontier
        counterFiveFreshFrontier).pairs := by
  intro h
  exact counterThreeFive_fifo_not_depthCompatible
    h.depthCompatible

/-- Whole-word execution only appends pairs; it never revises an earlier
FIFO choice. -/
theorem ExitLedger.run_pairs_append {L R : Type} :
    ∀ (Q : ExitLedger L R) (es : List (HeavyExitEvent L R)),
      ∃ tail, (Q.run es).pairs = Q.pairs ++ tail := by
  intro Q es
  induction es generalizing Q with
  | nil => exact ⟨[], by simp [ExitLedger.run]⟩
  | cons e es ih =>
      obtain ⟨tail, htail⟩ := ih (Q.expose e.2)
      refine ⟨(heavyQueueStep Q.left Q.right e.2).pairs ++ tail, ?_⟩
      rw [ExitLedger.run, htail]
      simp [ExitLedger.expose, List.append_assoc]

/-- The concrete ledger immediately after the `3`-versus-`5` frontier
comparison. -/
def counterThreeFiveLedger : ExitLedger BinaryAddress BinaryAddress :=
  let A := fifoAllocate counterThreeFreshFrontier counterFiveFreshFrontier
  ⟨A.pairs, A.left, A.right⟩

theorem counterThreeFiveLedger_phase :
    HeavyQueueInvariant .n2 counterThreeFiveLedger.left
      counterThreeFiveLedger.right := by
  exact counterThreeFive_fifo_phase

/-- No correction word can make the accumulated FIFO pair list
depth-compatible, because the initial bad pair remains in the ledger. -/
theorem counterThreeFive_run_not_depthCompatible
    (es : List (HeavyExitEvent BinaryAddress BinaryAddress)) :
    ¬ ∀ p ∈ (counterThreeFiveLedger.run es).pairs,
      p.1.length = p.2.length := by
  intro hdepth
  obtain ⟨tail, htail⟩ := ExitLedger.run_pairs_append counterThreeFiveLedger es
  have hbad : ([true], [true, false, false]) ∈
      (counterThreeFiveLedger.run es).pairs := by
    rw [htail]
    simp [counterThreeFiveLedger, counterThreeFreshFrontier,
      counterFiveFreshFrontier, fifoAllocate]
  have := hdepth ([true], [true, false, false]) hbad
  norm_num at this

/-- In particular, later lag closure cannot promote this run to one binary
automorphism.  The obstruction is independent of the correction outcomes. -/
theorem counterThreeFive_run_not_autRealizable
    (es : List (HeavyExitEvent BinaryAddress BinaryAddress)) (n : ℕ)
    (π : AutK 1 0 n) :
    ¬ AutRealizesAddressPairs n π (counterThreeFiveLedger.run es).pairs := by
  intro h
  exact counterThreeFive_run_not_depthCompatible es h.depthCompatible

end GraphMarkovMatching
