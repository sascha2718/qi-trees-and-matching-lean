/-
The finite bidirectional screen block for the two-law ledger.

The reachable screen alphabet is the one used by `VaryingTwoLawLedger`.
The Boolean coordinate records the orientation.  Consequently the transfer
matrix is the direct sum of the left-to-right and right-to-left cross-screen
matrices.  A non-power-of-two atom in each target support makes the two blocks
acyclic, hence the whole finite matrix is nilpotent.
-/
import GraphMarkovMatching.Archive.VaryingTwoLawLedger
import GraphMarkovMatching.Closure.Geometric

namespace GraphMarkovMatching

open scoped ENNReal Classical

/-- Forget reachability while retaining membership in the larger live-screen
universe used by the cross-law acyclicity theorem. -/
noncomputable def crossScreenIndexToLive (N : ℕ) :
    {sc // sc ∈ crossScreenIndex N} → {sc // sc ∈ crossLiveScreens N} :=
  fun i => ⟨i.val, (Finset.mem_filter.mp i.property).1⟩

/-- The cross-screen matrix restricted to the reachable `Z/F` alphabet. -/
noncomputable def crossReachN (N : ℕ) (SL SR : Finset ℕ) (CW : ℝ≥0∞) :
    {sc // sc ∈ crossScreenIndex N} →
      {sc // sc ∈ crossScreenIndex N} → ℝ≥0∞ :=
  fun i j => if j.val ∈ crossScreenSucc SL SR i.val then CW else 0

private lemma crossReachN_le (N : ℕ) (SL SR : Finset ℕ) (CW : ℝ≥0∞)
    (i j : {sc // sc ∈ crossScreenIndex N}) :
    crossReachN N SL SR CW i j ≤ CW := by
  by_cases h : j.val ∈ crossScreenSucc SL SR i.val
  · rw [crossReachN, if_pos h]
  · rw [crossReachN, if_neg h]
    exact zero_le

lemma crossReachN_eq_crossN (N : ℕ) (SL SR : Finset ℕ) (CW : ℝ≥0∞)
    (i j : {sc // sc ∈ crossScreenIndex N}) :
    crossReachN N SL SR CW i j =
      crossN N SL SR CW (crossScreenIndexToLive N i)
        (crossScreenIndexToLive N j) := rfl

/-- Restricting the live cross-screen graph cannot create a cycle. -/
theorem crossReachN_acyclic_of_nonpower_right
    {N : ℕ} {SL SR : Finset ℕ} {b : ℕ}
    (hb : b ∈ SR) (hb2 : 2 ≤ b) (hbpow : ¬ IsPowerOfTwo b)
    (CW : ℝ≥0∞) :
    ∀ i, ¬ Relation.TransGen (supportRel (crossReachN N SL SR CW)) i i := by
  intro i hcyc
  apply crossN_acyclic_of_nonpower_right hb hb2 hbpow CW
    (crossScreenIndexToLive N i)
  exact hcyc.lift (crossScreenIndexToLive N) (fun a b hab => by
    simpa [supportRel, crossReachN_eq_crossN] using hab)

/-- The full screen matrix.  It never changes orientation: the `true` block
uses `SL` for the source and `SR` for the target, and the `false` block uses
the reverse order. -/
noncomputable def twoLawN (N : ℕ) (SL SR : Finset ℕ) (CW : ℝ≥0∞) :
    (Bool × {sc // sc ∈ crossScreenIndex N}) →
      (Bool × {sc // sc ∈ crossScreenIndex N}) → ℝ≥0∞ :=
  fun i j => if i.1 = j.1 then
    if i.1 then crossReachN N SL SR CW i.2 j.2
    else crossReachN N SR SL CW i.2 j.2
  else 0

private lemma twoLawN_orientation {N : ℕ} {SL SR : Finset ℕ} {CW : ℝ≥0∞}
    {i j : Bool × {sc // sc ∈ crossScreenIndex N}}
    (h : twoLawN N SL SR CW i j ≠ 0) : i.1 = j.1 := by
  by_contra hij
  exact h (by simp [twoLawN, hij])

/-- A rank for the direct sum, chosen from the appropriate directed block. -/
noncomputable def twoLawRank (N : ℕ) (SL SR : Finset ℕ) (CW : ℝ≥0∞)
    (i : Bool × {sc // sc ∈ crossScreenIndex N}) : ℕ :=
  if i.1 then reachRank (crossReachN N SL SR CW) i.2
  else reachRank (crossReachN N SR SL CW) i.2

private lemma twoLawRank_lt_of_support
    {N : ℕ} {SL SR : Finset ℕ} {bL bR : ℕ}
    (hbL : bL ∈ SL) (hbL2 : 2 ≤ bL) (hbLpow : ¬ IsPowerOfTwo bL)
    (hbR : bR ∈ SR) (hbR2 : 2 ≤ bR) (hbRpow : ¬ IsPowerOfTwo bR)
    (CW : ℝ≥0∞)
    {i j : Bool × {sc // sc ∈ crossScreenIndex N}}
    (hij : twoLawN N SL SR CW i j ≠ 0) :
    twoLawRank N SL SR CW j < twoLawRank N SL SR CW i := by
  have hor := twoLawN_orientation hij
  rcases i with ⟨li, si⟩
  rcases j with ⟨lj, sj⟩
  simp only at hor
  subst lj
  cases li with
  | false =>
      simp only [twoLawRank, Bool.false_eq]
      exact reachRank_lt_of_support
        (crossReachN_acyclic_of_nonpower_right hbL hbL2 hbLpow CW)
        (by simpa [twoLawN] using hij)
  | true =>
      simp only [twoLawRank, ↓reduceIte]
      exact reachRank_lt_of_support
        (crossReachN_acyclic_of_nonpower_right hbR hbR2 hbRpow CW)
        (by simpa [twoLawN] using hij)

private lemma twoLawRank_lt_card
    {N : ℕ} {SL SR : Finset ℕ} {bL bR : ℕ}
    (hbL : bL ∈ SL) (hbL2 : 2 ≤ bL) (hbLpow : ¬ IsPowerOfTwo bL)
    (hbR : bR ∈ SR) (hbR2 : 2 ≤ bR) (hbRpow : ¬ IsPowerOfTwo bR)
    (CW : ℝ≥0∞)
    (i : Bool × {sc // sc ∈ crossScreenIndex N}) :
    twoLawRank N SL SR CW i <
      Fintype.card (Bool × {sc // sc ∈ crossScreenIndex N}) := by
  have hpos : 0 < Fintype.card {sc // sc ∈ crossScreenIndex N} :=
    Fintype.card_pos_iff.mpr ⟨i.2⟩
  have hcard : Fintype.card (Bool × {sc // sc ∈ crossScreenIndex N}) =
      2 * Fintype.card {sc // sc ∈ crossScreenIndex N} := by
    simp [Fintype.card_prod]
  cases hi : i.1 with
  | false =>
      have hlt := reachRank_lt_card
        (crossReachN_acyclic_of_nonpower_right (SL := SR) (SR := SL)
          hbL hbL2 hbLpow CW) i.2
      rw [twoLawRank, hi, if_neg (by simp)]
      rw [hcard]
      omega
  | true =>
      have hlt := reachRank_lt_card
        (crossReachN_acyclic_of_nonpower_right (SL := SL) (SR := SR)
          hbR hbR2 hbRpow CW) i.2
      rw [twoLawRank, hi, if_pos (by simp)]
      rw [hcard]
      omega

/-- **Bidirectional finite nilpotence.**  One non-power-of-two atom in each
law kills the block in which that law is the target. -/
theorem twoLawN_nilpotent
    {N : ℕ} {SL SR : Finset ℕ} {bL bR : ℕ}
    (hbL : bL ∈ SL) (hbL2 : 2 ≤ bL) (hbLpow : ¬ IsPowerOfTwo bL)
    (hbR : bR ∈ SR) (hbR2 : 2 ≤ bR) (hbRpow : ¬ IsPowerOfTwo bR)
    (CW : ℝ≥0∞) :
    ∀ x, (mulVec (twoLawN N SL SR CW))^[
        Fintype.card (Bool × {sc // sc ∈ crossScreenIndex N})] x =
      fun _ => 0 := by
  exact nilpotent_of_rank (twoLawN N SL SR CW)
    (twoLawRank N SL SR CW)
    (Fintype.card (Bool × {sc // sc ∈ crossScreenIndex N}))
    (fun _ _ h => twoLawRank_lt_of_support hbL hbL2 hbLpow
      hbR hbR2 hbRpow CW h)
    (twoLawRank_lt_card hbL hbL2 hbLpow hbR hbR2 hbRpow CW)

/-- The positive exponent used by the screened closure engine. -/
theorem twoLawN_nilpotent_succ
    {N : ℕ} {SL SR : Finset ℕ} {bL bR : ℕ}
    (hbL : bL ∈ SL) (hbL2 : 2 ≤ bL) (hbLpow : ¬ IsPowerOfTwo bL)
    (hbR : bR ∈ SR) (hbR2 : 2 ≤ bR) (hbRpow : ¬ IsPowerOfTwo bR)
    (CW : ℝ≥0∞) :
    ∀ x, (mulVec (twoLawN N SL SR CW))^[
        Fintype.card (Bool × {sc // sc ∈ crossScreenIndex N}) + 1] x =
      fun _ => 0 := by
  intro x
  rw [Function.iterate_succ_apply]
  exact twoLawN_nilpotent hbL hbL2 hbLpow hbR hbR2 hbRpow CW
    (mulVec (twoLawN N SL SR CW) x)

/-- Uniform row bound for the bidirectional reachable matrix. -/
lemma twoLawN_row_sum_le (N : ℕ) (SL SR : Finset ℕ) (CW : ℝ≥0∞)
    (i : Bool × {sc // sc ∈ crossScreenIndex N}) :
    ∑ j, twoLawN N SL SR CW i j ≤ CW * (crossScreenIndex N).card := by
  calc
    ∑ j, twoLawN N SL SR CW i j
        ≤ ∑ j : Bool × {sc // sc ∈ crossScreenIndex N},
            if i.1 = j.1 then CW else 0 := by
          refine Finset.sum_le_sum fun j _ => ?_
          by_cases hor : i.1 = j.1
          · rw [if_pos hor]
            rw [twoLawN, if_pos hor]
            cases hi : i.1
            · simpa [hi] using crossReachN_le N SR SL CW i.2 j.2
            · simpa [hi] using crossReachN_le N SL SR CW i.2 j.2
          · simp [twoLawN, hor]
    _ = CW * (crossScreenIndex N).card := by
          rcases i with ⟨li, si⟩
          cases li <;> simp [Fintype.sum_prod_type, mul_comm]

end GraphMarkovMatching
