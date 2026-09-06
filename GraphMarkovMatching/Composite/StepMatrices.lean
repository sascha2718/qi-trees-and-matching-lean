/-
The concrete screen-ledger input, part two of six: the common matrix `cNc` and the priced
matrix `cMp` with their budgets, the rank, reachability of the moved letters, the
dictionary images of the moves, the screen embedding, and the nilpotence of the common
block through block diagonality (`cNc_nilpotent`, `cGood_nilpotent`).  The descended pair
screens follow in `StepRows`.
-/
import GraphMarkovMatching.Composite.StepLetters

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type}

/-! ### The matrices -/

section Matrices

variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ)

/-- The good gate of a coordinate: jointly reachable at some common
level and off the fresh diagonal. -/
def cNGate {N : ℕ} (i : cIdx N) : Prop :=
  (∃ n, cGateR exc1 exc2 ν1 ν2 i.1 n (cRawS i) (cRawZ i) (cRawT i))
    ∧ ¬(cRawS i = none ∧ none ∈ cRawZ i)

/-- The common target set of a coordinate: a source component, the
whole lifted zero-list successor, and a common tilt move. -/
noncomputable def cNTgt {N : ℕ} (i : cIdx N) : Finset (cIdx N) :=
  ((cLiftB N (cSrcC (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1) (cRawS i)))
      ×ˢ cLiftO N (cTiltC (cExcO exc1 exc2 (!i.1)) (cRawT i))).image
    fun p => (i.1, p.1,
      cLiftB N (cZSuccR (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
        (cRawZ i)), p.2)

/-- The exceptional-entrance target set. -/
noncomputable def cETgt {N : ℕ} (i : cIdx N) : Finset (cIdx N) :=
  ((cLiftB N (cSrcE (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1) (cRawS i)))
      ×ˢ cLiftO N (cTiltC (cExcO exc1 exc2 (!i.1)) (cRawT i))).image
    fun p => (i.1, p.1,
      cLiftB N (cZSuccR (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
        (cRawZ i)), p.2)

/-- The priced tilt target set with a common cell move: these moves
carry the uniform tilt-renewal weight and ride in the nilpotent common
block, exactly as the one-law ledger keeps the tilt-renewal weight
inside the common row constant `C_W` (`thm:geom`,
`thm:composite-ledger`). -/
noncomputable def cPTgtC {N : ℕ} (i : cIdx N) : Finset (cIdx N) :=
  ((cLiftB N (cSrcC (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1) (cRawS i)))
      ×ˢ cLiftO N (cTiltP (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
        (cRawT i))).image
    fun p => (i.1, p.1,
      cLiftB N (cZSuccR (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
        (cRawZ i)), p.2)

/-- The priced tilt target set with an exceptional entrance cell move:
the only priced tilt moves kept in the rare block. -/
noncomputable def cPTgtE {N : ℕ} (i : cIdx N) : Finset (cIdx N) :=
  ((cLiftB N (cSrcE (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1) (cRawS i)))
      ×ˢ cLiftO N (cTiltP (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
        (cRawT i))).image
    fun p => (i.1, p.1,
      cLiftB N (cZSuccR (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
        (cRawZ i)), p.2)

/-- **The common matrix**: weight `4` on gated common moves and weight
`4·RT·T` on gated priced tilt moves with a common cell move; the
tilt-renewal weight sits in the nilpotent block. -/
noncomputable def cNc (RTT : ℝ≥0∞) {N : ℕ} (i j : cIdx N) : ℝ≥0∞ :=
  (if cNGate exc1 exc2 ν1 ν2 i ∧ cNGate exc1 exc2 ν1 ν2 j
      ∧ j ∈ cNTgt exc1 exc2 K1 K2 i then 4 else 0)
    + (if cNGate exc1 exc2 ν1 ν2 i ∧ cNGate exc1 exc2 ν1 ν2 j
        ∧ j ∈ cPTgtC exc1 exc2 K1 K2 i then 4 * RTT else 0)

/-- **The raw priced weights**: only the exceptional-entrance moves,
the unit entrances at weight `4·eM` and the priced entrances at weight
`4·eM·RT·T`; every rare entry is proportional to the exceptional
mass. -/
noncomputable def cMpw (eM RTT : ℝ≥0∞) {N : ℕ} (i j : cIdx N) : ℝ≥0∞ :=
  (if j ∈ cETgt exc1 exc2 K1 K2 i then 4 * eM else 0)
    + (if j ∈ cPTgtE exc1 exc2 K1 K2 i then 4 * eM * RTT else 0)

/-- **The priced matrix**: the raw priced weights at price `χ0⁻¹`. -/
noncomputable def cMp (χ0 eM RTT : ℝ≥0∞) {N : ℕ} (i j : cIdx N) :
    ℝ≥0∞ :=
  χ0⁻¹ * cMpw exc1 exc2 K1 K2 eM RTT i j

private lemma sum_ite_mem_le {ι : Type} [Fintype ι] (s : Finset ι)
    (w : ℝ≥0∞) :
    (∑ j, if j ∈ s then w else 0) ≤ s.card * w := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul]

lemma cNTgt_card_le {N : ℕ} (i : cIdx N) :
    (cNTgt exc1 exc2 K1 K2 i).card ≤ 4 * cMx K1 K2 := by
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product]
  have h1 := le_trans (cLiftB_card_le (N := N) _)
    (cSrcC_card_le (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1) (cRawS i))
  have h2 := le_trans (cLiftO_card_le N _)
    (cTiltC_card_le (cExcO exc1 exc2 (!i.1)) (cRawT i))
  have hK := cKO_card_le_cMx K1 K2 i.1
  have hone := one_le_cMx K1 K2
  calc _ ≤ (2 * max (cKO K1 K2 i.1).card 1) * 2 :=
        Nat.mul_le_mul h1 h2
    _ ≤ 4 * cMx K1 K2 := by
        have : max (cKO K1 K2 i.1).card 1 ≤ cMx K1 K2 :=
          max_le hK hone
        omega

lemma cETgt_card_le {N : ℕ} (i : cIdx N) :
    (cETgt exc1 exc2 K1 K2 i).card ≤ 4 * cMx K1 K2 := by
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product]
  have h1 := le_trans (cLiftB_card_le (N := N) _)
    (cSrcE_card_le (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1) (cRawS i))
  have h2 := le_trans (cLiftO_card_le N _)
    (cTiltC_card_le (cExcO exc1 exc2 (!i.1)) (cRawT i))
  have hK := cKO_card_le_cMx K1 K2 i.1
  have hone := one_le_cMx K1 K2
  calc _ ≤ (2 * max (cKO K1 K2 i.1).card 1) * 2 :=
        Nat.mul_le_mul h1 h2
    _ ≤ 4 * cMx K1 K2 := by
        have : max (cKO K1 K2 i.1).card 1 ≤ cMx K1 K2 :=
          max_le hK hone
        omega

lemma cPTgtC_card_le {N : ℕ} (i : cIdx N) :
    (cPTgtC exc1 exc2 K1 K2 i).card ≤ 4 * (cMx K1 K2 * cMx K1 K2) := by
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product]
  have h1 := le_trans (cLiftB_card_le (N := N) _)
    (cSrcC_card_le (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1) (cRawS i))
  have h2 := le_trans (cLiftO_card_le N _)
    (cTiltP_card_le (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
      (cRawT i))
  have hK1 : max (cKO K1 K2 i.1).card 1 ≤ cMx K1 K2 :=
    max_le (cKO_card_le_cMx K1 K2 i.1) (one_le_cMx K1 K2)
  have hK2 : max (cKO K1 K2 (!i.1)).card 1 ≤ cMx K1 K2 :=
    max_le (cKO_card_le_cMx K1 K2 (!i.1)) (one_le_cMx K1 K2)
  calc _ ≤ (2 * max (cKO K1 K2 i.1).card 1)
        * (2 * max (cKO K1 K2 (!i.1)).card 1) := Nat.mul_le_mul h1 h2
    _ ≤ 4 * (cMx K1 K2 * cMx K1 K2) := by
        have := Nat.mul_le_mul hK1 hK2
        nlinarith

lemma cPTgtE_card_le {N : ℕ} (i : cIdx N) :
    (cPTgtE exc1 exc2 K1 K2 i).card ≤ 4 * (cMx K1 K2 * cMx K1 K2) := by
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product]
  have h1 := le_trans (cLiftB_card_le (N := N) _)
    (cSrcE_card_le (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1) (cRawS i))
  have h2 := le_trans (cLiftO_card_le N _)
    (cTiltP_card_le (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
      (cRawT i))
  have hK1 : max (cKO K1 K2 i.1).card 1 ≤ cMx K1 K2 :=
    max_le (cKO_card_le_cMx K1 K2 i.1) (one_le_cMx K1 K2)
  have hK2 : max (cKO K1 K2 (!i.1)).card 1 ≤ cMx K1 K2 :=
    max_le (cKO_card_le_cMx K1 K2 (!i.1)) (one_le_cMx K1 K2)
  calc _ ≤ (2 * max (cKO K1 K2 i.1).card 1)
        * (2 * max (cKO K1 K2 (!i.1)).card 1) := Nat.mul_le_mul h1 h2
    _ ≤ 4 * (cMx K1 K2 * cMx K1 K2) := by
        have := Nat.mul_le_mul hK1 hK2
        nlinarith

/-- The common row budget `16·mx + 16·mx²·RT·T` (the row sum `C_W` of
`thm:composite-ledger`, carrying the tilt-renewal weight as in the
one-law `C_W`). -/
noncomputable def cNcBudget (RTT : ℝ≥0∞) (mx : ℕ) : ℝ≥0∞ :=
  16 * mx + 16 * (mx * mx) * RTT

/-- The common row bound (`common_row` of `ScreenLedgerInput` at
`C ≥ cNcBudget (RT·T) cMx`). -/
lemma cNc_row_le (RTT : ℝ≥0∞) {N : ℕ} (i : cIdx N) :
    ∑ j, cNc exc1 exc2 ν1 ν2 K1 K2 RTT i j
      ≤ cNcBudget RTT (cMx K1 K2) := by
  rw [cNcBudget]
  calc ∑ j, cNc exc1 exc2 ν1 ν2 K1 K2 RTT i j
      ≤ ∑ j, ((if j ∈ cNTgt exc1 exc2 K1 K2 i then (4 : ℝ≥0∞) else 0)
          + if j ∈ cPTgtC exc1 exc2 K1 K2 i then 4 * RTT else 0) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [cNc]
        refine add_le_add ?_ ?_
        · by_cases hj : cNGate exc1 exc2 ν1 ν2 i
              ∧ cNGate exc1 exc2 ν1 ν2 j ∧ j ∈ cNTgt exc1 exc2 K1 K2 i
          · rw [if_pos hj, if_pos hj.2.2]
          · rw [if_neg hj]
            exact zero_le
        · by_cases hj : cNGate exc1 exc2 ν1 ν2 i
              ∧ cNGate exc1 exc2 ν1 ν2 j ∧ j ∈ cPTgtC exc1 exc2 K1 K2 i
          · rw [if_pos hj, if_pos hj.2.2]
          · rw [if_neg hj]
            exact zero_le
    _ = (∑ j, if j ∈ cNTgt exc1 exc2 K1 K2 i then (4 : ℝ≥0∞) else 0)
        + ∑ j, if j ∈ cPTgtC exc1 exc2 K1 K2 i then 4 * RTT else 0 :=
        Finset.sum_add_distrib
    _ ≤ (cNTgt exc1 exc2 K1 K2 i).card * 4
        + (cPTgtC exc1 exc2 K1 K2 i).card * (4 * RTT) :=
        add_le_add (sum_ite_mem_le _ _) (sum_ite_mem_le _ _)
    _ ≤ ((4 * cMx K1 K2 : ℕ) : ℝ≥0∞) * 4
        + ((4 * (cMx K1 K2 * cMx K1 K2) : ℕ) : ℝ≥0∞) * (4 * RTT) := by
        refine add_le_add (mul_le_mul_left ?_ _) (mul_le_mul_left ?_ _)
        · exact_mod_cast cNTgt_card_le exc1 exc2 K1 K2 i
        · exact_mod_cast cPTgtC_card_le exc1 exc2 K1 K2 i
    _ = 16 * (cMx K1 K2 : ℝ≥0∞)
        + 16 * ((cMx K1 K2 : ℝ≥0∞) * cMx K1 K2) * RTT := by
        push_cast
        ring

/-- The raw priced budget entering the entrance-price smallness:
`16·mx·eM + 16·mx²·eM·RT·T`, proportional to the exceptional mass. -/
noncomputable def cMpBudget (eM RTT : ℝ≥0∞) (mx : ℕ) : ℝ≥0∞ :=
  16 * mx * eM + 16 * (mx * mx) * (eM * RTT)

/-- The raw priced row bound. -/
lemma cMpw_row_le (eM RTT : ℝ≥0∞) {N : ℕ} (i : cIdx N) :
    ∑ j, cMpw exc1 exc2 K1 K2 eM RTT i j
      ≤ cMpBudget eM RTT (cMx K1 K2) := by
  rw [cMpBudget]
  calc ∑ j, cMpw exc1 exc2 K1 K2 eM RTT i j
      = (∑ j, if j ∈ cETgt exc1 exc2 K1 K2 i then 4 * eM else 0)
        + ∑ j, if j ∈ cPTgtE exc1 exc2 K1 K2 i then 4 * eM * RTT
            else 0 := by
        rw [← Finset.sum_add_distrib]
        rfl
    _ ≤ (cETgt exc1 exc2 K1 K2 i).card * (4 * eM)
        + (cPTgtE exc1 exc2 K1 K2 i).card * (4 * eM * RTT) :=
        add_le_add (sum_ite_mem_le _ _) (sum_ite_mem_le _ _)
    _ ≤ ((4 * cMx K1 K2 : ℕ) : ℝ≥0∞) * (4 * eM)
        + ((4 * (cMx K1 K2 * cMx K1 K2) : ℕ) : ℝ≥0∞)
          * (4 * eM * RTT) := by
        refine add_le_add (mul_le_mul_left ?_ _) (mul_le_mul_left ?_ _)
        · exact_mod_cast cETgt_card_le exc1 exc2 K1 K2 i
        · exact_mod_cast cPTgtE_card_le exc1 exc2 K1 K2 i
    _ = 16 * (cMx K1 K2 : ℝ≥0∞) * eM
        + 16 * ((cMx K1 K2 : ℝ≥0∞) * cMx K1 K2) * (eM * RTT) := by
        push_cast
        ring

/-- The priced row bound (`priced_row` of `ScreenLedgerInput`) under
the affordability budget. -/
lemma cMp_row_le (χ0 eM RTT C : ℝ≥0∞) (hχ0 : χ0 ≠ 0) (hχ1 : χ0 ≤ 1)
    (hafford : cMpBudget eM RTT (cMx K1 K2) ≤ χ0 * C) {N : ℕ}
    (i : cIdx N) :
    ∑ j, cMp exc1 exc2 K1 K2 χ0 eM RTT i j ≤ C := by
  have hχt : χ0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hχ1
  calc ∑ j, cMp exc1 exc2 K1 K2 χ0 eM RTT i j
      = χ0⁻¹ * ∑ j, cMpw exc1 exc2 K1 K2 eM RTT i j := by
        simp only [cMp]
        rw [← Finset.mul_sum]
    _ ≤ χ0⁻¹ * (χ0 * C) :=
        mul_le_mul_right
          (le_trans (cMpw_row_le exc1 exc2 K1 K2 eM RTT i) hafford) _
    _ = C := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hχ0 hχt, one_mul]

/-- The priced entries recover the raw weights. -/
lemma chi0_mul_cMp (χ0 eM RTT : ℝ≥0∞) (hχ0 : χ0 ≠ 0) (hχ1 : χ0 ≤ 1)
    {N : ℕ} (i j : cIdx N) :
    χ0 * cMp exc1 exc2 K1 K2 χ0 eM RTT i j
      = cMpw exc1 exc2 K1 K2 eM RTT i j := by
  have hχt : χ0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hχ1
  rw [cMp, ← mul_assoc, ENNReal.mul_inv_cancel hχ0 hχt, one_mul]

end Matrices

/-! ### The rank -/

/-- The orientation-block payload of the index. -/
abbrev cPay (N : ℕ) : Type := cLB N × Finset (cLB N) × Option (cLB N)

/-- The ledger rank: the payload cardinality. -/
noncomputable def cRank (N : ℕ) : ℕ := Fintype.card (cPay N)

lemma cRank_pos (N : ℕ) : 0 < cRank N :=
  Fintype.card_pos_iff.mpr
    ⟨⟨⟨none, none_mem_cLetterBox N⟩, ∅, none⟩⟩

/-- **`eq:composite-cardinals`, the rank**: the ledger rank is exactly
`r = n_A · 2^{n_A} · (n_A + 1)` at `n_A = (N+1)³ + N + 2`. -/
lemma cRank_eq (N : ℕ) :
    cRank N = ((N + 1) ^ 3 + N + 2) * 2 ^ ((N + 1) ^ 3 + N + 2)
      * ((N + 1) ^ 3 + N + 2 + 1) := by
  have hcard : Fintype.card (cLB N) = (N + 1) ^ 3 + N + 2 := by
    rw [← cLetterBox_card N]
    exact Fintype.card_coe _
  rw [cRank, Fintype.card_prod, Fintype.card_prod, Fintype.card_finset,
    Fintype.card_option, hcard]
  ring

/-! ### Reachability of the moved letters -/

section Reach

variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ) (N : ℕ)

lemma cReachO_spawn {o : Bool} {n : ℕ} {l m : Option CtrC}
    (hl : cReachO exc1 exc2 ν1 ν2 o n l)
    (hsp : cSpawn (cExcO exc1 exc2 o) (cNuO ν1 ν2 o) l m) :
    cReachO exc1 exc2 ν1 ν2 o (n + 1) m := by
  cases o with
  | false => exact ⟨l, hl, hsp⟩
  | true => exact ⟨l, hl, hsp⟩

/-- Reachable letters of an orientation are boundedly tame. -/
lemma cReachO_cTameB
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hch1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 → exc1 k = none → k ≤ N)
    (hdeclB1 : ∀ k p, exc1 k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (hch2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 → exc2 k = none → k ≤ N)
    (hdeclB2 : ∀ k p, exc2 k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (o : Bool) {n : ℕ} {l : Option CtrC}
    (hl : cReachO exc1 exc2 ν1 ν2 o n l) :
    cTameB (cExcO exc1 exc2 o) N l := by
  cases o with
  | false =>
      exact cReach_cTameB exc1 ν1 N (fun j hj => (hN j hj).1) hch1
        hdeclB1 hl
  | true =>
      exact cReach_cTameB exc2 ν2 N (fun j hj => (hN j hj).2) hch2
        hdeclB2 hl

/-- Member counters spawn their components reachably. -/
lemma cMsL_comp_reach {o : Bool} {n : ℕ} {Z : Finset (Option CtrC)}
    (hZ : ∀ l ∈ Z, cReachO exc1 exc2 ν1 ν2 (!o) n l)
    (hsup : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    {c : CtrC} (hc : c ∈ cMsL (cKO K1 K2 (!o)) Z) {m : Option CtrC}
    (hm : m = cComp0 (cExcO exc1 exc2 (!o)) c
      ∨ m = cComp1 (cExcO exc1 exc2 (!o)) c) :
    cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) m := by
  rcases mem_cMsL.mp hc with hz | ⟨hz, k, hk, rfl⟩
  · exact cReachO_spawn exc1 exc2 ν1 ν2 (hZ _ hz) hm
  · exact cReachO_spawn exc1 exc2 ν1 ν2 (hZ _ hz)
      ⟨k, (hsup k).mpr hk, hm⟩

/-- Zero-list successor letters stay reachable. -/
lemma cZSuccR_reach {o : Bool} {n : ℕ} {Z : Finset (Option CtrC)}
    (hZ : ∀ l ∈ Z, cReachO exc1 exc2 ν1 ν2 (!o) n l)
    (hsup : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o)) :
    ∀ l' ∈ cZSuccR (cExcO exc1 exc2 (!o)) (cKO K1 K2 (!o)) Z,
      cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l' := by
  intro l' hl'
  obtain ⟨c, hc, hor⟩ := mem_cZSuccR.mp hl'
  exact cMsL_comp_reach exc1 exc2 ν1 ν2 K1 K2 hZ hsup hc hor

end Reach

/-! ### The dictionary images of the moves -/

/-- The dictionary image of a common counter's components is its
successor set. -/
lemma cDict_pair_comps_ord {exc : ℕ → Option (ℕ × ℕ)} {j : ℕ}
    (hj : exc j = none) :
    ({cDict (cComp0 exc (CtrC.ord j)), cDict (cComp1 exc (CtrC.ord j))}
        : Finset Letter) = succZ j := by
  rw [cComp0_ord_none hj, cComp1_ord_none hj]
  rcases Nat.lt_or_ge j 3 with h2 | h3
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      succZ_le_two (by omega), cDict_none]
    exact Finset.insert_eq_self.mpr (Finset.mem_singleton_self _)
  · rcases Nat.lt_or_ge j 4 with h4 | h4
    · rw [if_neg (by omega), if_pos (by omega : j = 3),
        if_neg (by omega), cDict_ord, cDict_none,
        (by omega : j = 3), succZ_three]
    · rw [if_pos h4, if_pos h4, cDict_ord, cDict_ord, succZ_of_ge h4]

/-- The dictionary image of a marker's components is its successor
set. -/
lemma cDict_pair_markComp (a b i : ℕ) :
    ({cDict (markComp0 a b i), cDict (markComp1 a b i)}
        : Finset Letter) = succM a b i := by
  rcases Nat.lt_or_ge (val a i) 3 with h2 | h3
  · rw [markComp0, if_neg (by omega), if_neg (by omega),
      markComp1, if_neg (by omega), if_neg (by omega),
      cDict_ord, cDict_none, succM_le_two (by omega)]
  · rcases Nat.lt_or_ge (val a i) 4 with h4 | h4
    · rw [markComp0, if_neg (by omega), if_pos (by omega : val a i = 3),
        markComp1, if_neg (by omega), if_pos (by omega : val a i = 3),
        cDict_ord, cDict_ord, succM_three (by omega : val a i = 3)]
    · rw [markComp0, if_pos h4, markComp1, if_pos h4,
        cDict_mark, cDict_ord, succM_of_ge h4]

/-- The dictionary image of the raw successor set of a tame member
letter is its grammar successor set. -/
lemma cDict_image_cSuccRaw {exc : ℕ → Option (ℕ × ℕ)} {ν : PMF ℕ}
    {Kf S : Finset ℕ} {Egr : Finset (ℕ × ℕ)} {N : ℕ}
    (hsup : ∀ k, (ν k : ℝ≥0∞) ≠ 0 ↔ k ∈ Kf)
    (hS : ∀ k, k ∈ S ↔ ((ν k : ℝ≥0∞) ≠ 0 ∧ exc k = none))
    (hEg : ∀ p, p ∈ Egr ↔ ∃ z, (ν z : ℝ≥0∞) ≠ 0 ∧ exc z = some p)
    {l : Option CtrC} (hl : cTameB exc N l) :
    (cSuccRaw exc Kf l).image cDict = succ S Egr (cDict l) := by
  cases l with
  | some c =>
      cases c with
      | ord j =>
          rw [cSuccRaw, cDict_ord, succ_Z, Finset.image_insert,
            Finset.image_singleton]
          exact cDict_pair_comps_ord hl.2
      | mark a b i =>
          rw [cSuccRaw, cDict_mark, succ_M, Finset.image_insert,
            Finset.image_singleton]
          exact cDict_pair_markComp a b i
  | none =>
      rw [cSuccRaw, cDict_none, succ_F]
      ext x
      rw [Finset.biUnion_image, Finset.mem_biUnion, Finset.mem_union]
      constructor
      · rintro ⟨k, hk, hx⟩
        rw [Finset.image_insert, Finset.image_singleton] at hx
        rcases hexc : exc k with _ | p
        · refine Or.inl (Finset.mem_biUnion.mpr ⟨k, ?_, ?_⟩)
          · exact (hS k).mpr ⟨(hsup k).mpr hk, hexc⟩
          · rw [cDict_pair_comps_ord hexc] at hx
            exact hx
        · refine Or.inr (Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩)
          · exact (hEg p).mpr ⟨k, (hsup k).mpr hk, hexc⟩
          · rw [cComp0_ord_some hexc, cComp1_ord_some hexc,
              cDict_pair_markComp p.1 p.2 0] at hx
            exact hx
      · rintro (hx | hx)
        · obtain ⟨k, hkS, hx⟩ := Finset.mem_biUnion.mp hx
          obtain ⟨hν, hexc⟩ := (hS k).mp hkS
          refine ⟨k, (hsup k).mp hν, ?_⟩
          rw [Finset.image_insert, Finset.image_singleton,
            cDict_pair_comps_ord hexc]
          exact hx
        · obtain ⟨p, hpE, hx⟩ := Finset.mem_biUnion.mp hx
          obtain ⟨z, hν, hexc⟩ := (hEg p).mp hpE
          refine ⟨z, (hsup z).mp hν, ?_⟩
          rw [Finset.image_insert, Finset.image_singleton,
            cComp0_ord_some hexc, cComp1_ord_some hexc,
            cDict_pair_markComp p.1 p.2 0]
          exact hx

/-- Common source moves land in the exceptional-free successor set of
the source cell. -/
lemma cDict_cSrcC_mem_succ {exc : ℕ → Option (ℕ × ℕ)} {ν : PMF ℕ}
    {Kf S : Finset ℕ} {N : ℕ}
    (hsup : ∀ k, (ν k : ℝ≥0∞) ≠ 0 ↔ k ∈ Kf)
    (hS : ∀ k, k ∈ S ↔ ((ν k : ℝ≥0∞) ≠ 0 ∧ exc k = none))
    {s : Option CtrC} (hs : cTameB exc N s)
    {s' : Option CtrC} (hs' : s' ∈ cSrcC exc Kf s) :
    cDict s' ∈ succ S ∅ (cDict s) := by
  cases s with
  | some c =>
      have hpair : cDict s' ∈ ({cDict (cComp0 exc c), cDict (cComp1 exc c)}
          : Finset Letter) := by
        rw [cSrcC] at hs'
        rcases Finset.mem_insert.mp hs' with rfl | hs'
        · exact Finset.mem_insert_self _ _
        · rw [Finset.mem_singleton.mp hs']
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      cases c with
      | ord j =>
          rw [cDict_ord, succ_Z]
          rw [cDict_pair_comps_ord hs.2] at hpair
          exact hpair
      | mark a b i =>
          rw [cDict_mark, succ_M]
          rw [cComp0_mark, cComp1_mark, cDict_pair_markComp a b i]
            at hpair
          exact hpair
  | none =>
      rw [cSrcC, Finset.mem_biUnion] at hs'
      obtain ⟨k, hk, hs'⟩ := hs'
      obtain ⟨hkK, hexc⟩ := Finset.mem_filter.mp hk
      rw [cDict_none, succ_F]
      refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨k, (hS k).mpr ⟨(hsup k).mpr hkK, hexc⟩, ?_⟩)
      rw [← cDict_pair_comps_ord hexc]
      rcases Finset.mem_insert.mp hs' with rfl | hs'
      · exact Finset.mem_insert_self _ _
      · rw [Finset.mem_singleton.mp hs']
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-! ### The screen embedding and the nilpotence of the common block -/

/-- The dictionary sends exactly the fresh letter to `F`. -/
lemma cDict_eq_F_iff {l : Option CtrC} :
    cDict l = Letter.F ↔ l = none := by
  cases l with
  | none => simp [cDict_none]
  | some c => cases c <;> simp [cDict]

/-- The screen embedding of a payload: the dictionary image of the
source letter and of the zero-list letters; the tilt rides along. -/
noncomputable def cEmb (N : ℕ) (p : cPay N) : Screen :=
  ⟨cDict p.1.1, (p.2.1.image Subtype.val).image cDict⟩

section Nilpotent

variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (N : ℕ)

/-- The per-orientation declared pairs. -/
def cEgO : Bool → Finset (ℕ × ℕ)
  | false => E1
  | true => E2

@[simp] lemma cEgO_false : cEgO E1 E2 false = E1 := rfl
@[simp] lemma cEgO_true : cEgO E1 E2 true = E2 := rfl

/-- The common support is charged and common on side 2 as well, through
the two-directional support pack. -/
lemma cS_char2
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0) :
    ∀ k, k ∈ S ↔ ((ν2 k : ℝ≥0∞) ≠ 0 ∧ exc2 k = none) := by
  intro k
  rw [hS1 k]
  constructor
  · rintro ⟨hν, hexc⟩
    obtain ⟨hkN, hν2⟩ := hcharged1 k hν hexc
    exact ⟨hν2, (hN k hkN).2⟩
  · rintro ⟨hν, hexc⟩
    obtain ⟨hkN, hν1⟩ := hcharged2 k hν hexc
    exact ⟨hν1, (hN k hkN).1⟩

section Dispatch

variable (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
variable (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
variable (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
variable (hdeclN1 : ∀ k p, exc1 k = some p →
  p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
variable (hdeclN2 : ∀ k p, exc2 k = some p →
  p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
variable (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
variable (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
variable (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
variable (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
variable (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
variable (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
variable (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)

include hN hcharged1 hcharged2 hS1 in
lemma cS_charO (o : Bool) :
    ∀ k, k ∈ S ↔ ((cNuO ν1 ν2 o k : ℝ≥0∞) ≠ 0
      ∧ cExcO exc1 exc2 o k = none) := by
  cases o with
  | false => exact hS1
  | true => exact cS_char2 exc1 exc2 ν1 ν2 S N hS1 hN hcharged1 hcharged2

include hsup1 hsup2 in
lemma cSupO (o : Bool) :
    ∀ k, (cNuO ν1 ν2 o k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 o := by
  cases o with
  | false => exact hsup1
  | true => exact hsup2

include hEg1 hEg2 in
lemma cEgO_char (o : Bool) :
    ∀ p, p ∈ cEgO E1 E2 o ↔ ∃ z, (cNuO ν1 ν2 o z : ℝ≥0∞) ≠ 0
      ∧ cExcO exc1 exc2 o z = some p := by
  cases o with
  | false => exact hEg1
  | true => exact hEg2

include hN in
lemma cHNO (o : Bool) : ∀ j, j ≤ N → cExcO exc1 exc2 o j = none := by
  cases o with
  | false => exact fun j hj => (hN j hj).1
  | true => exact fun j hj => (hN j hj).2

include hdeclN1 hdeclN2 in
lemma cHDeclBO (o : Bool) : ∀ k p, cExcO exc1 exc2 o k = some p →
    p.1 ≤ N ∧ p.2 ≤ N := by
  cases o with
  | false => exact fun k p hp => ⟨(hdeclN1 k p hp).1, (hdeclN1 k p hp).2.1⟩
  | true => exact fun k p hp => ⟨(hdeclN2 k p hp).1, (hdeclN2 k p hp).2.1⟩

include hdecl1 hdecl2 in
lemma cHDeclCO (o : Bool) : ∀ k p, cExcO exc1 exc2 o k = some p →
    cNuO ν1 ν2 o p.1 ≠ 0 ∧ cNuO ν1 ν2 o p.2 ≠ 0 := by
  cases o with
  | false => exact hdecl1
  | true => exact hdecl2

include hN hdecl1 hdecl2 hdeclN1 hdeclN2 hcharged1 hcharged2 hS1 hEg1
  hEg2 in
lemma cESO (o : Bool) :
    ∀ p ∈ cEgO E1 E2 o, p.1 ∈ S ∧ p.2 ∈ S := by
  refine cEgr_subset_support (cExcO exc1 exc2 o) (cNuO ν1 ν2 o) N S
    (cEgO E1 E2 o)
    (cHNO exc1 exc2 N hN o) ?_ ?_ ?_ ?_
  · exact cHDeclBO exc1 exc2 ν1 ν2 N hdeclN1 hdeclN2 o
  · exact cHDeclCO exc1 exc2 ν1 ν2 hdecl1 hdecl2 o
  · exact cS_charO exc1 exc2 ν1 ν2 S N hN hcharged1 hcharged2 hS1 o
  · exact cEgO_char exc1 exc2 ν1 ν2 E1 E2 hEg1 hEg2 o

include hN hdecl1 hdecl2 hdeclN1 hdeclN2 hcharged1 hcharged2 hS1 hEg1
  hEg2 in
/-- Aligned anchoring in either orientation. -/
lemma cAligned_screenAnchoredO (o : Bool) {n : ℕ} {l1 : Option CtrC}
    (h1 : cReachO exc1 exc2 ν1 ν2 o n l1) {zl : Finset Letter}
    (hzl : ∀ t ∈ zl, ∃ l2, cReachO exc1 exc2 ν1 ν2 (!o) n l2
      ∧ t = cDict l2) :
    ScreenAnchored S (cEgO E1 E2 o) (cEgO E1 E2 (!o)) n
      ⟨cDict l1, zl⟩ := by
  have hS2 := cS_char2 exc1 exc2 ν1 ν2 S N hS1 hN hcharged1 hcharged2
  have hN1 : ∀ j, j ≤ N → exc1 j = none := fun j hj => (hN j hj).1
  have hN2 : ∀ j, j ≤ N → exc2 j = none := fun j hj => (hN j hj).2
  have hch1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 → exc1 k = none → k ≤ N :=
    fun k hk he => (hcharged1 k hk he).1
  have hch2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 → exc2 k = none → k ≤ N :=
    fun k hk he => (hcharged2 k hk he).1
  have hdB1 : ∀ k p, exc1 k = some p → p.1 ≤ N ∧ p.2 ≤ N :=
    fun k p hp => ⟨(hdeclN1 k p hp).1, (hdeclN1 k p hp).2.1⟩
  have hdB2 : ∀ k p, exc2 k = some p → p.1 ≤ N ∧ p.2 ≤ N :=
    fun k p hp => ⟨(hdeclN2 k p hp).1, (hdeclN2 k p hp).2.1⟩
  have hES1 : ∀ p ∈ E1, p.1 ∈ S ∧ p.2 ∈ S :=
    cEgr_subset_support exc1 ν1 N S E1 hN1 hdB1 hdecl1 hS1 hEg1
  have hES2 : ∀ p ∈ E2, p.1 ∈ S ∧ p.2 ∈ S :=
    cEgr_subset_support exc2 ν2 N S E2 hN2 hdB2 hdecl2 hS2 hEg2
  cases o with
  | false =>
      exact cAligned_screenAnchored exc1 exc2 ν1 ν2 N S E1 E2
        hN1 hch1 hdB1 hS1 hEg1 hES1 hN2 hch2 hdB2 hS2 hEg2 hES2 h1 hzl
  | true =>
      exact cAligned_screenAnchored exc2 exc1 ν2 ν1 N S E2 E1
        hN2 hch2 hdB2 hS2 hEg2 hES2 hN1 hch1 hdB1 hS1 hEg1 hES1 h1 hzl

include hN hdecl1 hdecl2 hdeclN1 hdeclN2 hcharged1 hcharged2 hS1 hEg1
  hEg2 in
/-- Gated coordinates embed into good screens. -/
lemma cNGate_cGood {i : cIdx N} (hi : cNGate exc1 exc2 ν1 ν2 i) :
    cGood S (cEgO E1 E2 i.1) (cEgO E1 E2 (!i.1)) (cEmb N i.2) := by
  obtain ⟨⟨n, hr1, hrZ, hrT, hZne⟩, hfd⟩ := hi
  refine ⟨⟨n, ?_⟩, hZne.image _, ?_⟩
  · refine cAligned_screenAnchoredO exc1 exc2 ν1 ν2 S E1 E2 N hN hdecl1
      hdecl2 hdeclN1 hdeclN2 hcharged1 hcharged2 hS1 hEg1 hEg2 i.1 hr1
      (fun t ht => ?_)
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨l, hrZ l hl, rfl⟩
  · rintro ⟨hcell, hFz⟩
    refine hfd ⟨cDict_eq_F_iff.mp hcell, ?_⟩
    obtain ⟨l, hl, hdl⟩ := Finset.mem_image.mp hFz
    rw [← cDict_eq_F_iff.mp hdl]
    exact hl

include hN hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1
  hEg2 in
/-- Gated moves with a common cell component are common full-successor
steps of the formal grammar; the tilt component rides along unseen, so
the common moves and the priced tilt-renewal moves with a common cell
move share this certificate. -/
private lemma cCommonCell_commonStep {i : cIdx N}
    (hgi : cNGate exc1 exc2 ν1 ν2 i) {sp : cLB N}
    (hsp : sp ∈ cLiftB N (cSrcC (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1)
      (cRawS i)))
    (tp : Option (cLB N)) :
    CommonStep S (cEgO E1 E2 (!i.1)) (cEmb N i.2)
      (cEmb N (sp, cLiftB N (cZSuccR (cExcO exc1 exc2 (!i.1))
        (cKO K1 K2 (!i.1)) (cRawZ i)), tp)) := by
  obtain ⟨⟨n, hr1, hrZ, hrT, hZne⟩, hfd⟩ := hgi
  have htameS : cTameB (cExcO exc1 exc2 i.1) N (cRawS i) :=
    cReachO_cTameB exc1 exc2 ν1 ν2 N hN
      (fun k hk he => (hcharged1 k hk he).1)
      (fun k p hp => ⟨(hdeclN1 k p hp).1, (hdeclN1 k p hp).2.1⟩)
      (fun k hk he => (hcharged2 k hk he).1)
      (fun k p hp => ⟨(hdeclN2 k p hp).1, (hdeclN2 k p hp).2.1⟩)
      i.1 hr1
  have hZSbox : ∀ l' ∈ cZSuccR (cExcO exc1 exc2 (!i.1))
      (cKO K1 K2 (!i.1)) (cRawZ i), l' ∈ cLetterBox N := by
    intro l' hl'
    have hre := cZSuccR_reach exc1 exc2 ν1 ν2 K1 K2 hrZ
      (cSupO ν1 ν2 K1 K2 hsup1 hsup2 (!i.1)) l' hl'
    exact cTameB_mem_cLetterBox (cReachO_cTameB exc1 exc2 ν1 ν2 N hN
      (fun k hk he => (hcharged1 k hk he).1)
      (fun k p hp => ⟨(hdeclN1 k p hp).1, (hdeclN1 k p hp).2.1⟩)
      (fun k hk he => (hcharged2 k hk he).1)
      (fun k p hp => ⟨(hdeclN2 k p hp).1, (hdeclN2 k p hp).2.1⟩)
      (!i.1) hre)
  constructor
  · show cDict sp.1 ∈ succ S ∅ (cDict (cRawS i))
    exact cDict_cSrcC_mem_succ
      (cSupO ν1 ν2 K1 K2 hsup1 hsup2 i.1)
      (cS_charO exc1 exc2 ν1 ν2 S N hN hcharged1 hcharged2 hS1 i.1)
      htameS (mem_cLiftB.mp hsp)
  · show ((cLiftB N (cZSuccR (cExcO exc1 exc2 (!i.1))
        (cKO K1 K2 (!i.1)) (cRawZ i))).image Subtype.val).image cDict
      = ((cRawZ i).image cDict).biUnion (succ S (cEgO E1 E2 (!i.1)))
    rw [cLiftB_image_val hZSbox, cZSuccR, Finset.biUnion_image,
      Finset.image_biUnion]
    refine Finset.biUnion_congr rfl fun l hl => ?_
    have htame := cReachO_cTameB exc1 exc2 ν1 ν2 N hN
      (fun k hk he => (hcharged1 k hk he).1)
      (fun k p hp => ⟨(hdeclN1 k p hp).1, (hdeclN1 k p hp).2.1⟩)
      (fun k hk he => (hcharged2 k hk he).1)
      (fun k p hp => ⟨(hdeclN2 k p hp).1, (hdeclN2 k p hp).2.1⟩)
      (!i.1) (hrZ l hl)
    exact cDict_image_cSuccRaw
      (cSupO ν1 ν2 K1 K2 hsup1 hsup2 (!i.1))
      (cS_charO exc1 exc2 ν1 ν2 S N hN hcharged1 hcharged2 hS1 (!i.1))
      (cEgO_char exc1 exc2 ν1 ν2 E1 E2 hEg1 hEg2 (!i.1)) htame

include hN hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1
  hEg2 in
/-- Gated common moves are common full-successor steps of the formal
grammar. -/
lemma cNTgt_commonStep {i j : cIdx N}
    (hgi : cNGate exc1 exc2 ν1 ν2 i)
    (hj : j ∈ cNTgt exc1 exc2 K1 K2 i) :
    CommonStep S (cEgO E1 E2 (!i.1)) (cEmb N i.2) (cEmb N j.2) := by
  obtain ⟨pr, hpr, hj⟩ := Finset.mem_image.mp hj
  subst hj
  exact cCommonCell_commonStep exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N hN
    hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1 hEg2 hgi
    (Finset.mem_product.mp hpr).1 pr.2

include hN hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1
  hEg2 in
/-- Gated priced tilt moves with a common cell move are common
full-successor steps of the formal grammar: the cell advances by a
common move and the zero list by the full successor set, so the
`CommonStep` support condition of the nilpotence embedding holds
unchanged. -/
lemma cPTgtC_commonStep {i j : cIdx N}
    (hgi : cNGate exc1 exc2 ν1 ν2 i)
    (hj : j ∈ cPTgtC exc1 exc2 K1 K2 i) :
    CommonStep S (cEgO E1 E2 (!i.1)) (cEmb N i.2) (cEmb N j.2) := by
  obtain ⟨pr, hpr, hj⟩ := Finset.mem_image.mp hj
  subst hj
  exact cCommonCell_commonStep exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N hN
    hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1 hEg2 hgi
    (Finset.mem_product.mp hpr).1 pr.2

end Dispatch

/-! ### Block diagonality and the nilpotence -/

private lemma mulVec_block_apply {P : Type} [Fintype P]
    (W : (Bool × P) → (Bool × P) → ℝ≥0∞)
    (hbd : ∀ o p o' q, o ≠ o' → W (o, p) (o', q) = 0)
    (v : Bool × P → ℝ≥0∞) (o : Bool) (p : P) :
    mulVec W v (o, p)
      = mulVec (fun p' q => W (o, p') (o, q)) (fun q => v (o, q)) p := by
  rw [mulVec, mulVec, Fintype.sum_prod_type, Fintype.sum_bool]
  cases o with
  | false =>
      rw [show (∑ q, W (false, p) (true, q) * v (true, q)) = 0 from
        Finset.sum_eq_zero fun q _ => by
          rw [hbd false p true q (by simp), zero_mul], zero_add]
  | true =>
      rw [show (∑ q, W (true, p) (false, q) * v (false, q)) = 0 from
        Finset.sum_eq_zero fun q _ => by
          rw [hbd true p false q (by simp), zero_mul], add_zero]

lemma mulVec_iterate_block {P : Type} [Fintype P]
    (W : (Bool × P) → (Bool × P) → ℝ≥0∞)
    (hbd : ∀ o p o' q, o ≠ o' → W (o, p) (o', q) = 0) :
    ∀ (m : ℕ) (v : Bool × P → ℝ≥0∞) (o : Bool) (p : P),
      (mulVec W)^[m] v (o, p)
        = (mulVec fun p' q => W (o, p') (o, q))^[m]
            (fun q => v (o, q)) p := by
  intro m
  induction m with
  | zero =>
      intro v o p
      rfl
  | succ m ih =>
      intro v o p
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        ih (mulVec W v) o p,
        show (fun q => mulVec W v (o, q))
            = mulVec (fun p' q => W (o, p') (o, q)) (fun q => v (o, q))
          from funext fun q => mulVec_block_apply W hbd v o q]

/-- **Nilpotence of the common block** (`eq:composite-nilpotent` for
the concrete matrix): the gated common matrix is annihilated by
`cRank N` applications of `mulVec`, through `cGood_nilpotent` per
orientation block. -/
theorem cNc_nilpotent
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (N : ℕ)
    (RTT : ℝ≥0∞) (hSne : S.Nonempty)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p) :
    (mulVec (cNc exc1 exc2 ν1 ν2 K1 K2 RTT (N := N)))^[cRank N]
        (fun _ => 1)
      = fun _ => 0 := by
  have hbd : ∀ (o : Bool) (p : cPay N) (o' : Bool) (q : cPay N),
      o ≠ o' → cNc exc1 exc2 ν1 ν2 K1 K2 RTT (o, p) (o', q) = 0 := by
    intro o p o' q hne
    have hb1 : ¬(cNGate exc1 exc2 ν1 ν2 ((o, p) : cIdx N)
        ∧ cNGate exc1 exc2 ν1 ν2 ((o', q) : cIdx N)
        ∧ ((o', q) : cIdx N)
          ∈ cNTgt exc1 exc2 K1 K2 ((o, p) : cIdx N)) := by
      rintro ⟨_, _, hj⟩
      obtain ⟨pr, _, hj⟩ := Finset.mem_image.mp hj
      exact hne (congrArg Prod.fst hj)
    have hb2 : ¬(cNGate exc1 exc2 ν1 ν2 ((o, p) : cIdx N)
        ∧ cNGate exc1 exc2 ν1 ν2 ((o', q) : cIdx N)
        ∧ ((o', q) : cIdx N)
          ∈ cPTgtC exc1 exc2 K1 K2 ((o, p) : cIdx N)) := by
      rintro ⟨_, _, hj⟩
      obtain ⟨pr, _, hj⟩ := Finset.mem_image.mp hj
      exact hne (congrArg Prod.fst hj)
    rw [cNc, if_neg hb1, if_neg hb2, add_zero]
  funext i
  obtain ⟨o, p⟩ := i
  rw [mulVec_iterate_block _ hbd (cRank N) _ o p]
  have hsupp : ∀ p q : cPay N,
      cNc exc1 exc2 ν1 ν2 K1 K2 RTT (o, p) (o, q) ≠ 0 →
      CommonStep S (cEgO E1 E2 (!o)) (cEmb N p) (cEmb N q)
        ∧ cGood S (cEgO E1 E2 o) (cEgO E1 E2 (!o)) (cEmb N p)
        ∧ cGood S (cEgO E1 E2 o) (cEgO E1 E2 (!o)) (cEmb N q) := by
    intro p q hne
    have hcond : (cNGate exc1 exc2 ν1 ν2 ((o, p) : cIdx N)
          ∧ cNGate exc1 exc2 ν1 ν2 ((o, q) : cIdx N)
          ∧ ((o, q) : cIdx N)
            ∈ cNTgt exc1 exc2 K1 K2 ((o, p) : cIdx N))
        ∨ (cNGate exc1 exc2 ν1 ν2 ((o, p) : cIdx N)
          ∧ cNGate exc1 exc2 ν1 ν2 ((o, q) : cIdx N)
          ∧ ((o, q) : cIdx N)
            ∈ cPTgtC exc1 exc2 K1 K2 ((o, p) : cIdx N)) := by
      by_contra hc
      rw [not_or] at hc
      rw [cNc, if_neg hc.1, if_neg hc.2, add_zero] at hne
      exact hne rfl
    have hstep : CommonStep S (cEgO E1 E2 (!o)) (cEmb N p) (cEmb N q)
        ∧ cNGate exc1 exc2 ν1 ν2 ((o, p) : cIdx N)
        ∧ cNGate exc1 exc2 ν1 ν2 ((o, q) : cIdx N) := by
      rcases hcond with ⟨hgi, hgj, hjt⟩ | ⟨hgi, hgj, hjt⟩
      · exact ⟨cNTgt_commonStep exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N hN
          hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1 hEg2
          hgi hjt, hgi, hgj⟩
      · exact ⟨cPTgtC_commonStep exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N hN
          hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1 hEg2
          hgi hjt, hgi, hgj⟩
    obtain ⟨hcs, hgi, hgj⟩ := hstep
    refine ⟨hcs, ?_, ?_⟩
    · exact cNGate_cGood exc1 exc2 ν1 ν2 S E1 E2 N hN hdecl1 hdecl2
        hdeclN1 hdeclN2 hcharged1 hcharged2 hS1 hEg1 hEg2 hgi
    · exact cNGate_cGood exc1 exc2 ν1 ν2 S E1 E2 N hN hdecl1 hdecl2
        hdeclN1 hdeclN2 hcharged1 hcharged2 hS1 hEg1 hEg2 hgj
  have hnil := cGood_nilpotent S hSne (cEgO E1 E2 o) (cEgO E1 E2 (!o))
    (cEmb N)
    (fun p q => cNc exc1 exc2 ν1 ν2 K1 K2 RTT ((o, p) : cIdx N) (o, q))
    hsupp
  have := congrFun hnil p
  simp only [cRank]
  exact this

end Nilpotent

end Composite
end GraphMarkovMatching
