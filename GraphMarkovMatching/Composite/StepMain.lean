/-
The concrete screen-ledger input, part five of six: the assembled one-step row `cE_step`,
the packaged ledger input `screenLedgerInput_holds`, and the final theorems of the priced
route, `composite_failure_le_final` with the affordability and smallness hypotheses.  The
merged block, which removes both, follows in `Step`.
-/
import GraphMarkovMatching.Composite.StepRouting

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type}

/-! ### The assembled one-step row -/

section StepMain

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ) (N : ℕ)

private lemma cHPairO
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (o : Bool) :
    ∀ k p, cExcO exc1 exc2 o k = some p →
      ∀ j, j ≤ p.1 → cExcO exc1 exc2 o j = none := by
  cases o with
  | false => exact hpair1
  | true => exact hpair2

private lemma cTiltSumO
    (hT1 : cTiltSum α exc1 μ ν1 v0 ≤ T)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T) (o : Bool) :
    cTiltSum α (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 ≤ T := by
  cases o with
  | false => exact hT1
  | true => exact hT2

private lemma cExcMassO
    (heM1 : cExcMass exc1 ν1 ≤ eM) (heM2 : cExcMass exc2 ν2 ≤ eM)
    (o : Bool) :
    cExcMass (cExcO exc1 exc2 o) (cNuO ν1 ν2 o) ≤ eM := by
  cases o with
  | false => exact heM1
  | true => exact heM2

/-- Routed unit cell output. -/
private lemma cCellOutU_routed (hα : 1 ≤ α) (o : Bool) (n h : ℕ)
    (cs : CtrC) {Z : Finset (Option CtrC)}
    (hsc0 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp0 (cExcO exc1 exc2 o) cs))
    (hsc1 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp1 (cExcO exc1 exc2 o) cs))
    (hZ : ∀ l ∈ Z, cReachO exc1 exc2 ν1 ν2 (!o) n l) (hZne : Z.Nonempty)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (hb0 : cComp0 (cExcO exc1 exc2 o) cs ∈ cLetterBox N)
    (hb1 : cComp1 (cExcO exc1 exc2 o) cs ∈ cLetterBox N)
    (hZb : ∀ l ∈ Z, l ∈ cLetterBox N)
    (hZSb : ∀ l' ∈ cZSuccR (cExcO exc1 exc2 (!o)) (cKO K1 K2 (!o)) Z,
      l' ∈ cLetterBox N)
    (TS : Finset (cIdx N))
    (hm0 : cMk N o hb0 (cZSuccR (cExcO exc1 exc2 (!o))
      (cKO K1 K2 (!o)) Z) option_forall_mem_none ∈ TS)
    (hm1 : cMk N o hb1 (cZSuccR (cExcO exc1 exc2 (!o))
      (cKO K1 K2 (!o)) Z) option_forall_mem_none ∈ TS) :
    cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o cs Z none h
      ≤ 2 * (∑ j ∈ TS, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
        + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
            * (2 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          + ((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            * ((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)) := by
  refine le_trans (cCellOutU α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα o n h
    cs hsc0 hsc1 hZ hZne hsupB hb0 hb1 hZb hZSb) ?_
  have h0 := Finset.single_le_sum
    (f := fun j => cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
    (fun _ _ => zero_le) hm0
  have h1 := Finset.single_le_sum
    (f := fun j => cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
    (fun _ _ => zero_le) hm1
  refine le_trans (add_le_add (add_le_add (add_le_add h0 h1) le_rfl)
    le_rfl) (le_of_eq ?_)
  ring

/-- Routed tilted cell output. -/
private lemma cCellOutT_routed (hα : 1 ≤ α) (o : Bool) (n h : ℕ)
    (cs c3 : CtrC) {Z : Finset (Option CtrC)}
    (hsc0 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp0 (cExcO exc1 exc2 o) cs))
    (hsc1 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp1 (cExcO exc1 exc2 o) cs))
    (hZ : ∀ l ∈ Z, cReachO exc1 exc2 ν1 ν2 (!o) n l) (hZne : Z.Nonempty)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (ht30 : cReachO exc1 exc2 ν1 ν2 (!o) (n + 1)
      (cComp0 (cExcO exc1 exc2 (!o)) c3))
    (ht31 : cReachO exc1 exc2 ν1 ν2 (!o) (n + 1)
      (cComp1 (cExcO exc1 exc2 (!o)) c3))
    (hb0 : cComp0 (cExcO exc1 exc2 o) cs ∈ cLetterBox N)
    (hb1 : cComp1 (cExcO exc1 exc2 o) cs ∈ cLetterBox N)
    (hb30 : cComp0 (cExcO exc1 exc2 (!o)) c3 ∈ cLetterBox N)
    (hb31 : cComp1 (cExcO exc1 exc2 (!o)) c3 ∈ cLetterBox N)
    (hZb : ∀ l ∈ Z, l ∈ cLetterBox N)
    (hZSb : ∀ l' ∈ cZSuccR (cExcO exc1 exc2 (!o)) (cKO K1 K2 (!o)) Z,
      l' ∈ cLetterBox N)
    (TS : Finset (cIdx N))
    (hm00 : cMk N o hb0 (cZSuccR (cExcO exc1 exc2 (!o))
      (cKO K1 K2 (!o)) Z) (option_forall_mem_some hb30) ∈ TS)
    (hm01 : cMk N o hb0 (cZSuccR (cExcO exc1 exc2 (!o))
      (cKO K1 K2 (!o)) Z) (option_forall_mem_some hb31) ∈ TS)
    (hm10 : cMk N o hb1 (cZSuccR (cExcO exc1 exc2 (!o))
      (cKO K1 K2 (!o)) Z) (option_forall_mem_some hb30) ∈ TS)
    (hm11 : cMk N o hb1 (cZSuccR (cExcO exc1 exc2 (!o))
      (cKO K1 K2 (!o)) Z) (option_forall_mem_some hb31) ∈ TS) :
    cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o cs Z (some (some c3)) h
      ≤ 4 * (∑ j ∈ TS, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
        + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
            * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          + 2 * (((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            * ((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j))) := by
  refine le_trans (cCellOutT α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα o n h
    cs c3 hsc0 hsc1 hZ hZne hsupB ht30 ht31 hb0 hb1 hb30 hb31 hZb
    hZSb) ?_
  have h00 := Finset.single_le_sum
    (f := fun j => cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
    (fun _ _ => zero_le) hm00
  have h01 := Finset.single_le_sum
    (f := fun j => cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
    (fun _ _ => zero_le) hm01
  have h10 := Finset.single_le_sum
    (f := fun j => cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
    (fun _ _ => zero_le) hm10
  have h11 := Finset.single_le_sum
    (f := fun j => cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
    (fun _ _ => zero_le) hm11
  refine le_trans (add_le_add
    (add_le_add (add_le_add (add_le_add h00 h11) le_rfl) le_rfl)
    (add_le_add (add_le_add (add_le_add h01 h10) le_rfl) le_rfl))
    (le_of_eq ?_)
  ring

/-- **The priced renewal rows of a source cell**: the `compFloor`-tilted
pair screens of the renewal cells, routed into a target ledger sum
through the tilted cell output and collected by the tilt-sum budget. -/
private lemma cPricedRows_le (hα : 1 ≤ α) (o : Bool) (n h : ℕ)
    (cs : CtrC) {Z : Finset (Option CtrC)} (T : ℝ≥0∞)
    (hsc0 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp0 (cExcO exc1 exc2 o) cs))
    (hsc1 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp1 (cExcO exc1 exc2 o) cs))
    (hZ : ∀ l ∈ Z, cReachO exc1 exc2 ν1 ν2 (!o) n l) (hZne : Z.Nonempty)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (hfrB : cReachO exc1 exc2 ν1 ν2 (!o) n none)
    (hT : cTiltSum α (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0 ≤ T)
    (hb0 : cComp0 (cExcO exc1 exc2 o) cs ∈ cLetterBox N)
    (hb1 : cComp1 (cExcO exc1 exc2 o) cs ∈ cLetterBox N)
    (hZb : ∀ l ∈ Z, l ∈ cLetterBox N)
    (hZSb : ∀ l' ∈ cZSuccR (cExcO exc1 exc2 (!o)) (cKO K1 K2 (!o)) Z,
      l' ∈ cLetterBox N)
    (hboxB : ∀ {n' : ℕ} {l : Option CtrC},
      cReachO exc1 exc2 ν1 ν2 (!o) n' l → l ∈ cLetterBox N)
    (TS : Finset (cIdx N))
    (hm : ∀ k', k' ∈ cKO K1 K2 (!o) →
      ∀ (hb30 : cComp0 (cExcO exc1 exc2 (!o)) (CtrC.ord k')
          ∈ cLetterBox N)
        (hb31 : cComp1 (cExcO exc1 exc2 (!o)) (CtrC.ord k')
          ∈ cLetterBox N),
        cMk N o hb0 (cZSuccR (cExcO exc1 exc2 (!o)) (cKO K1 K2 (!o)) Z)
            (option_forall_mem_some hb30) ∈ TS
        ∧ cMk N o hb0 (cZSuccR (cExcO exc1 exc2 (!o)) (cKO K1 K2 (!o))
              Z) (option_forall_mem_some hb31) ∈ TS
        ∧ cMk N o hb1 (cZSuccR (cExcO exc1 exc2 (!o)) (cKO K1 K2 (!o))
              Z) (option_forall_mem_some hb30) ∈ TS
        ∧ cMk N o hb1 (cZSuccR (cExcO exc1 exc2 (!o)) (cKO K1 K2 (!o))
              Z) (option_forall_mem_some hb31) ∈ TS) :
    ∑ k' ∈ cKO K1 K2 (!o), (if cNuO ν1 ν2 (!o) k' = 0 then 0
        else compFloor (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
            k' ^ (-α)
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o cs Z
              (some (some (CtrC.ord k'))) h)
      ≤ T * (4 * (∑ j ∈ TS, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
              * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              * ((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)))) := by
  calc ∑ k' ∈ cKO K1 K2 (!o), (if cNuO ν1 ν2 (!o) k' = 0
        then 0 else compFloor (cExcO exc1 exc2 (!o)) μ
            (cNuO ν1 ν2 (!o)) v0 k' ^ (-α)
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o cs Z
              (some (some (CtrC.ord k'))) h)
      ≤ ∑ k' ∈ cKO K1 K2 (!o), (if cNuO ν1 ν2 (!o) k' = 0
          then 0 else compFloor (cExcO exc1 exc2 (!o)) μ
              (cNuO ν1 ν2 (!o)) v0 k' ^ (-α))
          * (4 * (∑ j ∈ TS, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                * ((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)))) := by
        refine Finset.sum_le_sum fun k' hk' => ?_
        by_cases hνk' : cNuO ν1 ν2 (!o) k' = 0
        · rw [if_pos hνk', if_pos hνk', zero_mul]
        · rw [if_neg hνk', if_neg hνk']
          have ht30 : cReachO exc1 exc2 ν1 ν2 (!o) (n + 1)
              (cComp0 (cExcO exc1 exc2 (!o)) (CtrC.ord k')) :=
            cReachO_spawn exc1 exc2 ν1 ν2 hfrB ⟨k', hνk', Or.inl rfl⟩
          have ht31 : cReachO exc1 exc2 ν1 ν2 (!o) (n + 1)
              (cComp1 (cExcO exc1 exc2 (!o)) (CtrC.ord k')) :=
            cReachO_spawn exc1 exc2 ν1 ν2 hfrB ⟨k', hνk', Or.inr rfl⟩
          obtain ⟨h00, h01, h10, h11⟩ :=
            hm k' hk' (hboxB ht30) (hboxB ht31)
          refine mul_le_mul_right ?_ _
          exact cCellOutT_routed α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα
            o n h cs (CtrC.ord k') hsc0 hsc1 hZ hZne hsupB ht30 ht31
            hb0 hb1 (hboxB ht30) (hboxB ht31) hZb hZSb TS h00 h01 h10
            h11
    _ = (∑ k' ∈ cKO K1 K2 (!o), if cNuO ν1 ν2 (!o) k' = 0
          then 0 else compFloor (cExcO exc1 exc2 (!o)) μ
              (cNuO ν1 ν2 (!o)) v0 k' ^ (-α))
        * (4 * (∑ j ∈ TS, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
              * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              * ((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)))) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ T * (4 * (∑ j ∈ TS, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
              * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              * ((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)))) := by
        refine mul_le_mul_left ?_ _
        exact le_trans (ENNReal.sum_le_tsum _) hT

/-- The inhomogeneity as its two literal summands. -/
private lemma cG_eq_parts (Lz : ℕ) (a b : ℝ≥0∞) :
    cG α Rv μ T RT Lz a b
      = 2 * etaG α Rv μ
          * (1 + T * (2 * ((1 + ENNReal.ofReal α * a)
              * (1 + ENNReal.ofReal α * a))))
        + (1 + RT * T)
          * (8 * (ENNReal.ofReal α * a * b)
            + 4 * (((Lz : ℝ≥0∞) * b) * ((Lz : ℝ≥0∞) * b))) := rfl

/-- The far mass fits the first summand. -/
private lemma cG_first_of_farMass {X a : ℝ≥0∞}
    (hX : X ≤ 2 * etaG α Rv μ) :
    X ≤ 2 * etaG α Rv μ
        * (1 + T * (2 * ((1 + ENNReal.ofReal α * a)
            * (1 + ENNReal.ofReal α * a)))) :=
  le_trans hX (le_trans (le_of_eq (mul_one _).symm)
    (mul_le_mul_right le_self_add _))

/-- The far tilt at the pair moment fits the first summand. -/
private lemma cG_first_of_farTilt {X F a : ℝ≥0∞}
    (hF : F ≤ 2 * etaG α Rv μ)
    (hX : X ≤ F * (T * cPairMoment α a)) :
    X ≤ 2 * etaG α Rv μ
        * (1 + T * (2 * ((1 + ENNReal.ofReal α * a)
            * (1 + ENNReal.ofReal α * a)))) := by
  refine le_trans hX ?_
  rw [cPairMoment]
  exact mul_le_mul' hF (le_add_self)

/-- A unit-coefficient quadratic charge fits the second summand. -/
private lemma cG_second_of_quad {X a b : ℝ≥0∞} (Lz : ℕ)
    (hX : X ≤ 8 * (ENNReal.ofReal α * a * b)
        + 4 * (((Lz : ℝ≥0∞) * b) * ((Lz : ℝ≥0∞) * b))) :
    X ≤ (1 + RT * T)
        * (8 * (ENNReal.ofReal α * a * b)
          + 4 * (((Lz : ℝ≥0∞) * b) * ((Lz : ℝ≥0∞) * b))) :=
  le_trans hX (le_trans (le_of_eq (one_mul _).symm)
    (mul_le_mul_left le_self_add _))

/-- A priced quadratic charge fits the second summand. -/
private lemma cG_second_of_quadP {X a b : ℝ≥0∞} (Lz : ℕ)
    (hX : X ≤ RT * T * (ENNReal.ofReal α * a * (4 * b)
        + 2 * (((Lz : ℝ≥0∞) * b) * ((Lz : ℝ≥0∞) * b)))) :
    X ≤ (1 + RT * T)
        * (8 * (ENNReal.ofReal α * a * b)
          + 4 * (((Lz : ℝ≥0∞) * b) * ((Lz : ℝ≥0∞) * b))) := by
  refine le_trans hX ?_
  refine le_trans (mul_le_mul_right ?_ (RT * T))
    (mul_le_mul_left le_add_self _)
  refine add_le_add ?_ ?_
  · refine le_trans (le_of_eq (by ring)) (mul_le_mul_left
      (by norm_num : (4 : ℝ≥0∞) ≤ 8) (ENNReal.ofReal α * a * b))
  · exact mul_le_mul_left (by norm_num : (2 : ℝ≥0∞) ≤ 4) _

/-- A doubled priced quadratic charge (the common and the entrance
renewal parts together) fits the second summand exactly. -/
private lemma cG_second_of_quadP2 {X a b : ℝ≥0∞} (Lz : ℕ)
    (hX : X ≤ 2 * (RT * T) * (ENNReal.ofReal α * a * (4 * b)
        + 2 * (((Lz : ℝ≥0∞) * b) * ((Lz : ℝ≥0∞) * b)))) :
    X ≤ (1 + RT * T)
        * (8 * (ENNReal.ofReal α * a * b)
          + 4 * (((Lz : ℝ≥0∞) * b) * ((Lz : ℝ≥0∞) * b))) := by
  refine le_trans hX ?_
  calc 2 * (RT * T) * (ENNReal.ofReal α * a * (4 * b)
        + 2 * (((Lz : ℝ≥0∞) * b) * ((Lz : ℝ≥0∞) * b)))
      = RT * T * (8 * (ENNReal.ofReal α * a * b)
          + 4 * (((Lz : ℝ≥0∞) * b) * ((Lz : ℝ≥0∞) * b))) := by ring
    _ ≤ (1 + RT * T) * (8 * (ENNReal.ofReal α * a * b)
          + 4 * (((Lz : ℝ≥0∞) * b) * ((Lz : ℝ≥0∞) * b))) :=
        mul_le_mul_left le_add_self _

/-- A `ν`-average split along the exceptional chart: the common part
at its own budget, the exceptional part at the exceptional mass. -/
private lemma tsum_nu_split_le (ν : PMF ℕ)
    (exc : ℕ → Option (ℕ × ℕ)) {f : ℕ → ℝ≥0∞} {UC UE : ℝ≥0∞}
    (hfc : ∀ k, (ν k : ℝ≥0∞) ≠ 0 → exc k = none → f k ≤ UC)
    (hfe : ∀ k, (ν k : ℝ≥0∞) ≠ 0 → exc k ≠ none → f k ≤ UE) :
    (∑' k, (ν k : ℝ≥0∞) * f k) ≤ UC + cExcMass exc ν * UE := by
  have hsplit : (∑' k, (ν k : ℝ≥0∞) * f k)
      = (∑' k, if exc k = none then (ν k : ℝ≥0∞) * f k else 0)
        + ∑' k, (if exc k = none then 0 else (ν k : ℝ≥0∞) * f k) := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun k => ?_
    by_cases hexck : exc k = none
    · rw [if_pos hexck, if_pos hexck, add_zero]
    · rw [if_neg hexck, if_neg hexck, zero_add]
  rw [hsplit]
  refine add_le_add ?_ ?_
  · calc ∑' k, (if exc k = none then (ν k : ℝ≥0∞) * f k else 0)
        ≤ ∑' k, (ν k : ℝ≥0∞) * UC := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          by_cases hexck : exc k = none
          · rw [if_pos hexck]
            by_cases hk : (ν k : ℝ≥0∞) = 0
            · rw [hk, zero_mul, zero_mul]
            · exact mul_le_mul_right (hfc k hk hexck) _
          · rw [if_neg hexck]
            exact zero_le
      _ = UC := by rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
  · calc ∑' k, (if exc k = none then 0 else (ν k : ℝ≥0∞) * f k)
        ≤ ∑' k, (if exc k = none then 0 else (ν k : ℝ≥0∞)) * UE := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          by_cases hexck : exc k = none
          · rw [if_pos hexck, if_pos hexck, zero_mul]
          · rw [if_neg hexck, if_neg hexck]
            by_cases hk : (ν k : ℝ≥0∞) = 0
            · rw [hk, zero_mul, zero_mul]
            · exact mul_le_mul_right (hfe k hk hexck) _
      _ = cExcMass exc ν * UE := by
          rw [ENNReal.tsum_mul_right, cExcMass]

private lemma cGlue_split {F X1 X2 Y1 Y2 A B C D : ℝ≥0∞}
    (hF : F ≤ A) (hY : Y1 + Y2 ≤ B) (h1 : X1 ≤ C) (h2 : X2 ≤ D) :
    F + ((X1 + Y1) + (X2 + Y2)) ≤ (A + B) + (C + D) := by
  have he : F + ((X1 + Y1) + (X2 + Y2))
      = (F + (Y1 + Y2)) + (X1 + X2) := by ring
  rw [he]
  exact add_le_add (add_le_add hF hY) (add_le_add h1 h2)

private lemma cGlue_split0 {X1 X2 Y1 Y2 A B C D : ℝ≥0∞}
    (hY : Y1 + Y2 ≤ B) (h1 : X1 ≤ C) (h2 : X2 ≤ D) :
    (X1 + Y1) + (X2 + Y2) ≤ (A + B) + (C + D) := by
  have he : (X1 + Y1) + (X2 + Y2) = (Y1 + Y2) + (X1 + X2) := by ring
  rw [he]
  exact add_le_add (le_trans hY le_add_self) (add_le_add h1 h2)

private lemma cGlue_N {MN G2 G1 MP : ℝ≥0∞} :
    MN + G2 ≤ (G1 + G2) + (MN + MP) := by
  have he : MN + G2 = G2 + MN := by ring
  rw [he]
  exact add_le_add le_add_self le_self_add

/-- The split renewal glue: the far tilt into the first inhomogeneity
summand, the common renewals into the common row, the entrance renewals
(at exceptional mass `M ≤ eM`) into the rare row, and the doubled
quadratic charge into the second inhomogeneity summand. -/
private lemma cRenewal_glue {RT T eM M A B Q F G1 G2 MN MP : ℝ≥0∞}
    (hM1 : M ≤ 1) (hMe : M ≤ eM) (hF : F ≤ G1)
    (hA : 4 * (RT * T) * A ≤ MN)
    (hB : 4 * eM * (RT * T) * B ≤ MP)
    (hQ : 2 * (RT * T) * Q ≤ G2) :
    F + RT * (T * (4 * A + Q) + M * (T * (4 * B + Q)))
      ≤ (G1 + G2) + (MN + MP) := by
  have hsplit : RT * (T * (4 * A + Q) + M * (T * (4 * B + Q)))
      ≤ 4 * (RT * T) * A + 4 * eM * (RT * T) * B
        + 2 * (RT * T) * Q := by
    have h1 : M * (T * (4 * B + Q))
        ≤ eM * (4 * (T * B)) + 1 * (T * Q) := by
      have he : M * (T * (4 * B + Q))
          = M * (4 * (T * B)) + M * (T * Q) := by ring
      rw [he]
      exact add_le_add (mul_le_mul_left hMe _) (mul_le_mul_left hM1 _)
    refine le_trans (mul_le_mul_right (add_le_add le_rfl h1) RT) ?_
    exact le_of_eq (by ring)
  calc F + RT * (T * (4 * A + Q) + M * (T * (4 * B + Q)))
      ≤ G1 + (4 * (RT * T) * A + 4 * eM * (RT * T) * B
          + 2 * (RT * T) * Q) := add_le_add hF hsplit
    _ ≤ G1 + (MN + MP + G2) :=
        add_le_add le_rfl (add_le_add (add_le_add hA hB) hQ)
    _ = (G1 + G2) + (MN + MP) := by ring

/-- **The assembled one-step screen row** (`thm:screen-rows`): every
gated coordinate at height `h + 1` is bounded by the inhomogeneity at
the running scalars plus the common and raw priced matrix rows. -/
theorem cVal_step_le
    (hα : 1 ≤ α) (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (T RT eM : ℝ≥0∞)
    (hT1 : cTiltSum α exc1 μ ν1 v0 ≤ T)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T)
    (hRT : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    (heM1 : cExcMass exc1 ν1 ≤ eM) (heM2 : cExcMass exc2 ν2 ≤ eM)
    (h : ℕ) (i : cIdx N) (n : ℕ)
    (hg : cGateR exc1 exc2 ν1 ν2 i.1 n (cRawS i) (cRawZ i) (cRawT i)) :
    cVal α Rv μ v0 exc1 exc2 ν1 ν2 N (h + 1) i
      ≤ cG α Rv μ T RT (cLz N K1 K2)
          (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)
          (⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
        + ((∑ j', cNc exc1 exc2 ν1 ν2 K1 K2 (RT * T) i j'
              * cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j')
          + ∑ j', cMpw exc1 exc2 K1 K2 eM (RT * T) i j'
              * cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j') := by
  obtain ⟨hr1, hrZ, hrT, hZne⟩ := hg
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hαpos : (0 : ℝ) < α := lt_of_lt_of_le one_pos hα
  have hsupO := cSupO ν1 ν2 K1 K2 hsup1 hsup2
  have hbox : ∀ (o' : Bool) {n' : ℕ} {l : Option CtrC},
      cReachO exc1 exc2 ν1 ν2 o' n' l → l ∈ cLetterBox N := by
    intro o' n' l hl
    exact cReachO_mem_cLetterBox exc1 exc2 ν1 ν2 N hN
      (fun k hk he => (hcharged1 k hk he).1)
      (fun k p hp => ⟨(hdeclN1 k p hp).1, (hdeclN1 k p hp).2.1⟩)
      (fun k hk he => (hcharged2 k hk he).1)
      (fun k p hp => ⟨(hdeclN2 k p hp).1, (hdeclN2 k p hp).2.1⟩) o' hl
  have hgate : ∃ n', cGateR exc1 exc2 ν1 ν2 i.1 n' (cRawS i) (cRawZ i)
      (cRawT i) := ⟨n, hr1, hrZ, hrT, hZne⟩
  have hZb : ∀ l ∈ cRawZ i, l ∈ cLetterBox N :=
    fun l hl => hbox (!i.1) (hrZ l hl)
  have hZSb : ∀ l' ∈ cZSuccR (cExcO exc1 exc2 (!i.1))
      (cKO K1 K2 (!i.1)) (cRawZ i), l' ∈ cLetterBox N :=
    fun l' hl' => hbox (!i.1) (cZSuccR_reach exc1 exc2 ν1 ν2 K1 K2 hrZ
      (hsupO (!i.1)) l' hl')
  have hFM : (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞))
      ≤ 2 * etaG α Rv μ :=
    cFarMass_le_two_etaG α Rv μ v0 hα0 hsymm hhalf
  have hFT : (∑' v, if Rv v v0 then 0
        else (μ v : ℝ≥0∞) * WresD α μ Rv v) ≤ 2 * etaG α Rv μ := by
    refine le_trans (ENNReal.tsum_le_tsum fun v => ?_)
      (far_tilt_le α Rv μ v0 hαpos hsymm hhalf)
    by_cases hv : Rv v v0
    · rw [if_pos hv]
      exact zero_le
    · rw [if_neg hv, if_neg (fun hv' => hv (hsymm v0 v hv'))]
      refine mul_le_mul_right ?_ _
      by_cases hr : rE μ Rv v = 0
      · rw [WresD, if_pos hr]
        exact zero_le
      · exact le_of_eq (rE_rpow_neg_eq_WresD μ Rv v hr).symm
  rw [cVal]
  rcases hsrc : cRawS i with _ | c1
  · -- fresh source
    -- fresh source
    by_cases hfz : none ∈ cRawZ i
    · rw [cInterp_fdiag_eq_zero α Rv μ v0 exc1 exc2 ν1 ν2 N i.1 hRv hμ0
        hN hdeclN1 hcharged1 hdeclN2 hcharged2 (h + 1) hfz]
      exact zero_le
    have hgi : cNGate exc1 exc2 ν1 ν2 i := ⟨hgate, fun hc => hfz hc.2⟩
    have hSN := cNTgt_sum_le α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N (RT * T)
      hRv hμ0 hN hdeclN1 hcharged1 hdeclN2 hcharged2 hgi h
    have hSE := cETgt_sum_le α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N eM
      (RT * T) (i := i) h
    have hr1' : cReachO exc1 exc2 ν1 ν2 i.1 n none := hsrc ▸ hr1
    rcases htl : cRawT i with _ | (_ | c3)
    · -- unit tilt
      -- unit tilt
      refine le_trans (cInterp_cT_succ_unit_le α Rv μ v0 exc1 exc2 ν1
        ν2 K1 K2 i.1 hμ0 (hsupO (!i.1)) (cRawZ i) h) ?_
      have hmix : (∑' k, cNuO ν1 ν2 i.1 k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 i.1
                (CtrC.ord k) (cRawZ i) none h)
          ≤ (2 * (∑ j ∈ cNTgt exc1 exc2 K1 K2 i,
                cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                  * (2 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                + ((cLz N K1 K2 : ℝ≥0∞)
                    * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                  * ((cLz N K1 K2 : ℝ≥0∞)
                    * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)))
            + cExcMass (cExcO exc1 exc2 i.1) (cNuO ν1 ν2 i.1)
              * (2 * (∑ j ∈ cETgt exc1 exc2 K1 K2 i,
                  cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                    * (2 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                  + ((cLz N K1 K2 : ℝ≥0∞)
                      * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                    * ((cLz N K1 K2 : ℝ≥0∞)
                      * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j))) := by
        refine tsum_nu_split_le (cNuO ν1 ν2 i.1) (cExcO exc1 exc2 i.1)
          (fun k hνk hexck => ?_) (fun k hνk hexck => ?_)
        · have hsc0 := cReachO_spawn exc1 exc2 ν1 ν2 hr1'
            (⟨k, hνk, Or.inl rfl⟩ : cSpawn _ _ none _)
          have hsc1 := cReachO_spawn exc1 exc2 ν1 ν2 hr1'
            (⟨k, hνk, Or.inr rfl⟩ : cSpawn _ _ none _)
          exact cCellOutU_routed α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα
            i.1 n h (CtrC.ord k) hsc0 hsc1 hrZ hZne (hsupO (!i.1))
            (hbox i.1 hsc0) (hbox i.1 hsc1) hZb hZSb _
            (cMk_mem_cNTgt exc1 exc2 K1 K2 N _ _
              (by rw [hsrc]
                  exact (comps_mem_cSrcC_none
                    ((hsupO i.1 k).mp hνk) hexck).1)
              (by rw [htl]; exact none_mem_cTiltC_none _))
            (cMk_mem_cNTgt exc1 exc2 K1 K2 N _ _
              (by rw [hsrc]
                  exact (comps_mem_cSrcC_none
                    ((hsupO i.1 k).mp hνk) hexck).2)
              (by rw [htl]; exact none_mem_cTiltC_none _))
        · have hsc0 := cReachO_spawn exc1 exc2 ν1 ν2 hr1'
            (⟨k, hνk, Or.inl rfl⟩ : cSpawn _ _ none _)
          have hsc1 := cReachO_spawn exc1 exc2 ν1 ν2 hr1'
            (⟨k, hνk, Or.inr rfl⟩ : cSpawn _ _ none _)
          exact cCellOutU_routed α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα
            i.1 n h (CtrC.ord k) hsc0 hsc1 hrZ hZne (hsupO (!i.1))
            (hbox i.1 hsc0) (hbox i.1 hsc1) hZb hZSb _
            (cMk_mem_cETgt exc1 exc2 K1 K2 N _ _
              (by rw [hsrc]
                  exact (comps_mem_cSrcE_none
                    ((hsupO i.1 k).mp hνk) hexck).1)
              (by rw [htl]; exact none_mem_cTiltC_none _))
            (cMk_mem_cETgt exc1 exc2 K1 K2 N _ _
              (by rw [hsrc]
                  exact (comps_mem_cSrcE_none
                    ((hsupO i.1 k).mp hνk) hexck).2)
              (by rw [htl]; exact none_mem_cTiltC_none _))
      refine le_trans (add_le_add le_rfl hmix) ?_
      have hUE : cExcMass (cExcO exc1 exc2 i.1) (cNuO ν1 ν2 i.1)
          * (2 * (∑ j ∈ cETgt exc1 exc2 K1 K2 i,
              cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                * (2 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + ((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                * ((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)))
          ≤ (2 * eM) * (∑ j ∈ cETgt exc1 exc2 K1 K2 i,
              cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                * (2 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + ((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                * ((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)) := by
        rw [mul_add]
        refine add_le_add ?_ ?_
        · refine le_trans (mul_le_mul_left
            (cExcMassO exc1 exc2 ν1 ν2 heM1 heM2 i.1) _) ?_
          exact le_of_eq (by ring)
        · exact le_trans (mul_le_mul_left
            (cExcMass_le_one _ _) _) (le_of_eq (one_mul _))
      refine le_trans (add_le_add le_rfl (add_le_add le_rfl hUE)) ?_
      have h2SN : (2 : ℝ≥0∞) * (∑ j ∈ cNTgt exc1 exc2 K1 K2 i,
            cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          ≤ ∑ j', cNc exc1 exc2 ν1 ν2 K1 K2 (RT * T) i j'
              * cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j' :=
        le_trans (mul_le_mul_left (by norm_num : (2 : ℝ≥0∞) ≤ 4) _) hSN
      have h2SE : (2 * eM) * (∑ j ∈ cETgt exc1 exc2 K1 K2 i,
            cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          ≤ ∑ j', cMpw exc1 exc2 K1 K2 eM (RT * T) i j'
              * cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j' := by
        refine le_trans (mul_le_mul_left ?_ _) hSE
        exact le_trans (le_of_eq (by ring))
          (mul_le_mul_left (by norm_num : (2 : ℝ≥0∞) ≤ 4) eM)
      have hquad : (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
            * (2 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          + ((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            * ((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j))
          + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
              * (2 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + ((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              * ((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j))
          ≤ 8 * (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + 4 * (((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              * ((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)) := by
        calc _ = 4 * (ENNReal.ofReal α
                * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                * ((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)) := by
              ring
          _ ≤ 8 * (ENNReal.ofReal α
                * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + 4 * (((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                * ((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)) :=
            add_le_add
              (mul_le_mul_left (by norm_num : (4 : ℝ≥0∞) ≤ 8) _)
              (mul_le_mul_left (by norm_num : (2 : ℝ≥0∞) ≤ 4) _)
      rw [cG_eq_parts]
      exact cGlue_split (cG_first_of_farMass (T := T) α Rv μ hFM)
        (cG_second_of_quad (T := T) (RT := RT) α (cLz N K1 K2) hquad) h2SN h2SE
    · -- fresh tilt
      -- fresh tilt: priced renewal below every charged cell; the
      -- common-cell renewals ride the nilpotent block, the entrance
      -- renewals the rare block
      have hfrB : cReachO exc1 exc2 ν1 ν2 (!i.1) n none :=
        hrT none (by rw [htl]; rfl)
      have hSPC := cPTgtC_sum_le α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N
        (RT * T) hRv hμ0 hN hdeclN1 hcharged1 hdeclN2 hcharged2 hgi h
      have hSPE := cPTgtE_sum_le α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N eM
        (RT * T) (i := i) h
      refine le_trans (cInterp_cT_succ_tiltT_le α Rv μ v0 exc1 exc2 ν1
        ν2 K1 K2 i.1 hα hμ0 (cHPairO exc1 exc2 hpair1 hpair2 (!i.1))
        (cHDeclCO exc1 exc2 ν1 ν2 hdecl1 hdecl2 (!i.1)) (hsupO (!i.1))
        (cTiltSumO α μ v0 exc1 exc2 ν1 ν2 hT1 hT2 (!i.1)) hRT
        (n := n) hr1' hfrB (cRawZ i) h) ?_
      have hUPkC : ∀ k, (cNuO ν1 ν2 i.1 k : ℝ≥0∞) ≠ 0 →
          cExcO exc1 exc2 i.1 k = none →
          cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 i.1 (CtrC.ord k)
            (cRawZ i) (some none) h
          ≤ T * (4 * (∑ j ∈ cPTgtC exc1 exc2 K1 K2 i,
                cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                  * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                    * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                  * ((cLz N K1 K2 : ℝ≥0∞)
                    * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)))) := by
        intro k hνk hexck
        have hsc0 := cReachO_spawn exc1 exc2 ν1 ν2 hr1'
          (⟨k, hνk, Or.inl rfl⟩ : cSpawn _ _ none _)
        have hsc1 := cReachO_spawn exc1 exc2 ν1 ν2 hr1'
          (⟨k, hνk, Or.inr rfl⟩ : cSpawn _ _ none _)
        refine le_trans (cPairScr_price α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2
          i.1 hα0 hμ0 (cHPairO exc1 exc2 hpair1 hpair2 (!i.1))
          (cHDeclCO exc1 exc2 ν1 ν2 hdecl1 hdecl2 (!i.1))
          (hsupO (!i.1)) (CtrC.ord k) (cRawZ i) h) ?_
        refine cPricedRows_le α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα i.1
          n h (CtrC.ord k) T hsc0 hsc1 hrZ hZne (hsupO (!i.1)) hfrB
          (cTiltSumO α μ v0 exc1 exc2 ν1 ν2 hT1 hT2 (!i.1))
          (hbox i.1 hsc0) (hbox i.1 hsc1) hZb hZSb (hbox (!i.1)) _
          fun k' hk' hb30 hb31 =>
            ⟨cMk_mem_cPTgtC exc1 exc2 K1 K2 N _ _
                (by rw [hsrc]
                    exact (comps_mem_cSrcC_none
                      ((hsupO i.1 k).mp hνk) hexck).1)
                (by rw [htl]; exact (comps_mem_cTiltP hk').1),
              cMk_mem_cPTgtC exc1 exc2 K1 K2 N _ _
                (by rw [hsrc]
                    exact (comps_mem_cSrcC_none
                      ((hsupO i.1 k).mp hνk) hexck).1)
                (by rw [htl]; exact (comps_mem_cTiltP hk').2),
              cMk_mem_cPTgtC exc1 exc2 K1 K2 N _ _
                (by rw [hsrc]
                    exact (comps_mem_cSrcC_none
                      ((hsupO i.1 k).mp hνk) hexck).2)
                (by rw [htl]; exact (comps_mem_cTiltP hk').1),
              cMk_mem_cPTgtC exc1 exc2 K1 K2 N _ _
                (by rw [hsrc]
                    exact (comps_mem_cSrcC_none
                      ((hsupO i.1 k).mp hνk) hexck).2)
                (by rw [htl]; exact (comps_mem_cTiltP hk').2)⟩
      have hUPkE : ∀ k, (cNuO ν1 ν2 i.1 k : ℝ≥0∞) ≠ 0 →
          cExcO exc1 exc2 i.1 k ≠ none →
          cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 i.1 (CtrC.ord k)
            (cRawZ i) (some none) h
          ≤ T * (4 * (∑ j ∈ cPTgtE exc1 exc2 K1 K2 i,
                cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                  * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                    * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                  * ((cLz N K1 K2 : ℝ≥0∞)
                    * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)))) := by
        intro k hνk hexck
        have hsc0 := cReachO_spawn exc1 exc2 ν1 ν2 hr1'
          (⟨k, hνk, Or.inl rfl⟩ : cSpawn _ _ none _)
        have hsc1 := cReachO_spawn exc1 exc2 ν1 ν2 hr1'
          (⟨k, hνk, Or.inr rfl⟩ : cSpawn _ _ none _)
        refine le_trans (cPairScr_price α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2
          i.1 hα0 hμ0 (cHPairO exc1 exc2 hpair1 hpair2 (!i.1))
          (cHDeclCO exc1 exc2 ν1 ν2 hdecl1 hdecl2 (!i.1))
          (hsupO (!i.1)) (CtrC.ord k) (cRawZ i) h) ?_
        refine cPricedRows_le α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα i.1
          n h (CtrC.ord k) T hsc0 hsc1 hrZ hZne (hsupO (!i.1)) hfrB
          (cTiltSumO α μ v0 exc1 exc2 ν1 ν2 hT1 hT2 (!i.1))
          (hbox i.1 hsc0) (hbox i.1 hsc1) hZb hZSb (hbox (!i.1)) _
          fun k' hk' hb30 hb31 =>
            ⟨cMk_mem_cPTgtE exc1 exc2 K1 K2 N _ _
                (by rw [hsrc]
                    exact (comps_mem_cSrcE_none
                      ((hsupO i.1 k).mp hνk) hexck).1)
                (by rw [htl]; exact (comps_mem_cTiltP hk').1),
              cMk_mem_cPTgtE exc1 exc2 K1 K2 N _ _
                (by rw [hsrc]
                    exact (comps_mem_cSrcE_none
                      ((hsupO i.1 k).mp hνk) hexck).1)
                (by rw [htl]; exact (comps_mem_cTiltP hk').2),
              cMk_mem_cPTgtE exc1 exc2 K1 K2 N _ _
                (by rw [hsrc]
                    exact (comps_mem_cSrcE_none
                      ((hsupO i.1 k).mp hνk) hexck).2)
                (by rw [htl]; exact (comps_mem_cTiltP hk').1),
              cMk_mem_cPTgtE exc1 exc2 K1 K2 N _ _
                (by rw [hsrc]
                    exact (comps_mem_cSrcE_none
                      ((hsupO i.1 k).mp hνk) hexck).2)
                (by rw [htl]; exact (comps_mem_cTiltP hk').2)⟩
      have hmixP : (∑' k, cNuO ν1 ν2 i.1 k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 i.1
                (CtrC.ord k) (cRawZ i) (some none) h)
          ≤ T * (4 * (∑ j ∈ cPTgtC exc1 exc2 K1 K2 i,
                cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                  * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                    * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                  * ((cLz N K1 K2 : ℝ≥0∞)
                    * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j))))
            + cExcMass (cExcO exc1 exc2 i.1) (cNuO ν1 ν2 i.1)
              * (T * (4 * (∑ j ∈ cPTgtE exc1 exc2 K1 K2 i,
                    cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                  + (ENNReal.ofReal α
                      * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                      * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                    + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                        * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                      * ((cLz N K1 K2 : ℝ≥0∞)
                        * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2
                            N h j))))) :=
        tsum_nu_split_le (cNuO ν1 ν2 i.1) (cExcO exc1 exc2 i.1)
          hUPkC hUPkE
      refine le_trans (add_le_add le_rfl
        (mul_le_mul_right hmixP RT)) ?_
      rw [cG_eq_parts]
      exact cRenewal_glue (cExcMass_le_one _ _)
        (cExcMassO exc1 exc2 ν1 ν2 heM1 heM2 i.1)
        (cG_first_of_farTilt (T := T) α Rv μ hFT le_rfl)
        hSPC hSPE
        (cG_second_of_quadP2 (T := T) (RT := RT) α
          (Lz := cLz N K1 K2) le_rfl)
    · -- frozen tilt
      -- frozen tilt
      have hc3 : cReachO exc1 exc2 ν1 ν2 (!i.1) n (some c3) :=
        hrT (some c3) (by rw [htl]; rfl)
      have ht30 : cReachO exc1 exc2 ν1 ν2 (!i.1) (n + 1)
          (cComp0 (cExcO exc1 exc2 (!i.1)) c3) :=
        cReachO_spawn exc1 exc2 ν1 ν2 hc3 (Or.inl rfl)
      have ht31 : cReachO exc1 exc2 ν1 ν2 (!i.1) (n + 1)
          (cComp1 (cExcO exc1 exc2 (!i.1)) c3) :=
        cReachO_spawn exc1 exc2 ν1 ν2 hc3 (Or.inr rfl)
      refine le_trans (cInterp_cT_succ_tiltZ_le α Rv μ v0 exc1 exc2 ν1
        ν2 K1 K2 i.1 hμ0 (hsupO (!i.1)) c3 (cRawZ i) h) ?_
      have hmix : (∑' k, cNuO ν1 ν2 i.1 k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 i.1
                (CtrC.ord k) (cRawZ i) (some (some c3)) h)
          ≤ (4 * (∑ j ∈ cNTgt exc1 exc2 K1 K2 i,
                cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                  * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                    * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                  * ((cLz N K1 K2 : ℝ≥0∞)
                    * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j))))
            + cExcMass (cExcO exc1 exc2 i.1) (cNuO ν1 ν2 i.1)
              * (4 * (∑ j ∈ cETgt exc1 exc2 K1 K2 i,
                  cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                    * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                  + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                      * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                    * ((cLz N K1 K2 : ℝ≥0∞)
                      * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)))) := by
        refine tsum_nu_split_le (cNuO ν1 ν2 i.1) (cExcO exc1 exc2 i.1)
          (fun k hνk hexck => ?_) (fun k hνk hexck => ?_)
        · have hsc0 := cReachO_spawn exc1 exc2 ν1 ν2 hr1'
            (⟨k, hνk, Or.inl rfl⟩ : cSpawn _ _ none _)
          have hsc1 := cReachO_spawn exc1 exc2 ν1 ν2 hr1'
            (⟨k, hνk, Or.inr rfl⟩ : cSpawn _ _ none _)
          exact cCellOutT_routed α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα
            i.1 n h (CtrC.ord k) c3 hsc0 hsc1 hrZ hZne (hsupO (!i.1))
            ht30 ht31 (hbox i.1 hsc0) (hbox i.1 hsc1)
            (hbox (!i.1) ht30) (hbox (!i.1) ht31) hZb hZSb _
            (cMk_mem_cNTgt exc1 exc2 K1 K2 N _ _
              (by rw [hsrc]
                  exact (comps_mem_cSrcC_none
                    ((hsupO i.1 k).mp hνk) hexck).1)
              (by rw [htl]; exact (comps_mem_cTiltC_some _ c3).1))
            (cMk_mem_cNTgt exc1 exc2 K1 K2 N _ _
              (by rw [hsrc]
                  exact (comps_mem_cSrcC_none
                    ((hsupO i.1 k).mp hνk) hexck).1)
              (by rw [htl]; exact (comps_mem_cTiltC_some _ c3).2))
            (cMk_mem_cNTgt exc1 exc2 K1 K2 N _ _
              (by rw [hsrc]
                  exact (comps_mem_cSrcC_none
                    ((hsupO i.1 k).mp hνk) hexck).2)
              (by rw [htl]; exact (comps_mem_cTiltC_some _ c3).1))
            (cMk_mem_cNTgt exc1 exc2 K1 K2 N _ _
              (by rw [hsrc]
                  exact (comps_mem_cSrcC_none
                    ((hsupO i.1 k).mp hνk) hexck).2)
              (by rw [htl]; exact (comps_mem_cTiltC_some _ c3).2))
        · have hsc0 := cReachO_spawn exc1 exc2 ν1 ν2 hr1'
            (⟨k, hνk, Or.inl rfl⟩ : cSpawn _ _ none _)
          have hsc1 := cReachO_spawn exc1 exc2 ν1 ν2 hr1'
            (⟨k, hνk, Or.inr rfl⟩ : cSpawn _ _ none _)
          exact cCellOutT_routed α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα
            i.1 n h (CtrC.ord k) c3 hsc0 hsc1 hrZ hZne (hsupO (!i.1))
            ht30 ht31 (hbox i.1 hsc0) (hbox i.1 hsc1)
            (hbox (!i.1) ht30) (hbox (!i.1) ht31) hZb hZSb _
            (cMk_mem_cETgt exc1 exc2 K1 K2 N _ _
              (by rw [hsrc]
                  exact (comps_mem_cSrcE_none
                    ((hsupO i.1 k).mp hνk) hexck).1)
              (by rw [htl]; exact (comps_mem_cTiltC_some _ c3).1))
            (cMk_mem_cETgt exc1 exc2 K1 K2 N _ _
              (by rw [hsrc]
                  exact (comps_mem_cSrcE_none
                    ((hsupO i.1 k).mp hνk) hexck).1)
              (by rw [htl]; exact (comps_mem_cTiltC_some _ c3).2))
            (cMk_mem_cETgt exc1 exc2 K1 K2 N _ _
              (by rw [hsrc]
                  exact (comps_mem_cSrcE_none
                    ((hsupO i.1 k).mp hνk) hexck).2)
              (by rw [htl]; exact (comps_mem_cTiltC_some _ c3).1))
            (cMk_mem_cETgt exc1 exc2 K1 K2 N _ _
              (by rw [hsrc]
                  exact (comps_mem_cSrcE_none
                    ((hsupO i.1 k).mp hνk) hexck).2)
              (by rw [htl]; exact (comps_mem_cTiltC_some _ c3).2))
      refine le_trans hmix ?_
      have hUE : cExcMass (cExcO exc1 exc2 i.1) (cNuO ν1 ν2 i.1)
          * (4 * (∑ j ∈ cETgt exc1 exc2 K1 K2 i,
              cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                * ((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j))))
          ≤ (4 * eM) * (∑ j ∈ cETgt exc1 exc2 K1 K2 i,
              cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                * ((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j))) := by
        rw [mul_add]
        refine add_le_add ?_ ?_
        · refine le_trans (mul_le_mul_left
            (cExcMassO exc1 exc2 ν1 ν2 heM1 heM2 i.1) _) ?_
          exact le_of_eq (by ring)
        · exact le_trans (mul_le_mul_left
            (cExcMass_le_one _ _) _) (le_of_eq (one_mul _))
      refine le_trans (add_le_add le_rfl hUE) ?_
      have hquad : (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
            * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          + 2 * (((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            * ((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)))
          + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
              * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              * ((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)))
          ≤ 8 * (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + 4 * (((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              * ((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)) :=
        le_of_eq (by ring)
      rw [cG_eq_parts]
      exact cGlue_split0 (cG_second_of_quad (T := T) (RT := RT) α (cLz N K1 K2) hquad)
        hSN (le_trans (mul_le_mul_left le_rfl _) hSE)
  · -- frozen source
    -- frozen source
    have hr1' : cReachO exc1 exc2 ν1 ν2 i.1 n (some c1) := hsrc ▸ hr1
    have hsc0 : cReachO exc1 exc2 ν1 ν2 i.1 (n + 1)
        (cComp0 (cExcO exc1 exc2 i.1) c1) :=
      cReachO_spawn exc1 exc2 ν1 ν2 hr1' (Or.inl rfl)
    have hsc1 : cReachO exc1 exc2 ν1 ν2 i.1 (n + 1)
        (cComp1 (cExcO exc1 exc2 i.1) c1) :=
      cReachO_spawn exc1 exc2 ν1 ν2 hr1' (Or.inr rfl)
    have hgi : cNGate exc1 exc2 ν1 ν2 i := by
      refine ⟨hgate, ?_⟩
      rintro ⟨he, -⟩
      rw [hsrc] at he
      exact Option.some_ne_none c1 he
    have hSN := cNTgt_sum_le α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N (RT * T)
      hRv hμ0 hN hdeclN1 hcharged1 hdeclN2 hcharged2 hgi h
    rcases htl : cRawT i with _ | (_ | c3)
    · -- unit tilt
      -- unit tilt
      rw [cInterp_cZ_succ_unit α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 i.1
        (hRv v0) hμ0 (hsupO (!i.1)) c1 (cRawZ i) h]
      refine le_trans (cCellOutU_routed α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2
        N hα i.1 n h c1 hsc0 hsc1 hrZ hZne (hsupO (!i.1))
        (hbox i.1 hsc0) (hbox i.1 hsc1) hZb hZSb _
        (cMk_mem_cNTgt exc1 exc2 K1 K2 N _ _
          (by rw [hsrc]; exact (comps_mem_cSrcC_some _ _ c1).1)
          (by rw [htl]; exact none_mem_cTiltC_none _))
        (cMk_mem_cNTgt exc1 exc2 K1 K2 N _ _
          (by rw [hsrc]; exact (comps_mem_cSrcC_some _ _ c1).2)
          (by rw [htl]; exact none_mem_cTiltC_none _))) ?_
      have hq1 : ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
            * (2 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          + ((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            * ((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          ≤ 8 * (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + 4 * (((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              * ((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)) := by
        calc _ = 2 * (ENNReal.ofReal α
                * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + 1 * (((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                * ((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)) := by
              ring
          _ ≤ 8 * (ENNReal.ofReal α
                * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + 4 * (((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                * ((cLz N K1 K2 : ℝ≥0∞)
                  * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)) :=
            add_le_add
              (mul_le_mul_left (by norm_num : (2 : ℝ≥0∞) ≤ 8) _)
              (mul_le_mul_left (by norm_num : (1 : ℝ≥0∞) ≤ 4) _)
      refine le_trans (add_le_add
        (le_trans (mul_le_mul_left
          (by norm_num : (2 : ℝ≥0∞) ≤ 4) _) hSN)
        (cG_second_of_quad (T := T) (RT := RT) α (cLz N K1 K2) hq1)) ?_
      rw [cG_eq_parts]
      exact cGlue_N
    · -- fresh tilt
      -- fresh tilt: priced renewal with a common cell move, riding
      -- the nilpotent block
      rw [cInterp_cZ_succ_tiltT α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 i.1
        (hRv v0) hμ0 (hsupO (!i.1)) c1 (cRawZ i) h]
      have hfrB : cReachO exc1 exc2 ν1 ν2 (!i.1) n none :=
        hrT none (by rw [htl]; rfl)
      have hSPC := cPTgtC_sum_le α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N
        (RT * T) hRv hμ0 hN hdeclN1 hcharged1 hdeclN2 hcharged2 hgi h
      have hUP : cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 i.1 c1
          (cRawZ i) (some none) h
          ≤ T * (4 * (∑ j ∈ cPTgtC exc1 exc2 K1 K2 i,
                cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
                  * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                    * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
                  * ((cLz N K1 K2 : ℝ≥0∞)
                    * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)))) := by
        refine le_trans (cPairScr_price α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2
          i.1 hα0 hμ0 (cHPairO exc1 exc2 hpair1 hpair2 (!i.1))
          (cHDeclCO exc1 exc2 ν1 ν2 hdecl1 hdecl2 (!i.1))
          (hsupO (!i.1)) c1 (cRawZ i) h) ?_
        refine cPricedRows_le α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα i.1
          n h c1 T hsc0 hsc1 hrZ hZne (hsupO (!i.1)) hfrB
          (cTiltSumO α μ v0 exc1 exc2 ν1 ν2 hT1 hT2 (!i.1))
          (hbox i.1 hsc0) (hbox i.1 hsc1) hZb hZSb (hbox (!i.1)) _
          fun k' hk' hb30 hb31 =>
            ⟨cMk_mem_cPTgtC exc1 exc2 K1 K2 N _ _
                (by rw [hsrc]; exact (comps_mem_cSrcC_some _ _ c1).1)
                (by rw [htl]; exact (comps_mem_cTiltP hk').1),
              cMk_mem_cPTgtC exc1 exc2 K1 K2 N _ _
                (by rw [hsrc]; exact (comps_mem_cSrcC_some _ _ c1).1)
                (by rw [htl]; exact (comps_mem_cTiltP hk').2),
              cMk_mem_cPTgtC exc1 exc2 K1 K2 N _ _
                (by rw [hsrc]; exact (comps_mem_cSrcC_some _ _ c1).2)
                (by rw [htl]; exact (comps_mem_cTiltP hk').1),
              cMk_mem_cPTgtC exc1 exc2 K1 K2 N _ _
                (by rw [hsrc]; exact (comps_mem_cSrcC_some _ _ c1).2)
                (by rw [htl]; exact (comps_mem_cTiltP hk').2)⟩
      refine le_trans (mul_le_mul' (hRT v0 (hRv v0)) hUP) ?_
      refine le_trans (le_of_eq (by ring :
        RT * (T * (4 * (∑ j ∈ cPTgtC exc1 exc2 K1 K2 i,
            cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          + (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
              * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              * ((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)))))
        = (4 * (RT * T)) * (∑ j ∈ cPTgtC exc1 exc2 K1 K2 i,
            cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          + RT * T * (ENNReal.ofReal α
              * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
              * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + 2 * (((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              * ((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j))))) ?_
      refine le_trans (add_le_add hSPC
        (cG_second_of_quadP (T := T) (RT := RT) α (Lz := cLz N K1 K2) le_rfl)) ?_
      rw [cG_eq_parts]
      exact cGlue_N
    · -- frozen tilt
      -- frozen tilt
      have hc3 : cReachO exc1 exc2 ν1 ν2 (!i.1) n (some c3) :=
        hrT (some c3) (by rw [htl]; rfl)
      have ht30 : cReachO exc1 exc2 ν1 ν2 (!i.1) (n + 1)
          (cComp0 (cExcO exc1 exc2 (!i.1)) c3) :=
        cReachO_spawn exc1 exc2 ν1 ν2 hc3 (Or.inl rfl)
      have ht31 : cReachO exc1 exc2 ν1 ν2 (!i.1) (n + 1)
          (cComp1 (cExcO exc1 exc2 (!i.1)) c3) :=
        cReachO_spawn exc1 exc2 ν1 ν2 hc3 (Or.inr rfl)
      rw [cInterp_cZ_succ_tiltZ α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 i.1
        (hRv v0) hμ0 (hsupO (!i.1)) c1 c3 (cRawZ i) h]
      refine le_trans (cCellOutT_routed α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2
        N hα i.1 n h c1 c3 hsc0 hsc1 hrZ hZne (hsupO (!i.1)) ht30 ht31
        (hbox i.1 hsc0) (hbox i.1 hsc1) (hbox (!i.1) ht30)
        (hbox (!i.1) ht31) hZb hZSb _
        (cMk_mem_cNTgt exc1 exc2 K1 K2 N _ _
          (by rw [hsrc]; exact (comps_mem_cSrcC_some _ _ c1).1)
          (by rw [htl]; exact (comps_mem_cTiltC_some _ c3).1))
        (cMk_mem_cNTgt exc1 exc2 K1 K2 N _ _
          (by rw [hsrc]; exact (comps_mem_cSrcC_some _ _ c1).1)
          (by rw [htl]; exact (comps_mem_cTiltC_some _ c3).2))
        (cMk_mem_cNTgt exc1 exc2 K1 K2 N _ _
          (by rw [hsrc]; exact (comps_mem_cSrcC_some _ _ c1).2)
          (by rw [htl]; exact (comps_mem_cTiltC_some _ c3).1))
        (cMk_mem_cNTgt exc1 exc2 K1 K2 N _ _
          (by rw [hsrc]; exact (comps_mem_cSrcC_some _ _ c1).2)
          (by rw [htl]; exact (comps_mem_cTiltC_some _ c3).2))) ?_
      have hq4 : ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
            * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          + 2 * (((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            * ((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j))
          ≤ 8 * (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            + 4 * (((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
              * ((cLz N K1 K2 : ℝ≥0∞)
                * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)) := by
        have he : ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
            * (4 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
            = 4 * (ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j) := by ring
        rw [he]
        exact add_le_add
          (mul_le_mul_left (by norm_num : (4 : ℝ≥0∞) ≤ 8) _)
          (mul_le_mul_left (by norm_num : (2 : ℝ≥0∞) ≤ 4) _)
      refine le_trans (add_le_add hSN
        (cG_second_of_quad (T := T) (RT := RT) α (cLz N K1 K2) hq4)) ?_
      rw [cG_eq_parts]
      exact cGlue_N

/-- **The ledger step** (`step` of `ScreenLedgerInput`): the gated
one-step row in `rareMatrix` form. -/
theorem cE_step
    (hα : 1 ≤ α) (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (T RT eM : ℝ≥0∞)
    (hT1 : cTiltSum α exc1 μ ν1 v0 ≤ T)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T)
    (hRT : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    (heM1 : cExcMass exc1 ν1 ≤ eM) (heM2 : cExcMass exc2 ν2 ≤ eM)
    (χ0 : ℝ≥0∞) (hχ0 : χ0 ≠ 0) (hχ1 : χ0 ≤ 1)
    (h : ℕ) (i : cIdx N) :
    cE α Rv μ v0 exc1 exc2 ν1 ν2 N (h + 1) i
      ≤ cG α Rv μ T RT (cLz N K1 K2)
          (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)
          (⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
        + mulVecInf
            (rareMatrix (cNc exc1 exc2 ν1 ν2 K1 K2 (RT * T) (N := N))
              (cMp exc1 exc2 K1 K2 χ0 eM (RT * T)) χ0)
            (cE α Rv μ v0 exc1 exc2 ν1 ν2 N h) i := by
  refine iSup_le fun n => iSup_le fun hg => ?_
  refine le_trans (cVal_step_le α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα
    hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2 hpair1
    hpair2 hdecl1 hdecl2 hsup1 hsup2 T RT eM hT1 hT2 hRT heM1 heM2
    h i n hg) ?_
  refine add_le_add le_rfl (le_of_eq ?_)
  rw [mulVecInf, tsum_fintype, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rareMatrix, add_mul,
    chi0_mul_cMp exc1 exc2 K1 K2 χ0 eM (RT * T) hχ0 hχ1 i j]

end StepMain

/-! ### The packaged ledger input and the final theorems -/

section Finale

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (N : ℕ)

/-- **The concrete screen-ledger input** (`thm:screen-rows`,
`thm:composite-acyclic`, `thm:zero-interface` assembled): the ledger
vector
`cE`, the matrices `cNc`/`cMp`, the inhomogeneity `cG`, and the rank
`cRank N` satisfy `ScreenLedgerInput` under the standing packs of both
orientations, the exact supports, the grammar data, and the scalar
budgets. -/
theorem screenLedgerInput_holds
    (hα : 1 ≤ α) (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (T RT eM : ℝ≥0∞)
    (hT1 : cTiltSum α exc1 μ ν1 v0 ≤ T)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T)
    (hRT : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    (heM1 : cExcMass exc1 ν1 ≤ eM) (heM2 : cExcMass exc2 ν2 ≤ eM)
    (χ0 C cu : ℝ≥0∞) (hχ0 : χ0 ≠ 0) (hχ1 : χ0 ≤ 1)
    (hC : cNcBudget (RT * T) (cMx K1 K2) ≤ C)
    (hafford : cMpBudget eM (RT * T) (cMx K1 K2) ≤ χ0 * C)
    (hcu : 2 ≤ cu) :
    ScreenLedgerInput α Rv μ v0 exc1 exc2 ν1 ν2
      (cE α Rv μ v0 exc1 exc2 ν1 ν2 N)
      (cNc exc1 exc2 ν1 ν2 K1 K2 (RT * T) (N := N))
      (cMp exc1 exc2 K1 K2 χ0 eM (RT * T))
      (cG α Rv μ T RT (cLz N K1 K2)) χ0 C (cRank N) cu where
  debt_le := fun h => cDebt_le_iSup_cE α Rv μ v0 exc1 exc2 ν1 ν2 N hN
    (fun k hk he => (hcharged1 k hk he).1)
    (fun k p hp => ⟨(hdeclN1 k p hp).1, (hdeclN1 k p hp).2.1⟩)
    (fun k hk he => (hcharged2 k hk he).1)
    (fun k p hp => ⟨(hdeclN2 k p hp).1, (hdeclN2 k p hp).2.1⟩) h
  g_mono := fun _ _ _ _ ha hb =>
    cG_mono α Rv μ T RT (cLz N K1 K2) ha hb
  base := fun i => le_trans (cE_base_le α Rv μ v0 exc1 exc2 ν1 ν2 N hα
    hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2 i)
    (mul_le_mul_left hcu _)
  common_row := fun i =>
    le_trans (cNc_row_le exc1 exc2 ν1 ν2 K1 K2 (RT * T) i) hC
  priced_row := fun i => cMp_row_le exc1 exc2 K1 K2 χ0 eM (RT * T) C
    hχ0 hχ1 hafford i
  rank_pos := cRank_pos N
  common_nilpotent := cNc_nilpotent exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N
    (RT * T) hSne hN hdecl1 hdecl2 hdeclN1 hdeclN2 hcharged1 hcharged2
    hsup1 hsup2 hS1 hEg1 hEg2
  step := fun h i => cE_step α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα hRv
    hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2 hpair1
    hpair2 hdecl1 hdecl2 hsup1 hsup2 T RT eM hT1 hT2 hRT heM1 heM2 χ0
    hχ0 hχ1 h i

/-- **Composite two-law mismatch bound, final form**
(`thm:composite-matching`, finite heights):
`composite_failure_le_closed`
with the screen-ledger input discharged by `screenLedgerInput_holds`.
Every hypothesis is explicit: the analytic pack `(δ, L, K)`, the
standing side packs of both orientations, the exact supports, the
grammar data `(S, E1, E2)`, the scalar budgets `(T, RT, eM, κ)`, the
smallness data `(χ0, C, cu)` with the affordability budget
`cMpBudget`, the `cG`-closure `hu`, and the threshold `heta`. -/
theorem composite_failure_le_final
    {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hsup1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K1)
    (hsup2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 ↔ k ∈ K2)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hSne : S.Nonempty)
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (T RT eM κ : ℝ≥0∞)
    (hT1 : cTiltSum α exc1 μ ν1 v0 ≤ T)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T)
    (hRT : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    (heM1 : cExcMass exc1 ν1 ≤ eM) (heM2 : cExcMass exc2 ν2 ≤ eM)
    (hκ1 : (K1.card : ℝ≥0∞) ≤ κ) (hκ2 : (K2.card : ℝ≥0∞) ≤ κ)
    (hlam : cLamS δ L K < 1)
    (χ0 C cu : ℝ≥0∞) (hχ0 : χ0 ≠ 0)
    (hC : cNcBudget (RT * T) (cMx K1 K2) ≤ C)
    (hafford : cMpBudget eM (RT * T) (cMx K1 K2) ≤ χ0 * C)
    (hcu : 2 ≤ cu)
    (hsmall : cSmallness χ0 C (cRank N))
    (hu : cG α Rv μ T RT (cLz N K1 K2)
        (cKc δ L K μ v0 T κ (cX C (cRank N) cu) * etaG α Rv μ)
        (cX C (cRank N) cu * etaG α Rv μ) ≤ cu * etaG α Rv μ)
    (heta : etaG α Rv μ
      ≤ cEtaStar α δ L K μ v0 T κ (cX C (cRank N) cu)) :
    ∀ h, failureD (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
        (fullSim (cRel Rv) h)
      ≤ cKc δ L K μ v0 T κ (cX C (cRank N) cu) * etaG α Rv μ :=
  composite_failure_le_closed α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 hα hδ
    hL0 hL hK0 hK hRv hsymm hμ0 hpair1 hdecl1
    (fun k hk => (hsup1 k).mp hk) hpair2 hdecl2
    (fun k hk => (hsup2 k).mp hk) N hN
    (fun k p hp => (hdeclN1 k p hp))
    (fun k hk he => hcharged1 k hk he) T κ hT1 hT2 hκ1 hκ2 hlam
    (screenLedgerInput_holds α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N
      hα hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2
      hpair1 hpair2 hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2 T RT
      eM hT1 hT2 hRT heM1 heM2 χ0 C cu hχ0 hsmall.1 hC hafford hcu)
    hsmall hu heta

end Finale

end Composite
end GraphMarkovMatching
