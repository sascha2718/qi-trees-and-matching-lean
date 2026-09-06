/-
The concrete screen-ledger input, part four of six: the exceptional mass and the
inhomogeneity `cG`, the routing of the ledger entries into the matrix rows, the move
membership facts, and the cell outputs.  The assembled one-step row follows in
`StepMain`.
-/
import GraphMarkovMatching.Composite.StepRows

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type}

/-! ### The exceptional mass and the inhomogeneity -/

/-- The retained exceptional mass of a side. -/
noncomputable def cExcMass (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) :
    ℝ≥0∞ :=
  ∑' z, if exc z = none then 0 else (ν z : ℝ≥0∞)

lemma cExcMass_le_one (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) :
    cExcMass exc ν ≤ 1 := by
  rw [cExcMass, ← ν.tsum_coe]
  refine ENNReal.tsum_le_tsum fun z => ?_
  split_ifs
  · exact zero_le
  · exact le_rfl

/-- **The inhomogeneity of the screen step** (`thm:screen-rows`, the
collected non-matrix terms): the far charges against the graph
potential and the pair moments, and the common and priced quadratic
charges of the Hall outputs. -/
noncomputable def cG (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
    (T RT : ℝ≥0∞) (Lz : ℕ) (a b : ℝ≥0∞) : ℝ≥0∞ :=
  2 * etaG α Rv μ
      * (1 + T * (2 * ((1 + ENNReal.ofReal α * a)
          * (1 + ENNReal.ofReal α * a))))
    + (1 + RT * T)
      * (8 * (ENNReal.ofReal α * a * b)
        + 4 * (((Lz : ℝ≥0∞) * b) * ((Lz : ℝ≥0∞) * b)))

/-- The inhomogeneity is monotone in the two running arguments
(`g_mono` of `ScreenLedgerInput`). -/
lemma cG_mono (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (T RT : ℝ≥0∞)
    (Lz : ℕ) {a a' b b' : ℝ≥0∞} (ha : a ≤ a') (hb : b ≤ b') :
    cG α Rv μ T RT Lz a b ≤ cG α Rv μ T RT Lz a' b' := by
  rw [cG, cG]
  have h1 : 1 + ENNReal.ofReal α * a ≤ 1 + ENNReal.ofReal α * a' :=
    add_le_add le_rfl (mul_le_mul_right ha _)
  refine add_le_add ?_ ?_
  · refine mul_le_mul_right (add_le_add le_rfl (mul_le_mul_right
      (mul_le_mul_right (mul_le_mul' h1 h1) 2) T)) _
  · refine mul_le_mul_right (add_le_add ?_ ?_) _
    · exact mul_le_mul_right
        (mul_le_mul' (mul_le_mul_right ha _) hb) 8
    · exact mul_le_mul_right (mul_le_mul'
        (mul_le_mul_right hb _) (mul_le_mul_right hb _)) 4

/-- The split of a Hall output: the moment unit goes to the linear
part, the moment excess to the running product. -/
private lemma one_add_mul_route {c X Y b Q : ℝ≥0∞} (hX : X ≤ b)
    (hY : Y ≤ b) :
    (1 + c) * (X + Y) + Q ≤ (X + Y) + c * (2 * b) + Q := by
  have h1 : (1 + c) * (X + Y) = (X + Y) + c * (X + Y) := by ring
  rw [h1]
  refine add_le_add (add_le_add le_rfl ?_) le_rfl
  calc c * (X + Y) ≤ c * (b + b) :=
        mul_le_mul_right (add_le_add hX hY) c
    _ = c * (2 * b) := by ring

/-! ### The routing of the ledger entries into the matrix rows -/

section Routing

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ) (N : ℕ)

/-- Target constructor for the common target set. -/
lemma cMk_mem_cNTgt {i : cIdx N} {s' : Option CtrC}
    (hs' : s' ∈ cLetterBox N) {t' : Option (Option CtrC)}
    (ht' : ∀ l ∈ t', l ∈ cLetterBox N)
    (hsC : s' ∈ cSrcC (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1) (cRawS i))
    (htC : t' ∈ cTiltC (cExcO exc1 exc2 (!i.1)) (cRawT i)) :
    cMk N i.1 hs' (cZSuccR (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
      (cRawZ i)) ht' ∈ cNTgt exc1 exc2 K1 K2 i := by
  rw [cNTgt]
  refine Finset.mem_image.mpr
    ⟨(⟨s', hs'⟩, t'.pmap (fun l hl => (⟨l, hl⟩ : cLB N)) ht'), ?_, rfl⟩
  exact Finset.mem_product.mpr
    ⟨mem_cLiftB.mpr hsC, pmap_mem_cLiftO ht' htC⟩

/-- Target constructor for the entrance target set. -/
lemma cMk_mem_cETgt {i : cIdx N} {s' : Option CtrC}
    (hs' : s' ∈ cLetterBox N) {t' : Option (Option CtrC)}
    (ht' : ∀ l ∈ t', l ∈ cLetterBox N)
    (hsE : s' ∈ cSrcE (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1) (cRawS i))
    (htC : t' ∈ cTiltC (cExcO exc1 exc2 (!i.1)) (cRawT i)) :
    cMk N i.1 hs' (cZSuccR (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
      (cRawZ i)) ht' ∈ cETgt exc1 exc2 K1 K2 i := by
  rw [cETgt]
  refine Finset.mem_image.mpr
    ⟨(⟨s', hs'⟩, t'.pmap (fun l hl => (⟨l, hl⟩ : cLB N)) ht'), ?_, rfl⟩
  exact Finset.mem_product.mpr
    ⟨mem_cLiftB.mpr hsE, pmap_mem_cLiftO ht' htC⟩

/-- Target constructor for the priced common target set. -/
lemma cMk_mem_cPTgtC {i : cIdx N} {s' : Option CtrC}
    (hs' : s' ∈ cLetterBox N) {t' : Option (Option CtrC)}
    (ht' : ∀ l ∈ t', l ∈ cLetterBox N)
    (hsC : s' ∈ cSrcC (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1) (cRawS i))
    (htP : t' ∈ cTiltP (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
      (cRawT i)) :
    cMk N i.1 hs' (cZSuccR (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
      (cRawZ i)) ht' ∈ cPTgtC exc1 exc2 K1 K2 i := by
  rw [cPTgtC]
  refine Finset.mem_image.mpr
    ⟨(⟨s', hs'⟩, t'.pmap (fun l hl => (⟨l, hl⟩ : cLB N)) ht'), ?_, rfl⟩
  exact Finset.mem_product.mpr
    ⟨mem_cLiftB.mpr hsC, pmap_mem_cLiftO ht' htP⟩

/-- Target constructor for the priced entrance target set. -/
lemma cMk_mem_cPTgtE {i : cIdx N} {s' : Option CtrC}
    (hs' : s' ∈ cLetterBox N) {t' : Option (Option CtrC)}
    (ht' : ∀ l ∈ t', l ∈ cLetterBox N)
    (hsE : s' ∈ cSrcE (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1) (cRawS i))
    (htP : t' ∈ cTiltP (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
      (cRawT i)) :
    cMk N i.1 hs' (cZSuccR (cExcO exc1 exc2 (!i.1)) (cKO K1 K2 (!i.1))
      (cRawZ i)) ht' ∈ cPTgtE exc1 exc2 K1 K2 i := by
  rw [cPTgtE]
  refine Finset.mem_image.mpr
    ⟨(⟨s', hs'⟩, t'.pmap (fun l hl => (⟨l, hl⟩ : cLB N)) ht'), ?_, rfl⟩
  exact Finset.mem_product.mpr
    ⟨mem_cLiftB.mpr hsE, pmap_mem_cLiftO ht' htP⟩

/-- **The common routing** (`eq:composite-nilpotent`, support side):
the common-target ledger sum is absorbed by the common matrix row;
fresh-diagonal and ungated targets vanish. -/
lemma cNTgt_sum_le (RTT : ℝ≥0∞)
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    {i : cIdx N} (hgi : cNGate exc1 exc2 ν1 ν2 i) (h : ℕ) :
    4 * ∑ j ∈ cNTgt exc1 exc2 K1 K2 i,
        cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j
      ≤ ∑ j', cNc exc1 exc2 ν1 ν2 K1 K2 RTT i j'
          * cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j' := by
  rw [Finset.mul_sum]
  refine le_trans (le_of_eq rfl) (le_trans (Finset.sum_le_sum
    (fun j hj => ?_)) (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) fun _ _ _ => zero_le))
  by_cases hfd : cRawS j = none ∧ none ∈ cRawZ j
  · have hE0 : cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j = 0 := by
      refine le_antisymm (iSup_le fun n' => iSup_le fun _ => ?_) zero_le
      rw [cVal, hfd.1]
      exact le_of_eq (cInterp_fdiag_eq_zero α Rv μ v0 exc1 exc2 ν1 ν2 N
        j.1 hRv hμ0 hN hdeclN1 hcharged1 hdeclN2 hcharged2 h hfd.2
        (cRawT j))
    rw [hE0, mul_zero, mul_zero]
  · by_cases hgj : ∃ n', cGateR exc1 exc2 ν1 ν2 j.1 n' (cRawS j)
        (cRawZ j) (cRawT j)
    · refine mul_le_mul_left ?_ _
      rw [cNc, if_pos ⟨hgi, ⟨hgj, hfd⟩, hj⟩]
      exact le_self_add
    · rw [cE_eq_zero_of_not_gate α Rv μ v0 exc1 exc2 ν1 ν2 hgj,
        mul_zero, mul_zero]

/-- **The priced common routing**: a uniformly weighted priced-common
ledger sum is absorbed by the common matrix row; fresh-diagonal and
ungated targets vanish. -/
lemma cPTgtC_sum_le (RTT : ℝ≥0∞)
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    {i : cIdx N} (hgi : cNGate exc1 exc2 ν1 ν2 i) (h : ℕ) :
    (4 * RTT) * ∑ j ∈ cPTgtC exc1 exc2 K1 K2 i,
        cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j
      ≤ ∑ j', cNc exc1 exc2 ν1 ν2 K1 K2 RTT i j'
          * cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j' := by
  rw [Finset.mul_sum]
  refine le_trans (le_of_eq rfl) (le_trans (Finset.sum_le_sum
    (fun j hj => ?_)) (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) fun _ _ _ => zero_le))
  by_cases hfd : cRawS j = none ∧ none ∈ cRawZ j
  · have hE0 : cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j = 0 := by
      refine le_antisymm (iSup_le fun n' => iSup_le fun _ => ?_) zero_le
      rw [cVal, hfd.1]
      exact le_of_eq (cInterp_fdiag_eq_zero α Rv μ v0 exc1 exc2 ν1 ν2 N
        j.1 hRv hμ0 hN hdeclN1 hcharged1 hdeclN2 hcharged2 h hfd.2
        (cRawT j))
    rw [hE0, mul_zero, mul_zero]
  · by_cases hgj : ∃ n', cGateR exc1 exc2 ν1 ν2 j.1 n' (cRawS j)
        (cRawZ j) (cRawT j)
    · refine mul_le_mul_left ?_ _
      have h2 : (if cNGate exc1 exc2 ν1 ν2 i ∧ cNGate exc1 exc2 ν1 ν2 j
          ∧ j ∈ cPTgtC exc1 exc2 K1 K2 i then 4 * RTT else 0)
          = 4 * RTT := if_pos ⟨hgi, ⟨hgj, hfd⟩, hj⟩
      rw [cNc, h2]
      exact le_add_self
    · rw [cE_eq_zero_of_not_gate α Rv μ v0 exc1 exc2 ν1 ν2 hgj,
        mul_zero, mul_zero]

/-- **The priced entrance routing**: an entrance-weighted priced ledger
sum is absorbed by the raw priced row. -/
lemma cPTgtE_sum_le (eM RTT : ℝ≥0∞) {i : cIdx N} (h : ℕ) :
    (4 * eM * RTT) * ∑ j ∈ cPTgtE exc1 exc2 K1 K2 i,
        cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j
      ≤ ∑ j', cMpw exc1 exc2 K1 K2 eM RTT i j'
          * cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j' := by
  rw [Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum (fun j hj => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => zero_le)
  refine mul_le_mul_left ?_ _
  rw [cMpw, if_pos hj]
  exact le_add_self

/-- **The entrance routing**. -/
lemma cETgt_sum_le (eM RTT : ℝ≥0∞) {i : cIdx N} (h : ℕ) :
    (4 * eM) * ∑ j ∈ cETgt exc1 exc2 K1 K2 i,
        cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j
      ≤ ∑ j', cMpw exc1 exc2 K1 K2 eM RTT i j'
          * cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j' := by
  rw [Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum (fun j hj => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => zero_le)
  refine mul_le_mul_left ?_ _
  rw [cMpw, if_pos hj]
  exact le_self_add

end Routing

/-! ### Move membership facts -/

lemma comps_mem_cSrcC_some (exc : ℕ → Option (ℕ × ℕ))
    (Kf : Finset ℕ) (c : CtrC) :
    cComp0 exc c ∈ cSrcC exc Kf (some c)
      ∧ cComp1 exc c ∈ cSrcC exc Kf (some c) := by
  rw [cSrcC]
  exact ⟨Finset.mem_insert_self _ _,
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

lemma comps_mem_cSrcC_none {exc : ℕ → Option (ℕ × ℕ)}
    {Kf : Finset ℕ} {k : ℕ} (hk : k ∈ Kf) (hexc : exc k = none) :
    cComp0 exc (CtrC.ord k) ∈ cSrcC exc Kf none
      ∧ cComp1 exc (CtrC.ord k) ∈ cSrcC exc Kf none := by
  rw [cSrcC]
  constructor
  · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hexc⟩,
      Finset.mem_insert_self _ _⟩
  · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hexc⟩,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

lemma comps_mem_cSrcE_none {exc : ℕ → Option (ℕ × ℕ)}
    {Kf : Finset ℕ} {k : ℕ} (hk : k ∈ Kf) (hexc : exc k ≠ none) :
    cComp0 exc (CtrC.ord k) ∈ cSrcE exc Kf none
      ∧ cComp1 exc (CtrC.ord k) ∈ cSrcE exc Kf none := by
  rw [cSrcE]
  constructor
  · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hexc⟩,
      Finset.mem_insert_self _ _⟩
  · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hexc⟩,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

lemma none_mem_cTiltC_none (exc : ℕ → Option (ℕ × ℕ)) :
    (none : Option (Option CtrC)) ∈ cTiltC exc none := by
  rw [cTiltC]
  exact Finset.mem_singleton_self _

lemma comps_mem_cTiltC_some (exc : ℕ → Option (ℕ × ℕ))
    (c3 : CtrC) :
    some (cComp0 exc c3) ∈ cTiltC exc (some (some c3))
      ∧ some (cComp1 exc c3) ∈ cTiltC exc (some (some c3)) := by
  rw [cTiltC]
  exact ⟨Finset.mem_insert_self _ _,
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

lemma comps_mem_cTiltP {exc : ℕ → Option (ℕ × ℕ)}
    {Kf : Finset ℕ} {k' : ℕ} (hk' : k' ∈ Kf) :
    some (cComp0 exc (CtrC.ord k')) ∈ cTiltP exc Kf (some none)
      ∧ some (cComp1 exc (CtrC.ord k')) ∈ cTiltP exc Kf (some none) := by
  rw [cTiltP]
  constructor
  · exact Finset.mem_biUnion.mpr ⟨k', hk', Finset.mem_insert_self _ _⟩
  · exact Finset.mem_biUnion.mpr ⟨k', hk',
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

/-! ### The cell outputs -/

section CellOut

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ) (N : ℕ)

/-- The tilted pair screen splits into the two ordered per-child
tilts. -/
private lemma cPairScr_tilt_split (hα0 : (0 : ℝ) ≤ α) (o : Bool)
    (cs c3 : CtrC) (Z : Finset (Option CtrC)) (h : ℕ) :
    cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o cs Z (some (some c3)) h
      ≤ (∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 cs h xp
          * (screenInd (SquareRel (fullSim (cRel Rv) h))
              (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
            * (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o)
                (some (cComp0 (cExcO exc1 exc2 (!o)) c3)) h xp.1
              * cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o)
                  (some (cComp1 (cExcO exc1 exc2 (!o)) c3)) h xp.2)))
        + ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 cs h xp
            * (screenInd (SquareRel (fullSim (cRel Rv) h))
                (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
              * (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o)
                  (some (cComp1 (cExcO exc1 exc2 (!o)) c3)) h xp.1
                * cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o)
                    (some (cComp0 (cExcO exc1 exc2 (!o)) c3)) h xp.2)) := by
  rw [cPairScr_eq_tsum, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun xp => ?_
  rw [cPairW, cTiltW_some, cTiltW_some,
    cLetO_eq μ v0 exc1 exc2 ν1 ν2 (!o), cLetO_eq μ v0 exc1 exc2 ν1 ν2 (!o)]
  have hs : WresD α (cXi (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
      c3 h) (SquareRel (fullSim (cRel Rv) h)) xp
      ≤ WresD α (cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
          (cComp0 (cExcO exc1 exc2 (!o)) c3) h) (fullSim (cRel Rv) h)
          xp.1
        * WresD α (cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
            (cComp1 (cExcO exc1 exc2 (!o)) c3) h) (fullSim (cRel Rv) h)
            xp.2
      + WresD α (cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
          (cComp1 (cExcO exc1 exc2 (!o)) c3) h) (fullSim (cRel Rv) h)
          xp.1
        * WresD α (cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
            (cComp0 (cExcO exc1 exc2 (!o)) c3) h) (fullSim (cRel Rv) h)
            xp.2 := by
    rw [cXi_eq_prod]
    exact WresD_square_le_sum hα0 _ _ _ xp
  calc cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 cs h xp
        * (screenInd (SquareRel (fullSim (cRel Rv) h))
            (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
          * WresD α (cXi (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
              c3 h) (SquareRel (fullSim (cRel Rv) h)) xp)
      ≤ cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 cs h xp
          * (screenInd (SquareRel (fullSim (cRel Rv) h))
              (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
            * (WresD α (cLet (cExcO exc1 exc2 (!o)) μ
                  (cNuO ν1 ν2 (!o)) v0
                  (cComp0 (cExcO exc1 exc2 (!o)) c3) h)
                  (fullSim (cRel Rv) h) xp.1
                * WresD α (cLet (cExcO exc1 exc2 (!o)) μ
                    (cNuO ν1 ν2 (!o)) v0
                    (cComp1 (cExcO exc1 exc2 (!o)) c3) h)
                    (fullSim (cRel Rv) h) xp.2
              + WresD α (cLet (cExcO exc1 exc2 (!o)) μ
                    (cNuO ν1 ν2 (!o)) v0
                    (cComp1 (cExcO exc1 exc2 (!o)) c3) h)
                    (fullSim (cRel Rv) h) xp.1
                * WresD α (cLet (cExcO exc1 exc2 (!o)) μ
                    (cNuO ν1 ν2 (!o)) v0
                    (cComp0 (cExcO exc1 exc2 (!o)) c3) h)
                    (fullSim (cRel Rv) h) xp.2)) :=
        mul_le_mul_right (mul_le_mul_right hs _) _
    _ = _ := by ring

/-- **The unit cell output**: the descended unit pair screen of a
reachable cell splits into two successor coordinates, the moment
excess, and the quadratic singleton charge. -/
lemma cCellOutU (hα : 1 ≤ α) (o : Bool) (n h : ℕ) (cs : CtrC)
    {Z : Finset (Option CtrC)}
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
      l' ∈ cLetterBox N) :
    cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o cs Z none h
      ≤ (cE α Rv μ v0 exc1 exc2 ν1 ν2 N h
            (cMk N o hb0 (cZSuccR (cExcO exc1 exc2 (!o))
              (cKO K1 K2 (!o)) Z) option_forall_mem_none)
          + cE α Rv μ v0 exc1 exc2 ν1 ν2 N h
            (cMk N o hb1 (cZSuccR (cExcO exc1 exc2 (!o))
              (cKO K1 K2 (!o)) Z) option_forall_mem_none))
        + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
          * (2 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
        + ((cLz N K1 K2 : ℝ≥0∞)
            * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          * ((cLz N K1 K2 : ℝ≥0∞)
            * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j) := by
  refine le_trans (le_of_eq ?_) (le_trans
    (cHallOut α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα o n h cs hsc0 hsc1
      hZ hZne hsupB option_forall_mem_none option_forall_mem_none
      hb0 hb1 hZb hZSb option_forall_mem_none option_forall_mem_none)
    (one_add_mul_route (le_iSup _ _) (le_iSup _ _)))
  rw [cPairScr_eq_tsum]
  exact tsum_congr fun xp => by rw [cPairW, cTiltW_none, one_mul]

/-- **The tilted cell output**: the descended tilted pair screen of a
reachable cell splits, over the two orders, into four successor
coordinates, the moment excesses, and the quadratic singleton
charges. -/
lemma cCellOutT (hα : 1 ≤ α) (o : Bool) (n h : ℕ) (cs c3 : CtrC)
    {Z : Finset (Option CtrC)}
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
      l' ∈ cLetterBox N) :
    cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o cs Z (some (some c3)) h
      ≤ ((cE α Rv μ v0 exc1 exc2 ν1 ν2 N h
            (cMk N o hb0 (cZSuccR (cExcO exc1 exc2 (!o))
              (cKO K1 K2 (!o)) Z) (option_forall_mem_some hb30))
          + cE α Rv μ v0 exc1 exc2 ν1 ν2 N h
            (cMk N o hb1 (cZSuccR (cExcO exc1 exc2 (!o))
              (cKO K1 K2 (!o)) Z) (option_forall_mem_some hb31)))
        + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
          * (2 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
        + ((cLz N K1 K2 : ℝ≥0∞)
            * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          * ((cLz N K1 K2 : ℝ≥0∞)
            * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j))
      + ((cE α Rv μ v0 exc1 exc2 ν1 ν2 N h
            (cMk N o hb0 (cZSuccR (cExcO exc1 exc2 (!o))
              (cKO K1 K2 (!o)) Z) (option_forall_mem_some hb31))
          + cE α Rv μ v0 exc1 exc2 ν1 ν2 N h
            (cMk N o hb1 (cZSuccR (cExcO exc1 exc2 (!o))
              (cKO K1 K2 (!o)) Z) (option_forall_mem_some hb30)))
        + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
          * (2 * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
        + ((cLz N K1 K2 : ℝ≥0∞)
            * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          * ((cLz N K1 K2 : ℝ≥0∞)
            * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)) := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  refine le_trans (cPairScr_tilt_split α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2
    hα0 o cs c3 Z h) (add_le_add ?_ ?_)
  · exact le_trans (cHallOut α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα o n h
      cs hsc0 hsc1 hZ hZne hsupB (option_forall_mem_some ht30)
      (option_forall_mem_some ht31) hb0 hb1 hZb hZSb
      (option_forall_mem_some hb30) (option_forall_mem_some hb31))
      (one_add_mul_route (le_iSup _ _) (le_iSup _ _))
  · exact le_trans (cHallOut α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα o n h
      cs hsc0 hsc1 hZ hZne hsupB (option_forall_mem_some ht31)
      (option_forall_mem_some ht30) hb0 hb1 hZb hZSb
      (option_forall_mem_some hb31) (option_forall_mem_some hb30))
      (one_add_mul_route (le_iSup _ _) (le_iSup _ _))

end CellOut

end Composite
end GraphMarkovMatching
