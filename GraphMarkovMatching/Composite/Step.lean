/-
The concrete screen-ledger input is built in six modules: `StepLetters`, `StepMatrices`,
`StepRows`, `StepRouting`, `StepMain`, and this one, which carries the merged block and
the final theorems; the account below covers all six.

The concrete screen-ledger input of the composite two-law programme
(`arbitrary_offspring_matching.tex`, the screen rows `thm:screen-rows`,
the geometric bound `thm:geom`, the closed recursion `thm:engine`, and
`thm:composite-matching`).

`Debt.lean` isolates the one remaining analytic hypothesis of the
composite programme in the single named Prop `ScreenLedgerInput`: a
finite ledger vector dominating the restricted debt, satisfying the
height-0 rows, and stepping through a common/priced matrix pair with a
nilpotent common block.  This file constructs a concrete instance and
derives the final theorems.

The index (`cIdx`): tuples of an orientation, a boxed source letter, a
boxed zero-list letter set, and an optional boxed tilt letter, where the
letter box `cLetterBox N` is the explicit finite envelope of the
reachable letters (`cReach_mem_cLetterBox`, sharpening `cReach_cTame` by
the marker-stage bound `cTameB`).  A coordinate value is the letter
screen of the tuple, gated by joint reachability at a common level
(`cE`), exactly as the debts of `Main` are; the three debt classes embed
by `cDebt_le_iSup_cE`.

The matrices: the common matrix `cNc` carries weight `4` on the
full-successor moves of `thm:screen-rows` (source letter to a cell
component, zero list to the entire lifted successor set, tilt letter to
a tilt component) and weight `4·RT·T` on the priced tilt-renewal moves
whose cell move is common (`cPTgtC`), both gated by joint reachability
and by the fresh diagonal.  The tilt-renewal weight belongs to the
common block: it is uniform (never proportional to the exceptional
mass), so it rides inside the nilpotent row constant, exactly as the
one-law ledger keeps it inside `C_W` (`thm:geom`, `thm:composite-ledger`);
the row budget is `cNcBudget`.  The
priced matrix `cMp` is `χ0⁻¹` times the raw priced weights (`cMpw`),
which carry only the exceptional-entrance moves: the unit entrances at
weight `4·eM` and the priced entrances (`cPTgtE`) at weight
`4·eM·RT·T`, so the rare budget `cMpBudget` is proportional to `eM`.
Nilpotence of the common block (`cNc_nilpotent`) goes through
`cGood_nilpotent` per orientation block: gated entries embed into good
screens of the formal grammar (`cEmb`, `cNTgt_commonStep`,
`cPTgtC_commonStep`; the priced-common moves advance the cell by a
common move and the zero list by the full successor set, so the
`CommonStep` support condition is unchanged), with the anchoring
certificates supplied by `cAligned_screenAnchored` and the fresh
diagonal pruned by `screenE_cT_opposite_eq_zero`.

The step (`cE_step`): one-step descent of every coordinate
(`cInterp_cZ_succ_unit` and its tilted forms, `cInterp_cT_succ_unit_le`,
`cInterp_cT_succ_tiltZ_le`), the multi-member Hall
factorization `hallFactorize` at the descended pair screens
(`cHallOut`), the composite price conversion `cPairScreen_price` for
fresh normalizations, and the routing of the outputs: full-list screens
into `cNc`/`cMp` entries, moments and singleton products into the
explicit monotone inhomogeneity `cG`.

The finale: `screenLedgerInput_holds` packages the structure, and
`composite_failure_le_final` is the closed theorem of `Debt` with the
ledger input discharged; the
remaining hypotheses are the standing packs of both orientations, the
grammar data, the scalar budgets (`hC : cNcBudget (RT*T) ≤ C`,
`hafford : cMpBudget ≤ χ0·C`, `hcu`), the smallness `cSmallness`, the
`cG`-closure `hu`, and the threshold `heta`.  Since the rare budget is
proportional to the exceptional mass, the pack is satisfiable: `Numeric`
proves the affordability from a positive exceptional-mass threshold and
exhibits the no-exception instance.

The merged block: the gated rare rows fold into the nilpotent block at
raw weight.  `cMw` is the gated raw rare matrix (the entrance moves of
`cMpw` under the joint-reachability gate of `cNc`); gated entrance
edges are source-entrance steps of the formal grammar
(`cDict_cSrcE_mem_succ`, `cETgt_commonStepE`, `cPTgtE_commonStepE`,
against `CommonStepES`: the cell enters through the declared pairs of
its own side), so the merged matrix `cNc + cMw` is nilpotent
(`cW_nilpotent`, through `cGoodE_nilpotent`).  `cE_stepM` collapses the
raw priced row of `cE_step` onto its gated part (ungated and
fresh-diagonal coordinates vanish on both ends), and
`screenLedgerInputM_holds` packages the merged input at price zero.
`composite_failure_le_merged` / `composite_matching_le_merged` are the
final theorems with no affordability and no smallness hypotheses: the
only scalar budget left is `hC : cNcBudget + cMpBudget ≤ C`.
-/
import GraphMarkovMatching.Composite.StepMain

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type}

/-! ### The merged block: gated rare rows at raw weight -/

section MergedMatrices

variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ)

/-- **The gated raw rare matrix**: the exceptional-entrance moves of
`cMpw` under the joint-reachability gate of `cNc`.  The gate is what
lets the rare rows ride the nilpotent block at raw weight
(`eq:composite-nilpotent`): gated entrance edges are good
source-entrance steps of the formal grammar. -/
noncomputable def cMw (eM RTT : ℝ≥0∞) {N : ℕ} (i j : cIdx N) : ℝ≥0∞ :=
  (if cNGate exc1 exc2 ν1 ν2 i ∧ cNGate exc1 exc2 ν1 ν2 j
      ∧ j ∈ cETgt exc1 exc2 K1 K2 i then 4 * eM else 0)
    + (if cNGate exc1 exc2 ν1 ν2 i ∧ cNGate exc1 exc2 ν1 ν2 j
        ∧ j ∈ cPTgtE exc1 exc2 K1 K2 i then 4 * eM * RTT else 0)

/-- The gated raw rare entries sit below the raw priced weights. -/
lemma cMw_le_cMpw (eM RTT : ℝ≥0∞) {N : ℕ} (i j : cIdx N) :
    cMw exc1 exc2 ν1 ν2 K1 K2 eM RTT i j
      ≤ cMpw exc1 exc2 K1 K2 eM RTT i j := by
  rw [cMw, cMpw]
  refine add_le_add ?_ ?_
  · by_cases hj : cNGate exc1 exc2 ν1 ν2 i ∧ cNGate exc1 exc2 ν1 ν2 j
        ∧ j ∈ cETgt exc1 exc2 K1 K2 i
    · rw [if_pos hj, if_pos hj.2.2]
    · rw [if_neg hj]
      exact zero_le
  · by_cases hj : cNGate exc1 exc2 ν1 ν2 i ∧ cNGate exc1 exc2 ν1 ν2 j
        ∧ j ∈ cPTgtE exc1 exc2 K1 K2 i
    · rw [if_pos hj, if_pos hj.2.2]
    · rw [if_neg hj]
      exact zero_le

/-- The gated raw rare row bound: at most the raw priced budget. -/
lemma cMw_row_le (eM RTT : ℝ≥0∞) {N : ℕ} (i : cIdx N) :
    ∑ j, cMw exc1 exc2 ν1 ν2 K1 K2 eM RTT i j
      ≤ cMpBudget eM RTT (cMx K1 K2) :=
  le_trans (Finset.sum_le_sum fun j _ =>
      cMw_le_cMpw exc1 exc2 ν1 ν2 K1 K2 eM RTT i j)
    (cMpw_row_le exc1 exc2 K1 K2 eM RTT i)

/-- Under the gates of both endpoints the gated raw rare entry recovers
the raw priced weight. -/
lemma cMw_eq_cMpw_of_gates (eM RTT : ℝ≥0∞) {N : ℕ} {i j : cIdx N}
    (hgi : cNGate exc1 exc2 ν1 ν2 i) (hgj : cNGate exc1 exc2 ν1 ν2 j) :
    cMw exc1 exc2 ν1 ν2 K1 K2 eM RTT i j
      = cMpw exc1 exc2 K1 K2 eM RTT i j := by
  rw [cMw, cMpw]
  congr 1
  · by_cases hP : j ∈ cETgt exc1 exc2 K1 K2 i
    · rw [if_pos hP, if_pos ⟨hgi, hgj, hP⟩]
    · rw [if_neg hP, if_neg fun hc => hP hc.2.2]
  · by_cases hP : j ∈ cPTgtE exc1 exc2 K1 K2 i
    · rw [if_pos hP, if_pos ⟨hgi, hgj, hP⟩]
    · rw [if_neg hP, if_neg fun hc => hP hc.2.2]

end MergedMatrices

/-- Exceptional-entrance source moves land in the declared-entrance
successor set of the source cell: the moved letters are the components
of the declared marker at stage `0`, whose dictionary images lie in
`succM p.1 p.2 0` (`cDict_markComp_mem_succM`) for the declared pair
`p` of the side, hence in the entrance clause of `succ`. -/
lemma cDict_cSrcE_mem_succ {exc : ℕ → Option (ℕ × ℕ)} {ν : PMF ℕ}
    {Kf S : Finset ℕ} {Egr : Finset (ℕ × ℕ)}
    (hsup : ∀ k, (ν k : ℝ≥0∞) ≠ 0 ↔ k ∈ Kf)
    (hEg : ∀ p, p ∈ Egr ↔ ∃ z, (ν z : ℝ≥0∞) ≠ 0 ∧ exc z = some p)
    {s s' : Option CtrC} (hs' : s' ∈ cSrcE exc Kf s) :
    cDict s' ∈ succ S Egr (cDict s) := by
  cases s with
  | some c =>
      rw [cSrcE] at hs'
      exact absurd hs' (Finset.notMem_empty _)
  | none =>
      rw [cSrcE, Finset.mem_biUnion] at hs'
      obtain ⟨k, hk, hs'⟩ := hs'
      obtain ⟨hkK, hexc⟩ := Finset.mem_filter.mp hk
      rcases hp : exc k with _ | p
      · exact absurd hp hexc
      rw [cDict_none, succ_F]
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨p, (hEg p).mpr ⟨k, (hsup k).mpr hkK, hp⟩, ?_⟩)
      have hcm := cDict_markComp_mem_succM p.1 p.2 0
      rcases Finset.mem_insert.mp hs' with rfl | hs'
      · rw [cComp0_ord_some hp]
        exact hcm.1
      · rw [Finset.mem_singleton.mp hs', cComp1_ord_some hp]
        exact hcm.2

section MergedNilpotent

variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (N : ℕ)

section MergedDispatch

variable (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
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

include hN hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1
  hEg2 in
/-- Gated moves with an exceptional-entrance cell component are
source-entrance steps of the formal grammar: the cell enters through a
declared pair of its own side (`cDict_cSrcE_mem_succ`), the zero list
advances to the entire lifted successor set of the target side, and the
tilt rides along unseen. -/
private lemma cEntranceCell_commonStepES {i : cIdx N}
    (hgi : cNGate exc1 exc2 ν1 ν2 i) {sp : cLB N}
    (hsp : sp ∈ cLiftB N (cSrcE (cExcO exc1 exc2 i.1) (cKO K1 K2 i.1)
      (cRawS i)))
    (tp : Option (cLB N)) :
    CommonStepES S (cEgO E1 E2 i.1) (cEgO E1 E2 (!i.1)) (cEmb N i.2)
      (cEmb N (sp, cLiftB N (cZSuccR (cExcO exc1 exc2 (!i.1))
        (cKO K1 K2 (!i.1)) (cRawZ i)), tp)) := by
  obtain ⟨⟨n, hr1, hrZ, hrT, hZne⟩, hfd⟩ := hgi
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
  · show cDict sp.1 ∈ succ S (cEgO E1 E2 i.1) (cDict (cRawS i))
    exact cDict_cSrcE_mem_succ
      (cSupO ν1 ν2 K1 K2 hsup1 hsup2 i.1)
      (cEgO_char exc1 exc2 ν1 ν2 E1 E2 hEg1 hEg2 i.1)
      (mem_cLiftB.mp hsp)
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
/-- Gated exceptional-entrance moves are source-entrance steps of the
formal grammar. -/
lemma cETgt_commonStepE {i j : cIdx N}
    (hgi : cNGate exc1 exc2 ν1 ν2 i)
    (hj : j ∈ cETgt exc1 exc2 K1 K2 i) :
    CommonStepES S (cEgO E1 E2 i.1) (cEgO E1 E2 (!i.1)) (cEmb N i.2)
      (cEmb N j.2) := by
  obtain ⟨pr, hpr, hj⟩ := Finset.mem_image.mp hj
  subst hj
  exact cEntranceCell_commonStepES exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N hN
    hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1 hEg2 hgi
    (Finset.mem_product.mp hpr).1 pr.2

include hN hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1
  hEg2 in
/-- Gated priced tilt moves with an exceptional entrance cell move are
source-entrance steps of the formal grammar. -/
lemma cPTgtE_commonStepE {i j : cIdx N}
    (hgi : cNGate exc1 exc2 ν1 ν2 i)
    (hj : j ∈ cPTgtE exc1 exc2 K1 K2 i) :
    CommonStepES S (cEgO E1 E2 i.1) (cEgO E1 E2 (!i.1)) (cEmb N i.2)
      (cEmb N j.2) := by
  obtain ⟨pr, hpr, hj⟩ := Finset.mem_image.mp hj
  subst hj
  exact cEntranceCell_commonStepES exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N hN
    hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1 hEg2 hgi
    (Finset.mem_product.mp hpr).1 pr.2

end MergedDispatch

end MergedNilpotent

/-- **Nilpotence of the merged block** (`eq:composite-nilpotent` for
the concrete merged matrix): the gated common matrix together with the
gated raw rare matrix is annihilated by `cRank N` applications of
`mulVec`, through `cGoodE_nilpotent` per orientation block.  The common
and priced-common moves lift through `CommonStep.toES`; the entrance
and priced-entrance moves are source-entrance steps. -/
theorem cW_nilpotent
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (N : ℕ)
    (eM RTT : ℝ≥0∞) (hSne : S.Nonempty)
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
    (mulVec (fun i j => cNc exc1 exc2 ν1 ν2 K1 K2 RTT (N := N) i j
        + cMw exc1 exc2 ν1 ν2 K1 K2 eM RTT i j))^[cRank N]
        (fun _ => 1)
      = fun _ => 0 := by
  have hbd : ∀ (o : Bool) (p : cPay N) (o' : Bool) (q : cPay N),
      o ≠ o' →
      cNc exc1 exc2 ν1 ν2 K1 K2 RTT ((o, p) : cIdx N) (o', q)
        + cMw exc1 exc2 ν1 ν2 K1 K2 eM RTT ((o, p) : cIdx N) (o', q)
        = 0 := by
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
    have hb3 : ¬(cNGate exc1 exc2 ν1 ν2 ((o, p) : cIdx N)
        ∧ cNGate exc1 exc2 ν1 ν2 ((o', q) : cIdx N)
        ∧ ((o', q) : cIdx N)
          ∈ cETgt exc1 exc2 K1 K2 ((o, p) : cIdx N)) := by
      rintro ⟨_, _, hj⟩
      obtain ⟨pr, _, hj⟩ := Finset.mem_image.mp hj
      exact hne (congrArg Prod.fst hj)
    have hb4 : ¬(cNGate exc1 exc2 ν1 ν2 ((o, p) : cIdx N)
        ∧ cNGate exc1 exc2 ν1 ν2 ((o', q) : cIdx N)
        ∧ ((o', q) : cIdx N)
          ∈ cPTgtE exc1 exc2 K1 K2 ((o, p) : cIdx N)) := by
      rintro ⟨_, _, hj⟩
      obtain ⟨pr, _, hj⟩ := Finset.mem_image.mp hj
      exact hne (congrArg Prod.fst hj)
    rw [cNc, cMw, if_neg hb1, if_neg hb2, if_neg hb3, if_neg hb4]
    simp
  funext i
  obtain ⟨o, p⟩ := i
  rw [mulVec_iterate_block _ hbd (cRank N) _ o p]
  have hsupp : ∀ p q : cPay N,
      cNc exc1 exc2 ν1 ν2 K1 K2 RTT ((o, p) : cIdx N) (o, q)
          + cMw exc1 exc2 ν1 ν2 K1 K2 eM RTT ((o, p) : cIdx N) (o, q)
        ≠ 0 →
      CommonStepES S (cEgO E1 E2 o) (cEgO E1 E2 (!o)) (cEmb N p)
          (cEmb N q)
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
            ∈ cPTgtC exc1 exc2 K1 K2 ((o, p) : cIdx N))
        ∨ (cNGate exc1 exc2 ν1 ν2 ((o, p) : cIdx N)
          ∧ cNGate exc1 exc2 ν1 ν2 ((o, q) : cIdx N)
          ∧ ((o, q) : cIdx N)
            ∈ cETgt exc1 exc2 K1 K2 ((o, p) : cIdx N))
        ∨ (cNGate exc1 exc2 ν1 ν2 ((o, p) : cIdx N)
          ∧ cNGate exc1 exc2 ν1 ν2 ((o, q) : cIdx N)
          ∧ ((o, q) : cIdx N)
            ∈ cPTgtE exc1 exc2 K1 K2 ((o, p) : cIdx N)) := by
      by_contra hc
      rw [not_or, not_or, not_or] at hc
      obtain ⟨h1, h2, h3, h4⟩ := hc
      rw [cNc, cMw, if_neg h1, if_neg h2, if_neg h3, if_neg h4] at hne
      simp at hne
    have hstep : CommonStepES S (cEgO E1 E2 o) (cEgO E1 E2 (!o))
          (cEmb N p) (cEmb N q)
        ∧ cNGate exc1 exc2 ν1 ν2 ((o, p) : cIdx N)
        ∧ cNGate exc1 exc2 ν1 ν2 ((o, q) : cIdx N) := by
      rcases hcond with ⟨hgi, hgj, hjt⟩ | ⟨hgi, hgj, hjt⟩
        | ⟨hgi, hgj, hjt⟩ | ⟨hgi, hgj, hjt⟩
      · exact ⟨(cNTgt_commonStep exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N hN
          hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1 hEg2
          hgi hjt).toES, hgi, hgj⟩
      · exact ⟨(cPTgtC_commonStep exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N hN
          hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1 hEg2
          hgi hjt).toES, hgi, hgj⟩
      · exact ⟨cETgt_commonStepE exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N hN
          hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1 hEg2
          hgi hjt, hgi, hgj⟩
      · exact ⟨cPTgtE_commonStepE exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N hN
          hdeclN1 hdeclN2 hcharged1 hcharged2 hsup1 hsup2 hS1 hEg1 hEg2
          hgi hjt, hgi, hgj⟩
    obtain ⟨hcs, hgi, hgj⟩ := hstep
    refine ⟨hcs, ?_, ?_⟩
    · exact cNGate_cGood exc1 exc2 ν1 ν2 S E1 E2 N hN hdecl1 hdecl2
        hdeclN1 hdeclN2 hcharged1 hcharged2 hS1 hEg1 hEg2 hgi
    · exact cNGate_cGood exc1 exc2 ν1 ν2 S E1 E2 N hN hdecl1 hdecl2
        hdeclN1 hdeclN2 hcharged1 hcharged2 hS1 hEg1 hEg2 hgj
  have hnil := cGoodE_nilpotent S hSne (cEgO E1 E2 o) (cEgO E1 E2 (!o))
    (cESO exc1 exc2 ν1 ν2 S E1 E2 N hN hdecl1 hdecl2 hdeclN1 hdeclN2
      hcharged1 hcharged2 hS1 hEg1 hEg2 o)
    (cEmb N)
    (fun p q => cNc exc1 exc2 ν1 ν2 K1 K2 RTT ((o, p) : cIdx N) (o, q)
      + cMw exc1 exc2 ν1 ν2 K1 K2 eM RTT ((o, p) : cIdx N) (o, q))
    hsupp
  have := congrFun hnil p
  simp only [cRank]
  exact this

/-! ### The merged step and the merged final theorems -/

section MergedStep

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ) (N : ℕ)

/-- **The merged ledger step**: the gated one-step row against the
merged common-plus-gated-rare matrix at raw weight.  The raw priced row
of `cVal_step_le` collapses onto its gated part: an ungated or
fresh-diagonal source vanishes at height `h + 1`, and an ungated or
fresh-diagonal target contributes zero to both sides. -/
theorem cE_stepM
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
    (h : ℕ) (i : cIdx N) :
    cE α Rv μ v0 exc1 exc2 ν1 ν2 N (h + 1) i
      ≤ cG α Rv μ T RT (cLz N K1 K2)
          (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)
          (⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
        + ∑ j', (cNc exc1 exc2 ν1 ν2 K1 K2 (RT * T) i j'
              + cMw exc1 exc2 ν1 ν2 K1 K2 eM (RT * T) i j')
            * cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j' := by
  refine iSup_le fun n => iSup_le fun hg => ?_
  by_cases hfd : cRawS i = none ∧ none ∈ cRawZ i
  · rw [cVal, hfd.1, cInterp_fdiag_eq_zero α Rv μ v0 exc1 exc2 ν1 ν2 N
      i.1 hRv hμ0 hN hdeclN1 hcharged1 hdeclN2 hcharged2 (h + 1) hfd.2]
    exact zero_le
  · have hgi : cNGate exc1 exc2 ν1 ν2 i := ⟨⟨n, hg⟩, hfd⟩
    refine le_trans (cVal_step_le α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα
      hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2 hpair1
      hpair2 hdecl1 hdecl2 hsup1 hsup2 T RT eM hT1 hT2 hRT heM1 heM2
      h i n hg) ?_
    refine add_le_add le_rfl ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [add_mul]
    refine add_le_add le_rfl ?_
    by_cases hgj : cNGate exc1 exc2 ν1 ν2 j
    · exact le_of_eq (by
        rw [cMw_eq_cMpw_of_gates exc1 exc2 ν1 ν2 K1 K2 eM (RT * T) hgi
          hgj])
    · have hE0 : cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j = 0 := by
        rw [cNGate, not_and_or] at hgj
        rcases hgj with hng | hfdj
        · exact cE_eq_zero_of_not_gate α Rv μ v0 exc1 exc2 ν1 ν2 hng
        · rw [not_not] at hfdj
          refine le_antisymm (iSup_le fun n' => iSup_le fun _ => ?_)
            zero_le
          rw [cVal, hfdj.1]
          exact le_of_eq (cInterp_fdiag_eq_zero α Rv μ v0 exc1 exc2 ν1
            ν2 N j.1 hRv hμ0 hN hdeclN1 hcharged1 hdeclN2 hcharged2 h
            hfdj.2 (cRawT j))
      rw [hE0, mul_zero, mul_zero]

end MergedStep

section MergedFinale

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (N : ℕ)

/-- **The merged screen-ledger input** (`thm:screen-rows`,
`thm:composite-acyclic`, `thm:zero-interface` assembled, merged form):
the
ledger vector `cE`, the merged matrix `cNc + cMw`, the zero priced
matrix, and the price `0` satisfy `ScreenLedgerInput` at any row budget
above `cNcBudget + cMpBudget`; no affordability and no smallness data
enter. -/
theorem screenLedgerInputM_holds
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
    (C cu : ℝ≥0∞)
    (hC : cNcBudget (RT * T) (cMx K1 K2)
        + cMpBudget eM (RT * T) (cMx K1 K2) ≤ C)
    (hcu : 2 ≤ cu) :
    ScreenLedgerInput α Rv μ v0 exc1 exc2 ν1 ν2
      (cE α Rv μ v0 exc1 exc2 ν1 ν2 N)
      (fun i j => cNc exc1 exc2 ν1 ν2 K1 K2 (RT * T) (N := N) i j
        + cMw exc1 exc2 ν1 ν2 K1 K2 eM (RT * T) i j)
      (fun _ _ => 0)
      (cG α Rv μ T RT (cLz N K1 K2)) 0 C (cRank N) cu where
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
  common_row := fun i => by
    show (∑ j, (cNc exc1 exc2 ν1 ν2 K1 K2 (RT * T) i j
        + cMw exc1 exc2 ν1 ν2 K1 K2 eM (RT * T) i j)) ≤ C
    rw [Finset.sum_add_distrib]
    exact le_trans (add_le_add
      (cNc_row_le exc1 exc2 ν1 ν2 K1 K2 (RT * T) i)
      (cMw_row_le exc1 exc2 ν1 ν2 K1 K2 eM (RT * T) i)) hC
  priced_row := fun i => by simp
  rank_pos := cRank_pos N
  common_nilpotent := cW_nilpotent exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N eM
    (RT * T) hSne hN hdecl1 hdecl2 hdeclN1 hdeclN2 hcharged1 hcharged2
    hsup1 hsup2 hS1 hEg1 hEg2
  step := fun h i => by
    refine le_trans (cE_stepM α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 N hα hRv
      hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2 hpair1
      hpair2 hdecl1 hdecl2 hsup1 hsup2 T RT eM hT1 hT2 hRT heM1 heM2
      h i) (add_le_add le_rfl (le_of_eq ?_))
    rw [mulVecInf, tsum_fintype]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [rareMatrix, zero_mul, add_zero]

/-- **Composite two-law mismatch bound, merged form**
(`thm:composite-matching`, finite heights):
`composite_failure_le_final` with
the rare rows folded into the nilpotent block at raw weight.  No
affordability and no smallness hypotheses remain; the only scalar row
budget is `hC : cNcBudget + cMpBudget ≤ C`, and the smallness condition
holds vacuously at price zero (`cSmallness_zero`). -/
theorem composite_failure_le_merged
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
    (C cu : ℝ≥0∞)
    (hC : cNcBudget (RT * T) (cMx K1 K2)
        + cMpBudget eM (RT * T) (cMx K1 K2) ≤ C)
    (hcu : 2 ≤ cu)
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
    (screenLedgerInputM_holds α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N
      hα hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2
      hpair1 hpair2 hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2 T RT
      eM hT1 hT2 hRT heM1 heM2 C cu hC hcu)
    (cSmallness_zero C (cRank N)) hu heta

/-- **Composite two-law infinite matching, merged form**
(`thm:composite-matching`): the closed infinite matching with the rare
rows folded into the nilpotent block at raw weight; no affordability and
no smallness hypotheses remain.  One binary-tree automorphism matches the
two infinite composite samples with probability at least
`1 - cKc * etaG`. -/
theorem composite_matching_le_merged {Omega : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Omega] (Pm : Measure Omega)
    [IsProbabilityMeasure Pm]
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
    (C cu : ℝ≥0∞)
    (hC : cNcBudget (RT * T) (cMx K1 K2)
        + cMpBudget eM (RT * T) (cMx K1 K2) ≤ C)
    (hcu : 2 ≤ cu)
    (hu : cG α Rv μ T RT (cLz N K1 K2)
        (cKc δ L K μ v0 T κ (cX C (cRank N) cu) * etaG α Rv μ)
        (cX C (cRank N) cu * etaG α Rv μ) ≤ cu * etaG α Rv μ)
    (heta : etaG α Rv μ
      ≤ cEtaStar α δ L K μ v0 T κ (cX C (cRank N) cu))
    (Xs Ys : (n : ℕ) → Omega → FullLab (CState V) n)
    (hXs : ∀ n omega, restrictLab n (Xs (n + 1) omega) = Xs n omega)
    (hYs : ∀ n omega, restrictLab n (Ys (n + 1) omega) = Ys n omega)
    (hpairM : ∀ n, Measurable (fun omega => (Xs n omega, Ys n omega)))
    (hlaw : ∀ n, Pm.map (fun omega => (Xs n omega, Ys n omega)) =
      (prodPMF (cT exc1 μ ν1 v0 n) (cT exc2 μ ν2 v0 n)).toMeasure) :
    1 - cKc δ L K μ v0 T κ (cX C (cRank N) cu) * etaG α Rv μ
      ≤ Pm {omega | InfMatch (cRel Rv)
          (fun n => Xs n omega) (fun n => Ys n omega)} :=
  composite_matching_le_closed Pm α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 hα hδ
    hL0 hL hK0 hK hRv hsymm hμ0 hpair1 hdecl1
    (fun k hk => (hsup1 k).mp hk) hpair2 hdecl2
    (fun k hk => (hsup2 k).mp hk) N hN
    (fun k p hp => (hdeclN1 k p hp))
    (fun k hk he => hcharged1 k hk he) T κ hT1 hT2 hκ1 hκ2 hlam
    (screenLedgerInputM_holds α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N
      hα hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2
      hpair1 hpair2 hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2 T RT
      eM hT1 hT2 hRT heM1 heM2 C cu hC hcu)
    (cSmallness_zero C (cRank N)) hu heta
    Xs Ys hXs hYs hpairM hlaw

end MergedFinale

end Composite
end GraphMarkovMatching
