/-
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
(`cInterp_cZ_succ`, `cInterp_cT_succ_le`), the multi-member Hall
factorization `hallFactorize` at the descended pair screens
(`cHallOut`), the composite price conversion `cPairScreen_price` for
fresh normalizations, and the routing of the outputs: full-list screens
into `cNc`/`cMp` entries, moments and singleton products into the
explicit monotone inhomogeneity `cG`.

The finale: `screenLedgerInput_holds` packages the structure, and
`composite_failure_le_final` / `composite_matching_le_final` are the
closed theorems of `Debt` with the ledger input discharged; the
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
import GraphMarkovMatching.Composite.Debt
import GraphMarkovMatching.Process.Factorize

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type}

/-! ### The bounded tameness envelope and the letter box -/

/-- Bounded tameness: the reachability envelope `cTame` sharpened by the
marker-stage certificate: a reachable marker is either at stage `0` or
records `2 ^ (i + 1) ≤ a`, so its stage is bounded by the running
value. -/
def cTameB (exc : ℕ → Option (ℕ × ℕ)) (N : ℕ) : Option CtrC → Prop
  | none => True
  | some (CtrC.ord j) => j ≤ N ∧ exc j = none
  | some (CtrC.mark a b i) => a ≤ N ∧ b ≤ N ∧ (i = 0 ∨ 2 ^ (i + 1) ≤ a)

/-- The components of a common bounded counter are boundedly tame. -/
lemma cTameB_comps_ord (exc : ℕ → Option (ℕ × ℕ)) (N : ℕ)
    (hN : ∀ j, j ≤ N → exc j = none) {k : ℕ} (hk : k ≤ N)
    (hexc : exc k = none) :
    cTameB exc N (cComp0 exc (CtrC.ord k))
      ∧ cTameB exc N (cComp1 exc (CtrC.ord k)) := by
  rw [cComp0_ord_none hexc, cComp1_ord_none hexc]
  rcases Nat.lt_or_ge k 3 with h2 | h3
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact ⟨trivial, trivial⟩
  · rcases Nat.lt_or_ge k 4 with h4 | h4
    · rw [if_neg (by omega), if_pos (by omega : k = 3),
        if_neg (by omega)]
      exact ⟨⟨by omega, hN 2 (by omega)⟩, trivial⟩
    · rw [if_pos h4, if_pos h4]
      exact ⟨⟨by omega, hN _ (by omega)⟩, ⟨by omega, hN _ (by omega)⟩⟩

/-- The components of a bounded marker are boundedly tame: the next
marker regenerates the stage certificate from the halving rule. -/
lemma cTameB_markComp (exc : ℕ → Option (ℕ × ℕ)) (N : ℕ)
    (hN : ∀ j, j ≤ N → exc j = none) {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N)
    (i : ℕ) :
    cTameB exc N (markComp0 a b i) ∧ cTameB exc N (markComp1 a b i) := by
  have hval : val a i ≤ a := Nat.div_le_self a (2 ^ i)
  rcases Nat.lt_or_ge (val a i) 3 with h2 | h3
  · rw [markComp0, if_neg (by omega), if_neg (by omega),
      markComp1, if_neg (by omega), if_neg (by omega)]
    exact ⟨⟨hb, hN b hb⟩, trivial⟩
  · rcases Nat.lt_or_ge (val a i) 4 with h4 | h4
    · have h3' : val a i = 3 := by omega
      rw [markComp0, if_neg (by omega), if_pos h3',
        markComp1, if_neg (by omega), if_pos h3']
      exact ⟨⟨by omega, hN 2 (by omega)⟩, ⟨hb, hN b hb⟩⟩
    · rw [markComp0, if_pos h4, markComp1, if_pos h4]
      have hstage : 2 ^ (i + 1 + 1) ≤ a := by
        have hdiv : 4 * 2 ^ i ≤ a := by
          have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos i)).mp h4
          omega
        have hpow : 2 ^ (i + 1 + 1) = 4 * 2 ^ i := by
          rw [pow_succ, pow_succ]
          ring
        omega
      exact ⟨⟨ha, hb, Or.inr hstage⟩, ⟨by omega, hN _ (by omega)⟩⟩

/-- One spawn step preserves bounded tameness. -/
lemma cTameB_of_cSpawn (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (N : ℕ)
    (hN : ∀ j, j ≤ N → exc j = none)
    (hch : ∀ k, (ν k : ℝ≥0∞) ≠ 0 → exc k = none → k ≤ N)
    (hdeclB : ∀ k p, exc k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    {l m : Option CtrC} (hl : cTameB exc N l) (hsp : cSpawn exc ν l m) :
    cTameB exc N m := by
  cases l with
  | none =>
      obtain ⟨k, hk, hor⟩ := hsp
      rcases hexc : exc k with _ | p
      · have hcm := cTameB_comps_ord exc N hN (hch k hk hexc) hexc
        rcases hor with rfl | rfl
        · exact hcm.1
        · exact hcm.2
      · obtain ⟨h1, h2⟩ := hdeclB k p hexc
        have hcm := cTameB_markComp exc N hN h1 h2 0
        rcases hor with rfl | rfl
        · rw [cComp0_ord_some hexc]
          exact hcm.1
        · rw [cComp1_ord_some hexc]
          exact hcm.2
  | some c =>
      cases c with
      | ord j =>
          have hl' : j ≤ N ∧ exc j = none := hl
          have hcm := cTameB_comps_ord exc N hN hl'.1 hl'.2
          rcases hsp with rfl | rfl
          · exact hcm.1
          · exact hcm.2
      | mark a b i =>
          have hl' : a ≤ N ∧ b ≤ N ∧ (i = 0 ∨ 2 ^ (i + 1) ≤ a) := hl
          have hcm := cTameB_markComp exc N hN hl'.1 hl'.2.1 i
          rcases hsp with rfl | rfl
          · rw [cComp0_mark]
            exact hcm.1
          · rw [cComp1_mark]
            exact hcm.2

/-- Reachable letters are boundedly tame. -/
theorem cReach_cTameB (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (N : ℕ)
    (hN : ∀ j, j ≤ N → exc j = none)
    (hch : ∀ k, (ν k : ℝ≥0∞) ≠ 0 → exc k = none → k ≤ N)
    (hdeclB : ∀ k p, exc k = some p → p.1 ≤ N ∧ p.2 ≤ N) :
    ∀ {n : ℕ} {l : Option CtrC}, cReach exc ν n l → cTameB exc N l := by
  intro n
  induction n with
  | zero =>
      intro l hl
      have hl' : l = none := hl
      subst hl'
      trivial
  | succ n ih =>
      intro l hl
      obtain ⟨l', hl', hsp⟩ := hl
      exact cTameB_of_cSpawn exc ν N hN hch hdeclB (ih hl') hsp

/-- The letter box: the fresh letter, the common counters up to `N`, and
the markers with data and stage up to `N`.  Every boundedly tame letter
lies in the box. -/
def cLetterBox (N : ℕ) : Finset (Option CtrC) :=
  insert none
    (((Finset.range (N + 1)).image fun j => some (CtrC.ord j))
      ∪ ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)
            ×ˢ Finset.range (N + 1)).image
          fun t => some (CtrC.mark t.1 t.2.1 t.2.2)))

lemma none_mem_cLetterBox (N : ℕ) : none ∈ cLetterBox N :=
  Finset.mem_insert_self _ _

lemma ord_mem_cLetterBox {N j : ℕ} (hj : j ≤ N) :
    some (CtrC.ord j) ∈ cLetterBox N := by
  refine Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_)
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩

lemma mark_mem_cLetterBox {N a b i : ℕ} (ha : a ≤ N) (hb : b ≤ N)
    (hi : i ≤ N) : some (CtrC.mark a b i) ∈ cLetterBox N := by
  refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
  refine Finset.mem_image.mpr ⟨(a, b, i), ?_, rfl⟩
  simp only [Finset.mem_product, Finset.mem_range]
  exact ⟨by omega, by omega, by omega⟩

/-- **`eq:composite-cardinals`, the alphabet count**: the letter box has exactly
`n_A = (N+1)³ + N + 2` letters. -/
lemma cLetterBox_card (N : ℕ) :
    (cLetterBox N).card = (N + 1) ^ 3 + N + 2 := by
  have hord : Function.Injective fun j : ℕ => some (CtrC.ord j) := by
    intro a b h
    simpa using h
  have hmark : Function.Injective
      fun t : ℕ × ℕ × ℕ => some (CtrC.mark t.1 t.2.1 t.2.2) := by
    intro a b h
    simp only [Option.some.injEq, CtrC.mark.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hnone : (none : Option CtrC) ∉
      ((Finset.range (N + 1)).image fun j => some (CtrC.ord j))
      ∪ ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)
            ×ˢ Finset.range (N + 1)).image
          fun t => some (CtrC.mark t.1 t.2.1 t.2.2)) := by
    simp
  have hdisj : Disjoint
      ((Finset.range (N + 1)).image fun j => some (CtrC.ord j))
      ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)
            ×ˢ Finset.range (N + 1)).image
          fun t => some (CtrC.mark t.1 t.2.1 t.2.2)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image] at ha hb
    obtain ⟨j, -, rfl⟩ := ha
    obtain ⟨t, -, ht⟩ := hb
    simp at ht
  rw [cLetterBox, Finset.card_insert_of_notMem hnone,
    Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hord,
    Finset.card_image_of_injective _ hmark]
  simp only [Finset.card_product, Finset.card_range]
  ring

/-- Boundedly tame letters lie in the box: the stage certificate forces
`i ≤ N` through `i + 1 < 2 ^ (i + 1)`. -/
lemma cTameB_mem_cLetterBox {exc : ℕ → Option (ℕ × ℕ)} {N : ℕ}
    {l : Option CtrC} (hl : cTameB exc N l) : l ∈ cLetterBox N := by
  cases l with
  | none => exact none_mem_cLetterBox N
  | some c =>
      cases c with
      | ord j => exact ord_mem_cLetterBox hl.1
      | mark a b i =>
          obtain ⟨ha, hb, hi⟩ := hl
          refine mark_mem_cLetterBox ha hb ?_
          rcases hi with rfl | hi
          · omega
          · have hlt : i + 1 < 2 ^ (i + 1) :=
              Nat.lt_pow_self (by omega)
            omega

/-- Reachable letters lie in the box. -/
theorem cReach_mem_cLetterBox (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ)
    (N : ℕ) (hN : ∀ j, j ≤ N → exc j = none)
    (hch : ∀ k, (ν k : ℝ≥0∞) ≠ 0 → exc k = none → k ≤ N)
    (hdeclB : ∀ k p, exc k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    {n : ℕ} {l : Option CtrC} (hl : cReach exc ν n l) :
    l ∈ cLetterBox N :=
  cTameB_mem_cLetterBox (cReach_cTameB exc ν N hN hch hdeclB hl)

/-! ### The debt index: orientation dispatchers, coordinates, gates -/

section Index

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (K1 K2 : Finset ℕ)

/-- The exceptional chart of an orientation: `false` reads side 1. -/
def cExcO : Bool → ℕ → Option (ℕ × ℕ)
  | false => exc1
  | true => exc2

/-- The offspring law of an orientation. -/
noncomputable def cNuO : Bool → PMF ℕ
  | false => ν1
  | true => ν2

/-- The support of an orientation. -/
def cKO : Bool → Finset ℕ
  | false => K1
  | true => K2

@[simp] lemma cExcO_false : cExcO exc1 exc2 false = exc1 := rfl
@[simp] lemma cExcO_true : cExcO exc1 exc2 true = exc2 := rfl
@[simp] lemma cNuO_false : cNuO ν1 ν2 false = ν1 := rfl
@[simp] lemma cNuO_true : cNuO ν1 ν2 true = ν2 := rfl
@[simp] lemma cKO_false : cKO K1 K2 false = K1 := rfl
@[simp] lemma cKO_true : cKO K1 K2 true = K2 := rfl

lemma cLetO_eq (o : Bool) (l : Option CtrC) (h : ℕ) :
    cLetO μ v0 exc1 exc2 ν1 ν2 o l h
      = cLet (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 l h := by
  cases o <;> rfl

lemma cReachO_eq (o : Bool) :
    cReachO exc1 exc2 ν1 ν2 o
      = cReach (cExcO exc1 exc2 o) (cNuO ν1 ν2 o) := by
  cases o <;> rfl

/-- The zero-list laws of a raw letter set. -/
noncomputable def cZLaws (o : Bool) (Z : Finset (Option CtrC)) (h : ℕ) :
    List (PMF (FullLab (CState V) h)) :=
  Z.toList.map fun l => cLetO μ v0 exc1 exc2 ν1 ν2 o l h

lemma mem_cZLaws {o : Bool} {Z : Finset (Option CtrC)} {h : ℕ}
    {ρ : PMF (FullLab (CState V) h)} :
    ρ ∈ cZLaws μ v0 exc1 exc2 ν1 ν2 o Z h
      ↔ ∃ l ∈ Z, ρ = cLetO μ v0 exc1 exc2 ν1 ν2 o l h := by
  rw [cZLaws, List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Finset.mem_toList.mp hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Finset.mem_toList.mpr hl, rfl⟩

/-- The tilt weight of an optional tilt letter: `none` is the unit
normalization, `some l` the restricted inverse degree of the letter. -/
noncomputable def cTiltW (o : Bool) (t : Option (Option CtrC)) (h : ℕ) :
    FullLab (CState V) h → ℝ≥0∞ :=
  match t with
  | none => fun _ => 1
  | some l => WresD α (cLetO μ v0 exc1 exc2 ν1 ν2 o l h)
      (fullSim (cRel Rv) h)

@[simp] lemma cTiltW_none (o : Bool) (h : ℕ) :
    cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 o none h = fun _ => 1 := rfl

@[simp] lemma cTiltW_some (o : Bool) (l : Option CtrC) (h : ℕ) :
    cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 o (some l) h
      = WresD α (cLetO μ v0 exc1 exc2 ν1 ν2 o l h)
          (fullSim (cRel Rv) h) := rfl

/-- The raw coordinate interpretation: the letter screen of an
orientation, a source letter, a zero-list letter set, and an optional
tilt letter. -/
noncomputable def cInterp (h : ℕ) (o : Bool) (s : Option CtrC)
    (Z : Finset (Option CtrC)) (t : Option (Option CtrC)) : ℝ≥0∞ :=
  screenE (cLetO μ v0 exc1 exc2 ν1 ν2 o s h) (fullSim (cRel Rv) h)
    (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z h)
    (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t h)

/-- The reachability gate of a raw coordinate: joint reachability of
all letters at a common level, and a nonempty zero list. -/
def cGateR (o : Bool) (n : ℕ) (s : Option CtrC) (Z : Finset (Option CtrC))
    (t : Option (Option CtrC)) : Prop :=
  cReachO exc1 exc2 ν1 ν2 o n s
    ∧ (∀ l ∈ Z, cReachO exc1 exc2 ν1 ν2 (!o) n l)
    ∧ (∀ l ∈ t, cReachO exc1 exc2 ν1 ν2 (!o) n l)
    ∧ Z.Nonempty

end Index

/-- The boxed letters. -/
abbrev cLB (N : ℕ) : Type := {l : Option CtrC // l ∈ cLetterBox N}

/-- The debt index: an orientation, a boxed source letter, a boxed
zero-list letter set, and an optional boxed tilt letter. -/
abbrev cIdx (N : ℕ) : Type :=
  Bool × cLB N × Finset (cLB N) × Option (cLB N)

/-- The raw source letter of a coordinate. -/
def cRawS {N : ℕ} (i : cIdx N) : Option CtrC := i.2.1.1

/-- The raw zero-list letter set of a coordinate. -/
def cRawZ {N : ℕ} (i : cIdx N) : Finset (Option CtrC) :=
  i.2.2.1.image Subtype.val

/-- The raw tilt letter of a coordinate. -/
def cRawT {N : ℕ} (i : cIdx N) : Option (Option CtrC) :=
  i.2.2.2.map Subtype.val

section Coord

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)

/-- The coordinate value at a height. -/
noncomputable def cVal (N h : ℕ) (i : cIdx N) : ℝ≥0∞ :=
  cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h i.1 (cRawS i) (cRawZ i) (cRawT i)

/-- The ledger vector: the coordinate value gated by joint reachability
at a common level, mirroring the debts of `Main`. -/
noncomputable def cE (N h : ℕ) (i : cIdx N) : ℝ≥0∞ :=
  ⨆ n : ℕ,
    ⨆ _ : cGateR exc1 exc2 ν1 ν2 i.1 n (cRawS i) (cRawZ i) (cRawT i),
      cVal α Rv μ v0 exc1 exc2 ν1 ν2 N h i

lemma cE_eq_zero_of_not_gate {N h : ℕ} {i : cIdx N}
    (hng : ¬ ∃ n, cGateR exc1 exc2 ν1 ν2 i.1 n (cRawS i) (cRawZ i)
      (cRawT i)) :
    cE α Rv μ v0 exc1 exc2 ν1 ν2 N h i = 0 := by
  refine le_antisymm ?_ zero_le
  exact iSup_le fun n => iSup_le fun hg => absurd ⟨n, hg⟩ hng

end Coord

/-! ### Boxing raw data -/

/-- The boxed lift of a raw letter set. -/
def cLiftB (N : ℕ) (s : Finset (Option CtrC)) : Finset (cLB N) :=
  (cLetterBox N).attach.filter fun x => x.1 ∈ s

lemma mem_cLiftB {N : ℕ} {s : Finset (Option CtrC)} {x : cLB N} :
    x ∈ cLiftB N s ↔ x.1 ∈ s := by
  rw [cLiftB, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_attach _ _, h⟩⟩

lemma cLiftB_image_val {N : ℕ} {s : Finset (Option CtrC)}
    (hs : ∀ l ∈ s, l ∈ cLetterBox N) :
    (cLiftB N s).image Subtype.val = s := by
  ext l
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_cLiftB.mp hx
  · intro hl
    exact ⟨⟨l, hs l hl⟩, mem_cLiftB.mpr hl, rfl⟩

lemma cLiftB_card_le {N : ℕ} (s : Finset (Option CtrC)) :
    (cLiftB N s).card ≤ s.card := by
  refine Finset.card_le_card_of_injOn Subtype.val
    (fun x hx => mem_cLiftB.mp hx) ?_
  exact Subtype.val_injective.injOn

/-- The coordinate of raw data: boxed source, lifted zero list, boxed
tilt. -/
def cMk (N : ℕ) (o : Bool) {s : Option CtrC} (hs : s ∈ cLetterBox N)
    (Z : Finset (Option CtrC)) {t : Option (Option CtrC)}
    (ht : ∀ l ∈ t, l ∈ cLetterBox N) : cIdx N :=
  (o, ⟨s, hs⟩, cLiftB N Z,
    t.pmap (fun l hl => (⟨l, hl⟩ : cLB N)) ht)

@[simp] lemma cMk_fst {N : ℕ} (o : Bool) {s : Option CtrC}
    (hs : s ∈ cLetterBox N) (Z : Finset (Option CtrC))
    {t : Option (Option CtrC)} (ht : ∀ l ∈ t, l ∈ cLetterBox N) :
    (cMk N o hs Z ht).1 = o := rfl

lemma cRawS_cMk {N : ℕ} (o : Bool) {s : Option CtrC}
    (hs : s ∈ cLetterBox N) (Z : Finset (Option CtrC))
    {t : Option (Option CtrC)} (ht : ∀ l ∈ t, l ∈ cLetterBox N) :
    cRawS (cMk N o hs Z ht) = s := rfl

lemma cRawZ_cMk {N : ℕ} (o : Bool) {s : Option CtrC}
    (hs : s ∈ cLetterBox N) {Z : Finset (Option CtrC)}
    {t : Option (Option CtrC)} (ht : ∀ l ∈ t, l ∈ cLetterBox N)
    (hZ : ∀ l ∈ Z, l ∈ cLetterBox N) :
    cRawZ (cMk N o hs Z ht) = Z :=
  cLiftB_image_val hZ

lemma cRawT_cMk {N : ℕ} (o : Bool) {s : Option CtrC}
    (hs : s ∈ cLetterBox N) (Z : Finset (Option CtrC))
    {t : Option (Option CtrC)} (ht : ∀ l ∈ t, l ∈ cLetterBox N) :
    cRawT (cMk N o hs Z ht) = t := by
  rw [cRawT]
  cases t <;> rfl

section GateVal

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)

/-- A gated raw coordinate with boxed data sits below its ledger
entry. -/
lemma cInterp_le_cE (N h : ℕ) (o : Bool) {s : Option CtrC}
    {Z : Finset (Option CtrC)} {t : Option (Option CtrC)}
    (hs : s ∈ cLetterBox N) (hZ : ∀ l ∈ Z, l ∈ cLetterBox N)
    (ht : ∀ l ∈ t, l ∈ cLetterBox N) {n : ℕ}
    (hg : cGateR exc1 exc2 ν1 ν2 o n s Z t) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o s Z t
      ≤ cE α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hs Z ht) := by
  have hval : cVal α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hs Z ht)
      = cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o s Z t := by
    rw [cVal, cRawZ_cMk o hs ht hZ, cRawT_cMk, cRawS_cMk, cMk_fst]
  have hg' : cGateR exc1 exc2 ν1 ν2 (cMk N o hs Z ht).1 n
      (cRawS (cMk N o hs Z ht)) (cRawZ (cMk N o hs Z ht))
      (cRawT (cMk N o hs Z ht)) := by
    rw [cRawZ_cMk o hs ht hZ, cRawT_cMk, cRawS_cMk, cMk_fst]
    exact hg
  rw [cE]
  exact le_trans (le_of_eq hval.symm)
    (le_iSup_of_le n (le_iSup_of_le hg' le_rfl))

/-- A gated raw coordinate with boxed data sits below the ledger
supremum. -/
lemma cInterp_le_iSup_cE (N h : ℕ) (o : Bool) {s : Option CtrC}
    {Z : Finset (Option CtrC)} {t : Option (Option CtrC)}
    (hs : s ∈ cLetterBox N) (hZ : ∀ l ∈ Z, l ∈ cLetterBox N)
    (ht : ∀ l ∈ t, l ∈ cLetterBox N) {n : ℕ}
    (hg : cGateR exc1 exc2 ν1 ν2 o n s Z t) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o s Z t
      ≤ ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j :=
  le_trans (cInterp_le_cE α Rv μ v0 exc1 exc2 ν1 ν2 N h o hs hZ ht hg)
    (le_iSup _ _)

end GateVal

private lemma option_forall_mem_none {A : Type} {P : A → Prop} :
    ∀ l ∈ (none : Option A), P l := by
  simp

private lemma option_forall_mem_some {A : Type} {P : A → Prop} {a : A}
    (ha : P a) : ∀ l ∈ some a, P l := by
  simpa using ha

/-! ### The debt classes embed into the ledger -/

section DebtLe

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (N : ℕ)

/-- Reachable letters of either orientation lie in the box. -/
lemma cReachO_mem_cLetterBox
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hch1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 → exc1 k = none → k ≤ N)
    (hdeclB1 : ∀ k p, exc1 k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (hch2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 → exc2 k = none → k ≤ N)
    (hdeclB2 : ∀ k p, exc2 k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (o : Bool) {n : ℕ} {l : Option CtrC}
    (hl : cReachO exc1 exc2 ν1 ν2 o n l) : l ∈ cLetterBox N := by
  cases o with
  | false =>
      exact cReach_mem_cLetterBox exc1 ν1 N (fun j hj => (hN j hj).1)
        hch1 hdeclB1 hl
  | true =>
      exact cReach_mem_cLetterBox exc2 ν2 N (fun j hj => (hN j hj).2)
        hch2 hdeclB2 hl

/-- The zero-mass debt coordinates are singleton unit coordinates. -/
private lemma zMass_eq_cInterp (h : ℕ) (o : Bool) (l1 l2 : Option CtrC) :
    zMass (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h)
        (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h) (fullSim (cRel Rv) h)
      = cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o l1 {l2} none := by
  rw [zMass_eq_screenE_unit, cInterp]
  refine screenE_congr_mem _ _ (fun ρ => ?_) _
  rw [mem_cZLaws, List.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨l2, Finset.mem_singleton_self _, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    rw [Finset.mem_singleton.mp hl]

/-- The one-member screen debt coordinates are singleton tilted
coordinates. -/
private lemma scrOne_eq_cInterp (h : ℕ) (o : Bool)
    (l1 l2 l3 : Option CtrC) :
    screenE (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h) (fullSim (cRel Rv) h)
        [cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h]
        (WresD α (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l3 h)
          (fullSim (cRel Rv) h))
      = cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o l1 {l2} (some l3) := by
  rw [cInterp]
  refine screenE_congr_mem _ _ (fun ρ => ?_) _
  rw [mem_cZLaws, List.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨l2, Finset.mem_singleton_self _, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    rw [Finset.mem_singleton.mp hl]

/-- The two-member screen debt coordinates are pair tilted
coordinates. -/
private lemma scrTwo_eq_cInterp (h : ℕ) (o : Bool)
    (l1 l2 l2' l3 : Option CtrC) :
    screenE (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h) (fullSim (cRel Rv) h)
        [cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h,
          cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2' h]
        (WresD α (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l3 h)
          (fullSim (cRel Rv) h))
      = cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o l1 {l2, l2'} (some l3) := by
  rw [cInterp]
  refine screenE_congr_mem _ _ (fun ρ => ?_) _
  rw [mem_cZLaws, List.mem_cons, List.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨l2, Finset.mem_insert_self _ _, rfl⟩
    · exact ⟨l2', Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
        rfl⟩
  · rintro ⟨l, hl, rfl⟩
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact Or.inl rfl
    · rw [Finset.mem_singleton.mp hl]
      exact Or.inr rfl

/-- **The debt embeds into the ledger** (`debt_le` of
`ScreenLedgerInput`): the three debt classes of `Main` are gated
coordinates of the index. -/
theorem cDebt_le_iSup_cE
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hch1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 → exc1 k = none → k ≤ N)
    (hdeclB1 : ∀ k p, exc1 k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (hch2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 → exc2 k = none → k ≤ N)
    (hdeclB2 : ∀ k p, exc2 k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (h : ℕ) :
    cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h
      ≤ ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j := by
  have hbox : ∀ (o : Bool) {n : ℕ} {l : Option CtrC},
      cReachO exc1 exc2 ν1 ν2 o n l → l ∈ cLetterBox N := by
    intro o n l hl
    exact cReachO_mem_cLetterBox exc1 exc2 ν1 ν2 N hN hch1 hdeclB1
      hch2 hdeclB2 o hl
  rw [cDebt]
  refine sup_le ?_ (sup_le ?_ ?_)
  · rw [cZeroDebt]
    refine iSup_le fun o => iSup_le fun n => iSup_le fun l1 =>
      iSup_le fun l2 => iSup_le fun r1 => iSup_le fun r2 => ?_
    rw [zMass_eq_cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o l1 l2]
    refine cInterp_le_iSup_cE α Rv μ v0 exc1 exc2 ν1 ν2 N h o
      (hbox o r1)
      (fun l hl => by rw [Finset.mem_singleton.mp hl]; exact hbox (!o) r2)
      option_forall_mem_none
      (n := n) ⟨r1, ?_, option_forall_mem_none, Finset.singleton_nonempty _⟩
    intro l hl
    rw [Finset.mem_singleton.mp hl]
    exact r2
  · rw [cScrOneDebt]
    refine iSup_le fun o => iSup_le fun n => iSup_le fun l1 =>
      iSup_le fun l2 => iSup_le fun l3 => iSup_le fun r1 =>
        iSup_le fun r2 => iSup_le fun r3 => ?_
    rw [scrOne_eq_cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o l1 l2 l3]
    refine cInterp_le_iSup_cE α Rv μ v0 exc1 exc2 ν1 ν2 N h o
      (hbox o r1)
      (fun l hl => by rw [Finset.mem_singleton.mp hl]; exact hbox (!o) r2)
      (option_forall_mem_some (hbox (!o) r3))
      (n := n) ⟨r1, ?_, option_forall_mem_some r3,
        Finset.singleton_nonempty _⟩
    intro l hl
    rw [Finset.mem_singleton.mp hl]
    exact r2
  · rw [cScrTwoDebt]
    refine iSup_le fun o => iSup_le fun n => iSup_le fun l1 =>
      iSup_le fun l2 => iSup_le fun l2' => iSup_le fun l3 =>
        iSup_le fun r1 => iSup_le fun r2 => iSup_le fun r2' =>
          iSup_le fun r3 => ?_
    rw [scrTwo_eq_cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o l1 l2 l2' l3]
    have hZ : ∀ l ∈ ({l2, l2'} : Finset (Option CtrC)),
        cReachO exc1 exc2 ν1 ν2 (!o) n l := by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact r2
      · rw [Finset.mem_singleton.mp hl]
        exact r2'
    refine cInterp_le_iSup_cE α Rv μ v0 exc1 exc2 ν1 ν2 N h o
      (hbox o r1) (fun l hl => hbox (!o) (hZ l hl))
      (option_forall_mem_some (hbox (!o) r3))
      (n := n) ⟨r1, hZ, option_forall_mem_some r3,
        Finset.insert_nonempty _ _⟩

end DebtLe

/-! ### Orientation pruning and the height-0 rows -/

section Base

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (N : ℕ)

/-- The fresh-diagonal pruning in either orientation
(`thm:exact-pruning`): the fresh source of a side against a zero list
containing the opposite fresh law vanishes, for any normalization. -/
lemma cPruneO (o : Bool)
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (h : ℕ) (zs : List (PMF (FullLab (CState V) h)))
    (hmem : cT (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0 h ∈ zs)
    (W : FullLab (CState V) h → ℝ≥0∞) :
    screenE (cT (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 h)
      (fullSim (cRel Rv) h) zs W = 0 := by
  cases o with
  | false =>
      exact screenE_cT_opposite_eq_zero Rv μ v0 exc1 exc2 ν1 ν2 N hRv hμ0
        hN hdeclN1 hcharged1 h zs hmem W
  | true =>
      exact screenE_cT_opposite_eq_zero Rv μ v0 exc2 exc1 ν2 ν1 N hRv hμ0
        (fun j hj => ⟨(hN j hj).2, (hN j hj).1⟩) hdeclN2 hcharged2
        h zs hmem W

/-- A fresh-diagonal raw coordinate vanishes at every height. -/
lemma cInterp_fdiag_eq_zero (o : Bool)
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (h : ℕ) {Z : Finset (Option CtrC)} (hfz : none ∈ Z)
    (t : Option (Option CtrC)) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o none Z t = 0 := by
  rw [cInterp, cLetO_eq, cLet_none]
  refine cPruneO Rv μ v0 exc1 exc2 ν1 ν2 N o hRv hμ0 hN hdeclN1
    hcharged1 hdeclN2 hcharged2 h _ ?_ _
  exact (mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mpr
    ⟨none, hfz, by rw [cLetO_eq, cLet_none]⟩

/-- The good degree of a point law is the relation indicator. -/
private lemma rE_pure_ite {X : Type} (a : X) (R : X → X → Prop) (x : X) :
    rE (PMF.pure a) R x = if R x a then 1 else 0 := by
  rw [rE, tsum_congr fun y => show (if R x y then (PMF.pure a) y else 0)
      = (PMF.pure a) y * (if R x y then 1 else 0) from by
    by_cases hy : R x y
    · rw [if_pos hy, if_pos hy, mul_one]
    · rw [if_neg hy, if_neg hy, mul_zero], tsum_pure_mul]

/-- At height 0 a frozen tilt is at most one. -/
private lemma WresD_cZ_zero_le_one (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ)
    (c3 : CtrC) (x : FullLab (CState V) 0) :
    WresD α (cZ exc μ ν v0 c3 0) (fullSim (cRel Rv) 0) x ≤ 1 := by
  by_cases h0 : rE (cZ exc μ ν v0 c3 0) (fullSim (cRel Rv) 0) x = 0
  · rw [WresD, if_pos h0]
    exact zero_le
  · rw [← rE_rpow_neg_eq_WresD _ _ _ h0]
    have h1 : rE (cZ exc μ ν v0 c3 0) (fullSim (cRel Rv) 0) x = 1 := by
      rw [show cZ exc μ ν v0 c3 0 = PMF.pure (leaf (v0, c3)) from rfl,
        rE_pure_ite] at h0 ⊢
      by_cases hx : fullSim (cRel Rv) 0 x (leaf (v0, c3))
      · rw [if_pos hx]
      · rw [if_neg hx] at h0
        exact absurd rfl h0
    rw [h1, ENNReal.one_rpow]

/-- **The height-0 rows** (`base` of `ScreenLedgerInput`,
`thm:zero-interface`): every ledger coordinate starts below
`2 * etaG` under `μ(v0) ≥ 1/2`. -/
theorem cE_base_le (hα : 1 ≤ α)
    (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0) (hhalf : 2⁻¹ ≤ μ v0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN1 : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged1 : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (hdeclN2 : ∀ k p, exc2 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hcharged2 : ∀ k, ν2 k ≠ 0 → exc2 k = none → k ≤ N ∧ ν1 k ≠ 0)
    (i : cIdx N) :
    cE α Rv μ v0 exc1 exc2 ν1 ν2 N 0 i ≤ 2 * etaG α Rv μ := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hαpos : (0 : ℝ) < α := lt_of_lt_of_le one_pos hα
  refine iSup_le fun n => iSup_le fun hg => ?_
  obtain ⟨hr1, hrZ, hrT, hZne⟩ := hg
  rw [cVal]
  rcases hsrc : cRawS i with _ | c1
  · -- fresh source
    by_cases hfz : none ∈ cRawZ i
    · rw [cInterp_fdiag_eq_zero α Rv μ v0 exc1 exc2 ν1 ν2 N i.1 hRv hμ0
        hN hdeclN1 hcharged1 hdeclN2 hcharged2 0 hfz]
      exact zero_le
    · obtain ⟨l0, hl0⟩ := hZne
      rcases hl0eq : l0 with _ | c2
      · exact absurd (hl0eq ▸ hl0) hfz
      · subst hl0eq
        have hmem : cZ (cExcO exc1 exc2 (!i.1)) μ (cNuO ν1 ν2 (!i.1)) v0
            c2 0 ∈ cZLaws μ v0 exc1 exc2 ν1 ν2 (!i.1) (cRawZ i) 0 :=
          (mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mpr
            ⟨some c2, hl0, by rw [cLetO_eq, cLet_some]⟩
        rw [cInterp, cLetO_eq, cLet_none]
        rcases htl : cRawT i with _ | l3
        · rw [cTiltW_none]
          exact cScr_base_cT_source_le Rv μ v0
            (cExcO exc1 exc2 i.1) (cExcO exc1 exc2 (!i.1))
            (cNuO ν1 ν2 i.1) (cNuO ν1 ν2 (!i.1)) c2 hmem
            (fun x => le_refl 1) (2 * etaG α Rv μ)
            (cFarMass_le_two_etaG α Rv μ v0 hα0 hsymm hhalf)
        · rcases l3 with _ | c3
          · rw [cTiltW_some, cLetO_eq, cLet_none]
            exact cScr_base_cT_source_tiltT_le α Rv μ v0
              (cExcO exc1 exc2 i.1) (cExcO exc1 exc2 (!i.1))
              (cNuO ν1 ν2 i.1) (cNuO ν1 ν2 (!i.1)) hαpos hsymm hhalf
              c2 hmem
          · rw [cTiltW_some, cLetO_eq, cLet_some]
            exact cScr_base_cT_source_le Rv μ v0
              (cExcO exc1 exc2 i.1) (cExcO exc1 exc2 (!i.1))
              (cNuO ν1 ν2 i.1) (cNuO ν1 ν2 (!i.1)) c2 hmem
              (WresD_cZ_zero_le_one α Rv μ v0
                (cExcO exc1 exc2 (!i.1)) (cNuO ν1 ν2 (!i.1)) c3)
              (2 * etaG α Rv μ)
              (cFarMass_le_two_etaG α Rv μ v0 hα0 hsymm hhalf)
  · -- frozen source: dead by reflexivity at the root
    obtain ⟨l0, hl0⟩ := hZne
    have hmem : (∃ c₂, cZ (cExcO exc1 exc2 (!i.1)) μ (cNuO ν1 ν2 (!i.1))
          v0 c₂ 0 ∈ cZLaws μ v0 exc1 exc2 ν1 ν2 (!i.1) (cRawZ i) 0)
        ∨ cT (cExcO exc1 exc2 (!i.1)) μ (cNuO ν1 ν2 (!i.1)) v0 0
          ∈ cZLaws μ v0 exc1 exc2 ν1 ν2 (!i.1) (cRawZ i) 0 := by
      rcases hl0eq : l0 with _ | c2
      · subst hl0eq
        exact Or.inr ((mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mpr
          ⟨none, hl0, by rw [cLetO_eq, cLet_none]⟩)
      · subst hl0eq
        exact Or.inl ⟨c2, (mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mpr
          ⟨some c2, hl0, by rw [cLetO_eq, cLet_some]⟩⟩
    rw [cInterp, cLetO_eq, cLet_some,
      cScr_base_cZ_source_eq_zero Rv μ v0
        (cExcO exc1 exc2 i.1) (cExcO exc1 exc2 (!i.1))
        (cNuO ν1 ν2 i.1) (cNuO ν1 ν2 (!i.1)) (hRv v0) hμ0 c1 hmem]
    exact zero_le

end Base

/-! ### Successor letters, member counters, and target sets -/

/-- The raw successor letters of a zero-list member on a target side:
the components of its cell, the fresh letter expanding to the
components of every charged cell. -/
def cSuccRaw (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ) :
    Option CtrC → Finset (Option CtrC)
  | some c => {cComp0 exc c, cComp1 exc c}
  | none => Kf.biUnion fun k =>
      {cComp0 exc (CtrC.ord k), cComp1 exc (CtrC.ord k)}

/-- The member counters of a zero-list letter set: frozen letters
contribute their counters, the fresh letter the whole support. -/
noncomputable def cMsL (Kf : Finset ℕ) (Z : Finset (Option CtrC)) :
    List CtrC :=
  Z.toList.flatMap fun l =>
    match l with
    | some c => [c]
    | none => Kf.toList.map CtrC.ord

lemma mem_cMsL {Kf : Finset ℕ} {Z : Finset (Option CtrC)} {c : CtrC} :
    c ∈ cMsL Kf Z
      ↔ some c ∈ Z ∨ (none ∈ Z ∧ ∃ k ∈ Kf, c = CtrC.ord k) := by
  rw [cMsL, List.mem_flatMap]
  constructor
  · rintro ⟨l, hl, hc⟩
    rcases l with _ | c'
    · refine Or.inr ⟨Finset.mem_toList.mp hl, ?_⟩
      obtain ⟨k, hk, hkc⟩ := List.mem_map.mp hc
      exact ⟨k, Finset.mem_toList.mp hk, hkc.symm⟩
    · rcases List.mem_singleton.mp hc with rfl
      exact Or.inl (Finset.mem_toList.mp hl)
  · rintro (hc | ⟨hz, k, hk, rfl⟩)
    · exact ⟨some c, Finset.mem_toList.mpr hc, List.mem_singleton_self _⟩
    · exact ⟨none, Finset.mem_toList.mpr hz,
        List.mem_map.mpr ⟨k, Finset.mem_toList.mpr hk, rfl⟩⟩

/-- The component letter list of the member counters. -/
noncomputable def cCompL (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ)
    (Z : Finset (Option CtrC)) : List (Option CtrC) :=
  (cMsL Kf Z).flatMap fun c => [cComp0 exc c, cComp1 exc c]

lemma mem_cCompL {exc : ℕ → Option (ℕ × ℕ)} {Kf : Finset ℕ}
    {Z : Finset (Option CtrC)} {l : Option CtrC} :
    l ∈ cCompL exc Kf Z
      ↔ ∃ c ∈ cMsL Kf Z, l = cComp0 exc c ∨ l = cComp1 exc c := by
  rw [cCompL, List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, hl⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨c, hc, Or.inl rfl⟩
    · rcases List.mem_singleton.mp hl with rfl
      exact ⟨c, hc, Or.inr rfl⟩
  · rintro ⟨c, hc, rfl | rfl⟩
    · exact ⟨c, hc, List.mem_cons_self ..⟩
    · exact ⟨c, hc, List.mem_cons.mpr
        (Or.inr (List.mem_singleton_self _))⟩

/-- The raw zero-list successor set. -/
def cZSuccR (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ)
    (Z : Finset (Option CtrC)) : Finset (Option CtrC) :=
  Z.biUnion (cSuccRaw exc Kf)

/-- The raw successor set collects exactly the components of the member
counters. -/
lemma mem_cZSuccR {exc : ℕ → Option (ℕ × ℕ)} {Kf : Finset ℕ}
    {Z : Finset (Option CtrC)} {l : Option CtrC} :
    l ∈ cZSuccR exc Kf Z
      ↔ ∃ c ∈ cMsL Kf Z, l = cComp0 exc c ∨ l = cComp1 exc c := by
  rw [cZSuccR, Finset.mem_biUnion]
  constructor
  · rintro ⟨lz, hlz, hl⟩
    rcases lz with _ | c'
    · rw [cSuccRaw, Finset.mem_biUnion] at hl
      obtain ⟨k, hk, hl⟩ := hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact ⟨CtrC.ord k, mem_cMsL.mpr (Or.inr ⟨hlz, k, hk, rfl⟩),
          Or.inl rfl⟩
      · rcases Finset.mem_singleton.mp hl with rfl
        exact ⟨CtrC.ord k, mem_cMsL.mpr (Or.inr ⟨hlz, k, hk, rfl⟩),
          Or.inr rfl⟩
    · rcases Finset.mem_insert.mp hl with rfl | hl
      · exact ⟨c', mem_cMsL.mpr (Or.inl hlz), Or.inl rfl⟩
      · rcases Finset.mem_singleton.mp hl with rfl
        exact ⟨c', mem_cMsL.mpr (Or.inl hlz), Or.inr rfl⟩
  · rintro ⟨c, hc, hor⟩
    rcases mem_cMsL.mp hc with hz | ⟨hz, k, hk, rfl⟩
    · refine ⟨some c, hz, ?_⟩
      rw [cSuccRaw]
      rcases hor with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · refine ⟨none, hz, ?_⟩
      rw [cSuccRaw, Finset.mem_biUnion]
      refine ⟨k, hk, ?_⟩
      rcases hor with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The length budget of a constant-length flat map. -/
private lemma length_flatMap_pair {A B : Type} (l : List A)
    (f g : A → B) :
    (l.flatMap fun a => [f a, g a]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.flatMap_cons, List.length_append, ih]
      simp only [List.length_cons, List.length_nil]
      omega

lemma cMsL_length_le (Kf : Finset ℕ) (Z : Finset (Option CtrC)) :
    (cMsL Kf Z).length ≤ Z.card * max Kf.card 1 := by
  rw [cMsL, List.length_flatMap]
  calc (Z.toList.map fun l =>
        (match l with
          | some c => [c]
          | none => Kf.toList.map CtrC.ord).length).sum
      ≤ (Z.toList.map fun l =>
          (match l with
            | some c => [c]
            | none => Kf.toList.map CtrC.ord).length).length
          • max Kf.card 1 := by
        refine List.sum_le_card_nsmul _ _ fun x hx => ?_
        obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
        rcases l with _ | c
        · rw [List.length_map, Finset.length_toList]
          exact le_max_left _ _
        · exact le_max_right _ _
    _ = Z.card * max Kf.card 1 := by
        rw [List.length_map, Finset.length_toList, smul_eq_mul]

lemma cCompL_length_le (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ)
    (Z : Finset (Option CtrC)) :
    (cCompL exc Kf Z).length ≤ 2 * (Z.card * max Kf.card 1) := by
  rw [cCompL, length_flatMap_pair]
  exact Nat.mul_le_mul_left 2 (cMsL_length_le Kf Z)

/-! ### The common and priced target sets -/

/-- The common source moves: components of a frozen counter, components
of the charged common cells below the fresh letter. -/
def cSrcC (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ) :
    Option CtrC → Finset (Option CtrC)
  | some c => {cComp0 exc c, cComp1 exc c}
  | none => (Kf.filter fun k => exc k = none).biUnion fun k =>
      {cComp0 exc (CtrC.ord k), cComp1 exc (CtrC.ord k)}

/-- The exceptional-entrance source moves below the fresh letter. -/
def cSrcE (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ) :
    Option CtrC → Finset (Option CtrC)
  | some _ => ∅
  | none => (Kf.filter fun k => exc k ≠ none).biUnion fun k =>
      {cComp0 exc (CtrC.ord k), cComp1 exc (CtrC.ord k)}

/-- The common tilt moves: the unit stays, a frozen tilt descends to a
component; the fresh tilt has no common move. -/
def cTiltC (exc : ℕ → Option (ℕ × ℕ)) :
    Option (Option CtrC) → Finset (Option (Option CtrC))
  | none => {none}
  | some (some c3) => {some (cComp0 exc c3), some (cComp1 exc c3)}
  | some none => ∅

/-- The priced tilt moves: the fresh tilt renews to a component of a
charged cell. -/
def cTiltP (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ) :
    Option (Option CtrC) → Finset (Option (Option CtrC))
  | some none => Kf.biUnion fun k =>
      {some (cComp0 exc (CtrC.ord k)), some (cComp1 exc (CtrC.ord k))}
  | none => ∅
  | some (some _) => ∅

/-- The boxed lift of a set of optional tilt letters. -/
def cLiftO (N : ℕ) (s : Finset (Option (Option CtrC))) :
    Finset (Option (cLB N)) :=
  s.biUnion fun t =>
    match t with
    | none => {none}
    | some l => (cLiftB N {l}).image some

lemma pmap_mem_cLiftO {N : ℕ} {s : Finset (Option (Option CtrC))}
    {t : Option (Option CtrC)} (ht : ∀ l ∈ t, l ∈ cLetterBox N)
    (hts : t ∈ s) :
    t.pmap (fun l hl => (⟨l, hl⟩ : cLB N)) ht ∈ cLiftO N s := by
  rw [cLiftO, Finset.mem_biUnion]
  refine ⟨t, hts, ?_⟩
  cases t with
  | none => exact Finset.mem_singleton_self _
  | some l =>
      refine Finset.mem_image.mpr ⟨⟨l, ht l rfl⟩, ?_, rfl⟩
      exact mem_cLiftB.mpr (Finset.mem_singleton_self _)

lemma cLiftO_card_le (N : ℕ) (s : Finset (Option (Option CtrC))) :
    (cLiftO N s).card ≤ s.card := by
  refine le_trans (Finset.card_biUnion_le) ?_
  calc ∑ t ∈ s, (match t with
        | none => ({none} : Finset (Option (cLB N)))
        | some l => (cLiftB N {l}).image some).card
      ≤ ∑ _t ∈ s, 1 := by
        refine Finset.sum_le_sum fun t _ => ?_
        rcases t with _ | l
        · exact le_of_eq (Finset.card_singleton _)
        · exact le_trans Finset.card_image_le
            (le_trans (cLiftB_card_le _) (le_of_eq (Finset.card_singleton _)))
    _ = s.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- The support budget. -/
def cMx (K1 K2 : Finset ℕ) : ℕ := max (max K1.card K2.card) 1

lemma one_le_cMx (K1 K2 : Finset ℕ) : 1 ≤ cMx K1 K2 :=
  le_max_right _ _

lemma cKO_card_le_cMx (K1 K2 : Finset ℕ) (o : Bool) :
    (cKO K1 K2 o).card ≤ cMx K1 K2 := by
  cases o with
  | false => exact le_trans (le_max_left _ _) (le_max_left _ _)
  | true => exact le_trans (le_max_right _ _) (le_max_left _ _)

/-- The singleton-screen length budget. -/
def cLz (N : ℕ) (K1 K2 : Finset ℕ) : ℕ :=
  2 * ((cLetterBox N).card * cMx K1 K2)

private lemma card_pair_le {A : Type} [DecidableEq A] (a b : A) :
    ({a, b} : Finset A).card ≤ 2 :=
  le_trans (Finset.card_insert_le _ _)
    (by rw [Finset.card_singleton])

private lemma biUnion_pair_card_le {A B : Type} [DecidableEq B]
    (s : Finset A) (f g : A → B) :
    (s.biUnion fun a => ({f a, g a} : Finset B)).card ≤ 2 * s.card := by
  refine le_trans (Finset.card_biUnion_le) ?_
  calc ∑ a ∈ s, ({f a, g a} : Finset B).card
      ≤ ∑ _a ∈ s, 2 := Finset.sum_le_sum fun a _ => card_pair_le _ _
    _ = 2 * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

lemma cSrcC_card_le (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ)
    (s : Option CtrC) : (cSrcC exc Kf s).card ≤ 2 * max Kf.card 1 := by
  rcases s with _ | c
  · rw [cSrcC]
    refine le_trans (biUnion_pair_card_le _ _ _) ?_
    have := Finset.card_filter_le Kf fun k => exc k = none
    have hK : Kf.card ≤ max Kf.card 1 := le_max_left _ _
    omega
  · rw [cSrcC]
    have h2 : (2 : ℕ) ≤ 2 * max Kf.card 1 := by
      have : 1 ≤ max Kf.card 1 := le_max_right _ _
      omega
    exact le_trans (card_pair_le _ _) h2

lemma cSrcE_card_le (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ)
    (s : Option CtrC) : (cSrcE exc Kf s).card ≤ 2 * max Kf.card 1 := by
  rcases s with _ | c
  · rw [cSrcE]
    refine le_trans (biUnion_pair_card_le _ _ _) ?_
    have := Finset.card_filter_le Kf fun k => exc k ≠ none
    have hK : Kf.card ≤ max Kf.card 1 := le_max_left _ _
    omega
  · rw [cSrcE]
    simp

lemma cTiltC_card_le (exc : ℕ → Option (ℕ × ℕ))
    (t : Option (Option CtrC)) : (cTiltC exc t).card ≤ 2 := by
  rcases t with _ | (_ | c3)
  · rw [cTiltC]
    simp
  · rw [cTiltC]
    simp
  · rw [cTiltC]
    exact card_pair_le _ _

lemma cTiltP_card_le (exc : ℕ → Option (ℕ × ℕ)) (Kf : Finset ℕ)
    (t : Option (Option CtrC)) :
    (cTiltP exc Kf t).card ≤ 2 * max Kf.card 1 := by
  rcases t with _ | (_ | c3)
  · rw [cTiltP]
    simp
  · rw [cTiltP]
    refine le_trans (biUnion_pair_card_le _ _ _) ?_
    have hK : Kf.card ≤ max Kf.card 1 := le_max_left _ _
    omega
  · rw [cTiltP]
    simp

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

/-- Common source moves stay reachable. -/
lemma cSrcC_reach {o : Bool} {n : ℕ} {s : Option CtrC}
    (hs : cReachO exc1 exc2 ν1 ν2 o n s)
    (hsup : ∀ k, (cNuO ν1 ν2 o k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 o) :
    ∀ s' ∈ cSrcC (cExcO exc1 exc2 o) (cKO K1 K2 o) s,
      cReachO exc1 exc2 ν1 ν2 o (n + 1) s' := by
  intro s' hs'
  rcases s with _ | c
  · rw [cSrcC, Finset.mem_biUnion] at hs'
    obtain ⟨k, hk, hs'⟩ := hs'
    have hν : (cNuO ν1 ν2 o k : ℝ≥0∞) ≠ 0 :=
      (hsup k).mpr (Finset.mem_filter.mp hk).1
    refine cReachO_spawn exc1 exc2 ν1 ν2 hs ⟨k, hν, ?_⟩
    rcases Finset.mem_insert.mp hs' with rfl | hs'
    · exact Or.inl rfl
    · exact Or.inr (Finset.mem_singleton.mp hs')
  · rw [cSrcC] at hs'
    refine cReachO_spawn exc1 exc2 ν1 ν2 hs ?_
    rcases Finset.mem_insert.mp hs' with rfl | hs'
    · exact Or.inl rfl
    · exact Or.inr (Finset.mem_singleton.mp hs')

/-- Exceptional-entrance source moves stay reachable. -/
lemma cSrcE_reach {o : Bool} {n : ℕ} {s : Option CtrC}
    (hs : cReachO exc1 exc2 ν1 ν2 o n s)
    (hsup : ∀ k, (cNuO ν1 ν2 o k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 o) :
    ∀ s' ∈ cSrcE (cExcO exc1 exc2 o) (cKO K1 K2 o) s,
      cReachO exc1 exc2 ν1 ν2 o (n + 1) s' := by
  intro s' hs'
  rcases s with _ | c
  · rw [cSrcE, Finset.mem_biUnion] at hs'
    obtain ⟨k, hk, hs'⟩ := hs'
    have hν : (cNuO ν1 ν2 o k : ℝ≥0∞) ≠ 0 :=
      (hsup k).mpr (Finset.mem_filter.mp hk).1
    refine cReachO_spawn exc1 exc2 ν1 ν2 hs ⟨k, hν, ?_⟩
    rcases Finset.mem_insert.mp hs' with rfl | hs'
    · exact Or.inl rfl
    · exact Or.inr (Finset.mem_singleton.mp hs')
  · rw [cSrcE] at hs'
    exact absurd hs' (Finset.notMem_empty _)

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

/-- Common tilt moves stay reachable. -/
lemma cTiltC_reach {o : Bool} {n : ℕ} {t : Option (Option CtrC)}
    (ht : ∀ l ∈ t, cReachO exc1 exc2 ν1 ν2 (!o) n l) :
    ∀ t' ∈ cTiltC (cExcO exc1 exc2 (!o)) t,
      ∀ l ∈ t', cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l := by
  intro t' ht' l hl
  rcases t with _ | (_ | c3)
  · rw [cTiltC, Finset.mem_singleton] at ht'
    subst ht'
    exact absurd hl (Option.not_mem_none l)
  · rw [cTiltC] at ht'
    exact absurd ht' (Finset.notMem_empty _)
  · rw [cTiltC] at ht'
    have hc3 : cReachO exc1 exc2 ν1 ν2 (!o) n (some c3) := ht _ rfl
    rcases Finset.mem_insert.mp ht' with rfl | ht'
    · rcases Option.mem_some_iff.mp hl with rfl
      exact cReachO_spawn exc1 exc2 ν1 ν2 hc3 (Or.inl rfl)
    · rcases Finset.mem_singleton.mp ht' with rfl
      rcases Option.mem_some_iff.mp hl with rfl
      exact cReachO_spawn exc1 exc2 ν1 ν2 hc3 (Or.inr rfl)

/-- Priced tilt moves stay reachable. -/
lemma cTiltP_reach {o : Bool} {n : ℕ} {t : Option (Option CtrC)}
    (ht : ∀ l ∈ t, cReachO exc1 exc2 ν1 ν2 (!o) n l)
    (hsup : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o)) :
    ∀ t' ∈ cTiltP (cExcO exc1 exc2 (!o)) (cKO K1 K2 (!o)) t,
      ∀ l ∈ t', cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l := by
  intro t' ht' l hl
  rcases t with _ | (_ | c3)
  · rw [cTiltP] at ht'
    exact absurd ht' (Finset.notMem_empty _)
  · rw [cTiltP, Finset.mem_biUnion] at ht'
    obtain ⟨k, hk, ht'⟩ := ht'
    have hfr : cReachO exc1 exc2 ν1 ν2 (!o) n none := ht _ rfl
    rcases Finset.mem_insert.mp ht' with rfl | ht'
    · rcases Option.mem_some_iff.mp hl with rfl
      exact cReachO_spawn exc1 exc2 ν1 ν2 hfr
        ⟨k, (hsup k).mpr hk, Or.inl rfl⟩
    · rcases Finset.mem_singleton.mp ht' with rfl
      rcases Option.mem_some_iff.mp hl with rfl
      exact cReachO_spawn exc1 exc2 ν1 ν2 hfr
        ⟨k, (hsup k).mpr hk, Or.inr rfl⟩
  · rw [cTiltP] at ht'
    exact absurd ht' (Finset.notMem_empty _)

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

include hcharged1 hcharged2 in
lemma cHChO (o : Bool) : ∀ k, (cNuO ν1 ν2 o k : ℝ≥0∞) ≠ 0 →
    cExcO exc1 exc2 o k = none → k ≤ N := by
  cases o with
  | false => exact fun k hk he => (hcharged1 k hk he).1
  | true => exact fun k hk he => (hcharged2 k hk he).1

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

private lemma mulVec_iterate_block {P : Type} [Fintype P]
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

/-! ### The descended pair screens -/

private lemma pmf_exists_ne_zero (ν : PMF ℕ) : ∃ k, (ν k : ℝ≥0∞) ≠ 0 := by
  by_contra hall
  push Not at hall
  have h1 := ν.tsum_coe
  rw [tsum_congr fun k => hall k, tsum_zero] at h1
  exact one_ne_zero h1.symm

section StepRows

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ) (N : ℕ)

/-- The descended member cells of a zero-list letter set. -/
noncomputable def cPairLaws (o : Bool) (Z : Finset (Option CtrC))
    (h : ℕ) :
    List (PMF (FullLab (CState V) h × FullLab (CState V) h)) :=
  (cMsL (cKO K1 K2 o) Z).map fun c =>
    cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 c h

/-- The descended pair tilt of an optional tilt letter. -/
noncomputable def cPairW (o : Bool) (t : Option (Option CtrC)) (h : ℕ) :
    FullLab (CState V) h × FullLab (CState V) h → ℝ≥0∞ :=
  match t with
  | none => fun _ => 1
  | some (some c3) => WresD α
      (cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 c3 h)
      (SquareRel (fullSim (cRel Rv) h))
  | some none => WresD α
      (cXiBar (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 h)
      (SquareRel (fullSim (cRel Rv) h))

/-- The descended pair screen of a source cell. -/
noncomputable def cPairScr (o : Bool) (cs : CtrC)
    (Z : Finset (Option CtrC)) (t : Option (Option CtrC)) (h : ℕ) :
    ℝ≥0∞ :=
  screenE (cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 cs h)
    (SquareRel (fullSim (cRel Rv) h))
    (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h)
    (cPairW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t h)

/-- **The dead-event descent at a compatible charged root**: the joint
height-`(h+1)` dead event of a zero-list letter set descends to the
joint dead event of the member cells. -/
private lemma cDead_descend (o : Bool) {u : V} (hu : Rv u v0)
    (hvpos : rE μ Rv u ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (Z : Finset (Option CtrC)) (h : ℕ) (cs : CtrC)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    (∀ ρ ∈ cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1),
        rE ρ (fullSim (cRel Rv) (h + 1)) (branch (u, cs) xp) = 0)
      ↔ ∀ ρ' ∈ cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h,
          rE ρ' (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
  constructor
  · intro hall ρ' hρ'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hρ'
    rcases mem_cMsL.mp hc with hz | ⟨hz, k, hk, rfl⟩
    · have h0 := hall _ ((mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mpr
        ⟨some c, hz, rfl⟩)
      rw [cLetO_eq, cLet_some] at h0
      exact (rE_cZ_succ_eq_zero_iff (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 Rv hu cs c h xp).mp h0
    · have h0 := hall _ ((mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mpr
        ⟨none, hz, rfl⟩)
      rw [cLetO_eq, cLet_none] at h0
      have hbar := (rE_cT_succ_eq_zero_iff (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 Rv hvpos cs h xp).mp h0
      exact ((rE_cXiBar_eq_zero_iff_charged (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 h _ xp).mp hbar) k ((hsupB k).mpr hk)
  · intro hcell ρ hρ
    obtain ⟨l, hl, rfl⟩ := (mem_cZLaws μ v0 exc1 exc2 ν1 ν2).mp hρ
    rcases l with _ | c
    · rw [cLetO_eq, cLet_none]
      refine (rE_cT_succ_eq_zero_iff (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 Rv hvpos cs h xp).mpr ?_
      refine (rE_cXiBar_eq_zero_iff_charged (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 h _ xp).mpr fun k hk => ?_
      refine hcell _ (List.mem_map.mpr ⟨CtrC.ord k, ?_, rfl⟩)
      exact mem_cMsL.mpr (Or.inr ⟨hl, k, (hsupB k).mp hk, rfl⟩)
    · rw [cLetO_eq, cLet_some]
      refine (rE_cZ_succ_eq_zero_iff (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 Rv hu cs c h xp).mpr ?_
      exact hcell _ (List.mem_map.mpr
        ⟨c, mem_cMsL.mpr (Or.inl hl), rfl⟩)

/-- **The screen descent below a compatible charged root**, generic
tilt. -/
private lemma cScreen_muM_descend (o : Bool) {u : V} (hu : Rv u v0)
    (hvpos : rE μ Rv u ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (Z : Finset (Option CtrC)) (h : ℕ) (cs : CtrC)
    (G : FullLab (CState V) (h + 1) → ℝ≥0∞) :
    screenE (muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0)
        (u, cs) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1)) G
      = ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 cs h xp
          * (screenInd (SquareRel (fullSim (cRel Rv) h))
              (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
            * G (branch (u, cs) xp)) := by
  rw [screenE, muM_compK_succ (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
    u cs h,
    tsum_congr fun x => mul_assoc _ _ (G x), tsum_map_mul]
  refine tsum_congr fun xp => ?_
  rw [screenInd, screenInd,
    if_congr (cDead_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hu hvpos
      hsupB Z h cs xp) rfl rfl]

/-- **Frozen-source descent, unit tilt.** -/
lemma cInterp_cZ_succ_unit (o : Bool) (hrefl0 : Rv v0 v0)
    (hμ0 : μ v0 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (c1 : CtrC) (Z : Finset (Option CtrC)) (h : ℕ) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1) o (some c1) Z none
      = cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o c1 Z none h := by
  have hvpos : rE μ Rv v0 ≠ 0 := rE_root_ne_zero Rv μ v0 hrefl0 hμ0
  rw [cInterp, cTiltW_none, cLetO_eq, cLet_some,
    show cZ (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 c1 (h + 1)
      = muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0) (v0, c1)
        (h + 1) from rfl,
    cScreen_muM_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hrefl0 hvpos
      hsupB Z h c1 (fun _ => 1),
    cPairScr, screenE]
  exact tsum_congr fun xp => by
    rw [cPairW]
    ring

/-- **Frozen-source descent, frozen tilt.** -/
lemma cInterp_cZ_succ_tiltZ (o : Bool) (hrefl0 : Rv v0 v0)
    (hμ0 : μ v0 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (c1 c3 : CtrC) (Z : Finset (Option CtrC)) (h : ℕ) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1) o (some c1) Z
        (some (some c3))
      = cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o c1 Z
          (some (some c3)) h := by
  have hvpos : rE μ Rv v0 ≠ 0 := rE_root_ne_zero Rv μ v0 hrefl0 hμ0
  rw [cInterp, cTiltW_some, cLetO_eq, cLet_some,
    cLetO_eq μ v0 exc1 exc2 ν1 ν2 (!o), cLet_some,
    show cZ (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 c1 (h + 1)
      = muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0) (v0, c1)
        (h + 1) from rfl,
    cScreen_muM_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hrefl0 hvpos
      hsupB Z h c1 _,
    cPairScr, screenE]
  refine tsum_congr fun xp => ?_
  have hW := WresD_cZ_succ_branch (cExcO exc1 exc2 (!o)) μ
    (cNuO ν1 ν2 (!o)) v0 Rv α v0 c1 c3 h xp
  rw [if_pos hrefl0] at hW
  rw [hW, cPairW]
  ring

/-- **Frozen-source descent, fresh tilt**: the root price times the
mixture-tilted pair screen. -/
lemma cInterp_cZ_succ_tiltT (o : Bool) (hrefl0 : Rv v0 v0)
    (hμ0 : μ v0 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (c1 : CtrC) (Z : Finset (Option CtrC)) (h : ℕ) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1) o (some c1) Z (some none)
      = (rE μ Rv v0) ^ (-α)
        * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o c1 Z
            (some none) h := by
  have hvpos : rE μ Rv v0 ≠ 0 := rE_root_ne_zero Rv μ v0 hrefl0 hμ0
  rw [cInterp, cTiltW_some, cLetO_eq, cLet_some,
    cLetO_eq μ v0 exc1 exc2 ν1 ν2 (!o), cLet_none,
    show cZ (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 c1 (h + 1)
      = muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0) (v0, c1)
        (h + 1) from rfl,
    cScreen_muM_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hrefl0 hvpos
      hsupB Z h c1 _,
    cPairScr, screenE, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun xp => ?_
  rw [WresD_cT_succ_branch (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o))
    v0 Rv α hvpos c1 h xp, cPairW]
  ring

/-- **The pair-level weight conversion** (`thm:mixture-tilt-composite`):
the mixture-tilted pair screen splits into `compFloor`-weighted cell
screens. -/
lemma cPairScr_price (o : Bool) (hα0 : 0 ≤ α) (hμ0 : μ v0 ≠ 0)
    (hpairB : ∀ k p, cExcO exc1 exc2 (!o) k = some p →
      ∀ j, j ≤ p.1 → cExcO exc1 exc2 (!o) j = none)
    (hdeclB : ∀ k p, cExcO exc1 exc2 (!o) k = some p →
      cNuO ν1 ν2 (!o) p.1 ≠ 0 ∧ cNuO ν1 ν2 (!o) p.2 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (cs : CtrC) (Z : Finset (Option CtrC)) (h : ℕ) :
    cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o cs Z (some none) h
      ≤ ∑ k ∈ cKO K1 K2 (!o), (if cNuO ν1 ν2 (!o) k = 0 then 0
          else compFloor (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
              k ^ (-α)
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o cs Z
                (some (some (CtrC.ord k))) h) := by
  rw [cPairScr]
  exact cPairScreen_price α Rv μ v0 (cExcO exc1 exc2 (!o))
    (cNuO ν1 ν2 (!o)) (cKO K1 K2 (!o)) hα0 hμ0 hpairB hdeclB
    (fun k hk => (hsupB k).mp hk) h _ _

/-- The `PhiDres` moment of a reachable letter pair. -/
private lemma cMomentW_le (hα : 1 ≤ α) (o : Bool) {n h : ℕ}
    {la lb : Option CtrC} (hra : cReachO exc1 exc2 ν1 ν2 o n la)
    (hrb : cReachO exc1 exc2 ν1 ν2 (!o) n lb) :
    ∑' x, cLet (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 la h x
        * WresD α (cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
            lb h) (fullSim (cRel Rv) h) x
      ≤ 1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h := by
  rw [show cLet (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 la h
      = cLetO μ v0 exc1 exc2 ν1 ν2 o la h from
      (cLetO_eq μ v0 exc1 exc2 ν1 ν2 o la h).symm,
    show cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0 lb h
      = cLetO μ v0 exc1 exc2 ν1 ν2 (!o) lb h from
      (cLetO_eq μ v0 exc1 exc2 ν1 ν2 (!o) lb h).symm]
  exact le_trans (tsum_WresD_le hα _ _ _)
    (add_le_add le_rfl (mul_le_mul_right
      (le_cPsi α Rv μ v0 exc1 exc2 ν1 ν2 o n la lb hra hrb h) _))

/-- The restricted pair moment: the cell-tilted moment of a reachable
source cell against a reachable tilt cell. -/
private lemma cPairMomentR (hα : 1 ≤ α) (o : Bool) {n h : ℕ}
    (ca cb : CtrC)
    (hra0 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp0 (cExcO exc1 exc2 o) ca))
    (hra1 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp1 (cExcO exc1 exc2 o) ca))
    (hrb0 : cReachO exc1 exc2 ν1 ν2 (!o) (n + 1)
      (cComp0 (cExcO exc1 exc2 (!o)) cb))
    (hrb1 : cReachO exc1 exc2 ν1 ν2 (!o) (n + 1)
      (cComp1 (cExcO exc1 exc2 (!o)) cb)) :
    ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 ca h xp
        * WresD α (cXi (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
            cb h) (SquareRel (fullSim (cRel Rv) h)) xp
      ≤ cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  set R := fullSim (cRel Rv) h
  rw [cXi_eq_prod (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 ca h,
    cXi_eq_prod (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0 cb h]
  set ρa := cLet (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
    (cComp0 (cExcO exc1 exc2 o) ca) h
  set ρb := cLet (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
    (cComp1 (cExcO exc1 exc2 o) ca) h
  set ρe := cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
    (cComp0 (cExcO exc1 exc2 (!o)) cb) h
  set ρf := cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
    (cComp1 (cExcO exc1 exc2 (!o)) cb) h
  have hmom : ∀ (la : Option CtrC) (lb : Option CtrC),
      cReachO exc1 exc2 ν1 ν2 o (n + 1) la →
      cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) lb →
      (∑' x, cLet (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 la h x
          * WresD α (cLet (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o))
              v0 lb h) R x)
        ≤ 1 + ENNReal.ofReal α
            * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h := by
    intro la lb hla hlb
    exact cMomentW_le α Rv μ v0 exc1 exc2 ν1 ν2 hα o hla hlb
  calc ∑' xp, prodPMF ρa ρb xp
        * WresD α (prodPMF ρe ρf) (SquareRel R) xp
      ≤ ∑' xp : FullLab (CState V) h × FullLab (CState V) h,
          (prodPMF ρa ρb xp
              * (WresD α ρe R xp.1 * WresD α ρf R xp.2)
            + prodPMF ρa ρb xp
              * (WresD α ρf R xp.1 * WresD α ρe R xp.2)) := by
        refine ENNReal.tsum_le_tsum fun xp => ?_
        calc prodPMF ρa ρb xp * WresD α (prodPMF ρe ρf) (SquareRel R) xp
            ≤ prodPMF ρa ρb xp
                * (WresD α ρe R xp.1 * WresD α ρf R xp.2
                  + WresD α ρf R xp.1 * WresD α ρe R xp.2) :=
              mul_le_mul_right (WresD_square_le_sum hα0 ρe ρf R xp) _
          _ = _ := by ring
    _ = (∑' xp : FullLab (CState V) h × FullLab (CState V) h,
          prodPMF ρa ρb xp
            * (WresD α ρe R xp.1 * WresD α ρf R xp.2))
        + ∑' xp : FullLab (CState V) h × FullLab (CState V) h,
            prodPMF ρa ρb xp
              * (WresD α ρf R xp.1 * WresD α ρe R xp.2) :=
        ENNReal.tsum_add
    _ ≤ (1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)
          * (1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)
        + (1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)
          * (1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) := by
        refine add_le_add ?_ ?_
        · rw [tsum_congr fun xp : FullLab (CState V) h
                × FullLab (CState V) h => show prodPMF ρa ρb xp
                * (WresD α ρe R xp.1 * WresD α ρf R xp.2)
              = (ρa xp.1 * WresD α ρe R xp.1)
                * (ρb xp.2 * WresD α ρf R xp.2) from by
              rw [prodPMF_apply]
              ring,
            tsum_prod_split (fun x => ρa x * WresD α ρe R x)
              (fun x => ρb x * WresD α ρf R x)]
          exact mul_le_mul' (hmom _ _ hra0 hrb0) (hmom _ _ hra1 hrb1)
        · rw [tsum_congr fun xp : FullLab (CState V) h
                × FullLab (CState V) h => show prodPMF ρa ρb xp
                * (WresD α ρf R xp.1 * WresD α ρe R xp.2)
              = (ρa xp.1 * WresD α ρf R xp.1)
                * (ρb xp.2 * WresD α ρe R xp.2) from by
              rw [prodPMF_apply]
              ring,
            tsum_prod_split (fun x => ρa x * WresD α ρf R x)
              (fun x => ρb x * WresD α ρe R x)]
          exact mul_le_mul' (hmom _ _ hra0 hrb1) (hmom _ _ hra1 hrb0)
    _ = cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) := by
        rw [cPairMoment]
        ring

/-- The zero-list successor set of a nonempty zero list is nonempty. -/
lemma cZSuccR_nonempty (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ)
    (Kf : Finset ℕ) (hsup : ∀ k, (ν k : ℝ≥0∞) ≠ 0 ↔ k ∈ Kf)
    {Z : Finset (Option CtrC)} (hZne : Z.Nonempty) :
    (cZSuccR exc Kf Z).Nonempty := by
  obtain ⟨l, hl⟩ := hZne
  rcases l with _ | c
  · obtain ⟨k, hk⟩ := pmf_exists_ne_zero ν
    exact ⟨cComp0 exc (CtrC.ord k), mem_cZSuccR.mpr
      ⟨CtrC.ord k, mem_cMsL.mpr (Or.inr ⟨hl, k, (hsup k).mp hk, rfl⟩),
        Or.inl rfl⟩⟩
  · exact ⟨cComp0 exc c, mem_cZSuccR.mpr
      ⟨c, mem_cMsL.mpr (Or.inl hl), Or.inl rfl⟩⟩

/-- **The Hall output of a descended pair screen** (`thm:hall-factor`
at the composite cells): a product-tilted pair screen of a reachable
source cell splits into the two full-list coordinates of the lifted
successor at the pair moment, plus the quadratic singleton charge. -/
lemma cHallOut (hα : 1 ≤ α) (o : Bool) (n h : ℕ) (c : CtrC)
    {Z : Finset (Option CtrC)}
    (hsc0 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp0 (cExcO exc1 exc2 o) c))
    (hsc1 : cReachO exc1 exc2 ν1 ν2 o (n + 1)
      (cComp1 (cExcO exc1 exc2 o) c))
    (hZ : ∀ l ∈ Z, cReachO exc1 exc2 ν1 ν2 (!o) n l) (hZne : Z.Nonempty)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    {t0 t1 : Option (Option CtrC)}
    (ht0 : ∀ l ∈ t0, cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l)
    (ht1 : ∀ l ∈ t1, cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l)
    (hb0 : cComp0 (cExcO exc1 exc2 o) c ∈ cLetterBox N)
    (hb1 : cComp1 (cExcO exc1 exc2 o) c ∈ cLetterBox N)
    (hZb : ∀ l ∈ Z, l ∈ cLetterBox N)
    (hZSb : ∀ l' ∈ cZSuccR (cExcO exc1 exc2 (!o)) (cKO K1 K2 (!o)) Z,
      l' ∈ cLetterBox N)
    (ht0b : ∀ l ∈ t0, l ∈ cLetterBox N)
    (ht1b : ∀ l ∈ t1, l ∈ cLetterBox N) :
    ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 c h xp
        * (screenInd (SquareRel (fullSim (cRel Rv) h))
            (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
          * (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t0 h xp.1
            * cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t1 h xp.2))
      ≤ (1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)
          * (cE α Rv μ v0 exc1 exc2 ν1 ν2 N h
              (cMk N o hb0 (cZSuccR (cExcO exc1 exc2 (!o))
                (cKO K1 K2 (!o)) Z) ht0b)
            + cE α Rv μ v0 exc1 exc2 ν1 ν2 N h
              (cMk N o hb1 (cZSuccR (cExcO exc1 exc2 (!o))
                (cKO K1 K2 (!o)) Z) ht1b))
        + ((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j)
          * ((cLz N K1 K2 : ℝ≥0∞)
              * ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j) := by
  set R := fullSim (cRel Rv) h with hR
  set b := ⨆ j, cE α Rv μ v0 exc1 exc2 ν1 ν2 N h j with hbdef
  set a1 := 1 + ENNReal.ofReal α * cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
    with ha1
  set G0 := cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t0 h with hG0
  set G1 := cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t1 h with hG1
  set ZS := cZSuccR (cExcO exc1 exc2 (!o)) (cKO K1 K2 (!o)) Z with hZS
  set eA := cExcO exc1 exc2 o with heA
  set nA := cNuO ν1 ν2 o with hnA
  set eB := cExcO exc1 exc2 (!o) with heB
  set nB := cNuO ν1 ν2 (!o) with hnB
  set ρa := cLet eA μ nA v0 (cComp0 eA c) h with hρa
  set ρb := cLet eA μ nA v0 (cComp1 eA c) h with hρb
  set ms := (cMsL (cKO K1 K2 (!o)) Z).map fun c' =>
    (cLet eB μ nB v0 (cComp0 eB c') h,
      cLet eB μ nB v0 (cComp1 eB c') h) with hms
  set zsL := (cCompL eB (cKO K1 K2 (!o)) Z).map fun l =>
    cLet eB μ nB v0 l h with hzsL
  have hZSre : ∀ l' ∈ ZS, cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l' :=
    cZSuccR_reach exc1 exc2 ν1 ν2 K1 K2 hZ hsupB
  have hZSne : ZS.Nonempty := cZSuccR_nonempty eB nB (cKO K1 K2 (!o))
    hsupB hZne
  -- the full-list screens are the successor coordinates
  have hfull : ∀ (ρ : PMF (FullLab (CState V) h)) (s' : Option CtrC)
      (hs' : s' ∈ cLetterBox N)
      (hres : cReachO exc1 exc2 ν1 ν2 o (n + 1) s')
      (heq : ρ = cLet eA μ nA v0 s' h)
      (t' : Option (Option CtrC))
      (ht' : ∀ l ∈ t', cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l)
      (ht'b : ∀ l ∈ t', l ∈ cLetterBox N),
      screenE ρ R zsL (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)
        ≤ cE α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hs' ZS ht'b) := by
    intro ρ s' hs' hres heq t' ht' ht'b
    subst heq
    have hcongr : screenE (cLet eA μ nA v0 s' h) R zsL
        (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)
        = cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o s' ZS t' := by
      rw [cInterp, cLetO_eq]
      refine screenE_congr_mem _ _ (fun ρ' => ?_) _
      rw [mem_cZLaws, hzsL, List.mem_map]
      constructor
      · rintro ⟨l, hlz, rfl⟩
        exact ⟨l, mem_cZSuccR.mpr (mem_cCompL.mp hlz),
          by rw [cLetO_eq]⟩
      · rintro ⟨l, hlz, rfl⟩
        exact ⟨l, mem_cCompL.mpr (mem_cZSuccR.mp hlz),
          by rw [cLetO_eq]⟩
    rw [hcongr]
    exact cInterp_le_cE α Rv μ v0 exc1 exc2 ν1 ν2 N h o hs'
      (fun l hl => hZSb l hl) ht'b (n := n + 1)
      ⟨hres, hZSre, ht', hZSne⟩
  -- the moments
  have hmom : ∀ (ρ : PMF (FullLab (CState V) h)) (s' : Option CtrC)
      (hres : cReachO exc1 exc2 ν1 ν2 o (n + 1) s')
      (heq : ρ = cLet eA μ nA v0 s' h) (t' : Option (Option CtrC))
      (ht' : ∀ l ∈ t', cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l),
      (∑' x, ρ x * cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h x)
        ≤ a1 := by
    intro ρ s' hres heq t' ht'
    subst heq
    rcases t' with _ | l3
    · rw [cTiltW_none]
      refine le_trans (le_of_eq ?_) le_self_add
      rw [tsum_congr fun x =>
        mul_one (cLet eA μ nA v0 s' h x), PMF.tsum_coe]
    · rw [cTiltW_some, cLetO_eq]
      exact cMomentW_le α Rv μ v0 exc1 exc2 ν1 ν2 hα o hres
        (ht' l3 rfl)
  -- the singleton sums
  have hsing : ∀ (ρ : PMF (FullLab (CState V) h)) (s' : Option CtrC)
      (hs' : s' ∈ cLetterBox N)
      (hres : cReachO exc1 exc2 ν1 ν2 o (n + 1) s')
      (heq : ρ = cLet eA μ nA v0 s' h) (t' : Option (Option CtrC))
      (ht' : ∀ l ∈ t', cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l)
      (ht'b : ∀ l ∈ t', l ∈ cLetterBox N),
      ((zsL.map fun ρ' => screenE ρ R [ρ']
          (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)).sum)
        ≤ (cLz N K1 K2 : ℝ≥0∞) * b := by
    intro ρ s' hs' hres heq t' ht' ht'b
    subst heq
    have hlen : (zsL.map fun ρ' => screenE (cLet eA μ nA v0 s' h) R [ρ']
        (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)).length
        ≤ cLz N K1 K2 := by
      rw [List.length_map, hzsL, List.length_map]
      refine le_trans (cCompL_length_le eB (cKO K1 K2 (!o)) Z) ?_
      rw [cLz]
      refine Nat.mul_le_mul_left 2 (Nat.mul_le_mul ?_ ?_)
      · exact Finset.card_le_card fun l hl => hZb l hl
      · exact max_le (cKO_card_le_cMx K1 K2 (!o)) (one_le_cMx K1 K2)
    have hmemb : ∀ x ∈ zsL.map fun ρ' => screenE (cLet eA μ nA v0 s' h)
        R [ρ'] (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h), x ≤ b := by
      intro x hx
      obtain ⟨ρ', hρ', rfl⟩ := List.mem_map.mp hx
      rw [hzsL, List.mem_map] at hρ'
      obtain ⟨l, hlz, rfl⟩ := hρ'
      have hlre : cReachO exc1 exc2 ν1 ν2 (!o) (n + 1) l := by
        obtain ⟨c', hc', hor⟩ := mem_cCompL.mp hlz
        exact cMsL_comp_reach exc1 exc2 ν1 ν2 K1 K2 hZ hsupB hc' hor
      have hlb : l ∈ cLetterBox N :=
        hZSb l (mem_cZSuccR.mpr (mem_cCompL.mp hlz))
      have hval : screenE (cLet eA μ nA v0 s' h) R
          [cLet eB μ nB v0 l h]
          (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)
          = cInterp α Rv μ v0 exc1 exc2 ν1 ν2 h o s' {l} t' := by
        rw [cInterp, cLetO_eq]
        refine screenE_congr_mem _ _ (fun ρ'' => ?_) _
        rw [mem_cZLaws, List.mem_singleton]
        constructor
        · rintro rfl
          exact ⟨l, Finset.mem_singleton_self _, by rw [cLetO_eq]⟩
        · rintro ⟨l', hl', rfl⟩
          rw [Finset.mem_singleton.mp hl', cLetO_eq]
      rw [hval, hbdef]
      refine le_trans (cInterp_le_cE α Rv μ v0 exc1 exc2 ν1 ν2 N h o
        hs' (fun l' hl' => by
          rw [Finset.mem_singleton.mp hl']
          exact hlb) ht'b (n := n + 1)
        ⟨hres, fun l' hl' => by
          rw [Finset.mem_singleton.mp hl']
          exact hlre, ht', Finset.singleton_nonempty _⟩) (le_iSup _ _)
    calc (zsL.map fun ρ' => screenE (cLet eA μ nA v0 s' h) R [ρ']
          (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)).sum
        ≤ (zsL.map fun ρ' => screenE (cLet eA μ nA v0 s' h) R [ρ']
            (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)).length • b :=
          List.sum_le_card_nsmul _ _ hmemb
      _ = ((zsL.map fun ρ' => screenE (cLet eA μ nA v0 s' h) R [ρ']
            (cTiltW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t' h)).length
              : ℝ≥0∞) * b := nsmul_eq_mul _ _
      _ ≤ (cLz N K1 K2 : ℝ≥0∞) * b :=
          mul_le_mul_left (Nat.cast_le.mpr hlen) b
  -- assemble through the Hall factorization
  have hind : ∀ xp : FullLab (CState V) h × FullLab (CState V) h,
      screenInd (SquareRel R)
        (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
      = if ∀ p ∈ ms, rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
          then 1 else 0 := by
    intro xp
    rw [screenInd]
    refine if_congr ⟨fun hall p hp => ?_, fun hall ρ hρ => ?_⟩ rfl rfl
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hp
      have := hall _ (List.mem_map.mpr ⟨c', hc', rfl⟩)
      rwa [cXi_eq_prod] at this
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hρ
      rw [cXi_eq_prod]
      exact hall _ (List.mem_map.mpr ⟨c', hc', rfl⟩)
  have hmem : ∀ p ∈ ms, p.1 ∈ zsL ∧ p.2 ∈ zsL := by
    intro p hp
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hp
    exact ⟨List.mem_map.mpr ⟨_, mem_cCompL.mpr ⟨c', hc', Or.inl rfl⟩,
        rfl⟩,
      List.mem_map.mpr ⟨_, mem_cCompL.mpr ⟨c', hc', Or.inr rfl⟩, rfl⟩⟩
  have hcov : ∀ ρ ∈ zsL, ∃ p ∈ ms, ρ = p.1 ∨ ρ = p.2 := by
    intro ρ hρ
    obtain ⟨l, hlz, rfl⟩ := List.mem_map.mp hρ
    obtain ⟨c', hc', hor⟩ := mem_cCompL.mp hlz
    refine ⟨_, List.mem_map.mpr ⟨c', hc', rfl⟩, ?_⟩
    rcases hor with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  calc ∑' xp, cXi eA μ nA v0 c h xp
        * (screenInd (SquareRel R)
            (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
          * (G0 xp.1 * G1 xp.2))
      = ∑' xp, prodPMF ρa ρb xp
          * ((if ∀ p ∈ ms, rE (prodPMF p.1 p.2) (SquareRel R) xp = 0
              then 1 else 0) * (G0 xp.1 * G1 xp.2)) := by
        rw [cXi_eq_prod eA μ nA v0 c h]
        exact tsum_congr fun xp => by rw [hind xp]
    _ ≤ screenE ρa R zsL G0 * (∑' x, ρb x * G1 x)
        + (∑' x, ρa x * G0 x) * screenE ρb R zsL G1
        + (zsL.map fun ρ => screenE ρa R [ρ] G0).sum
          * (zsL.map fun ρ' => screenE ρb R [ρ'] G1).sum :=
        hallFactorize ρa ρb R ms zsL hmem hcov G0 G1
    _ ≤ cE α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hb0 ZS ht0b) * a1
        + a1 * cE α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hb1 ZS ht1b)
        + ((cLz N K1 K2 : ℝ≥0∞) * b) * ((cLz N K1 K2 : ℝ≥0∞) * b) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact mul_le_mul'
            (hfull ρa _ hb0 hsc0 hρa t0 ht0 ht0b)
            (hmom ρb _ hsc1 hρb t1 ht1)
        · exact mul_le_mul' (hmom ρa _ hsc0 hρa t0 ht0)
            (hfull ρb _ hb1 hsc1 hρb t1 ht1 ht1b)
        · exact mul_le_mul' (hsing ρa _ hb0 hsc0 hρa t0 ht0 ht0b)
            (hsing ρb _ hb1 hsc1 hρb t1 ht1 ht1b)
    _ ≤ a1 * (cE α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hb0 ZS ht0b)
          + cE α Rv μ v0 exc1 exc2 ν1 ν2 N h (cMk N o hb1 ZS ht1b))
        + ((cLz N K1 K2 : ℝ≥0∞) * b) * ((cLz N K1 K2 : ℝ≥0∞) * b) := by
        refine add_le_add (le_of_eq ?_) le_rfl
        ring

private lemma screenInd_le_one₀ {X : Type} (R : X → X → Prop)
    (zs : List (PMF X)) (x : X) : screenInd R zs x ≤ 1 := by
  rw [screenInd]
  split_ifs <;> simp

private lemma mul_ind_mul_le {X : Type} {a w : ℝ≥0∞}
    (R : X → X → Prop) (zs : List (PMF X)) (x : X) :
    a * screenInd R zs x * w ≤ a * w := by
  calc a * screenInd R zs x * w
      ≤ a * 1 * w :=
        mul_le_mul_left (mul_le_mul_right (screenInd_le_one₀ R zs x) a) w
    _ = a * w := by rw [mul_one]

private lemma cPairScr_eq_tsum (o : Bool) (cs : CtrC)
    (Z : Finset (Option CtrC)) (t : Option (Option CtrC)) (h : ℕ) :
    cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o cs Z t h
      = ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 cs h xp
          * (screenInd (SquareRel (fullSim (cRel Rv) h))
              (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
            * cPairW α Rv μ v0 exc1 exc2 ν1 ν2 (!o) t h xp) := by
  rw [cPairScr, screenE]
  exact tsum_congr fun xp => mul_assoc _ _ _

/-- **Fresh-source descent, unit tilt**: far roots inject into the far
mass, near roots into the retained mixture of descended pair
screens. -/
lemma cInterp_cT_succ_unit_le (o : Bool) (hμ0 : μ v0 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (Z : Finset (Option CtrC)) (h : ℕ) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1) o none Z none
      ≤ (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞))
        + ∑' k, cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o (CtrC.ord k) Z
                none h := by
  rw [cInterp, cTiltW_none, cLetO_eq, cLet_none,
    cT_eq_freshQ_bind (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 (h + 1),
    screenE_bind_left]
  have hpt : ∀ s : V × ℕ,
      freshQ μ (cNuO ν1 ν2 o) s
        * screenE (muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0)
            (s.1, CtrC.ord s.2) (h + 1)) (fullSim (cRel Rv) (h + 1))
            (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1)) (fun _ => 1)
      ≤ (if Rv s.1 v0 then 0 else freshQ μ (cNuO ν1 ν2 o) s)
        + freshQ μ (cNuO ν1 ν2 o) s
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord s.2) Z none h := by
    rintro ⟨w, k⟩
    by_cases hw : Rv w v0
    · rw [if_pos hw, zero_add]
      refine mul_le_mul_right (le_of_eq ?_) _
      rw [cScreen_muM_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hw
        (rE_near_ne_zero Rv μ v0 hμ0 hw) hsupB Z h (CtrC.ord k)
        (fun _ => 1),
        cPairScr_eq_tsum]
      rfl
    · rw [if_neg hw]
      refine le_trans ?_ le_self_add
      exact le_trans (mul_le_mul_right (screenE_unit_le_one _ _ _) _)
        (le_of_eq (mul_one _))
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_add]
  refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · calc ∑' s : V × ℕ, (if Rv s.1 v0 then 0
          else freshQ μ (cNuO ν1 ν2 o) s)
        = ∑' s : V × ℕ,
            (if Rv s.1 v0 then 0 else (μ s.1 : ℝ≥0∞))
              * cNuO ν1 ν2 o s.2 := by
          refine tsum_congr fun s => ?_
          by_cases hv : Rv s.1 v0
          · rw [if_pos hv, if_pos hv, zero_mul]
          · rw [if_neg hv, if_neg hv]
            exact prodPMF_apply μ (cNuO ν1 ν2 o) s
      _ = (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞))
          * ∑' l, (cNuO ν1 ν2 o l : ℝ≥0∞) :=
          tsum_prod_split
            (fun v => if Rv v v0 then 0 else (μ v : ℝ≥0∞))
            (fun l => (cNuO ν1 ν2 o l : ℝ≥0∞))
      _ = ∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞) := by
          rw [(cNuO ν1 ν2 o).tsum_coe, mul_one]
  · calc ∑' s : V × ℕ, freshQ μ (cNuO ν1 ν2 o) s
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord s.2) Z none h
        = ∑' s : V × ℕ, (μ s.1 : ℝ≥0∞) * (cNuO ν1 ν2 o s.2
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord s.2) Z none h) := by
          refine tsum_congr fun s => ?_
          rw [show freshQ μ (cNuO ν1 ν2 o) s
              = μ s.1 * cNuO ν1 ν2 o s.2 from
              prodPMF_apply μ (cNuO ν1 ν2 o) s, mul_assoc]
      _ = (∑' v, (μ v : ℝ≥0∞)) * ∑' k, cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord k) Z none h :=
          tsum_prod_split (fun v => (μ v : ℝ≥0∞))
            (fun k => cNuO ν1 ν2 o k
              * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                  (CtrC.ord k) Z none h)
      _ = ∑' k, cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord k) Z none h := by
          rw [PMF.tsum_coe, one_mul]

/-- **Fresh-source descent, frozen tilt**: the frozen tilt kills the
far roots. -/
lemma cInterp_cT_succ_tiltZ_le (o : Bool) (hμ0 : μ v0 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    (c3 : CtrC) (Z : Finset (Option CtrC)) (h : ℕ) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1) o none Z (some (some c3))
      ≤ ∑' k, cNuO ν1 ν2 o k
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o (CtrC.ord k) Z
              (some (some c3)) h := by
  rw [cInterp, cTiltW_some, cLetO_eq, cLet_none,
    cLetO_eq μ v0 exc1 exc2 ν1 ν2 (!o), cLet_some,
    cT_eq_freshQ_bind (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 (h + 1),
    screenE_bind_left]
  have hpt : ∀ s : V × ℕ,
      freshQ μ (cNuO ν1 ν2 o) s
        * screenE (muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0)
            (s.1, CtrC.ord s.2) (h + 1)) (fullSim (cRel Rv) (h + 1))
            (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1))
            (WresD α (cZ (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
              c3 (h + 1)) (fullSim (cRel Rv) (h + 1)))
      ≤ freshQ μ (cNuO ν1 ν2 o) s
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord s.2) Z (some (some c3)) h := by
    rintro ⟨w, k⟩
    by_cases hw : Rv w v0
    · refine mul_le_mul_right (le_of_eq ?_) _
      rw [cScreen_muM_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hw
        (rE_near_ne_zero Rv μ v0 hμ0 hw) hsupB Z h (CtrC.ord k) _,
        cPairScr_eq_tsum]
      refine tsum_congr fun xp => ?_
      have hW := WresD_cZ_succ_branch (cExcO exc1 exc2 (!o)) μ
        (cNuO ν1 ν2 (!o)) v0 Rv α w (CtrC.ord k) c3 h xp
      rw [if_pos hw] at hW
      rw [hW, cPairW]
    · have h0 : screenE (muM (compK (cExcO exc1 exc2 o) μ
          (cNuO ν1 ν2 o) v0) (w, CtrC.ord k) (h + 1))
          (fullSim (cRel Rv) (h + 1))
          (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1))
          (WresD α (cZ (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
            c3 (h + 1)) (fullSim (cRel Rv) (h + 1))) = 0 := by
        refine le_antisymm ?_ zero_le
        calc screenE (muM (compK (cExcO exc1 exc2 o) μ
              (cNuO ν1 ν2 o) v0) (w, CtrC.ord k) (h + 1))
              (fullSim (cRel Rv) (h + 1))
              (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1))
              (WresD α (cZ (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o))
                v0 c3 (h + 1)) (fullSim (cRel Rv) (h + 1)))
            ≤ ∑' x, muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0)
                (w, CtrC.ord k) (h + 1) x
                * WresD α (cZ (cExcO exc1 exc2 (!o)) μ
                    (cNuO ν1 ν2 (!o)) v0 c3 (h + 1))
                    (fullSim (cRel Rv) (h + 1)) x := by
              rw [screenE]
              exact ENNReal.tsum_le_tsum fun x => mul_ind_mul_le _ _ x
          _ = ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
                (CtrC.ord k) h xp
                * WresD α (cZ (cExcO exc1 exc2 (!o)) μ
                    (cNuO ν1 ν2 (!o)) v0 c3 (h + 1))
                    (fullSim (cRel Rv) (h + 1))
                    (branch (w, CtrC.ord k) xp) := by
              rw [muM_compK_succ]
              exact tsum_map_mul _ _ _
          _ = 0 := by
              refine ENNReal.tsum_eq_zero.mpr fun xp => ?_
              have hW := WresD_cZ_succ_branch (cExcO exc1 exc2 (!o)) μ
                (cNuO ν1 ν2 (!o)) v0 Rv α w (CtrC.ord k) c3 h xp
              rw [if_neg hw] at hW
              rw [hW, mul_zero]
      rw [h0, mul_zero]
      exact zero_le
  refine le_trans (ENNReal.tsum_le_tsum hpt) (le_of_eq ?_)
  calc ∑' s : V × ℕ, freshQ μ (cNuO ν1 ν2 o) s
        * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
            (CtrC.ord s.2) Z (some (some c3)) h
      = ∑' s : V × ℕ, (μ s.1 : ℝ≥0∞) * (cNuO ν1 ν2 o s.2
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord s.2) Z (some (some c3)) h) := by
        refine tsum_congr fun s => ?_
        rw [show freshQ μ (cNuO ν1 ν2 o) s
            = μ s.1 * cNuO ν1 ν2 o s.2 from
            prodPMF_apply μ (cNuO ν1 ν2 o) s, mul_assoc]
    _ = (∑' v, (μ v : ℝ≥0∞)) * ∑' k, cNuO ν1 ν2 o k
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord k) Z (some (some c3)) h :=
        tsum_prod_split (fun v => (μ v : ℝ≥0∞))
          (fun k => cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord k) Z (some (some c3)) h)
    _ = ∑' k, cNuO ν1 ν2 o k
          * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord k) Z (some (some c3)) h := by
        rw [PMF.tsum_coe, one_mul]

/-- **Fresh-source descent, fresh tilt**: far roots inject into the far
tilt at the priced pair moment, near roots into the root price times
the retained mixture of mixture-tilted pair screens. -/
lemma cInterp_cT_succ_tiltT_le (o : Bool) (hα : 1 ≤ α)
    (hμ0 : μ v0 ≠ 0)
    (hpairB : ∀ k p, cExcO exc1 exc2 (!o) k = some p →
      ∀ j, j ≤ p.1 → cExcO exc1 exc2 (!o) j = none)
    (hdeclB : ∀ k p, cExcO exc1 exc2 (!o) k = some p →
      cNuO ν1 ν2 (!o) p.1 ≠ 0 ∧ cNuO ν1 ν2 (!o) p.2 ≠ 0)
    (hsupB : ∀ k, (cNuO ν1 ν2 (!o) k : ℝ≥0∞) ≠ 0 ↔ k ∈ cKO K1 K2 (!o))
    {T RT : ℝ≥0∞}
    (hT : cTiltSum α (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0 ≤ T)
    (hRT : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    {n : ℕ} (hfrA : cReachO exc1 exc2 ν1 ν2 o n none)
    (hfrB : cReachO exc1 exc2 ν1 ν2 (!o) n none)
    (Z : Finset (Option CtrC)) (h : ℕ) :
    cInterp α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1) o none Z (some none)
      ≤ (∑' v, if Rv v v0 then 0
            else (μ v : ℝ≥0∞) * WresD α μ Rv v)
          * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h))
        + RT * ∑' k, cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o (CtrC.ord k) Z
                (some none) h := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hmix : ∀ k : ℕ, (cNuO ν1 ν2 o k : ℝ≥0∞) ≠ 0 →
      (∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
          (CtrC.ord k) h xp
        * WresD α (cXiBar (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o))
            v0 h) (SquareRel (fullSim (cRel Rv) h)) xp)
      ≤ T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) := by
    intro k hk
    refine le_trans (tsum_WresD_cXiBar_le_sum (cExcO exc1 exc2 (!o)) μ
      (cNuO ν1 ν2 (!o)) v0 hpairB hdeclB hμ0 hα0 Rv h _) ?_
    calc ∑' k', (if cNuO ν1 ν2 (!o) k' = 0 then 0 else
          compFloor (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
              k' ^ (-α)
            * ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
                (CtrC.ord k) h xp
              * WresD α (cXi (cExcO exc1 exc2 (!o)) μ
                  (cNuO ν1 ν2 (!o)) v0 (CtrC.ord k') h)
                  (SquareRel (fullSim (cRel Rv) h)) xp)
        ≤ ∑' k', (if cNuO ν1 ν2 (!o) k' = 0 then 0 else
            compFloor (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
                k' ^ (-α))
              * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) := by
          refine ENNReal.tsum_le_tsum fun k' => ?_
          by_cases hk' : cNuO ν1 ν2 (!o) k' = 0
          · rw [if_pos hk', if_pos hk', zero_mul]
          · rw [if_neg hk', if_neg hk']
            refine mul_le_mul_right ?_ _
            refine cPairMomentR α Rv μ v0 exc1 exc2 ν1 ν2 hα o
              (CtrC.ord k) (CtrC.ord k') (n := n) ?_ ?_ ?_ ?_
            · exact cReachO_spawn exc1 exc2 ν1 ν2 hfrA
                ⟨k, hk, Or.inl rfl⟩
            · exact cReachO_spawn exc1 exc2 ν1 ν2 hfrA
                ⟨k, hk, Or.inr rfl⟩
            · exact cReachO_spawn exc1 exc2 ν1 ν2 hfrB
                ⟨k', hk', Or.inl rfl⟩
            · exact cReachO_spawn exc1 exc2 ν1 ν2 hfrB
                ⟨k', hk', Or.inr rfl⟩
      _ = (∑' k', if cNuO ν1 ν2 (!o) k' = 0 then 0 else
            compFloor (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
                k' ^ (-α))
            * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) :=
          ENNReal.tsum_mul_right
      _ ≤ T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) :=
          mul_le_mul_left hT _
  rw [cInterp, cTiltW_some, cLetO_eq, cLet_none,
    cLetO_eq μ v0 exc1 exc2 ν1 ν2 (!o), cLet_none,
    cT_eq_freshQ_bind (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0 (h + 1),
    screenE_bind_left]
  have hpt : ∀ s : V × ℕ,
      freshQ μ (cNuO ν1 ν2 o) s
        * screenE (muM (compK (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0)
            (s.1, CtrC.ord s.2) (h + 1)) (fullSim (cRel Rv) (h + 1))
            (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1))
            (WresD α (cT (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
              (h + 1)) (fullSim (cRel Rv) (h + 1)))
      ≤ (if Rv s.1 v0 then 0
          else (μ s.1 : ℝ≥0∞) * WresD α μ Rv s.1
            * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h))
            * cNuO ν1 ν2 o s.2)
        + freshQ μ (cNuO ν1 ν2 o) s
          * (RT * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord s.2) Z (some none) h) := by
    rintro ⟨w, k⟩
    by_cases hνk : (cNuO ν1 ν2 o k : ℝ≥0∞) = 0
    · have hfq : freshQ μ (cNuO ν1 ν2 o) (w, k) = 0 := by
        rw [show freshQ μ (cNuO ν1 ν2 o) (w, k)
            = μ w * cNuO ν1 ν2 o k from
            prodPMF_apply μ (cNuO ν1 ν2 o) (w, k), hνk, mul_zero]
      rw [hfq, zero_mul]
      exact zero_le
    by_cases hw : Rv w v0
    · rw [if_pos hw, zero_add]
      refine mul_le_mul_right ?_ _
      have hvpos : rE μ Rv w ≠ 0 := rE_near_ne_zero Rv μ v0 hμ0 hw
      rw [cScreen_muM_descend Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o hw hvpos
        hsupB Z h (CtrC.ord k) _]
      calc ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
            (CtrC.ord k) h xp
            * (screenInd (SquareRel (fullSim (cRel Rv) h))
                (cPairLaws μ v0 exc1 exc2 ν1 ν2 K1 K2 (!o) Z h) xp
              * WresD α (cT (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o))
                  v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
                  (branch (w, CtrC.ord k) xp))
          = (rE μ Rv w) ^ (-α)
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord k) Z (some none) h := by
            rw [cPairScr_eq_tsum, ← ENNReal.tsum_mul_left]
            refine tsum_congr fun xp => ?_
            rw [WresD_cT_succ_branch (cExcO exc1 exc2 (!o)) μ
              (cNuO ν1 ν2 (!o)) v0 Rv α hvpos (CtrC.ord k) h xp,
              cPairW]
            ring
        _ ≤ RT * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord k) Z (some none) h :=
            mul_le_mul_left (hRT w hw) _
    · rw [if_neg hw]
      refine le_trans ?_ le_self_add
      by_cases hvr : rE μ Rv w = 0
      · have h0 : ∀ x, WresD α (cT (cExcO exc1 exc2 (!o)) μ
            (cNuO ν1 ν2 (!o)) v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
            (branch (w, CtrC.ord k)
              x) = 0 := by
          intro x
          rw [WresD, if_pos]
          rw [rE_cT_succ_branch Rv (cExcO exc1 exc2 (!o)) μ
            (cNuO ν1 ν2 (!o)) v0 w (CtrC.ord k) h x, hvr, zero_mul]
        have hz : screenE (muM (compK (cExcO exc1 exc2 o) μ
            (cNuO ν1 ν2 o) v0) (w, CtrC.ord k) (h + 1))
            (fullSim (cRel Rv) (h + 1))
            (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1))
            (WresD α (cT (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
              (h + 1)) (fullSim (cRel Rv) (h + 1))) = 0 := by
          refine le_antisymm ?_ zero_le
          calc _ ≤ ∑' x, muM (compK (cExcO exc1 exc2 o) μ
                (cNuO ν1 ν2 o) v0) (w, CtrC.ord k) (h + 1) x
                * WresD α (cT (cExcO exc1 exc2 (!o)) μ
                    (cNuO ν1 ν2 (!o)) v0 (h + 1))
                    (fullSim (cRel Rv) (h + 1)) x := by
                rw [screenE]
                exact ENNReal.tsum_le_tsum fun x => mul_ind_mul_le _ _ x
            _ = ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
                  (CtrC.ord k) h xp
                  * WresD α (cT (cExcO exc1 exc2 (!o)) μ
                      (cNuO ν1 ν2 (!o)) v0 (h + 1))
                      (fullSim (cRel Rv) (h + 1))
                      (branch (w, CtrC.ord k) xp) := by
                rw [muM_compK_succ]
                exact tsum_map_mul _ _ _
            _ = 0 := ENNReal.tsum_eq_zero.mpr fun xp => by
                rw [h0 xp, mul_zero]
        rw [hz, mul_zero]
        exact zero_le
      · have hscr : screenE (muM (compK (cExcO exc1 exc2 o) μ
            (cNuO ν1 ν2 o) v0) (w, CtrC.ord k) (h + 1))
            (fullSim (cRel Rv) (h + 1))
            (cZLaws μ v0 exc1 exc2 ν1 ν2 (!o) Z (h + 1))
            (WresD α (cT (cExcO exc1 exc2 (!o)) μ (cNuO ν1 ν2 (!o)) v0
              (h + 1)) (fullSim (cRel Rv) (h + 1)))
            ≤ (rE μ Rv w) ^ (-α)
              * (T * cPairMoment α
                  (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)) := by
          calc _ ≤ ∑' x, muM (compK (cExcO exc1 exc2 o) μ
                (cNuO ν1 ν2 o) v0) (w, CtrC.ord k) (h + 1) x
                * WresD α (cT (cExcO exc1 exc2 (!o)) μ
                    (cNuO ν1 ν2 (!o)) v0 (h + 1))
                    (fullSim (cRel Rv) (h + 1)) x := by
                rw [screenE]
                exact ENNReal.tsum_le_tsum fun x => mul_ind_mul_le _ _ x
            _ = (rE μ Rv w) ^ (-α)
                * ∑' xp, cXi (cExcO exc1 exc2 o) μ (cNuO ν1 ν2 o) v0
                    (CtrC.ord k) h xp
                  * WresD α (cXiBar (cExcO exc1 exc2 (!o)) μ
                      (cNuO ν1 ν2 (!o)) v0 h)
                      (SquareRel (fullSim (cRel Rv) h)) xp := by
                rw [muM_compK_succ, tsum_map_mul _ _ _,
                  ← ENNReal.tsum_mul_left]
                refine tsum_congr fun xp => ?_
                rw [WresD_cT_succ_branch (cExcO exc1 exc2 (!o)) μ
                  (cNuO ν1 ν2 (!o)) v0 Rv α hvr (CtrC.ord k) h xp]
                ring
            _ ≤ (rE μ Rv w) ^ (-α)
                * (T * cPairMoment α
                    (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)) :=
                mul_le_mul_right (hmix k hνk) _
        calc freshQ μ (cNuO ν1 ν2 o) (w, k) * _
            ≤ freshQ μ (cNuO ν1 ν2 o) (w, k)
              * ((rE μ Rv w) ^ (-α)
                * (T * cPairMoment α
                    (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h))) :=
              mul_le_mul_right hscr _
          _ = (μ w : ℝ≥0∞) * WresD α μ Rv w
              * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h))
              * cNuO ν1 ν2 o k := by
              rw [show freshQ μ (cNuO ν1 ν2 o) (w, k)
                  = μ w * cNuO ν1 ν2 o k from
                  prodPMF_apply μ (cNuO ν1 ν2 o) (w, k),
                ← rE_rpow_neg_eq_WresD μ Rv w hvr]
              ring
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_add]
  refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · calc ∑' s : V × ℕ, (if Rv s.1 v0 then 0
          else (μ s.1 : ℝ≥0∞) * WresD α μ Rv s.1
            * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h))
            * cNuO ν1 ν2 o s.2)
        = ∑' s : V × ℕ,
            ((if Rv s.1 v0 then 0
              else (μ s.1 : ℝ≥0∞) * WresD α μ Rv s.1)
              * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)))
              * cNuO ν1 ν2 o s.2 := by
          refine tsum_congr fun s => ?_
          by_cases hv : Rv s.1 v0
          · rw [if_pos hv, if_pos hv, zero_mul, zero_mul]
          · rw [if_neg hv, if_neg hv]
      _ = ((∑' v, if Rv v v0 then 0
            else (μ v : ℝ≥0∞) * WresD α μ Rv v)
          * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)))
          * ∑' l, (cNuO ν1 ν2 o l : ℝ≥0∞) := by
          rw [← ENNReal.tsum_mul_right]
          exact tsum_prod_split
            (fun v => (if Rv v v0 then 0
                else (μ v : ℝ≥0∞) * WresD α μ Rv v)
              * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)))
            (fun l => (cNuO ν1 ν2 o l : ℝ≥0∞))
      _ = (∑' v, if Rv v v0 then 0
            else (μ v : ℝ≥0∞) * WresD α μ Rv v)
          * (T * cPairMoment α (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)) := by
          rw [(cNuO ν1 ν2 o).tsum_coe, mul_one]
  · calc ∑' s : V × ℕ, freshQ μ (cNuO ν1 ν2 o) s
          * (RT * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
              (CtrC.ord s.2) Z (some none) h)
        = ∑' s : V × ℕ, (μ s.1 : ℝ≥0∞) * (RT * (cNuO ν1 ν2 o s.2
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord s.2) Z (some none) h)) := by
          refine tsum_congr fun s => ?_
          rw [show freshQ μ (cNuO ν1 ν2 o) s
              = μ s.1 * cNuO ν1 ν2 o s.2 from
              prodPMF_apply μ (cNuO ν1 ν2 o) s]
          ring
      _ = (∑' v, (μ v : ℝ≥0∞)) * ∑' k, RT * (cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord k) Z (some none) h) :=
          tsum_prod_split (fun v => (μ v : ℝ≥0∞))
            (fun k => RT * (cNuO ν1 ν2 o k
              * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                  (CtrC.ord k) Z (some none) h))
      _ = RT * ∑' k, cNuO ν1 ν2 o k
            * cPairScr α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 o
                (CtrC.ord k) Z (some none) h := by
          rw [PMF.tsum_coe, one_mul, ENNReal.tsum_mul_left]

end StepRows

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

private lemma comps_mem_cSrcC_some (exc : ℕ → Option (ℕ × ℕ))
    (Kf : Finset ℕ) (c : CtrC) :
    cComp0 exc c ∈ cSrcC exc Kf (some c)
      ∧ cComp1 exc c ∈ cSrcC exc Kf (some c) := by
  rw [cSrcC]
  exact ⟨Finset.mem_insert_self _ _,
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

private lemma comps_mem_cSrcC_none {exc : ℕ → Option (ℕ × ℕ)}
    {Kf : Finset ℕ} {k : ℕ} (hk : k ∈ Kf) (hexc : exc k = none) :
    cComp0 exc (CtrC.ord k) ∈ cSrcC exc Kf none
      ∧ cComp1 exc (CtrC.ord k) ∈ cSrcC exc Kf none := by
  rw [cSrcC]
  constructor
  · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hexc⟩,
      Finset.mem_insert_self _ _⟩
  · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hexc⟩,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

private lemma comps_mem_cSrcE_none {exc : ℕ → Option (ℕ × ℕ)}
    {Kf : Finset ℕ} {k : ℕ} (hk : k ∈ Kf) (hexc : exc k ≠ none) :
    cComp0 exc (CtrC.ord k) ∈ cSrcE exc Kf none
      ∧ cComp1 exc (CtrC.ord k) ∈ cSrcE exc Kf none := by
  rw [cSrcE]
  constructor
  · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hexc⟩,
      Finset.mem_insert_self _ _⟩
  · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hexc⟩,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

private lemma none_mem_cTiltC_none (exc : ℕ → Option (ℕ × ℕ)) :
    (none : Option (Option CtrC)) ∈ cTiltC exc none := by
  rw [cTiltC]
  exact Finset.mem_singleton_self _

private lemma comps_mem_cTiltC_some (exc : ℕ → Option (ℕ × ℕ))
    (c3 : CtrC) :
    some (cComp0 exc c3) ∈ cTiltC exc (some (some c3))
      ∧ some (cComp1 exc c3) ∈ cTiltC exc (some (some c3)) := by
  rw [cTiltC]
  exact ⟨Finset.mem_insert_self _ _,
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

private lemma comps_mem_cTiltP {exc : ℕ → Option (ℕ × ℕ)}
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
private lemma cCellOutU (hα : 1 ≤ α) (o : Bool) (n h : ℕ) (cs : CtrC)
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
private lemma cCellOutT (hα : 1 ≤ α) (o : Bool) (n h : ℕ) (cs c3 : CtrC)
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

/-- A `ν`-average of a uniformly bounded charged family. -/
private lemma tsum_nu_mul_le (ν : PMF ℕ) {f : ℕ → ℝ≥0∞} {U : ℝ≥0∞}
    (hf : ∀ k, (ν k : ℝ≥0∞) ≠ 0 → f k ≤ U) :
    (∑' k, (ν k : ℝ≥0∞) * f k) ≤ U := by
  calc ∑' k, (ν k : ℝ≥0∞) * f k
      ≤ ∑' k, (ν k : ℝ≥0∞) * U := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        by_cases hk : (ν k : ℝ≥0∞) = 0
        · rw [hk, zero_mul, zero_mul]
        · exact mul_le_mul_right (hf k hk) _
    _ = (∑' k, (ν k : ℝ≥0∞)) * U := ENNReal.tsum_mul_right
    _ = U := by rw [ν.tsum_coe, one_mul]

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

private lemma cGlue_PT2 {F A B Q G1 G2 MN MP : ℝ≥0∞}
    (hF : F ≤ G1) (hA : A ≤ MN) (hB : B ≤ MP) (hQ : Q ≤ G2) :
    F + (A + B + Q) ≤ (G1 + G2) + (MN + MP) := by
  have he : F + (A + B + Q) = (F + Q) + (A + B) := by ring
  rw [he]
  exact add_le_add (add_le_add hF hQ) (add_le_add hA hB)

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

/-- **Composite two-law infinite matching, final form**
(`thm:composite-matching`): `composite_matching_le_closed` with the
screen-ledger input discharged by `screenLedgerInput_holds`: one
binary-tree automorphism matches the two infinite composite samples
with probability at least `1 - cKc * etaG`. -/
theorem composite_matching_le_final {Omega : Type*}
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
    (χ0 C cu : ℝ≥0∞) (hχ0 : χ0 ≠ 0)
    (hC : cNcBudget (RT * T) (cMx K1 K2) ≤ C)
    (hafford : cMpBudget eM (RT * T) (cMx K1 K2) ≤ χ0 * C)
    (hcu : 2 ≤ cu)
    (hsmall : cSmallness χ0 C (cRank N))
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
    (screenLedgerInput_holds α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 S E1 E2 N
      hα hRv hsymm hμ0 hhalf hN hdeclN1 hcharged1 hdeclN2 hcharged2
      hpair1 hpair2 hdecl1 hdecl2 hsup1 hsup2 hS1 hSne hEg1 hEg2 T RT
      eM hT1 hT2 hRT heM1 heM2 χ0 C cu hχ0 hsmall.1 hC hafford hcu)
    hsmall hu heta Xs Ys hXs hYs hpairM hlaw

end Finale

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
(`thm:composite-matching`): `composite_matching_le_final` with the rare
rows
folded into the nilpotent block at raw weight; no affordability and no
smallness hypotheses remain.  One binary-tree automorphism matches the
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
