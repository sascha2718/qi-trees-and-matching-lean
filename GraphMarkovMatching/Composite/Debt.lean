/-
The screen-debt discharge layer of the composite two-law programme
(`arbitrary_offspring_matching.tex`, `sec:composite`: the screen half of
the closed recursion `thm:engine`, the geometric bound on the invariant
vector `thm:geom`, and `thm:composite-matching`).

`Main` isolates the screen half of the composite ledger in the single
named hypothesis `ScreenDebtBound`: the restricted debt scalar stays
below `X * etaG` at every height.  This file carries out the discharge
programme for that hypothesis.

Unconditional layer:

* `cDict`: the dictionary from kernel letters to the formal grammar
  (`eq:composite-alphabet`): `none ↦ F`, `some (ord j) ↦ Z j`,
  `some (mark a b i) ↦ M a b i`;
* `cTame`, `cReach_cTame`: the reachability envelope: under the
  standing side pack every reachable ordinary letter is common and
  bounded by `N`, and every reachable marker carries bounded data;
* `cSpawn_cDict_mem_succ`: the kernel-to-grammar bridge: the dictionary
  sends one spawn step of the kernel into one successor step of the
  formal grammar with common support `S` and declared entrances `Egr`;
* `cReach_anchored` (`def:composite-anchored`, `thm:composite-anchor`):
  the anchoring certificate by construction: a letter reachable at
  level `n` is
  `Anchored` at depth `n`; `cAligned_screenAnchored` packages the joint
  certificate `ScreenAnchored` at the common depth for the aligned
  pairs of the restricted index of `Main`;
* `cGood`, `cGood_nilpotent` (`thm:composite-acyclic`,
  `eq:composite-nilpotent`): the good screens (anchored, zero-list
  nonempty, F-diagonal-free) and the nilpotence of any common transfer
  matrix supported on good common steps, through `ledger_nilpotent`;
* `cFarMass_le_two_etaG`, `cScr_base_cZ_source_eq_zero`,
  `cScr_base_cT_source_le`, `cScr_base_cT_source_tiltT_le`: the
  height-0 rows of the screen ledger (`thm:zero-interface`): frozen
  sources are alive against frozen and fresh members by reflexivity,
  fresh sources pay at most the far mass, respectively the far tilt,
  both at most `2 * etaG` under `μ(v0) ≥ 1/2`.

Conditional layer.  The assembled one-step screen row (the screen rows
`thm:screen-rows`, the routing of the descents of `Assembly` through
the Hall factorization into a finite common/priced matrix pair) is the
one remaining analytic input; it is isolated as the single named Prop
`ScreenLedgerInput`.  Everything after it is proved:

* `cX`, `cSmallness`: the geometric debt multiplier
  `cX C r cu = 2 (∑_{j<r} (2C)^j) cu` of `thm:geom` and the smallness
  condition `χ0 (2C)^r ≤ 1/2` on the priced entrance weight `χ0`, a
  device of this route with no counterpart in the paper; `C` and `r`
  play the roles of the row sum `C_W` and the rank `r` of
  `eq:composite-cardinals`;
* `screenDebtBound_holds` (`thm:geom` feeding the screen half of
  `thm:engine`): the coupled geometric closure: given the ledger input,
  the smallness condition, and the debt-closure inequality for the
  inhomogeneous row shape, the restricted debt
  stays below `cX C r cu * etaG` at every height, simultaneously with
  the ordinary closure, through `graftWeightedLedger_estimate`;
* `composite_failure_le_closed`, `composite_matching_le_closed`
  (`thm:composite-matching`): the headline theorems of `Main` with the
  screen-ledger bound discharged; the only remaining hypothesis beyond
  the standing packs is `ScreenLedgerInput`;
* `cSmallness_zero`, `cGoodE_nilpotent`: the merged-block layer:
  smallness is vacuous at price zero, and the nilpotence certificate
  extends to matrices supported on good source-entrance steps
  (`CommonStepES`), through `ledger_nilpotentES`; this feeds the merged
  ledger of `Step`, which carries the rare rows inside the nilpotent
  block at raw weight.
-/
import GraphMarkovMatching.Composite.Main
import GraphMarkovMatching.Composite.Ledger
import GraphMarkovMatching.Closure.Green

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type}

/-! ### The dictionary and the reachability envelope -/

/-- The dictionary from kernel letters to grammar letters
(`eq:composite-alphabet`): the fresh letter to `F`, an ordinary counter
to the forced letter, and a marker to the marker. -/
def cDict : Option CtrC → Letter
  | none => Letter.F
  | some (CtrC.ord j) => Letter.Z j
  | some (CtrC.mark a b i) => Letter.M a b i

@[simp] lemma cDict_none : cDict none = Letter.F := rfl

@[simp] lemma cDict_ord (j : ℕ) :
    cDict (some (CtrC.ord j)) = Letter.Z j := rfl

@[simp] lemma cDict_mark (a b i : ℕ) :
    cDict (some (CtrC.mark a b i)) = Letter.M a b i := rfl

/-- The reachability envelope of a side pack: ordinary letters are
common and bounded by `N`, markers carry bounded data. -/
def cTame (exc : ℕ → Option (ℕ × ℕ)) (N : ℕ) : Option CtrC → Prop
  | none => True
  | some (CtrC.ord j) => j ≤ N ∧ exc j = none
  | some (CtrC.mark a b _) => a ≤ N ∧ b ≤ N

/-- The components of a common bounded counter are tame. -/
lemma cTame_comps_ord (exc : ℕ → Option (ℕ × ℕ)) (N : ℕ)
    (hN : ∀ j, j ≤ N → exc j = none) {k : ℕ} (hk : k ≤ N)
    (hexc : exc k = none) :
    cTame exc N (cComp0 exc (CtrC.ord k))
      ∧ cTame exc N (cComp1 exc (CtrC.ord k)) := by
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

/-- The components of a bounded marker are tame. -/
lemma cTame_markComp (exc : ℕ → Option (ℕ × ℕ)) (N : ℕ)
    (hN : ∀ j, j ≤ N → exc j = none) {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N)
    (i : ℕ) :
    cTame exc N (markComp0 a b i) ∧ cTame exc N (markComp1 a b i) := by
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
      exact ⟨⟨ha, hb⟩, ⟨by omega, hN _ (by omega)⟩⟩

/-- One spawn step preserves tameness under the standing side pack. -/
lemma cTame_of_cSpawn (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (N : ℕ)
    (hN : ∀ j, j ≤ N → exc j = none)
    (hch : ∀ k, (ν k : ℝ≥0∞) ≠ 0 → exc k = none → k ≤ N)
    (hdeclB : ∀ k p, exc k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    {l m : Option CtrC} (hl : cTame exc N l) (hsp : cSpawn exc ν l m) :
    cTame exc N m := by
  cases l with
  | none =>
      obtain ⟨k, hk, hor⟩ := hsp
      rcases hexc : exc k with _ | p
      · have hcm := cTame_comps_ord exc N hN (hch k hk hexc) hexc
        rcases hor with rfl | rfl
        · exact hcm.1
        · exact hcm.2
      · obtain ⟨h1, h2⟩ := hdeclB k p hexc
        have hcm := cTame_markComp exc N hN h1 h2 0
        rcases hor with rfl | rfl
        · rw [cComp0_ord_some hexc]
          exact hcm.1
        · rw [cComp1_ord_some hexc]
          exact hcm.2
  | some c =>
      cases c with
      | ord j =>
          have hl' : j ≤ N ∧ exc j = none := hl
          have hcm := cTame_comps_ord exc N hN hl'.1 hl'.2
          rcases hsp with rfl | rfl
          · exact hcm.1
          · exact hcm.2
      | mark a b i =>
          have hl' : a ≤ N ∧ b ≤ N := hl
          have hcm := cTame_markComp exc N hN hl'.1 hl'.2 i
          rcases hsp with rfl | rfl
          · rw [cComp0_mark]
            exact hcm.1
          · rw [cComp1_mark]
            exact hcm.2

/-- Reachable letters are tame. -/
theorem cReach_cTame (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (N : ℕ)
    (hN : ∀ j, j ≤ N → exc j = none)
    (hch : ∀ k, (ν k : ℝ≥0∞) ≠ 0 → exc k = none → k ≤ N)
    (hdeclB : ∀ k p, exc k = some p → p.1 ≤ N ∧ p.2 ≤ N) :
    ∀ {n : ℕ} {l : Option CtrC}, cReach exc ν n l → cTame exc N l := by
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
      exact cTame_of_cSpawn exc ν N hN hch hdeclB (ih hl') hsp

/-! ### The kernel-to-grammar bridge -/

/-- The dictionary sends the components of a bounded marker into the
grammar successors of the marker letter. -/
lemma cDict_markComp_mem_succM (a b i : ℕ) :
    cDict (markComp0 a b i) ∈ succM a b i
      ∧ cDict (markComp1 a b i) ∈ succM a b i := by
  rcases Nat.lt_or_ge (val a i) 3 with h2 | h3
  · rw [markComp0, if_neg (by omega), if_neg (by omega),
      markComp1, if_neg (by omega), if_neg (by omega),
      succM_le_two (by omega)]
    exact ⟨by simp, by simp⟩
  · rcases Nat.lt_or_ge (val a i) 4 with h4 | h4
    · have h3' : val a i = 3 := by omega
      rw [markComp0, if_neg (by omega), if_pos h3',
        markComp1, if_neg (by omega), if_pos h3', succM_three h3']
      exact ⟨by simp, by simp⟩
    · rw [markComp0, if_pos h4, markComp1, if_pos h4, succM_of_ge h4]
      exact ⟨by simp, by simp⟩

/-- The dictionary sends the components of a common counter into the
grammar successors of the forced letter. -/
lemma cDict_comps_ord_mem_succZ {exc : ℕ → Option (ℕ × ℕ)} {k : ℕ}
    (hexc : exc k = none) :
    cDict (cComp0 exc (CtrC.ord k)) ∈ succZ k
      ∧ cDict (cComp1 exc (CtrC.ord k)) ∈ succZ k := by
  rw [cComp0_ord_none hexc, cComp1_ord_none hexc]
  rcases Nat.lt_or_ge k 3 with h2 | h3
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      succZ_le_two (by omega)]
    exact ⟨by simp, by simp⟩
  · rcases Nat.lt_or_ge k 4 with h4 | h4
    · have h3' : k = 3 := by omega
      subst h3'
      rw [if_neg (by omega), if_pos rfl, if_neg (by omega), succZ_three]
      exact ⟨by simp, by simp⟩
    · rw [if_pos h4, if_pos h4, succZ_of_ge h4]
      exact ⟨by simp, by simp⟩

/-- **The kernel-to-grammar bridge**: the dictionary sends one spawn
step of a tame letter into one successor step of the formal grammar,
where `S` is the charged common support and `Egr` the charged declared
pairs of the side. -/
theorem cSpawn_cDict_mem_succ
    (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (N : ℕ)
    (S : Finset ℕ) (Egr : Finset (ℕ × ℕ))
    (hS : ∀ k, k ∈ S ↔ ((ν k : ℝ≥0∞) ≠ 0 ∧ exc k = none))
    (hEgr : ∀ p, p ∈ Egr ↔ ∃ z, (ν z : ℝ≥0∞) ≠ 0 ∧ exc z = some p)
    {l m : Option CtrC} (hl : cTame exc N l) (hsp : cSpawn exc ν l m) :
    cDict m ∈ succ S Egr (cDict l) := by
  cases l with
  | none =>
      obtain ⟨k, hk, hor⟩ := hsp
      show cDict m ∈ succ S Egr Letter.F
      rw [succ_F]
      rcases hexc : exc k with _ | p
      · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨k, (hS k).mpr ⟨hk, hexc⟩, ?_⟩)
        have hcm := cDict_comps_ord_mem_succZ (exc := exc) hexc
        rcases hor with rfl | rfl
        · exact hcm.1
        · exact hcm.2
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨p, (hEgr p).mpr ⟨k, hk, hexc⟩, ?_⟩)
        have hcm := cDict_markComp_mem_succM p.1 p.2 0
        rcases hor with rfl | rfl
        · rw [cComp0_ord_some hexc]
          exact hcm.1
        · rw [cComp1_ord_some hexc]
          exact hcm.2
  | some c =>
      cases c with
      | ord j =>
          have hl' : j ≤ N ∧ exc j = none := hl
          have hcm := cDict_comps_ord_mem_succZ (exc := exc) hl'.2
          show cDict m ∈ succ S Egr (Letter.Z j)
          rw [succ_Z]
          rcases hsp with rfl | rfl
          · exact hcm.1
          · exact hcm.2
      | mark a b i =>
          have hcm := cDict_markComp_mem_succM a b i
          show cDict m ∈ succ S Egr (Letter.M a b i)
          rw [succ_M]
          rcases hsp with rfl | rfl
          · rw [cComp0_mark]
            exact hcm.1
          · rw [cComp1_mark]
            exact hcm.2

/-! ### Anchoring certificates by construction -/

/-- The charged declared pairs lie in the charged common support. -/
lemma cEgr_subset_support
    (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (N : ℕ)
    (S : Finset ℕ) (Egr : Finset (ℕ × ℕ))
    (hN : ∀ j, j ≤ N → exc j = none)
    (hdeclB : ∀ k p, exc k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (hdeclC : ∀ k p, exc k = some p → ν p.1 ≠ 0 ∧ ν p.2 ≠ 0)
    (hS : ∀ k, k ∈ S ↔ ((ν k : ℝ≥0∞) ≠ 0 ∧ exc k = none))
    (hEgr : ∀ p, p ∈ Egr ↔ ∃ z, (ν z : ℝ≥0∞) ≠ 0 ∧ exc z = some p) :
    ∀ p ∈ Egr, p.1 ∈ S ∧ p.2 ∈ S := by
  intro p hp
  obtain ⟨z, _, hzp⟩ := (hEgr p).mp hp
  obtain ⟨hb1, hb2⟩ := hdeclB z p hzp
  obtain ⟨hc1, hc2⟩ := hdeclC z p hzp
  exact ⟨(hS p.1).mpr ⟨hc1, hN p.1 hb1⟩, (hS p.2).mpr ⟨hc2, hN p.2 hb2⟩⟩

/-- **Anchoring by construction** (`def:composite-anchored`,
`thm:composite-anchor`): a letter reachable at level `n` of the index of
`Main` is anchored at depth `n` for the formal grammar of its side.
This is the anchoring certificate of the restricted debt index:
alignment at a common level is alignment at a common anchoring depth. -/
theorem cReach_anchored
    (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) (N : ℕ)
    (S : Finset ℕ) (Egr : Finset (ℕ × ℕ))
    (hN : ∀ j, j ≤ N → exc j = none)
    (hch : ∀ k, (ν k : ℝ≥0∞) ≠ 0 → exc k = none → k ≤ N)
    (hdeclB : ∀ k p, exc k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (hS : ∀ k, k ∈ S ↔ ((ν k : ℝ≥0∞) ≠ 0 ∧ exc k = none))
    (hEgr : ∀ p, p ∈ Egr ↔ ∃ z, (ν z : ℝ≥0∞) ≠ 0 ∧ exc z = some p)
    (hES : ∀ p ∈ Egr, p.1 ∈ S ∧ p.2 ∈ S) :
    ∀ {n : ℕ} {l : Option CtrC}, cReach exc ν n l →
      Anchored S Egr n (cDict l) := by
  intro n
  induction n with
  | zero =>
      intro l hl
      have hl' : l = none := hl
      subst hl'
      exact anchored_F_of_mem hES (zero_mem _)
  | succ n ih =>
      intro l hl
      obtain ⟨l', hl', hsp⟩ := hl
      exact (ih hl').step (cSpawn_cDict_mem_succ exc ν N S Egr hS hEgr
        (cReach_cTame exc ν N hN hch hdeclB hl') hsp)

/-- **The joint anchoring certificate for aligned screens**: a source
letter reachable at level `n` on side 1, against a zero list of
dictionary images of letters reachable at the same level `n` on side
2, forms a screen `ScreenAnchored` at the common depth `n`.  This is
the certificate `∃ δ, ScreenAnchored … δ` demanded by the good set of
`thm:composite-acyclic` for every tuple of the restricted debt index. -/
theorem cAligned_screenAnchored
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (N : ℕ)
    (S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ))
    (hN1 : ∀ j, j ≤ N → exc1 j = none)
    (hch1 : ∀ k, (ν1 k : ℝ≥0∞) ≠ 0 → exc1 k = none → k ≤ N)
    (hdeclB1 : ∀ k p, exc1 k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (hS1 : ∀ k, k ∈ S ↔ ((ν1 k : ℝ≥0∞) ≠ 0 ∧ exc1 k = none))
    (hEg1 : ∀ p, p ∈ E1 ↔ ∃ z, (ν1 z : ℝ≥0∞) ≠ 0 ∧ exc1 z = some p)
    (hES1 : ∀ p ∈ E1, p.1 ∈ S ∧ p.2 ∈ S)
    (hN2 : ∀ j, j ≤ N → exc2 j = none)
    (hch2 : ∀ k, (ν2 k : ℝ≥0∞) ≠ 0 → exc2 k = none → k ≤ N)
    (hdeclB2 : ∀ k p, exc2 k = some p → p.1 ≤ N ∧ p.2 ≤ N)
    (hS2 : ∀ k, k ∈ S ↔ ((ν2 k : ℝ≥0∞) ≠ 0 ∧ exc2 k = none))
    (hEg2 : ∀ p, p ∈ E2 ↔ ∃ z, (ν2 z : ℝ≥0∞) ≠ 0 ∧ exc2 z = some p)
    (hES2 : ∀ p ∈ E2, p.1 ∈ S ∧ p.2 ∈ S)
    {n : ℕ} {l1 : Option CtrC} (h1 : cReach exc1 ν1 n l1)
    {zl : Finset Letter}
    (hzl : ∀ t ∈ zl, ∃ l2, cReach exc2 ν2 n l2 ∧ t = cDict l2) :
    ScreenAnchored S E1 E2 n ⟨cDict l1, zl⟩ := by
  constructor
  · exact cReach_anchored exc1 ν1 N S E1 hN1 hch1 hdeclB1 hS1 hEg1
      hES1 h1
  · intro t ht
    obtain ⟨l2, h2, rfl⟩ := hzl t ht
    exact cReach_anchored exc2 ν2 N S E2 hN2 hch2 hdeclB2 hS2 hEg2
      hES2 h2

/-! ### Good screens and nilpotence of the common block -/

/-- The good screens of the composite ledger (`thm:composite-acyclic`):
anchored at some depth, zero-list nonempty, and F-diagonal-free.  The
tuples of the restricted debt index of `Main` are good: anchoring is
`cAligned_screenAnchored`, and the F-diagonal tuples are exactly zero
by the pruning `screenE_cT_opposite_eq_zero`, so they never need a
matrix row. -/
def cGood (S : Finset ℕ) (E1 E2 : Finset (ℕ × ℕ)) (s : Screen) : Prop :=
  (∃ δ, ScreenAnchored S E1 E2 δ s) ∧ s.zlist.Nonempty
    ∧ ¬(s.cell = Letter.F ∧ Letter.F ∈ s.zlist)

/-- **Nilpotence of the common block** (`eq:composite-nilpotent`): a
transfer matrix over a finite index of screens whose support consists
of good common steps is annihilated by `card ι` applications of
`mulVec`, through `ledger_nilpotent`. -/
theorem cGood_nilpotent (S : Finset ℕ) (hSne : S.Nonempty)
    (E1 E2 : Finset (ℕ × ℕ)) {ι : Type} [Fintype ι] (emb : ι → Screen)
    (Nmat : ι → ι → ℝ≥0∞)
    (hsupp : ∀ i j, Nmat i j ≠ 0 → CommonStep S E2 (emb i) (emb j)
      ∧ cGood S E1 E2 (emb i) ∧ cGood S E1 E2 (emb j)) :
    (mulVec Nmat)^[Fintype.card ι] (fun _ => 1) = fun _ => 0 := by
  have h := ledger_nilpotent S hSne E1 E2 (cGood S E1 E2)
    (fun s hs => hs.2.2) (fun s hs => hs.2.1) (fun s hs => hs.1)
    emb Nmat hsupp (fun _ => 1)
  have hbridge : matApply Nmat = mulVec Nmat := rfl
  rwa [hbridge] at h

/-! ### The height-0 rows of the screen ledger -/

section BaseRows

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)

private lemma screenInd_le_one' {X : Type} (R : X → X → Prop)
    (zs : List (PMF X)) (x : X) : screenInd R zs x ≤ 1 := by
  rw [screenInd]
  split_ifs <;> simp

private lemma screenE_mono_g {X : Type} (ρs : PMF X) (R : X → X → Prop)
    (zs : List (PMF X)) {g g' : X → ℝ≥0∞} (hg : ∀ x, g x ≤ g' x) :
    screenE ρs R zs g ≤ screenE ρs R zs g' := by
  rw [screenE, screenE]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul_right (hg x) _

/-- The frozen dead event at height 0 is the far-root event. -/
private lemma rE_cZ_zero_eq_zero_iff (c₂ : CtrC) (w : V) (c : CtrC) :
    rE (cZ exc2 μ ν2 v0 c₂ 0) (fullSim (cRel Rv) 0) (leaf (w, c)) = 0
      ↔ ¬ Rv w v0 := by
  constructor
  · intro h0 hr
    rw [rE] at h0
    have hterm := ENNReal.tsum_eq_zero.mp h0 (leaf ((v0 : V), c₂))
    rw [if_pos ((fullSim_leaf (cRel Rv) (w, c) ((v0 : V), c₂)).mpr hr),
      show cZ exc2 μ ν2 v0 c₂ 0 = PMF.pure (leaf ((v0 : V), c₂)) from rfl,
      PMF.pure_apply, if_pos rfl] at hterm
    exact one_ne_zero hterm
  · intro hr
    rw [rE]
    refine ENNReal.tsum_eq_zero.mpr fun y => ?_
    by_cases hy : fullSim (cRel Rv) 0 (leaf (w, c)) y
    · have hyne : y ≠ leaf ((v0 : V), c₂) := by
        intro hyb
        exact hr ((fullSim_leaf (cRel Rv) (w, c) ((v0 : V), c₂)).mp
          (hyb ▸ hy))
      rw [if_pos hy,
        show cZ exc2 μ ν2 v0 c₂ 0 = PMF.pure (leaf ((v0 : V), c₂)) from rfl,
        PMF.pure_apply, if_neg hyne]
    · rw [if_neg hy]

/-- **Height-0 rows, frozen source**: at height 0 a frozen source is
alive against every frozen and fresh member by reflexivity and the
root charge, so any screen whose zero list contains one vanishes, for
every normalization. -/
theorem cScr_base_cZ_source_eq_zero (hrefl0 : Rv v0 v0) (hμ0 : μ v0 ≠ 0)
    (c₁ : CtrC) {zs : List (PMF (FullLab (CState V) 0))}
    (hmem : (∃ c₂, cZ exc2 μ ν2 v0 c₂ 0 ∈ zs) ∨ cT exc2 μ ν2 v0 0 ∈ zs)
    (W : FullLab (CState V) 0 → ℝ≥0∞) :
    screenE (cZ exc1 μ ν1 v0 c₁ 0) (fullSim (cRel Rv) 0) zs W = 0 := by
  have hlive : ∃ ρ ∈ zs,
      rE ρ (fullSim (cRel Rv) 0) (leaf ((v0 : V), c₁)) ≠ 0 := by
    rcases hmem with ⟨c₂, hc₂⟩ | hT
    · refine ⟨cZ exc2 μ ν2 v0 c₂ 0, hc₂, ?_⟩
      intro h0
      exact ((rE_cZ_zero_eq_zero_iff Rv μ v0 exc2 ν2 c₂ v0 c₁).mp h0)
        hrefl0
    · refine ⟨cT exc2 μ ν2 v0 0, hT, ?_⟩
      rw [rE_cT_zero Rv exc2 μ ν2 v0 v0 c₁]
      exact rE_root_ne_zero Rv μ v0 hrefl0 hμ0
  obtain ⟨ρ, hρ, hne⟩ := hlive
  rw [screenE]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : x = leaf ((v0 : V), c₁)
  · subst hx
    rw [screenInd, if_neg (fun hall => hne (hall ρ hρ)), mul_zero,
      zero_mul]
  · rw [show cZ exc1 μ ν1 v0 c₁ 0 = PMF.pure (leaf ((v0 : V), c₁)) from
      rfl, PMF.pure_apply, if_neg hx, zero_mul, zero_mul]

/-- **Height-0 rows, fresh source, bounded normalization**: at height 0
a fresh-source screen with a frozen member and a normalization at most
one is dominated by the far mass. -/
theorem cScr_base_cT_source_le (c₂ : CtrC)
    {zs : List (PMF (FullLab (CState V) 0))}
    (hmem : cZ exc2 μ ν2 v0 c₂ 0 ∈ zs)
    {W : FullLab (CState V) 0 → ℝ≥0∞} (hW : ∀ x, W x ≤ 1)
    (FM : ℝ≥0∞)
    (hFM : (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞)) ≤ FM) :
    screenE (cT exc1 μ ν1 v0 0) (fullSim (cRel Rv) 0) zs W ≤ FM := by
  refine le_trans (screenE_mono_g _ _ _ hW) ?_
  refine le_trans (screenE_le_of_mem _ _ hmem _) ?_
  rw [← zMass_eq_screenE_unit]
  exact cZMass_base_TZ Rv μ v0 exc1 exc2 ν1 ν2 c₂ FM hFM

/-- The far mass is at most `2 * etaG` under `μ(v0) ≥ 1/2`
(`thm:zero-interface`). -/
theorem cFarMass_le_two_etaG (hα0 : 0 ≤ α)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0) :
    (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞)) ≤ 2 * etaG α Rv μ := by
  rw [farMass_eq_qE Rv μ v0 hsymm]
  exact qE_zero_le α Rv μ v0 hα0 hhalf

/-- **Height-0 rows, fresh source, fresh normalization**: at height 0 a
fresh-source screen with a frozen member and the fresh-normalization
tilt is dominated by the far tilt, hence by `2 * etaG` under
`μ(v0) ≥ 1/2` (`thm:zero-interface`). -/
theorem cScr_base_cT_source_tiltT_le (hα : 0 < α)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0)
    (c₂ : CtrC) {zs : List (PMF (FullLab (CState V) 0))}
    (hmem : cZ exc2 μ ν2 v0 c₂ 0 ∈ zs) :
    screenE (cT exc1 μ ν1 v0 0) (fullSim (cRel Rv) 0) zs
        (WresD α (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0))
      ≤ 2 * etaG α Rv μ := by
  refine le_trans (screenE_le_of_mem _ _ hmem _) ?_
  rw [screenE]
  have hassoc : ∀ x : FullLab (CState V) 0,
      cT exc1 μ ν1 v0 0 x
        * screenInd (fullSim (cRel Rv) 0) [cZ exc2 μ ν2 v0 c₂ 0] x
        * WresD α (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0) x
      = cT exc1 μ ν1 v0 0 x
        * (screenInd (fullSim (cRel Rv) 0) [cZ exc2 μ ν2 v0 c₂ 0] x
          * WresD α (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0) x) :=
    fun x => mul_assoc _ _ _
  rw [tsum_congr hassoc, cT_eq_freshQ_bind exc1 μ ν1 v0 0, tsum_bind_mul]
  have hpt : ∀ s : V × ℕ,
      freshQ μ ν1 s
        * ∑' x, muM (compK exc1 μ ν1 v0) (s.1, CtrC.ord s.2) 0 x
            * (screenInd (fullSim (cRel Rv) 0) [cZ exc2 μ ν2 v0 c₂ 0] x
              * WresD α (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0) x)
      ≤ (if Rv v0 s.1 then 0
          else (μ s.1 : ℝ≥0∞) * (rE μ Rv s.1) ^ (-α)) * ν1 s.2 := by
    rintro ⟨w, k⟩
    have hpure : (∑' x, muM (compK exc1 μ ν1 v0) (w, CtrC.ord k) 0 x
          * (screenInd (fullSim (cRel Rv) 0) [cZ exc2 μ ν2 v0 c₂ 0] x
            * WresD α (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0) x))
        = screenInd (fullSim (cRel Rv) 0) [cZ exc2 μ ν2 v0 c₂ 0]
            (leaf ((w : V), CtrC.ord k))
          * WresD α (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0)
              (leaf ((w : V), CtrC.ord k)) := by
      rw [show muM (compK exc1 μ ν1 v0) (w, CtrC.ord k) 0
          = PMF.pure (leaf ((w : V), CtrC.ord k)) from rfl]
      exact tsum_pure_mul _ _
    rw [hpure]
    by_cases hv : Rv v0 w
    · rw [if_pos hv, zero_mul]
      have hind : screenInd (fullSim (cRel Rv) 0)
          [cZ exc2 μ ν2 v0 c₂ 0] (leaf ((w : V), CtrC.ord k)) = 0 := by
        rw [screenInd, if_neg]
        intro hall
        exact ((rE_cZ_zero_eq_zero_iff Rv μ v0 exc2 ν2 c₂ w
            (CtrC.ord k)).mp
          (hall _ (List.mem_singleton_self _))) (hsymm v0 w hv)
      rw [hind, zero_mul, mul_zero]
    · rw [if_neg hv]
      have hW : WresD α (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0)
          (leaf ((w : V), CtrC.ord k)) ≤ (rE μ Rv w) ^ (-α) := by
        by_cases hr : rE (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0)
            (leaf ((w : V), CtrC.ord k)) = 0
        · rw [WresD, if_pos hr]
          exact zero_le
        · exact le_of_eq (by
            rw [← rE_rpow_neg_eq_WresD (cT exc2 μ ν2 v0 0)
                (fullSim (cRel Rv) 0) (leaf ((w : V), CtrC.ord k)) hr,
              rE_cT_zero Rv exc2 μ ν2 v0 w (CtrC.ord k)])
      calc freshQ μ ν1 (w, k)
            * (screenInd (fullSim (cRel Rv) 0) [cZ exc2 μ ν2 v0 c₂ 0]
                (leaf ((w : V), CtrC.ord k))
              * WresD α (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0)
                  (leaf ((w : V), CtrC.ord k)))
          ≤ freshQ μ ν1 (w, k) * (1 * (rE μ Rv w) ^ (-α)) :=
            mul_le_mul_right
              (mul_le_mul' (screenInd_le_one' _ _ _) hW) _
        _ = ((μ w : ℝ≥0∞) * (rE μ Rv w) ^ (-α)) * ν1 k := by
            rw [show freshQ μ ν1 (w, k) = μ w * ν1 k from rfl, one_mul]
            ring
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [tsum_prod_split
    (fun v => if Rv v0 v then 0 else (μ v : ℝ≥0∞) * (rE μ Rv v) ^ (-α))
    (fun l => (ν1 l : ℝ≥0∞)), ν1.tsum_coe, mul_one]
  exact far_tilt_le α Rv μ v0 hα hsymm hhalf

end BaseRows

/-! ### The geometric constants (`thm:geom`) and the entrance price -/

/-- The geometric debt multiplier
`cX C r cu = 2 (∑_{j<r} (2C)^j) · cu`, the output of `thm:geom` at
common row weight `C`, rank `r`, and base debt weight `cu`. -/
noncomputable def cX (C : ℝ≥0∞) (r : ℕ) (cu : ℝ≥0∞) : ℝ≥0∞ :=
  graftGreenMultiplier C r * cu

/-- The composite smallness condition on the priced entrance weight:
`χ0` is admissible and contracts the `r`-step common block of row weight
`C`.  It is a device of this route and has no counterpart in the paper;
the merged ledger of `Step` discharges it at price zero, so the headline
theorems carry no condition on the exceptional masses.  Here `C` and `r`
play the roles of the row sum `C_W` and the rank `r` of
`eq:composite-cardinals`. -/
def cSmallness (χ0 C : ℝ≥0∞) (r : ℕ) : Prop :=
  χ0 ≤ 1 ∧ χ0 * (2 * C) ^ r ≤ 2⁻¹

/-! ### The screen-ledger input and the discharge -/

/-- **The screen-ledger input** (the screen rows `thm:screen-rows` in
assembled finite-vector form): the one remaining analytic hypothesis of the
composite programme, and the single named Prop isolating it.

Its exact content: a finite ledger vector `E` over an index `ι` of
debt coordinates which

* dominates the restricted debt of `Main` at every height (`debt_le`);
* starts below `cu * etaG` (`base`; the height-0 rows
  `cScr_base_cZ_source_eq_zero`, `cScr_base_cT_source_le`,
  `cScr_base_cT_source_tiltT_le` and `cFarMass_le_two_etaG` bound the
  base coordinates by `0` and `2 * etaG`);
* satisfies the one-step screen row against a common/priced matrix
  pair `Nc + χ0 • Mp` (`step`), with an inhomogeneous shape
  `g (cPsi h) (⨆ E h)` monotone in both arguments (`g_mono`), both row
  sums bounded by `C` (`common_row`, `priced_row`), and the common
  block nilpotent in `r` steps (`common_nilpotent`; for the canonical
  matrix supported on good common steps this is `cGood_nilpotent`,
  with the anchoring certificates supplied by
  `cAligned_screenAnchored` and the F-diagonal coordinates pruned to
  zero by `screenE_cT_opposite_eq_zero`). -/
structure ScreenLedgerInput (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
    (v0 : V) (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    {ι : Type} [Fintype ι] (E : ℕ → ι → ℝ≥0∞)
    (Nc Mp : ι → ι → ℝ≥0∞) (g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (χ0 C : ℝ≥0∞) (r : ℕ) (cu : ℝ≥0∞) : Prop where
  debt_le : ∀ h, cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h ≤ ⨆ i, E h i
  g_mono : ∀ a a' b b', a ≤ a' → b ≤ b' → g a b ≤ g a' b'
  base : ∀ i, E 0 i ≤ cu * etaG α Rv μ
  common_row : ∀ i, ∑ j, Nc i j ≤ C
  priced_row : ∀ i, ∑ j, Mp i j ≤ C
  rank_pos : 0 < r
  common_nilpotent : (mulVec Nc)^[r] (fun _ => 1) = fun _ => 0
  step : ∀ h i, E (h + 1) i
    ≤ g (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) (⨆ j, E h j)
      + mulVecInf (rareMatrix Nc Mp χ0) (E h) i

/-- **Discharge of the screen-ledger bound** (`thm:geom` feeding the
screen half of `thm:engine`): the ledger input, the entrance-price
smallness condition `cSmallness`, and the debt-closure inequality for
the inhomogeneous shape `g` yield `ScreenDebtBound` at the geometric
multiplier `cX C r cu`, coupled to the ordinary closure of
`Main` through the invariant box of `graftWeightedLedger_estimate`. -/
theorem screenDebtBound_holds
    (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 : Finset ℕ)
    {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hrefl0 : Rv v0 v0) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hfin1 : ∀ k, ν1 k ≠ 0 → k ∈ K1)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hfin2 : ∀ k, ν2 k ≠ 0 → k ∈ K2)
    (T κ : ℝ≥0∞)
    (hT1 : cTiltSum α exc1 μ ν1 v0 ≤ T)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T)
    (hκ1 : (K1.card : ℝ≥0∞) ≤ κ) (hκ2 : (K2.card : ℝ≥0∞) ≤ κ)
    (hlam : cLamS δ L K < 1)
    {ι : Type} [Fintype ι] {E : ℕ → ι → ℝ≥0∞}
    {Nc Mp : ι → ι → ℝ≥0∞} {g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}
    {χ0 C : ℝ≥0∞} {r : ℕ} {cu : ℝ≥0∞}
    (hin : ScreenLedgerInput α Rv μ v0 exc1 exc2 ν1 ν2 E Nc Mp g
      χ0 C r cu)
    (hsmall : cSmallness χ0 C r)
    (hu : g (cKc δ L K μ v0 T κ (cX C r cu) * etaG α Rv μ)
        (cX C r cu * etaG α Rv μ) ≤ cu * etaG α Rv μ)
    (heta : etaG α Rv μ ≤ cEtaStar α δ L K μ v0 T κ (cX C r cu)) :
    ScreenDebtBound α Rv μ v0 exc1 exc2 ν1 ν2 (cX C r cu) := by
  obtain ⟨hχ1, hhalf⟩ := hsmall
  have hXi : graftGreenMultiplier C r * (cu * etaG α Rv μ)
      = cX C r cu * etaG α Rv μ := by
    rw [cX, mul_assoc]
  have hΨ0 : cPsi α Rv μ v0 exc1 exc2 ν1 ν2 0
      ≤ cKc δ L K μ v0 T κ (cX C r cu) * etaG α Rv μ := by
    refine le_trans (cPsi_base α Rv μ v0 exc1 exc2 ν1 ν2 hrefl0) ?_
    refine le_trans (cTheta0_le α Rv μ v0 hμ0) ?_
    exact mul_le_mul_left (cRootA_le_cKc δ L K μ v0 T κ (cX C r cu)) _
  have hΨstep : ∀ h, cPsi α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1)
      ≤ cStepF α δ L K (cRootA μ v0 * etaG α Rv μ) T κ
          (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h) (⨆ i, E h i) := by
    intro h
    refine le_trans (cPsi_step α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 hα hδ
      hL0 hL hK0 hK hrefl0 hsymm hμ0 hpair1 hdecl1 hfin1 hpair2 hdecl2
      hfin2 T κ hT1 hT2 hκ1 hκ2 h) ?_
    exact cStepF_mono α δ L K T κ (cTheta0_le α Rv μ v0 hμ0) le_rfl
      (hin.debt_le h)
  have hclose : cStepF α δ L K (cRootA μ v0 * etaG α Rv μ) T κ
      (cKc δ L K μ v0 T κ (cX C r cu) * etaG α Rv μ)
      (graftGreenMultiplier C r * (cu * etaG α Rv μ))
      ≤ cKc δ L K μ v0 T κ (cX C r cu) * etaG α Rv μ := by
    rw [hXi]
    exact cStepF_absorb α δ L K μ v0 T κ (cX C r cu) hlam heta
  have hu' : g (cKc δ L K μ v0 T κ (cX C r cu) * etaG α Rv μ)
      (graftGreenMultiplier C r * (cu * etaG α Rv μ))
      ≤ cu * etaG α Rv μ := by
    rw [hXi]
    exact hu
  have hmain := graftWeightedLedger_estimate Nc Mp χ0 C r hin.rank_pos
    hχ1 hin.common_row hin.priced_row hin.common_nilpotent hhalf
    (cKc δ L K μ v0 T κ (cX C r cu)) (etaG α Rv μ) (cu * etaG α Rv μ)
    (cPsi α Rv μ v0 exc1 exc2 ν1 ν2) E
    (fun a b => cStepF α δ L K (cRootA μ v0 * etaG α Rv μ) T κ a b) g
    (fun a a' b b' ha hb => cStepF_mono α δ L K T κ le_rfl ha hb)
    hin.g_mono hΨ0 hin.base hΨstep hin.step hu' hclose
  intro h
  refine le_trans (hin.debt_le h) ?_
  refine le_trans (iSup_le fun i => (hmain h).2 i) ?_
  rw [hXi]

/-! ### The closed headline theorems (`thm:composite-matching`) -/

/-- **Composite two-law mismatch bound, closed form**
(`thm:composite-matching`, finite heights): `composite_failure_le` with
the screen-ledger bound discharged through `screenDebtBound_holds`.  All
hypotheses are explicit; the debt multiplier is the geometric constant
`cX C r cu` of `thm:geom`, and the smallness condition is the
entrance-price condition `cSmallness`. -/
theorem composite_failure_le_closed
    (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 : Finset ℕ)
    {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hfin1 : ∀ k, ν1 k ≠ 0 → k ∈ K1)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hfin2 : ∀ k, ν2 k ≠ 0 → k ∈ K2)
    (N : ℕ)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (T κ : ℝ≥0∞)
    (hT1 : cTiltSum α exc1 μ ν1 v0 ≤ T)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T)
    (hκ1 : (K1.card : ℝ≥0∞) ≤ κ) (hκ2 : (K2.card : ℝ≥0∞) ≤ κ)
    (hlam : cLamS δ L K < 1)
    {ι : Type} [Fintype ι] {E : ℕ → ι → ℝ≥0∞}
    {Nc Mp : ι → ι → ℝ≥0∞} {g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}
    {χ0 C : ℝ≥0∞} {r : ℕ} {cu : ℝ≥0∞}
    (hin : ScreenLedgerInput α Rv μ v0 exc1 exc2 ν1 ν2 E Nc Mp g
      χ0 C r cu)
    (hsmall : cSmallness χ0 C r)
    (hu : g (cKc δ L K μ v0 T κ (cX C r cu) * etaG α Rv μ)
        (cX C r cu * etaG α Rv μ) ≤ cu * etaG α Rv μ)
    (heta : etaG α Rv μ ≤ cEtaStar α δ L K μ v0 T κ (cX C r cu)) :
    ∀ h, failureD (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
        (fullSim (cRel Rv) h)
      ≤ cKc δ L K μ v0 T κ (cX C r cu) * etaG α Rv μ :=
  composite_failure_le α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 hα hδ hL0 hL
    hK0 hK hrefl hsymm hμ0 hpair1 hdecl1 hfin1 hpair2 hdecl2 hfin2 N
    hN hdeclN hcharged T κ (cX C r cu) hT1 hT2 hκ1 hκ2 hlam
    (screenDebtBound_holds α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 hα hδ hL0
      hL hK0 hK (hrefl v0) hsymm hμ0 hpair1 hdecl1 hfin1 hpair2 hdecl2
      hfin2 T κ hT1 hT2 hκ1 hκ2 hlam hin hsmall hu heta) heta

/-- **Composite two-law infinite matching, closed form**
(`thm:composite-matching`): `composite_matching_le` with the
screen-ledger bound discharged through `screenDebtBound_holds`.  One
binary-tree automorphism matches the two infinite composite samples
with probability at least `1 - cKc * etaG`. -/
theorem composite_matching_le_closed {Omega : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Omega] (Pm : Measure Omega)
    [IsProbabilityMeasure Pm]
    (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (K1 K2 : Finset ℕ)
    {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hμ0 : μ v0 ≠ 0)
    (hpair1 : ∀ k p, exc1 k = some p → ∀ j, j ≤ p.1 → exc1 j = none)
    (hdecl1 : ∀ k p, exc1 k = some p → ν1 p.1 ≠ 0 ∧ ν1 p.2 ≠ 0)
    (hfin1 : ∀ k, ν1 k ≠ 0 → k ∈ K1)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hfin2 : ∀ k, ν2 k ≠ 0 → k ∈ K2)
    (N : ℕ)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hdeclN : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (T κ : ℝ≥0∞)
    (hT1 : cTiltSum α exc1 μ ν1 v0 ≤ T)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T)
    (hκ1 : (K1.card : ℝ≥0∞) ≤ κ) (hκ2 : (K2.card : ℝ≥0∞) ≤ κ)
    (hlam : cLamS δ L K < 1)
    {ι : Type} [Fintype ι] {E : ℕ → ι → ℝ≥0∞}
    {Nc Mp : ι → ι → ℝ≥0∞} {g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}
    {χ0 C : ℝ≥0∞} {r : ℕ} {cu : ℝ≥0∞}
    (hin : ScreenLedgerInput α Rv μ v0 exc1 exc2 ν1 ν2 E Nc Mp g
      χ0 C r cu)
    (hsmall : cSmallness χ0 C r)
    (hu : g (cKc δ L K μ v0 T κ (cX C r cu) * etaG α Rv μ)
        (cX C r cu * etaG α Rv μ) ≤ cu * etaG α Rv μ)
    (heta : etaG α Rv μ ≤ cEtaStar α δ L K μ v0 T κ (cX C r cu))
    (Xs Ys : (n : ℕ) → Omega → FullLab (CState V) n)
    (hXs : ∀ n omega, restrictLab n (Xs (n + 1) omega) = Xs n omega)
    (hYs : ∀ n omega, restrictLab n (Ys (n + 1) omega) = Ys n omega)
    (hpairM : ∀ n, Measurable (fun omega => (Xs n omega, Ys n omega)))
    (hlaw : ∀ n, Pm.map (fun omega => (Xs n omega, Ys n omega)) =
      (prodPMF (cT exc1 μ ν1 v0 n) (cT exc2 μ ν2 v0 n)).toMeasure) :
    1 - cKc δ L K μ v0 T κ (cX C r cu) * etaG α Rv μ
      ≤ Pm {omega | InfMatch (cRel Rv)
          (fun n => Xs n omega) (fun n => Ys n omega)} :=
  composite_matching_le α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 Pm hα hδ hL0
    hL hK0 hK hrefl hsymm hμ0 hpair1 hdecl1 hfin1 hpair2 hdecl2 hfin2
    N hN hdeclN hcharged T κ (cX C r cu) hT1 hT2 hκ1 hκ2 hlam
    (screenDebtBound_holds α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2 hα hδ hL0
      hL hK0 hK (hrefl v0) hsymm hμ0 hpair1 hdecl1 hfin1 hpair2 hdecl2
      hfin2 T κ hT1 hT2 hκ1 hκ2 hlam hin hsmall hu heta) heta
    Xs Ys hXs hYs hpairM hlaw

/-! ### The merged block: nilpotence with the rare rows folded in -/

/-- The entrance-price smallness condition holds vacuously at price
zero: the merged ledger carries its rare rows inside the nilpotent
block, so no smallness data remain. -/
lemma cSmallness_zero (C : ℝ≥0∞) (r : ℕ) : cSmallness 0 C r :=
  ⟨zero_le_one, by rw [zero_mul]; exact zero_le⟩

/-- **Nilpotence of the merged block** (`eq:composite-nilpotent`,
source-entrance form): a transfer matrix over a finite index of screens
whose support consists of good source-entrance steps is annihilated by
`card ι` applications of `mulVec`, through `ledger_nilpotentES`; the
membership of the source side's declared pairs in the common support is
discharged by `cEgr_subset_support` under the standing pack. -/
theorem cGoodE_nilpotent (S : Finset ℕ) (hSne : S.Nonempty)
    (E1 E2 : Finset (ℕ × ℕ)) (hES1 : ∀ p ∈ E1, p.1 ∈ S ∧ p.2 ∈ S)
    {ι : Type} [Fintype ι] (emb : ι → Screen)
    (Nmat : ι → ι → ℝ≥0∞)
    (hsupp : ∀ i j, Nmat i j ≠ 0 → CommonStepES S E1 E2 (emb i) (emb j)
      ∧ cGood S E1 E2 (emb i) ∧ cGood S E1 E2 (emb j)) :
    (mulVec Nmat)^[Fintype.card ι] (fun _ => 1) = fun _ => 0 := by
  have h := ledger_nilpotentES S hSne E1 E2 hES1 (cGood S E1 E2)
    (fun s hs => hs.2.2) (fun s hs => hs.2.1) (fun s hs => hs.1)
    emb Nmat hsupp (fun _ => 1)
  have hbridge : matApply Nmat = mulVec Nmat := rfl
  rwa [hbridge] at h

end Composite
end GraphMarkovMatching
