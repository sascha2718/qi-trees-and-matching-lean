/-
The composite two-law matching endpoint
(`arbitrary_offspring_matching.tex`, `thm:composite-matching`): the
running coordinates of the two-sided composite
ledger over the *reachable* letter index, the ordinary height recursion
assembled from restricted-hypothesis forms of the rows of `Assembly`,
the explicit closure constants, and the headline matching theorems.

The running index.  The suprema defining the ordinary scalar and the
debt scalar do not range over all letter tuples: phase-misaligned
screens (the two-law analogue of the unrestricted live 2-cycle of
`rem:phase-cycle`, e.g. an ord-2 cell against a fresh dead letter when
the common support forces even return depths) are not controlled by the
ledger and must not enter the debt.  The index used here is the
synchronized reachability index: `cSpawn` spawns the component letters
of a cell one level down (`cComp0`/`cComp1`, with the fresh letter
spawning the components of every charged mixture cell), `cReach n`
is the `n`-step spawn closure of the fresh seed, and every supremum
ranges over tuples of letters reachable *at a common level `n`* on
their respective sides.  Reachable-at-a-common-level is the anchoring
alignment of `def:composite-anchored`: `Debt.lean` certifies that a
level-`n`
reachable letter is `Anchored` at depth `n` for the formal grammar of
its side, so aligned tuples carry the anchoring certificates
(`∃ δ, ScreenAnchored … δ`) demanded by the acyclicity theorem.
Mirror-diagonal and fresh-in-source-diagonal screens are *left in* the
index: they vanish identically by the pruning of `Bridge` and
`ScreenDescent`, so excluding them would only add bookkeeping.

Delivered unconditionally:

* `cLetO`, `cSpawn`, `cReach`, `cReachO`: the oriented letter laws and
  the reachability index;
* `cPsi`, `cZeroDebt`, `cScrOneDebt`, `cScrTwoDebt`, `cDebt`: the
  running coordinates over the reachable index, in both orientations
  of the two side packs `(exc1, ν1)` and `(exc2, ν2)`;
* `cSquareR_le`, `cPairScreenR_tilt_le`, `cOneSidedR_le`, `cMixR_le`,
  `cRowR_ZZ`, `cRowR_ZT`, `cRowR_TZ`, `cRowR_TT`: the rows of
  `Assembly` re-derived with hypotheses quantified only over the
  spawned component tuples, so that one recursion step consumes only
  coordinates of the reachable index;
* `cPsi_base` (`thm:base`) and `cPsi_step` (`thm:psi-rows`): the
  height-0 bound and the one-step ordinary recursion
  `cPsi (h+1) ≤ cStepF … (cPsi h) (cDebt h)`;
* the closure constants `cRootA`, `cLamS`, `cQuadC`, `cLinB`, `cKc`,
  `cB2`, `cC2`, `cC3` and the threshold `cEtaStar` (the constants `K`
  and `eps` of `eq:composite-K-eps`), with the scalar absorption
  `cStepF_absorb` (the absorption computation of `thm:numeric`).

The screen half of the ledger (the screen rows `thm:screen-rows` with
their explicit common and priced matrices, and the nilpotence of the
common block through `ledger_nilpotent`) is not derived in this file; it
enters through the single named hypothesis `ScreenDebtBound`, the
invariant bound `eq:levels` of the closed recursion `thm:engine`: the
restricted debt scalar is at most `X * etaG` at every height.
`Debt.lean` reduces `ScreenDebtBound` to the assembled screen rows
through the geometric estimate `thm:geom`.

Conditional on `ScreenDebtBound`:

* `cPsi_le_of_debt` (`thm:engine`): `cPsi h ≤ cKc * etaG`
  at every height whenever `etaG ≤ cEtaStar`;
* `composite_failure_le` (`thm:composite-matching`, finite heights): the
  directed mismatch of the two composite fresh laws is at most
  `cKc * etaG` at every height, through
  `cFailure_le_PhiDres_of_support` and the fresh-fresh seed coordinate
  of `cPsi`;
* `composite_matching_le` (`thm:composite-matching`, the infinite
  endpoint):
  one binary-tree automorphism matches the two infinite composite
  samples with probability at least `1 - cKc * etaG`, through
  `cMatching_infinite_of_PhiDres`.
-/
import GraphMarkovMatching.Composite.Assembly

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

variable {V : Type}

section Coordinates

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ)

/-! ### The oriented letter laws -/

/-- The oriented letter law: orientation `false` reads a letter in the
side-1 pack, orientation `true` in the side-2 pack.  The target side of
an orientation `o` is the side `!o`. -/
noncomputable def cLetO :
    Bool → Option CtrC → (h : ℕ) → PMF (FullLab (CState V) h)
  | false => cLet exc1 μ ν1 v0
  | true => cLet exc2 μ ν2 v0

@[simp] lemma cLetO_false :
    cLetO μ v0 exc1 exc2 ν1 ν2 false = cLet exc1 μ ν1 v0 := rfl

@[simp] lemma cLetO_true :
    cLetO μ v0 exc1 exc2 ν1 ν2 true = cLet exc2 μ ν2 v0 := rfl

/-! ### The reachable letter index

The rows descend a letter of a side to the component letters of its
cell: a frozen letter spawns `cComp0`/`cComp1` of its counter, the
fresh letter spawns the components of every charged mixture cell.
`cReach n` is the `n`-step spawn closure of the fresh seed; the
running suprema below pair letters reachable at a *common* level,
which is exactly the phase alignment certified by the anchoring
machinery of `Anchor` (see `Debt.lean`). -/

/-- One spawn step of a side: the component letters of the cell of `l`.
The fresh letter spawns the components of every charged mixture
cell. -/
def cSpawn (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) :
    Option CtrC → Option CtrC → Prop
  | some c, m => m = cComp0 exc c ∨ m = cComp1 exc c
  | none, m => ∃ k, (ν k : ℝ≥0∞) ≠ 0 ∧
      (m = cComp0 exc (CtrC.ord k) ∨ m = cComp1 exc (CtrC.ord k))

@[simp] lemma cSpawn_some (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ)
    (c : CtrC) (m : Option CtrC) :
    cSpawn exc ν (some c) m ↔ (m = cComp0 exc c ∨ m = cComp1 exc c) :=
  Iff.rfl

@[simp] lemma cSpawn_none (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ)
    (m : Option CtrC) :
    cSpawn exc ν none m ↔ ∃ k, (ν k : ℝ≥0∞) ≠ 0 ∧
      (m = cComp0 exc (CtrC.ord k) ∨ m = cComp1 exc (CtrC.ord k)) :=
  Iff.rfl

/-- Level-`n` reachability of a letter from the fresh seed. -/
def cReach (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) :
    ℕ → Option CtrC → Prop
  | 0, l => l = none
  | n + 1, m => ∃ l, cReach exc ν n l ∧ cSpawn exc ν l m

lemma cReach_zero (exc : ℕ → Option (ℕ × ℕ)) (ν : PMF ℕ) :
    cReach exc ν 0 none := rfl

/-- Oriented reachability: orientation `false` reads the side-1 pack,
orientation `true` the side-2 pack. -/
def cReachO (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) :
    Bool → ℕ → Option CtrC → Prop
  | false => cReach exc1 ν1
  | true => cReach exc2 ν2

@[simp] lemma cReachO_false (n : ℕ) (l : Option CtrC) :
    cReachO exc1 exc2 ν1 ν2 false n l ↔ cReach exc1 ν1 n l := Iff.rfl

@[simp] lemma cReachO_true (n : ℕ) (l : Option CtrC) :
    cReachO exc1 exc2 ν1 ν2 true n l ↔ cReach exc2 ν2 n l := Iff.rfl

lemma cReachO_zero (o : Bool) :
    cReachO exc1 exc2 ν1 ν2 o 0 none := by
  cases o with
  | false => exact cReach_zero exc1 ν1
  | true => exact cReach_zero exc2 ν2

/-! ### The running coordinates -/

/-- The ordinary scalar of the composite ledger (the coordinate `Psi_h`
of `thm:engine`): the supremum of the restricted letter-pair
potentials over the pairs reachable at a common level, in both
orientations. -/
noncomputable def cPsi (h : ℕ) : ℝ≥0∞ :=
  ⨆ o : Bool, ⨆ n : ℕ, ⨆ l1 : Option CtrC, ⨆ l2 : Option CtrC,
    ⨆ _ : cReachO exc1 exc2 ν1 ν2 o n l1,
      ⨆ _ : cReachO exc1 exc2 ν1 ν2 (!o) n l2,
        PhiDres α (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h)
          (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h) (fullSim (cRel Rv) h)

/-- The zero-mass debt: the supremum of the letter-pair zero-interface
masses over the aligned reachable pairs, in both orientations. -/
noncomputable def cZeroDebt (h : ℕ) : ℝ≥0∞ :=
  ⨆ o : Bool, ⨆ n : ℕ, ⨆ l1 : Option CtrC, ⨆ l2 : Option CtrC,
    ⨆ _ : cReachO exc1 exc2 ν1 ν2 o n l1,
      ⨆ _ : cReachO exc1 exc2 ν1 ν2 (!o) n l2,
        zMass (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h)
          (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h) (fullSim (cRel Rv) h)

/-- The one-member screen debt: the supremum of the tilted singleton
letter screens over the aligned reachable triples, in both
orientations. -/
noncomputable def cScrOneDebt (h : ℕ) : ℝ≥0∞ :=
  ⨆ o : Bool, ⨆ n : ℕ, ⨆ l1 : Option CtrC, ⨆ l2 : Option CtrC,
    ⨆ l3 : Option CtrC,
      ⨆ _ : cReachO exc1 exc2 ν1 ν2 o n l1,
        ⨆ _ : cReachO exc1 exc2 ν1 ν2 (!o) n l2,
          ⨆ _ : cReachO exc1 exc2 ν1 ν2 (!o) n l3,
            screenE (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h)
              (fullSim (cRel Rv) h)
              [cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h]
              (WresD α (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l3 h)
                (fullSim (cRel Rv) h))

/-- The two-member screen debt: the supremum of the tilted two-member
letter screens over the aligned reachable tuples, in both
orientations. -/
noncomputable def cScrTwoDebt (h : ℕ) : ℝ≥0∞ :=
  ⨆ o : Bool, ⨆ n : ℕ, ⨆ l1 : Option CtrC, ⨆ l2 : Option CtrC,
    ⨆ l2' : Option CtrC, ⨆ l3 : Option CtrC,
      ⨆ _ : cReachO exc1 exc2 ν1 ν2 o n l1,
        ⨆ _ : cReachO exc1 exc2 ν1 ν2 (!o) n l2,
          ⨆ _ : cReachO exc1 exc2 ν1 ν2 (!o) n l2',
            ⨆ _ : cReachO exc1 exc2 ν1 ν2 (!o) n l3,
              screenE (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h)
                (fullSim (cRel Rv) h)
                [cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h,
                  cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2' h]
                (WresD α (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l3 h)
                  (fullSim (cRel Rv) h))

/-- The debt scalar of the composite ledger (the screen vector `E_h` of
`thm:engine`, here a single scalar): the join of the zero-mass and the
screen debts. -/
noncomputable def cDebt (h : ℕ) : ℝ≥0∞ :=
  cZeroDebt Rv μ v0 exc1 exc2 ν1 ν2 h
    ⊔ (cScrOneDebt α Rv μ v0 exc1 exc2 ν1 ν2 h
      ⊔ cScrTwoDebt α Rv μ v0 exc1 exc2 ν1 ν2 h)

/-! ### The coordinate injections -/

lemma le_cPsi (o : Bool) (n : ℕ) (l1 l2 : Option CtrC)
    (h1 : cReachO exc1 exc2 ν1 ν2 o n l1)
    (h2 : cReachO exc1 exc2 ν1 ν2 (!o) n l2) (h : ℕ) :
    PhiDres α (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h)
        (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h) (fullSim (cRel Rv) h)
      ≤ cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h := by
  rw [cPsi]
  exact le_iSup_of_le o (le_iSup_of_le n (le_iSup_of_le l1
    (le_iSup_of_le l2 (le_iSup_of_le h1 (le_iSup_of_le h2 le_rfl)))))

lemma zMass_le_cDebt (o : Bool) (n : ℕ) (l1 l2 : Option CtrC)
    (h1 : cReachO exc1 exc2 ν1 ν2 o n l1)
    (h2 : cReachO exc1 exc2 ν1 ν2 (!o) n l2) (h : ℕ) :
    zMass (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h)
        (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h) (fullSim (cRel Rv) h)
      ≤ cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h := by
  rw [cDebt]
  refine le_trans ?_ le_sup_left
  rw [cZeroDebt]
  exact le_iSup_of_le o (le_iSup_of_le n (le_iSup_of_le l1
    (le_iSup_of_le l2 (le_iSup_of_le h1 (le_iSup_of_le h2 le_rfl)))))

lemma scrOne_le_cDebt (o : Bool) (n : ℕ) (l1 l2 l3 : Option CtrC)
    (h1 : cReachO exc1 exc2 ν1 ν2 o n l1)
    (h2 : cReachO exc1 exc2 ν1 ν2 (!o) n l2)
    (h3 : cReachO exc1 exc2 ν1 ν2 (!o) n l3) (h : ℕ) :
    screenE (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h) (fullSim (cRel Rv) h)
        [cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h]
        (WresD α (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l3 h)
          (fullSim (cRel Rv) h))
      ≤ cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h := by
  rw [cDebt]
  refine le_trans ?_ (le_trans le_sup_left le_sup_right)
  rw [cScrOneDebt]
  exact le_iSup_of_le o (le_iSup_of_le n (le_iSup_of_le l1
    (le_iSup_of_le l2 (le_iSup_of_le l3 (le_iSup_of_le h1
      (le_iSup_of_le h2 (le_iSup_of_le h3 le_rfl)))))))

lemma scrTwo_le_cDebt (o : Bool) (n : ℕ) (l1 l2 l2' l3 : Option CtrC)
    (h1 : cReachO exc1 exc2 ν1 ν2 o n l1)
    (h2 : cReachO exc1 exc2 ν1 ν2 (!o) n l2)
    (h2' : cReachO exc1 exc2 ν1 ν2 (!o) n l2')
    (h3 : cReachO exc1 exc2 ν1 ν2 (!o) n l3) (h : ℕ) :
    screenE (cLetO μ v0 exc1 exc2 ν1 ν2 o l1 h) (fullSim (cRel Rv) h)
        [cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2 h,
          cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l2' h]
        (WresD α (cLetO μ v0 exc1 exc2 ν1 ν2 (!o) l3 h)
          (fullSim (cRel Rv) h))
      ≤ cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h := by
  rw [cDebt]
  refine le_trans ?_ (le_trans le_sup_right le_sup_right)
  rw [cScrTwoDebt]
  exact le_iSup_of_le o (le_iSup_of_le n (le_iSup_of_le l1
    (le_iSup_of_le l2 (le_iSup_of_le l2' (le_iSup_of_le l3
      (le_iSup_of_le h1 (le_iSup_of_le h2
        (le_iSup_of_le h2' (le_iSup_of_le h3 le_rfl)))))))))

/-! ### The ordinary step function -/

/-- The ordinary step function of the composite ledger (the step
function `f` of `def:step-functions`): the root injection, one square
cell with its
priced one-sided tilt mass, and the quadratic cross term.  The
parameter `κ` dominates both support cardinalities, `T` both composite
tilt sums. -/
noncomputable def cStepF (α δ L K : ℝ) (θ0 T κ a b : ℝ≥0∞) : ℝ≥0∞ :=
  θ0 + (cellCB α δ L K a b b
      + T * (κ * (4 * b * (1 + ENNReal.ofReal α * a) + 4 * (b * b))))
    + ENNReal.ofReal (2 * α)
      * (θ0 * (cellCB α δ L K a b b
        + T * (κ * (4 * b * (1 + ENNReal.ofReal α * a) + 4 * (b * b)))))

/-- The step function is monotone in the root charge, the ordinary
argument, and the debt argument. -/
lemma cStepF_mono (α δ L K : ℝ) (T κ : ℝ≥0∞) {θ0 θ0' a a' b b' : ℝ≥0∞}
    (hθ : θ0 ≤ θ0') (ha : a ≤ a') (hb : b ≤ b') :
    cStepF α δ L K θ0 T κ a b ≤ cStepF α δ L K θ0' T κ a' b' := by
  have hmid : cellCB α δ L K a b b
        + T * (κ * (4 * b * (1 + ENNReal.ofReal α * a) + 4 * (b * b)))
      ≤ cellCB α δ L K a' b' b'
        + T * (κ * (4 * b' * (1 + ENNReal.ofReal α * a') + 4 * (b' * b'))) := by
    refine add_le_add (cellCB_mono α δ L K ha hb hb) ?_
    refine mul_le_mul_right (mul_le_mul_right (add_le_add ?_ ?_) κ) T
    · exact mul_le_mul' (mul_le_mul_right hb 4)
        (add_le_add le_rfl (mul_le_mul_right ha _))
    · exact mul_le_mul_right (mul_le_mul' hb hb) 4
  simp only [cStepF]
  exact add_le_add (add_le_add hθ hmid)
    (mul_le_mul_right (mul_le_mul' hθ hmid) _)

/-- The priced one-sided mass of a row is dominated by the step
function's one-sided term. -/
lemma osb_le_cStepF_term (α : ℝ) {T' T κ : ℝ≥0∞} (n : ℕ)
    (hT : T' ≤ T) (hn : (n : ℝ≥0∞) ≤ κ) (M D : ℝ≥0∞) :
    oneSidedBound α T' n M D
      ≤ T * (κ * (4 * D * (1 + ENNReal.ofReal α * M) + 4 * (D * D))) := by
  rw [oneSidedBound]
  exact mul_le_mul' hT (mul_le_mul_left hn _)

/-- The square-cell output of a row is dominated by the step
function. -/
lemma cell_le_cStepF (α δ L K : ℝ) (θ0 T κ M D : ℝ≥0∞) :
    cellCB α δ L K M D D ≤ cStepF α δ L K θ0 T κ M D := by
  simp only [cStepF]
  calc cellCB α δ L K M D D
      ≤ cellCB α δ L K M D D
        + T * (κ * (4 * D * (1 + ENNReal.ofReal α * M) + 4 * (D * D))) :=
        le_self_add
    _ ≤ θ0 + (cellCB α δ L K M D D
        + T * (κ * (4 * D * (1 + ENNReal.ofReal α * M) + 4 * (D * D)))) :=
        le_add_self
    _ ≤ θ0 + (cellCB α δ L K M D D
        + T * (κ * (4 * D * (1 + ENNReal.ofReal α * M) + 4 * (D * D))))
        + ENNReal.ofReal (2 * α)
          * (θ0 * (cellCB α δ L K M D D
            + T * (κ * (4 * D * (1 + ENNReal.ofReal α * M)
              + 4 * (D * D))))) := le_self_add

/-- The three-term output of a fresh-target row is dominated by the
step function. -/
lemma row_le_cStepF (α δ L K : ℝ) {θ0 θ' T κ M D osb : ℝ≥0∞}
    (hθ : θ' ≤ θ0)
    (hosb : osb
      ≤ T * (κ * (4 * D * (1 + ENNReal.ofReal α * M) + 4 * (D * D)))) :
    θ' + (cellCB α δ L K M D D + osb)
      + ENNReal.ofReal (2 * α) * (θ' * (cellCB α δ L K M D D + osb))
    ≤ cStepF α δ L K θ0 T κ M D := by
  have hmid : cellCB α δ L K M D D + osb
      ≤ cellCB α δ L K M D D
        + T * (κ * (4 * D * (1 + ENNReal.ofReal α * M) + 4 * (D * D))) :=
    add_le_add le_rfl hosb
  simp only [cStepF]
  exact add_le_add (add_le_add hθ hmid)
    (mul_le_mul_right (mul_le_mul' hθ hmid) _)

/-! ### Restricted-hypothesis helpers -/

/-- A PMF average of a family bounded on the charged support is
bounded. -/
private lemma tsum_pmf_mul_le_charged {w : PMF ℕ} {g : ℕ → ℝ≥0∞}
    {C : ℝ≥0∞} (hg : ∀ k, (w k : ℝ≥0∞) ≠ 0 → g k ≤ C) :
    (∑' k, w k * g k) ≤ C := by
  calc ∑' k, w k * g k
      ≤ ∑' k, w k * C := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        by_cases hk : (w k : ℝ≥0∞) = 0
        · rw [hk, zero_mul, zero_mul]
        · exact mul_le_mul_right (hg k hk) _
    _ = (∑' k, (w k : ℝ≥0∞)) * C := ENNReal.tsum_mul_right
    _ = C := by rw [w.tsum_coe, one_mul]

/-! ### The restricted rows

`Assembly` states its rows with letter bounds quantified over all
letters; the versions below demand the bounds only at the spawned
component tuples, so that the ordinary step consumes only coordinates
of the reachable index (`thm:composite-ledger` at the reachable
index). -/

/-- **The composite square cell, restricted hypotheses**: the
restricted square coordinate of two composite cells is bounded by
`cellCB` from the letter-pair ordinary bounds, reversed zero masses,
and tilted letter screens, demanded only at the component letters of
the two cells. -/
theorem cSquareR_le {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (c₁ c₂ : CtrC) (h : ℕ)
    (M Z E' : ℝ≥0∞)
    (hM : ∀ m1 m2 : Option CtrC, cSpawn exc1 ν1 (some c₁) m1 →
      cSpawn exc2 ν2 (some c₂) m2 →
      PhiDres α (cLet exc1 μ ν1 v0 m1 h) (cLet exc2 μ ν2 v0 m2 h)
          (fullSim (cRel Rv) h) ≤ M
        ∧ PhiDres α (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
            (fullSim (cRel Rv) h) ≤ M)
    (hZ : ∀ m1 m2 : Option CtrC, cSpawn exc1 ν1 (some c₁) m1 →
      cSpawn exc2 ν2 (some c₂) m2 →
      zMass (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
        (fullSim (cRel Rv) h) ≤ Z)
    (hE1 : ∀ m1 m2 m3 : Option CtrC, cSpawn exc1 ν1 (some c₁) m1 →
      cSpawn exc2 ν2 (some c₂) m2 → cSpawn exc2 ν2 (some c₂) m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 m2 h]
        (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h)) ≤ E') :
    PhiDres α (cXi exc1 μ ν1 v0 c₁ h) (cXi exc2 μ ν2 v0 c₂ h)
        (SquareRel (fullSim (cRel Rv) h))
      ≤ cellCB α δ L K M Z E' := by
  rw [cXi_eq_prod exc1 μ ν1 v0 c₁ h, cXi_eq_prod exc2 μ ν2 v0 c₂ h]
  refine le_trans (PhiDres_square_le hα hδ hL0 hL hK0 hK
    (cLet exc1 μ ν1 v0 (cComp0 exc1 c₁) h)
    (cLet exc1 μ ν1 v0 (cComp1 exc1 c₁) h)
    (cLet exc2 μ ν2 v0 (cComp0 exc2 c₂) h)
    (cLet exc2 μ ν2 v0 (cComp1 exc2 c₂) h)
    (fullSim (cRel Rv) h)
    (fullSim_symm (cRel Rv) (fun a b hab => hsymm a.1 b.1 hab) h) M Z
    (hM (cComp0 exc1 c₁) (cComp0 exc2 c₂) (Or.inl rfl) (Or.inl rfl)).1
    (hM (cComp0 exc1 c₁) (cComp1 exc2 c₂) (Or.inl rfl) (Or.inr rfl)).1
    (hM (cComp1 exc1 c₁) (cComp0 exc2 c₂) (Or.inr rfl) (Or.inl rfl)).1
    (hM (cComp1 exc1 c₁) (cComp1 exc2 c₂) (Or.inr rfl) (Or.inr rfl)).1
    (hM (cComp0 exc1 c₁) (cComp0 exc2 c₂) (Or.inl rfl) (Or.inl rfl)).2
    (hM (cComp1 exc1 c₁) (cComp0 exc2 c₂) (Or.inr rfl) (Or.inl rfl)).2
    (hM (cComp0 exc1 c₁) (cComp1 exc2 c₂) (Or.inl rfl) (Or.inr rfl)).2
    (hM (cComp1 exc1 c₁) (cComp1 exc2 c₂) (Or.inr rfl) (Or.inr rfl)).2
    (hZ (cComp0 exc1 c₁) (cComp0 exc2 c₂) (Or.inl rfl) (Or.inl rfl))
    (hZ (cComp1 exc1 c₁) (cComp0 exc2 c₂) (Or.inr rfl) (Or.inl rfl))
    (hZ (cComp0 exc1 c₁) (cComp1 exc2 c₂) (Or.inl rfl) (Or.inr rfl))
    (hZ (cComp1 exc1 c₁) (cComp1 exc2 c₂) (Or.inr rfl) (Or.inr rfl))) ?_
  rw [cellCB]
  refine add_le_add le_rfl ?_
  refine le_trans (mul_le_mul_left (add_le_add (add_le_add (add_le_add
    (hE1 (cComp0 exc1 c₁) (cComp0 exc2 c₂) (cComp1 exc2 c₂)
      (Or.inl rfl) (Or.inl rfl) (Or.inr rfl))
    (hE1 (cComp0 exc1 c₁) (cComp1 exc2 c₂) (cComp0 exc2 c₂)
      (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)))
    (hE1 (cComp1 exc1 c₁) (cComp0 exc2 c₂) (cComp1 exc2 c₂)
      (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)))
    (hE1 (cComp1 exc1 c₁) (cComp1 exc2 c₂) (cComp0 exc2 c₂)
      (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)))
    (1 + ENNReal.ofReal α * M)) (le_of_eq (by ring))

/-- **The tilted pair-screen cell, restricted hypotheses**: the Hall
factorization of a pair-level cell screen through the survivor split,
with the letter bounds demanded only at the component letters of the
three cells involved. -/
theorem cPairScreenR_tilt_le (hα : 1 ≤ α) (c₁ c₂ c₃ : CtrC) (h : ℕ)
    (M E' : ℝ≥0∞)
    (hM1 : ∀ m1 m3 : Option CtrC, cSpawn exc1 ν1 (some c₁) m1 →
      cSpawn exc2 ν2 (some c₃) m3 →
      PhiDres α (cLet exc1 μ ν1 v0 m1 h) (cLet exc2 μ ν2 v0 m3 h)
        (fullSim (cRel Rv) h) ≤ M)
    (hE1 : ∀ m1 m2 m3 : Option CtrC, cSpawn exc1 ν1 (some c₁) m1 →
      cSpawn exc2 ν2 (some c₂) m2 → cSpawn exc2 ν2 (some c₃) m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 m2 h]
        (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h)) ≤ E')
    (hE2 : ∀ m1 m3 : Option CtrC, cSpawn exc1 ν1 (some c₁) m1 →
      cSpawn exc2 ν2 (some c₃) m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 (cComp0 exc2 c₂) h,
          cLet exc2 μ ν2 v0 (cComp1 exc2 c₂) h]
        (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h)) ≤ E') :
    screenE (cXi exc1 μ ν1 v0 c₁ h) (SquareRel (fullSim (cRel Rv) h))
        [cXi exc2 μ ν2 v0 c₂ h]
        (WresD α (cXi exc2 μ ν2 v0 c₃ h)
          (SquareRel (fullSim (cRel Rv) h)))
      ≤ cCellBound α M E' := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hmomW : ∀ m1 m3 : Option CtrC, cSpawn exc1 ν1 (some c₁) m1 →
      cSpawn exc2 ν2 (some c₃) m3 →
      (∑' x, cLet exc1 μ ν1 v0 m1 h x
        * WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h) x)
      ≤ 1 + ENNReal.ofReal α * M := fun m1 m3 hm1 hm3 =>
    le_trans (tsum_WresD_le hα _ _ _)
      (add_le_add le_rfl (mul_le_mul_right (hM1 m1 m3 hm1 hm3) _))
  rw [screenE_singleton, cXi_eq_prod exc1 μ ν1 v0 c₁ h,
    cXi_eq_prod exc2 μ ν2 v0 c₂ h, cXi_eq_prod exc2 μ ν2 v0 c₃ h]
  set ρa := cLet exc1 μ ν1 v0 (cComp0 exc1 c₁) h with hρa
  set ρb := cLet exc1 μ ν1 v0 (cComp1 exc1 c₁) h with hρb
  set ρc := cLet exc2 μ ν2 v0 (cComp0 exc2 c₂) h with hρc
  set ρd := cLet exc2 μ ν2 v0 (cComp1 exc2 c₂) h with hρd
  set ρe := cLet exc2 μ ν2 v0 (cComp0 exc2 c₃) h with hρe
  set ρf := cLet exc2 μ ν2 v0 (cComp1 exc2 c₃) h with hρf
  have hsplit := tsum_ind_split (prodPMF ρa ρb)
    (fun xp => if rE (prodPMF ρc ρd)
        (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
    (WresD α (prodPMF ρe ρf) (SquareRel (fullSim (cRel Rv) h)))
    (fun xp => WresD α ρe (fullSim (cRel Rv) h) xp.1
      * WresD α ρf (fullSim (cRel Rv) h) xp.2)
    (fun xp => WresD α ρf (fullSim (cRel Rv) h) xp.1
      * WresD α ρe (fullSim (cRel Rv) h) xp.2)
    (fun xp => WresD_square_le_sum hα0 ρe ρf (fullSim (cRel Rv) h) xp)
  refine le_trans hsplit ?_
  have horder1 : (∑' xp : FullLab (CState V) h × FullLab (CState V) h,
      prodPMF ρa ρb xp
        * ((if rE (prodPMF ρc ρd)
              (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * (WresD α ρe (fullSim (cRel Rv) h) xp.1
            * WresD α ρf (fullSim (cRel Rv) h) xp.2)))
      ≤ E' * (1 + ENNReal.ofReal α * M)
        + (1 + ENNReal.ofReal α * M) * E' + E' * E' + E' * E' := by
    refine le_trans (deadScreen_factorize ρa ρb ρc ρd
      (fullSim (cRel Rv) h) (WresD α ρe (fullSim (cRel Rv) h))
      (WresD α ρf (fullSim (cRel Rv) h))) ?_
    exact add_le_add (add_le_add (add_le_add
      (mul_le_mul' (hE2 (cComp0 exc1 c₁) (cComp0 exc2 c₃)
          (Or.inl rfl) (Or.inl rfl))
        (hmomW (cComp1 exc1 c₁) (cComp1 exc2 c₃)
          (Or.inr rfl) (Or.inr rfl)))
      (mul_le_mul' (hmomW (cComp0 exc1 c₁) (cComp0 exc2 c₃)
          (Or.inl rfl) (Or.inl rfl))
        (hE2 (cComp1 exc1 c₁) (cComp1 exc2 c₃)
          (Or.inr rfl) (Or.inr rfl))))
      (mul_le_mul' (hE1 (cComp0 exc1 c₁) (cComp0 exc2 c₂)
          (cComp0 exc2 c₃) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl))
        (hE1 (cComp1 exc1 c₁) (cComp0 exc2 c₂) (cComp1 exc2 c₃)
          (Or.inr rfl) (Or.inl rfl) (Or.inr rfl))))
      (mul_le_mul' (hE1 (cComp0 exc1 c₁) (cComp1 exc2 c₂)
          (cComp0 exc2 c₃) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl))
        (hE1 (cComp1 exc1 c₁) (cComp1 exc2 c₂) (cComp1 exc2 c₃)
          (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)))
  have horder2 : (∑' xp : FullLab (CState V) h × FullLab (CState V) h,
      prodPMF ρa ρb xp
        * ((if rE (prodPMF ρc ρd)
              (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * (WresD α ρf (fullSim (cRel Rv) h) xp.1
            * WresD α ρe (fullSim (cRel Rv) h) xp.2)))
      ≤ E' * (1 + ENNReal.ofReal α * M)
        + (1 + ENNReal.ofReal α * M) * E' + E' * E' + E' * E' := by
    refine le_trans (deadScreen_factorize ρa ρb ρc ρd
      (fullSim (cRel Rv) h) (WresD α ρf (fullSim (cRel Rv) h))
      (WresD α ρe (fullSim (cRel Rv) h))) ?_
    exact add_le_add (add_le_add (add_le_add
      (mul_le_mul' (hE2 (cComp0 exc1 c₁) (cComp1 exc2 c₃)
          (Or.inl rfl) (Or.inr rfl))
        (hmomW (cComp1 exc1 c₁) (cComp0 exc2 c₃)
          (Or.inr rfl) (Or.inl rfl)))
      (mul_le_mul' (hmomW (cComp0 exc1 c₁) (cComp1 exc2 c₃)
          (Or.inl rfl) (Or.inr rfl))
        (hE2 (cComp1 exc1 c₁) (cComp0 exc2 c₃)
          (Or.inr rfl) (Or.inl rfl))))
      (mul_le_mul' (hE1 (cComp0 exc1 c₁) (cComp0 exc2 c₂)
          (cComp1 exc2 c₃) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl))
        (hE1 (cComp1 exc1 c₁) (cComp0 exc2 c₂) (cComp0 exc2 c₃)
          (Or.inr rfl) (Or.inl rfl) (Or.inl rfl))))
      (mul_le_mul' (hE1 (cComp0 exc1 c₁) (cComp1 exc2 c₂)
          (cComp1 exc2 c₃) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl))
        (hE1 (cComp1 exc1 c₁) (cComp1 exc2 c₂) (cComp0 exc2 c₃)
          (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)))
  refine le_trans (add_le_add horder1 horder2) (le_of_eq ?_)
  rw [cCellBound]
  ring

/-- **The priced one-sided tilt mass, restricted hypotheses**
(`thm:mixture-tilt-composite` inside the row assembly): the letter
bounds are
demanded only at the components of the source cell and of the charged
target mixture cells. -/
theorem cOneSidedR_le (hα : 1 ≤ α) (hμ0 : μ v0 ≠ 0)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hfin2 : ∀ k, ν2 k ≠ 0 → k ∈ K2)
    (c₁ : CtrC) (h : ℕ) (M E' T2 : ℝ≥0∞)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T2)
    (hM1 : ∀ m1 m3 : Option CtrC, cSpawn exc1 ν1 (some c₁) m1 →
      cSpawn exc2 ν2 none m3 →
      PhiDres α (cLet exc1 μ ν1 v0 m1 h) (cLet exc2 μ ν2 v0 m3 h)
        (fullSim (cRel Rv) h) ≤ M)
    (hE1 : ∀ m1 m2 m3 : Option CtrC, cSpawn exc1 ν1 (some c₁) m1 →
      cSpawn exc2 ν2 none m2 → cSpawn exc2 ν2 none m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 m2 h]
        (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h)) ≤ E')
    (hE2 : ∀ (m1 : Option CtrC) (j : ℕ) (m3 : Option CtrC),
      cSpawn exc1 ν1 (some c₁) m1 → (ν2 j : ℝ≥0∞) ≠ 0 →
      cSpawn exc2 ν2 none m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 (cComp0 exc2 (CtrC.ord j)) h,
          cLet exc2 μ ν2 v0 (cComp1 exc2 (CtrC.ord j)) h]
        (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h)) ≤ E') :
    ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if ∃ j, ν2 j ≠ 0 ∧ rE (cXi exc2 μ ν2 v0 (CtrC.ord j) h)
              (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (cXiBar exc2 μ ν2 v0 h)
              (SquareRel (fullSim (cRel Rv) h)) xp)
      ≤ oneSidedBound α T2 K2.card M E' := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hTj : ∀ j : ℕ, (ν2 j : ℝ≥0∞) ≠ 0 →
      (∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if ν2 j ≠ 0 ∧ rE (cXi exc2 μ ν2 v0 (CtrC.ord j) h)
              (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (cXiBar exc2 μ ν2 v0 h)
              (SquareRel (fullSim (cRel Rv) h)) xp))
      ≤ T2 * cCellBound α M E' := by
    intro j hj
    have h1 : (∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if ν2 j ≠ 0 ∧ rE (cXi exc2 μ ν2 v0 (CtrC.ord j) h)
              (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (cXiBar exc2 μ ν2 v0 h)
              (SquareRel (fullSim (cRel Rv) h)) xp))
        ≤ screenE (cXi exc1 μ ν1 v0 c₁ h)
            (SquareRel (fullSim (cRel Rv) h))
            [cXi exc2 μ ν2 v0 (CtrC.ord j) h]
            (WresD α (cXiBar exc2 μ ν2 v0 h)
              (SquareRel (fullSim (cRel Rv) h))) := by
      rw [screenE_singleton]
      refine ENNReal.tsum_le_tsum fun xp => ?_
      refine mul_le_mul_right (mul_le_mul_left ?_ _) _
      by_cases hc : ν2 j ≠ 0 ∧ rE (cXi exc2 μ ν2 v0 (CtrC.ord j) h)
          (SquareRel (fullSim (cRel Rv) h)) xp = 0
      · rw [if_pos hc, if_pos hc.2]
      · rw [if_neg hc]
        exact zero_le
    refine le_trans h1 ?_
    refine le_trans (screenE_WresD_cXiBar_le_sum exc2 μ ν2 v0 hpair2
      hdecl2 hμ0 hα0 Rv h (cXi exc1 μ ν1 v0 c₁ h)
      [cXi exc2 μ ν2 v0 (CtrC.ord j) h]) ?_
    have hcell : ∀ k : ℕ, (ν2 k : ℝ≥0∞) ≠ 0 →
        screenE (cXi exc1 μ ν1 v0 c₁ h)
          (SquareRel (fullSim (cRel Rv) h))
          [cXi exc2 μ ν2 v0 (CtrC.ord j) h]
          (WresD α (cXi exc2 μ ν2 v0 (CtrC.ord k) h)
            (SquareRel (fullSim (cRel Rv) h)))
        ≤ cCellBound α M E' := fun k hk =>
      cPairScreenR_tilt_le α Rv μ v0 exc1 exc2 ν1 ν2 hα c₁ (CtrC.ord j)
        (CtrC.ord k) h M E'
        (fun m1 m3 hm1 hm3 => hM1 m1 m3 hm1 ⟨k, hk, hm3⟩)
        (fun m1 m2 m3 hm1 hm2 hm3 =>
          hE1 m1 m2 m3 hm1 ⟨j, hj, hm2⟩ ⟨k, hk, hm3⟩)
        (fun m1 m3 hm1 hm3 => hE2 m1 j m3 hm1 hj ⟨k, hk, hm3⟩)
    calc ∑' k, (if ν2 k = 0 then 0 else
          compFloor exc2 μ ν2 v0 k ^ (-α)
            * screenE (cXi exc1 μ ν1 v0 c₁ h)
                (SquareRel (fullSim (cRel Rv) h))
                [cXi exc2 μ ν2 v0 (CtrC.ord j) h]
                (WresD α (cXi exc2 μ ν2 v0 (CtrC.ord k) h)
                  (SquareRel (fullSim (cRel Rv) h))))
        ≤ ∑' k, (if ν2 k = 0 then 0 else
            compFloor exc2 μ ν2 v0 k ^ (-α)) * cCellBound α M E' := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          by_cases hk : ν2 k = 0
          · rw [if_pos hk, if_pos hk, zero_mul]
          · rw [if_neg hk, if_neg hk]
            exact mul_le_mul_right (hcell k hk) _
      _ = (∑' k, (if ν2 k = 0 then 0 else
            compFloor exc2 μ ν2 v0 k ^ (-α))) * cCellBound α M E' :=
          ENNReal.tsum_mul_right
      _ ≤ T2 * cCellBound α M E' := mul_le_mul_left hT2 _
  refine le_trans (exists_dead_tsum_le (cXi exc1 μ ν1 v0 c₁ h) ν2
    (fun j => cXi exc2 μ ν2 v0 (CtrC.ord j) h)
    (SquareRel (fullSim (cRel Rv) h))
    (WresD α (cXiBar exc2 μ ν2 v0 h)
      (SquareRel (fullSim (cRel Rv) h)))) ?_
  have hvanish : ∀ j ∉ K2,
      (∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if ν2 j ≠ 0 ∧ rE (cXi exc2 μ ν2 v0 (CtrC.ord j) h)
              (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (cXiBar exc2 μ ν2 v0 h)
              (SquareRel (fullSim (cRel Rv) h)) xp)) = 0 := by
    intro j hj
    have hz : ν2 j = 0 := by
      by_contra hne
      exact hj (hfin2 j hne)
    refine ENNReal.tsum_eq_zero.mpr fun xp => ?_
    rw [if_neg (fun hc => hc.1 hz), zero_mul, mul_zero]
  rw [tsum_eq_sum hvanish]
  have hterm : ∀ j ∈ K2,
      (∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if ν2 j ≠ 0 ∧ rE (cXi exc2 μ ν2 v0 (CtrC.ord j) h)
              (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (cXiBar exc2 μ ν2 v0 h)
              (SquareRel (fullSim (cRel Rv) h)) xp))
      ≤ T2 * cCellBound α M E' := by
    intro j _
    by_cases hj : (ν2 j : ℝ≥0∞) = 0
    · refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun xp => ?_))
        zero_le
      rw [if_neg (fun hc => hc.1 hj), zero_mul, mul_zero]
    · exact hTj j hj
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul, oneSidedBound_eq_cellBound]
  exact le_of_eq (by ring)

/-- **The fresh-target mixture cell, restricted hypotheses**: the
square-cell bound plus the priced one-sided bound, with the letter
bounds demanded only at the spawned component tuples. -/
theorem cMixR_le {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hμ0 : μ v0 ≠ 0)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hfin2 : ∀ k, ν2 k ≠ 0 → k ∈ K2)
    (c₁ : CtrC) (h : ℕ) (M Z E' T2 : ℝ≥0∞)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T2)
    (hM : ∀ m1 m2 : Option CtrC, cSpawn exc1 ν1 (some c₁) m1 →
      cSpawn exc2 ν2 none m2 →
      PhiDres α (cLet exc1 μ ν1 v0 m1 h) (cLet exc2 μ ν2 v0 m2 h)
          (fullSim (cRel Rv) h) ≤ M
        ∧ PhiDres α (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
            (fullSim (cRel Rv) h) ≤ M)
    (hZ : ∀ m1 m2 : Option CtrC, cSpawn exc1 ν1 (some c₁) m1 →
      cSpawn exc2 ν2 none m2 →
      zMass (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
        (fullSim (cRel Rv) h) ≤ Z)
    (hE1 : ∀ m1 m2 m3 : Option CtrC, cSpawn exc1 ν1 (some c₁) m1 →
      cSpawn exc2 ν2 none m2 → cSpawn exc2 ν2 none m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 m2 h]
        (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h)) ≤ E')
    (hE2 : ∀ (m1 : Option CtrC) (j : ℕ) (m3 : Option CtrC),
      cSpawn exc1 ν1 (some c₁) m1 → (ν2 j : ℝ≥0∞) ≠ 0 →
      cSpawn exc2 ν2 none m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 (cComp0 exc2 (CtrC.ord j)) h,
          cLet exc2 μ ν2 v0 (cComp1 exc2 (CtrC.ord j)) h]
        (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h)) ≤ E') :
    PhiDres α (cXi exc1 μ ν1 v0 c₁ h) (cXiBar exc2 μ ν2 v0 h)
        (SquareRel (fullSim (cRel Rv) h))
      ≤ cellCB α δ L K M Z E' + oneSidedBound α T2 K2.card M E' := by
  refine le_trans (PhiDres_bind_target_le hα (cXi exc1 μ ν1 v0 c₁ h) ν2
    (fun k => cXi exc2 μ ν2 v0 (CtrC.ord k) h)
    (SquareRel (fullSim (cRel Rv) h))) (add_le_add ?_ ?_)
  · refine tsum_pmf_mul_le_charged fun j hj => ?_
    exact cSquareR_le α Rv μ v0 exc1 exc2 ν1 ν2 hα hδ hL0 hL hK0 hK hsymm
      c₁ (CtrC.ord j) h M Z E'
      (fun m1 m2 hm1 hm2 => hM m1 m2 hm1 ⟨j, hj, hm2⟩)
      (fun m1 m2 hm1 hm2 => hZ m1 m2 hm1 ⟨j, hj, hm2⟩)
      (fun m1 m2 m3 hm1 hm2 hm3 =>
        hE1 m1 m2 m3 hm1 ⟨j, hj, hm2⟩ ⟨j, hj, hm3⟩)
  · exact cOneSidedR_le α Rv μ v0 exc1 exc2 ν1 ν2 K2 hα hμ0 hpair2 hdecl2
      hfin2 c₁ h M E' T2 hT2 (fun m1 m3 hm1 hm3 => (hM m1 m3 hm1 hm3).1)
      hE1 hE2

/-- The frozen-frozen ordinary row at the reachable index
(`eq:row-ZZ`). -/
theorem cRowR_ZZ {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hrefl0 : Rv v0 v0) (hsymm : ∀ a b, Rv a b → Rv b a)
    (cs ct : CtrC) (h : ℕ) (M Z E' : ℝ≥0∞)
    (hM : ∀ m1 m2 : Option CtrC, cSpawn exc1 ν1 (some cs) m1 →
      cSpawn exc2 ν2 (some ct) m2 →
      PhiDres α (cLet exc1 μ ν1 v0 m1 h) (cLet exc2 μ ν2 v0 m2 h)
          (fullSim (cRel Rv) h) ≤ M
        ∧ PhiDres α (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
            (fullSim (cRel Rv) h) ≤ M)
    (hZ : ∀ m1 m2 : Option CtrC, cSpawn exc1 ν1 (some cs) m1 →
      cSpawn exc2 ν2 (some ct) m2 →
      zMass (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
        (fullSim (cRel Rv) h) ≤ Z)
    (hE1 : ∀ m1 m2 m3 : Option CtrC, cSpawn exc1 ν1 (some cs) m1 →
      cSpawn exc2 ν2 (some ct) m2 → cSpawn exc2 ν2 (some ct) m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 m2 h]
        (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h)) ≤ E') :
    PhiDres α (cZ exc1 μ ν1 v0 cs (h + 1)) (cZ exc2 μ ν2 v0 ct (h + 1))
        (fullSim (cRel Rv) (h + 1))
      ≤ cellCB α δ L K M Z E' := by
  rw [cPhiDres_cZ_cZ_succ α Rv μ v0 exc1 exc2 ν1 ν2 hrefl0 cs ct h]
  exact cSquareR_le α Rv μ v0 exc1 exc2 ν1 ν2 hα hδ hL0 hL hK0 hK hsymm
    cs ct h M Z E' hM hZ hE1

/-- The frozen-fresh ordinary row at the reachable index
(`eq:row-ZF`). -/
theorem cRowR_ZT {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hμ0 : μ v0 ≠ 0)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hfin2 : ∀ k, ν2 k ≠ 0 → k ∈ K2)
    (cs : CtrC) (h : ℕ) (M Z E' T2 : ℝ≥0∞)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T2)
    (hM : ∀ m1 m2 : Option CtrC, cSpawn exc1 ν1 (some cs) m1 →
      cSpawn exc2 ν2 none m2 →
      PhiDres α (cLet exc1 μ ν1 v0 m1 h) (cLet exc2 μ ν2 v0 m2 h)
          (fullSim (cRel Rv) h) ≤ M
        ∧ PhiDres α (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
            (fullSim (cRel Rv) h) ≤ M)
    (hZ : ∀ m1 m2 : Option CtrC, cSpawn exc1 ν1 (some cs) m1 →
      cSpawn exc2 ν2 none m2 →
      zMass (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
        (fullSim (cRel Rv) h) ≤ Z)
    (hE1 : ∀ m1 m2 m3 : Option CtrC, cSpawn exc1 ν1 (some cs) m1 →
      cSpawn exc2 ν2 none m2 → cSpawn exc2 ν2 none m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 m2 h]
        (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h)) ≤ E')
    (hE2 : ∀ (m1 : Option CtrC) (j : ℕ) (m3 : Option CtrC),
      cSpawn exc1 ν1 (some cs) m1 → (ν2 j : ℝ≥0∞) ≠ 0 →
      cSpawn exc2 ν2 none m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 (cComp0 exc2 (CtrC.ord j)) h,
          cLet exc2 μ ν2 v0 (cComp1 exc2 (CtrC.ord j)) h]
        (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h)) ≤ E') :
    PhiDres α (cZ exc1 μ ν1 v0 cs (h + 1)) (cT exc2 μ ν2 v0 (h + 1))
        (fullSim (cRel Rv) (h + 1))
      ≤ phiE α (q μ Rv v0)
        + (cellCB α δ L K M Z E' + oneSidedBound α T2 K2.card M E')
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v0)
            * (cellCB α δ L K M Z E'
              + oneSidedBound α T2 K2.card M E')) := by
  have hmid := cMixR_le α Rv μ v0 exc1 exc2 ν1 ν2 K2 hα hδ hL0 hL hK0 hK
    hsymm hμ0 hpair2 hdecl2 hfin2 cs h M Z E' T2 hT2 hM hZ hE1 hE2
  refine le_trans (cPhiDres_cZ_cT_succ α Rv μ v0 exc1 exc2 ν1 ν2 hα
    cs h) ?_
  exact add_le_add (add_le_add le_rfl hmid)
    (mul_le_mul_right (mul_le_mul_right hmid _) _)

/-- The fresh-frozen ordinary row at the reachable index
(`eq:row-FZ`). -/
theorem cRowR_TZ {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a)
    (ct : CtrC) (h : ℕ) (M Z E' : ℝ≥0∞)
    (hM : ∀ m1 m2 : Option CtrC, cSpawn exc1 ν1 none m1 →
      cSpawn exc2 ν2 (some ct) m2 →
      PhiDres α (cLet exc1 μ ν1 v0 m1 h) (cLet exc2 μ ν2 v0 m2 h)
          (fullSim (cRel Rv) h) ≤ M
        ∧ PhiDres α (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
            (fullSim (cRel Rv) h) ≤ M)
    (hZ : ∀ m1 m2 : Option CtrC, cSpawn exc1 ν1 none m1 →
      cSpawn exc2 ν2 (some ct) m2 →
      zMass (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
        (fullSim (cRel Rv) h) ≤ Z)
    (hE1 : ∀ m1 m2 m3 : Option CtrC, cSpawn exc1 ν1 none m1 →
      cSpawn exc2 ν2 (some ct) m2 → cSpawn exc2 ν2 (some ct) m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 m2 h]
        (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h)) ≤ E') :
    PhiDres α (cT exc1 μ ν1 v0 (h + 1)) (cZ exc2 μ ν2 v0 ct (h + 1))
        (fullSim (cRel Rv) (h + 1))
      ≤ cellCB α δ L K M Z E' := by
  refine le_trans (cPhiDres_cT_cZ_succ α Rv μ v0 exc1 exc2 ν1 ν2 ct h) ?_
  refine tsum_pmf_mul_le_charged fun k hk => ?_
  exact cSquareR_le α Rv μ v0 exc1 exc2 ν1 ν2 hα hδ hL0 hL hK0 hK hsymm
    (CtrC.ord k) ct h M Z E'
    (fun m1 m2 hm1 hm2 => hM m1 m2 ⟨k, hk, hm1⟩ hm2)
    (fun m1 m2 hm1 hm2 => hZ m1 m2 ⟨k, hk, hm1⟩ hm2)
    (fun m1 m2 m3 hm1 hm2 hm3 => hE1 m1 m2 m3 ⟨k, hk, hm1⟩ hm2 hm3)

/-- The fresh-fresh ordinary row at the reachable index
(`eq:row-FF`). -/
theorem cRowR_TT {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hμ0 : μ v0 ≠ 0)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hfin2 : ∀ k, ν2 k ≠ 0 → k ∈ K2)
    (h : ℕ) (M Z E' T2 : ℝ≥0∞)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T2)
    (hM : ∀ m1 m2 : Option CtrC, cSpawn exc1 ν1 none m1 →
      cSpawn exc2 ν2 none m2 →
      PhiDres α (cLet exc1 μ ν1 v0 m1 h) (cLet exc2 μ ν2 v0 m2 h)
          (fullSim (cRel Rv) h) ≤ M
        ∧ PhiDres α (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
            (fullSim (cRel Rv) h) ≤ M)
    (hZ : ∀ m1 m2 : Option CtrC, cSpawn exc1 ν1 none m1 →
      cSpawn exc2 ν2 none m2 →
      zMass (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
        (fullSim (cRel Rv) h) ≤ Z)
    (hE1 : ∀ m1 m2 m3 : Option CtrC, cSpawn exc1 ν1 none m1 →
      cSpawn exc2 ν2 none m2 → cSpawn exc2 ν2 none m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 m2 h]
        (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h)) ≤ E')
    (hE2 : ∀ (m1 : Option CtrC) (j : ℕ) (m3 : Option CtrC),
      cSpawn exc1 ν1 none m1 → (ν2 j : ℝ≥0∞) ≠ 0 →
      cSpawn exc2 ν2 none m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 (cComp0 exc2 (CtrC.ord j)) h,
          cLet exc2 μ ν2 v0 (cComp1 exc2 (CtrC.ord j)) h]
        (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h)) ≤ E') :
    PhiDres α (cT exc1 μ ν1 v0 (h + 1)) (cT exc2 μ ν2 v0 (h + 1))
        (fullSim (cRel Rv) (h + 1))
      ≤ etaG α Rv μ
        + (cellCB α δ L K M Z E' + oneSidedBound α T2 K2.card M E')
        + ENNReal.ofReal (2 * α)
          * (etaG α Rv μ
            * (cellCB α δ L K M Z E'
              + oneSidedBound α T2 K2.card M E')) := by
  have hmix : (∑' k, ν1 k
      * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
          (cXiBar exc2 μ ν2 v0 h) (SquareRel (fullSim (cRel Rv) h)))
      ≤ cellCB α δ L K M Z E' + oneSidedBound α T2 K2.card M E' := by
    refine tsum_pmf_mul_le_charged fun k hk => ?_
    exact cMixR_le α Rv μ v0 exc1 exc2 ν1 ν2 K2 hα hδ hL0 hL hK0 hK hsymm
      hμ0 hpair2 hdecl2 hfin2 (CtrC.ord k) h M Z E' T2 hT2
      (fun m1 m2 hm1 hm2 => hM m1 m2 ⟨k, hk, hm1⟩ hm2)
      (fun m1 m2 hm1 hm2 => hZ m1 m2 ⟨k, hk, hm1⟩ hm2)
      (fun m1 m2 m3 hm1 hm2 hm3 => hE1 m1 m2 m3 ⟨k, hk, hm1⟩ hm2 hm3)
      (fun m1 j m3 hm1 hj hm3 => hE2 m1 j m3 ⟨k, hk, hm1⟩ hj hm3)
  refine le_trans (cPhiDres_cT_cT_succ α Rv μ v0 exc1 exc2 ν1 ν2 hα h) ?_
  exact add_le_add (add_le_add le_rfl hmix)
    (mul_le_mul_right (mul_le_mul_right hmix _) _)

/-! ### The base row and the ordinary step -/

/-- **The ordinary base row** (`thm:base`(i)): at height 0 the
ordinary scalar is below the root charge `etaG + phiE (q v0)`. -/
theorem cPsi_base (hrefl0 : Rv v0 v0) :
    cPsi α Rv μ v0 exc1 exc2 ν1 ν2 0
      ≤ etaG α Rv μ + phiE α (q μ Rv v0) := by
  rw [cPsi]
  refine iSup_le fun o => iSup_le fun n => iSup_le fun l1 =>
    iSup_le fun l2 => iSup_le fun _ => iSup_le fun _ => ?_
  cases o with
  | false => exact cRow_base α Rv μ v0 exc1 exc2 ν1 ν2 hrefl0 l1 l2
  | true => exact cRow_base α Rv μ v0 exc2 exc1 ν2 ν1 hrefl0 l1 l2

/-- **The assembled ordinary step** (`thm:psi-rows`): every
aligned letter-pair coordinate at height `h + 1`, in either
orientation, is bounded through its restricted row by the step
function evaluated at the running scalars; the row hypotheses are
discharged by the coordinate injections at the spawned level `n + 1`
of the reachable index. -/
theorem cPsi_step {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
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
    (h : ℕ) :
    cPsi α Rv μ v0 exc1 exc2 ν1 ν2 (h + 1)
      ≤ cStepF α δ L K (etaG α Rv μ + phiE α (q μ Rv v0)) T κ
          (cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h)
          (cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h) := by
  have hM12 : ∀ (n : ℕ) (m1 m2 : Option CtrC),
      cReach exc1 ν1 n m1 → cReach exc2 ν2 n m2 →
      PhiDres α (cLet exc1 μ ν1 v0 m1 h) (cLet exc2 μ ν2 v0 m2 h)
          (fullSim (cRel Rv) h) ≤ cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
        ∧ PhiDres α (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
            (fullSim (cRel Rv) h) ≤ cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h :=
    fun n m1 m2 r1 r2 =>
      ⟨le_cPsi α Rv μ v0 exc1 exc2 ν1 ν2 false n m1 m2 r1 r2 h,
        le_cPsi α Rv μ v0 exc1 exc2 ν1 ν2 true n m2 m1 r2 r1 h⟩
  have hM21 : ∀ (n : ℕ) (m1 m2 : Option CtrC),
      cReach exc2 ν2 n m1 → cReach exc1 ν1 n m2 →
      PhiDres α (cLet exc2 μ ν2 v0 m1 h) (cLet exc1 μ ν1 v0 m2 h)
          (fullSim (cRel Rv) h) ≤ cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
        ∧ PhiDres α (cLet exc1 μ ν1 v0 m2 h) (cLet exc2 μ ν2 v0 m1 h)
            (fullSim (cRel Rv) h) ≤ cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h :=
    fun n m1 m2 r1 r2 =>
      ⟨le_cPsi α Rv μ v0 exc1 exc2 ν1 ν2 true n m1 m2 r1 r2 h,
        le_cPsi α Rv μ v0 exc1 exc2 ν1 ν2 false n m2 m1 r2 r1 h⟩
  have hZ12 : ∀ (n : ℕ) (m1 m2 : Option CtrC),
      cReach exc1 ν1 n m1 → cReach exc2 ν2 n m2 →
      zMass (cLet exc2 μ ν2 v0 m2 h) (cLet exc1 μ ν1 v0 m1 h)
          (fullSim (cRel Rv) h)
        ≤ cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h :=
    fun n m1 m2 r1 r2 =>
      zMass_le_cDebt α Rv μ v0 exc1 exc2 ν1 ν2 true n m2 m1 r2 r1 h
  have hZ21 : ∀ (n : ℕ) (m1 m2 : Option CtrC),
      cReach exc2 ν2 n m1 → cReach exc1 ν1 n m2 →
      zMass (cLet exc1 μ ν1 v0 m2 h) (cLet exc2 μ ν2 v0 m1 h)
          (fullSim (cRel Rv) h)
        ≤ cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h :=
    fun n m1 m2 r1 r2 =>
      zMass_le_cDebt α Rv μ v0 exc1 exc2 ν1 ν2 false n m2 m1 r2 r1 h
  have hE1_12 : ∀ (n : ℕ) (m1 m2 m3 : Option CtrC),
      cReach exc1 ν1 n m1 → cReach exc2 ν2 n m2 → cReach exc2 ν2 n m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
          [cLet exc2 μ ν2 v0 m2 h]
          (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h))
        ≤ cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h :=
    fun n m1 m2 m3 r1 r2 r3 =>
      scrOne_le_cDebt α Rv μ v0 exc1 exc2 ν1 ν2 false n m1 m2 m3
        r1 r2 r3 h
  have hE1_21 : ∀ (n : ℕ) (m1 m2 m3 : Option CtrC),
      cReach exc2 ν2 n m1 → cReach exc1 ν1 n m2 → cReach exc1 ν1 n m3 →
      screenE (cLet exc2 μ ν2 v0 m1 h) (fullSim (cRel Rv) h)
          [cLet exc1 μ ν1 v0 m2 h]
          (WresD α (cLet exc1 μ ν1 v0 m3 h) (fullSim (cRel Rv) h))
        ≤ cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h :=
    fun n m1 m2 m3 r1 r2 r3 =>
      scrOne_le_cDebt α Rv μ v0 exc1 exc2 ν1 ν2 true n m1 m2 m3
        r1 r2 r3 h
  have hE2_12 : ∀ (n : ℕ) (m1 m2 m2' m3 : Option CtrC),
      cReach exc1 ν1 n m1 → cReach exc2 ν2 n m2 → cReach exc2 ν2 n m2' →
      cReach exc2 ν2 n m3 →
      screenE (cLet exc1 μ ν1 v0 m1 h) (fullSim (cRel Rv) h)
          [cLet exc2 μ ν2 v0 m2 h, cLet exc2 μ ν2 v0 m2' h]
          (WresD α (cLet exc2 μ ν2 v0 m3 h) (fullSim (cRel Rv) h))
        ≤ cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h :=
    fun n m1 m2 m2' m3 r1 r2 r2' r3 =>
      scrTwo_le_cDebt α Rv μ v0 exc1 exc2 ν1 ν2 false n m1 m2 m2' m3
        r1 r2 r2' r3 h
  have hE2_21 : ∀ (n : ℕ) (m1 m2 m2' m3 : Option CtrC),
      cReach exc2 ν2 n m1 → cReach exc1 ν1 n m2 → cReach exc1 ν1 n m2' →
      cReach exc1 ν1 n m3 →
      screenE (cLet exc2 μ ν2 v0 m1 h) (fullSim (cRel Rv) h)
          [cLet exc1 μ ν1 v0 m2 h, cLet exc1 μ ν1 v0 m2' h]
          (WresD α (cLet exc1 μ ν1 v0 m3 h) (fullSim (cRel Rv) h))
        ≤ cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h :=
    fun n m1 m2 m2' m3 r1 r2 r2' r3 =>
      scrTwo_le_cDebt α Rv μ v0 exc1 exc2 ν1 ν2 true n m1 m2 m2' m3
        r1 r2 r2' r3 h
  rw [cPsi]
  refine iSup_le fun o => iSup_le fun n => iSup_le fun l1 =>
    iSup_le fun l2 => iSup_le fun r1 => iSup_le fun r2 => ?_
  cases o with
  | false =>
      cases l1 with
      | some cs =>
          cases l2 with
          | some ct =>
              exact le_trans
                (cRowR_ZZ α Rv μ v0 exc1 exc2 ν1 ν2 hα hδ hL0 hL hK0 hK
                  hrefl0 hsymm cs ct h _ _ _
                  (fun m1 m2 hm1 hm2 => hM12 (n + 1) m1 m2
                    ⟨some cs, r1, hm1⟩ ⟨some ct, r2, hm2⟩)
                  (fun m1 m2 hm1 hm2 => hZ12 (n + 1) m1 m2
                    ⟨some cs, r1, hm1⟩ ⟨some ct, r2, hm2⟩)
                  (fun m1 m2 m3 hm1 hm2 hm3 => hE1_12 (n + 1) m1 m2 m3
                    ⟨some cs, r1, hm1⟩ ⟨some ct, r2, hm2⟩
                    ⟨some ct, r2, hm3⟩))
                (cell_le_cStepF α δ L K _ T κ _ _)
          | none =>
              exact le_trans
                (cRowR_ZT α Rv μ v0 exc1 exc2 ν1 ν2 K2 hα hδ hL0 hL hK0
                  hK hsymm hμ0 hpair2 hdecl2 hfin2 cs h _ _ _ T hT2
                  (fun m1 m2 hm1 hm2 => hM12 (n + 1) m1 m2
                    ⟨some cs, r1, hm1⟩ ⟨none, r2, hm2⟩)
                  (fun m1 m2 hm1 hm2 => hZ12 (n + 1) m1 m2
                    ⟨some cs, r1, hm1⟩ ⟨none, r2, hm2⟩)
                  (fun m1 m2 m3 hm1 hm2 hm3 => hE1_12 (n + 1) m1 m2 m3
                    ⟨some cs, r1, hm1⟩ ⟨none, r2, hm2⟩ ⟨none, r2, hm3⟩)
                  (fun m1 j m3 hm1 hj hm3 => hE2_12 (n + 1) m1
                    (cComp0 exc2 (CtrC.ord j)) (cComp1 exc2 (CtrC.ord j))
                    m3 ⟨some cs, r1, hm1⟩
                    ⟨none, r2, ⟨j, hj, Or.inl rfl⟩⟩
                    ⟨none, r2, ⟨j, hj, Or.inr rfl⟩⟩ ⟨none, r2, hm3⟩))
                (row_le_cStepF α δ L K le_add_self
                  (osb_le_cStepF_term α K2.card le_rfl hκ2 _ _))
      | none =>
          cases l2 with
          | some ct =>
              exact le_trans
                (cRowR_TZ α Rv μ v0 exc1 exc2 ν1 ν2 hα hδ hL0 hL hK0 hK
                  hsymm ct h _ _ _
                  (fun m1 m2 hm1 hm2 => hM12 (n + 1) m1 m2
                    ⟨none, r1, hm1⟩ ⟨some ct, r2, hm2⟩)
                  (fun m1 m2 hm1 hm2 => hZ12 (n + 1) m1 m2
                    ⟨none, r1, hm1⟩ ⟨some ct, r2, hm2⟩)
                  (fun m1 m2 m3 hm1 hm2 hm3 => hE1_12 (n + 1) m1 m2 m3
                    ⟨none, r1, hm1⟩ ⟨some ct, r2, hm2⟩
                    ⟨some ct, r2, hm3⟩))
                (cell_le_cStepF α δ L K _ T κ _ _)
          | none =>
              exact le_trans
                (cRowR_TT α Rv μ v0 exc1 exc2 ν1 ν2 K2 hα hδ hL0 hL hK0
                  hK hsymm hμ0 hpair2 hdecl2 hfin2 h _ _ _ T hT2
                  (fun m1 m2 hm1 hm2 => hM12 (n + 1) m1 m2
                    ⟨none, r1, hm1⟩ ⟨none, r2, hm2⟩)
                  (fun m1 m2 hm1 hm2 => hZ12 (n + 1) m1 m2
                    ⟨none, r1, hm1⟩ ⟨none, r2, hm2⟩)
                  (fun m1 m2 m3 hm1 hm2 hm3 => hE1_12 (n + 1) m1 m2 m3
                    ⟨none, r1, hm1⟩ ⟨none, r2, hm2⟩ ⟨none, r2, hm3⟩)
                  (fun m1 j m3 hm1 hj hm3 => hE2_12 (n + 1) m1
                    (cComp0 exc2 (CtrC.ord j)) (cComp1 exc2 (CtrC.ord j))
                    m3 ⟨none, r1, hm1⟩
                    ⟨none, r2, ⟨j, hj, Or.inl rfl⟩⟩
                    ⟨none, r2, ⟨j, hj, Or.inr rfl⟩⟩ ⟨none, r2, hm3⟩))
                (row_le_cStepF α δ L K le_self_add
                  (osb_le_cStepF_term α K2.card le_rfl hκ2 _ _))
  | true =>
      cases l1 with
      | some cs =>
          cases l2 with
          | some ct =>
              exact le_trans
                (cRowR_ZZ α Rv μ v0 exc2 exc1 ν2 ν1 hα hδ hL0 hL hK0 hK
                  hrefl0 hsymm cs ct h _ _ _
                  (fun m1 m2 hm1 hm2 => hM21 (n + 1) m1 m2
                    ⟨some cs, r1, hm1⟩ ⟨some ct, r2, hm2⟩)
                  (fun m1 m2 hm1 hm2 => hZ21 (n + 1) m1 m2
                    ⟨some cs, r1, hm1⟩ ⟨some ct, r2, hm2⟩)
                  (fun m1 m2 m3 hm1 hm2 hm3 => hE1_21 (n + 1) m1 m2 m3
                    ⟨some cs, r1, hm1⟩ ⟨some ct, r2, hm2⟩
                    ⟨some ct, r2, hm3⟩))
                (cell_le_cStepF α δ L K _ T κ _ _)
          | none =>
              exact le_trans
                (cRowR_ZT α Rv μ v0 exc2 exc1 ν2 ν1 K1 hα hδ hL0 hL hK0
                  hK hsymm hμ0 hpair1 hdecl1 hfin1 cs h _ _ _ T hT1
                  (fun m1 m2 hm1 hm2 => hM21 (n + 1) m1 m2
                    ⟨some cs, r1, hm1⟩ ⟨none, r2, hm2⟩)
                  (fun m1 m2 hm1 hm2 => hZ21 (n + 1) m1 m2
                    ⟨some cs, r1, hm1⟩ ⟨none, r2, hm2⟩)
                  (fun m1 m2 m3 hm1 hm2 hm3 => hE1_21 (n + 1) m1 m2 m3
                    ⟨some cs, r1, hm1⟩ ⟨none, r2, hm2⟩ ⟨none, r2, hm3⟩)
                  (fun m1 j m3 hm1 hj hm3 => hE2_21 (n + 1) m1
                    (cComp0 exc1 (CtrC.ord j)) (cComp1 exc1 (CtrC.ord j))
                    m3 ⟨some cs, r1, hm1⟩
                    ⟨none, r2, ⟨j, hj, Or.inl rfl⟩⟩
                    ⟨none, r2, ⟨j, hj, Or.inr rfl⟩⟩ ⟨none, r2, hm3⟩))
                (row_le_cStepF α δ L K le_add_self
                  (osb_le_cStepF_term α K1.card le_rfl hκ1 _ _))
      | none =>
          cases l2 with
          | some ct =>
              exact le_trans
                (cRowR_TZ α Rv μ v0 exc2 exc1 ν2 ν1 hα hδ hL0 hL hK0 hK
                  hsymm ct h _ _ _
                  (fun m1 m2 hm1 hm2 => hM21 (n + 1) m1 m2
                    ⟨none, r1, hm1⟩ ⟨some ct, r2, hm2⟩)
                  (fun m1 m2 hm1 hm2 => hZ21 (n + 1) m1 m2
                    ⟨none, r1, hm1⟩ ⟨some ct, r2, hm2⟩)
                  (fun m1 m2 m3 hm1 hm2 hm3 => hE1_21 (n + 1) m1 m2 m3
                    ⟨none, r1, hm1⟩ ⟨some ct, r2, hm2⟩
                    ⟨some ct, r2, hm3⟩))
                (cell_le_cStepF α δ L K _ T κ _ _)
          | none =>
              exact le_trans
                (cRowR_TT α Rv μ v0 exc2 exc1 ν2 ν1 K1 hα hδ hL0 hL hK0
                  hK hsymm hμ0 hpair1 hdecl1 hfin1 h _ _ _ T hT1
                  (fun m1 m2 hm1 hm2 => hM21 (n + 1) m1 m2
                    ⟨none, r1, hm1⟩ ⟨none, r2, hm2⟩)
                  (fun m1 m2 hm1 hm2 => hZ21 (n + 1) m1 m2
                    ⟨none, r1, hm1⟩ ⟨none, r2, hm2⟩)
                  (fun m1 m2 m3 hm1 hm2 hm3 => hE1_21 (n + 1) m1 m2 m3
                    ⟨none, r1, hm1⟩ ⟨none, r2, hm2⟩ ⟨none, r2, hm3⟩)
                  (fun m1 j m3 hm1 hj hm3 => hE2_21 (n + 1) m1
                    (cComp0 exc1 (CtrC.ord j)) (cComp1 exc1 (CtrC.ord j))
                    m3 ⟨none, r1, hm1⟩
                    ⟨none, r2, ⟨j, hj, Or.inl rfl⟩⟩
                    ⟨none, r2, ⟨j, hj, Or.inr rfl⟩⟩ ⟨none, r2, hm3⟩))
                (row_le_cStepF α δ L K le_self_add
                  (osb_le_cStepF_term α K1.card le_rfl hκ1 _ _))

end Coordinates

/-! ### The closure constants -/

/-- The root-charge multiplier `A`: the base and inhomogeneous charges
`etaG + phiE (q v0)` are at most `A * etaG` by `phiE_root_le`. -/
noncomputable def cRootA (μ : PMF V) (v0 : V) : ℝ≥0∞ := 1 + (μ v0)⁻¹

/-- The linear ordinary coefficient `λ` of the square cell, the factor
`2L + 2(1 + δ)K` of `eq:res-four-law`. -/
noncomputable def cLamS (δ L K : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * L + 2 * (1 + δ) * K)

/-- The quadratic ordinary coefficient of the square cell. -/
noncomputable def cQuadC (α δ L : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)

/-- The linear debt coefficient `B1`: the debt terms of the step
function enter linearly with this total weight, at debt multiplier
`X`. -/
noncomputable def cLinB (δ : ℝ) (T κ X : ℝ≥0∞) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 * (1 + δ)) + 4 + 4 * T * κ) * X

/-- The ordinary barrier `Kc` (the constant `K` of
`eq:composite-K-eps`): the linear slack
`1 - λ` is spent on the root charge, the linear debt, and one unit of
quadratic reserve. -/
noncomputable def cKc (δ L K : ℝ) (μ : PMF V) (v0 : V)
    (T κ X : ℝ≥0∞) : ℝ≥0∞ :=
  (cRootA μ v0 + cLinB δ T κ X + 1) * (1 - cLamS δ L K)⁻¹

/-- The quadratic coefficient `B2` of the expanded step function at
the invariant point. -/
noncomputable def cB2 (α δ L K : ℝ) (μ : PMF V) (v0 : V)
    (T κ X : ℝ≥0∞) : ℝ≥0∞ :=
  cQuadC α δ L * (cKc δ L K μ v0 T κ X * cKc δ L K μ v0 T κ X)
    + 4 * ENNReal.ofReal α * X * cKc δ L K μ v0 T κ X * (1 + T * κ)
    + 4 * T * κ * (X * X)

/-- The first absorbed coefficient of the closure (an absorption budget
of `thm:numeric`). -/
noncomputable def cC2 (α δ L K : ℝ) (μ : PMF V) (v0 : V)
    (T κ X : ℝ≥0∞) : ℝ≥0∞ :=
  cB2 α δ L K μ v0 T κ X
    + ENNReal.ofReal (2 * α) * cRootA μ v0
      * (cLamS δ L K * cKc δ L K μ v0 T κ X + cLinB δ T κ X)

/-- The second absorbed coefficient of the closure. -/
noncomputable def cC3 (α δ L K : ℝ) (μ : PMF V) (v0 : V)
    (T κ X : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * α) * cRootA μ v0 * cB2 α δ L K μ v0 T κ X

/-- The explicit graph-potential threshold `etaStar` (the constant
`eps` of `eq:composite-K-eps`), in existence-level form: one inverse of
the total absorbed coefficient. -/
noncomputable def cEtaStar (α δ L K : ℝ) (μ : PMF V) (v0 : V)
    (T κ X : ℝ≥0∞) : ℝ≥0∞ :=
  (cC2 α δ L K μ v0 T κ X + cC3 α δ L K μ v0 T κ X + 1)⁻¹

/-! ### Finiteness and positivity of the constants -/

lemma cLinB_ne_top (δ : ℝ) {T κ X : ℝ≥0∞} (hT : T ≠ ⊤) (hκ : κ ≠ ⊤)
    (hX : X ≠ ⊤) : cLinB δ T κ X ≠ ⊤ := by
  rw [cLinB]
  refine ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofNat_ne_top⟩,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hT) hκ⟩) hX

/-! ### The fixed-point identity and the scalar absorption -/

/-- The barrier identity: the barrier absorbs its own linear
recursion. -/
lemma cKc_fix (δ L K : ℝ) (μ : PMF V) (v0 : V) (T κ X : ℝ≥0∞)
    (hlam : cLamS δ L K < 1) :
    cRootA μ v0 + cLinB δ T κ X + 1
        + cLamS δ L K * cKc δ L K μ v0 T κ X
      = cKc δ L K μ v0 T κ X := by
  have h0 : (1 : ℝ≥0∞) - cLamS δ L K ≠ 0 := (tsub_pos_of_lt hlam).ne'
  have ht : (1 : ℝ≥0∞) - cLamS δ L K ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hcancel : ((1 : ℝ≥0∞) - cLamS δ L K)
      * ((1 : ℝ≥0∞) - cLamS δ L K)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel h0 ht
  have hsum : ((1 : ℝ≥0∞) - cLamS δ L K) + cLamS δ L K = 1 :=
    tsub_add_cancel_of_le hlam.le
  rw [cKc]
  calc cRootA μ v0 + cLinB δ T κ X + 1
        + cLamS δ L K * ((cRootA μ v0 + cLinB δ T κ X + 1)
          * (1 - cLamS δ L K)⁻¹)
      = (cRootA μ v0 + cLinB δ T κ X + 1)
          * ((1 - cLamS δ L K) * (1 - cLamS δ L K)⁻¹)
        + cLamS δ L K * ((cRootA μ v0 + cLinB δ T κ X + 1)
          * (1 - cLamS δ L K)⁻¹) := by rw [hcancel, mul_one]
    _ = (cRootA μ v0 + cLinB δ T κ X + 1)
          * (((1 - cLamS δ L K) + cLamS δ L K)
            * (1 - cLamS δ L K)⁻¹) := by ring
    _ = (cRootA μ v0 + cLinB δ T κ X + 1) * (1 - cLamS δ L K)⁻¹ := by
        rw [hsum, one_mul]

/-- The barrier dominates the root multiplier. -/
lemma cRootA_le_cKc (δ L K : ℝ) (μ : PMF V) (v0 : V) (T κ X : ℝ≥0∞) :
    cRootA μ v0 ≤ cKc δ L K μ v0 T κ X := by
  have hone : (1 : ℝ≥0∞) ≤ (1 - cLamS δ L K)⁻¹ := by
    have h1 := ENNReal.inv_le_inv'
      (tsub_le_self : (1 : ℝ≥0∞) - cLamS δ L K ≤ 1)
    rwa [inv_one] at h1
  rw [cKc]
  calc cRootA μ v0
      ≤ cRootA μ v0 + cLinB δ T κ X + 1 := le_self_add.trans le_self_add
    _ = (cRootA μ v0 + cLinB δ T κ X + 1) * 1 := (mul_one _).symm
    _ ≤ (cRootA μ v0 + cLinB δ T κ X + 1) * (1 - cLamS δ L K)⁻¹ :=
        mul_le_mul_right hone _

/-- The root charge is at most the root multiplier times the graph
potential. -/
lemma cTheta0_le (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (hμ0 : μ v0 ≠ 0) :
    etaG α Rv μ + phiE α (q μ Rv v0) ≤ cRootA μ v0 * etaG α Rv μ := by
  rw [cRootA, add_mul, one_mul]
  exact add_le_add le_rfl (phiE_root_le α Rv μ v0 hμ0)

/-- **Scalar absorption** (the closure inequalities `eq:closure`,
verified by the absorption computation of `thm:numeric`): at graph
potential below the threshold, the step function maps the invariant
box `cPsi ≤ Kc * η`, `cDebt ≤ X * η` into itself. -/
theorem cStepF_absorb (α δ L K : ℝ) (μ : PMF V) (v0 : V)
    (T κ X : ℝ≥0∞) (hlam : cLamS δ L K < 1) {η : ℝ≥0∞}
    (heta : η ≤ cEtaStar α δ L K μ v0 T κ X) :
    cStepF α δ L K (cRootA μ v0 * η) T κ
        (cKc δ L K μ v0 T κ X * η) (X * η)
      ≤ cKc δ L K μ v0 T κ X * η := by
  have hS3ne0 : cC2 α δ L K μ v0 T κ X + cC3 α δ L K μ v0 T κ X + 1
      ≠ 0 := (lt_of_lt_of_le zero_lt_one le_add_self).ne'
  have heta' : η ≤ (cC2 α δ L K μ v0 T κ X
      + cC3 α δ L K μ v0 T κ X + 1)⁻¹ := by
    rw [cEtaStar] at heta
    exact heta
  have hquad : cC2 α δ L K μ v0 T κ X * η
      + cC3 α δ L K μ v0 T κ X * (η * η) ≤ 1 := by
    by_cases htop : cC2 α δ L K μ v0 T κ X
        + cC3 α δ L K μ v0 T κ X + 1 = ⊤
    · have hη0 : η = 0 := by
        rw [htop, ENNReal.inv_top] at heta'
        exact le_zero_iff.mp heta'
      rw [hη0]
      simp
    · have hη1 : η ≤ 1 :=
        le_trans heta' (ENNReal.inv_le_one.mpr le_add_self)
      calc cC2 α δ L K μ v0 T κ X * η
            + cC3 α δ L K μ v0 T κ X * (η * η)
          ≤ cC2 α δ L K μ v0 T κ X * η
            + cC3 α δ L K μ v0 T κ X * η := by
            refine add_le_add le_rfl ?_
            calc cC3 α δ L K μ v0 T κ X * (η * η)
                ≤ cC3 α δ L K μ v0 T κ X * (η * 1) :=
                  mul_le_mul_right (mul_le_mul_right hη1 η) _
              _ = cC3 α δ L K μ v0 T κ X * η := by rw [mul_one]
        _ = (cC2 α δ L K μ v0 T κ X + cC3 α δ L K μ v0 T κ X) * η :=
            (add_mul _ _ _).symm
        _ ≤ (cC2 α δ L K μ v0 T κ X + cC3 α δ L K μ v0 T κ X + 1) * η :=
            mul_le_mul_left le_self_add η
        _ ≤ (cC2 α δ L K μ v0 T κ X + cC3 α δ L K μ v0 T κ X + 1)
            * (cC2 α δ L K μ v0 T κ X
              + cC3 α δ L K μ v0 T κ X + 1)⁻¹ :=
            mul_le_mul_right heta' _
        _ = 1 := ENNReal.mul_inv_cancel hS3ne0 htop
  have hlin : cRootA μ v0
      + (cLamS δ L K * cKc δ L K μ v0 T κ X + cLinB δ T κ X) + 1
      ≤ cKc δ L K μ v0 T κ X := by
    have h1 : cRootA μ v0
        + (cLamS δ L K * cKc δ L K μ v0 T κ X + cLinB δ T κ X) + 1
        = cRootA μ v0 + cLinB δ T κ X + 1
          + cLamS δ L K * cKc δ L K μ v0 T κ X := by ring
    rw [h1, cKc_fix δ L K μ v0 T κ X hlam]
  calc cStepF α δ L K (cRootA μ v0 * η) T κ
        (cKc δ L K μ v0 T κ X * η) (X * η)
      = (cRootA μ v0
          + (cLamS δ L K * cKc δ L K μ v0 T κ X + cLinB δ T κ X)
          + (cC2 α δ L K μ v0 T κ X * η
            + cC3 α δ L K μ v0 T κ X * (η * η))) * η := by
        simp only [cStepF, cellCB, cC2, cC3, cB2, cLamS, cLinB, cQuadC]
        ring
    _ ≤ (cRootA μ v0
          + (cLamS δ L K * cKc δ L K μ v0 T κ X + cLinB δ T κ X)
          + 1) * η := mul_le_mul_left (add_le_add le_rfl hquad) η
    _ ≤ cKc δ L K μ v0 T κ X * η := mul_le_mul_left hlin η

/-! ### The screen-ledger hypothesis -/

/-- **The screen-ledger bound** (the invariant bound `eq:levels`): the
restricted debt scalar is at most `X * etaG` at every height.  This is
the screen half of the closed recursion `thm:engine`; `Debt.lean`
discharges it from the assembled screen rows (`thm:screen-rows`), the
pruning dichotomy of `Bridge`, and the nilpotence of the common block
(`ledger_nilpotent`) through the geometric estimate `thm:geom`. -/
def ScreenDebtBound (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
    (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
    (X : ℝ≥0∞) : Prop :=
  ∀ h : ℕ, cDebt α Rv μ v0 exc1 exc2 ν1 ν2 h ≤ X * etaG α Rv μ

/-! ### The uniform closure -/

section Closure

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ)

/-- **Uniform closure of the ordinary ledger** (`thm:engine`, ordinary
half): under the screen-ledger
bound, the ordinary scalar stays below `cKc * etaG` at every height
whenever the graph potential is below the threshold. -/
theorem cPsi_le_of_debt {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
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
    (T κ X : ℝ≥0∞)
    (hT1 : cTiltSum α exc1 μ ν1 v0 ≤ T)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T)
    (hκ1 : (K1.card : ℝ≥0∞) ≤ κ) (hκ2 : (K2.card : ℝ≥0∞) ≤ κ)
    (hlam : cLamS δ L K < 1)
    (hdebt : ScreenDebtBound α Rv μ v0 exc1 exc2 ν1 ν2 X)
    (heta : etaG α Rv μ ≤ cEtaStar α δ L K μ v0 T κ X) :
    ∀ h, cPsi α Rv μ v0 exc1 exc2 ν1 ν2 h
      ≤ cKc δ L K μ v0 T κ X * etaG α Rv μ := by
  intro h
  induction h with
  | zero =>
      refine le_trans (cPsi_base α Rv μ v0 exc1 exc2 ν1 ν2 hrefl0) ?_
      refine le_trans (cTheta0_le α Rv μ v0 hμ0) ?_
      exact mul_le_mul_left (cRootA_le_cKc δ L K μ v0 T κ X) _
  | succ h ih =>
      refine le_trans (cPsi_step α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2
        hα hδ hL0 hL hK0 hK hrefl0 hsymm hμ0 hpair1 hdecl1 hfin1
        hpair2 hdecl2 hfin2 T κ hT1 hT2 hκ1 hκ2 h) ?_
      refine le_trans (cStepF_mono α δ L K T κ
        (cTheta0_le α Rv μ v0 hμ0) ih (hdebt h)) ?_
      exact cStepF_absorb α δ L K μ v0 T κ X hlam heta

/-! ### The headline theorems (`thm:composite-matching`) -/

/-- **Composite two-law mismatch bound** (`thm:composite-matching`,
finite heights): under the standing packs of both orientations, the support
pack, the screen-ledger bound, and graph potential below the
threshold, the directed mismatch of the two composite fresh laws is at
most `cKc * etaG` at every height. -/
theorem composite_failure_le {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
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
    (T κ X : ℝ≥0∞)
    (hT1 : cTiltSum α exc1 μ ν1 v0 ≤ T)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T)
    (hκ1 : (K1.card : ℝ≥0∞) ≤ κ) (hκ2 : (K2.card : ℝ≥0∞) ≤ κ)
    (hlam : cLamS δ L K < 1)
    (hdebt : ScreenDebtBound α Rv μ v0 exc1 exc2 ν1 ν2 X)
    (heta : etaG α Rv μ ≤ cEtaStar α δ L K μ v0 T κ X) :
    ∀ h, failureD (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
        (fullSim (cRel Rv) h)
      ≤ cKc δ L K μ v0 T κ X * etaG α Rv μ := by
  intro h
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  refine le_trans (cFailure_le_PhiDres_of_support hα0 Rv μ v0
    exc1 exc2 ν1 ν2 N hrefl hμ0 hN hdeclN hcharged h) ?_
  refine le_trans ?_ (cPsi_le_of_debt α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2
    hα hδ hL0 hL hK0 hK (hrefl v0) hsymm hμ0 hpair1 hdecl1 hfin1
    hpair2 hdecl2 hfin2 T κ X hT1 hT2 hκ1 hκ2 hlam hdebt heta h)
  exact le_cPsi α Rv μ v0 exc1 exc2 ν1 ν2 false 0 none none
    (cReachO_zero exc1 exc2 ν1 ν2 false)
    (cReachO_zero exc1 exc2 ν1 ν2 (!false)) h

/-- **Composite two-law infinite matching** (`thm:composite-matching`):
the
infinite-tree matching probability of the two composite samples is at
least `1 - cKc * etaG`, by chaining the uniform mismatch bound into
the projective endpoint `cMatching_infinite_of_PhiDres`. -/
theorem composite_matching_le {Omega : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace Omega] (Pm : Measure Omega)
    [IsProbabilityMeasure Pm]
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
    (T κ X : ℝ≥0∞)
    (hT1 : cTiltSum α exc1 μ ν1 v0 ≤ T)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T)
    (hκ1 : (K1.card : ℝ≥0∞) ≤ κ) (hκ2 : (K2.card : ℝ≥0∞) ≤ κ)
    (hlam : cLamS δ L K < 1)
    (hdebt : ScreenDebtBound α Rv μ v0 exc1 exc2 ν1 ν2 X)
    (heta : etaG α Rv μ ≤ cEtaStar α δ L K μ v0 T κ X)
    (Xs Ys : (n : ℕ) → Omega → FullLab (CState V) n)
    (hXs : ∀ n omega, restrictLab n (Xs (n + 1) omega) = Xs n omega)
    (hYs : ∀ n omega, restrictLab n (Ys (n + 1) omega) = Ys n omega)
    (hpairM : ∀ n, Measurable (fun omega => (Xs n omega, Ys n omega)))
    (hlaw : ∀ n, Pm.map (fun omega => (Xs n omega, Ys n omega)) =
      (prodPMF (cT exc1 μ ν1 v0 n) (cT exc2 μ ν2 v0 n)).toMeasure) :
    1 - cKc δ L K μ v0 T κ X * etaG α Rv μ
      ≤ Pm {omega | InfMatch (cRel Rv)
          (fun n => Xs n omega) (fun n => Ys n omega)} := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  refine cMatching_infinite_of_PhiDres Pm hα0 Rv μ v0 exc1 exc2 ν1 ν2 N
    hrefl hμ0 hN hdeclN hcharged
    (cKc δ L K μ v0 T κ X * etaG α Rv μ) (fun n => ?_)
    Xs Ys hXs hYs hpairM hlaw
  refine le_trans (le_cPsi α Rv μ v0 exc1 exc2 ν1 ν2 false 0 none none
    (cReachO_zero exc1 exc2 ν1 ν2 false)
    (cReachO_zero exc1 exc2 ν1 ν2 (!false)) n) ?_
  exact cPsi_le_of_debt α Rv μ v0 exc1 exc2 ν1 ν2 K1 K2
    hα hδ hL0 hL hK0 hK (hrefl v0) hsymm hμ0 hpair1 hdecl1 hfin1
    hpair2 hdecl2 hfin2 T κ X hT1 hT2 hκ1 hκ2 hlam hdebt heta n

end Closure

end Composite
end GraphMarkovMatching
