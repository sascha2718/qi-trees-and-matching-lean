/-
The assembled rows of the composite two-law ledger
(`arbitrary_offspring_matching.tex`, `sec:composite`,
`thm:composite-ledger`), in
hypothesis-threaded form: every height-`(h + 1)` ordinary coordinate,
screen coordinate, and zero mass of the two-sided composite ledger is
bounded through an explicit row by height-`h` quantities of the same
classes (`≤ M` for ordinary letter-pair coordinates, `≤ Z` for reversed
letter zero masses, `≤ E'` for tilted letter screens) together with
explicit constants.  All rows are stated generically in the two side
packs `(exc1, ν1)` (source) and `(exc2, ν2)` (target); the swapped
orientation is the same theorem with the packs exchanged.

* `cLet`, `cComp0`, `cComp1`, `cXi_eq_prod`: the letter alphabet
  `Option CtrC` (`some c` the frozen law below `(v0, c)`, `none` the
  fresh law) and the product presentation of every composite cell,
  markers and exceptional entrances included;
* `cCellBound`, `cTiltSum`, `cMemberList`: the named constants of the
  rows: the per-cell screen bound `4E'(1 + αM) + 4E'²`, the composite
  charged tilt sum `∑_k compFloor(k)^{-α}` (a finite sum over the
  support by `cTiltSum_eq_sum`), and the full member list of the fresh
  cell mixture over the support `K2`;
* `cSquare_le`, `cMix_le`, `cOneSided_le`: the height-`h` square cell
  (`PhiDres_square_le` at the composite letters), the fresh-target
  mixture cell, and the weighted one-sided tilt mass;
* `cRow_ZZ`, `cRow_ZT`, `cRow_TZ`, `cRow_TT` (`thm:psi-rows`):
  the four ordinary rows at height `h + 1`; `cRow_base` the height-0
  base for all letter pairs (`thm:base`);
* `cScr_ZZ_unit` .. `cScr_TZ_tiltZ`, `cScr_TT_prune`
  (the screen rows `thm:screen-rows`): the one-step descent of
  the height-`(h + 1)` screens to pair-level cell screens at height
  `h`, the frozen-target lists descending to the target cell and the
  fresh-target list to the full member list `cMemberList`; fresh
  sources keep the retained coefficients `ν1 k`, fresh normalizations
  the root price `(rE μ Rv v0)^{-α}` and the composite prices
  `compFloor^{-α}` (`cPairScreen_price`);
* `cPairScreen_unit_factorize`, `cPairScreen_tilt_le`: the Hall
  factorization of a pair-level cell screen into letter screens and
  moments;
* `cZMass_row_ZZ`, `cZMass_row_ZT`, `cZMass_row_TZ` and the
  `cZMass_base_*` family: the zero-mass rows in `zMass` form (the
  fresh-fresh mass vanishes by `zMass_cT_cT_eq_zero` of `Bridge`);
* `cScr_base_unit`, `cScr_base_tilt`: the height-0 screen bounds.
-/
import GraphMarkovMatching.Composite.Bridge
import GraphMarkovMatching.Composite.ScreenDescent
import GraphMarkovMatching.Rows.Psi

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type}

/-! ### Generic helpers -/

/-- A tsum with support inside a finite set is the finite sum. -/
lemma tsum_eq_finsetSum_of_support {f : ℕ → ℝ≥0∞} {Kf : Finset ℕ}
    (hf : ∀ k, f k ≠ 0 → k ∈ Kf) : ∑' k, f k = ∑ k ∈ Kf, f k :=
  tsum_eq_sum fun k hk => by
    by_contra h0
    exact hk (hf k h0)

/-- A PMF average of a uniformly bounded family is bounded. -/
lemma tsum_pmf_mul_le {w : PMF ℕ} {g : ℕ → ℝ≥0∞} {C : ℝ≥0∞}
    (hg : ∀ k, g k ≤ C) : (∑' k, w k * g k) ≤ C := by
  calc ∑' k, w k * g k
      ≤ ∑' k, w k * C :=
        ENNReal.tsum_le_tsum fun k => mul_le_mul_right (hg k) _
    _ = (∑' k, (w k : ℝ≥0∞)) * C := ENNReal.tsum_mul_right
    _ = C := by rw [w.tsum_coe, one_mul]

/-- The zero-interface mass is the unit-normalized singleton screen. -/
lemma zMass_eq_screenE_unit {X : Type} (ρs ρt : PMF X)
    (R : X → X → Prop) :
    zMass ρs ρt R = screenE ρs R [ρt] (fun _ => 1) := by
  rw [zMass_eq_tsum, screenE_singleton]
  exact tsum_congr fun x => by rw [mul_one]

private lemma screenInd_le_one {X : Type} (R : X → X → Prop)
    (zs : List (PMF X)) (x : X) : screenInd R zs x ≤ 1 := by
  rw [screenInd]
  split_ifs <;> simp

/-- A unit-normalized screen is at most one. -/
lemma screenE_unit_le_one {X : Type} (ρs : PMF X) (R : X → X → Prop)
    (zs : List (PMF X)) : screenE ρs R zs (fun _ => 1) ≤ 1 := by
  rw [screenE]
  calc ∑' x, ρs x * screenInd R zs x * (fun _ => (1 : ℝ≥0∞)) x
      ≤ ∑' x, ρs x := ENNReal.tsum_le_tsum fun x => by
        calc ρs x * screenInd R zs x * (fun _ => (1 : ℝ≥0∞)) x
            = ρs x * screenInd R zs x := mul_one _
          _ ≤ ρs x * 1 := mul_le_mul_right (screenInd_le_one R zs x) _
          _ = ρs x := mul_one _
    _ = 1 := ρs.tsum_coe

/-- Enlarging the zero list shrinks the screen: a screen is below the
singleton screen of any member of its list. -/
lemma screenE_le_of_mem {X : Type} (ρs : PMF X) (R : X → X → Prop)
    {zs : List (PMF X)} {ρ : PMF X} (hρ : ρ ∈ zs) (g : X → ℝ≥0∞) :
    screenE ρs R zs g ≤ screenE ρs R [ρ] g := by
  rw [screenE, screenE]
  refine ENNReal.tsum_le_tsum fun x => ?_
  refine mul_le_mul_left (mul_le_mul_right ?_ (ρs x)) (g x)
  by_cases hall : ∀ τ ∈ zs, rE τ R x = 0
  · rw [screenInd, if_pos hall, screenInd, if_pos]
    intro τ hτ
    rw [List.mem_singleton.mp hτ]
    exact hall ρ hρ
  · rw [screenInd, if_neg hall]
    exact zero_le

/-- The good degree of a point law vanishes exactly off its relation
class. -/
private lemma rE_pure_eq_zero_iff {X : Type} (a : X) (R : X → X → Prop)
    (x : X) : rE (PMF.pure a) R x = 0 ↔ ¬ R x a := by
  rw [rE]
  constructor
  · intro h0 hxa
    have hterm := ENNReal.tsum_eq_zero.mp h0 a
    rw [if_pos hxa, PMF.pure_apply, if_pos rfl] at hterm
    exact one_ne_zero hterm
  · intro hxa
    refine ENNReal.tsum_eq_zero.mpr fun y => ?_
    by_cases hy : R x y
    · rw [if_pos hy, PMF.pure_apply,
        if_neg (show ¬ y = a from fun h => hxa (h ▸ hy))]
    · rw [if_neg hy]

/-- Distributing a two-term pointwise bound over a weighted, indicated
sum. -/
private lemma tsum_ind_split {Y : Type} (ρs : PMF Y)
    (c W P Q : Y → ℝ≥0∞) (hW : ∀ y, W y ≤ P y + Q y) :
    ∑' y, ρs y * (c y * W y)
      ≤ (∑' y, ρs y * (c y * P y)) + ∑' y, ρs y * (c y * Q y) := by
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun y => ?_
  calc ρs y * (c y * W y)
      ≤ ρs y * (c y * (P y + Q y)) :=
        mul_le_mul_right (mul_le_mul_right (hW y) _) _
    _ = ρs y * (c y * P y) + ρs y * (c y * Q y) := by ring

/-- **Target-mixture split of the restricted potential**: against a
countable target mixture, the restricted potential is at most the
mixture of the component coordinates (two-sided points, by Jensen) plus
the one-sided mass, indicated by some charged dead component and tilted
by the restricted inverse mixture degree. -/
lemma PhiDres_bind_target_le {X : Type} {α : ℝ} (hα : 1 ≤ α)
    (ρs : PMF X) (w : PMF ℕ) (f : ℕ → PMF X) (R : X → X → Prop) :
    PhiDres α ρs (w.bind f) R
      ≤ (∑' j, w j * PhiDres α ρs (f j) R)
        + ∑' x, ρs x
            * ((if ∃ j, w j ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0)
              * WresD α (w.bind f) R x) := by
  have hαpos : (0 : ℝ) < α := lt_of_lt_of_le one_pos hα
  have hpt : ∀ x : X,
      ρs x * (if rE (w.bind f) R x = 0 then 0
          else phiE α (q (w.bind f) R x))
      ≤ ρs x * ∑' j, w j * (if rE (f j) R x = 0 then 0
            else phiE α (q (f j) R x))
        + ρs x * ((if ∃ j, w j ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0)
            * WresD α (w.bind f) R x) := by
    intro x
    by_cases hres : rE (w.bind f) R x = 0
    · rw [if_pos hres, mul_zero]
      exact zero_le
    · rw [if_neg hres]
      by_cases hos : ∃ j, w j ≠ 0 ∧ rE (f j) R x = 0
      · have hb : phiE α (q (w.bind f) R x) ≤ WresD α (w.bind f) R x := by
          rw [phiE_eq_qE_mul_rpow α R (w.bind f) hαpos x,
            rE_rpow_neg_eq_WresD (w.bind f) R x hres]
          exact le_trans (mul_le_mul_left qE_le_one _)
            (le_of_eq (one_mul _))
        refine le_trans ?_ le_add_self
        calc ρs x * phiE α (q (w.bind f) R x)
            ≤ ρs x * WresD α (w.bind f) R x := mul_le_mul_right hb _
          _ = ρs x * ((if ∃ j, w j ≠ 0 ∧ rE (f j) R x = 0
                then 1 else 0) * WresD α (w.bind f) R x) := by
              rw [if_pos hos, one_mul]
      · have hos' : ∀ j, w j ≠ 0 → rE (f j) R x ≠ 0 :=
          fun j hj h0 => hos ⟨j, hj, h0⟩
        have hjen : phiE α (q (w.bind f) R x)
            ≤ ∑' j, w j * phiE α (q (f j) R x) := by
          have hq : q (w.bind f) R x
              = (∑' j, w j * ENNReal.ofReal (q (f j) R x)).toReal := by
            rw [q, show qE (w.bind f) R x
                = ∑' j, w j * qE (f j) R x from qE_bind w f R x]
            congr 1
            exact tsum_congr fun j => by
              rw [show ENNReal.ofReal (q (f j) R x) = qE (f j) R x from
                by rw [q, ENNReal.ofReal_toReal qE_ne_top]]
          rw [hq]
          exact phiE_tsum_jensen hα (fun j => (w j : ℝ≥0∞))
            (fun j => q (f j) R x) w.tsum_coe (fun j => q_nonneg)
            (fun j => q_le_one)
        have hterm : (∑' j, w j * phiE α (q (f j) R x))
            = ∑' j, w j * (if rE (f j) R x = 0 then 0
                else phiE α (q (f j) R x)) := by
          refine tsum_congr fun j => ?_
          by_cases hj : w j = 0
          · rw [hj, zero_mul, zero_mul]
          · rw [if_neg (hos' j hj)]
        exact le_trans (mul_le_mul_right (le_of_le_of_eq hjen hterm) _)
          le_self_add
  calc PhiDres α ρs (w.bind f) R
      ≤ ∑' x, (ρs x * ∑' j, w j * (if rE (f j) R x = 0 then 0
            else phiE α (q (f j) R x))
          + ρs x * ((if ∃ j, w j ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0)
              * WresD α (w.bind f) R x)) := by
        rw [PhiDres]
        exact ENNReal.tsum_le_tsum hpt
    _ = (∑' x, ρs x * ∑' j, w j * (if rE (f j) R x = 0 then 0
            else phiE α (q (f j) R x)))
        + ∑' x, ρs x * ((if ∃ j, w j ≠ 0 ∧ rE (f j) R x = 0
            then 1 else 0) * WresD α (w.bind f) R x) := ENNReal.tsum_add
    _ ≤ (∑' j, w j * PhiDres α ρs (f j) R)
        + ∑' x, ρs x * ((if ∃ j, w j ≠ 0 ∧ rE (f j) R x = 0
            then 1 else 0) * WresD α (w.bind f) R x) := by
        refine add_le_add (le_of_eq ?_) le_rfl
        rw [tsum_congr fun x => (ENNReal.tsum_mul_left).symm,
          ENNReal.tsum_comm]
        refine tsum_congr fun j => ?_
        rw [tsum_congr fun x => show ρs x * (w j
              * (if rE (f j) R x = 0 then 0 else phiE α (q (f j) R x)))
            = w j * (ρs x * (if rE (f j) R x = 0 then 0
                else phiE α (q (f j) R x))) from by ring,
          ENNReal.tsum_mul_left, PhiDres]

/-- **Union bound over the dead components**: the existential one-sided
indicator of a mixture is dominated by the sum of per-component dead
indicators, for any nonnegative tilt. -/
lemma exists_dead_tsum_le {X : Type} (ρs : PMF X) (w : PMF ℕ)
    (f : ℕ → PMF X) (R : X → X → Prop) (W : X → ℝ≥0∞) :
    ∑' x, ρs x * ((if ∃ j, w j ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0)
        * W x)
      ≤ ∑' j, ∑' x, ρs x
          * ((if w j ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0) * W x) := by
  have hpt : ∀ x, ρs x
      * ((if ∃ j, w j ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0) * W x)
      ≤ ∑' j, ρs x
          * ((if w j ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0) * W x) := by
    intro x
    by_cases hex : ∃ j, w j ≠ 0 ∧ rE (f j) R x = 0
    · obtain ⟨j₀, hj₀⟩ := hex
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum j₀)
      rw [if_pos ⟨j₀, hj₀⟩, if_pos hj₀]
    · rw [if_neg hex, zero_mul, mul_zero]
      exact zero_le
  exact le_trans (ENNReal.tsum_le_tsum hpt) (le_of_eq ENNReal.tsum_comm)

/-! ### The letter alphabet and the cell shapes -/

/-- The letter alphabet of a side: `some c` is the frozen law below
`(v0, c)`, `none` the fresh law. -/
noncomputable def cLet (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) : Option CtrC → (h : ℕ) → PMF (FullLab (CState V) h)
  | some c, h => cZ exc μ ν v0 c h
  | none, h => cT exc μ ν v0 h

@[simp] lemma cLet_some (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) (c : CtrC) (h : ℕ) :
    cLet exc μ ν v0 (some c) h = cZ exc μ ν v0 c h := rfl

@[simp] lemma cLet_none (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) (h : ℕ) :
    cLet exc μ ν v0 none h = cT exc μ ν v0 h := rfl

/-- The first letter component of a marker cell. -/
def markComp0 (a b i : ℕ) : Option CtrC :=
  if 4 ≤ val a i then some (CtrC.mark a b (i + 1))
  else if val a i = 3 then some (CtrC.ord 2)
  else some (CtrC.ord b)

/-- The second letter component of a marker cell. -/
def markComp1 (a b i : ℕ) : Option CtrC :=
  if 4 ≤ val a i then some (CtrC.ord (val a i - val a i / 2))
  else if val a i = 3 then some (CtrC.ord b)
  else none

/-- The first letter component of a composite cell. -/
def cComp0 (exc : ℕ → Option (ℕ × ℕ)) : CtrC → Option CtrC
  | CtrC.ord k =>
      match exc k with
      | some p => markComp0 p.1 p.2 0
      | none =>
          if 4 ≤ k then some (CtrC.ord (k / 2))
          else if k = 3 then some (CtrC.ord 2) else none
  | CtrC.mark a b i => markComp0 a b i

/-- The second letter component of a composite cell. -/
def cComp1 (exc : ℕ → Option (ℕ × ℕ)) : CtrC → Option CtrC
  | CtrC.ord k =>
      match exc k with
      | some p => markComp1 p.1 p.2 0
      | none => if 4 ≤ k then some (CtrC.ord (k - k / 2)) else none
  | CtrC.mark a b i => markComp1 a b i

lemma cComp0_mark (exc : ℕ → Option (ℕ × ℕ)) (a b i : ℕ) :
    cComp0 exc (CtrC.mark a b i) = markComp0 a b i := rfl

lemma cComp1_mark (exc : ℕ → Option (ℕ × ℕ)) (a b i : ℕ) :
    cComp1 exc (CtrC.mark a b i) = markComp1 a b i := rfl

lemma cComp0_ord_none {exc : ℕ → Option (ℕ × ℕ)} {k : ℕ}
    (hk : exc k = none) :
    cComp0 exc (CtrC.ord k)
      = (if 4 ≤ k then some (CtrC.ord (k / 2))
          else if k = 3 then some (CtrC.ord 2) else none) := by
  simp only [cComp0, hk]

lemma cComp1_ord_none {exc : ℕ → Option (ℕ × ℕ)} {k : ℕ}
    (hk : exc k = none) :
    cComp1 exc (CtrC.ord k)
      = (if 4 ≤ k then some (CtrC.ord (k - k / 2)) else none) := by
  simp only [cComp1, hk]

lemma cComp0_ord_some {exc : ℕ → Option (ℕ × ℕ)} {k : ℕ} {p : ℕ × ℕ}
    (hk : exc k = some p) :
    cComp0 exc (CtrC.ord k) = markComp0 p.1 p.2 0 := by
  simp only [cComp0, hk]

lemma cComp1_ord_some {exc : ℕ → Option (ℕ × ℕ)} {k : ℕ} {p : ℕ × ℕ}
    (hk : exc k = some p) :
    cComp1 exc (CtrC.ord k) = markComp1 p.1 p.2 0 := by
  simp only [cComp1, hk]

section Shapes

variable (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V) (ν : PMF ℕ) (v0 : V)

private lemma cXi_mark_eq_prod (a b i h : ℕ) :
    cXi exc μ ν v0 (CtrC.mark a b i) h
      = prodPMF (cLet exc μ ν v0 (markComp0 a b i) h)
          (cLet exc μ ν v0 (markComp1 a b i) h) := by
  rcases Nat.lt_or_ge (val a i) 3 with h2 | h3
  · have e0 : markComp0 a b i = some (CtrC.ord b) := by
      rw [markComp0, if_neg (by omega), if_neg (by omega)]
    have e1 : markComp1 a b i = none := by
      rw [markComp1, if_neg (by omega), if_neg (by omega)]
    rw [e0, e1, cLet_some, cLet_none]
    exact cXi_mark_le_two exc μ ν v0 (by omega) h
  · rcases Nat.lt_or_ge (val a i) 4 with h4 | h4
    · have h3' : val a i = 3 := by omega
      have e0 : markComp0 a b i = some (CtrC.ord 2) := by
        rw [markComp0, if_neg (by omega), if_pos h3']
      have e1 : markComp1 a b i = some (CtrC.ord b) := by
        rw [markComp1, if_neg (by omega), if_pos h3']
      rw [e0, e1, cLet_some, cLet_some]
      exact cXi_mark_three exc μ ν v0 h3' h
    · have e0 : markComp0 a b i = some (CtrC.mark a b (i + 1)) := by
        rw [markComp0, if_pos h4]
      have e1 : markComp1 a b i
          = some (CtrC.ord (val a i - val a i / 2)) := by
        rw [markComp1, if_pos h4]
      rw [e0, e1, cLet_some, cLet_some]
      exact cXi_mark_of_ge exc μ ν v0 h4 h

/-- **The product presentation of every composite cell** (the cell
shapes of `Kernel`, uniformly over all tagged letters): the cell of any
counter is the product of its two letter components. -/
lemma cXi_eq_prod (c : CtrC) (h : ℕ) :
    cXi exc μ ν v0 c h
      = prodPMF (cLet exc μ ν v0 (cComp0 exc c) h)
          (cLet exc μ ν v0 (cComp1 exc c) h) := by
  cases c with
  | mark a b i =>
      rw [cComp0_mark, cComp1_mark]
      exact cXi_mark_eq_prod exc μ ν v0 a b i h
  | ord k =>
      rcases hk : exc k with _ | p
      · rcases Nat.lt_or_ge k 3 with h2 | h3
        · rw [cComp0_ord_none hk, cComp1_ord_none hk, if_neg (by omega),
            if_neg (by omega), if_neg (by omega), cLet_none]
          exact cXi_ord_none_le_two exc μ ν v0 hk (by omega) h
        · rcases Nat.lt_or_ge k 4 with h4 | h4
          · have h3' : k = 3 := by omega
            rw [cComp0_ord_none hk, cComp1_ord_none hk, if_neg (by omega),
              if_pos h3', if_neg (by omega), cLet_some, cLet_none]
            exact cXi_ord_none_three exc μ ν v0 hk h3' h
          · rw [cComp0_ord_none hk, cComp1_ord_none hk, if_pos h4,
              if_pos h4, cLet_some, cLet_some]
            exact cXi_ord_none_of_ge exc μ ν v0 hk h4 h
      · rw [cComp0_ord_some hk, cComp1_ord_some hk,
          cXi_ord_exc exc μ ν v0 hk h]
        exact cXi_mark_eq_prod exc μ ν v0 p.1 p.2 0 h

end Shapes

/-! ### The named constants -/

/-- The per-cell screen bound of the tilted pair screens:
`4E'(1 + αM) + 4E'²`. -/
noncomputable def cCellBound (α : ℝ) (M E' : ℝ≥0∞) : ℝ≥0∞ :=
  4 * E' * (1 + ENNReal.ofReal α * M) + 4 * (E' * E')

/-- The one-sided bound is the priced tilt sum times the counted cell
bound. -/
lemma oneSidedBound_eq_cellBound (α : ℝ) (Tν : ℝ≥0∞) (cS : ℕ)
    (M E' : ℝ≥0∞) :
    oneSidedBound α Tν cS M E' = Tν * (cS * cCellBound α M E') := rfl

/-- The composite charged tilt sum: the inverse `α`-power of the
composite floor, summed over the charged arities. -/
noncomputable def cTiltSum (α : ℝ) (exc : ℕ → Option (ℕ × ℕ))
    (μ : PMF V) (ν : PMF ℕ) (v0 : V) : ℝ≥0∞ :=
  ∑' k, if ν k = 0 then 0 else compFloor exc μ ν v0 k ^ (-α)

/-- Under finite support the composite tilt sum is a finite sum. -/
lemma cTiltSum_eq_sum (α : ℝ) (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) {Kf : Finset ℕ}
    (hfin : ∀ k, ν k ≠ 0 → k ∈ Kf) :
    cTiltSum α exc μ ν v0
      = ∑ k ∈ Kf, if ν k = 0 then 0
          else compFloor exc μ ν v0 k ^ (-α) := by
  rw [cTiltSum]
  exact tsum_eq_finsetSum_of_support fun k hk =>
    hfin k fun h0 => hk (by rw [if_pos h0])

/-- The full member list of the fresh cell mixture over the support:
common components and exceptional marked components alike enter as
their cells. -/
noncomputable def cMemberList (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) (Kf : Finset ℕ) (h : ℕ) :
    List (PMF (FullLab (CState V) h × FullLab (CState V) h)) :=
  Kf.toList.map fun k => cXi exc μ ν v0 (CtrC.ord k) h

section Assembly

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)
variable (K1 K2 : Finset ℕ)

/-- The root degree at `v0` is charged. -/
lemma rE_root_ne_zero (hrefl0 : Rv v0 v0) (hμ0 : μ v0 ≠ 0) :
    rE μ Rv v0 ≠ 0 :=
  fun h0 => hμ0 (le_antisymm (h0 ▸ le_rE_of_refl hrefl0) zero_le)

/-- The far root mass in established form: under symmetry it is the bad
degree of the graph law at `v0`. -/
lemma farMass_eq_qE (hsymm : ∀ a b, Rv a b → Rv b a) :
    (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞)) = qE μ Rv v0 := by
  refine tsum_congr fun v => ?_
  by_cases hv : Rv v v0
  · rw [if_pos hv, if_pos (hsymm v v0 hv)]
  · rw [if_neg hv, if_neg (fun hv' => hv (hsymm v0 v hv'))]

/-- The root potential is dominated by the graph potential at the price
`μ(v0)⁻¹`; this folds the inhomogeneous row constants into `η`-terms. -/
lemma phiE_root_le (hμ0 : μ v0 ≠ 0) :
    phiE α (q μ Rv v0) ≤ (μ v0)⁻¹ * etaG α Rv μ := by
  have htop : μ v0 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (pmf_apply_le_one μ v0)
  have hcomp : μ v0 * phiE α (q μ Rv v0) ≤ etaG α Rv μ := by
    rw [etaG, PhiD]
    exact ENNReal.le_tsum v0
  calc phiE α (q μ Rv v0)
      = (μ v0)⁻¹ * (μ v0 * phiE α (q μ Rv v0)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hμ0 htop, one_mul]
    _ ≤ (μ v0)⁻¹ * etaG α Rv μ := mul_le_mul_right hcomp _

/-! ### The square cell and the forced-forced row -/

/-- **The composite square cell** (`thm:composite-ledger`, the cell
input of `thm:psi-rows`): the restricted square coordinate of two
composite cells is bounded by `cellCB` from the letter-pair ordinary
bounds `≤ M`, the reversed letter zero masses `≤ Z`, and the tilted
letter screens `≤ E'`. -/
theorem cSquare_le {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (c₁ c₂ : CtrC) (h : ℕ)
    (M Z E' : ℝ≥0∞)
    (hM : ∀ l1 l2 : Option CtrC,
      PhiDres α (cLet exc1 μ ν1 v0 l1 h) (cLet exc2 μ ν2 v0 l2 h)
          (fullSim (cRel Rv) h) ≤ M
        ∧ PhiDres α (cLet exc2 μ ν2 v0 l2 h) (cLet exc1 μ ν1 v0 l1 h)
            (fullSim (cRel Rv) h) ≤ M)
    (hZ : ∀ l1 l2 : Option CtrC,
      zMass (cLet exc2 μ ν2 v0 l2 h) (cLet exc1 μ ν1 v0 l1 h)
        (fullSim (cRel Rv) h) ≤ Z)
    (hE1 : ∀ l1 l2 l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E') :
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
    (hM (cComp0 exc1 c₁) (cComp0 exc2 c₂)).1
    (hM (cComp0 exc1 c₁) (cComp1 exc2 c₂)).1
    (hM (cComp1 exc1 c₁) (cComp0 exc2 c₂)).1
    (hM (cComp1 exc1 c₁) (cComp1 exc2 c₂)).1
    (hM (cComp0 exc1 c₁) (cComp0 exc2 c₂)).2
    (hM (cComp1 exc1 c₁) (cComp0 exc2 c₂)).2
    (hM (cComp0 exc1 c₁) (cComp1 exc2 c₂)).2
    (hM (cComp1 exc1 c₁) (cComp1 exc2 c₂)).2
    (hZ (cComp0 exc1 c₁) (cComp0 exc2 c₂))
    (hZ (cComp1 exc1 c₁) (cComp0 exc2 c₂))
    (hZ (cComp0 exc1 c₁) (cComp1 exc2 c₂))
    (hZ (cComp1 exc1 c₁) (cComp1 exc2 c₂))) ?_
  rw [cellCB]
  refine add_le_add le_rfl ?_
  refine le_trans (mul_le_mul_left (add_le_add (add_le_add (add_le_add
    (hE1 (cComp0 exc1 c₁) (cComp0 exc2 c₂) (cComp1 exc2 c₂))
    (hE1 (cComp0 exc1 c₁) (cComp1 exc2 c₂) (cComp0 exc2 c₂)))
    (hE1 (cComp1 exc1 c₁) (cComp0 exc2 c₂) (cComp1 exc2 c₂)))
    (hE1 (cComp1 exc1 c₁) (cComp1 exc2 c₂) (cComp0 exc2 c₂)))
    (1 + ENNReal.ofReal α * M)) (le_of_eq (by ring))

/-- **The frozen-frozen ordinary row** (`eq:row-ZZ`):
the height-`(h + 1)` coordinate is exactly the height-`h` square cell,
bounded by `cellCB`. -/
theorem cRow_ZZ {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hrefl0 : Rv v0 v0) (hsymm : ∀ a b, Rv a b → Rv b a)
    (cs ct : CtrC) (h : ℕ) (M Z E' : ℝ≥0∞)
    (hM : ∀ l1 l2 : Option CtrC,
      PhiDres α (cLet exc1 μ ν1 v0 l1 h) (cLet exc2 μ ν2 v0 l2 h)
          (fullSim (cRel Rv) h) ≤ M
        ∧ PhiDres α (cLet exc2 μ ν2 v0 l2 h) (cLet exc1 μ ν1 v0 l1 h)
            (fullSim (cRel Rv) h) ≤ M)
    (hZ : ∀ l1 l2 : Option CtrC,
      zMass (cLet exc2 μ ν2 v0 l2 h) (cLet exc1 μ ν1 v0 l1 h)
        (fullSim (cRel Rv) h) ≤ Z)
    (hE1 : ∀ l1 l2 l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E') :
    PhiDres α (cZ exc1 μ ν1 v0 cs (h + 1)) (cZ exc2 μ ν2 v0 ct (h + 1))
        (fullSim (cRel Rv) (h + 1))
      ≤ cellCB α δ L K M Z E' := by
  rw [cPhiDres_cZ_cZ_succ α Rv μ v0 exc1 exc2 ν1 ν2 hrefl0 cs ct h]
  exact cSquare_le α Rv μ v0 exc1 exc2 ν1 ν2 hα hδ hL0 hL hK0 hK hsymm
    cs ct h M Z E' hM hZ hE1

/-! ### The tilted pair-screen cell -/

/-- **The tilted pair-screen cell**: a pair-level cell screen with a
frozen cell dead list and a cell tilt factorizes through the survivor
split and the Hall routing into letter screens and moments, giving the
per-cell bound `cCellBound`. -/
theorem cPairScreen_tilt_le (hα : 1 ≤ α) (c₁ c₂ c₃ : CtrC) (h : ℕ)
    (M E' : ℝ≥0∞)
    (hM1 : ∀ l1 l3 : Option CtrC,
      PhiDres α (cLet exc1 μ ν1 v0 l1 h) (cLet exc2 μ ν2 v0 l3 h)
        (fullSim (cRel Rv) h) ≤ M)
    (hE1 : ∀ l1 l2 l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E')
    (hE2 : ∀ l1 l2 l2' l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h, cLet exc2 μ ν2 v0 l2' h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E') :
    screenE (cXi exc1 μ ν1 v0 c₁ h) (SquareRel (fullSim (cRel Rv) h))
        [cXi exc2 μ ν2 v0 c₂ h]
        (WresD α (cXi exc2 μ ν2 v0 c₃ h)
          (SquareRel (fullSim (cRel Rv) h)))
      ≤ cCellBound α M E' := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hmomW : ∀ l1 l3 : Option CtrC,
      (∑' x, cLet exc1 μ ν1 v0 l1 h x
        * WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h) x)
      ≤ 1 + ENNReal.ofReal α * M := fun l1 l3 =>
    le_trans (tsum_WresD_le hα _ _ _)
      (add_le_add le_rfl (mul_le_mul_right (hM1 l1 l3) _))
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
      (mul_le_mul' (hE2 (cComp0 exc1 c₁) (cComp0 exc2 c₂)
          (cComp1 exc2 c₂) (cComp0 exc2 c₃))
        (hmomW (cComp1 exc1 c₁) (cComp1 exc2 c₃)))
      (mul_le_mul' (hmomW (cComp0 exc1 c₁) (cComp0 exc2 c₃))
        (hE2 (cComp1 exc1 c₁) (cComp0 exc2 c₂)
          (cComp1 exc2 c₂) (cComp1 exc2 c₃))))
      (mul_le_mul' (hE1 (cComp0 exc1 c₁) (cComp0 exc2 c₂)
          (cComp0 exc2 c₃))
        (hE1 (cComp1 exc1 c₁) (cComp0 exc2 c₂) (cComp1 exc2 c₃))))
      (mul_le_mul' (hE1 (cComp0 exc1 c₁) (cComp1 exc2 c₂)
          (cComp0 exc2 c₃))
        (hE1 (cComp1 exc1 c₁) (cComp1 exc2 c₂) (cComp1 exc2 c₃)))
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
      (mul_le_mul' (hE2 (cComp0 exc1 c₁) (cComp0 exc2 c₂)
          (cComp1 exc2 c₂) (cComp1 exc2 c₃))
        (hmomW (cComp1 exc1 c₁) (cComp0 exc2 c₃)))
      (mul_le_mul' (hmomW (cComp0 exc1 c₁) (cComp1 exc2 c₃))
        (hE2 (cComp1 exc1 c₁) (cComp0 exc2 c₂)
          (cComp1 exc2 c₂) (cComp0 exc2 c₃))))
      (mul_le_mul' (hE1 (cComp0 exc1 c₁) (cComp0 exc2 c₂)
          (cComp1 exc2 c₃))
        (hE1 (cComp1 exc1 c₁) (cComp0 exc2 c₂) (cComp0 exc2 c₃))))
      (mul_le_mul' (hE1 (cComp0 exc1 c₁) (cComp1 exc2 c₂)
          (cComp1 exc2 c₃))
        (hE1 (cComp1 exc1 c₁) (cComp1 exc2 c₂) (cComp0 exc2 c₃)))
  refine le_trans (add_le_add horder1 horder2) (le_of_eq ?_)
  rw [cCellBound]
  ring

/-! ### The priced one-sided tilt mass and the mixture cell -/

/-- **The weighted one-sided tilt mass** (`thm:mixture-tilt-composite`
inside the row assembly): the one-sided mass of the fresh-target mixture below a
composite source cell is bounded by `oneSidedBound` with the composite
tilt sum and the support cardinality. -/
theorem cOneSided_le (hα : 1 ≤ α) (hμ0 : μ v0 ≠ 0)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hfin2 : ∀ k, ν2 k ≠ 0 → k ∈ K2)
    (c₁ : CtrC) (h : ℕ) (M E' T2 : ℝ≥0∞)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T2)
    (hM1 : ∀ l1 l3 : Option CtrC,
      PhiDres α (cLet exc1 μ ν1 v0 l1 h) (cLet exc2 μ ν2 v0 l3 h)
        (fullSim (cRel Rv) h) ≤ M)
    (hE1 : ∀ l1 l2 l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E')
    (hE2 : ∀ l1 l2 l2' l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h, cLet exc2 μ ν2 v0 l2' h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E') :
    ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if ∃ j, ν2 j ≠ 0 ∧ rE (cXi exc2 μ ν2 v0 (CtrC.ord j) h)
              (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (cXiBar exc2 μ ν2 v0 h)
              (SquareRel (fullSim (cRel Rv) h)) xp)
      ≤ oneSidedBound α T2 K2.card M E' := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hTj : ∀ j : ℕ,
      (∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * ((if ν2 j ≠ 0 ∧ rE (cXi exc2 μ ν2 v0 (CtrC.ord j) h)
              (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (cXiBar exc2 μ ν2 v0 h)
              (SquareRel (fullSim (cRel Rv) h)) xp))
      ≤ T2 * cCellBound α M E' := by
    intro j
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
    have hcell : ∀ k : ℕ,
        screenE (cXi exc1 μ ν1 v0 c₁ h)
          (SquareRel (fullSim (cRel Rv) h))
          [cXi exc2 μ ν2 v0 (CtrC.ord j) h]
          (WresD α (cXi exc2 μ ν2 v0 (CtrC.ord k) h)
            (SquareRel (fullSim (cRel Rv) h)))
        ≤ cCellBound α M E' := fun k =>
      cPairScreen_tilt_le α Rv μ v0 exc1 exc2 ν1 ν2 hα c₁ (CtrC.ord j)
        (CtrC.ord k) h M E' hM1 hE1 hE2
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
            exact mul_le_mul_right (hcell k) _
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
  refine le_trans (Finset.sum_le_sum fun j _ => hTj j) ?_
  rw [Finset.sum_const, nsmul_eq_mul, oneSidedBound_eq_cellBound]
  exact le_of_eq (by ring)

/-- **The fresh-target mixture cell**: the restricted square coordinate
toward the fresh cell mixture is bounded by the square-cell bound plus
the priced one-sided bound. -/
theorem cMix_le {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hμ0 : μ v0 ≠ 0)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hfin2 : ∀ k, ν2 k ≠ 0 → k ∈ K2)
    (c₁ : CtrC) (h : ℕ) (M Z E' T2 : ℝ≥0∞)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T2)
    (hM : ∀ l1 l2 : Option CtrC,
      PhiDres α (cLet exc1 μ ν1 v0 l1 h) (cLet exc2 μ ν2 v0 l2 h)
          (fullSim (cRel Rv) h) ≤ M
        ∧ PhiDres α (cLet exc2 μ ν2 v0 l2 h) (cLet exc1 μ ν1 v0 l1 h)
            (fullSim (cRel Rv) h) ≤ M)
    (hZ : ∀ l1 l2 : Option CtrC,
      zMass (cLet exc2 μ ν2 v0 l2 h) (cLet exc1 μ ν1 v0 l1 h)
        (fullSim (cRel Rv) h) ≤ Z)
    (hE1 : ∀ l1 l2 l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E')
    (hE2 : ∀ l1 l2 l2' l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h, cLet exc2 μ ν2 v0 l2' h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E') :
    PhiDres α (cXi exc1 μ ν1 v0 c₁ h) (cXiBar exc2 μ ν2 v0 h)
        (SquareRel (fullSim (cRel Rv) h))
      ≤ cellCB α δ L K M Z E' + oneSidedBound α T2 K2.card M E' := by
  refine le_trans (PhiDres_bind_target_le hα (cXi exc1 μ ν1 v0 c₁ h) ν2
    (fun k => cXi exc2 μ ν2 v0 (CtrC.ord k) h)
    (SquareRel (fullSim (cRel Rv) h))) (add_le_add ?_ ?_)
  · exact tsum_pmf_mul_le fun j =>
      cSquare_le α Rv μ v0 exc1 exc2 ν1 ν2 hα hδ hL0 hL hK0 hK hsymm
        c₁ (CtrC.ord j) h M Z E' hM hZ hE1
  · exact cOneSided_le α Rv μ v0 exc1 exc2 ν1 ν2 K2 hα hμ0 hpair2 hdecl2
      hfin2 c₁ h M E' T2 hT2 (fun l1 l3 => (hM l1 l3).1) hE1 hE2

/-! ### The remaining ordinary rows -/

/-- **The frozen-fresh ordinary row** (`eq:row-ZF`):
the root charge, the mixture cell, and the quadratic cross term. -/
theorem cRow_ZT {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hμ0 : μ v0 ≠ 0)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hfin2 : ∀ k, ν2 k ≠ 0 → k ∈ K2)
    (cs : CtrC) (h : ℕ) (M Z E' T2 : ℝ≥0∞)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T2)
    (hM : ∀ l1 l2 : Option CtrC,
      PhiDres α (cLet exc1 μ ν1 v0 l1 h) (cLet exc2 μ ν2 v0 l2 h)
          (fullSim (cRel Rv) h) ≤ M
        ∧ PhiDres α (cLet exc2 μ ν2 v0 l2 h) (cLet exc1 μ ν1 v0 l1 h)
            (fullSim (cRel Rv) h) ≤ M)
    (hZ : ∀ l1 l2 : Option CtrC,
      zMass (cLet exc2 μ ν2 v0 l2 h) (cLet exc1 μ ν1 v0 l1 h)
        (fullSim (cRel Rv) h) ≤ Z)
    (hE1 : ∀ l1 l2 l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E')
    (hE2 : ∀ l1 l2 l2' l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h, cLet exc2 μ ν2 v0 l2' h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E') :
    PhiDres α (cZ exc1 μ ν1 v0 cs (h + 1)) (cT exc2 μ ν2 v0 (h + 1))
        (fullSim (cRel Rv) (h + 1))
      ≤ phiE α (q μ Rv v0)
        + (cellCB α δ L K M Z E' + oneSidedBound α T2 K2.card M E')
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v0)
            * (cellCB α δ L K M Z E'
              + oneSidedBound α T2 K2.card M E')) := by
  have hmid := cMix_le α Rv μ v0 exc1 exc2 ν1 ν2 K2 hα hδ hL0 hL hK0 hK
    hsymm hμ0 hpair2 hdecl2 hfin2 cs h M Z E' T2 hT2 hM hZ hE1 hE2
  refine le_trans (cPhiDres_cZ_cT_succ α Rv μ v0 exc1 exc2 ν1 ν2 hα
    cs h) ?_
  exact add_le_add (add_le_add le_rfl hmid)
    (mul_le_mul_right (mul_le_mul_right hmid _) _)

/-- **The fresh-frozen ordinary row** (`eq:row-FZ`):
the retained `ν1`-mixture of square cells collapses into one
square-cell bound; exceptional source arities enter through their
marker cells. -/
theorem cRow_TZ {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a)
    (ct : CtrC) (h : ℕ) (M Z E' : ℝ≥0∞)
    (hM : ∀ l1 l2 : Option CtrC,
      PhiDres α (cLet exc1 μ ν1 v0 l1 h) (cLet exc2 μ ν2 v0 l2 h)
          (fullSim (cRel Rv) h) ≤ M
        ∧ PhiDres α (cLet exc2 μ ν2 v0 l2 h) (cLet exc1 μ ν1 v0 l1 h)
            (fullSim (cRel Rv) h) ≤ M)
    (hZ : ∀ l1 l2 : Option CtrC,
      zMass (cLet exc2 μ ν2 v0 l2 h) (cLet exc1 μ ν1 v0 l1 h)
        (fullSim (cRel Rv) h) ≤ Z)
    (hE1 : ∀ l1 l2 l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E') :
    PhiDres α (cT exc1 μ ν1 v0 (h + 1)) (cZ exc2 μ ν2 v0 ct (h + 1))
        (fullSim (cRel Rv) (h + 1))
      ≤ cellCB α δ L K M Z E' := by
  refine le_trans (cPhiDres_cT_cZ_succ α Rv μ v0 exc1 exc2 ν1 ν2 ct h) ?_
  exact tsum_pmf_mul_le fun k =>
    cSquare_le α Rv μ v0 exc1 exc2 ν1 ν2 hα hδ hL0 hL hK0 hK hsymm
      (CtrC.ord k) ct h M Z E' hM hZ hE1

/-- **The fresh-fresh ordinary row** (`eq:row-FF`):
the root integrates to the graph potential `etaG`, the mixture to one
mixture-cell bound, and the cross term is quadratic. -/
theorem cRow_TT {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hμ0 : μ v0 ≠ 0)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hfin2 : ∀ k, ν2 k ≠ 0 → k ∈ K2)
    (h : ℕ) (M Z E' T2 : ℝ≥0∞)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T2)
    (hM : ∀ l1 l2 : Option CtrC,
      PhiDres α (cLet exc1 μ ν1 v0 l1 h) (cLet exc2 μ ν2 v0 l2 h)
          (fullSim (cRel Rv) h) ≤ M
        ∧ PhiDres α (cLet exc2 μ ν2 v0 l2 h) (cLet exc1 μ ν1 v0 l1 h)
            (fullSim (cRel Rv) h) ≤ M)
    (hZ : ∀ l1 l2 : Option CtrC,
      zMass (cLet exc2 μ ν2 v0 l2 h) (cLet exc1 μ ν1 v0 l1 h)
        (fullSim (cRel Rv) h) ≤ Z)
    (hE1 : ∀ l1 l2 l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E')
    (hE2 : ∀ l1 l2 l2' l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h, cLet exc2 μ ν2 v0 l2' h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E') :
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
      ≤ cellCB α δ L K M Z E' + oneSidedBound α T2 K2.card M E' :=
    tsum_pmf_mul_le fun k =>
      cMix_le α Rv μ v0 exc1 exc2 ν1 ν2 K2 hα hδ hL0 hL hK0 hK hsymm hμ0
        hpair2 hdecl2 hfin2 (CtrC.ord k) h M Z E' T2 hT2 hM hZ hE1 hE2
  refine le_trans (cPhiDres_cT_cT_succ α Rv μ v0 exc1 exc2 ν1 ν2 hα h) ?_
  exact add_le_add (add_le_add le_rfl hmix)
    (mul_le_mul_right (mul_le_mul_right hmix _) _)

/-- **The ordinary base row**: at height 0 every letter-pair coordinate
is below `etaG + phiE(q(v0))`. -/
theorem cRow_base (hrefl0 : Rv v0 v0) (l1 l2 : Option CtrC) :
    PhiDres α (cLet exc1 μ ν1 v0 l1 0) (cLet exc2 μ ν2 v0 l2 0)
        (fullSim (cRel Rv) 0)
      ≤ etaG α Rv μ + phiE α (q μ Rv v0) := by
  cases l1 with
  | some c₁ =>
      cases l2 with
      | some c₂ =>
          rw [cLet_some, cLet_some,
            cPhiDres_cZ_cZ_zero α Rv μ v0 exc1 exc2 ν1 ν2 hrefl0 c₁ c₂]
          exact zero_le
      | none =>
          rw [cLet_some, cLet_none]
          exact le_trans
            (cPhiDres_cZ_cT_zero_le α Rv μ v0 exc1 exc2 ν1 ν2 c₁)
            le_add_self
  | none =>
      cases l2 with
      | some c₂ =>
          rw [cLet_none, cLet_some,
            cPhiDres_cT_cZ_zero α Rv μ v0 exc1 exc2 ν1 ν2 c₂]
          exact zero_le
      | none =>
          rw [cLet_none, cLet_none]
          exact le_trans
            (cPhiDres_cT_cT_zero_le α Rv μ v0 exc1 exc2 ν1 ν2)
            le_self_add

/-! ### The screen rows: frozen source

The height-`(h + 1)` screens of the composite ledger descend at the
root `v0` to pair-level cell screens at height `h`.  Frozen-target
singleton lists descend to the target cell, the fresh-target list to
the full member list `cMemberList`; a fresh normalization contributes
the root price `(rE μ Rv v0)^{-α}` and descends to the mixture tilt,
which `cPairScreen_price` converts into `compFloor`-priced cell
tilts. -/

/-- Frozen source, frozen dead law, unit normalization. -/
theorem cScr_ZZ_unit (hrefl0 : Rv v0 v0) (c₁ c₂ : CtrC) (h : ℕ) :
    screenE (cZ exc1 μ ν1 v0 c₁ (h + 1)) (fullSim (cRel Rv) (h + 1))
        [cZ exc2 μ ν2 v0 c₂ (h + 1)] (fun _ => 1)
      = screenE (cXi exc1 μ ν1 v0 c₁ h) (SquareRel (fullSim (cRel Rv) h))
          [cXi exc2 μ ν2 v0 c₂ h] (fun _ => 1) := by
  rw [screenE_singleton, screenE_singleton]
  exact screenG_cZ_succ Rv μ v0 exc1 exc2 ν1 ν2 v0 hrefl0 c₁ c₂ h
    (fun _ => 1)

/-- Frozen source, frozen dead law, frozen normalization. -/
theorem cScr_ZZ_tiltZ (hrefl0 : Rv v0 v0) (c₁ c₂ c₃ : CtrC) (h : ℕ) :
    screenE (cZ exc1 μ ν1 v0 c₁ (h + 1)) (fullSim (cRel Rv) (h + 1))
        [cZ exc2 μ ν2 v0 c₂ (h + 1)]
        (WresD α (cZ exc2 μ ν2 v0 c₃ (h + 1)) (fullSim (cRel Rv) (h + 1)))
      = screenE (cXi exc1 μ ν1 v0 c₁ h) (SquareRel (fullSim (cRel Rv) h))
          [cXi exc2 μ ν2 v0 c₂ h]
          (WresD α (cXi exc2 μ ν2 v0 c₃ h)
            (SquareRel (fullSim (cRel Rv) h))) := by
  rw [screenE_singleton, screenE_singleton]
  refine Eq.trans (screenG_cZ_succ Rv μ v0 exc1 exc2 ν1 ν2 v0 hrefl0
    c₁ c₂ h (WresD α (cZ exc2 μ ν2 v0 c₃ (h + 1))
      (fullSim (cRel Rv) (h + 1)))) ?_
  refine tsum_congr fun xp => ?_
  have hW := WresD_cZ_succ_branch exc2 μ ν2 v0 Rv α v0 c₁ c₃ h xp
  rw [if_pos hrefl0] at hW
  rw [hW]

/-- Frozen source, frozen dead law, fresh normalization: the root
price times the mixture-tilted cell screen. -/
theorem cScr_ZZ_tiltT (hrefl0 : Rv v0 v0) (hμ0 : μ v0 ≠ 0)
    (c₁ c₂ : CtrC) (h : ℕ) :
    screenE (cZ exc1 μ ν1 v0 c₁ (h + 1)) (fullSim (cRel Rv) (h + 1))
        [cZ exc2 μ ν2 v0 c₂ (h + 1)]
        (WresD α (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1)))
      = (rE μ Rv v0) ^ (-α)
        * screenE (cXi exc1 μ ν1 v0 c₁ h)
            (SquareRel (fullSim (cRel Rv) h)) [cXi exc2 μ ν2 v0 c₂ h]
            (WresD α (cXiBar exc2 μ ν2 v0 h)
              (SquareRel (fullSim (cRel Rv) h))) := by
  have hvpos := rE_root_ne_zero Rv μ v0 hrefl0 hμ0
  rw [screenE_singleton, screenE_singleton, ← ENNReal.tsum_mul_left]
  refine Eq.trans (screenG_cZ_succ Rv μ v0 exc1 exc2 ν1 ν2 v0 hrefl0
    c₁ c₂ h (WresD α (cT exc2 μ ν2 v0 (h + 1))
      (fullSim (cRel Rv) (h + 1)))) ?_
  refine tsum_congr fun xp => ?_
  rw [WresD_cT_succ_branch exc2 μ ν2 v0 Rv α hvpos c₁ h xp]
  ring

/-- The mixture-dead event is the dead event of the full member
list. -/
lemma rE_cXiBar_eq_zero_iff_memberList
    (hsupp2 : ∀ k, ν2 k ≠ 0 ↔ k ∈ K2) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cXiBar exc2 μ ν2 v0 h) (SquareRel (fullSim (cRel Rv) h)) xp = 0
      ↔ ∀ ρ ∈ cMemberList exc2 μ ν2 v0 K2 h,
          rE ρ (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
  rw [rE_cXiBar_eq_zero_iff_charged exc2 μ ν2 v0 h
    (SquareRel (fullSim (cRel Rv) h)) xp]
  constructor
  · intro hall ρ hρ
    simp only [cMemberList, List.mem_map, Finset.mem_toList] at hρ
    obtain ⟨k, hk, rfl⟩ := hρ
    exact hall k ((hsupp2 k).mpr hk)
  · intro hall k hk
    refine hall _ ?_
    simp only [cMemberList, List.mem_map, Finset.mem_toList]
    exact ⟨k, (hsupp2 k).mp hk, rfl⟩

/-- Frozen source, fresh dead law, unit normalization: the descended
zero list is the full member list over the support `K2`. -/
theorem cScr_ZT_unit (hrefl0 : Rv v0 v0) (hμ0 : μ v0 ≠ 0)
    (hsupp2 : ∀ k, ν2 k ≠ 0 ↔ k ∈ K2) (c₁ : CtrC) (h : ℕ) :
    screenE (cZ exc1 μ ν1 v0 c₁ (h + 1)) (fullSim (cRel Rv) (h + 1))
        [cT exc2 μ ν2 v0 (h + 1)] (fun _ => 1)
      = screenE (cXi exc1 μ ν1 v0 c₁ h) (SquareRel (fullSim (cRel Rv) h))
          (cMemberList exc2 μ ν2 v0 K2 h) (fun _ => 1) := by
  have hvpos := rE_root_ne_zero Rv μ v0 hrefl0 hμ0
  rw [screenE_singleton, screenE]
  refine Eq.trans (screenG_cT_succ Rv μ v0 exc1 exc2 ν1 ν2 v0 hvpos c₁ h
    (fun _ => 1)) ?_
  refine tsum_congr fun xp => ?_
  have hind : (if rE (cXiBar exc2 μ ν2 v0 h)
        (SquareRel (fullSim (cRel Rv) h)) xp = 0 then (1 : ℝ≥0∞) else 0)
      = screenInd (SquareRel (fullSim (cRel Rv) h))
          (cMemberList exc2 μ ν2 v0 K2 h) xp := by
    rw [screenInd]
    exact if_congr (rE_cXiBar_eq_zero_iff_memberList Rv μ v0 exc2 ν2 K2
      hsupp2 h xp) rfl rfl
  rw [hind]
  simp only [mul_one]

/-- Frozen source, fresh dead law, frozen normalization. -/
theorem cScr_ZT_tiltZ (hrefl0 : Rv v0 v0) (hμ0 : μ v0 ≠ 0)
    (hsupp2 : ∀ k, ν2 k ≠ 0 ↔ k ∈ K2) (c₁ c₃ : CtrC) (h : ℕ) :
    screenE (cZ exc1 μ ν1 v0 c₁ (h + 1)) (fullSim (cRel Rv) (h + 1))
        [cT exc2 μ ν2 v0 (h + 1)]
        (WresD α (cZ exc2 μ ν2 v0 c₃ (h + 1)) (fullSim (cRel Rv) (h + 1)))
      = screenE (cXi exc1 μ ν1 v0 c₁ h) (SquareRel (fullSim (cRel Rv) h))
          (cMemberList exc2 μ ν2 v0 K2 h)
          (WresD α (cXi exc2 μ ν2 v0 c₃ h)
            (SquareRel (fullSim (cRel Rv) h))) := by
  have hvpos := rE_root_ne_zero Rv μ v0 hrefl0 hμ0
  rw [screenE_singleton, screenE]
  refine Eq.trans (screenG_cT_succ Rv μ v0 exc1 exc2 ν1 ν2 v0 hvpos c₁ h
    (WresD α (cZ exc2 μ ν2 v0 c₃ (h + 1))
      (fullSim (cRel Rv) (h + 1)))) ?_
  refine tsum_congr fun xp => ?_
  have hW := WresD_cZ_succ_branch exc2 μ ν2 v0 Rv α v0 c₁ c₃ h xp
  rw [if_pos hrefl0] at hW
  have hind : (if rE (cXiBar exc2 μ ν2 v0 h)
        (SquareRel (fullSim (cRel Rv) h)) xp = 0 then (1 : ℝ≥0∞) else 0)
      = screenInd (SquareRel (fullSim (cRel Rv) h))
          (cMemberList exc2 μ ν2 v0 K2 h) xp := by
    rw [screenInd]
    exact if_congr (rE_cXiBar_eq_zero_iff_memberList Rv μ v0 exc2 ν2 K2
      hsupp2 h xp) rfl rfl
  rw [hW, hind, mul_assoc]

/-- Frozen source, fresh dead law, fresh normalization: the root price
times the mixture-tilted member-list screen. -/
theorem cScr_ZT_tiltT (hrefl0 : Rv v0 v0) (hμ0 : μ v0 ≠ 0)
    (hsupp2 : ∀ k, ν2 k ≠ 0 ↔ k ∈ K2) (c₁ : CtrC) (h : ℕ) :
    screenE (cZ exc1 μ ν1 v0 c₁ (h + 1)) (fullSim (cRel Rv) (h + 1))
        [cT exc2 μ ν2 v0 (h + 1)]
        (WresD α (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1)))
      = (rE μ Rv v0) ^ (-α)
        * screenE (cXi exc1 μ ν1 v0 c₁ h)
            (SquareRel (fullSim (cRel Rv) h))
            (cMemberList exc2 μ ν2 v0 K2 h)
            (WresD α (cXiBar exc2 μ ν2 v0 h)
              (SquareRel (fullSim (cRel Rv) h))) := by
  have hvpos := rE_root_ne_zero Rv μ v0 hrefl0 hμ0
  rw [screenE_singleton, screenE, ← ENNReal.tsum_mul_left]
  refine Eq.trans (screenG_cT_succ Rv μ v0 exc1 exc2 ν1 ν2 v0 hvpos c₁ h
    (WresD α (cT exc2 μ ν2 v0 (h + 1))
      (fullSim (cRel Rv) (h + 1)))) ?_
  refine tsum_congr fun xp => ?_
  have hind : (if rE (cXiBar exc2 μ ν2 v0 h)
        (SquareRel (fullSim (cRel Rv) h)) xp = 0 then (1 : ℝ≥0∞) else 0)
      = screenInd (SquareRel (fullSim (cRel Rv) h))
          (cMemberList exc2 μ ν2 v0 K2 h) xp := by
    rw [screenInd]
    exact if_congr (rE_cXiBar_eq_zero_iff_memberList Rv μ v0 exc2 ν2 K2
      hsupp2 h xp) rfl rfl
  rw [WresD_cT_succ_branch exc2 μ ν2 v0 Rv α hvpos c₁ h xp, hind]
  ring

/-! ### The screen rows: fresh source -/

/-- Fresh source, frozen dead law, unit normalization: far roots inject
into the far mass, near roots contribute the retained `ν1`-mixture of
pair-level cell screens over the support `K1`. -/
theorem cScr_TZ_unit (hfin1 : ∀ k, ν1 k ≠ 0 → k ∈ K1) (c₂ : CtrC)
    (h : ℕ) (FM : ℝ≥0∞)
    (hFM : (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞)) ≤ FM) :
    screenE (cT exc1 μ ν1 v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
        [cZ exc2 μ ν2 v0 c₂ (h + 1)] (fun _ => 1)
      ≤ FM + ∑ k ∈ K1, ν1 k
          * screenE (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
              (SquareRel (fullSim (cRel Rv) h))
              [cXi exc2 μ ν2 v0 c₂ h] (fun _ => 1) := by
  rw [cT_eq_freshQ_bind exc1 μ ν1 v0 (h + 1), screenE_bind_left]
  have hpt : ∀ s : V × ℕ,
      freshQ μ ν1 s
        * screenE (muM (compK exc1 μ ν1 v0) (s.1, CtrC.ord s.2) (h + 1))
            (fullSim (cRel Rv) (h + 1)) [cZ exc2 μ ν2 v0 c₂ (h + 1)]
            (fun _ => 1)
      ≤ (if Rv s.1 v0 then 0 else freshQ μ ν1 s)
        + freshQ μ ν1 s
          * screenE (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
              (SquareRel (fullSim (cRel Rv) h))
              [cXi exc2 μ ν2 v0 c₂ h] (fun _ => 1) := by
    rintro ⟨w, k⟩
    by_cases hw : Rv w v0
    · rw [if_pos hw, zero_add]
      refine mul_le_mul_right (le_of_eq ?_) _
      rw [screenE_singleton, screenE_singleton]
      exact screenG_cZ_succ Rv μ v0 exc1 exc2 ν1 ν2 w hw (CtrC.ord k)
        c₂ h (fun _ => 1)
    · rw [if_neg hw]
      refine le_trans ?_ le_self_add
      exact le_trans (mul_le_mul_right (screenE_unit_le_one _ _ _) _)
        (le_of_eq (mul_one _))
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_add]
  refine add_le_add ?_ ?_
  · calc ∑' s : V × ℕ, (if Rv s.1 v0 then 0 else freshQ μ ν1 s)
        = ∑' s : V × ℕ,
            (if Rv s.1 v0 then 0 else (μ s.1 : ℝ≥0∞)) * ν1 s.2 := by
          refine tsum_congr fun s => ?_
          by_cases hv : Rv s.1 v0
          · rw [if_pos hv, if_pos hv, zero_mul]
          · rw [if_neg hv, if_neg hv]
            exact prodPMF_apply μ ν1 s
      _ = (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞))
          * ∑' l, (ν1 l : ℝ≥0∞) :=
          tsum_prod_split (fun v => if Rv v v0 then 0 else (μ v : ℝ≥0∞))
            (fun l => (ν1 l : ℝ≥0∞))
      _ ≤ FM := by
          rw [ν1.tsum_coe, mul_one]
          exact hFM
  · have hsplit : (∑' s : V × ℕ, freshQ μ ν1 s
        * screenE (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
            (SquareRel (fullSim (cRel Rv) h))
            [cXi exc2 μ ν2 v0 c₂ h] (fun _ => 1))
        = ∑' k, ν1 k
          * screenE (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
              (SquareRel (fullSim (cRel Rv) h))
              [cXi exc2 μ ν2 v0 c₂ h] (fun _ => 1) := by
      rw [tsum_congr fun s : V × ℕ => show freshQ μ ν1 s
          * screenE (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
              (SquareRel (fullSim (cRel Rv) h))
              [cXi exc2 μ ν2 v0 c₂ h] (fun _ => 1)
          = (μ s.1 : ℝ≥0∞) * (ν1 s.2
              * screenE (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
                  (SquareRel (fullSim (cRel Rv) h))
                  [cXi exc2 μ ν2 v0 c₂ h] (fun _ => 1)) from by
        rw [show freshQ μ ν1 s = μ s.1 * ν1 s.2 from prodPMF_apply μ ν1 s,
          mul_assoc],
        tsum_prod_split (fun v => (μ v : ℝ≥0∞))
          (fun k => ν1 k
            * screenE (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
                (SquareRel (fullSim (cRel Rv) h))
                [cXi exc2 μ ν2 v0 c₂ h] (fun _ => 1)),
        PMF.tsum_coe, one_mul]
    rw [hsplit]
    refine le_of_eq (tsum_eq_finsetSum_of_support fun k hk => ?_)
    refine hfin1 k fun h0 => hk ?_
    rw [h0, zero_mul]

/-- Fresh source, frozen dead law, frozen normalization: the frozen
tilt kills far roots, and the near roots contribute the retained
`ν1`-mixture of tilted cell screens. -/
theorem cScr_TZ_tiltZ (hfin1 : ∀ k, ν1 k ≠ 0 → k ∈ K1) (c₂ c₃ : CtrC)
    (h : ℕ) :
    screenE (cT exc1 μ ν1 v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
        [cZ exc2 μ ν2 v0 c₂ (h + 1)]
        (WresD α (cZ exc2 μ ν2 v0 c₃ (h + 1)) (fullSim (cRel Rv) (h + 1)))
      ≤ ∑ k ∈ K1, ν1 k
          * screenE (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
              (SquareRel (fullSim (cRel Rv) h))
              [cXi exc2 μ ν2 v0 c₂ h]
              (WresD α (cXi exc2 μ ν2 v0 c₃ h)
                (SquareRel (fullSim (cRel Rv) h))) := by
  rw [cT_eq_freshQ_bind exc1 μ ν1 v0 (h + 1), screenE_bind_left]
  have hpt : ∀ s : V × ℕ,
      freshQ μ ν1 s
        * screenE (muM (compK exc1 μ ν1 v0) (s.1, CtrC.ord s.2) (h + 1))
            (fullSim (cRel Rv) (h + 1)) [cZ exc2 μ ν2 v0 c₂ (h + 1)]
            (WresD α (cZ exc2 μ ν2 v0 c₃ (h + 1))
              (fullSim (cRel Rv) (h + 1)))
      ≤ freshQ μ ν1 s
        * screenE (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
            (SquareRel (fullSim (cRel Rv) h))
            [cXi exc2 μ ν2 v0 c₂ h]
            (WresD α (cXi exc2 μ ν2 v0 c₃ h)
              (SquareRel (fullSim (cRel Rv) h))) := by
    rintro ⟨w, k⟩
    by_cases hw : Rv w v0
    · refine mul_le_mul_right (le_of_eq ?_) _
      rw [screenE_singleton, screenE_singleton]
      refine Eq.trans (screenG_cZ_succ Rv μ v0 exc1 exc2 ν1 ν2 w hw
        (CtrC.ord k) c₂ h (WresD α (cZ exc2 μ ν2 v0 c₃ (h + 1))
          (fullSim (cRel Rv) (h + 1)))) ?_
      refine tsum_congr fun xp => ?_
      have hW := WresD_cZ_succ_branch exc2 μ ν2 v0 Rv α w
        (CtrC.ord k) c₃ h xp
      rw [if_pos hw] at hW
      rw [hW]
    · have hzero : screenE
          (muM (compK exc1 μ ν1 v0) (w, CtrC.ord k) (h + 1))
          (fullSim (cRel Rv) (h + 1)) [cZ exc2 μ ν2 v0 c₂ (h + 1)]
          (WresD α (cZ exc2 μ ν2 v0 c₃ (h + 1))
            (fullSim (cRel Rv) (h + 1))) = 0 := by
        rw [screenE_singleton]
        refine Eq.trans (screenG_cZ_succ_far Rv μ v0 exc1 exc2 ν1 ν2 w hw
          (CtrC.ord k) c₂ h (WresD α (cZ exc2 μ ν2 v0 c₃ (h + 1))
            (fullSim (cRel Rv) (h + 1)))) ?_
        refine ENNReal.tsum_eq_zero.mpr fun xp => ?_
        have hW := WresD_cZ_succ_branch exc2 μ ν2 v0 Rv α w
          (CtrC.ord k) c₃ h xp
        rw [if_neg hw] at hW
        rw [hW, mul_zero]
      rw [hzero, mul_zero]
      exact zero_le
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  have hsplit : (∑' s : V × ℕ, freshQ μ ν1 s
      * screenE (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
          (SquareRel (fullSim (cRel Rv) h)) [cXi exc2 μ ν2 v0 c₂ h]
          (WresD α (cXi exc2 μ ν2 v0 c₃ h)
            (SquareRel (fullSim (cRel Rv) h))))
      = ∑' k, ν1 k
        * screenE (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
            (SquareRel (fullSim (cRel Rv) h)) [cXi exc2 μ ν2 v0 c₂ h]
            (WresD α (cXi exc2 μ ν2 v0 c₃ h)
              (SquareRel (fullSim (cRel Rv) h))) := by
    rw [tsum_congr fun s : V × ℕ => show freshQ μ ν1 s
        * screenE (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
            (SquareRel (fullSim (cRel Rv) h)) [cXi exc2 μ ν2 v0 c₂ h]
            (WresD α (cXi exc2 μ ν2 v0 c₃ h)
              (SquareRel (fullSim (cRel Rv) h)))
        = (μ s.1 : ℝ≥0∞) * (ν1 s.2
            * screenE (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
                (SquareRel (fullSim (cRel Rv) h))
                [cXi exc2 μ ν2 v0 c₂ h]
                (WresD α (cXi exc2 μ ν2 v0 c₃ h)
                  (SquareRel (fullSim (cRel Rv) h)))) from by
      rw [show freshQ μ ν1 s = μ s.1 * ν1 s.2 from prodPMF_apply μ ν1 s,
        mul_assoc],
      tsum_prod_split (fun v => (μ v : ℝ≥0∞))
        (fun k => ν1 k
          * screenE (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
              (SquareRel (fullSim (cRel Rv) h)) [cXi exc2 μ ν2 v0 c₂ h]
              (WresD α (cXi exc2 μ ν2 v0 c₃ h)
                (SquareRel (fullSim (cRel Rv) h)))),
      PMF.tsum_coe, one_mul]
  rw [hsplit]
  refine le_of_eq (tsum_eq_finsetSum_of_support fun k hk => ?_)
  refine hfin1 k fun h0 => hk ?_
  rw [h0, zero_mul]

/-- The near-root degree is charged: a root compatible with `v0`
carries at least the mass of `v0`. -/
lemma rE_near_ne_zero (hμ0 : μ v0 ≠ 0) {w : V} (hw : Rv w v0) :
    rE μ Rv w ≠ 0 := by
  intro h0
  apply hμ0
  rw [rE] at h0
  have hterm := ENNReal.tsum_eq_zero.mp h0 v0
  rw [if_pos hw] at hterm
  exact hterm

/-- The pair-moment constant `2(1 + αM)²` of the untied mixture
moment. -/
noncomputable def cPairMoment (α : ℝ) (M : ℝ≥0∞) : ℝ≥0∞ :=
  2 * ((1 + ENNReal.ofReal α * M) * (1 + ENNReal.ofReal α * M))

/-- The untied cell-tilted moment of a source cell: the survivor split
into two ordered products of letter moments. -/
lemma cPairMoment_le (hα : 1 ≤ α) (c₁ c₂ : CtrC) (h : ℕ) (M : ℝ≥0∞)
    (hM1 : ∀ l1 l3 : Option CtrC,
      PhiDres α (cLet exc1 μ ν1 v0 l1 h) (cLet exc2 μ ν2 v0 l3 h)
        (fullSim (cRel Rv) h) ≤ M) :
    ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * WresD α (cXi exc2 μ ν2 v0 c₂ h)
            (SquareRel (fullSim (cRel Rv) h)) xp
      ≤ cPairMoment α M := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hmomW : ∀ l1 l3 : Option CtrC,
      (∑' x, cLet exc1 μ ν1 v0 l1 h x
        * WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h) x)
      ≤ 1 + ENNReal.ofReal α * M := fun l1 l3 =>
    le_trans (tsum_WresD_le hα _ _ _)
      (add_le_add le_rfl (mul_le_mul_right (hM1 l1 l3) _))
  rw [cXi_eq_prod exc1 μ ν1 v0 c₁ h, cXi_eq_prod exc2 μ ν2 v0 c₂ h]
  set ρa := cLet exc1 μ ν1 v0 (cComp0 exc1 c₁) h with hρa
  set ρb := cLet exc1 μ ν1 v0 (cComp1 exc1 c₁) h with hρb
  set ρe := cLet exc2 μ ν2 v0 (cComp0 exc2 c₂) h with hρe
  set ρf := cLet exc2 μ ν2 v0 (cComp1 exc2 c₂) h with hρf
  calc ∑' xp, prodPMF ρa ρb xp
        * WresD α (prodPMF ρe ρf) (SquareRel (fullSim (cRel Rv) h)) xp
      ≤ ∑' xp : FullLab (CState V) h × FullLab (CState V) h,
          (prodPMF ρa ρb xp
              * (WresD α ρe (fullSim (cRel Rv) h) xp.1
                * WresD α ρf (fullSim (cRel Rv) h) xp.2)
            + prodPMF ρa ρb xp
              * (WresD α ρf (fullSim (cRel Rv) h) xp.1
                * WresD α ρe (fullSim (cRel Rv) h) xp.2)) := by
        refine ENNReal.tsum_le_tsum fun xp => ?_
        calc prodPMF ρa ρb xp
              * WresD α (prodPMF ρe ρf)
                  (SquareRel (fullSim (cRel Rv) h)) xp
            ≤ prodPMF ρa ρb xp
                * (WresD α ρe (fullSim (cRel Rv) h) xp.1
                    * WresD α ρf (fullSim (cRel Rv) h) xp.2
                  + WresD α ρf (fullSim (cRel Rv) h) xp.1
                    * WresD α ρe (fullSim (cRel Rv) h) xp.2) :=
              mul_le_mul_right
                (WresD_square_le_sum hα0 ρe ρf (fullSim (cRel Rv) h) xp) _
          _ = prodPMF ρa ρb xp
                * (WresD α ρe (fullSim (cRel Rv) h) xp.1
                  * WresD α ρf (fullSim (cRel Rv) h) xp.2)
              + prodPMF ρa ρb xp
                * (WresD α ρf (fullSim (cRel Rv) h) xp.1
                  * WresD α ρe (fullSim (cRel Rv) h) xp.2) := by ring
    _ = (∑' xp : FullLab (CState V) h × FullLab (CState V) h,
          prodPMF ρa ρb xp
            * (WresD α ρe (fullSim (cRel Rv) h) xp.1
              * WresD α ρf (fullSim (cRel Rv) h) xp.2))
        + ∑' xp : FullLab (CState V) h × FullLab (CState V) h,
            prodPMF ρa ρb xp
              * (WresD α ρf (fullSim (cRel Rv) h) xp.1
                * WresD α ρe (fullSim (cRel Rv) h) xp.2) :=
        ENNReal.tsum_add
    _ ≤ (1 + ENNReal.ofReal α * M) * (1 + ENNReal.ofReal α * M)
        + (1 + ENNReal.ofReal α * M) * (1 + ENNReal.ofReal α * M) := by
        refine add_le_add ?_ ?_
        · rw [tsum_congr fun xp : FullLab (CState V) h × FullLab (CState V) h
              => show prodPMF ρa ρb xp
                * (WresD α ρe (fullSim (cRel Rv) h) xp.1
                  * WresD α ρf (fullSim (cRel Rv) h) xp.2)
              = (ρa xp.1 * WresD α ρe (fullSim (cRel Rv) h) xp.1)
                * (ρb xp.2 * WresD α ρf (fullSim (cRel Rv) h) xp.2) from by
                rw [prodPMF_apply]; ring,
            tsum_prod_split
              (fun x => ρa x * WresD α ρe (fullSim (cRel Rv) h) x)
              (fun x => ρb x * WresD α ρf (fullSim (cRel Rv) h) x)]
          exact mul_le_mul'
            (hmomW (cComp0 exc1 c₁) (cComp0 exc2 c₂))
            (hmomW (cComp1 exc1 c₁) (cComp1 exc2 c₂))
        · rw [tsum_congr fun xp : FullLab (CState V) h × FullLab (CState V) h
              => show prodPMF ρa ρb xp
                * (WresD α ρf (fullSim (cRel Rv) h) xp.1
                  * WresD α ρe (fullSim (cRel Rv) h) xp.2)
              = (ρa xp.1 * WresD α ρf (fullSim (cRel Rv) h) xp.1)
                * (ρb xp.2 * WresD α ρe (fullSim (cRel Rv) h) xp.2) from by
                rw [prodPMF_apply]; ring,
            tsum_prod_split
              (fun x => ρa x * WresD α ρf (fullSim (cRel Rv) h) x)
              (fun x => ρb x * WresD α ρe (fullSim (cRel Rv) h) x)]
          exact mul_le_mul'
            (hmomW (cComp0 exc1 c₁) (cComp1 exc2 c₂))
            (hmomW (cComp1 exc1 c₁) (cComp0 exc2 c₂))
    _ = cPairMoment α M := by rw [cPairMoment]; ring

/-- The untied mixture-tilted moment: the composite prices convert the
mixture tilt into cell tilts, each bounded by the pair moment. -/
lemma cMixMoment_le (hα : 1 ≤ α) (hμ0 : μ v0 ≠ 0)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (c₁ : CtrC) (h : ℕ) (M T2 : ℝ≥0∞)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T2)
    (hM1 : ∀ l1 l3 : Option CtrC,
      PhiDres α (cLet exc1 μ ν1 v0 l1 h) (cLet exc2 μ ν2 v0 l3 h)
        (fullSim (cRel Rv) h) ≤ M) :
    ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
        * WresD α (cXiBar exc2 μ ν2 v0 h)
            (SquareRel (fullSim (cRel Rv) h)) xp
      ≤ T2 * cPairMoment α M := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  refine le_trans (tsum_WresD_cXiBar_le_sum exc2 μ ν2 v0 hpair2 hdecl2
    hμ0 hα0 Rv h (cXi exc1 μ ν1 v0 c₁ h)) ?_
  calc ∑' k, (if ν2 k = 0 then 0 else
        compFloor exc2 μ ν2 v0 k ^ (-α)
          * ∑' xp, cXi exc1 μ ν1 v0 c₁ h xp
              * WresD α (cXi exc2 μ ν2 v0 (CtrC.ord k) h)
                  (SquareRel (fullSim (cRel Rv) h)) xp)
      ≤ ∑' k, (if ν2 k = 0 then 0 else
          compFloor exc2 μ ν2 v0 k ^ (-α)) * cPairMoment α M := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        by_cases hk : ν2 k = 0
        · rw [if_pos hk, if_pos hk, zero_mul]
        · rw [if_neg hk, if_neg hk]
          exact mul_le_mul_right (cPairMoment_le α Rv μ v0 exc1 exc2
            ν1 ν2 hα c₁ (CtrC.ord k) h M hM1) _
    _ = (∑' k, (if ν2 k = 0 then 0 else
          compFloor exc2 μ ν2 v0 k ^ (-α))) * cPairMoment α M :=
        ENNReal.tsum_mul_right
    _ ≤ T2 * cPairMoment α M := mul_le_mul_left hT2 _

/-- **The mixture-tilted pair screen**: a pair-level cell screen with
the fresh-target mixture tilt is bounded by the priced cell bound. -/
theorem cPairScreen_mix_le (hα : 1 ≤ α) (hμ0 : μ v0 ≠ 0)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (c₁ c₂ : CtrC) (h : ℕ) (M E' T2 : ℝ≥0∞)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T2)
    (hM1 : ∀ l1 l3 : Option CtrC,
      PhiDres α (cLet exc1 μ ν1 v0 l1 h) (cLet exc2 μ ν2 v0 l3 h)
        (fullSim (cRel Rv) h) ≤ M)
    (hE1 : ∀ l1 l2 l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E')
    (hE2 : ∀ l1 l2 l2' l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h, cLet exc2 μ ν2 v0 l2' h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E') :
    screenE (cXi exc1 μ ν1 v0 c₁ h) (SquareRel (fullSim (cRel Rv) h))
        [cXi exc2 μ ν2 v0 c₂ h]
        (WresD α (cXiBar exc2 μ ν2 v0 h)
          (SquareRel (fullSim (cRel Rv) h)))
      ≤ T2 * cCellBound α M E' := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  refine le_trans (screenE_WresD_cXiBar_le_sum exc2 μ ν2 v0 hpair2 hdecl2
    hμ0 hα0 Rv h (cXi exc1 μ ν1 v0 c₁ h)
    [cXi exc2 μ ν2 v0 c₂ h]) ?_
  calc ∑' k, (if ν2 k = 0 then 0 else
        compFloor exc2 μ ν2 v0 k ^ (-α)
          * screenE (cXi exc1 μ ν1 v0 c₁ h)
              (SquareRel (fullSim (cRel Rv) h))
              [cXi exc2 μ ν2 v0 c₂ h]
              (WresD α (cXi exc2 μ ν2 v0 (CtrC.ord k) h)
                (SquareRel (fullSim (cRel Rv) h))))
      ≤ ∑' k, (if ν2 k = 0 then 0 else
          compFloor exc2 μ ν2 v0 k ^ (-α)) * cCellBound α M E' := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        by_cases hk : ν2 k = 0
        · rw [if_pos hk, if_pos hk, zero_mul]
        · rw [if_neg hk, if_neg hk]
          exact mul_le_mul_right (cPairScreen_tilt_le α Rv μ v0 exc1 exc2
            ν1 ν2 hα c₁ c₂ (CtrC.ord k) h M E' hM1 hE1 hE2) _
    _ = (∑' k, (if ν2 k = 0 then 0 else
          compFloor exc2 μ ν2 v0 k ^ (-α))) * cCellBound α M E' :=
        ENNReal.tsum_mul_right
    _ ≤ T2 * cCellBound α M E' := mul_le_mul_left hT2 _

/-- Fresh source, frozen dead law, fresh normalization: far roots
inject into the fresh-tilted far mass `FT` at the priced pair moment,
near roots into the root price `RT` times the priced cell bound. -/
theorem cScr_TZ_tiltT (hα : 1 ≤ α) (hμ0 : μ v0 ≠ 0)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (c₂ : CtrC) (h : ℕ) (M E' T2 RT FT : ℝ≥0∞)
    (hT2 : cTiltSum α exc2 μ ν2 v0 ≤ T2)
    (hRT : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    (hFT : (∑' v, if Rv v v0 then 0
        else (μ v : ℝ≥0∞) * WresD α μ Rv v) ≤ FT)
    (hM1 : ∀ l1 l3 : Option CtrC,
      PhiDres α (cLet exc1 μ ν1 v0 l1 h) (cLet exc2 μ ν2 v0 l3 h)
        (fullSim (cRel Rv) h) ≤ M)
    (hE1 : ∀ l1 l2 l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E')
    (hE2 : ∀ l1 l2 l2' l3 : Option CtrC,
      screenE (cLet exc1 μ ν1 v0 l1 h) (fullSim (cRel Rv) h)
        [cLet exc2 μ ν2 v0 l2 h, cLet exc2 μ ν2 v0 l2' h]
        (WresD α (cLet exc2 μ ν2 v0 l3 h) (fullSim (cRel Rv) h)) ≤ E') :
    screenE (cT exc1 μ ν1 v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
        [cZ exc2 μ ν2 v0 c₂ (h + 1)]
        (WresD α (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1)))
      ≤ FT * (T2 * cPairMoment α M)
        + RT * (T2 * cCellBound α M E') := by
  rw [cT_eq_freshQ_bind exc1 μ ν1 v0 (h + 1), screenE_bind_left]
  have hpt : ∀ s : V × ℕ,
      freshQ μ ν1 s
        * screenE (muM (compK exc1 μ ν1 v0) (s.1, CtrC.ord s.2) (h + 1))
            (fullSim (cRel Rv) (h + 1)) [cZ exc2 μ ν2 v0 c₂ (h + 1)]
            (WresD α (cT exc2 μ ν2 v0 (h + 1))
              (fullSim (cRel Rv) (h + 1)))
      ≤ (if Rv s.1 v0 then 0
          else (μ s.1 : ℝ≥0∞) * WresD α μ Rv s.1
            * (T2 * cPairMoment α M) * ν1 s.2)
        + freshQ μ ν1 s * (RT * (T2 * cCellBound α M E')) := by
    rintro ⟨w, k⟩
    by_cases hw : Rv w v0
    · rw [if_pos hw, zero_add]
      refine mul_le_mul_right ?_ _
      have hvpos : rE μ Rv w ≠ 0 := rE_near_ne_zero Rv μ v0 hμ0 hw
      rw [screenE_singleton]
      refine le_trans (le_of_eq (screenG_cZ_succ Rv μ v0 exc1 exc2 ν1 ν2
        w hw (CtrC.ord k) c₂ h (WresD α (cT exc2 μ ν2 v0 (h + 1))
          (fullSim (cRel Rv) (h + 1))))) ?_
      calc ∑' xp, cXi exc1 μ ν1 v0 (CtrC.ord k) h xp
            * ((if rE (cXi exc2 μ ν2 v0 c₂ h)
                  (SquareRel (fullSim (cRel Rv) h)) xp = 0
                then 1 else 0)
              * WresD α (cT exc2 μ ν2 v0 (h + 1))
                  (fullSim (cRel Rv) (h + 1))
                  (branch (w, CtrC.ord k) xp))
          = (rE μ Rv w) ^ (-α)
            * ∑' xp, cXi exc1 μ ν1 v0 (CtrC.ord k) h xp
                * ((if rE (cXi exc2 μ ν2 v0 c₂ h)
                      (SquareRel (fullSim (cRel Rv) h)) xp = 0
                    then 1 else 0)
                  * WresD α (cXiBar exc2 μ ν2 v0 h)
                      (SquareRel (fullSim (cRel Rv) h)) xp) := by
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun xp => ?_
            rw [WresD_cT_succ_branch exc2 μ ν2 v0 Rv α hvpos
              (CtrC.ord k) h xp]
            ring
        _ ≤ RT * (T2 * cCellBound α M E') := by
            refine mul_le_mul' (hRT w hw) ?_
            rw [← screenE_singleton]
            exact cPairScreen_mix_le α Rv μ v0 exc1 exc2 ν1 ν2 hα hμ0
              hpair2 hdecl2 (CtrC.ord k) c₂ h M E' T2 hT2 hM1 hE1 hE2
    · rw [if_neg hw]
      refine le_trans ?_ le_self_add
      by_cases hvr : rE μ Rv w = 0
      · have hz : screenE
            (muM (compK exc1 μ ν1 v0) (w, CtrC.ord k) (h + 1))
            (fullSim (cRel Rv) (h + 1)) [cZ exc2 μ ν2 v0 c₂ (h + 1)]
            (WresD α (cT exc2 μ ν2 v0 (h + 1))
              (fullSim (cRel Rv) (h + 1))) = 0 := by
          rw [screenE_singleton]
          refine Eq.trans (screenG_cZ_succ_far Rv μ v0 exc1 exc2 ν1 ν2
            w hw (CtrC.ord k) c₂ h (WresD α (cT exc2 μ ν2 v0 (h + 1))
              (fullSim (cRel Rv) (h + 1)))) ?_
          refine ENNReal.tsum_eq_zero.mpr fun xp => ?_
          have hzt : WresD α (cT exc2 μ ν2 v0 (h + 1))
              (fullSim (cRel Rv) (h + 1))
              (branch (w, CtrC.ord k) xp) = 0 := by
            rw [WresD, if_pos (show rE (cT exc2 μ ν2 v0 (h + 1))
                (fullSim (cRel Rv) (h + 1))
                (branch (w, CtrC.ord k) xp) = 0 from by
              rw [rE_cT_succ_branch Rv exc2 μ ν2 v0 w (CtrC.ord k) h xp,
                hvr, zero_mul])]
          rw [hzt, mul_zero]
        rw [hz, mul_zero]
        exact zero_le
      · have hroot : screenE
            (muM (compK exc1 μ ν1 v0) (w, CtrC.ord k) (h + 1))
            (fullSim (cRel Rv) (h + 1)) [cZ exc2 μ ν2 v0 c₂ (h + 1)]
            (WresD α (cT exc2 μ ν2 v0 (h + 1))
              (fullSim (cRel Rv) (h + 1)))
            ≤ (rE μ Rv w) ^ (-α) * (T2 * cPairMoment α M) := by
          rw [screenE_singleton]
          refine le_trans (le_of_eq (screenG_cZ_succ_far Rv μ v0 exc1
            exc2 ν1 ν2 w hw (CtrC.ord k) c₂ h
            (WresD α (cT exc2 μ ν2 v0 (h + 1))
              (fullSim (cRel Rv) (h + 1))))) ?_
          calc ∑' xp, cXi exc1 μ ν1 v0 (CtrC.ord k) h xp
                * WresD α (cT exc2 μ ν2 v0 (h + 1))
                    (fullSim (cRel Rv) (h + 1))
                    (branch (w, CtrC.ord k) xp)
              = (rE μ Rv w) ^ (-α)
                * ∑' xp, cXi exc1 μ ν1 v0 (CtrC.ord k) h xp
                    * WresD α (cXiBar exc2 μ ν2 v0 h)
                        (SquareRel (fullSim (cRel Rv) h)) xp := by
                rw [← ENNReal.tsum_mul_left]
                refine tsum_congr fun xp => ?_
                rw [WresD_cT_succ_branch exc2 μ ν2 v0 Rv α hvr
                  (CtrC.ord k) h xp]
                ring
            _ ≤ (rE μ Rv w) ^ (-α) * (T2 * cPairMoment α M) :=
                mul_le_mul_right (cMixMoment_le α Rv μ v0 exc1 exc2 ν1 ν2
                  hα hμ0 hpair2 hdecl2 (CtrC.ord k) h M T2 hT2 hM1) _
        calc freshQ μ ν1 (w, k)
              * screenE (muM (compK exc1 μ ν1 v0)
                  (w, CtrC.ord k) (h + 1)) (fullSim (cRel Rv) (h + 1))
                  [cZ exc2 μ ν2 v0 c₂ (h + 1)]
                  (WresD α (cT exc2 μ ν2 v0 (h + 1))
                    (fullSim (cRel Rv) (h + 1)))
            ≤ freshQ μ ν1 (w, k)
              * ((rE μ Rv w) ^ (-α) * (T2 * cPairMoment α M)) :=
              mul_le_mul_right hroot _
          _ = (μ w : ℝ≥0∞) * WresD α μ Rv w
              * (T2 * cPairMoment α M) * ν1 k := by
              rw [show freshQ μ ν1 (w, k) = μ w * ν1 k from rfl,
                ← rE_rpow_neg_eq_WresD μ Rv w hvr]
              ring
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_add]
  refine add_le_add ?_ ?_
  · calc ∑' s : V × ℕ, (if Rv s.1 v0 then 0
          else (μ s.1 : ℝ≥0∞) * WresD α μ Rv s.1
            * (T2 * cPairMoment α M) * ν1 s.2)
        = ∑' s : V × ℕ,
            ((if Rv s.1 v0 then 0
              else (μ s.1 : ℝ≥0∞) * WresD α μ Rv s.1)
                * (T2 * cPairMoment α M)) * ν1 s.2 := by
          refine tsum_congr fun s => ?_
          by_cases hv : Rv s.1 v0
          · rw [if_pos hv, if_pos hv, zero_mul, zero_mul]
          · rw [if_neg hv, if_neg hv]
      _ = ((∑' v, if Rv v v0 then 0
            else (μ v : ℝ≥0∞) * WresD α μ Rv v)
          * (T2 * cPairMoment α M)) * ∑' l, (ν1 l : ℝ≥0∞) := by
          rw [← ENNReal.tsum_mul_right]
          exact tsum_prod_split
            (fun v => (if Rv v v0 then 0
              else (μ v : ℝ≥0∞) * WresD α μ Rv v)
                * (T2 * cPairMoment α M))
            (fun l => (ν1 l : ℝ≥0∞))
      _ ≤ FT * (T2 * cPairMoment α M) := by
          rw [ν1.tsum_coe, mul_one]
          exact mul_le_mul_left hFT _
  · rw [ENNReal.tsum_mul_right, (freshQ μ ν1).tsum_coe, one_mul]

/-- Fresh source against a zero list containing the opposite fresh law:
exact pruning, for any normalization (`thm:exact-pruning`). -/
theorem cScr_TT_prune (N : ℕ) (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (h : ℕ) (W : FullLab (CState V) h → ℝ≥0∞) :
    screenE (cT exc1 μ ν1 v0 h) (fullSim (cRel Rv) h)
      [cT exc2 μ ν2 v0 h] W = 0 :=
  screenE_cT_opposite_eq_zero Rv μ v0 exc1 exc2 ν1 ν2 N hRv hμ0 hN hpair
    hcharged h [cT exc2 μ ν2 v0 h] (List.mem_singleton_self _) W

/-! ### The Hall factorization and the price conversion -/

/-- **Hall factorization of the unit pair screen**: a pair-level cell
screen with unit normalization factorizes into unit letter screens. -/
theorem cPairScreen_unit_factorize (c₁ c₂ : CtrC) (h : ℕ) :
    screenE (cXi exc1 μ ν1 v0 c₁ h) (SquareRel (fullSim (cRel Rv) h))
        [cXi exc2 μ ν2 v0 c₂ h] (fun _ => 1)
      ≤ screenE (cLet exc1 μ ν1 v0 (cComp0 exc1 c₁) h)
            (fullSim (cRel Rv) h)
            [cLet exc2 μ ν2 v0 (cComp0 exc2 c₂) h,
              cLet exc2 μ ν2 v0 (cComp1 exc2 c₂) h] (fun _ => 1)
        + screenE (cLet exc1 μ ν1 v0 (cComp1 exc1 c₁) h)
            (fullSim (cRel Rv) h)
            [cLet exc2 μ ν2 v0 (cComp0 exc2 c₂) h,
              cLet exc2 μ ν2 v0 (cComp1 exc2 c₂) h] (fun _ => 1)
        + screenE (cLet exc1 μ ν1 v0 (cComp0 exc1 c₁) h)
            (fullSim (cRel Rv) h)
            [cLet exc2 μ ν2 v0 (cComp0 exc2 c₂) h] (fun _ => 1)
          * screenE (cLet exc1 μ ν1 v0 (cComp1 exc1 c₁) h)
              (fullSim (cRel Rv) h)
              [cLet exc2 μ ν2 v0 (cComp0 exc2 c₂) h] (fun _ => 1)
        + screenE (cLet exc1 μ ν1 v0 (cComp0 exc1 c₁) h)
            (fullSim (cRel Rv) h)
            [cLet exc2 μ ν2 v0 (cComp1 exc2 c₂) h] (fun _ => 1)
          * screenE (cLet exc1 μ ν1 v0 (cComp1 exc1 c₁) h)
              (fullSim (cRel Rv) h)
              [cLet exc2 μ ν2 v0 (cComp1 exc2 c₂) h] (fun _ => 1) := by
  refine le_trans (le_of_eq ?_) (cDeadMass_factorize μ v0 exc1 exc2 ν1 ν2
    (cXi_eq_prod exc1 μ ν1 v0 c₁ h) (cXi_eq_prod exc2 μ ν2 v0 c₂ h)
    (fullSim (cRel Rv) h))
  rw [screenE_singleton]
  refine tsum_congr fun xp => ?_
  rw [mul_one]

/-- **The composite weight conversion for pair screens**
(`thm:mixture-tilt-composite` at the screen coordinates): a mixture-tilted pair
screen is below the `compFloor`-priced sum of cell-tilted pair screens
over the support `K2`. -/
theorem cPairScreen_price (hα0 : 0 ≤ α) (hμ0 : μ v0 ≠ 0)
    (hpair2 : ∀ k p, exc2 k = some p → ∀ j, j ≤ p.1 → exc2 j = none)
    (hdecl2 : ∀ k p, exc2 k = some p → ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hfin2 : ∀ k, ν2 k ≠ 0 → k ∈ K2) (h : ℕ)
    (ρs : PMF (FullLab (CState V) h × FullLab (CState V) h))
    (zs : List (PMF (FullLab (CState V) h × FullLab (CState V) h))) :
    screenE ρs (SquareRel (fullSim (cRel Rv) h)) zs
        (WresD α (cXiBar exc2 μ ν2 v0 h)
          (SquareRel (fullSim (cRel Rv) h)))
      ≤ ∑ k ∈ K2, (if ν2 k = 0 then 0 else
          compFloor exc2 μ ν2 v0 k ^ (-α)
            * screenE ρs (SquareRel (fullSim (cRel Rv) h)) zs
                (WresD α (cXi exc2 μ ν2 v0 (CtrC.ord k) h)
                  (SquareRel (fullSim (cRel Rv) h)))) := by
  refine le_trans (screenE_WresD_cXiBar_le_sum exc2 μ ν2 v0 hpair2 hdecl2
    hμ0 hα0 Rv h ρs zs) ?_
  refine le_of_eq (tsum_eq_finsetSum_of_support fun k hk => ?_)
  refine hfin2 k fun h0 => hk ?_
  rw [if_pos h0]

/-! ### The zero-mass rows (`zMass` form) -/

/-- Frozen-frozen zero-mass row: the height-`(h + 1)` zero mass is the
unit pair-screen of the cells. -/
theorem cZMass_row_ZZ (hrefl0 : Rv v0 v0) (c₁ c₂ : CtrC) (h : ℕ) :
    zMass (cZ exc1 μ ν1 v0 c₁ (h + 1)) (cZ exc2 μ ν2 v0 c₂ (h + 1))
        (fullSim (cRel Rv) (h + 1))
      = screenE (cXi exc1 μ ν1 v0 c₁ h) (SquareRel (fullSim (cRel Rv) h))
          [cXi exc2 μ ν2 v0 c₂ h] (fun _ => 1) := by
  rw [zMass_eq_screenE_unit]
  exact cScr_ZZ_unit Rv μ v0 exc1 exc2 ν1 ν2 hrefl0 c₁ c₂ h

/-- Frozen-fresh zero-mass row: the descended zero list is the full
member list. -/
theorem cZMass_row_ZT (hrefl0 : Rv v0 v0) (hμ0 : μ v0 ≠ 0)
    (hsupp2 : ∀ k, ν2 k ≠ 0 ↔ k ∈ K2) (c₁ : CtrC) (h : ℕ) :
    zMass (cZ exc1 μ ν1 v0 c₁ (h + 1)) (cT exc2 μ ν2 v0 (h + 1))
        (fullSim (cRel Rv) (h + 1))
      = screenE (cXi exc1 μ ν1 v0 c₁ h) (SquareRel (fullSim (cRel Rv) h))
          (cMemberList exc2 μ ν2 v0 K2 h) (fun _ => 1) := by
  rw [zMass_eq_screenE_unit]
  exact cScr_ZT_unit Rv μ v0 exc1 exc2 ν1 ν2 K2 hrefl0 hμ0 hsupp2 c₁ h

/-- Fresh-frozen zero-mass row: far mass plus the retained
`ν1`-mixture of unit pair screens. -/
theorem cZMass_row_TZ (hfin1 : ∀ k, ν1 k ≠ 0 → k ∈ K1) (c₂ : CtrC)
    (h : ℕ) (FM : ℝ≥0∞)
    (hFM : (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞)) ≤ FM) :
    zMass (cT exc1 μ ν1 v0 (h + 1)) (cZ exc2 μ ν2 v0 c₂ (h + 1))
        (fullSim (cRel Rv) (h + 1))
      ≤ FM + ∑ k ∈ K1, ν1 k
          * screenE (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
              (SquareRel (fullSim (cRel Rv) h))
              [cXi exc2 μ ν2 v0 c₂ h] (fun _ => 1) := by
  rw [zMass_eq_screenE_unit]
  exact cScr_TZ_unit Rv μ v0 exc1 exc2 ν1 ν2 K1 hfin1 c₂ h FM hFM

/-! ### The height-zero base cases -/

/-- Unit screens at any height are at most one; `screenE_unit_le_one`
is the generic form used at height 0. -/
theorem cScr_base_unit (l1 : Option CtrC)
    (zs : List (PMF (FullLab (CState V) 0))) :
    screenE (cLet exc1 μ ν1 v0 l1 0) (fullSim (cRel Rv) 0) zs
      (fun _ => 1) ≤ 1 :=
  screenE_unit_le_one _ _ _

/-- Tilted screens at height 0 are bounded by the tilted moment of the
base ordinary row. -/
theorem cScr_base_tilt (hα : 1 ≤ α) (hrefl0 : Rv v0 v0)
    (l1 l3 : Option CtrC) (zs : List (PMF (FullLab (CState V) 0))) :
    screenE (cLet exc1 μ ν1 v0 l1 0) (fullSim (cRel Rv) 0) zs
        (WresD α (cLet exc2 μ ν2 v0 l3 0) (fullSim (cRel Rv) 0))
      ≤ 1 + ENNReal.ofReal α * (etaG α Rv μ + phiE α (q μ Rv v0)) := by
  have hdrop : screenE (cLet exc1 μ ν1 v0 l1 0) (fullSim (cRel Rv) 0) zs
        (WresD α (cLet exc2 μ ν2 v0 l3 0) (fullSim (cRel Rv) 0))
      ≤ ∑' x, cLet exc1 μ ν1 v0 l1 0 x
          * WresD α (cLet exc2 μ ν2 v0 l3 0) (fullSim (cRel Rv) 0) x := by
    rw [screenE]
    refine ENNReal.tsum_le_tsum fun x => ?_
    calc cLet exc1 μ ν1 v0 l1 0 x * screenInd (fullSim (cRel Rv) 0) zs x
          * WresD α (cLet exc2 μ ν2 v0 l3 0) (fullSim (cRel Rv) 0) x
        ≤ cLet exc1 μ ν1 v0 l1 0 x * 1
            * WresD α (cLet exc2 μ ν2 v0 l3 0) (fullSim (cRel Rv) 0) x :=
          mul_le_mul_left
            (mul_le_mul_right (screenInd_le_one _ _ _) _) _
      _ = cLet exc1 μ ν1 v0 l1 0 x
            * WresD α (cLet exc2 μ ν2 v0 l3 0) (fullSim (cRel Rv) 0) x := by
          rw [mul_one]
  refine le_trans hdrop (le_trans (tsum_WresD_le hα _ _ _) ?_)
  exact add_le_add le_rfl (mul_le_mul_right
    (cRow_base α Rv μ v0 exc1 exc2 ν1 ν2 hrefl0 l1 l3) _)

/-- Frozen-frozen zero mass at height 0 vanishes. -/
theorem cZMass_base_ZZ (hrefl0 : Rv v0 v0) (c₁ c₂ : CtrC) :
    zMass (cZ exc1 μ ν1 v0 c₁ 0) (cZ exc2 μ ν2 v0 c₂ 0)
      (fullSim (cRel Rv) 0) = 0 := by
  have hr : rE (cZ exc2 μ ν2 v0 c₂ 0) (fullSim (cRel Rv) 0)
      (leaf (v0, c₁)) ≠ 0 := by
    intro h0
    rw [show cZ exc2 μ ν2 v0 c₂ 0 = PMF.pure (leaf (v0, c₂)) from rfl,
      rE_pure_eq_zero_iff] at h0
    exact h0 ((fullSim_leaf (cRel Rv) (v0, c₁) (v0, c₂)).mpr hrefl0)
  rw [zMass_eq_tsum,
    show cZ exc1 μ ν1 v0 c₁ 0 = PMF.pure (leaf (v0, c₁)) from rfl,
    tsum_pure_mul, if_neg hr]

/-- Frozen-fresh zero mass at height 0 vanishes. -/
theorem cZMass_base_ZT (hrefl0 : Rv v0 v0) (hμ0 : μ v0 ≠ 0)
    (c₁ : CtrC) :
    zMass (cZ exc1 μ ν1 v0 c₁ 0) (cT exc2 μ ν2 v0 0)
      (fullSim (cRel Rv) 0) = 0 := by
  have hr : rE (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0)
      (leaf (v0, c₁)) ≠ 0 := by
    rw [rE_cT_zero Rv exc2 μ ν2 v0 v0 c₁]
    exact rE_root_ne_zero Rv μ v0 hrefl0 hμ0
  rw [zMass_eq_tsum,
    show cZ exc1 μ ν1 v0 c₁ 0 = PMF.pure (leaf (v0, c₁)) from rfl,
    tsum_pure_mul, if_neg hr]

/-- Fresh-frozen zero mass at height 0 is the far mass. -/
theorem cZMass_base_TZ (c₂ : CtrC) (FM : ℝ≥0∞)
    (hFM : (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞)) ≤ FM) :
    zMass (cT exc1 μ ν1 v0 0) (cZ exc2 μ ν2 v0 c₂ 0)
      (fullSim (cRel Rv) 0) ≤ FM := by
  rw [zMass_eq_tsum, cT_eq_freshQ_bind exc1 μ ν1 v0 0, tsum_bind_mul]
  have hpt : ∀ s : V × ℕ,
      freshQ μ ν1 s
        * ∑' x, muM (compK exc1 μ ν1 v0) (s.1, CtrC.ord s.2) 0 x
            * (if rE (cZ exc2 μ ν2 v0 c₂ 0) (fullSim (cRel Rv) 0) x = 0
                then 1 else 0)
      = (if Rv s.1 v0 then 0 else (μ s.1 : ℝ≥0∞)) * ν1 s.2 := by
    intro s
    have hpure : (∑' x, muM (compK exc1 μ ν1 v0) (s.1, CtrC.ord s.2) 0 x
        * (if rE (cZ exc2 μ ν2 v0 c₂ 0) (fullSim (cRel Rv) 0) x = 0
            then 1 else 0))
        = (if rE (cZ exc2 μ ν2 v0 c₂ 0) (fullSim (cRel Rv) 0)
              (leaf (s.1, CtrC.ord s.2)) = 0 then 1 else 0) := by
      rw [show muM (compK exc1 μ ν1 v0) (s.1, CtrC.ord s.2) 0
          = PMF.pure (leaf (s.1, CtrC.ord s.2)) from rfl]
      exact tsum_pure_mul _ _
    rw [hpure]
    have hiff : rE (cZ exc2 μ ν2 v0 c₂ 0) (fullSim (cRel Rv) 0)
          (leaf (s.1, CtrC.ord s.2)) = 0 ↔ ¬ Rv s.1 v0 := by
      rw [show cZ exc2 μ ν2 v0 c₂ 0 = PMF.pure (leaf (v0, c₂)) from rfl,
        rE_pure_eq_zero_iff]
      constructor
      · intro hnr hr
        exact hnr ((fullSim_leaf (cRel Rv) (s.1, CtrC.ord s.2)
          (v0, c₂)).mpr hr)
      · intro hnr hsim
        exact hnr ((fullSim_leaf (cRel Rv) (s.1, CtrC.ord s.2)
          (v0, c₂)).mp hsim)
    by_cases hv : Rv s.1 v0
    · rw [if_pos hv, if_neg (fun h0 => hiff.mp h0 hv), mul_zero,
        zero_mul]
    · rw [if_neg hv, if_pos (hiff.mpr hv), mul_one]
      exact prodPMF_apply μ ν1 s
  rw [tsum_congr hpt,
    tsum_prod_split (fun v => if Rv v v0 then 0 else (μ v : ℝ≥0∞))
      (fun l => (ν1 l : ℝ≥0∞)), ν1.tsum_coe, mul_one]
  exact hFM

end Assembly

end Composite
end GraphMarkovMatching
