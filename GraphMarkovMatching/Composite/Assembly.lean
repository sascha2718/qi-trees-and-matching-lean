/-
The letter alphabet, the row constants, and the base rows of the
composite two-law ledger (`arbitrary_offspring_matching.tex`,
`sec:composite`, `thm:composite-ledger`).  Everything is stated
generically in the two side packs `(exc1, ν1)` (source) and `(exc2, ν2)`
(target); the swapped orientation is the same theorem with the packs
exchanged.

* `cLet`, `cComp0`, `cComp1`, `cXi_eq_prod`: the letter alphabet
  `Option CtrC` (`some c` the frozen law below `(v0, c)`, `none` the
  fresh law) and the product presentation of every composite cell,
  markers and exceptional entrances included;
* `cCellBound`, `cTiltSum`: the named constants of the rows: the
  per-cell screen bound `4E'(1 + αM) + 4E'²` and the composite charged
  tilt sum `∑_k compFloor(k)^{-α}` (a finite sum over the support by
  `cTiltSum_eq_sum`);
* `cRow_base` (`thm:base`): the height-0 ordinary base for all letter
  pairs;
* `cPairMoment`, `cPairScreen_price`: the pair-level cell moment and the
  conversion of a fresh normalization, carrying the root price
  `(rE μ Rv v0)^{-α}`, into `compFloor`-priced cell tilts;
* `cZMass_base_TZ`: the height-0 zero-mass base.
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

/-- The zero-interface mass is the unit-normalized singleton screen. -/
lemma zMass_eq_screenE_unit {X : Type} (ρs ρt : PMF X)
    (R : X → X → Prop) :
    zMass ρs ρt R = screenE ρs R [ρt] (fun _ => 1) := by
  rw [zMass_eq_tsum, screenE_singleton]
  exact tsum_congr fun x => by rw [mul_one]

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
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one μ v0)
  have hcomp : μ v0 * phiE α (q μ Rv v0) ≤ etaG α Rv μ := by
    rw [etaG, PhiD]
    exact ENNReal.le_tsum v0
  calc phiE α (q μ Rv v0)
      = (μ v0)⁻¹ * (μ v0 * phiE α (q μ Rv v0)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hμ0 htop, one_mul]
    _ ≤ (μ v0)⁻¹ * etaG α Rv μ := mul_le_mul_right hcomp _

/-! ### The ordinary base row -/

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

/-! ### The price conversion of a fresh normalization

A fresh normalization contributes the root price `(rE μ Rv v0)^{-α}` and
descends to the mixture tilt, which `cPairScreen_price` converts into
`compFloor`-priced cell tilts. -/

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

/-! ### The Hall factorization and the price conversion -/

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

/-! ### The height-zero zero-mass base -/

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
