/-
The composite cell step (`arbitrary_offspring_matching.tex`,
`sec:composite`, feeding the ordinary rows of `thm:psi-rows` into the
ledger `thm:composite-ledger`): the one-step reductions that express every
height-`(h+1)` ordinary coordinate of the two-law composite ledger through
height-`h` coordinates of the same laws `cZ`/`cXi`/`cT`/`cXiBar`, for a
source side `(exc1, μ, ν1, v0)` and a target side `(exc2, μ, ν2, v0)`
sharing the graph law, the distinguished state, and the state relation
`cRel Rv`.  This is the composite analogue of the one-law
`VaryingCells`/`VaryingStep` layer, covering all tagged letters, markers
included.

* `compK_state_blind`, `pairMix_compK`, `muM_compK_succ`,
  `cT_eq_freshQ_bind`: the composite kernel ignores the graph state, so
  every cell is a `cXi` and the fresh law is a `freshQ`-mixture;
* `rE_cZ_succ_branch`, `qE_cZ_succ_branch`: the forced decomposition at a
  branch point, one lemma for all letters: the degree toward a frozen
  height-`(h+1)` law is the root indicator times the cell degree;
* `rE_cZ_ord_none_of_ge_succ_branch` .. `rE_cZ_mark_le_two_succ_branch`:
  the same identity with the cell resolved into its kernel shape:
  deterministic children (ordinary `k ≥ 4`, markers at running value
  `≥ 4` or `= 3`), one frozen child and one fresh child (ordinary `3`,
  markers at running value `≤ 2`; the marker freezes the port
  `(v0, ord b)` on the left), two fresh children (ordinary `k ≤ 2`), and
  the exceptional entrance into the stage-zero marker cell;
* `rE_cT_succ_branch`, `qE_cT_succ_branch`: the fresh decomposition: the
  degree toward the fresh law factorizes as the root ball mass times the
  mixture cell degree, and the bad degree as
  `q(v) + r(v)·q̄`;
* `rE_cXiBar_eq_tsum`, `rE_cXiBar_eq_zero_iff`,
  `mul_rE_cXi_le_rE_cXiBar`: the fresh cell mixture identity;
* `cPhiDres_muM_cZ_succ`, `cPhiDres_cZ_cZ_succ`: forced source against
  forced target, an exact reduction to the square coordinate under the
  root indicator;
* `phiE_cT_branch_le`, `cPhiDres_muM_cT_succ`, `cPhiDres_cZ_cT_succ`:
  source against fresh target, the split bound through the root factor;
* `cPhiDres_cT_cZ_succ`, `cPhiDres_cT_cT_succ`: fresh source: the root
  integrates to the graph potential `etaG` and the counter mixture splits
  the coordinate into the `ν1`-weighted sum over side-1 cells, the
  exceptional arities contributing their own `cXi (ord z)` cells;
* `cPhiDres_cXiBar_eq`: source linearity of the mixture coordinate;
* `qE_cT_zero`, `rE_cT_zero`, `cPhiDres_cZ_cZ_zero`, `cPhiDres_cT_cZ_zero`,
  `cPhiDres_cZ_cT_zero_le`, `cPhiDres_cT_cT_zero_le`: the height-zero base
  for all letter pairs.
-/
import GraphMarkovMatching.Composite.Support
import GraphMarkovMatching.Process.Cells
import GraphMarkovMatching.Process.Contraction
import GraphMarkovMatching.Process.Descent

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type}

section OneSide

variable (α : ℝ) (Rv : V → V → Prop)
variable (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V) (ν : PMF ℕ) (v0 : V)

/-! ### Label-blindness of the composite kernel -/

/-- The composite kernel reads only the tagged counter. -/
lemma compK_state_blind (v w : V) (c : CtrC) :
    compK exc μ ν v0 (v, c) = compK exc μ ν v0 (w, c) := by
  cases c <;> rfl

/-- Every cell of the composite kernel is a `cXi`, whatever the root
state. -/
lemma pairMix_compK (v : V) (c : CtrC) (h : ℕ) :
    pairMix (compK exc μ ν v0) (v, c) h = cXi exc μ ν v0 c h := by
  rw [cXi, pairMix, pairMix, compK_state_blind exc μ ν v0 v v0 c]

/-- The measure recursion of the composite kernel through the cell law. -/
lemma muM_compK_succ (v : V) (c : CtrC) (h : ℕ) :
    muM (compK exc μ ν v0) (v, c) (h + 1)
      = (cXi exc μ ν v0 c h).map (branch (v, c)) := by
  rw [muM_succ, pairMix_compK]

/-- The composite fresh law as a `freshQ`-mixture: markers carry no fresh
mass, so a fresh sample is an ordinary tagged `μ ⊗ ν` draw. -/
lemma cT_eq_freshQ_bind (h : ℕ) :
    cT exc μ ν v0 h
      = (freshQ μ ν).bind fun s =>
          muM (compK exc μ ν v0) (s.1, CtrC.ord s.2) h := by
  rw [cT, freshC, PMF.bind_map]
  rfl

/-! ### The forced decomposition at a branch point -/

/-- **The forced decomposition** (all letters, markers included): the good
degree toward a frozen height-`(h+1)` law is the root indicator times the
cell degree. -/
lemma rE_cZ_succ_branch (v : V) (cs c : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 c (h + 1)) (fullSim (cRel Rv) (h + 1)) (branch (v, cs) xp)
      = if Rv v v0 then
          rE (cXi exc μ ν v0 c h) (SquareRel (fullSim (cRel Rv) h)) xp
        else 0 :=
  rE_succ_branch (compK exc μ ν v0) (cRel Rv) (v, cs) (v0, c) h xp

/-- The bad-degree form of the forced decomposition at a compatible root. -/
lemma qE_cZ_succ_branch {v : V} (hv : Rv v v0) (cs c : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    qE (cZ exc μ ν v0 c (h + 1)) (fullSim (cRel Rv) (h + 1)) (branch (v, cs) xp)
      = qE (cXi exc μ ν v0 c h) (SquareRel (fullSim (cRel Rv) h)) xp :=
  qE_succ_branch (compK exc μ ν v0) (cRel Rv)
    (show cRel Rv (v, cs) (v0, c) from hv) h xp

/-! ### The forced decomposition in the three kernel shapes -/

/-- Ordinary counter `k ≥ 4`, not exceptional: deterministic children. -/
lemma rE_cZ_ord_none_of_ge_succ_branch {k : ℕ} (hk : exc k = none)
    (h4 : 4 ≤ k) (v : V) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.ord k) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (v, cs) xp)
      = if Rv v v0 then
          rE (prodPMF (cZ exc μ ν v0 (CtrC.ord (k / 2)) h)
              (cZ exc μ ν v0 (CtrC.ord (k - k / 2)) h))
            (SquareRel (fullSim (cRel Rv) h)) xp
        else 0 := by
  rw [rE_cZ_succ_branch Rv exc μ ν v0 v cs (CtrC.ord k) h xp,
    cXi_ord_none_of_ge exc μ ν v0 hk h4 h]

/-- Ordinary counter `3`, not exceptional: frozen `(v0, ord 2)` on the
left, fresh right child. -/
lemma rE_cZ_ord_none_three_succ_branch {k : ℕ} (hk : exc k = none)
    (h3 : k = 3) (v : V) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.ord k) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (v, cs) xp)
      = if Rv v v0 then
          rE (prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h) (cT exc μ ν v0 h))
            (SquareRel (fullSim (cRel Rv) h)) xp
        else 0 := by
  rw [rE_cZ_succ_branch Rv exc μ ν v0 v cs (CtrC.ord k) h xp,
    cXi_ord_none_three exc μ ν v0 hk h3 h]

/-- Ordinary counter `≤ 2`, not exceptional: two fresh children. -/
lemma rE_cZ_ord_none_le_two_succ_branch {k : ℕ} (hk : exc k = none)
    (h2 : k ≤ 2) (v : V) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.ord k) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (v, cs) xp)
      = if Rv v v0 then
          rE (prodPMF (cT exc μ ν v0 h) (cT exc μ ν v0 h))
            (SquareRel (fullSim (cRel Rv) h)) xp
        else 0 := by
  rw [rE_cZ_succ_branch Rv exc μ ν v0 v cs (CtrC.ord k) h xp,
    cXi_ord_none_le_two exc μ ν v0 hk h2 h]

/-- Exceptional counter: the chart entrance, the cell of the stage-zero
marker of its declared pair. -/
lemma rE_cZ_ord_exc_succ_branch {z : ℕ} {p : ℕ × ℕ} (hz : exc z = some p)
    (v : V) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.ord z) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (v, cs) xp)
      = if Rv v v0 then
          rE (cXi exc μ ν v0 (CtrC.mark p.1 p.2 0) h)
            (SquareRel (fullSim (cRel Rv) h)) xp
        else 0 := by
  rw [rE_cZ_succ_branch Rv exc μ ν v0 v cs (CtrC.ord z) h xp,
    cXi_ord_exc exc μ ν v0 hz h]

/-- Marker at running value `≥ 4`: deterministic children, the advanced
marker on the left. -/
lemma rE_cZ_mark_of_ge_succ_branch {a b i : ℕ} (hval : 4 ≤ val a i)
    (v : V) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.mark a b i) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (v, cs) xp)
      = if Rv v v0 then
          rE (prodPMF (cZ exc μ ν v0 (CtrC.mark a b (i + 1)) h)
              (cZ exc μ ν v0 (CtrC.ord (val a i - val a i / 2)) h))
            (SquareRel (fullSim (cRel Rv) h)) xp
        else 0 := by
  rw [rE_cZ_succ_branch Rv exc μ ν v0 v cs (CtrC.mark a b i) h xp,
    cXi_mark_of_ge exc μ ν v0 hval h]

/-- Marker at running value `3`: deterministic children, the port
`(v0, ord b)` delivered on the right. -/
lemma rE_cZ_mark_three_succ_branch {a b i : ℕ} (hval : val a i = 3)
    (v : V) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.mark a b i) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (v, cs) xp)
      = if Rv v v0 then
          rE (prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h)
              (cZ exc μ ν v0 (CtrC.ord b) h))
            (SquareRel (fullSim (cRel Rv) h)) xp
        else 0 := by
  rw [rE_cZ_succ_branch Rv exc μ ν v0 v cs (CtrC.mark a b i) h xp,
    cXi_mark_three exc μ ν v0 hval h]

/-- Marker at running value `≤ 2`: the frozen port `(v0, ord b)` on the
left, fresh right child. -/
lemma rE_cZ_mark_le_two_succ_branch {a b i : ℕ} (hval : val a i ≤ 2)
    (v : V) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cZ exc μ ν v0 (CtrC.mark a b i) (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (v, cs) xp)
      = if Rv v v0 then
          rE (prodPMF (cZ exc μ ν v0 (CtrC.ord b) h) (cT exc μ ν v0 h))
            (SquareRel (fullSim (cRel Rv) h)) xp
        else 0 := by
  rw [rE_cZ_succ_branch Rv exc μ ν v0 v cs (CtrC.mark a b i) h xp,
    cXi_mark_le_two exc μ ν v0 hval h]

/-! ### The fresh decomposition and the mixture identity -/

/-- **The fresh decomposition**: the good degree toward the composite
fresh law is the root ball mass times the mixture cell degree. -/
lemma rE_cT_succ_branch (v : V) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cT exc μ ν v0 (h + 1)) (fullSim (cRel Rv) (h + 1)) (branch (v, cs) xp)
      = rE μ Rv v
        * rE (cXiBar exc μ ν v0 h) (SquareRel (fullSim (cRel Rv) h)) xp := by
  rw [cT_eq_freshQ_bind exc μ ν v0 (h + 1), rE_bind]
  calc ∑' s : V × ℕ, freshQ μ ν s
        * rE (muM (compK exc μ ν v0) (s.1, CtrC.ord s.2) (h + 1))
            (fullSim (cRel Rv) (h + 1)) (branch (v, cs) xp)
      = ∑' s : V × ℕ, (if Rv v s.1 then μ s.1 else 0)
          * (ν s.2 * rE (cXi exc μ ν v0 (CtrC.ord s.2) h)
              (SquareRel (fullSim (cRel Rv) h)) xp) := by
        refine tsum_congr fun s => ?_
        obtain ⟨w, l⟩ := s
        rw [rE_succ_branch (compK exc μ ν v0) (cRel Rv) (v, cs)
            (w, CtrC.ord l) h xp,
          pairMix_compK exc μ ν v0 w (CtrC.ord l) h]
        by_cases hw : Rv v w
        · rw [if_pos (show cRel Rv (v, cs) (w, CtrC.ord l) from hw),
            if_pos hw]
          simp only [freshQ, prodPMF_apply]
          ring
        · rw [if_neg (show ¬ cRel Rv (v, cs) (w, CtrC.ord l) from hw),
            if_neg hw, mul_zero, zero_mul]
    _ = (∑' w, if Rv v w then μ w else 0)
        * ∑' l, ν l * rE (cXi exc μ ν v0 (CtrC.ord l) h)
            (SquareRel (fullSim (cRel Rv) h)) xp :=
      tsum_prod_split (fun w => if Rv v w then μ w else 0)
        (fun l => ν l * rE (cXi exc μ ν v0 (CtrC.ord l) h)
          (SquareRel (fullSim (cRel Rv) h)) xp)
    _ = rE μ Rv v
        * rE (cXiBar exc μ ν v0 h) (SquareRel (fullSim (cRel Rv) h)) xp := by
      have h2 : rE (cXiBar exc μ ν v0 h) (SquareRel (fullSim (cRel Rv) h)) xp
          = ∑' l, ν l * rE (cXi exc μ ν v0 (CtrC.ord l) h)
              (SquareRel (fullSim (cRel Rv) h)) xp :=
        rE_bind ν (fun l => cXi exc μ ν v0 (CtrC.ord l) h) _ xp
      rw [h2]
      rfl

/-- The fresh cell mixture identity:
`r_{·|Ξ̄} = ∑_k ν_k r_{·|Ξ_k}` at the composite cells. -/
lemma rE_cXiBar_eq_tsum (h : ℕ)
    (R : FullLab (CState V) h × FullLab (CState V) h
      → FullLab (CState V) h × FullLab (CState V) h → Prop)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cXiBar exc μ ν v0 h) R xp
      = ∑' k, ν k * rE (cXi exc μ ν v0 (CtrC.ord k) h) R xp := by
  rw [cXiBar, rE_bind]

/-- A zero degree toward the fresh cell mixture forces a zero degree
toward every charged component. -/
lemma rE_cXiBar_eq_zero_iff (h : ℕ)
    (R : FullLab (CState V) h × FullLab (CState V) h
      → FullLab (CState V) h × FullLab (CState V) h → Prop)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE (cXiBar exc μ ν v0 h) R xp = 0 ↔
      ∀ k, ν k = 0 ∨ rE (cXi exc μ ν v0 (CtrC.ord k) h) R xp = 0 := by
  rw [cXiBar, rE_bind_eq_zero_iff]

/-- One charged cell already bounds the mixture degree from below. -/
lemma mul_rE_cXi_le_rE_cXiBar (h : ℕ)
    (R : FullLab (CState V) h × FullLab (CState V) h
      → FullLab (CState V) h × FullLab (CState V) h → Prop)
    (xp : FullLab (CState V) h × FullLab (CState V) h) (k : ℕ) :
    ν k * rE (cXi exc μ ν v0 (CtrC.ord k) h) R xp
      ≤ rE (cXiBar exc μ ν v0 h) R xp := by
  rw [cXiBar]
  exact mul_rE_le_rE_bind ν _ R xp k

/-- **The root factorisation of the bad degree**: against the composite
fresh law, the bad degree of an attached sample is exactly
`q(v) + r(v)·q̄` with `q̄` the bad degree of the child pair against the
fresh cell mixture. -/
lemma qE_cT_succ_branch (v : V) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    qE (cT exc μ ν v0 (h + 1)) (fullSim (cRel Rv) (h + 1)) (branch (v, cs) xp)
      = qE μ Rv v + rE μ Rv v
          * qE (cXiBar exc μ ν v0 h) (SquareRel (fullSim (cRel Rv) h)) xp := by
  set qΞ := qE (cXiBar exc μ ν v0 h) (SquareRel (fullSim (cRel Rv) h)) xp
    with hqΞ
  rw [cT_eq_freshQ_bind exc μ ν v0 (h + 1), qE_bind, ENNReal.tsum_prod']
  have hinner : ∀ w : V,
      (∑' k' : ℕ, freshQ μ ν (w, k')
        * qE (muM (compK exc μ ν v0) (w, CtrC.ord k') (h + 1))
            (fullSim (cRel Rv) (h + 1)) (branch (v, cs) xp))
      = μ w * (if Rv v w then qΞ else 1) := by
    intro w
    by_cases hvw : Rv v w
    · rw [if_pos hvw]
      calc (∑' k' : ℕ, freshQ μ ν (w, k')
            * qE (muM (compK exc μ ν v0) (w, CtrC.ord k') (h + 1))
                (fullSim (cRel Rv) (h + 1)) (branch (v, cs) xp))
          = ∑' k' : ℕ, μ w * (ν k'
              * qE (cXi exc μ ν v0 (CtrC.ord k') h)
                  (SquareRel (fullSim (cRel Rv) h)) xp) := by
            refine tsum_congr fun k' => ?_
            rw [qE_succ_branch (compK exc μ ν v0) (cRel Rv)
                (show cRel Rv (v, cs) (w, CtrC.ord k') from hvw) h xp,
              pairMix_compK exc μ ν v0 w (CtrC.ord k') h,
              show freshQ μ ν (w, k') = μ w * ν k' from rfl]
            ring
        _ = μ w * ∑' k' : ℕ, ν k'
              * qE (cXi exc μ ν v0 (CtrC.ord k') h)
                  (SquareRel (fullSim (cRel Rv) h)) xp :=
            ENNReal.tsum_mul_left
        _ = μ w * qΞ := by rw [hqΞ, cXiBar, qE_bind]
    · rw [if_neg hvw, mul_one]
      calc (∑' k' : ℕ, freshQ μ ν (w, k')
            * qE (muM (compK exc μ ν v0) (w, CtrC.ord k') (h + 1))
                (fullSim (cRel Rv) (h + 1)) (branch (v, cs) xp))
          = ∑' k' : ℕ, μ w * ν k' := by
            refine tsum_congr fun k' => ?_
            rw [qE_succ_branch_mismatch (compK exc μ ν v0) (cRel Rv)
                (show ¬ cRel Rv (v, cs) (w, CtrC.ord k') from hvw) h xp,
              mul_one]
            rfl
        _ = μ w := by rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  calc (∑' w, ∑' k', freshQ μ ν (w, k')
        * qE (muM (compK exc μ ν v0) (w, CtrC.ord k') (h + 1))
            (fullSim (cRel Rv) (h + 1)) (branch (v, cs) xp))
      = ∑' w, μ w * (if Rv v w then qΞ else 1) := tsum_congr hinner
    _ = ∑' w, ((if Rv v w then μ w else 0) * qΞ
          + (if Rv v w then 0 else μ w)) := by
        refine tsum_congr fun w => ?_
        by_cases hvw : Rv v w
        · rw [if_pos hvw, if_pos hvw, if_pos hvw, add_zero]
        · rw [if_neg hvw, if_neg hvw, if_neg hvw, zero_mul, zero_add,
            mul_one]
    _ = (∑' w, (if Rv v w then μ w else 0)) * qΞ
          + ∑' w, (if Rv v w then 0 else μ w) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ = rE μ Rv v * qΞ + qE μ Rv v := by rw [rE, qE]
    _ = qE μ Rv v + rE μ Rv v * qΞ := add_comm _ _

/-- The split at the root: the potential weight of an attached sample
against the composite fresh law splits into the root charge, the mixture
charge, and the quadratic cross term. -/
lemma phiE_cT_branch_le (hα : 1 ≤ α) (v : V) (cs : CtrC) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    phiE α (q (cT exc μ ν v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (v, cs) xp))
      ≤ phiE α (q μ Rv v)
        + phiE α (q (cXiBar exc μ ν v0 h) (SquareRel (fullSim (cRel Rv) h)) xp)
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v)
            * phiE α (q (cXiBar exc μ ν v0 h)
                (SquareRel (fullSim (cRel Rv) h)) xp)) := by
  have hkey : q (cT exc μ ν v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (v, cs) xp)
      = q μ Rv v + (1 - q μ Rv v)
          * q (cXiBar exc μ ν v0 h) (SquareRel (fullSim (cRel Rv) h)) xp := by
    have hre : (rE μ Rv v).toReal = 1 - q μ Rv v := by
      have h1 := toReal_rE_add_toReal_qE μ Rv v
      rw [q]
      linarith
    rw [q, qE_cT_succ_branch Rv exc μ ν v0 v cs h xp,
      ENNReal.toReal_add qE_ne_top (ENNReal.mul_ne_top rE_ne_top qE_ne_top),
      ENNReal.toReal_mul, hre]
    rfl
  rw [hkey]
  exact phiE_split hα q_nonneg q_le_one q_nonneg q_le_one

/-! ### The height-zero base identities of the fresh law -/

/-- At height zero the composite fresh bad degree is the label bad degree:
counters and tags integrate out. -/
lemma qE_cT_zero (v : V) (c : CtrC) :
    qE (cT exc μ ν v0 0) (fullSim (cRel Rv) 0) (leaf (v, c)) = qE μ Rv v := by
  rw [cT_eq_freshQ_bind exc μ ν v0 0, qE_bind]
  calc ∑' s : V × ℕ, freshQ μ ν s
        * qE (muM (compK exc μ ν v0) (s.1, CtrC.ord s.2) 0)
            (fullSim (cRel Rv) 0) (leaf (v, c))
      = ∑' s : V × ℕ, (if Rv v s.1 then 0 else μ s.1) * ν s.2 := by
        refine tsum_congr fun s => ?_
        obtain ⟨w, l⟩ := s
        rw [show muM (compK exc μ ν v0) (w, CtrC.ord l) 0
            = PMF.pure (leaf (w, CtrC.ord l)) from rfl, qE_pure, badInd]
        by_cases hb : fullSim (cRel Rv) 0 (leaf (v, c)) (leaf (w, CtrC.ord l))
        · rw [if_pos hb,
            if_pos (show Rv v w from
              (fullSim_leaf (cRel Rv) (v, c) (w, CtrC.ord l)).mp hb),
            mul_zero, zero_mul]
        · rw [if_neg hb,
            if_neg (show ¬ Rv v w from fun hr =>
              hb ((fullSim_leaf (cRel Rv) (v, c) (w, CtrC.ord l)).mpr hr)),
            mul_one, show freshQ μ ν (w, l) = μ w * ν l from rfl]
    _ = (∑' w, if Rv v w then 0 else μ w) * ∑' l, (ν l : ℝ≥0∞) :=
        tsum_prod_split (fun w => if Rv v w then 0 else μ w)
          (fun l => (ν l : ℝ≥0∞))
    _ = qE μ Rv v := by rw [ν.tsum_coe, mul_one]; rfl

/-- The good-degree form of the height-zero fresh identity. -/
lemma rE_cT_zero (v : V) (c : CtrC) :
    rE (cT exc μ ν v0 0) (fullSim (cRel Rv) 0) (leaf (v, c)) = rE μ Rv v := by
  have h1 := rE_add_qE (cT exc μ ν v0 0) (fullSim (cRel Rv) 0) (leaf (v, c))
  have h2 := rE_add_qE μ Rv v
  rw [qE_cT_zero Rv exc μ ν v0 v c] at h1
  calc rE (cT exc μ ν v0 0) (fullSim (cRel Rv) 0) (leaf (v, c))
      = 1 - qE μ Rv v := ENNReal.eq_sub_of_add_eq qE_ne_top h1
    _ = rE μ Rv v := (ENNReal.eq_sub_of_add_eq qE_ne_top h2).symm

/-- Source linearity of the mixture coordinate: a `Ξ̄`-source restricted
potential is the `ν`-average of its cell coordinates. -/
lemma cPhiDres_cXiBar_eq (h : ℕ)
    (ρt : PMF (FullLab (CState V) h × FullLab (CState V) h))
    (R : FullLab (CState V) h × FullLab (CState V) h
      → FullLab (CState V) h × FullLab (CState V) h → Prop) :
    PhiDres α (cXiBar exc μ ν v0 h) ρt R
      = ∑' k, ν k * PhiDres α (cXi exc μ ν v0 (CtrC.ord k) h) ρt R := by
  rw [cXiBar, PhiDres_bind_left]

end OneSide

section TwoSides

variable (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ)

/-! ### Forced target: the exact reduction -/

/-- **Forced target, one cell root**: with source letters read by side 1
and target letters by side 2, the restricted coordinate toward a frozen
side-2 law is the root indicator times the restricted square coordinate.
Both letters range over all tagged counters, markers included. -/
lemma cPhiDres_muM_cZ_succ (v : V) (cs ct : CtrC) (h : ℕ) :
    PhiDres α (muM (compK exc1 μ ν1 v0) (v, cs) (h + 1))
        (cZ exc2 μ ν2 v0 ct (h + 1)) (fullSim (cRel Rv) (h + 1))
      = if Rv v v0 then
          PhiDres α (cXi exc1 μ ν1 v0 cs h) (cXi exc2 μ ν2 v0 ct h)
            (SquareRel (fullSim (cRel Rv) h))
        else 0 := by
  rw [muM_compK_succ exc1 μ ν1 v0 v cs h, PhiDres, tsum_map_mul]
  by_cases hv : Rv v v0
  · rw [if_pos hv, PhiDres]
    refine tsum_congr fun xp => ?_
    congr 1
    have hrE := rE_cZ_succ_branch Rv exc2 μ ν2 v0 v cs ct h xp
    rw [if_pos hv] at hrE
    have hq : q (cZ exc2 μ ν2 v0 ct (h + 1)) (fullSim (cRel Rv) (h + 1))
          (branch (v, cs) xp)
        = q (cXi exc2 μ ν2 v0 ct h) (SquareRel (fullSim (cRel Rv) h)) xp := by
      rw [q, q, qE_cZ_succ_branch Rv exc2 μ ν2 v0 hv cs ct h xp]
    rw [hrE, hq]
  · rw [if_neg hv]
    refine ENNReal.tsum_eq_zero.mpr fun xp => ?_
    have hrE := rE_cZ_succ_branch Rv exc2 μ ν2 v0 v cs ct h xp
    rw [if_neg hv] at hrE
    rw [hrE]
    simp

/-- The forced-forced pair step: an exact identity at the root `v0`. -/
lemma cPhiDres_cZ_cZ_succ (hrefl : Rv v0 v0) (cs ct : CtrC) (h : ℕ) :
    PhiDres α (cZ exc1 μ ν1 v0 cs (h + 1)) (cZ exc2 μ ν2 v0 ct (h + 1))
        (fullSim (cRel Rv) (h + 1))
      = PhiDres α (cXi exc1 μ ν1 v0 cs h) (cXi exc2 μ ν2 v0 ct h)
          (SquareRel (fullSim (cRel Rv) h)) := by
  rw [show cZ exc1 μ ν1 v0 cs (h + 1)
      = muM (compK exc1 μ ν1 v0) (v0, cs) (h + 1) from rfl,
    cPhiDres_muM_cZ_succ α Rv μ v0 exc1 exc2 ν1 ν2 v0 cs ct h, if_pos hrefl]

/-! ### Fresh target: the split bound -/

/-- **Fresh target, one cell root**: the split bound through the root
factor, the composite analogue of `PhiDres_muM_Tlaw_succ`. -/
lemma cPhiDres_muM_cT_succ (hα : 1 ≤ α) (v : V) (c : CtrC) (h : ℕ) :
    PhiDres α (muM (compK exc1 μ ν1 v0) (v, c) (h + 1))
        (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
      ≤ phiE α (q μ Rv v)
        + PhiDres α (cXi exc1 μ ν1 v0 c h) (cXiBar exc2 μ ν2 v0 h)
            (SquareRel (fullSim (cRel Rv) h))
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v)
            * PhiDres α (cXi exc1 μ ν1 v0 c h) (cXiBar exc2 μ ν2 v0 h)
                (SquareRel (fullSim (cRel Rv) h))) := by
  rw [muM_compK_succ exc1 μ ν1 v0 v c h, PhiDres, tsum_map_mul]
  have hpt : ∀ xp : FullLab (CState V) h × FullLab (CState V) h,
      cXi exc1 μ ν1 v0 c h xp
        * (if rE (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
              (branch (v, c) xp) = 0 then 0
            else phiE α (q (cT exc2 μ ν2 v0 (h + 1))
              (fullSim (cRel Rv) (h + 1)) (branch (v, c) xp)))
      ≤ cXi exc1 μ ν1 v0 c h xp * phiE α (q μ Rv v)
        + cXi exc1 μ ν1 v0 c h xp
          * (if rE (cXiBar exc2 μ ν2 v0 h) (SquareRel (fullSim (cRel Rv) h)) xp
                = 0 then 0
              else phiE α (q (cXiBar exc2 μ ν2 v0 h)
                (SquareRel (fullSim (cRel Rv) h)) xp))
        + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v)
            * (cXi exc1 μ ν1 v0 c h xp
              * (if rE (cXiBar exc2 μ ν2 v0 h)
                    (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 0
                  else phiE α (q (cXiBar exc2 μ ν2 v0 h)
                    (SquareRel (fullSim (cRel Rv) h)) xp)))) := by
    intro xp
    by_cases hres : rE (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
        (branch (v, c) xp) = 0
    · rw [if_pos hres, mul_zero]
      exact zero_le
    · rw [if_neg hres]
      have hfac := rE_cT_succ_branch Rv exc2 μ ν2 v0 v c h xp
      rw [hfac] at hres
      obtain ⟨-, hXi⟩ := mul_ne_zero_iff.mp hres
      rw [if_neg hXi]
      calc cXi exc1 μ ν1 v0 c h xp
            * phiE α (q (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
                (branch (v, c) xp))
          ≤ cXi exc1 μ ν1 v0 c h xp * (phiE α (q μ Rv v)
              + phiE α (q (cXiBar exc2 μ ν2 v0 h)
                  (SquareRel (fullSim (cRel Rv) h)) xp)
              + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v)
                  * phiE α (q (cXiBar exc2 μ ν2 v0 h)
                      (SquareRel (fullSim (cRel Rv) h)) xp))) :=
            mul_le_mul_right
              (phiE_cT_branch_le α Rv exc2 μ ν2 v0 hα v c h xp) _
        _ = cXi exc1 μ ν1 v0 c h xp * phiE α (q μ Rv v)
              + cXi exc1 μ ν1 v0 c h xp
                * phiE α (q (cXiBar exc2 μ ν2 v0 h)
                    (SquareRel (fullSim (cRel Rv) h)) xp)
              + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v)
                  * (cXi exc1 μ ν1 v0 c h xp
                    * phiE α (q (cXiBar exc2 μ ν2 v0 h)
                        (SquareRel (fullSim (cRel Rv) h)) xp))) := by ring
  calc ∑' xp, cXi exc1 μ ν1 v0 c h xp
        * (if rE (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
              (branch (v, c) xp) = 0 then 0
            else phiE α (q (cT exc2 μ ν2 v0 (h + 1))
              (fullSim (cRel Rv) (h + 1)) (branch (v, c) xp)))
      ≤ ∑' xp, (cXi exc1 μ ν1 v0 c h xp * phiE α (q μ Rv v)
          + cXi exc1 μ ν1 v0 c h xp
            * (if rE (cXiBar exc2 μ ν2 v0 h)
                  (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 0
                else phiE α (q (cXiBar exc2 μ ν2 v0 h)
                  (SquareRel (fullSim (cRel Rv) h)) xp))
          + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v)
              * (cXi exc1 μ ν1 v0 c h xp
                * (if rE (cXiBar exc2 μ ν2 v0 h)
                      (SquareRel (fullSim (cRel Rv) h)) xp = 0 then 0
                    else phiE α (q (cXiBar exc2 μ ν2 v0 h)
                      (SquareRel (fullSim (cRel Rv) h)) xp))))) :=
        ENNReal.tsum_le_tsum hpt
    _ = phiE α (q μ Rv v)
        + PhiDres α (cXi exc1 μ ν1 v0 c h) (cXiBar exc2 μ ν2 v0 h)
            (SquareRel (fullSim (cRel Rv) h))
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v)
            * PhiDres α (cXi exc1 μ ν1 v0 c h) (cXiBar exc2 μ ν2 v0 h)
                (SquareRel (fullSim (cRel Rv) h))) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
          PMF.tsum_coe, one_mul, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
          PhiDres]

/-- The forced-fresh pair step at the root `v0`. -/
lemma cPhiDres_cZ_cT_succ (hα : 1 ≤ α) (cs : CtrC) (h : ℕ) :
    PhiDres α (cZ exc1 μ ν1 v0 cs (h + 1)) (cT exc2 μ ν2 v0 (h + 1))
        (fullSim (cRel Rv) (h + 1))
      ≤ phiE α (q μ Rv v0)
        + PhiDres α (cXi exc1 μ ν1 v0 cs h) (cXiBar exc2 μ ν2 v0 h)
            (SquareRel (fullSim (cRel Rv) h))
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v0)
            * PhiDres α (cXi exc1 μ ν1 v0 cs h) (cXiBar exc2 μ ν2 v0 h)
                (SquareRel (fullSim (cRel Rv) h))) :=
  cPhiDres_muM_cT_succ α Rv μ v0 exc1 exc2 ν1 ν2 hα v0 cs h

/-! ### Fresh source: the counter mixture -/

/-- **Fresh source against a forced target**: the root mass is at most
one, so the `ν1`-mixture of square coordinates bounds the coordinate.
The sum runs over all side-1 arities: common `k` and exceptional `z`
alike contribute their cells `cXi exc1 μ ν1 v0 (ord ·)`. -/
lemma cPhiDres_cT_cZ_succ (ct : CtrC) (h : ℕ) :
    PhiDres α (cT exc1 μ ν1 v0 (h + 1)) (cZ exc2 μ ν2 v0 ct (h + 1))
        (fullSim (cRel Rv) (h + 1))
      ≤ ∑' k, ν1 k * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
          (cXi exc2 μ ν2 v0 ct h) (SquareRel (fullSim (cRel Rv) h)) := by
  rw [cT_eq_freshQ_bind exc1 μ ν1 v0 (h + 1), PhiDres_bind_left]
  calc ∑' s : V × ℕ, freshQ μ ν1 s
        * PhiDres α (muM (compK exc1 μ ν1 v0) (s.1, CtrC.ord s.2) (h + 1))
            (cZ exc2 μ ν2 v0 ct (h + 1)) (fullSim (cRel Rv) (h + 1))
      = ∑' s : V × ℕ, (μ s.1 * (if Rv s.1 v0 then 1 else 0))
          * (ν1 s.2 * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
              (cXi exc2 μ ν2 v0 ct h) (SquareRel (fullSim (cRel Rv) h))) := by
        refine tsum_congr fun s => ?_
        obtain ⟨w, l⟩ := s
        rw [cPhiDres_muM_cZ_succ α Rv μ v0 exc1 exc2 ν1 ν2 w (CtrC.ord l) ct h]
        by_cases hw : Rv w v0
        · rw [if_pos hw, if_pos hw]
          simp only [freshQ, prodPMF_apply]
          ring
        · rw [if_neg hw, if_neg hw]
          simp
    _ = (∑' w, μ w * (if Rv w v0 then 1 else 0))
        * ∑' k, ν1 k * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
            (cXi exc2 μ ν2 v0 ct h) (SquareRel (fullSim (cRel Rv) h)) :=
        tsum_prod_split (fun w => μ w * (if Rv w v0 then 1 else 0))
          (fun k => ν1 k * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
            (cXi exc2 μ ν2 v0 ct h) (SquareRel (fullSim (cRel Rv) h)))
    _ ≤ 1 * ∑' k, ν1 k * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
            (cXi exc2 μ ν2 v0 ct h) (SquareRel (fullSim (cRel Rv) h)) := by
        refine mul_le_mul_left ?_ _
        calc ∑' w, μ w * (if Rv w v0 then 1 else 0)
            ≤ ∑' w, μ w * 1 := ENNReal.tsum_le_tsum fun w =>
              mul_le_mul_right (by split_ifs <;> simp) _
          _ = 1 := by rw [tsum_congr fun w => mul_one (μ w), PMF.tsum_coe]
    _ = ∑' k, ν1 k * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
            (cXi exc2 μ ν2 v0 ct h) (SquareRel (fullSim (cRel Rv) h)) :=
        one_mul _

/-- **The fresh-fresh pair step**: the root integrates to the graph
potential `etaG`, the counter mixture to the `ν1`-average of square
coordinates toward the side-2 mixture, and the cross term is quadratic. -/
lemma cPhiDres_cT_cT_succ (hα : 1 ≤ α) (h : ℕ) :
    PhiDres α (cT exc1 μ ν1 v0 (h + 1)) (cT exc2 μ ν2 v0 (h + 1))
        (fullSim (cRel Rv) (h + 1))
      ≤ etaG α Rv μ
        + (∑' k, ν1 k * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
            (cXiBar exc2 μ ν2 v0 h) (SquareRel (fullSim (cRel Rv) h)))
        + ENNReal.ofReal (2 * α)
          * (etaG α Rv μ
            * ∑' k, ν1 k * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
                (cXiBar exc2 μ ν2 v0 h) (SquareRel (fullSim (cRel Rv) h))) := by
  rw [cT_eq_freshQ_bind exc1 μ ν1 v0 (h + 1), PhiDres_bind_left]
  calc ∑' s : V × ℕ, freshQ μ ν1 s
        * PhiDres α (muM (compK exc1 μ ν1 v0) (s.1, CtrC.ord s.2) (h + 1))
            (cT exc2 μ ν2 v0 (h + 1)) (fullSim (cRel Rv) (h + 1))
      ≤ ∑' s : V × ℕ, freshQ μ ν1 s
          * (phiE α (q μ Rv s.1)
            + PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
                (cXiBar exc2 μ ν2 v0 h) (SquareRel (fullSim (cRel Rv) h))
            + ENNReal.ofReal (2 * α)
              * (phiE α (q μ Rv s.1)
                * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
                    (cXiBar exc2 μ ν2 v0 h)
                    (SquareRel (fullSim (cRel Rv) h)))) := by
        refine ENNReal.tsum_le_tsum fun s => mul_le_mul_right ?_ _
        obtain ⟨v, k⟩ := s
        exact cPhiDres_muM_cT_succ α Rv μ v0 exc1 exc2 ν1 ν2 hα v
          (CtrC.ord k) h
    _ = (∑' s : V × ℕ, (μ s.1 * phiE α (q μ Rv s.1)) * ν1 s.2)
        + (∑' s : V × ℕ, μ s.1 * (ν1 s.2
            * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
                (cXiBar exc2 μ ν2 v0 h) (SquareRel (fullSim (cRel Rv) h))))
        + ENNReal.ofReal (2 * α)
          * ∑' s : V × ℕ, (μ s.1 * phiE α (q μ Rv s.1))
              * (ν1 s.2 * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
                  (cXiBar exc2 μ ν2 v0 h)
                  (SquareRel (fullSim (cRel Rv) h))) := by
        rw [tsum_congr fun s : V × ℕ => show freshQ μ ν1 s
            * (phiE α (q μ Rv s.1)
              + PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
                  (cXiBar exc2 μ ν2 v0 h) (SquareRel (fullSim (cRel Rv) h))
              + ENNReal.ofReal (2 * α)
                * (phiE α (q μ Rv s.1)
                  * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
                      (cXiBar exc2 μ ν2 v0 h)
                      (SquareRel (fullSim (cRel Rv) h))))
            = (μ s.1 * phiE α (q μ Rv s.1)) * ν1 s.2
              + μ s.1 * (ν1 s.2
                * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
                    (cXiBar exc2 μ ν2 v0 h) (SquareRel (fullSim (cRel Rv) h)))
              + ENNReal.ofReal (2 * α)
                * ((μ s.1 * phiE α (q μ Rv s.1))
                  * (ν1 s.2 * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord s.2) h)
                      (cXiBar exc2 μ ν2 v0 h)
                      (SquareRel (fullSim (cRel Rv) h))))
            from by simp only [freshQ, prodPMF_apply]; ring,
          ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ = etaG α Rv μ
        + (∑' k, ν1 k * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
            (cXiBar exc2 μ ν2 v0 h) (SquareRel (fullSim (cRel Rv) h)))
        + ENNReal.ofReal (2 * α)
          * (etaG α Rv μ
            * ∑' k, ν1 k * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
                (cXiBar exc2 μ ν2 v0 h)
                (SquareRel (fullSim (cRel Rv) h))) := by
        rw [tsum_prod_split (fun v => μ v * phiE α (q μ Rv v))
            (fun k => (ν1 k : ℝ≥0∞)),
          tsum_prod_split (fun v => (μ v : ℝ≥0∞))
            (fun k => ν1 k * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
              (cXiBar exc2 μ ν2 v0 h) (SquareRel (fullSim (cRel Rv) h))),
          tsum_prod_split (fun v => μ v * phiE α (q μ Rv v))
            (fun k => ν1 k * PhiDres α (cXi exc1 μ ν1 v0 (CtrC.ord k) h)
              (cXiBar exc2 μ ν2 v0 h) (SquareRel (fullSim (cRel Rv) h))),
          PMF.tsum_coe, PMF.tsum_coe, mul_one, one_mul, etaG, PhiD]

/-! ### The height-zero base case -/

/-- The forced-forced base coordinates vanish: compatible frozen roots
start at zero potential, for every pair of letters. -/
lemma cPhiDres_cZ_cZ_zero (hrefl : Rv v0 v0) (cs ct : CtrC) :
    PhiDres α (cZ exc1 μ ν1 v0 cs 0) (cZ exc2 μ ν2 v0 ct 0)
      (fullSim (cRel Rv) 0) = 0 := by
  rw [show cZ exc1 μ ν1 v0 cs 0 = PMF.pure (leaf (v0, cs)) from rfl, PhiDres,
    tsum_pure_mul]
  have hq : qE (cZ exc2 μ ν2 v0 ct 0) (fullSim (cRel Rv) 0)
      (leaf (v0, cs)) = 0 := by
    rw [show cZ exc2 μ ν2 v0 ct 0 = PMF.pure (leaf (v0, ct)) from rfl,
      qE_pure, badInd,
      if_pos ((fullSim_leaf (cRel Rv) (v0, cs) (v0, ct)).mpr hrefl)]
  have hr : rE (cZ exc2 μ ν2 v0 ct 0) (fullSim (cRel Rv) 0)
      (leaf (v0, cs)) ≠ 0 := by
    intro h0
    have hone := rE_add_qE (cZ exc2 μ ν2 v0 ct 0) (fullSim (cRel Rv) 0)
      (leaf (v0, cs))
    rw [h0, hq, zero_add] at hone
    exact zero_ne_one hone
  rw [if_neg hr, q, hq]
  simp

/-- The fresh-forced base coordinate is exactly zero: an incompatible leaf
is removed by the restriction, a compatible one contributes nothing. -/
lemma cPhiDres_cT_cZ_zero (ct : CtrC) :
    PhiDres α (cT exc1 μ ν1 v0 0) (cZ exc2 μ ν2 v0 ct 0)
      (fullSim (cRel Rv) 0) = 0 := by
  rw [PhiDres]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hxb : fullSim (cRel Rv) 0 x (leaf (v0, ct))
  · by_cases hr : rE (cZ exc2 μ ν2 v0 ct 0) (fullSim (cRel Rv) 0) x = 0
    · rw [if_pos hr, mul_zero]
    · have hq : qE (cZ exc2 μ ν2 v0 ct 0) (fullSim (cRel Rv) 0) x = 0 := by
        rw [show cZ exc2 μ ν2 v0 ct 0 = PMF.pure (leaf (v0, ct)) from rfl,
          qE_pure, badInd, if_pos hxb]
      rw [if_neg hr, q, hq]
      simp
  · have hr : rE (cZ exc2 μ ν2 v0 ct 0) (fullSim (cRel Rv) 0) x = 0 := by
      rw [show cZ exc2 μ ν2 v0 ct 0 = PMF.pure (leaf (v0, ct)) from rfl, rE]
      refine ENNReal.tsum_eq_zero.mpr fun y => ?_
      by_cases hy : fullSim (cRel Rv) 0 x y
      · rw [if_pos hy, PMF.pure_apply,
          if_neg (fun hyb : y = leaf (v0, ct) => hxb (hyb ▸ hy))]
      · rw [if_neg hy]
    rw [if_pos hr, mul_zero]

/-- The forced-fresh base coordinate is at most the root charge. -/
lemma cPhiDres_cZ_cT_zero_le (cs : CtrC) :
    PhiDres α (cZ exc1 μ ν1 v0 cs 0) (cT exc2 μ ν2 v0 0)
        (fullSim (cRel Rv) 0)
      ≤ phiE α (q μ Rv v0) := by
  rw [show cZ exc1 μ ν1 v0 cs 0 = PMF.pure (leaf (v0, cs)) from rfl, PhiDres,
    tsum_pure_mul]
  have hq : q (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0) (leaf (v0, cs))
      = q μ Rv v0 := by
    rw [q, q, qE_cT_zero Rv exc2 μ ν2 v0 v0 cs]
  by_cases hr : rE (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0)
      (leaf (v0, cs)) = 0
  · rw [if_pos hr]
    exact zero_le
  · rw [if_neg hr, hq]

/-- The fresh-fresh base coordinate is at most the graph potential. -/
lemma cPhiDres_cT_cT_zero_le :
    PhiDres α (cT exc1 μ ν1 v0 0) (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0)
      ≤ etaG α Rv μ := by
  rw [cT_eq_freshQ_bind exc1 μ ν1 v0 0, PhiDres_bind_left]
  calc ∑' s : V × ℕ, freshQ μ ν1 s
        * PhiDres α (muM (compK exc1 μ ν1 v0) (s.1, CtrC.ord s.2) 0)
            (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0)
      ≤ ∑' s : V × ℕ, (μ s.1 * phiE α (q μ Rv s.1)) * ν1 s.2 := by
        refine ENNReal.tsum_le_tsum fun s => ?_
        obtain ⟨v, k⟩ := s
        have hP : PhiDres α (muM (compK exc1 μ ν1 v0) (v, CtrC.ord k) 0)
            (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0)
            ≤ phiE α (q μ Rv v) := by
          rw [show muM (compK exc1 μ ν1 v0) (v, CtrC.ord k) 0
              = PMF.pure (leaf (v, CtrC.ord k)) from rfl, PhiDres,
            tsum_pure_mul]
          have hq : q (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0)
              (leaf (v, CtrC.ord k)) = q μ Rv v := by
            rw [q, q, qE_cT_zero Rv exc2 μ ν2 v0 v (CtrC.ord k)]
          by_cases hr : rE (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0)
              (leaf (v, CtrC.ord k)) = 0
          · rw [if_pos hr]
            exact zero_le
          · rw [if_neg hr, hq]
        calc freshQ μ ν1 (v, k)
              * PhiDres α (muM (compK exc1 μ ν1 v0) (v, CtrC.ord k) 0)
                  (cT exc2 μ ν2 v0 0) (fullSim (cRel Rv) 0)
            ≤ freshQ μ ν1 (v, k) * phiE α (q μ Rv v) :=
              mul_le_mul_right hP _
          _ = (μ v * phiE α (q μ Rv v)) * ν1 k := by
              rw [show freshQ μ ν1 (v, k) = μ v * ν1 k from rfl]
              ring
    _ = etaG α Rv μ := by
        rw [tsum_prod_split (fun v => μ v * phiE α (q μ Rv v))
          (fun l => (ν1 l : ℝ≥0∞)), ν1.tsum_coe, mul_one, etaG, PhiD]

end TwoSides

end Composite
end GraphMarkovMatching
