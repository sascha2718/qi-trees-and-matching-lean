/-
The composite tagged kernel and the cluster minorization
(`arbitrary_offspring_matching.tex`, `sec:composite`,
`def:composite-kernel` and `thm:cluster`).

The kernel is parametrized by a side function `exc : ℕ → Option (ℕ × ℕ)`
assigning to each exceptional arity its declared composite pair; ordinary
counters descend by the balanced rule, an exceptional counter enters the
chart of its pair, and the pair-indexed markers `CtrC.mark a b i` carry
the pending forced label `(v0, ord b)` down the designated path.  Markers
have zero fresh mass.

* `CtrC`, `CState`, `freshC`: tagged counters, states, and the fresh law;
* `markK`, `compK`: the marker step and the composite kernel; the
  exceptional entrance is literally `markK μ ν v0 a b 0`, mirroring
  `succM` of the formal grammar;
* `cT`, `cZ`, `cXi`, `cXiBar`: the fresh, frozen, cell, and fresh-cell
  mixture laws;
* `repZ`, `repXi`: the replacement component of a pair `(a, b)`, the
  balanced subtree with the designated port forced to `(v0, ord b)`;
* `mul_repZ_le_cZ`, `mul_repXi_le_cXi_ord`, `repXi_le_cXiBar`
  (`thm:cluster`, `eq:cluster-minor`): the replacement component is
  a literal sub-component of the plain law with coefficient `μ(v0)ν(b)`,
  hence of the fresh cell mixture with the composite floor
  `ν(a)μ(v0)ν(b)`.
-/
import GraphMarkovMatching.Composite.Grammar
import GraphMarkovMatching.Process.Kernel

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical

/-- Tagged counters: ordinary counters and the pair-indexed markers of the
composite charts.  Fresh vertices only sample ordinary counters. -/
inductive CtrC where
  | ord (k : ℕ) : CtrC
  | mark (a b i : ℕ) : CtrC
deriving DecidableEq

/-- Tagged states: a graph state and a tagged counter. -/
abbrev CState (V : Type) := V × CtrC

variable {V : Type}

/-- The fresh law: the original fresh law with the counter embedded as an
ordinary tagged counter.  Markers are never sampled freshly. -/
noncomputable def freshC (μ : PMF V) (ν : PMF ℕ) : PMF (CState V) :=
  (freshQ μ ν).map fun s => (s.1, CtrC.ord s.2)

@[simp] theorem freshC_ord_apply (μ : PMF V) (ν : PMF ℕ) (v : V) (k : ℕ) :
    freshC μ ν (v, CtrC.ord k) = μ v * ν k := by
  rw [freshC, PMF.map_apply]
  have heq : ∀ a : V × ℕ,
      ((v, CtrC.ord k) = (a.1, CtrC.ord a.2)) ↔ a = (v, k) := by
    intro a
    rcases a with ⟨w, j⟩
    constructor
    · intro h
      simp only [Prod.mk.injEq, CtrC.ord.injEq] at h ⊢
      exact ⟨h.1.symm, h.2.symm⟩
    · intro h
      simp only [Prod.mk.injEq, CtrC.ord.injEq] at h ⊢
      exact ⟨h.1.symm, h.2.symm⟩
  simp_rw [heq]
  rw [tsum_ite_eq]
  exact prodPMF_apply μ ν (v, k)

@[simp] theorem freshC_mark_apply (μ : PMF V) (ν : PMF ℕ) (v : V)
    (a b i : ℕ) : freshC μ ν (v, CtrC.mark a b i) = 0 := by
  rw [freshC, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro s
  rw [if_neg]
  intro h
  exact CtrC.noConfusion (congrArg Prod.snd h)

/-- The marker step of the pair `(a, b)` at stage `i`
(`def:composite-kernel`, rules (ii) at `i = 0` and (iii) at
`i ≥ 1`). -/
noncomputable def markK (μ : PMF V) (ν : PMF ℕ) (v0 : V) (a b i : ℕ) :
    PMF (CState V × CState V) :=
  if val a i ≤ 2 then (freshC μ ν).map fun f => ((v0, CtrC.ord b), f)
  else if val a i = 3 then PMF.pure ((v0, CtrC.ord 2), (v0, CtrC.ord b))
  else PMF.pure ((v0, CtrC.mark a b (i + 1)),
    (v0, CtrC.ord (val a i - val a i / 2)))

lemma markK_le_two {μ : PMF V} {ν : PMF ℕ} {v0 : V} {a b i : ℕ}
    (h : val a i ≤ 2) :
    markK μ ν v0 a b i = (freshC μ ν).map fun f => ((v0, CtrC.ord b), f) := by
  rw [markK, if_pos h]

lemma markK_three {μ : PMF V} {ν : PMF ℕ} {v0 : V} {a b i : ℕ}
    (h : val a i = 3) :
    markK μ ν v0 a b i =
      PMF.pure ((v0, CtrC.ord 2), (v0, CtrC.ord b)) := by
  rw [markK, if_neg (by omega), if_pos h]

lemma markK_of_ge {μ : PMF V} {ν : PMF ℕ} {v0 : V} {a b i : ℕ}
    (h : 4 ≤ val a i) :
    markK μ ν v0 a b i =
      PMF.pure ((v0, CtrC.mark a b (i + 1)),
        (v0, CtrC.ord (val a i - val a i / 2))) := by
  rw [markK, if_neg (by omega), if_neg (by omega)]

/-- The composite kernel of a side with exceptional data `exc`
(`def:composite-kernel`). -/
noncomputable def compK (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V)
    (ν : PMF ℕ) (v0 : V) : CState V → PMF (CState V × CState V)
  | (_, CtrC.mark a b i) => markK μ ν v0 a b i
  | (_, CtrC.ord k) =>
      match exc k with
      | some p => markK μ ν v0 p.1 p.2 0
      | none =>
          if 4 ≤ k then
            PMF.pure ((v0, CtrC.ord (k / 2)), (v0, CtrC.ord (k - k / 2)))
          else if k = 3 then
            (freshC μ ν).map fun f => ((v0, CtrC.ord 2), f)
          else prodPMF (freshC μ ν) (freshC μ ν)

variable (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V) (ν : PMF ℕ) (v0 : V)

@[simp] lemma compK_mark (v : V) (a b i : ℕ) :
    compK exc μ ν v0 (v, CtrC.mark a b i) = markK μ ν v0 a b i := rfl

lemma compK_ord_exc {z : ℕ} {p : ℕ × ℕ} (hz : exc z = some p) (v : V) :
    compK exc μ ν v0 (v, CtrC.ord z) = markK μ ν v0 p.1 p.2 0 := by
  simp only [compK, hz]

lemma compK_ord_none_of_ge {k : ℕ} (hk : exc k = none) (h4 : 4 ≤ k) (v : V) :
    compK exc μ ν v0 (v, CtrC.ord k) =
      PMF.pure ((v0, CtrC.ord (k / 2)), (v0, CtrC.ord (k - k / 2))) := by
  simp only [compK, hk, if_pos h4]

lemma compK_ord_none_three {k : ℕ} (hk : exc k = none) (h3 : k = 3) (v : V) :
    compK exc μ ν v0 (v, CtrC.ord k) =
      (freshC μ ν).map fun f => ((v0, CtrC.ord 2), f) := by
  subst h3
  simp only [compK, hk]
  norm_num

lemma compK_ord_none_le_two {k : ℕ} (hk : exc k = none) (h2 : k ≤ 2) (v : V) :
    compK exc μ ν v0 (v, CtrC.ord k) =
      prodPMF (freshC μ ν) (freshC μ ν) := by
  simp only [compK, hk, if_neg (by omega : ¬ 4 ≤ k),
    if_neg (by omega : ¬ k = 3)]

/-- The fresh subtree law of the side. -/
noncomputable def cT (h : ℕ) : PMF (FullLab (CState V) h) :=
  (freshC μ ν).bind fun s => muM (compK exc μ ν v0) s h

/-- The frozen subtree law below the label `(v0, c)`. -/
noncomputable def cZ (c : CtrC) (h : ℕ) : PMF (FullLab (CState V) h) :=
  muM (compK exc μ ν v0) (v0, c) h

/-- The child-pair law below a root with tagged counter `c`. -/
noncomputable def cXi (c : CtrC) (h : ℕ) :
    PMF (FullLab (CState V) h × FullLab (CState V) h) :=
  pairMix (compK exc μ ν v0) (v0, c) h

/-- The fresh cell mixture. -/
noncomputable def cXiBar (h : ℕ) :
    PMF (FullLab (CState V) h × FullLab (CState V) h) :=
  ν.bind fun k => cXi exc μ ν v0 (CtrC.ord k) h

lemma cZ_succ (c : CtrC) (h : ℕ) :
    cZ exc μ ν v0 c (h + 1) = (cXi exc μ ν v0 c h).map (branch (v0, c)) := rfl

/-- The cell law does not depend on the root state, so the exceptional cell
is the stage-zero marker cell of its pair. -/
lemma cXi_ord_exc {z : ℕ} {p : ℕ × ℕ} (hz : exc z = some p) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.ord z) h = cXi exc μ ν v0 (CtrC.mark p.1 p.2 0) h := by
  rw [cXi, cXi, pairMix, pairMix, compK_ord_exc exc μ ν v0 hz, compK_mark]

/-! ### Cell shapes -/

lemma pairMix_pure_pattern {S : Type} (P : S → PMF (S × S))
    (s a b : S) (h : ℕ) (hs : P s = PMF.pure (a, b)) :
    pairMix P s h = prodPMF (muM P a h) (muM P b h) := by
  rw [pairMix, hs]
  simp

/-- A bind in the second coordinate of a product factors out. -/
lemma bind_prodPMF_right {A X Y : Type} (ρ : PMF A) (p : PMF X)
    (τ : A → PMF Y) :
    (ρ.bind fun f => prodPMF p (τ f)) = prodPMF p (ρ.bind τ) := by
  apply PMF.ext
  intro z
  rw [PMF.bind_apply, prodPMF_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun f => ?_
  rw [prodPMF_apply]
  ring

/-- A product kernel mixes into a product of mixtures. -/
lemma prodPMF_bind_pair {A B X Y : Type} (q : PMF A) (r : PMF B)
    (F : A → PMF X) (G : B → PMF Y) :
    ((prodPMF q r).bind fun c => prodPMF (F c.1) (G c.2)) =
      prodPMF (q.bind F) (r.bind G) := by
  apply PMF.ext
  intro z
  rw [PMF.bind_apply, prodPMF_apply, PMF.bind_apply, PMF.bind_apply,
    ENNReal.tsum_prod']
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  simp only [prodPMF_apply]
  ring

/-- The cell of a kernel that freezes the left child and refreshes the
right child. -/
lemma pairMix_map_pattern {S : Type} (P : S → PMF (S × S)) (ρ : PMF S)
    (s c₀ : S) (h : ℕ) (hs : P s = ρ.map fun f => (c₀, f)) :
    pairMix P s h =
      prodPMF (muM P c₀ h) (ρ.bind fun f => muM P f h) := by
  rw [pairMix, hs, PMF.bind_map]
  have hcomp : ((fun στ : S × S => prodPMF (muM P στ.1 h) (muM P στ.2 h)) ∘
      fun f => (c₀, f)) = fun f => prodPMF (muM P c₀ h) (muM P f h) := rfl
  rw [hcomp]
  exact bind_prodPMF_right ρ (muM P c₀ h) fun f => muM P f h

/-- The cell of a kernel that refreshes both children. -/
lemma pairMix_prod_pattern {S : Type} (P : S → PMF (S × S)) (ρ : PMF S)
    (s : S) (h : ℕ) (hs : P s = prodPMF ρ ρ) :
    pairMix P s h =
      prodPMF (ρ.bind fun f => muM P f h) (ρ.bind fun f => muM P f h) := by
  rw [pairMix, hs]
  exact prodPMF_bind_pair ρ ρ (fun s => muM P s h) (fun s => muM P s h)

lemma cXi_mark_of_ge {a b i : ℕ} (hval : 4 ≤ val a i) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.mark a b i) h =
      prodPMF (cZ exc μ ν v0 (CtrC.mark a b (i + 1)) h)
        (cZ exc μ ν v0 (CtrC.ord (val a i - val a i / 2)) h) :=
  pairMix_pure_pattern _ _ _ _ _ (by rw [compK_mark, markK_of_ge hval])

lemma cXi_mark_three {a b i : ℕ} (hval : val a i = 3) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.mark a b i) h =
      prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h)
        (cZ exc μ ν v0 (CtrC.ord b) h) :=
  pairMix_pure_pattern _ _ _ _ _ (by rw [compK_mark, markK_three hval])

lemma cXi_mark_le_two {a b i : ℕ} (hval : val a i ≤ 2) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.mark a b i) h =
      prodPMF (cZ exc μ ν v0 (CtrC.ord b) h) (cT exc μ ν v0 h) :=
  pairMix_map_pattern _ _ _ _ _ (by rw [compK_mark, markK_le_two hval])

lemma cXi_ord_none_of_ge {k : ℕ} (hk : exc k = none) (h4 : 4 ≤ k) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.ord k) h =
      prodPMF (cZ exc μ ν v0 (CtrC.ord (k / 2)) h)
        (cZ exc μ ν v0 (CtrC.ord (k - k / 2)) h) :=
  pairMix_pure_pattern _ _ _ _ _ (compK_ord_none_of_ge exc μ ν v0 hk h4 v0)

lemma cXi_ord_none_three {k : ℕ} (hk : exc k = none) (h3 : k = 3) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.ord k) h =
      prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h) (cT exc μ ν v0 h) :=
  pairMix_map_pattern _ _ _ _ _ (compK_ord_none_three exc μ ν v0 hk h3 v0)

lemma cXi_ord_none_le_two {k : ℕ} (hk : exc k = none) (h2 : k ≤ 2) (h : ℕ) :
    cXi exc μ ν v0 (CtrC.ord k) h =
      prodPMF (cT exc μ ν v0 h) (cT exc μ ν v0 h) :=
  pairMix_prod_pattern _ _ _ _ (compK_ord_none_le_two exc μ ν v0 hk h2 v0)

/-! ### Minorizations -/

/-- Pointwise component minorization for an arbitrary PMF mixture. -/
lemma pmf_component_le_bind {A X : Type} (w : PMF A) (f : A → PMF X)
    (a : A) (x : X) : w a * f a x ≤ (w.bind f) x := by
  rw [PMF.bind_apply]
  exact ENNReal.le_tsum a

/-- Every frozen ordinary context is a literal component of the fresh law,
with coefficient exactly `μ(v0)ν(b)`. -/
theorem mul_cZ_le_cT (b h : ℕ) (x : FullLab (CState V) h) :
    (μ v0 * ν b) * cZ exc μ ν v0 (CtrC.ord b) h x ≤ cT exc μ ν v0 h x := by
  have hfresh := pmf_component_le_bind (freshC μ ν)
    (fun s => muM (compK exc μ ν v0) s h) (v0, CtrC.ord b) x
  rw [freshC_ord_apply] at hfresh
  exact hfresh

lemma mul_map_le_map {A X : Type} (p : ℝ≥0∞) (ρ σ : PMF A) (f : A → X)
    (hρ : ∀ x, p * ρ x ≤ σ x) (y : X) :
    p * (ρ.map f) y ≤ (σ.map f) y := by
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun x => by
    by_cases hx : y = f x
    · rw [if_pos hx, if_pos hx]
      exact hρ x
    · simp [hx]

lemma mul_prodPMF_le_prodPMF_left {A B : Type} (p : ℝ≥0∞)
    (ρ ρ' : PMF A) (τ : PMF B) (hρ : ∀ x, p * ρ x ≤ ρ' x)
    (z : A × B) :
    p * prodPMF ρ τ z ≤ prodPMF ρ' τ z := by
  rw [prodPMF_apply, prodPMF_apply]
  calc
    p * (ρ z.1 * τ z.2) = (p * ρ z.1) * τ z.2 := by ring
    _ ≤ ρ' z.1 * τ z.2 := by
      simpa [mul_comm, mul_left_comm] using
        (mul_le_mul_right (hρ z.1) (τ z.2))

lemma mul_prodPMF_le_prodPMF_right {A B : Type} (p : ℝ≥0∞)
    (ρ : PMF A) (τ τ' : PMF B) (hτ : ∀ y, p * τ y ≤ τ' y)
    (z : A × B) :
    p * prodPMF ρ τ z ≤ prodPMF ρ τ' z := by
  rw [prodPMF_apply, prodPMF_apply]
  calc
    p * (ρ z.1 * τ z.2) = ρ z.1 * (p * τ z.2) := by ring
    _ ≤ ρ z.1 * τ' z.2 := mul_le_mul_right (hτ z.2) _

lemma pmf_apply_le_one {A : Type} (p : PMF A) (a : A) : p a ≤ 1 :=
  (ENNReal.le_tsum a).trans_eq p.tsum_coe

/-! ### The replacement component -/

/-- The replacement subtree of a pair with port continuation `b`, below a
balanced root of counter `v`: the balanced subtree with the designated
port forced to the label `(v0, ord b)` (`thm:cluster`). -/
noncomputable def repZ (b : ℕ) : ℕ → (h : ℕ) → PMF (FullLab (CState V) h)
  | v, 0 => PMF.pure (leaf (v0, CtrC.ord v))
  | v, h + 1 =>
      if 4 ≤ v then
        (prodPMF (repZ b (v / 2) h)
          (cZ exc μ ν v0 (CtrC.ord (v - v / 2)) h)).map
          (branch (v0, CtrC.ord v))
      else if v = 3 then
        (prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h)
          (cZ exc μ ν v0 (CtrC.ord b) h)).map (branch (v0, CtrC.ord v))
      else
        (prodPMF (cZ exc μ ν v0 (CtrC.ord b) h) (cT exc μ ν v0 h)).map
          (branch (v0, CtrC.ord v))

/-- **The cluster minorization at subtree level**: the replacement subtree
is a sub-component of the plain balanced subtree, with coefficient exactly
`μ(v0)ν(b)`, provided the balanced counters involved are not
exceptional. -/
theorem mul_repZ_le_cZ (b : ℕ) :
    ∀ (h v : ℕ), (∀ j, j ≤ v → exc j = none) →
      ∀ x, (μ v0 * ν b) * repZ exc μ ν v0 b v h x ≤
        cZ exc μ ν v0 (CtrC.ord v) h x := by
  intro h
  induction h with
  | zero =>
      intro v hv x
      have hle : μ v0 * ν b ≤ 1 :=
        mul_le_one' (pmf_apply_le_one μ v0) (pmf_apply_le_one ν b)
      calc (μ v0 * ν b) * repZ exc μ ν v0 b v 0 x
          ≤ 1 * repZ exc μ ν v0 b v 0 x := mul_le_mul_left hle _
        _ = repZ exc μ ν v0 b v 0 x := one_mul _
        _ = cZ exc μ ν v0 (CtrC.ord v) 0 x := rfl
  | succ h ih =>
      intro v hv x
      rcases Nat.lt_or_ge v 3 with h2 | h3
      · -- v ≤ 2 : the port is the left child, the right child is fresh
        rw [show repZ exc μ ν v0 b v (h + 1) =
            (prodPMF (cZ exc μ ν v0 (CtrC.ord b) h) (cT exc μ ν v0 h)).map
              (branch (v0, CtrC.ord v)) from by
          rw [repZ, if_neg (by omega), if_neg (by omega)]]
        rw [cZ_succ, cXi_ord_none_le_two exc μ ν v0 (hv v le_rfl) (by omega)]
        refine mul_map_le_map _ _ _ _ (fun z => ?_) x
        exact mul_prodPMF_le_prodPMF_left _ _ _ _
          (fun y => mul_cZ_le_cT exc μ ν v0 b h y) z
      · rcases Nat.lt_or_ge v 4 with h4 | h4
        · -- v = 3 : the port is the right child
          have hv3 : v = 3 := by omega
          subst hv3
          rw [show repZ exc μ ν v0 b 3 (h + 1) =
              (prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h)
                (cZ exc μ ν v0 (CtrC.ord b) h)).map
                (branch (v0, CtrC.ord 3)) from by
            rw [repZ, if_neg (by omega), if_pos rfl]]
          rw [cZ_succ, cXi_ord_none_three exc μ ν v0 (hv 3 le_rfl) rfl]
          refine mul_map_le_map _ _ _ _ (fun z => ?_) x
          exact mul_prodPMF_le_prodPMF_right _ _ _ _
            (fun y => mul_cZ_le_cT exc μ ν v0 b h y) z
        · -- v ≥ 4 : recurse along the designated path
          rw [show repZ exc μ ν v0 b v (h + 1) =
              (prodPMF (repZ exc μ ν v0 b (v / 2) h)
                (cZ exc μ ν v0 (CtrC.ord (v - v / 2)) h)).map
                (branch (v0, CtrC.ord v)) from by
            rw [repZ, if_pos h4]]
          rw [cZ_succ, cXi_ord_none_of_ge exc μ ν v0 (hv v le_rfl) h4]
          refine mul_map_le_map _ _ _ _ (fun z => ?_) x
          exact mul_prodPMF_le_prodPMF_left _ _ _ _
            (ih (v / 2) (fun j hj => hv j (by omega))) z

/-- The replacement cell of a pair `(a, b)`: the child pair below a
balanced counter-`a` root with the designated port forced. -/
noncomputable def repXi (a b : ℕ) (h : ℕ) :
    PMF (FullLab (CState V) h × FullLab (CState V) h) :=
  if 4 ≤ a then
    prodPMF (repZ exc μ ν v0 b (a / 2) h)
      (cZ exc μ ν v0 (CtrC.ord (a - a / 2)) h)
  else if a = 3 then
    prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h) (cZ exc μ ν v0 (CtrC.ord b) h)
  else prodPMF (cZ exc μ ν v0 (CtrC.ord b) h) (cT exc μ ν v0 h)

/-- **The cluster minorization at cell level** (`eq:cluster-minor`,
first half): the replacement cell is a sub-component of the balanced cell
of `a`, with coefficient `μ(v0)ν(b)`. -/
theorem mul_repXi_le_cXi_ord {a : ℕ} (b : ℕ)
    (ha : ∀ j, j ≤ a → exc j = none) (h : ℕ)
    (x : FullLab (CState V) h × FullLab (CState V) h) :
    (μ v0 * ν b) * repXi exc μ ν v0 a b h x ≤
      cXi exc μ ν v0 (CtrC.ord a) h x := by
  rcases Nat.lt_or_ge a 3 with h2 | h3
  · rw [show repXi exc μ ν v0 a b h =
        prodPMF (cZ exc μ ν v0 (CtrC.ord b) h) (cT exc μ ν v0 h) from by
      rw [repXi, if_neg (by omega), if_neg (by omega)]]
    rw [cXi_ord_none_le_two exc μ ν v0 (ha a le_rfl) (by omega)]
    exact mul_prodPMF_le_prodPMF_left _ _ _ _
      (fun y => mul_cZ_le_cT exc μ ν v0 b h y) x
  · rcases Nat.lt_or_ge a 4 with h4 | h4
    · have ha3 : a = 3 := by omega
      subst ha3
      rw [show repXi exc μ ν v0 3 b h =
          prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h)
            (cZ exc μ ν v0 (CtrC.ord b) h) from by
        rw [repXi, if_neg (by omega), if_pos rfl]]
      rw [cXi_ord_none_three exc μ ν v0 (ha 3 le_rfl) rfl]
      exact mul_prodPMF_le_prodPMF_right _ _ _ _
        (fun y => mul_cZ_le_cT exc μ ν v0 b h y) x
    · rw [show repXi exc μ ν v0 a b h =
          prodPMF (repZ exc μ ν v0 b (a / 2) h)
            (cZ exc μ ν v0 (CtrC.ord (a - a / 2)) h) from by
        rw [repXi, if_pos h4]]
      rw [cXi_ord_none_of_ge exc μ ν v0 (ha a le_rfl) h4]
      exact mul_prodPMF_le_prodPMF_left _ _ _ _
        (mul_repZ_le_cZ exc μ ν v0 b h (a / 2)
          (fun j hj => ha j (by omega))) x

/-- **The composite cluster floor** (`thm:cluster`, second minorisation
of `eq:cluster-minor`): the replacement cell of a declared pair is a
literal component of the fresh cell mixture, with the exact mass
`ν(a) μ(v0) ν(b)`, the floor of `eq:composite-floor` before the bound
`μ(v0) ≥ 1/2` is applied. -/
theorem repXi_le_cXiBar {a : ℕ} (b : ℕ)
    (ha : ∀ j, j ≤ a → exc j = none) (h : ℕ)
    (x : FullLab (CState V) h × FullLab (CState V) h) :
    (ν a * (μ v0 * ν b)) * repXi exc μ ν v0 a b h x ≤
      cXiBar exc μ ν v0 h x := by
  calc (ν a * (μ v0 * ν b)) * repXi exc μ ν v0 a b h x
      = ν a * ((μ v0 * ν b) * repXi exc μ ν v0 a b h x) := by ring
    _ ≤ ν a * cXi exc μ ν v0 (CtrC.ord a) h x :=
      mul_le_mul_right (mul_repXi_le_cXi_ord exc μ ν v0 b ha h x) _
    _ ≤ cXiBar exc μ ν v0 h x :=
      pmf_component_le_bind ν (fun k => cXi exc μ ν v0 (CtrC.ord k) h) a x

/-- Every charged cell is a component of the fresh cell mixture. -/
lemma cXi_le_cXiBar (k h : ℕ)
    (x : FullLab (CState V) h × FullLab (CState V) h) :
    ν k * cXi exc μ ν v0 (CtrC.ord k) h x ≤ cXiBar exc μ ν v0 h x :=
  pmf_component_le_bind ν (fun j => cXi exc μ ν v0 (CtrC.ord j) h) k x

end Composite
end GraphMarkovMatching
