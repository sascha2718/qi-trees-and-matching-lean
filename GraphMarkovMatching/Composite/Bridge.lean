/-
The bridge between the composite lemmas and the ledger functionals
(`arbitrary_offspring_matching.tex`, `sec:composite`).

The composite modules state their results in local functionals (`simDeg`,
`invTilt`, tsum-form dead sums); the row assembly runs in the established
functionals of the one-law stack (`rE`, `qE`, `PhiD`, `PhiDres`, `WresD`,
`screenE`, `zMass`, `failureD`).  This file is the dictionary.

* `simDeg_eq_rE`, `simDeg_add_qE`, `qE_eq_one_sub_simDeg`,
  `simDeg_eq_one_sub_qE`: the degree bridge; the local compatible mass is
  literally the established good degree, and the bad degree is its
  complement;
* `rE_stateMap`, `qE_stateMap`, `q_stateMap`, `WresD_stateMap` (and the
  `_pair_` forms): the projection identities; against the matching
  relation every degree of a tagged law is the corresponding degree of
  its state marginal at the projected point, so the target side sees the
  state marginal only and the source integrand factors through the state
  projection;
* `PhiD_congr_target` / `PhiD_congr_source` (and `PhiDres`, `zMass`,
  `failureD`, `screenE` analogues, single and pair): the state-marginal
  invariance of the ledger functionals: the source law and the target law
  can each be replaced by any law with the same `stateMap`-pushforward;
* `WresD_cXi_exc`, `PhiDres_cXi_exc_target`, ..., `screenE_cZ_mark_source`:
  the marked/replacement identifications; by `stateMap_cXi_exc` and
  `stateMap_cZ_mark`, every functional takes the same value on the marked
  cell `cXi (CtrC.ord z)` of a declared pair as on its replacement cell
  `repXi`, and on the frozen marker subtree `cZ (CtrC.mark a b i)` as on
  the replacement subtree `repZ` at the running value, in source and in
  target position;
* `compFloor`, `mul_compFloor_rE_cXi_le`, `WresD_cXiBar_le_sum`,
  `tsum_WresD_cXiBar_le_sum`, `screenE_WresD_cXiBar_le_sum`
  (`thm:mixture-tilt-composite` in ledger form): the weighted
  fresh-target mixture bound; the restricted inverse degree of the fresh
  cell mixture is below the charged sum of component inverse degrees, each
  weighted by the inverse power of a common quantity: `ν k` for a common
  arity and the composite floor `ν p₁ · (μ v₀ · ν p₂)` for a declared
  exceptional arity, pointwise, integrated against an arbitrary source
  law, and inside an arbitrary screen;
* `mirrorCtr`, `cZ_hasMatchingSupport` (with the `_common`, `_exc`,
  `_mark` instances), `screenE_cT_opposite_eq_zero`, `zMass_cT_cT_eq_zero`,
  `PhiDres_cT_cT_eq_PhiD`, `zMass_cZ_mirror_eq_zero`,
  `PhiDres_cZ_mirror_eq_PhiD`, `screenE_cZ_mirror_mem_eq_zero`
  (`thm:support-equality`, `thm:exact-pruning` in ledger form): the
  support witness packaged as `HasMatchingSupport` for the mirrored
  letter pairs, and the resulting exact pruning: screens whose dead set
  contains the opposite fresh law or the mirrored component vanish, the
  zero-interface mass between the two fresh laws vanishes, and the
  restricted potential of the fresh pair is the full one.
-/
import GraphMarkovMatching.Composite.Tilt
import GraphMarkovMatching.Composite.Endpoint
import GraphMarkovMatching.Potential.ZeroInterface
import GraphMarkovMatching.Process.MatchingSupport

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type}

/-! ### The degree bridge -/

/-- The local compatible mass is the established good degree, with the
same argument orientation. -/
theorem simDeg_eq_rE {X : Type} (ρ : PMF X) (Rel : X → X → Prop) (x : X) :
    simDeg ρ Rel x = rE ρ Rel x := rfl

/-- The two degrees partition the mass, in the local notation. -/
theorem simDeg_add_qE {X : Type} (ρ : PMF X) (Rel : X → X → Prop) (x : X) :
    simDeg ρ Rel x + qE ρ Rel x = 1 :=
  rE_add_qE ρ Rel x

/-- The established bad degree is the complement of the local degree. -/
theorem qE_eq_one_sub_simDeg {X : Type} (ρ : PMF X) (Rel : X → X → Prop)
    (x : X) : qE ρ Rel x = 1 - simDeg ρ Rel x := by
  rw [simDeg_eq_rE]
  exact ENNReal.eq_sub_of_add_eq rE_ne_top
    (by rw [add_comm]; exact rE_add_qE ρ Rel x)

/-- The local degree is the complement of the established bad degree. -/
theorem simDeg_eq_one_sub_qE {X : Type} (ρ : PMF X) (Rel : X → X → Prop)
    (x : X) : simDeg ρ Rel x = 1 - qE ρ Rel x := by
  rw [simDeg_eq_rE]
  exact ENNReal.eq_sub_of_add_eq qE_ne_top (rE_add_qE ρ Rel x)

/-! ### Generic projection layer

A relation that transports along a projection `f` sees laws only through
their `f`-pushforward, on the target side pointwise and on the source
side after the change of variables `tsum_map_mul`. -/

private lemma tsum_mul_comp_congr {X Y : Type} (f : X → Y)
    {ρ ρ' : PMF X} (heq : ρ.map f = ρ'.map f) (G : Y → ℝ≥0∞) :
    ∑' x, ρ x * G (f x) = ∑' x, ρ' x * G (f x) := by
  rw [← tsum_map_mul ρ f G, heq, tsum_map_mul ρ' f G]

section GenericProjection

variable {X Y : Type} (f : X → Y) {RX : X → X → Prop} {RY : Y → Y → Prop}
variable (hiff : ∀ x y, RX x y ↔ RY (f x) (f y))
include hiff

private lemma rE_comp_map (ρ : PMF X) (x : X) :
    rE ρ RX x = rE (ρ.map f) RY (f x) := by
  calc rE ρ RX x
      = ∑' a, ρ a * (if RY (f x) (f a) then 1 else 0) := by
        rw [rE]
        refine tsum_congr fun a => ?_
        by_cases hxa : RX x a
        · rw [if_pos hxa, if_pos ((hiff x a).mp hxa), mul_one]
        · rw [if_neg hxa, if_neg fun hc => hxa ((hiff x a).mpr hc), mul_zero]
    _ = ∑' w, (ρ.map f) w * (if RY (f x) w then 1 else 0) :=
        (tsum_map_mul ρ f fun w => if RY (f x) w then 1 else 0).symm
    _ = rE (ρ.map f) RY (f x) := by
        rw [rE]
        refine tsum_congr fun w => ?_
        by_cases hw : RY (f x) w
        · rw [if_pos hw, if_pos hw, mul_one]
        · rw [if_neg hw, if_neg hw, mul_zero]

private lemma qE_comp_map (ρ : PMF X) (x : X) :
    qE ρ RX x = qE (ρ.map f) RY (f x) := by
  calc qE ρ RX x
      = ∑' a, ρ a * (if RY (f x) (f a) then 0 else 1) := by
        rw [qE]
        refine tsum_congr fun a => ?_
        by_cases hxa : RX x a
        · rw [if_pos hxa, if_pos ((hiff x a).mp hxa), mul_zero]
        · rw [if_neg hxa, if_neg fun hc => hxa ((hiff x a).mpr hc), mul_one]
    _ = ∑' w, (ρ.map f) w * (if RY (f x) w then 0 else 1) :=
        (tsum_map_mul ρ f fun w => if RY (f x) w then 0 else 1).symm
    _ = qE (ρ.map f) RY (f x) := by
        rw [qE]
        refine tsum_congr fun w => ?_
        by_cases hw : RY (f x) w
        · rw [if_pos hw, if_pos hw, mul_zero]
        · rw [if_neg hw, if_neg hw, mul_one]

private lemma q_comp_map (ρ : PMF X) (x : X) :
    q ρ RX x = q (ρ.map f) RY (f x) := by
  rw [q, q, qE_comp_map f hiff ρ x]

private lemma WresD_comp_map (α : ℝ) (ρ : PMF X) (x : X) :
    WresD α ρ RX x = WresD α (ρ.map f) RY (f x) := by
  rw [WresD, WresD, rE_comp_map f hiff ρ x, WnnD, WnnD,
    q_comp_map f hiff ρ x]

private lemma rE_congr_map {ρ ρ' : PMF X} (heq : ρ.map f = ρ'.map f)
    (x : X) : rE ρ RX x = rE ρ' RX x := by
  rw [rE_comp_map f hiff ρ x, rE_comp_map f hiff ρ' x, heq]

private lemma qE_congr_map {ρ ρ' : PMF X} (heq : ρ.map f = ρ'.map f)
    (x : X) : qE ρ RX x = qE ρ' RX x := by
  rw [qE_comp_map f hiff ρ x, qE_comp_map f hiff ρ' x, heq]

private lemma q_congr_map {ρ ρ' : PMF X} (heq : ρ.map f = ρ'.map f)
    (x : X) : q ρ RX x = q ρ' RX x := by
  rw [q_comp_map f hiff ρ x, q_comp_map f hiff ρ' x, heq]

private lemma WresD_congr_map (α : ℝ) {ρ ρ' : PMF X}
    (heq : ρ.map f = ρ'.map f) (x : X) :
    WresD α ρ RX x = WresD α ρ' RX x := by
  rw [WresD_comp_map f hiff α ρ x, WresD_comp_map f hiff α ρ' x, heq]

private lemma PhiD_congr_map_target (α : ℝ) (ρs : PMF X) {ρt ρt' : PMF X}
    (heq : ρt.map f = ρt'.map f) :
    PhiD α ρs ρt RX = PhiD α ρs ρt' RX := by
  rw [PhiD, PhiD]
  exact tsum_congr fun x => by rw [q_congr_map f hiff heq x]

private lemma PhiDres_congr_map_target (α : ℝ) (ρs : PMF X)
    {ρt ρt' : PMF X} (heq : ρt.map f = ρt'.map f) :
    PhiDres α ρs ρt RX = PhiDres α ρs ρt' RX := by
  rw [PhiDres, PhiDres]
  exact tsum_congr fun x => by
    rw [rE_congr_map f hiff heq x, q_congr_map f hiff heq x]

private lemma zMass_congr_map_target (ρs : PMF X) {ρt ρt' : PMF X}
    (heq : ρt.map f = ρt'.map f) :
    zMass ρs ρt RX = zMass ρs ρt' RX := by
  rw [zMass, zMass]
  exact tsum_congr fun y => by rw [rE_congr_map f hiff heq y]

private lemma failureD_congr_map_target (ρs : PMF X) {ρt ρt' : PMF X}
    (heq : ρt.map f = ρt'.map f) :
    failureD ρs ρt RX = failureD ρs ρt' RX := by
  rw [failureD, failureD]
  exact tsum_congr fun x => by rw [qE_congr_map f hiff heq x]

private lemma PhiD_congr_map_source (α : ℝ) {ρs ρs' : PMF X}
    (heq : ρs.map f = ρs'.map f) (ρt : PMF X) :
    PhiD α ρs ρt RX = PhiD α ρs' ρt RX := by
  have hint : ∀ (τ : PMF X) (x : X),
      τ x * phiE α (q ρt RX x)
        = τ x * phiE α (q (ρt.map f) RY (f x)) := fun τ x => by
    rw [q_comp_map f hiff ρt x]
  calc PhiD α ρs ρt RX
      = ∑' x, ρs x * phiE α (q (ρt.map f) RY (f x)) := by
        rw [PhiD]; exact tsum_congr fun x => hint ρs x
    _ = ∑' x, ρs' x * phiE α (q (ρt.map f) RY (f x)) :=
        tsum_mul_comp_congr f heq fun w => phiE α (q (ρt.map f) RY w)
    _ = PhiD α ρs' ρt RX := by
        rw [PhiD]; exact (tsum_congr fun x => hint ρs' x).symm

private lemma PhiDres_congr_map_source (α : ℝ) {ρs ρs' : PMF X}
    (heq : ρs.map f = ρs'.map f) (ρt : PMF X) :
    PhiDres α ρs ρt RX = PhiDres α ρs' ρt RX := by
  have hint : ∀ x : X,
      (if rE ρt RX x = 0 then 0 else phiE α (q ρt RX x))
        = (if rE (ρt.map f) RY (f x) = 0 then 0
            else phiE α (q (ρt.map f) RY (f x))) := fun x => by
    rw [rE_comp_map f hiff ρt x, q_comp_map f hiff ρt x]
  calc PhiDres α ρs ρt RX
      = ∑' x, ρs x * (if rE (ρt.map f) RY (f x) = 0 then 0
          else phiE α (q (ρt.map f) RY (f x))) := by
        rw [PhiDres]; exact tsum_congr fun x => by rw [hint x]
    _ = ∑' x, ρs' x * (if rE (ρt.map f) RY (f x) = 0 then 0
          else phiE α (q (ρt.map f) RY (f x))) :=
        tsum_mul_comp_congr f heq fun w =>
          if rE (ρt.map f) RY w = 0 then 0 else phiE α (q (ρt.map f) RY w)
    _ = PhiDres α ρs' ρt RX := by
        rw [PhiDres]; exact (tsum_congr fun x => by rw [hint x]).symm

private lemma zMass_congr_map_source {ρs ρs' : PMF X}
    (heq : ρs.map f = ρs'.map f) (ρt : PMF X) :
    zMass ρs ρt RX = zMass ρs' ρt RX := by
  have hint : ∀ y : X,
      (if rE ρt RX y = 0 then (1 : ℝ≥0∞) else 0)
        = (if rE (ρt.map f) RY (f y) = 0 then 1 else 0) := fun y => by
    rw [rE_comp_map f hiff ρt y]
  calc zMass ρs ρt RX
      = ∑' y, ρs y * (if rE (ρt.map f) RY (f y) = 0 then 1 else 0) := by
        rw [zMass]; exact tsum_congr fun y => by rw [hint y]
    _ = ∑' y, ρs' y * (if rE (ρt.map f) RY (f y) = 0 then 1 else 0) :=
        tsum_mul_comp_congr f heq fun w =>
          if rE (ρt.map f) RY w = 0 then 1 else 0
    _ = zMass ρs' ρt RX := by
        rw [zMass]; exact (tsum_congr fun y => by rw [hint y]).symm

private lemma failureD_congr_map_source {ρs ρs' : PMF X}
    (heq : ρs.map f = ρs'.map f) (ρt : PMF X) :
    failureD ρs ρt RX = failureD ρs' ρt RX := by
  have hint : ∀ x : X, qE ρt RX x = qE (ρt.map f) RY (f x) := fun x =>
    qE_comp_map f hiff ρt x
  calc failureD ρs ρt RX
      = ∑' x, ρs x * qE (ρt.map f) RY (f x) := by
        rw [failureD]; exact tsum_congr fun x => by rw [hint x]
    _ = ∑' x, ρs' x * qE (ρt.map f) RY (f x) :=
        tsum_mul_comp_congr f heq fun w => qE (ρt.map f) RY w
    _ = failureD ρs' ρt RX := by
        rw [failureD]; exact (tsum_congr fun x => by rw [hint x]).symm

private lemma screenInd_comp_map (zs : List (PMF X)) (x : X) :
    screenInd RX zs x
      = screenInd RY (zs.map fun ρ => ρ.map f) (f x) := by
  rw [screenInd, screenInd]
  refine if_congr ?_ rfl rfl
  constructor
  · intro hall τ hτ
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hτ
    rw [← rE_comp_map f hiff ρ x]
    exact hall ρ hρ
  · intro hall ρ hρ
    rw [rE_comp_map f hiff ρ x]
    exact hall (ρ.map f) (List.mem_map.mpr ⟨ρ, hρ, rfl⟩)

private lemma screenInd_congr_zlist {zs zs' : List (PMF X)}
    (hzz : List.Forall₂ (fun ρ ρ' => ρ.map f = ρ'.map f) zs zs') (x : X) :
    screenInd RX zs x = screenInd RX zs' x := by
  rw [screenInd, screenInd]
  refine if_congr ?_ rfl rfl
  induction hzz with
  | nil => exact Iff.rfl
  | @cons ρ ρ' tl tl' hρ htl ih =>
      rw [List.forall_mem_cons, List.forall_mem_cons]
      exact and_congr (by rw [rE_congr_map f hiff hρ x]) ih

private lemma screenE_congr_map_source {ρs ρs' : PMF X}
    (heq : ρs.map f = ρs'.map f) (zs : List (PMF X)) (g0 : Y → ℝ≥0∞) :
    screenE ρs RX zs (fun x => g0 (f x))
      = screenE ρs' RX zs (fun x => g0 (f x)) := by
  have hint : ∀ (τ : PMF X) (x : X),
      τ x * screenInd RX zs x * g0 (f x)
        = τ x * (screenInd RY (zs.map fun ρ => ρ.map f) (f x) * g0 (f x)) :=
    fun τ x => by rw [mul_assoc, screenInd_comp_map f hiff zs x]
  calc screenE ρs RX zs (fun x => g0 (f x))
      = ∑' x, ρs x
          * (screenInd RY (zs.map fun ρ => ρ.map f) (f x) * g0 (f x)) := by
        rw [screenE]; exact tsum_congr fun x => hint ρs x
    _ = ∑' x, ρs' x
          * (screenInd RY (zs.map fun ρ => ρ.map f) (f x) * g0 (f x)) :=
        tsum_mul_comp_congr f heq fun w =>
          screenInd RY (zs.map fun ρ => ρ.map f) w * g0 w
    _ = screenE ρs' RX zs (fun x => g0 (f x)) := by
        rw [screenE]; exact (tsum_congr fun x => hint ρs' x).symm

end GenericProjection

/-! ### State-marginal invariance, single-tree laws -/

section SingleTree

variable (Rv : V → V → Prop) (h : ℕ)

/-- The good degree of a tagged law against the matching relation is the
good degree of its state marginal at the projected point. -/
theorem rE_stateMap (ρt : PMF (FullLab (CState V) h))
    (x : FullLab (CState V) h) :
    rE ρt (fullSim (cRel Rv) h) x
      = rE (ρt.map (stateMap h)) (fullSim Rv h) (stateMap h x) :=
  rE_comp_map (stateMap h) (fullSim_cRel_iff Rv h) ρt x

/-- The bad-degree form of `rE_stateMap`. -/
theorem qE_stateMap (ρt : PMF (FullLab (CState V) h))
    (x : FullLab (CState V) h) :
    qE ρt (fullSim (cRel Rv) h) x
      = qE (ρt.map (stateMap h)) (fullSim Rv h) (stateMap h x) :=
  qE_comp_map (stateMap h) (fullSim_cRel_iff Rv h) ρt x

/-- The real bad-degree form of `rE_stateMap`. -/
theorem q_stateMap (ρt : PMF (FullLab (CState V) h))
    (x : FullLab (CState V) h) :
    q ρt (fullSim (cRel Rv) h) x
      = q (ρt.map (stateMap h)) (fullSim Rv h) (stateMap h x) :=
  q_comp_map (stateMap h) (fullSim_cRel_iff Rv h) ρt x

/-- The restricted inverse-degree form of `rE_stateMap`. -/
theorem WresD_stateMap (α : ℝ) (ρt : PMF (FullLab (CState V) h))
    (x : FullLab (CState V) h) :
    WresD α ρt (fullSim (cRel Rv) h) x
      = WresD α (ρt.map (stateMap h)) (fullSim Rv h) (stateMap h x) :=
  WresD_comp_map (stateMap h) (fullSim_cRel_iff Rv h) α ρt x

/-- Degrees only see state marginals: target replacement for `rE`. -/
theorem rE_congr_stateMap {ρt ρt' : PMF (FullLab (CState V) h)}
    (heq : ρt.map (stateMap h) = ρt'.map (stateMap h))
    (x : FullLab (CState V) h) :
    rE ρt (fullSim (cRel Rv) h) x = rE ρt' (fullSim (cRel Rv) h) x :=
  rE_congr_map (stateMap h) (fullSim_cRel_iff Rv h) heq x

/-- Target replacement for `qE`. -/
theorem qE_congr_stateMap {ρt ρt' : PMF (FullLab (CState V) h)}
    (heq : ρt.map (stateMap h) = ρt'.map (stateMap h))
    (x : FullLab (CState V) h) :
    qE ρt (fullSim (cRel Rv) h) x = qE ρt' (fullSim (cRel Rv) h) x :=
  qE_congr_map (stateMap h) (fullSim_cRel_iff Rv h) heq x

/-- Target replacement for `q`. -/
theorem q_congr_stateMap {ρt ρt' : PMF (FullLab (CState V) h)}
    (heq : ρt.map (stateMap h) = ρt'.map (stateMap h))
    (x : FullLab (CState V) h) :
    q ρt (fullSim (cRel Rv) h) x = q ρt' (fullSim (cRel Rv) h) x :=
  q_congr_map (stateMap h) (fullSim_cRel_iff Rv h) heq x

/-- Target replacement for `WresD`. -/
theorem WresD_congr_stateMap (α : ℝ) {ρt ρt' : PMF (FullLab (CState V) h)}
    (heq : ρt.map (stateMap h) = ρt'.map (stateMap h))
    (x : FullLab (CState V) h) :
    WresD α ρt (fullSim (cRel Rv) h) x
      = WresD α ρt' (fullSim (cRel Rv) h) x :=
  WresD_congr_map (stateMap h) (fullSim_cRel_iff Rv h) α heq x

/-- Target replacement for the full directed potential. -/
theorem PhiD_congr_target (α : ℝ) (ρs : PMF (FullLab (CState V) h))
    {ρt ρt' : PMF (FullLab (CState V) h)}
    (heq : ρt.map (stateMap h) = ρt'.map (stateMap h)) :
    PhiD α ρs ρt (fullSim (cRel Rv) h)
      = PhiD α ρs ρt' (fullSim (cRel Rv) h) :=
  PhiD_congr_map_target (stateMap h) (fullSim_cRel_iff Rv h) α ρs heq

/-- Source replacement for the full directed potential. -/
theorem PhiD_congr_source (α : ℝ) {ρs ρs' : PMF (FullLab (CState V) h)}
    (heq : ρs.map (stateMap h) = ρs'.map (stateMap h))
    (ρt : PMF (FullLab (CState V) h)) :
    PhiD α ρs ρt (fullSim (cRel Rv) h)
      = PhiD α ρs' ρt (fullSim (cRel Rv) h) :=
  PhiD_congr_map_source (stateMap h) (fullSim_cRel_iff Rv h) α heq ρt

/-- Target replacement for the restricted directed potential. -/
theorem PhiDres_congr_target (α : ℝ) (ρs : PMF (FullLab (CState V) h))
    {ρt ρt' : PMF (FullLab (CState V) h)}
    (heq : ρt.map (stateMap h) = ρt'.map (stateMap h)) :
    PhiDres α ρs ρt (fullSim (cRel Rv) h)
      = PhiDres α ρs ρt' (fullSim (cRel Rv) h) :=
  PhiDres_congr_map_target (stateMap h) (fullSim_cRel_iff Rv h) α ρs heq

/-- Source replacement for the restricted directed potential. -/
theorem PhiDres_congr_source (α : ℝ) {ρs ρs' : PMF (FullLab (CState V) h)}
    (heq : ρs.map (stateMap h) = ρs'.map (stateMap h))
    (ρt : PMF (FullLab (CState V) h)) :
    PhiDres α ρs ρt (fullSim (cRel Rv) h)
      = PhiDres α ρs' ρt (fullSim (cRel Rv) h) :=
  PhiDres_congr_map_source (stateMap h) (fullSim_cRel_iff Rv h) α heq ρt

/-- Target replacement for the zero-interface mass. -/
theorem zMass_congr_target (ρs : PMF (FullLab (CState V) h))
    {ρt ρt' : PMF (FullLab (CState V) h)}
    (heq : ρt.map (stateMap h) = ρt'.map (stateMap h)) :
    zMass ρs ρt (fullSim (cRel Rv) h)
      = zMass ρs ρt' (fullSim (cRel Rv) h) :=
  zMass_congr_map_target (stateMap h) (fullSim_cRel_iff Rv h) ρs heq

/-- Source replacement for the zero-interface mass. -/
theorem zMass_congr_source {ρs ρs' : PMF (FullLab (CState V) h)}
    (heq : ρs.map (stateMap h) = ρs'.map (stateMap h))
    (ρt : PMF (FullLab (CState V) h)) :
    zMass ρs ρt (fullSim (cRel Rv) h)
      = zMass ρs' ρt (fullSim (cRel Rv) h) :=
  zMass_congr_map_source (stateMap h) (fullSim_cRel_iff Rv h) heq ρt

/-- Target replacement for the mismatch mass. -/
theorem failureD_congr_target (ρs : PMF (FullLab (CState V) h))
    {ρt ρt' : PMF (FullLab (CState V) h)}
    (heq : ρt.map (stateMap h) = ρt'.map (stateMap h)) :
    failureD ρs ρt (fullSim (cRel Rv) h)
      = failureD ρs ρt' (fullSim (cRel Rv) h) :=
  failureD_congr_map_target (stateMap h) (fullSim_cRel_iff Rv h) ρs heq

/-- Source replacement for the mismatch mass. -/
theorem failureD_congr_source {ρs ρs' : PMF (FullLab (CState V) h)}
    (heq : ρs.map (stateMap h) = ρs'.map (stateMap h))
    (ρt : PMF (FullLab (CState V) h)) :
    failureD ρs ρt (fullSim (cRel Rv) h)
      = failureD ρs' ρt (fullSim (cRel Rv) h) :=
  failureD_congr_map_source (stateMap h) (fullSim_cRel_iff Rv h) heq ρt

/-- Screens only see state marginals of their zero lists: elementwise
replacement of the dead laws. -/
theorem screenE_congr_zlist (ρs : PMF (FullLab (CState V) h))
    {zs zs' : List (PMF (FullLab (CState V) h))}
    (hzz : List.Forall₂
      (fun ρ ρ' => ρ.map (stateMap h) = ρ'.map (stateMap h)) zs zs')
    (g : FullLab (CState V) h → ℝ≥0∞) :
    screenE ρs (fullSim (cRel Rv) h) zs g
      = screenE ρs (fullSim (cRel Rv) h) zs' g := by
  rw [screenE, screenE]
  exact tsum_congr fun x => by
    rw [screenInd_congr_zlist (stateMap h) (fullSim_cRel_iff Rv h) hzz x]

/-- Source replacement for a screen with a restricted inverse-degree
normalization. -/
theorem screenE_WresD_congr_source (α : ℝ)
    {ρs ρs' : PMF (FullLab (CState V) h)}
    (heq : ρs.map (stateMap h) = ρs'.map (stateMap h))
    (zs : List (PMF (FullLab (CState V) h)))
    (ρt : PMF (FullLab (CState V) h)) :
    screenE ρs (fullSim (cRel Rv) h) zs (WresD α ρt (fullSim (cRel Rv) h))
      = screenE ρs' (fullSim (cRel Rv) h) zs
          (WresD α ρt (fullSim (cRel Rv) h)) := by
  have hg : WresD α ρt (fullSim (cRel Rv) h)
      = fun x => WresD α (ρt.map (stateMap h)) (fullSim Rv h)
          (stateMap h x) :=
    funext fun x => WresD_stateMap Rv h α ρt x
  rw [hg]
  exact screenE_congr_map_source (stateMap h) (fullSim_cRel_iff Rv h) heq zs
    (WresD α (ρt.map (stateMap h)) (fullSim Rv h))

end SingleTree

/-! ### State-marginal invariance, child-pair laws -/

section PairLaws

variable (Rv : V → V → Prop) (h : ℕ)

/-- The pair form of `rE_stateMap`, against the squared matching
relation. -/
theorem rE_pair_stateMap
    (ρt : PMF (FullLab (CState V) h × FullLab (CState V) h))
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE ρt (SquareRel (fullSim (cRel Rv) h)) xp
      = rE (ρt.map (Prod.map (stateMap h) (stateMap h)))
          (SquareRel (fullSim Rv h))
          (Prod.map (stateMap h) (stateMap h) xp) :=
  rE_comp_map (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) ρt xp

/-- The pair form of `qE_stateMap`. -/
theorem qE_pair_stateMap
    (ρt : PMF (FullLab (CState V) h × FullLab (CState V) h))
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    qE ρt (SquareRel (fullSim (cRel Rv) h)) xp
      = qE (ρt.map (Prod.map (stateMap h) (stateMap h)))
          (SquareRel (fullSim Rv h))
          (Prod.map (stateMap h) (stateMap h) xp) :=
  qE_comp_map (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) ρt xp

/-- The pair form of `q_stateMap`. -/
theorem q_pair_stateMap
    (ρt : PMF (FullLab (CState V) h × FullLab (CState V) h))
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    q ρt (SquareRel (fullSim (cRel Rv) h)) xp
      = q (ρt.map (Prod.map (stateMap h) (stateMap h)))
          (SquareRel (fullSim Rv h))
          (Prod.map (stateMap h) (stateMap h) xp) :=
  q_comp_map (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) ρt xp

/-- The pair form of `WresD_stateMap`. -/
theorem WresD_pair_stateMap (α : ℝ)
    (ρt : PMF (FullLab (CState V) h × FullLab (CState V) h))
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    WresD α ρt (SquareRel (fullSim (cRel Rv) h)) xp
      = WresD α (ρt.map (Prod.map (stateMap h) (stateMap h)))
          (SquareRel (fullSim Rv h))
          (Prod.map (stateMap h) (stateMap h) xp) :=
  WresD_comp_map (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) α ρt xp

/-- Pair target replacement for `rE`. -/
theorem rE_pair_congr_stateMap
    {ρt ρt' : PMF (FullLab (CState V) h × FullLab (CState V) h)}
    (heq : ρt.map (Prod.map (stateMap h) (stateMap h))
      = ρt'.map (Prod.map (stateMap h) (stateMap h)))
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    rE ρt (SquareRel (fullSim (cRel Rv) h)) xp
      = rE ρt' (SquareRel (fullSim (cRel Rv) h)) xp :=
  rE_congr_map (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) heq xp

/-- Pair target replacement for `qE`. -/
theorem qE_pair_congr_stateMap
    {ρt ρt' : PMF (FullLab (CState V) h × FullLab (CState V) h)}
    (heq : ρt.map (Prod.map (stateMap h) (stateMap h))
      = ρt'.map (Prod.map (stateMap h) (stateMap h)))
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    qE ρt (SquareRel (fullSim (cRel Rv) h)) xp
      = qE ρt' (SquareRel (fullSim (cRel Rv) h)) xp :=
  qE_congr_map (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) heq xp

/-- Pair target replacement for `q`. -/
theorem q_pair_congr_stateMap
    {ρt ρt' : PMF (FullLab (CState V) h × FullLab (CState V) h)}
    (heq : ρt.map (Prod.map (stateMap h) (stateMap h))
      = ρt'.map (Prod.map (stateMap h) (stateMap h)))
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    q ρt (SquareRel (fullSim (cRel Rv) h)) xp
      = q ρt' (SquareRel (fullSim (cRel Rv) h)) xp :=
  q_congr_map (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) heq xp

/-- Pair target replacement for `WresD`. -/
theorem WresD_pair_congr_stateMap (α : ℝ)
    {ρt ρt' : PMF (FullLab (CState V) h × FullLab (CState V) h)}
    (heq : ρt.map (Prod.map (stateMap h) (stateMap h))
      = ρt'.map (Prod.map (stateMap h) (stateMap h)))
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    WresD α ρt (SquareRel (fullSim (cRel Rv) h)) xp
      = WresD α ρt' (SquareRel (fullSim (cRel Rv) h)) xp :=
  WresD_congr_map (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) α heq xp

/-- Pair target replacement for the full directed potential. -/
theorem PhiD_pair_congr_target (α : ℝ)
    (ρs : PMF (FullLab (CState V) h × FullLab (CState V) h))
    {ρt ρt' : PMF (FullLab (CState V) h × FullLab (CState V) h)}
    (heq : ρt.map (Prod.map (stateMap h) (stateMap h))
      = ρt'.map (Prod.map (stateMap h) (stateMap h))) :
    PhiD α ρs ρt (SquareRel (fullSim (cRel Rv) h))
      = PhiD α ρs ρt' (SquareRel (fullSim (cRel Rv) h)) :=
  PhiD_congr_map_target (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) α ρs heq

/-- Pair source replacement for the full directed potential. -/
theorem PhiD_pair_congr_source (α : ℝ)
    {ρs ρs' : PMF (FullLab (CState V) h × FullLab (CState V) h)}
    (heq : ρs.map (Prod.map (stateMap h) (stateMap h))
      = ρs'.map (Prod.map (stateMap h) (stateMap h)))
    (ρt : PMF (FullLab (CState V) h × FullLab (CState V) h)) :
    PhiD α ρs ρt (SquareRel (fullSim (cRel Rv) h))
      = PhiD α ρs' ρt (SquareRel (fullSim (cRel Rv) h)) :=
  PhiD_congr_map_source (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) α heq ρt

/-- Pair target replacement for the restricted directed potential. -/
theorem PhiDres_pair_congr_target (α : ℝ)
    (ρs : PMF (FullLab (CState V) h × FullLab (CState V) h))
    {ρt ρt' : PMF (FullLab (CState V) h × FullLab (CState V) h)}
    (heq : ρt.map (Prod.map (stateMap h) (stateMap h))
      = ρt'.map (Prod.map (stateMap h) (stateMap h))) :
    PhiDres α ρs ρt (SquareRel (fullSim (cRel Rv) h))
      = PhiDres α ρs ρt' (SquareRel (fullSim (cRel Rv) h)) :=
  PhiDres_congr_map_target (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) α ρs heq

/-- Pair source replacement for the restricted directed potential. -/
theorem PhiDres_pair_congr_source (α : ℝ)
    {ρs ρs' : PMF (FullLab (CState V) h × FullLab (CState V) h)}
    (heq : ρs.map (Prod.map (stateMap h) (stateMap h))
      = ρs'.map (Prod.map (stateMap h) (stateMap h)))
    (ρt : PMF (FullLab (CState V) h × FullLab (CState V) h)) :
    PhiDres α ρs ρt (SquareRel (fullSim (cRel Rv) h))
      = PhiDres α ρs' ρt (SquareRel (fullSim (cRel Rv) h)) :=
  PhiDres_congr_map_source (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) α heq ρt

/-- Pair target replacement for the zero-interface mass. -/
theorem zMass_pair_congr_target
    (ρs : PMF (FullLab (CState V) h × FullLab (CState V) h))
    {ρt ρt' : PMF (FullLab (CState V) h × FullLab (CState V) h)}
    (heq : ρt.map (Prod.map (stateMap h) (stateMap h))
      = ρt'.map (Prod.map (stateMap h) (stateMap h))) :
    zMass ρs ρt (SquareRel (fullSim (cRel Rv) h))
      = zMass ρs ρt' (SquareRel (fullSim (cRel Rv) h)) :=
  zMass_congr_map_target (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) ρs heq

/-- Pair source replacement for the zero-interface mass. -/
theorem zMass_pair_congr_source
    {ρs ρs' : PMF (FullLab (CState V) h × FullLab (CState V) h)}
    (heq : ρs.map (Prod.map (stateMap h) (stateMap h))
      = ρs'.map (Prod.map (stateMap h) (stateMap h)))
    (ρt : PMF (FullLab (CState V) h × FullLab (CState V) h)) :
    zMass ρs ρt (SquareRel (fullSim (cRel Rv) h))
      = zMass ρs' ρt (SquareRel (fullSim (cRel Rv) h)) :=
  zMass_congr_map_source (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) heq ρt

/-- Pair form of the zero-list replacement for screens. -/
theorem screenE_pair_congr_zlist
    (ρs : PMF (FullLab (CState V) h × FullLab (CState V) h))
    {zs zs' : List (PMF (FullLab (CState V) h × FullLab (CState V) h))}
    (hzz : List.Forall₂
      (fun ρ ρ' => ρ.map (Prod.map (stateMap h) (stateMap h))
        = ρ'.map (Prod.map (stateMap h) (stateMap h))) zs zs')
    (g : FullLab (CState V) h × FullLab (CState V) h → ℝ≥0∞) :
    screenE ρs (SquareRel (fullSim (cRel Rv) h)) zs g
      = screenE ρs (SquareRel (fullSim (cRel Rv) h)) zs' g := by
  rw [screenE, screenE]
  exact tsum_congr fun xp => by
    rw [screenInd_congr_zlist (Prod.map (stateMap h) (stateMap h))
      (squareRel_cRel_iff Rv h) hzz xp]

/-- Pair source replacement for a screen with a restricted inverse-degree
normalization. -/
theorem screenE_pair_WresD_congr_source (α : ℝ)
    {ρs ρs' : PMF (FullLab (CState V) h × FullLab (CState V) h)}
    (heq : ρs.map (Prod.map (stateMap h) (stateMap h))
      = ρs'.map (Prod.map (stateMap h) (stateMap h)))
    (zs : List (PMF (FullLab (CState V) h × FullLab (CState V) h)))
    (ρt : PMF (FullLab (CState V) h × FullLab (CState V) h)) :
    screenE ρs (SquareRel (fullSim (cRel Rv) h)) zs
        (WresD α ρt (SquareRel (fullSim (cRel Rv) h)))
      = screenE ρs' (SquareRel (fullSim (cRel Rv) h)) zs
          (WresD α ρt (SquareRel (fullSim (cRel Rv) h))) := by
  have hg : WresD α ρt (SquareRel (fullSim (cRel Rv) h))
      = fun xp => WresD α (ρt.map (Prod.map (stateMap h) (stateMap h)))
          (SquareRel (fullSim Rv h))
          (Prod.map (stateMap h) (stateMap h) xp) :=
    funext fun xp => WresD_pair_stateMap Rv h α ρt xp
  rw [hg]
  exact screenE_congr_map_source (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) heq zs
    (WresD α (ρt.map (Prod.map (stateMap h) (stateMap h)))
      (SquareRel (fullSim Rv h)))

end PairLaws

/-! ### The marked/replacement identifications

By the state-marginal equalities `stateMap_cXi_exc` and `stateMap_cZ_mark`
every ledger functional identifies the marked coordinates with the
replacement coordinates, in source and in target position; the other side
of each functional is an arbitrary law, so the two side packs are
unrelated. -/

section MarkedReplacement

variable (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V) (ν : PMF ℕ) (v0 : V)

/-- The marked cell and the replacement cell have the same restricted
inverse degree. -/
theorem WresD_cXi_exc (α : ℝ) (Rv : V → V → Prop) {z : ℕ} {p : ℕ × ℕ}
    (hz : exc z = some p) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    WresD α (cXi exc μ ν v0 (CtrC.ord z) h)
        (SquareRel (fullSim (cRel Rv) h)) xp
      = WresD α (repXi exc μ ν v0 p.1 p.2 h)
          (SquareRel (fullSim (cRel Rv) h)) xp :=
  WresD_pair_congr_stateMap Rv h α (stateMap_cXi_exc exc μ ν v0 hz h) xp

/-- The marked cell as a target of the full potential is the replacement
cell. -/
theorem PhiD_cXi_exc_target (α : ℝ) (Rv : V → V → Prop) {z : ℕ}
    {p : ℕ × ℕ} (hz : exc z = some p) (h : ℕ)
    (ρs : PMF (FullLab (CState V) h × FullLab (CState V) h)) :
    PhiD α ρs (cXi exc μ ν v0 (CtrC.ord z) h)
        (SquareRel (fullSim (cRel Rv) h))
      = PhiD α ρs (repXi exc μ ν v0 p.1 p.2 h)
          (SquareRel (fullSim (cRel Rv) h)) :=
  PhiD_pair_congr_target Rv h α ρs (stateMap_cXi_exc exc μ ν v0 hz h)

/-- The marked cell as a source of the full potential is the replacement
cell. -/
theorem PhiD_cXi_exc_source (α : ℝ) (Rv : V → V → Prop) {z : ℕ}
    {p : ℕ × ℕ} (hz : exc z = some p) (h : ℕ)
    (ρt : PMF (FullLab (CState V) h × FullLab (CState V) h)) :
    PhiD α (cXi exc μ ν v0 (CtrC.ord z) h) ρt
        (SquareRel (fullSim (cRel Rv) h))
      = PhiD α (repXi exc μ ν v0 p.1 p.2 h) ρt
          (SquareRel (fullSim (cRel Rv) h)) :=
  PhiD_pair_congr_source Rv h α (stateMap_cXi_exc exc μ ν v0 hz h) ρt

/-- The marked cell as a target of the restricted potential is the
replacement cell. -/
theorem PhiDres_cXi_exc_target (α : ℝ) (Rv : V → V → Prop) {z : ℕ}
    {p : ℕ × ℕ} (hz : exc z = some p) (h : ℕ)
    (ρs : PMF (FullLab (CState V) h × FullLab (CState V) h)) :
    PhiDres α ρs (cXi exc μ ν v0 (CtrC.ord z) h)
        (SquareRel (fullSim (cRel Rv) h))
      = PhiDres α ρs (repXi exc μ ν v0 p.1 p.2 h)
          (SquareRel (fullSim (cRel Rv) h)) :=
  PhiDres_pair_congr_target Rv h α ρs (stateMap_cXi_exc exc μ ν v0 hz h)

/-- The marked cell as a source of the restricted potential is the
replacement cell. -/
theorem PhiDres_cXi_exc_source (α : ℝ) (Rv : V → V → Prop) {z : ℕ}
    {p : ℕ × ℕ} (hz : exc z = some p) (h : ℕ)
    (ρt : PMF (FullLab (CState V) h × FullLab (CState V) h)) :
    PhiDres α (cXi exc μ ν v0 (CtrC.ord z) h) ρt
        (SquareRel (fullSim (cRel Rv) h))
      = PhiDres α (repXi exc μ ν v0 p.1 p.2 h) ρt
          (SquareRel (fullSim (cRel Rv) h)) :=
  PhiDres_pair_congr_source Rv h α (stateMap_cXi_exc exc μ ν v0 hz h) ρt

/-- The marked cell as a target of the zero-interface mass is the
replacement cell. -/
theorem zMass_cXi_exc_target (Rv : V → V → Prop) {z : ℕ} {p : ℕ × ℕ}
    (hz : exc z = some p) (h : ℕ)
    (ρs : PMF (FullLab (CState V) h × FullLab (CState V) h)) :
    zMass ρs (cXi exc μ ν v0 (CtrC.ord z) h)
        (SquareRel (fullSim (cRel Rv) h))
      = zMass ρs (repXi exc μ ν v0 p.1 p.2 h)
          (SquareRel (fullSim (cRel Rv) h)) :=
  zMass_pair_congr_target Rv h ρs (stateMap_cXi_exc exc μ ν v0 hz h)

/-- The marked cell as a source of the zero-interface mass is the
replacement cell. -/
theorem zMass_cXi_exc_source (Rv : V → V → Prop) {z : ℕ} {p : ℕ × ℕ}
    (hz : exc z = some p) (h : ℕ)
    (ρt : PMF (FullLab (CState V) h × FullLab (CState V) h)) :
    zMass (cXi exc μ ν v0 (CtrC.ord z) h) ρt
        (SquareRel (fullSim (cRel Rv) h))
      = zMass (repXi exc μ ν v0 p.1 p.2 h) ρt
          (SquareRel (fullSim (cRel Rv) h)) :=
  zMass_pair_congr_source Rv h (stateMap_cXi_exc exc μ ν v0 hz h) ρt

/-- The marked cell as a screen source is the replacement cell, for any
restricted inverse-degree normalization. -/
theorem screenE_cXi_exc_source (α : ℝ) (Rv : V → V → Prop) {z : ℕ}
    {p : ℕ × ℕ} (hz : exc z = some p) (h : ℕ)
    (zs : List (PMF (FullLab (CState V) h × FullLab (CState V) h)))
    (ρt : PMF (FullLab (CState V) h × FullLab (CState V) h)) :
    screenE (cXi exc μ ν v0 (CtrC.ord z) h)
        (SquareRel (fullSim (cRel Rv) h)) zs
        (WresD α ρt (SquareRel (fullSim (cRel Rv) h)))
      = screenE (repXi exc μ ν v0 p.1 p.2 h)
          (SquareRel (fullSim (cRel Rv) h)) zs
          (WresD α ρt (SquareRel (fullSim (cRel Rv) h))) :=
  screenE_pair_WresD_congr_source Rv h α
    (stateMap_cXi_exc exc μ ν v0 hz h) zs ρt

/-- The frozen marker subtree and the replacement subtree have the same
restricted inverse degree. -/
theorem WresD_cZ_mark (α : ℝ) (Rv : V → V → Prop) (a b i h : ℕ)
    (x : FullLab (CState V) h) :
    WresD α (cZ exc μ ν v0 (CtrC.mark a b i) h) (fullSim (cRel Rv) h) x
      = WresD α (repZ exc μ ν v0 b (val a i) h) (fullSim (cRel Rv) h) x :=
  WresD_congr_stateMap Rv h α (stateMap_cZ_mark exc μ ν v0 a b h i) x

/-- The frozen marker subtree as a target of the full potential is the
replacement subtree. -/
theorem PhiD_cZ_mark_target (α : ℝ) (Rv : V → V → Prop) (a b i h : ℕ)
    (ρs : PMF (FullLab (CState V) h)) :
    PhiD α ρs (cZ exc μ ν v0 (CtrC.mark a b i) h) (fullSim (cRel Rv) h)
      = PhiD α ρs (repZ exc μ ν v0 b (val a i) h) (fullSim (cRel Rv) h) :=
  PhiD_congr_target Rv h α ρs (stateMap_cZ_mark exc μ ν v0 a b h i)

/-- The frozen marker subtree as a source of the full potential is the
replacement subtree. -/
theorem PhiD_cZ_mark_source (α : ℝ) (Rv : V → V → Prop) (a b i h : ℕ)
    (ρt : PMF (FullLab (CState V) h)) :
    PhiD α (cZ exc μ ν v0 (CtrC.mark a b i) h) ρt (fullSim (cRel Rv) h)
      = PhiD α (repZ exc μ ν v0 b (val a i) h) ρt (fullSim (cRel Rv) h) :=
  PhiD_congr_source Rv h α (stateMap_cZ_mark exc μ ν v0 a b h i) ρt

/-- The frozen marker subtree as a target of the restricted potential is
the replacement subtree. -/
theorem PhiDres_cZ_mark_target (α : ℝ) (Rv : V → V → Prop) (a b i h : ℕ)
    (ρs : PMF (FullLab (CState V) h)) :
    PhiDres α ρs (cZ exc μ ν v0 (CtrC.mark a b i) h) (fullSim (cRel Rv) h)
      = PhiDres α ρs (repZ exc μ ν v0 b (val a i) h)
          (fullSim (cRel Rv) h) :=
  PhiDres_congr_target Rv h α ρs (stateMap_cZ_mark exc μ ν v0 a b h i)

/-- The frozen marker subtree as a source of the restricted potential is
the replacement subtree. -/
theorem PhiDres_cZ_mark_source (α : ℝ) (Rv : V → V → Prop) (a b i h : ℕ)
    (ρt : PMF (FullLab (CState V) h)) :
    PhiDres α (cZ exc μ ν v0 (CtrC.mark a b i) h) ρt (fullSim (cRel Rv) h)
      = PhiDres α (repZ exc μ ν v0 b (val a i) h) ρt
          (fullSim (cRel Rv) h) :=
  PhiDres_congr_source Rv h α (stateMap_cZ_mark exc μ ν v0 a b h i) ρt

/-- The frozen marker subtree as a target of the zero-interface mass is
the replacement subtree. -/
theorem zMass_cZ_mark_target (Rv : V → V → Prop) (a b i h : ℕ)
    (ρs : PMF (FullLab (CState V) h)) :
    zMass ρs (cZ exc μ ν v0 (CtrC.mark a b i) h) (fullSim (cRel Rv) h)
      = zMass ρs (repZ exc μ ν v0 b (val a i) h) (fullSim (cRel Rv) h) :=
  zMass_congr_target Rv h ρs (stateMap_cZ_mark exc μ ν v0 a b h i)

/-- The frozen marker subtree as a source of the zero-interface mass is
the replacement subtree. -/
theorem zMass_cZ_mark_source (Rv : V → V → Prop) (a b i h : ℕ)
    (ρt : PMF (FullLab (CState V) h)) :
    zMass (cZ exc μ ν v0 (CtrC.mark a b i) h) ρt (fullSim (cRel Rv) h)
      = zMass (repZ exc μ ν v0 b (val a i) h) ρt (fullSim (cRel Rv) h) :=
  zMass_congr_source Rv h (stateMap_cZ_mark exc μ ν v0 a b h i) ρt

/-- The frozen marker subtree as a screen source is the replacement
subtree, for any restricted inverse-degree normalization. -/
theorem screenE_cZ_mark_source (α : ℝ) (Rv : V → V → Prop) (a b i h : ℕ)
    (zs : List (PMF (FullLab (CState V) h)))
    (ρt : PMF (FullLab (CState V) h)) :
    screenE (cZ exc μ ν v0 (CtrC.mark a b i) h) (fullSim (cRel Rv) h) zs
        (WresD α ρt (fullSim (cRel Rv) h))
      = screenE (repZ exc μ ν v0 b (val a i) h) (fullSim (cRel Rv) h) zs
          (WresD α ρt (fullSim (cRel Rv) h)) :=
  screenE_WresD_congr_source Rv h α
    (stateMap_cZ_mark exc μ ν v0 a b h i) zs ρt

end MarkedReplacement

/-! ### The weighted fresh-target mixture bound
(`thm:mixture-tilt-composite`) -/

section PricedMixture

variable (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V) (ν : PMF ℕ) (v0 : V)

/-- The composite floor of an arity: its own weight for a common arity,
the composite replacement floor `ν p₁ · (μ v₀ · ν p₂)` for a declared
exceptional arity.  Every value is a common quantity. -/
noncomputable def compFloor (k : ℕ) : ℝ≥0∞ :=
  match exc k with
  | none => ν k
  | some p => ν p.1 * (μ v0 * ν p.2)

lemma compFloor_none {k : ℕ} (hk : exc k = none) :
    compFloor exc μ ν v0 k = ν k := by
  simp [compFloor, hk]

lemma compFloor_some {k : ℕ} {p : ℕ × ℕ} (hk : exc k = some p) :
    compFloor exc μ ν v0 k = ν p.1 * (μ v0 * ν p.2) := by
  simp [compFloor, hk]

/-- The composite floor of a charged arity is charged, under the
declared-pair hypotheses. -/
lemma compFloor_ne_zero
    (hdecl : ∀ k p, exc k = some p → ν p.1 ≠ 0 ∧ ν p.2 ≠ 0)
    (hμ0 : μ v0 ≠ 0) {k : ℕ} (hνk : ν k ≠ 0) :
    compFloor exc μ ν v0 k ≠ 0 := by
  rcases hexc : exc k with _ | p
  · rw [compFloor_none exc μ ν v0 hexc]
    exact hνk
  · rw [compFloor_some exc μ ν v0 hexc]
    exact mul_ne_zero (hdecl k p hexc).1
      (mul_ne_zero hμ0 (hdecl k p hexc).2)

private lemma cXiBar_eq_bind (h : ℕ) :
    cXiBar exc μ ν v0 h
      = ν.bind fun k => cXi exc μ ν v0 (CtrC.ord k) h := rfl

/-- **The composite floor minorizes the mixture degree**: the good degree
of every cell of the fresh mixture, marked or not, enters the mixture
degree with at least its composite floor.  For a common arity this is the
literal mixture component; for a declared exceptional arity the marked
cell first trades places with its replacement cell (same state marginal)
and then enters through the cluster floor `repXi_le_cXiBar`. -/
theorem mul_compFloor_rE_cXi_le
    (hpair : ∀ k p, exc k = some p → ∀ j, j ≤ p.1 → exc j = none)
    (Rv : V → V → Prop) (h k : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    compFloor exc μ ν v0 k
        * rE (cXi exc μ ν v0 (CtrC.ord k) h)
            (SquareRel (fullSim (cRel Rv) h)) xp
      ≤ rE (cXiBar exc μ ν v0 h) (SquareRel (fullSim (cRel Rv) h)) xp := by
  rcases hexc : exc k with _ | p
  · rw [compFloor_none exc μ ν v0 hexc, cXiBar_eq_bind exc μ ν v0 h]
    exact mul_rE_le_rE_bind ν (fun j => cXi exc μ ν v0 (CtrC.ord j) h)
      (SquareRel (fullSim (cRel Rv) h)) xp k
  · rw [compFloor_some exc μ ν v0 hexc,
      rE_pair_congr_stateMap Rv h (stateMap_cXi_exc exc μ ν v0 hexc h) xp]
    have hmono := mul_simDeg_le_simDeg (ν p.1 * (μ v0 * ν p.2))
      (SquareRel (fullSim (cRel Rv) h))
      (fun y => repXi_le_cXiBar exc μ ν v0 p.2 (hpair k p hexc) h y) xp
    rw [simDeg_eq_rE, simDeg_eq_rE] at hmono
    exact hmono

/-- **The weighted fresh-target mixture bound, pointwise**
(`thm:mixture-tilt-composite` in the `WresD` shape of the one-law stack):
the restricted inverse degree of the fresh cell mixture is below the
charged sum of component inverse degrees, each weighted by the inverse
power of its
composite floor: `(ν k)^{-α}` for a common arity, and
`(ν p₁ · (μ v₀ · ν p₂))^{-α}` for a declared exceptional arity, whose
component is the marked cell `cXi (CtrC.ord k)`, or equivalently (by
`WresD_cXi_exc`) the replacement cell.  No bare inverse exceptional mass
forms. -/
theorem WresD_cXiBar_le_sum
    (hpair : ∀ k p, exc k = some p → ∀ j, j ≤ p.1 → exc j = none)
    (hdecl : ∀ k p, exc k = some p → ν p.1 ≠ 0 ∧ ν p.2 ≠ 0)
    (hμ0 : μ v0 ≠ 0) {α : ℝ} (hα0 : 0 ≤ α) (Rv : V → V → Prop) (h : ℕ)
    (xp : FullLab (CState V) h × FullLab (CState V) h) :
    WresD α (cXiBar exc μ ν v0 h) (SquareRel (fullSim (cRel Rv) h)) xp
      ≤ ∑' k, (if ν k = 0 then 0 else
          compFloor exc μ ν v0 k ^ (-α)
            * WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
                (SquareRel (fullSim (cRel Rv) h)) xp) := by
  by_cases hbar : rE (cXiBar exc μ ν v0 h)
      (SquareRel (fullSim (cRel Rv) h)) xp = 0
  · rw [WresD, if_pos hbar]
    exact zero_le
  · have hnall : ¬ ∀ k, ν k = 0 ∨
        rE (cXi exc μ ν v0 (CtrC.ord k) h)
          (SquareRel (fullSim (cRel Rv) h)) xp = 0 := by
      intro hall
      apply hbar
      rw [cXiBar_eq_bind exc μ ν v0 h]
      exact (rE_bind_eq_zero_iff ν
        (fun k => cXi exc μ ν v0 (CtrC.ord k) h)
        (SquareRel (fullSim (cRel Rv) h)) xp).mpr hall
    obtain ⟨k, hk⟩ := not_forall.mp hnall
    obtain ⟨hνk, hXik⟩ := not_or.mp hk
    have hfl0 : compFloor exc μ ν v0 k ≠ 0 :=
      compFloor_ne_zero exc μ ν v0 hdecl hμ0 hνk
    have hmin := mul_compFloor_rE_cXi_le exc μ ν v0 hpair Rv h k xp
    have hstep : WresD α (cXiBar exc μ ν v0 h)
          (SquareRel (fullSim (cRel Rv) h)) xp
        ≤ compFloor exc μ ν v0 k ^ (-α)
          * WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
              (SquareRel (fullSim (cRel Rv) h)) xp := by
      rw [← rE_rpow_neg_eq_WresD (cXiBar exc μ ν v0 h)
          (SquareRel (fullSim (cRel Rv) h)) xp hbar,
        ← rE_rpow_neg_eq_WresD (cXi exc μ ν v0 (CtrC.ord k) h)
          (SquareRel (fullSim (cRel Rv) h)) xp hXik,
        ← ENNReal.mul_rpow_of_ne_zero hfl0 hXik (-α)]
      exact rpow_neg_antitone hα0 hmin
    refine hstep.trans ?_
    refine (le_of_eq ?_).trans (ENNReal.le_tsum k)
    rw [if_neg hνk]

/-- The integrated priced mixture bound, against an arbitrary source
law. -/
theorem tsum_WresD_cXiBar_le_sum
    (hpair : ∀ k p, exc k = some p → ∀ j, j ≤ p.1 → exc j = none)
    (hdecl : ∀ k p, exc k = some p → ν p.1 ≠ 0 ∧ ν p.2 ≠ 0)
    (hμ0 : μ v0 ≠ 0) {α : ℝ} (hα0 : 0 ≤ α) (Rv : V → V → Prop) (h : ℕ)
    (ρs : PMF (FullLab (CState V) h × FullLab (CState V) h)) :
    ∑' xp, ρs xp * WresD α (cXiBar exc μ ν v0 h)
        (SquareRel (fullSim (cRel Rv) h)) xp
      ≤ ∑' k, (if ν k = 0 then 0 else
          compFloor exc μ ν v0 k ^ (-α)
            * ∑' xp, ρs xp * WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
                (SquareRel (fullSim (cRel Rv) h)) xp) := by
  calc ∑' xp, ρs xp * WresD α (cXiBar exc μ ν v0 h)
        (SquareRel (fullSim (cRel Rv) h)) xp
      ≤ ∑' xp, ρs xp * ∑' k, (if ν k = 0 then 0 else
          compFloor exc μ ν v0 k ^ (-α)
            * WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
                (SquareRel (fullSim (cRel Rv) h)) xp) :=
        ENNReal.tsum_le_tsum fun xp => mul_le_mul_right
          (WresD_cXiBar_le_sum exc μ ν v0 hpair hdecl hμ0 hα0 Rv h xp) _
    _ = ∑' k, ∑' xp, ρs xp * (if ν k = 0 then 0 else
          compFloor exc μ ν v0 k ^ (-α)
            * WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
                (SquareRel (fullSim (cRel Rv) h)) xp) := by
        calc ∑' xp, ρs xp * ∑' k, (if ν k = 0 then 0 else
              compFloor exc μ ν v0 k ^ (-α)
                * WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
                    (SquareRel (fullSim (cRel Rv) h)) xp)
            = ∑' xp, ∑' k, ρs xp * (if ν k = 0 then 0 else
                compFloor exc μ ν v0 k ^ (-α)
                  * WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
                      (SquareRel (fullSim (cRel Rv) h)) xp) :=
              tsum_congr fun xp => ENNReal.tsum_mul_left.symm
          _ = _ := ENNReal.tsum_comm
    _ = ∑' k, (if ν k = 0 then 0 else
          compFloor exc μ ν v0 k ^ (-α)
            * ∑' xp, ρs xp * WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
                (SquareRel (fullSim (cRel Rv) h)) xp) := by
        refine tsum_congr fun k => ?_
        by_cases hνk : ν k = 0
        · rw [if_pos hνk]
          exact ENNReal.tsum_eq_zero.mpr fun xp => by
            rw [if_pos hνk, mul_zero]
        · rw [if_neg hνk, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun xp => by rw [if_neg hνk]; ring

/-- The priced mixture bound inside an arbitrary screen: the one-sided
conversion used by the screen rows. -/
theorem screenE_WresD_cXiBar_le_sum
    (hpair : ∀ k p, exc k = some p → ∀ j, j ≤ p.1 → exc j = none)
    (hdecl : ∀ k p, exc k = some p → ν p.1 ≠ 0 ∧ ν p.2 ≠ 0)
    (hμ0 : μ v0 ≠ 0) {α : ℝ} (hα0 : 0 ≤ α) (Rv : V → V → Prop) (h : ℕ)
    (ρs : PMF (FullLab (CState V) h × FullLab (CState V) h))
    (zs : List (PMF (FullLab (CState V) h × FullLab (CState V) h))) :
    screenE ρs (SquareRel (fullSim (cRel Rv) h)) zs
        (WresD α (cXiBar exc μ ν v0 h) (SquareRel (fullSim (cRel Rv) h)))
      ≤ ∑' k, (if ν k = 0 then 0 else
          compFloor exc μ ν v0 k ^ (-α)
            * screenE ρs (SquareRel (fullSim (cRel Rv) h)) zs
                (WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
                  (SquareRel (fullSim (cRel Rv) h)))) := by
  rw [screenE]
  calc ∑' xp, ρs xp * screenInd (SquareRel (fullSim (cRel Rv) h)) zs xp
        * WresD α (cXiBar exc μ ν v0 h)
            (SquareRel (fullSim (cRel Rv) h)) xp
      ≤ ∑' xp, ρs xp * screenInd (SquareRel (fullSim (cRel Rv) h)) zs xp
          * ∑' k, (if ν k = 0 then 0 else
              compFloor exc μ ν v0 k ^ (-α)
                * WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
                    (SquareRel (fullSim (cRel Rv) h)) xp) :=
        ENNReal.tsum_le_tsum fun xp => mul_le_mul_right
          (WresD_cXiBar_le_sum exc μ ν v0 hpair hdecl hμ0 hα0 Rv h xp) _
    _ = ∑' k, ∑' xp, ρs xp
          * screenInd (SquareRel (fullSim (cRel Rv) h)) zs xp
          * (if ν k = 0 then 0 else
              compFloor exc μ ν v0 k ^ (-α)
                * WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
                    (SquareRel (fullSim (cRel Rv) h)) xp) := by
        calc ∑' xp, ρs xp * screenInd (SquareRel (fullSim (cRel Rv) h)) zs xp
              * ∑' k, (if ν k = 0 then 0 else
                  compFloor exc μ ν v0 k ^ (-α)
                    * WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
                        (SquareRel (fullSim (cRel Rv) h)) xp)
            = ∑' xp, ∑' k, ρs xp
                * screenInd (SquareRel (fullSim (cRel Rv) h)) zs xp
                * (if ν k = 0 then 0 else
                    compFloor exc μ ν v0 k ^ (-α)
                      * WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
                          (SquareRel (fullSim (cRel Rv) h)) xp) :=
              tsum_congr fun xp => ENNReal.tsum_mul_left.symm
          _ = _ := ENNReal.tsum_comm
    _ = ∑' k, (if ν k = 0 then 0 else
          compFloor exc μ ν v0 k ^ (-α)
            * screenE ρs (SquareRel (fullSim (cRel Rv) h)) zs
                (WresD α (cXi exc μ ν v0 (CtrC.ord k) h)
                  (SquareRel (fullSim (cRel Rv) h)))) := by
        refine tsum_congr fun k => ?_
        by_cases hνk : ν k = 0
        · rw [if_pos hνk]
          exact ENNReal.tsum_eq_zero.mpr fun xp => by
            rw [if_pos hνk, mul_zero]
        · rw [if_neg hνk, screenE, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun xp => by rw [if_neg hνk]; ring

end PricedMixture

/-! ### Pruning in ledger form (`thm:support-equality`,
`thm:exact-pruning`) -/

section Pruning

/-- The mirror of a tagged counter: common counters map to themselves, an
exceptional counter to the head of its declared pair, and a marker at
stage `i` to the plain running value.  This is the counter part of
`mirrorC`. -/
def mirrorCtr (exc1 : ℕ → Option (ℕ × ℕ)) : CtrC → CtrC
  | CtrC.ord k =>
      match exc1 k with
      | some p => CtrC.ord p.1
      | none => CtrC.ord k
  | CtrC.mark a _ i => CtrC.ord (val a i)

lemma mirrorCtr_ord_none {exc1 : ℕ → Option (ℕ × ℕ)} {k : ℕ}
    (hk : exc1 k = none) : mirrorCtr exc1 (CtrC.ord k) = CtrC.ord k := by
  simp [mirrorCtr, hk]

lemma mirrorCtr_ord_some {exc1 : ℕ → Option (ℕ × ℕ)} {k : ℕ} {p : ℕ × ℕ}
    (hk : exc1 k = some p) :
    mirrorCtr exc1 (CtrC.ord k) = CtrC.ord p.1 := by
  simp [mirrorCtr, hk]

lemma mirrorCtr_mark (exc1 : ℕ → Option (ℕ × ℕ)) (a b i : ℕ) :
    mirrorCtr exc1 (CtrC.mark a b i) = CtrC.ord (val a i) := rfl

lemma mirrorC_eq_mirrorCtr (exc1 : ℕ → Option (ℕ × ℕ)) (v : V)
    (c : CtrC) : mirrorC exc1 (v, c) = (v, mirrorCtr exc1 c) := by
  cases c with
  | ord k =>
      rcases hk : exc1 k with _ | p
      · rw [mirrorC_ord_none hk, mirrorCtr_ord_none hk]
      · rw [mirrorC_ord_some hk, mirrorCtr_ord_some hk]
  | mark a b i => rfl

variable (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (N : ℕ)

/-- **The support witness in ledger form** (`thm:support-equality`):
every safe frozen law of the left side has matching support in the frozen
law of the mirrored counter on the right side. -/
theorem cZ_hasMatchingSupport
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (c : CtrC) (hsafe : Safe exc1 ν2 N ((v0 : V), c)) (h : ℕ) :
    HasMatchingSupport (cZ exc1 μ ν1 v0 c h)
      (cZ exc2 μ ν2 v0 (mirrorCtr exc1 c) h) (fullSim (cRel Rv) h) := by
  intro x hx
  obtain ⟨y, hy, hsim⟩ := exists_sim_of_muM_ne_zero Rv μ v0 exc1 exc2 ν1 ν2 N
    hRv hμ0 hN hpair hcharged h (v0, c) hsafe x hx
  rw [mirrorC_eq_mirrorCtr] at hy
  exact ⟨y, hy, hsim⟩

/-- A common letter pair supports itself across the two sides. -/
theorem cZ_hasMatchingSupport_common
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    {k : ℕ} (hk : k ≤ N) (h : ℕ) :
    HasMatchingSupport (cZ exc1 μ ν1 v0 (CtrC.ord k) h)
      (cZ exc2 μ ν2 v0 (CtrC.ord k) h) (fullSim (cRel Rv) h) := by
  have hmain := cZ_hasMatchingSupport Rv μ v0 exc1 exc2 ν1 ν2 N
    hRv hμ0 hN hpair hcharged (CtrC.ord k) (Or.inl hk) h
  rwa [mirrorCtr_ord_none (hN k hk).1] at hmain

/-- An exceptional letter is supported by the head of its declared
pair. -/
theorem cZ_hasMatchingSupport_exc
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    {z : ℕ} {p : ℕ × ℕ} (hz : exc1 z = some p) (h : ℕ) :
    HasMatchingSupport (cZ exc1 μ ν1 v0 (CtrC.ord z) h)
      (cZ exc2 μ ν2 v0 (CtrC.ord p.1) h) (fullSim (cRel Rv) h) := by
  have hmain := cZ_hasMatchingSupport Rv μ v0 exc1 exc2 ν1 ν2 N
    hRv hμ0 hN hpair hcharged (CtrC.ord z) (Or.inr ⟨p, hz⟩) h
  rwa [mirrorCtr_ord_some hz] at hmain

/-- A marker letter is supported by the plain running value. -/
theorem cZ_hasMatchingSupport_mark
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hb2 : ν2 b ≠ 0) (i h : ℕ) :
    HasMatchingSupport (cZ exc1 μ ν1 v0 (CtrC.mark a b i) h)
      (cZ exc2 μ ν2 v0 (CtrC.ord (val a i)) h) (fullSim (cRel Rv) h) := by
  have hmain := cZ_hasMatchingSupport Rv μ v0 exc1 exc2 ν1 ν2 N
    hRv hμ0 hN hpair hcharged (CtrC.mark a b i) ⟨ha, hb, hb2⟩ h
  rwa [mirrorCtr_mark] at hmain

/-- **Exact pruning in ledger form** (`thm:exact-pruning`): a screen on
the left fresh law whose dead set contains the opposite fresh law is
exactly zero, for any normalization. -/
theorem screenE_cT_opposite_eq_zero
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (h : ℕ) (zs : List (PMF (FullLab (CState V) h)))
    (hmem : cT exc2 μ ν2 v0 h ∈ zs)
    (W : FullLab (CState V) h → ℝ≥0∞) :
    screenE (cT exc1 μ ν1 v0 h) (fullSim (cRel Rv) h) zs W = 0 :=
  screenE_eq_zero_of_matching_mem
    (cT_hasMatchingSupport Rv μ v0 exc1 exc2 ν1 ν2 N
      hRv hμ0 hN hpair hcharged h) zs hmem W

/-- The zero-interface mass between the two fresh laws vanishes. -/
theorem zMass_cT_cT_eq_zero
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (h : ℕ) :
    zMass (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
      (fullSim (cRel Rv) h) = 0 :=
  (cT_hasMatchingSupport Rv μ v0 exc1 exc2 ν1 ν2 N
    hRv hμ0 hN hpair hcharged h).zMass_eq_zero

/-- On the fresh pair the restricted potential is the full one. -/
theorem PhiDres_cT_cT_eq_PhiD
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (α : ℝ) (h : ℕ) :
    PhiDres α (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
        (fullSim (cRel Rv) h)
      = PhiD α (cT exc1 μ ν1 v0 h) (cT exc2 μ ν2 v0 h)
          (fullSim (cRel Rv) h) :=
  (cT_hasMatchingSupport Rv μ v0 exc1 exc2 ν1 ν2 N
    hRv hμ0 hN hpair hcharged h).PhiDres_eq_PhiD α

/-- The zero-interface mass of a safe frozen law against its mirrored
component vanishes. -/
theorem zMass_cZ_mirror_eq_zero
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (c : CtrC) (hsafe : Safe exc1 ν2 N ((v0 : V), c)) (h : ℕ) :
    zMass (cZ exc1 μ ν1 v0 c h)
      (cZ exc2 μ ν2 v0 (mirrorCtr exc1 c) h) (fullSim (cRel Rv) h) = 0 :=
  (cZ_hasMatchingSupport Rv μ v0 exc1 exc2 ν1 ν2 N
    hRv hμ0 hN hpair hcharged c hsafe h).zMass_eq_zero

/-- Against the mirrored component the restricted potential of a safe
frozen law is the full one. -/
theorem PhiDres_cZ_mirror_eq_PhiD
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (α : ℝ) (c : CtrC) (hsafe : Safe exc1 ν2 N ((v0 : V), c)) (h : ℕ) :
    PhiDres α (cZ exc1 μ ν1 v0 c h)
        (cZ exc2 μ ν2 v0 (mirrorCtr exc1 c) h) (fullSim (cRel Rv) h)
      = PhiD α (cZ exc1 μ ν1 v0 c h)
          (cZ exc2 μ ν2 v0 (mirrorCtr exc1 c) h) (fullSim (cRel Rv) h) :=
  (cZ_hasMatchingSupport Rv μ v0 exc1 exc2 ν1 ν2 N
    hRv hμ0 hN hpair hcharged c hsafe h).PhiDres_eq_PhiD α

/-- A screen on a safe frozen law whose dead set contains the mirrored
component is exactly zero, for any normalization. -/
theorem screenE_cZ_mirror_mem_eq_zero
    (hRv : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    (hN : ∀ j, j ≤ N → exc1 j = none ∧ exc2 j = none)
    (hpair : ∀ k p, exc1 k = some p →
      p.1 ≤ N ∧ p.2 ≤ N ∧ ν2 p.1 ≠ 0 ∧ ν2 p.2 ≠ 0)
    (hcharged : ∀ k, ν1 k ≠ 0 → exc1 k = none → k ≤ N ∧ ν2 k ≠ 0)
    (c : CtrC) (hsafe : Safe exc1 ν2 N ((v0 : V), c)) (h : ℕ)
    (zs : List (PMF (FullLab (CState V) h)))
    (hmem : cZ exc2 μ ν2 v0 (mirrorCtr exc1 c) h ∈ zs)
    (W : FullLab (CState V) h → ℝ≥0∞) :
    screenE (cZ exc1 μ ν1 v0 c h) (fullSim (cRel Rv) h) zs W = 0 :=
  screenE_eq_zero_of_matching_mem
    (cZ_hasMatchingSupport Rv μ v0 exc1 exc2 ν1 ν2 N
      hRv hμ0 hN hpair hcharged c hsafe h) zs hmem W

end Pruning

end Composite
end GraphMarkovMatching

