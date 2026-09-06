/-
The bridge between the composite lemmas and the ledger functionals
(`arbitrary_offspring_matching.tex`, `sec:composite`).

The composite modules state their results in local functionals (`simDeg`,
`invTilt`, tsum-form dead sums); the row assembly runs in the established
functionals of the one-law stack (`rE`, `qE`, `PhiD`, `PhiDres`, `WresD`,
`screenE`, `zMass`, `failureD`).  This file is the dictionary.

* `simDeg_eq_rE`: the degree bridge; the local compatible mass is
  literally the established good degree;
* `rE_comp_map`, `rE_congr_map`, `rE_pair_congr_stateMap`: the projection
  identities; against the matching relation the good degree of a tagged
  law is the good degree of its state marginal at the projected point, so
  a pair target can be replaced by any law with the same
  `stateMap`-pushforward;
* `compFloor`, `mul_compFloor_rE_cXi_le`, `WresD_cXiBar_le_sum`,
  `tsum_WresD_cXiBar_le_sum`, `screenE_WresD_cXiBar_le_sum`
  (`thm:mixture-tilt-composite` in ledger form): the weighted
  fresh-target mixture bound; the restricted inverse degree of the fresh
  cell mixture is below the charged sum of component inverse degrees, each
  weighted by the inverse power of a common quantity: `ν k` for a common
  arity and the composite floor `ν p₁ · (μ v₀ · ν p₂)` for a declared
  exceptional arity, pointwise, integrated against an arbitrary source
  law, and inside an arbitrary screen;
* `screenE_cT_opposite_eq_zero` (`thm:support-equality`,
  `thm:exact-pruning` in ledger form): a screen on one fresh law whose
  dead set contains the opposite fresh law vanishes, by the support
  witness of `Support`.
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

/-! ### Generic projection layer

A relation that transports along a projection `f` sees laws only through
their `f`-pushforward, on the target side pointwise and on the source
side after the change of variables `tsum_map_mul`. -/

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

private lemma rE_congr_map {ρ ρ' : PMF X} (heq : ρ.map f = ρ'.map f)
    (x : X) : rE ρ RX x = rE ρ' RX x := by
  rw [rE_comp_map f hiff ρ x, rE_comp_map f hiff ρ' x, heq]

end GenericProjection

/-! ### State-marginal invariance, child-pair laws -/

section PairLaws

variable (Rv : V → V → Prop) (h : ℕ)

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

end PairLaws

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
component is the marked cell `cXi (CtrC.ord k)`.  No bare inverse
exceptional mass forms. -/
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

variable (Rv : V → V → Prop) (μ : PMF V) (v0 : V)
variable (exc1 exc2 : ℕ → Option (ℕ × ℕ)) (ν1 ν2 : PMF ℕ) (N : ℕ)

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

end Pruning

end Composite
end GraphMarkovMatching

