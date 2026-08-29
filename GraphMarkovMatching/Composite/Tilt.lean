/-
The weighted mixture tilt (`arbitrary_offspring_matching.tex`,
`sec:composite`, `thm:mixture-tilt-composite`): the inverse `α`-power
tilt of the fresh cell mixture `cXiBar` is weighted by inverse common
quantities only, never by a bare exceptional mass.

* `stateMap`, `fullSim_cRel_iff`, `squareRel_cRel_iff`: the graph-state
  projection of a tagged labelling, and state-blindness of the matching
  relation: labels compare through their states only, so matching
  transports along the projection, singly and on child pairs;
* `stateMap_cZ_mark`, `stateMap_cXi_exc`: the state-marginal equality of
  the marked and the replacement laws; the marker step at running value
  `v` and the successor step of the replacement subtree at `v` have
  literally mirrored case structure, so the state projections of the
  frozen marker subtree and of the replacement subtree agree exactly, at
  every height and unconditionally in the side data;
* `simDeg_eq_of_stateMap_eq`, `simDeg_pair_eq_of_stateMap_eq`: degrees
  against the matching relation only see state marginals;
* `invTilt`, `invTilt_le_of_mul_le`: the inverse `α`-power tilt in the
  safe convention, and its pointwise pricing under a component floor
  (the `c ≠ ⊤` side condition is not needed and not assumed);
* `simDeg_le_one`, `pmf_apply_ne_top`, `simDeg_bind`,
  `exists_component_of_simDeg_cXiBar_ne_zero`: degree bounds and the
  mixture covering: a charged mixture degree has a charged component;
* `invTilt_simDeg_cXiBar_le` (`thm:mixture-tilt-composite`): at every
  point charged by the fresh cell mixture, the tilt of the mixture degree
  is weighted through a charged common cell at `ν(k)^{-α}`, or through a
  charged exceptional cell at the inverse composite floor
  `(ν(p₁)·(μ(v₀)·ν(p₂)))^{-α}`; the floor is a common quantity, kept
  nonzero by the declared-pair hypotheses, so no bare inverse
  exceptional mass ever forms.
-/
import GraphMarkovMatching.Composite.Support
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace GraphMarkovMatching
namespace Composite

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type}

/-! ### The state projection and state-blindness of matching -/

/-- The graph-state projection of a tagged labelling: every vertex keeps
its graph state and forgets its tagged counter. -/
def stateMap : (h : ℕ) → FullLab (CState V) h → FullLab V h
  | 0, x => leaf x.1
  | h + 1, x => branch x.1.1 (stateMap h x.2.1, stateMap h x.2.2)

lemma stateMap_leaf (s : CState V) : stateMap 0 (leaf s) = leaf s.1 := rfl

lemma stateMap_branch (h : ℕ) (s : CState V)
    (p : FullLab (CState V) h × FullLab (CState V) h) :
    stateMap (h + 1) (branch s p)
      = branch s.1 (stateMap h p.1, stateMap h p.2) := rfl

/-- **State-blindness of the matching relation**: labels compare through
their graph states only, so two tagged labellings match exactly when
their state projections match. -/
lemma fullSim_cRel_iff (Rv : V → V → Prop) :
    ∀ (h : ℕ) (x y : FullLab (CState V) h),
      fullSim (cRel Rv) h x y
        ↔ fullSim Rv h (stateMap h x) (stateMap h y) := by
  intro h
  induction h with
  | zero =>
      intro x y
      constructor
      · intro hxy
        exact (fullSim_leaf Rv x.1 y.1).mpr
          ((fullSim_leaf (cRel Rv) x y).mp hxy)
      · intro hxy
        exact (fullSim_leaf (cRel Rv) x y).mpr
          ((fullSim_leaf Rv x.1 y.1).mp hxy)
  | succ h ih =>
      intro x y
      constructor
      · intro hxy
        have h1 := (fullSim_branch (cRel Rv) h x.1 y.1
          (x.2.1, x.2.2) (y.2.1, y.2.2)).mp hxy
        refine (fullSim_branch Rv h x.1.1 y.1.1
          (stateMap h x.2.1, stateMap h x.2.2)
          (stateMap h y.2.1, stateMap h y.2.2)).mpr ⟨h1.1, ?_⟩
        rcases h1.2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inl ⟨(ih x.2.1 y.2.1).mp ha, (ih x.2.2 y.2.2).mp hb⟩
        · exact Or.inr ⟨(ih x.2.1 y.2.2).mp ha, (ih x.2.2 y.2.1).mp hb⟩
      · intro hxy
        have h1 := (fullSim_branch Rv h x.1.1 y.1.1
          (stateMap h x.2.1, stateMap h x.2.2)
          (stateMap h y.2.1, stateMap h y.2.2)).mp hxy
        refine (fullSim_branch (cRel Rv) h x.1 y.1
          (x.2.1, x.2.2) (y.2.1, y.2.2)).mpr ⟨h1.1, ?_⟩
        rcases h1.2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inl ⟨(ih x.2.1 y.2.1).mpr ha, (ih x.2.2 y.2.2).mpr hb⟩
        · exact Or.inr ⟨(ih x.2.1 y.2.2).mpr ha, (ih x.2.2 y.2.1).mpr hb⟩

/-- The pair form of state-blindness, for the symmetrised square of the
matching relation on child pairs. -/
lemma squareRel_cRel_iff (Rv : V → V → Prop) (h : ℕ)
    (x y : FullLab (CState V) h × FullLab (CState V) h) :
    SquareRel (fullSim (cRel Rv) h) x y
      ↔ SquareRel (fullSim Rv h)
          (Prod.map (stateMap h) (stateMap h) x)
          (Prod.map (stateMap h) (stateMap h) y) := by
  constructor
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact Or.inl ⟨(fullSim_cRel_iff Rv h x.1 y.1).mp ha,
        (fullSim_cRel_iff Rv h x.2 y.2).mp hb⟩
    · exact Or.inr ⟨(fullSim_cRel_iff Rv h x.1 y.2).mp ha,
        (fullSim_cRel_iff Rv h x.2 y.1).mp hb⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact Or.inl ⟨(fullSim_cRel_iff Rv h x.1 y.1).mpr ha,
        (fullSim_cRel_iff Rv h x.2 y.2).mpr hb⟩
    · exact Or.inr ⟨(fullSim_cRel_iff Rv h x.1 y.2).mpr ha,
        (fullSim_cRel_iff Rv h x.2 y.1).mpr hb⟩

/-! ### Pushforward algebra -/

/-- Attaching a root and projecting the states equals projecting the
subtree states and attaching the root state. -/
private lemma map_branch_stateMap {h : ℕ} (u : V) (c : CtrC)
    (ρ : PMF (FullLab (CState V) h × FullLab (CState V) h)) :
    (ρ.map (branch (u, c))).map (stateMap (h + 1)) =
      (ρ.map (Prod.map (stateMap h) (stateMap h))).map (branch u) := by
  have hfun : stateMap (h + 1) ∘ branch ((u, c) : CState V)
      = branch u ∘ Prod.map (stateMap h) (stateMap h) := by
    funext p
    rfl
  rw [PMF.map_comp, PMF.map_comp, hfun]

/-- Pushforward of a product PMF under a componentwise map. -/
private lemma prodPMF_map_prodMap {A B C D : Type} (p : PMF A) (q : PMF B)
    (f : A → C) (g : B → D) :
    (prodPMF p q).map (Prod.map f g) = prodPMF (p.map f) (q.map g) := by
  apply PMF.ext
  intro z
  rw [PMF.map_apply, prodPMF_apply, PMF.map_apply, PMF.map_apply,
    show ((∑' a, if z.1 = f a then p a else 0)
          * ∑' b, if z.2 = g b then q b else 0)
        = ∑' ab : A × B, (if z.1 = f ab.1 then p ab.1 else 0)
            * (if z.2 = g ab.2 then q ab.2 else 0) from
      (tsum_prod_split (fun a => if z.1 = f a then p a else 0)
        (fun b => if z.2 = g b then q b else 0)).symm]
  refine tsum_congr fun ab => ?_
  by_cases h1 : z.1 = f ab.1 <;> by_cases h2 : z.2 = g ab.2
  · rw [if_pos (show z = Prod.map f g ab from Prod.ext h1 h2), if_pos h1,
      if_pos h2, prodPMF_apply]
  · rw [if_neg (show ¬ z = Prod.map f g ab from
        fun hc => h2 (congrArg Prod.snd hc)), if_pos h1, if_neg h2,
      mul_zero]
  · rw [if_neg (show ¬ z = Prod.map f g ab from
        fun hc => h1 (congrArg Prod.fst hc)), if_neg h1, zero_mul]
  · rw [if_neg (show ¬ z = Prod.map f g ab from
        fun hc => h1 (congrArg Prod.fst hc)), if_neg h1, zero_mul]

/-! ### The state-marginal equality of the marked and replacement laws -/

variable (exc : ℕ → Option (ℕ × ℕ)) (μ : PMF V) (ν : PMF ℕ) (v0 : V)

/-- **The state-marginal equality at subtree level**: the frozen subtree
below a marker of the pair `(a, b)` at stage `i` and the replacement
subtree at the running value `val a i` project to the same state law, at
every height.  The marker step and the replacement step have literally
mirrored case structure, so no hypothesis on the side data is needed. -/
theorem stateMap_cZ_mark (a b : ℕ) :
    ∀ (h i : ℕ),
      (cZ exc μ ν v0 (CtrC.mark a b i) h).map (stateMap h) =
        (repZ exc μ ν v0 b (val a i) h).map (stateMap h) := by
  intro h
  induction h with
  | zero =>
      intro i
      rw [show cZ exc μ ν v0 (CtrC.mark a b i) 0
            = PMF.pure (leaf (v0, CtrC.mark a b i)) from rfl,
        show repZ exc μ ν v0 b (val a i) 0
            = PMF.pure (leaf (v0, CtrC.ord (val a i))) from rfl,
        PMF.pure_map, PMF.pure_map]
      rfl
  | succ h ih =>
      intro i
      rcases Nat.lt_or_ge (val a i) 3 with h2 | h3
      · -- running value at most two: port left, fresh right on both sides
        rw [cZ_succ, cXi_mark_le_two exc μ ν v0 (by omega) h,
          show repZ exc μ ν v0 b (val a i) (h + 1) =
              (prodPMF (cZ exc μ ν v0 (CtrC.ord b) h) (cT exc μ ν v0 h)).map
                (branch (v0, CtrC.ord (val a i))) from by
            rw [repZ, if_neg (by omega), if_neg (by omega)],
          map_branch_stateMap, map_branch_stateMap]
      · rcases Nat.lt_or_ge (val a i) 4 with h4 | h4
        · -- running value three: forced left, port right on both sides
          have hv3 : val a i = 3 := by omega
          rw [cZ_succ, cXi_mark_three exc μ ν v0 hv3 h,
            show repZ exc μ ν v0 b (val a i) (h + 1) =
                (prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h)
                  (cZ exc μ ν v0 (CtrC.ord b) h)).map
                  (branch (v0, CtrC.ord (val a i))) from by
              rw [repZ, if_neg (by omega), if_pos hv3],
            map_branch_stateMap, map_branch_stateMap]
        · -- running value at least four: recurse along the designated path
          rw [cZ_succ, cXi_mark_of_ge exc μ ν v0 h4 h,
            show repZ exc μ ν v0 b (val a i) (h + 1) =
                (prodPMF (repZ exc μ ν v0 b (val a i / 2) h)
                  (cZ exc μ ν v0 (CtrC.ord (val a i - val a i / 2)) h)).map
                  (branch (v0, CtrC.ord (val a i))) from by
              rw [repZ, if_pos h4],
            map_branch_stateMap, map_branch_stateMap,
            prodPMF_map_prodMap, prodPMF_map_prodMap]
          have hih := ih (i + 1)
          rw [val_succ] at hih
          rw [hih]

/-- **The state-marginal equality at cell level**: the cell of an
exceptional counter and the replacement cell of its declared pair project
to the same state law on child pairs. -/
theorem stateMap_cXi_exc {z : ℕ} {p : ℕ × ℕ} (hz : exc z = some p)
    (h : ℕ) :
    (cXi exc μ ν v0 (CtrC.ord z) h).map
        (Prod.map (stateMap h) (stateMap h)) =
      (repXi exc μ ν v0 p.1 p.2 h).map
        (Prod.map (stateMap h) (stateMap h)) := by
  rw [cXi_ord_exc exc μ ν v0 hz h]
  rcases Nat.lt_or_ge p.1 3 with h2 | h3
  · have hval : val p.1 0 ≤ 2 := by rw [val_zero]; omega
    rw [cXi_mark_le_two exc μ ν v0 hval h,
      show repXi exc μ ν v0 p.1 p.2 h =
          prodPMF (cZ exc μ ν v0 (CtrC.ord p.2) h) (cT exc μ ν v0 h) from by
        rw [repXi, if_neg (by omega), if_neg (by omega)]]
  · rcases Nat.lt_or_ge p.1 4 with h4 | h4
    · have hp3 : p.1 = 3 := by omega
      have hval : val p.1 0 = 3 := by rw [val_zero]; omega
      rw [cXi_mark_three exc μ ν v0 hval h,
        show repXi exc μ ν v0 p.1 p.2 h =
            prodPMF (cZ exc μ ν v0 (CtrC.ord 2) h)
              (cZ exc μ ν v0 (CtrC.ord p.2) h) from by
          rw [repXi, if_neg (by omega), if_pos hp3]]
    · have hval : 4 ≤ val p.1 0 := by rw [val_zero]; omega
      rw [cXi_mark_of_ge exc μ ν v0 hval h,
        show repXi exc μ ν v0 p.1 p.2 h =
            prodPMF (repZ exc μ ν v0 p.2 (p.1 / 2) h)
              (cZ exc μ ν v0 (CtrC.ord (p.1 - p.1 / 2)) h) from by
          rw [repXi, if_pos h4],
        prodPMF_map_prodMap, prodPMF_map_prodMap]
      have hih := stateMap_cZ_mark exc μ ν v0 p.1 p.2 h (0 + 1)
      rw [val_succ, val_zero] at hih
      rw [val_zero, hih]

/-! ### Degrees only see states -/

/-- Change of variables for an indicator sum against a pushforward: the
mass of a fibered condition is the pushforward mass of the condition. -/
private lemma tsum_ite_comp {A B : Type} (ρ : PMF A) (f : A → B)
    (Q : B → Prop) :
    (∑' a, if Q (f a) then ρ a else 0)
      = ∑' b, if Q b then (ρ.map f) b else 0 := by
  symm
  calc (∑' b, if Q b then (ρ.map f) b else 0)
      = ∑' b, ∑' a, (if Q b then (if b = f a then ρ a else 0) else 0) := by
        refine tsum_congr fun b => ?_
        by_cases hb : Q b
        · rw [if_pos hb, PMF.map_apply]
          exact tsum_congr fun a => (if_pos hb).symm
        · rw [if_neg hb]
          exact (ENNReal.tsum_eq_zero.mpr fun a => if_neg hb).symm
    _ = ∑' a, ∑' b, (if Q b then (if b = f a then ρ a else 0) else 0) :=
        ENNReal.tsum_comm
    _ = ∑' a, (if Q (f a) then ρ a else 0) := by
        refine tsum_congr fun a => ?_
        rw [show (fun b => if Q b then (if b = f a then ρ a else 0) else 0)
            = fun b => if b = f a then (if Q b then ρ a else 0) else 0 from
          funext fun b => by
            by_cases hb : Q b <;> by_cases hba : b = f a <;>
              simp [hb, hba]]
        exact tsum_ite_eq (f a) fun b => if Q b then ρ a else 0

/-- Degrees against a relation that transports along a projection only
see the projected law. -/
private lemma simDeg_congr_of_map_eq {X Y : Type} {ρ ρ' : PMF X}
    (f : X → Y) {RelX : X → X → Prop} {RelY : Y → Y → Prop}
    (hiff : ∀ x y, RelX x y ↔ RelY (f x) (f y))
    (heq : ρ.map f = ρ'.map f) (x : X) :
    simDeg ρ RelX x = simDeg ρ' RelX x := by
  have hrw : ∀ τ : PMF X,
      simDeg τ RelX x = ∑' w, if RelY (f x) w then (τ.map f) w else 0 := by
    intro τ
    rw [simDeg,
      show (fun y => if RelX x y then τ y else 0)
          = fun y => if RelY (f x) (f y) then τ y else 0 from
        funext fun y => by
          by_cases hy : RelX x y
          · rw [if_pos hy, if_pos ((hiff x y).mp hy)]
          · rw [if_neg hy, if_neg fun hc => hy ((hiff x y).mpr hc)]]
    exact tsum_ite_comp τ f (RelY (f x))
  rw [hrw ρ, hrw ρ', heq]

/-- **Degrees only see states**: two tagged laws with the same state
marginal have the same degree against the matching relation. -/
lemma simDeg_eq_of_stateMap_eq (Rv : V → V → Prop) (h : ℕ)
    {ρ ρ' : PMF (FullLab (CState V) h)}
    (heq : ρ.map (stateMap h) = ρ'.map (stateMap h))
    (x : FullLab (CState V) h) :
    simDeg ρ (fullSim (cRel Rv) h) x = simDeg ρ' (fullSim (cRel Rv) h) x :=
  simDeg_congr_of_map_eq (stateMap h) (fullSim_cRel_iff Rv h) heq x

/-- The pair form: two child-pair laws with the same componentwise state
marginal have the same degree against the squared matching relation. -/
lemma simDeg_pair_eq_of_stateMap_eq (Rv : V → V → Prop) (h : ℕ)
    {ρ ρ' : PMF (FullLab (CState V) h × FullLab (CState V) h)}
    (heq : ρ.map (Prod.map (stateMap h) (stateMap h))
      = ρ'.map (Prod.map (stateMap h) (stateMap h)))
    (x : FullLab (CState V) h × FullLab (CState V) h) :
    simDeg ρ (SquareRel (fullSim (cRel Rv) h)) x
      = simDeg ρ' (SquareRel (fullSim (cRel Rv) h)) x :=
  simDeg_congr_of_map_eq (Prod.map (stateMap h) (stateMap h))
    (squareRel_cRel_iff Rv h) heq x

/-! ### The inverse power tilt -/

/-- The inverse `α`-power tilt in the safe convention: zero degree is
tilted to zero, positive degree to its inverse `α`-power. -/
noncomputable def invTilt (α : ℝ) (t : ℝ≥0∞) : ℝ≥0∞ :=
  if t = 0 then 0 else t ^ (-α)

/-- **Pointwise pricing**: a component floor `c * t ≤ t'` prices the tilt
of `t'` by the inverse `α`-power of the floor coefficient. -/
lemma invTilt_le_of_mul_le {α : ℝ} (hα : 0 ≤ α) {c t t' : ℝ≥0∞}
    (hc0 : c ≠ 0) (ht : t ≠ 0) (hle : c * t ≤ t') :
    invTilt α t' ≤ c ^ (-α) * invTilt α t := by
  have ht'0 : t' ≠ 0 := fun h0 =>
    mul_ne_zero hc0 ht (le_antisymm (h0 ▸ hle) zero_le)
  rw [invTilt, if_neg ht'0, invTilt, if_neg ht]
  calc t' ^ (-α) ≤ (c * t) ^ (-α) := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
        exact ENNReal.inv_le_inv' (ENNReal.rpow_le_rpow hle hα)
    _ = c ^ (-α) * t ^ (-α) := ENNReal.mul_rpow_of_ne_zero hc0 ht (-α)

/-! ### Degree bounds and the mixture covering -/

/-- Degrees are at most one. -/
lemma simDeg_le_one {X : Type} (ρ : PMF X) (Rel : X → X → Prop) (x : X) :
    simDeg ρ Rel x ≤ 1 := by
  rw [simDeg]
  refine le_trans (ENNReal.tsum_le_tsum fun y => ?_) (le_of_eq ρ.tsum_coe)
  by_cases hy : Rel x y
  · exact le_of_eq (if_pos hy)
  · rw [if_neg hy]
    exact zero_le

/-- PMF values are finite. -/
lemma pmf_apply_ne_top {A : Type} (p : PMF A) (a : A) : p a ≠ ⊤ :=
  (lt_of_le_of_lt (pmf_apply_le_one p a) ENNReal.one_lt_top).ne

/-- The degree of a mixture is the mixture of degrees. -/
lemma simDeg_bind {A X : Type} (w : PMF A) (f : A → PMF X)
    (Rel : X → X → Prop) (x : X) :
    simDeg (w.bind f) Rel x = ∑' a, w a * simDeg (f a) Rel x := by
  rw [simDeg]
  calc (∑' y, if Rel x y then (w.bind f) y else 0)
      = ∑' y, ∑' a, (if Rel x y then w a * f a y else 0) := by
        refine tsum_congr fun y => ?_
        by_cases hy : Rel x y
        · rw [if_pos hy, PMF.bind_apply]
          exact tsum_congr fun a => (if_pos hy).symm
        · rw [if_neg hy]
          exact (ENNReal.tsum_eq_zero.mpr fun a => if_neg hy).symm
    _ = ∑' a, ∑' y, (if Rel x y then w a * f a y else 0) :=
        ENNReal.tsum_comm
    _ = ∑' a, w a * simDeg (f a) Rel x := by
        refine tsum_congr fun a => ?_
        rw [simDeg, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun y => ?_
        by_cases hy : Rel x y
        · rw [if_pos hy, if_pos hy]
        · rw [if_neg hy, if_neg hy, mul_zero]

/-- **Mixture covering**: a point charged by the fresh cell mixture is
charged by some charged cell of the mixture. -/
lemma exists_component_of_simDeg_cXiBar_ne_zero {h : ℕ}
    {Rel : (FullLab (CState V) h × FullLab (CState V) h) →
      (FullLab (CState V) h × FullLab (CState V) h) → Prop}
    {x : FullLab (CState V) h × FullLab (CState V) h}
    (hx : simDeg (cXiBar exc μ ν v0 h) Rel x ≠ 0) :
    ∃ k, ν k ≠ 0 ∧ simDeg (cXi exc μ ν v0 (CtrC.ord k) h) Rel x ≠ 0 := by
  have hx' : (∑' k, ν k * simDeg (cXi exc μ ν v0 (CtrC.ord k) h) Rel x)
      ≠ 0 := by
    rw [← simDeg_bind ν (fun k => cXi exc μ ν v0 (CtrC.ord k) h) Rel x]
    exact hx
  obtain ⟨k, hk⟩ := exists_ne_zero_of_tsum_ne_zero hx'
  exact ⟨k, (mul_ne_zero_iff.mp hk).1, (mul_ne_zero_iff.mp hk).2⟩

/-! ### The weighted mixture tilt -/

/-- **The weighted mixture tilt** (`thm:mixture-tilt-composite`): at
every point charged by the fresh cell mixture, the inverse `α`-power tilt
of the mixture degree is bounded through a charged component cell.
Either the component is common and the weight is the inverse power of its
common weight `ν(k)`, or it is exceptional and, through the state-marginal
equality with the replacement cell and the cluster floor, the weight is
the inverse power of the composite floor `ν(p₁)·(μ(v₀)·ν(p₂))`, a common
quantity.  A bare inverse exceptional mass never forms. -/
theorem invTilt_simDeg_cXiBar_le
    (hpair : ∀ k p, exc k = some p → ∀ j, j ≤ p.1 → exc j = none)
    (hdecl : ∀ k p, exc k = some p → ν p.1 ≠ 0 ∧ ν p.2 ≠ 0)
    (hμ0 : μ v0 ≠ 0) {α : ℝ} (hα : 0 ≤ α)
    (Rv : V → V → Prop) (h : ℕ)
    (x : FullLab (CState V) h × FullLab (CState V) h)
    (hx : simDeg (cXiBar exc μ ν v0 h)
      (SquareRel (fullSim (cRel Rv) h)) x ≠ 0) :
    (∃ k, ν k ≠ 0 ∧ exc k = none ∧
      simDeg (cXi exc μ ν v0 (CtrC.ord k) h)
        (SquareRel (fullSim (cRel Rv) h)) x ≠ 0 ∧
      invTilt α (simDeg (cXiBar exc μ ν v0 h)
          (SquareRel (fullSim (cRel Rv) h)) x)
        ≤ (ν k) ^ (-α) *
          invTilt α (simDeg (cXi exc μ ν v0 (CtrC.ord k) h)
            (SquareRel (fullSim (cRel Rv) h)) x)) ∨
    (∃ z p, ν z ≠ 0 ∧ exc z = some p ∧
      simDeg (cXi exc μ ν v0 (CtrC.ord z) h)
        (SquareRel (fullSim (cRel Rv) h)) x ≠ 0 ∧
      invTilt α (simDeg (cXiBar exc μ ν v0 h)
          (SquareRel (fullSim (cRel Rv) h)) x)
        ≤ (ν p.1 * (μ v0 * ν p.2)) ^ (-α) *
          invTilt α (simDeg (cXi exc μ ν v0 (CtrC.ord z) h)
            (SquareRel (fullSim (cRel Rv) h)) x)) := by
  obtain ⟨k, hνk, hk⟩ :=
    exists_component_of_simDeg_cXiBar_ne_zero exc μ ν v0 hx
  rcases hexc : exc k with _ | p
  · -- a common component: priced by its common weight
    refine Or.inl ⟨k, hνk, hexc, hk, ?_⟩
    refine invTilt_le_of_mul_le hα hνk hk ?_
    exact mul_simDeg_le_simDeg (ν k) _
      (fun y => cXi_le_cXiBar exc μ ν v0 k h y) x
  · -- an exceptional component: priced by the composite floor of its pair
    have hfloor : ∀ j, j ≤ p.1 → exc j = none := hpair k p hexc
    obtain ⟨hp1, hp2⟩ := hdecl k p hexc
    have hrep : simDeg (cXi exc μ ν v0 (CtrC.ord k) h)
        (SquareRel (fullSim (cRel Rv) h)) x
      = simDeg (repXi exc μ ν v0 p.1 p.2 h)
        (SquareRel (fullSim (cRel Rv) h)) x :=
      simDeg_pair_eq_of_stateMap_eq Rv h
        (stateMap_cXi_exc exc μ ν v0 hexc h) x
    have hmin : (ν p.1 * (μ v0 * ν p.2)) *
        simDeg (cXi exc μ ν v0 (CtrC.ord k) h)
          (SquareRel (fullSim (cRel Rv) h)) x
      ≤ simDeg (cXiBar exc μ ν v0 h)
          (SquareRel (fullSim (cRel Rv) h)) x := by
      rw [hrep]
      exact mul_simDeg_le_simDeg _ _
        (fun y => repXi_le_cXiBar exc μ ν v0 p.2 hfloor h y) x
    exact Or.inr ⟨k, p, hνk, hexc, hk,
      invTilt_le_of_mul_le hα
        (mul_ne_zero hp1 (mul_ne_zero hμ0 hp2)) hk hmin⟩

end Composite
end GraphMarkovMatching
