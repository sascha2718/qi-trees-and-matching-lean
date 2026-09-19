/-
The independent root of `arbitrary_offspring_matching.tex` (`sec:independent-root`): the
restricted potential at height `h+1` is at most `ζ + D_μ Q` whenever the child-pair
restricted potential is at most `Q`, using the root identity
`(1 - sr)/(sr)^α = (1-s)/s^α · r^{-α} + s^{1-α}(1-r)/r^α`, the inverse moment
`1 + α Q` of the child pair, and the independence of the source root state from its
children.  The height-zero potentials are at most `ζ`.
-/
import GraphMarkovMatching.Stopped.Moments
import GraphMarkovMatching.Stopped.Scalar

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

/-! ### Pointwise identities (`sec:independent-root`) -/

/-- The bad degree depends on the target law only through the good degree
(`sec:restricted-potential`): `q = 1 - r`. -/
private lemma q_eq_of_rE_eq {X Y : Type} {ρ : PMF X} {R : X → X → Prop} {x : X}
    {ρ' : PMF Y} {R' : Y → Y → Prop} {y : Y} (h : rE ρ R x = rE ρ' R' y) :
    q ρ R x = q ρ' R' y := by
  have h1 := toReal_rE_eq ρ R x
  have h2 := toReal_rE_eq ρ' R' y
  rw [h] at h1
  linarith

/-- The bad degree in terms of the good degree, `q = 1 - r` (`sec:restricted-potential`). -/
private lemma q_eq_one_sub {X : Type} (ρ : PMF X) (R : X → X → Prop) (x : X) :
    q ρ R x = 1 - (rE ρ R x).toReal := by
  have h := toReal_rE_eq ρ R x
  linarith

/-- **The root identity** in the safe form (`sec:independent-root`): for a root factor
`c ∈ (0,1]` and a child degree `r ∈ (0,1]`,
`φ_α(1 - cr) = φ_α(1 - c) r^{-α} + c^{1-α} φ_α(1 - r)`. -/
private lemma phiE_one_sub_mul {α : ℝ} {c r : ℝ≥0∞} (hc0 : c ≠ 0) (hc1 : c ≤ 1)
    (hr0 : r ≠ 0) (hr1 : r ≤ 1) :
    phiE α (1 - (c * r).toReal)
      = phiE α (1 - c.toReal) * r ^ (-α) + c ^ (1 - α) * phiE α (1 - r.toReal) := by
  have hcT : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc1
  have hrT : r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hr1
  have hcs : 0 < c.toReal := ENNReal.toReal_pos hc0 hcT
  have hrs : 0 < r.toReal := ENNReal.toReal_pos hr0 hrT
  have hcs1 : c.toReal ≤ 1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hc1
  have hrs1 : r.toReal ≤ 1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hr1
  have hprod : 0 < c.toReal * r.toReal := mul_pos hcs hrs
  have h1 : 1 - c.toReal * r.toReal < 1 := by linarith
  have h2 : 1 - c.toReal < 1 := by linarith
  have h3 : 1 - r.toReal < 1 := by linarith
  have hA : 0 ≤ (1 - c.toReal) / c.toReal ^ α :=
    div_nonneg (by linarith) (Real.rpow_nonneg hcs.le α)
  have hB : 0 ≤ (1 - r.toReal) / r.toReal ^ α :=
    div_nonneg (by linarith) (Real.rpow_nonneg hrs.le α)
  have hrn : 0 ≤ r.toReal ^ (-α) := Real.rpow_nonneg hrs.le _
  have hcn : 0 ≤ c.toReal ^ (1 - α) := Real.rpow_nonneg hcs.le _
  have hr' : r ^ (-α) = ENNReal.ofReal (r.toReal ^ (-α)) := by
    rw [← ENNReal.ofReal_rpow_of_pos hrs, ENNReal.ofReal_toReal hrT]
  have hc' : c ^ (1 - α) = ENNReal.ofReal (c.toReal ^ (1 - α)) := by
    rw [← ENNReal.ofReal_rpow_of_pos hcs, ENNReal.ofReal_toReal hcT]
  rw [ENNReal.toReal_mul, phiE_of_lt h1, phiE_of_lt h2, phiE_of_lt h3, hr', hc']
  simp only [phi, sub_sub_cancel]
  rw [root_split hcs hrs, ENNReal.ofReal_add (mul_nonneg hA hrn) (mul_nonneg hcn hB),
    ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hcn]

namespace Model

variable {V I : Type} (M : Model V I)

/-! ### The root potentials (`sec:independent-root`) -/

/-- The height-zero restricted potential is the restricted potential of the root laws. -/
lemma P_zero_eq (α : ℝ) (s t : I) :
    M.P α s t 0 = PhiDres α (M.rootLaw s) (M.rootLaw t) M.R := by
  rw [P]
  unfold PhiDres
  rw [M.rho_zero s, tsum_map_mul, rootT, tsum_map_mul]
  refine tsum_congr fun v => ?_
  have hd : rE (M.rho t 0) (M.sim 0) (leaf (s, v)) = rE (M.rootLaw t) M.R v :=
    M.deg_zero t (s, v)
  rw [hd, q_eq_of_rE_eq hd]

/-- Against a forced target the restricted root potential vanishes: on the positive set the
root factor is one (`sec:independent-root`). -/
lemma PhiDres_rootLaw_forced (α : ℝ) (s : I) {t : I} (ht : ¬ M.fresh t) :
    PhiDres α (M.rootLaw s) (M.rootLaw t) M.R = 0 := by
  rw [PhiDres, ENNReal.tsum_eq_zero]
  intro v
  rw [rootLaw_forced M ht, q_eq_one_sub, rE_pure]
  by_cases hv : M.R v M.zero
  · rw [if_pos hv, if_neg one_ne_zero, ENNReal.toReal_one, sub_self, phiE_zero, mul_zero]
  · rw [if_neg hv, if_pos rfl, mul_zero]

/-- Against a fresh target the restricted root potential is at most `η` for a fresh source
and `φ_α(δ)` for a forced source (`sec:independent-root`). -/
lemma PhiDres_rootLaw_fresh_le (α : ℝ) (s : I) {t : I} (ht : M.fresh t) :
    PhiDres α (M.rootLaw s) (M.rootLaw t) M.R ≤ if M.fresh s then M.eta α else M.e0 α := by
  have hle : PhiDres α (M.rootLaw s) (M.rootLaw t) M.R
      ≤ PhiD α (M.rootLaw s) (M.rootLaw t) M.R := by
    rw [PhiDres, PhiD]
    refine ENNReal.tsum_le_tsum fun v => mul_le_mul_right ?_ _
    split_ifs
    · exact zero_le
    · exact le_rfl
  refine hle.trans ?_
  rw [rootLaw_fresh M ht]
  by_cases hs : M.fresh s
  · rw [if_pos hs, rootLaw_fresh M hs, eta]
  · rw [if_neg hs, rootLaw_forced M hs, PhiD, tsum_pure_mul, e0]

/-- The restricted root potential is at most `ζ_α` (`sec:independent-root`). -/
lemma PhiDres_rootLaw_le (α : ℝ) (s t : I) :
    PhiDres α (M.rootLaw s) (M.rootLaw t) M.R ≤ M.zeta α := by
  by_cases ht : M.fresh t
  · refine (M.PhiDres_rootLaw_fresh_le α s ht).trans ?_
    split_ifs
    · exact M.eta_le_zeta α
    · exact M.e0_le_zeta α
  · rw [M.PhiDres_rootLaw_forced α s ht]
    exact zero_le

set_option linter.unusedVariables false in
/-- **The height-zero potentials** are at most `ζ_α`: `η` for a fresh pair, `φ_α(δ)` for a
forced source against a fresh target, and zero against a forced target.  The standing
hypotheses of `sec:quantitative-stopping` (compatibility, `α ≥ 1`) are carried for a uniform
interface; the height-zero bound holds without them. -/
theorem P_zero_le (hc : M.IsCompat) {α : ℝ} (hα : 1 ≤ α) (s t : I) :
    M.P α s t 0 ≤ M.zeta α := by
  rw [M.P_zero_eq α s t]
  exact M.PhiDres_rootLaw_le α s t

/-! ### The root step (`sec:independent-root`) -/

/-- **The root averages**: the restricted root potential times the inverse moment factor
`1 + α Qb`, plus the restricted `(1-α)`-moment of the root factor times `Qb`, is at most
`ζ_α + D_μ Qb` in each of the three cases (fresh-fresh, forced-fresh, forced target). -/
private lemma root_average_le {α : ℝ} (s t : I) (Qb : ℝ≥0∞) :
    PhiDres α (M.rootLaw s) (M.rootLaw t) M.R * (1 + ENNReal.ofReal α * Qb)
      + (∑' v, M.rootLaw s v * (if rE (M.rootLaw t) M.R v = 0 then 0
          else (rE (M.rootLaw t) M.R v) ^ (1 - α))) * Qb
      ≤ M.zeta α + M.DmuC α * Qb := by
  by_cases ht : M.fresh t
  · have hA := M.PhiDres_rootLaw_fresh_le α s ht
    rw [rootLaw_fresh M ht] at hA ⊢
    by_cases hs : M.fresh s
    · rw [if_pos hs] at hA
      rw [rootLaw_fresh M hs] at hA ⊢
      have hS : (∑' v, M.μ v * (if rE M.μ M.R v = 0 then 0 else (rE M.μ M.R v) ^ (1 - α)))
          ≤ ∑' v, M.μ v * (rE M.μ M.R v) ^ (1 - α) := by
        refine ENNReal.tsum_le_tsum fun v => mul_le_mul_right ?_ _
        split_ifs
        · exact zero_le
        · exact le_rfl
      refine le_trans (add_le_add (mul_le_mul_left hA _) (mul_le_mul_left hS _)) ?_
      calc M.eta α * (1 + ENNReal.ofReal α * Qb)
            + (∑' v, M.μ v * (rE M.μ M.R v) ^ (1 - α)) * Qb
          = M.eta α
            + (ENNReal.ofReal α * M.eta α + ∑' v, M.μ v * (rE M.μ M.R v) ^ (1 - α)) * Qb := by
            ring
        _ ≤ M.zeta α + M.DmuC α * Qb :=
            add_le_add (M.eta_le_zeta α)
              (mul_le_mul_left ((le_max_left _ _).trans (le_max_right _ _)) _)
    · rw [if_neg hs] at hA
      rw [rootLaw_forced M hs] at hA ⊢
      rw [tsum_pure_mul]
      have hS : (if rE M.μ M.R M.zero = 0 then (0 : ℝ≥0∞) else (rE M.μ M.R M.zero) ^ (1 - α))
          ≤ (rE M.μ M.R M.zero) ^ (1 - α) := by
        split_ifs
        · exact zero_le
        · exact le_rfl
      refine le_trans (add_le_add (mul_le_mul_left hA _) (mul_le_mul_left hS _)) ?_
      calc M.e0 α * (1 + ENNReal.ofReal α * Qb) + (rE M.μ M.R M.zero) ^ (1 - α) * Qb
          = M.e0 α + (ENNReal.ofReal α * M.e0 α + (rE M.μ M.R M.zero) ^ (1 - α)) * Qb := by
            ring
        _ ≤ M.zeta α + M.DmuC α * Qb :=
            add_le_add (M.e0_le_zeta α)
              (mul_le_mul_left ((le_max_right _ _).trans (le_max_right _ _)) _)
  · rw [M.PhiDres_rootLaw_forced α s ht, zero_mul, zero_add]
    have hS : (∑' v, M.rootLaw s v * (if rE (M.rootLaw t) M.R v = 0 then 0
        else (rE (M.rootLaw t) M.R v) ^ (1 - α))) ≤ 1 := by
      calc (∑' v, M.rootLaw s v * (if rE (M.rootLaw t) M.R v = 0 then 0
            else (rE (M.rootLaw t) M.R v) ^ (1 - α)))
          ≤ ∑' v, M.rootLaw s v := by
            refine ENNReal.tsum_le_tsum fun v => ?_
            rw [rootLaw_forced M ht, rE_pure]
            by_cases hv : M.R v M.zero
            · rw [if_pos hv, if_neg one_ne_zero, ENNReal.one_rpow, mul_one]
            · rw [if_neg hv, if_pos rfl, mul_zero]
              exact zero_le
        _ = 1 := (M.rootLaw s).tsum_coe
    calc _ ≤ 1 * Qb := mul_le_mul_left hS _
      _ ≤ M.DmuC α * Qb := mul_le_mul_left (M.one_le_DmuC α) _
      _ ≤ M.zeta α + M.DmuC α * Qb := le_add_self

set_option linter.unusedVariables false in
/-- **The root step** (`sec:independent-root`): if the restricted potential of the source
child-pair mixture against the target child-pair mixture at height `h` is at most `Qb`,
the restricted potential at height `h+1` is at most `ζ_α + D_μ Qb`.  The compatibility
hypothesis of `sec:quantitative-stopping` is carried for a uniform interface; the root
identity and the inverse moment need only `α ≥ 1`. -/
theorem P_succ_le (hc : M.IsCompat) {α : ℝ} (hα : 1 ≤ α) (s t : I) (h : ℕ) {Qb : ℝ≥0∞}
    (hQ : PhiDres α (M.childMix s h) (M.childMix t h) (SquareRel (M.sim h)) ≤ Qb) :
    M.P α s t (h + 1) ≤ M.zeta α + M.DmuC α * Qb := by
  -- the child-pair inverse moment and the child-pair restricted potential
  have hmom : ∑' p, M.childMix s h p * WresD α (M.childMix t h) (SquareRel (M.sim h)) p
      ≤ 1 + ENNReal.ofReal α * Qb :=
    (tsum_WresD_le hα _ _ _).trans (add_le_add_right (mul_le_mul_right hQ _) _)
  have hpot : ∑' p, M.childMix s h p
      * (if rE (M.childMix t h) (SquareRel (M.sim h)) p = 0 then 0
          else phiE α (q (M.childMix t h) (SquareRel (M.sim h)) p)) ≤ Qb := hQ
  -- the potential as an iterated sum: the root state, then the independent child pair
  have hP : M.P α s t (h + 1) = ∑' v, M.rootLaw s v * ∑' p, M.childMix s h p
      * (if rE (M.rho t (h + 1)) (M.sim (h + 1)) (branch (s, v) p) = 0 then 0
          else phiE α (q (M.rho t (h + 1)) (M.sim (h + 1)) (branch (s, v) p))) := by
    rw [P]
    unfold PhiDres
    rw [M.rho_succ s, tsum_bind_mul, rootT, tsum_map_mul]
    refine tsum_congr fun v => ?_
    rw [tsum_map_mul]
  -- the inner bound at a fixed source root state, by the root identity
  have hinner : ∀ v, (∑' p, M.childMix s h p
      * (if rE (M.rho t (h + 1)) (M.sim (h + 1)) (branch (s, v) p) = 0 then 0
          else phiE α (q (M.rho t (h + 1)) (M.sim (h + 1)) (branch (s, v) p))))
      ≤ (if rE (M.rootLaw t) M.R v = 0 then 0 else phiE α (q (M.rootLaw t) M.R v))
          * (1 + ENNReal.ofReal α * Qb)
        + (if rE (M.rootLaw t) M.R v = 0 then 0 else (rE (M.rootLaw t) M.R v) ^ (1 - α))
          * Qb := by
    intro v
    have hd : ∀ p, rE (M.rho t (h + 1)) (M.sim (h + 1)) (branch (s, v) p)
        = rE (M.rootLaw t) M.R v * rE (M.childMix t h) (SquareRel (M.sim h)) p :=
      fun p => M.deg_succ t h (s, v) p
    by_cases hc0 : rE (M.rootLaw t) M.R v = 0
    · rw [if_pos hc0, if_pos hc0, zero_mul, zero_mul, add_zero]
      refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun p => ?_)
      rw [hd p, hc0, zero_mul, if_pos rfl, mul_zero]
    · rw [if_neg hc0, if_neg hc0]
      calc (∑' p, M.childMix s h p
            * (if rE (M.rho t (h + 1)) (M.sim (h + 1)) (branch (s, v) p) = 0 then 0
                else phiE α (q (M.rho t (h + 1)) (M.sim (h + 1)) (branch (s, v) p))))
          ≤ ∑' p, M.childMix s h p
            * (phiE α (q (M.rootLaw t) M.R v)
                * WresD α (M.childMix t h) (SquareRel (M.sim h)) p
              + (rE (M.rootLaw t) M.R v) ^ (1 - α)
                * (if rE (M.childMix t h) (SquareRel (M.sim h)) p = 0 then 0
                    else phiE α (q (M.childMix t h) (SquareRel (M.sim h)) p))) := by
            refine ENNReal.tsum_le_tsum fun p => mul_le_mul_right ?_ _
            by_cases hr0 : rE (M.childMix t h) (SquareRel (M.sim h)) p = 0
            · rw [hd p, hr0, mul_zero, if_pos rfl]
              exact zero_le
            · have hcr : rE (M.rootLaw t) M.R v
                  * rE (M.childMix t h) (SquareRel (M.sim h)) p ≠ 0 := mul_ne_zero hc0 hr0
              rw [hd p, if_neg hcr, if_neg hr0,
                q_eq_one_sub (M.rho t (h + 1)) (M.sim (h + 1)) (branch (s, v) p), hd p,
                phiE_one_sub_mul hc0 rE_le_one hr0 rE_le_one,
                ← q_eq_one_sub (M.rootLaw t) M.R v,
                ← q_eq_one_sub (M.childMix t h) (SquareRel (M.sim h)) p,
                rE_rpow_neg_eq_WresD _ _ _ hr0]
        _ = phiE α (q (M.rootLaw t) M.R v)
              * ∑' p, M.childMix s h p * WresD α (M.childMix t h) (SquareRel (M.sim h)) p
            + (rE (M.rootLaw t) M.R v) ^ (1 - α)
              * ∑' p, M.childMix s h p
                * (if rE (M.childMix t h) (SquareRel (M.sim h)) p = 0 then 0
                    else phiE α (q (M.childMix t h) (SquareRel (M.sim h)) p)) := by
            rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
            exact tsum_congr fun p => by ring
        _ ≤ phiE α (q (M.rootLaw t) M.R v) * (1 + ENNReal.ofReal α * Qb)
            + (rE (M.rootLaw t) M.R v) ^ (1 - α) * Qb :=
            add_le_add (mul_le_mul_right hmom _) (mul_le_mul_right hpot _)
  -- integrate the root state and identify the root averages
  have hmain : M.P α s t (h + 1)
      ≤ PhiDres α (M.rootLaw s) (M.rootLaw t) M.R * (1 + ENNReal.ofReal α * Qb)
        + (∑' v, M.rootLaw s v * (if rE (M.rootLaw t) M.R v = 0 then 0
            else (rE (M.rootLaw t) M.R v) ^ (1 - α))) * Qb := by
    rw [hP]
    calc (∑' v, M.rootLaw s v * ∑' p, M.childMix s h p
          * (if rE (M.rho t (h + 1)) (M.sim (h + 1)) (branch (s, v) p) = 0 then 0
              else phiE α (q (M.rho t (h + 1)) (M.sim (h + 1)) (branch (s, v) p))))
        ≤ ∑' v, M.rootLaw s v
          * ((if rE (M.rootLaw t) M.R v = 0 then 0 else phiE α (q (M.rootLaw t) M.R v))
              * (1 + ENNReal.ofReal α * Qb)
            + (if rE (M.rootLaw t) M.R v = 0 then 0 else (rE (M.rootLaw t) M.R v) ^ (1 - α))
              * Qb) :=
          ENNReal.tsum_le_tsum fun v => mul_le_mul_right (hinner v) _
      _ = PhiDres α (M.rootLaw s) (M.rootLaw t) M.R * (1 + ENNReal.ofReal α * Qb)
          + (∑' v, M.rootLaw s v * (if rE (M.rootLaw t) M.R v = 0 then 0
              else (rE (M.rootLaw t) M.R v) ^ (1 - α))) * Qb := by
          rw [PhiDres, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
          exact tsum_congr fun v => by ring
  exact hmain.trans (M.root_average_le s t Qb)

end Model

end GraphMarkovMatching.Stopped
