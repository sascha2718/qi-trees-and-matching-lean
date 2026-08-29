/-
The nondegenerating varying-offspring bound
(`arbitrary_offspring_matching.tex`, Theorem `thm:main-matching`), certified with the
four-law constants of `thm:four-law`.

This is the corrected Step 2 of the renewal argument, in its one-block
(change-of-measure) form.  The per-state kernel budgets of the abstract
Markov pipeline are infinite for this process, so the recursion is run on
the fresh-pair potential `Θ_h = Φ_α(T_h → T_h; ≈_h)` instead:

* the bad degree of an attached sample against the fresh law factorises
  exactly, `q = δ_v + (1 - δ_v)·q̃`, where `δ_v` is the root-incompatibility
  mass and `q̃` is the bad degree of the frozen child pair against the full
  child-pair mixture `Ξ̄` (`qE_Tlaw_succ_branch`); no pattern conditioning
  ever happens, so no infinite budget is formed;
* the split lemma charges the root factor to the one-site graph potential
  `η = Φ_α(μ → μ; R_v)` with the product factor `1 + 2α·η`;
* the two-sided comparison `ofReal cr · T⊗T ≤ Ξ̄ ≤ ofReal Cr · T⊗T`
  transfers the mixture potential to the product reference
  (`phiE_q_le_of_between`, the certified change of measure), and the
  four-law contracts the product square with the certified constants
  `A = 2L + 2(1+δ)K` and `C = 2L·c_α + 20 + 2(1+δ⁻¹)α²`.

The recursion
`Θ_{h+1} ≤ η + D·(A·Θ_h + C·Θ_h²) + 2α·η·D·(A·Θ_h + C·Θ_h²)` with
`D = Cr·(Cr/cr^α)` then closes to a height-uniform bound under a closure
inequality, and the mean bad degree bounds the matching failure
probability.  At `α = 5/2`, `δ = 1` the linear constant `A` is the constant
`A₄` of `thm:four-law`, and with `cr = ν₂`, `Cr = C̄` the factor `D` is the
`D = C̄²/ν₂^{5/2}` of the retired draft's halving corollary; the pipeline
is described in `sec:lean` of `appendices.tex`.
-/
import GraphMarkovMatching.Process.Kernel
import GraphMarkovMatching.FourLaw.Assembly

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u

/-! ### The change of measure, pointwise -/

/-- **Change of measure for the safe potential**: if `ofReal cr · ρ ≤ ξ ≤
ofReal Cr · ρ`, then `φ_α(q_ξ(x)) ≤ (Cr/cr^α) · φ_α(q_ρ(x))` for every left
object `x`. -/
lemma phiE_q_le_of_between {X : Type u} {α : ℝ} (hα : 1 ≤ α) {cr Cr : ℝ}
    (hc0 : 0 < cr) (hC1 : 1 ≤ Cr)
    {ξ ρ : PMF X} {R : X → X → Prop}
    (hlow : ∀ y, ENNReal.ofReal cr * ρ y ≤ ξ y)
    (hup : ∀ y, ξ y ≤ ENNReal.ofReal Cr * ρ y) (x : X) :
    phiE α (q ξ R x) ≤ ENNReal.ofReal (Cr / cr ^ α) * phiE α (q ρ R x) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hCr0 : (0 : ℝ) ≤ Cr := by linarith
  have hqE : qE ξ R x ≤ ENNReal.ofReal Cr * qE ρ R x := by
    rw [qE, qE, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun y => ?_
    by_cases hy : R x y
    · simp [hy]
    · rw [if_neg hy, if_neg hy]
      exact hup y
  have hrE : ENNReal.ofReal cr * rE ρ R x ≤ rE ξ R x := by
    rw [rE, rE, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun y => ?_
    by_cases hy : R x y
    · rw [if_pos hy, if_pos hy]
      exact hlow y
    · simp [hy]
  have hq : q ξ R x ≤ Cr * q ρ R x := by
    have h1 := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top qE_ne_top) hqE
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCr0] at h1
  have hr : cr * (1 - q ρ R x) ≤ 1 - q ξ R x := by
    have h1 := ENNReal.toReal_mono rE_ne_top hrE
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0.le] at h1
    have h2 := toReal_rE_add_toReal_qE ρ R x
    have h3 := toReal_rE_add_toReal_qE ξ R x
    have hr0eq : (rE ρ R x).toReal = 1 - (qE ρ R x).toReal := by linarith
    have hr1eq : (rE ξ R x).toReal = 1 - (qE ξ R x).toReal := by linarith
    rw [q, q]
    calc cr * (1 - (qE ρ R x).toReal) = cr * (rE ρ R x).toReal := by rw [hr0eq]
      _ ≤ (rE ξ R x).toReal := h1
      _ = 1 - (qE ξ R x).toReal := hr1eq
  by_cases hq0 : q ρ R x < 1
  · have hr0 : (0 : ℝ) < 1 - q ρ R x := by linarith
    have hr1 : (0 : ℝ) < 1 - q ξ R x :=
      lt_of_lt_of_le (mul_pos hc0 hr0) hr
    have hq1 : q ξ R x < 1 := by linarith
    have hpow : (cr * (1 - q ρ R x)) ^ α ≤ (1 - q ξ R x) ^ α :=
      Real.rpow_le_rpow (mul_pos hc0 hr0).le hr hα0
    have hsplit : (cr * (1 - q ρ R x)) ^ α = cr ^ α * (1 - q ρ R x) ^ α :=
      Real.mul_rpow hc0.le hr0.le
    have hfrac : phi α (q ξ R x) ≤ (Cr / cr ^ α) * phi α (q ρ R x) := by
      rw [phi, phi, div_mul_div_comm]
      have hd1 : (0 : ℝ) < (1 - q ξ R x) ^ α := Real.rpow_pos_of_pos hr1 α
      have hd0 : (0 : ℝ) < cr ^ α * (1 - q ρ R x) ^ α :=
        mul_pos (Real.rpow_pos_of_pos hc0 α) (Real.rpow_pos_of_pos hr0 α)
      rw [div_le_div_iff₀ hd1 hd0]
      calc q ξ R x * (cr ^ α * (1 - q ρ R x) ^ α)
          = q ξ R x * (cr * (1 - q ρ R x)) ^ α := by rw [hsplit]
        _ ≤ (Cr * q ρ R x) * (1 - q ξ R x) ^ α :=
            mul_le_mul hq hpow
              (Real.rpow_nonneg (mul_pos hc0 hr0).le α)
              (mul_nonneg hCr0 q_nonneg)
    rw [phiE_of_lt hq1, phiE_of_lt hq0,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hfrac
  · have hq0' : q ρ R x = 1 := le_antisymm q_le_one (not_lt.mp hq0)
    rw [hq0', phiE_one]
    have hpos : (0 : ℝ) < Cr / cr ^ α :=
      div_pos (by linarith) (Real.rpow_pos_of_pos hc0 α)
    rw [ENNReal.mul_top (by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hpos)]
    exact le_top

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (ν : PMF ℕ) (v0 : V)

/-! ### The potentials -/

/-- The one-site graph potential `η = Φ_α(μ → μ; R_v)`. -/
noncomputable def etaG : ℝ≥0∞ := PhiD α μ μ Rv

/-- The fresh-pair potential at height `h`. -/
noncomputable def Theta (h : ℕ) : ℝ≥0∞ :=
  PhiD α (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) (fullSim (labRel Rv) h)

/-- Left decomposition of a `Ξ̄`-source potential into components. -/
lemma PhiD_XiBar_eq (h : ℕ) (ν' : PMF (FullLab (V × ℕ) h × FullLab (V × ℕ) h))
    (R : FullLab (V × ℕ) h × FullLab (V × ℕ) h
      → FullLab (V × ℕ) h × FullLab (V × ℕ) h → Prop) :
    PhiD α (XiBar μ ν v0 h) ν' R = ∑' k, ν k * PhiD α (Xi μ ν v0 k h) ν' R := by
  rw [XiBar, PhiD_bind_left]

/-! ### Height zero -/

lemma qE_Tlaw_zero_leaf (s : V × ℕ) :
    qE (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0) (leaf s) = qE μ Rv s.1 := by
  rw [Tlaw, qE_bind, ENNReal.tsum_prod']
  calc (∑' w, ∑' k', freshQ μ ν (w, k')
        * qE (muM (varyK μ ν v0) (w, k') 0) (fullSim (labRel Rv) 0) (leaf s))
      = ∑' w, ∑' k', (μ w * badInd Rv s.1 w) * ν k' := by
        refine tsum_congr fun w => tsum_congr fun k' => ?_
        have hbad : badInd (fullSim (labRel Rv) 0) (leaf s) (leaf (w, k'))
            = badInd Rv s.1 w := by
          rw [badInd, badInd]
          by_cases hR : Rv s.1 w
          · rw [if_pos ((fullSim_leaf (labRel Rv) s (w, k')).mpr hR), if_pos hR]
          · rw [if_neg (fun hc => hR ((fullSim_leaf (labRel Rv) s (w, k')).mp hc)),
              if_neg hR]
        rw [show muM (varyK μ ν v0) (w, k') 0 = PMF.pure (leaf (w, k')) from rfl,
          qE_pure, hbad, show freshQ μ ν (w, k') = μ w * ν k' from rfl]
        ring
    _ = ∑' w, μ w * badInd Rv s.1 w := by
        refine tsum_congr fun w => ?_
        rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
    _ = qE μ Rv s.1 := (qE_eq_tsum_mul μ Rv s.1).symm

lemma Theta_zero : Theta α Rv μ ν v0 0 = etaG α Rv μ := by
  rw [Theta, Tlaw, PhiD_bind_left]
  calc (∑' s : V × ℕ, freshQ μ ν s
        * PhiD α (muM (varyK μ ν v0) s 0) (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0))
      = ∑' s : V × ℕ, (μ s.1 * phiE α (q μ Rv s.1)) * ν s.2 := by
        refine tsum_congr fun s => ?_
        rw [show muM (varyK μ ν v0) s 0 = PMF.pure (leaf s) from rfl,
          show PhiD α (PMF.pure (leaf s)) (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0)
              = phiE α (q (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0) (leaf s)) from by
            rw [PhiD, tsum_pure_mul],
          show q (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0) (leaf s) = q μ Rv s.1 from by
            rw [q, q, qE_Tlaw_zero_leaf Rv μ ν v0 s],
          show freshQ μ ν s = μ s.1 * ν s.2 from rfl]
        ring
    _ = (∑' v, μ v * phiE α (q μ Rv v)) * ∑' k, ν k :=
        tsum_prod_split (fun v => μ v * phiE α (q μ Rv v)) (fun k => ν k)
    _ = etaG α Rv μ := by rw [PMF.tsum_coe, mul_one, etaG, PhiD]

/-! ### The exact conditional factorisation -/

/-- **The root factorisation**: against the fresh law, the bad degree of an
attached sample is exactly `δ_v + (1 - δ_v)·q̃` with `q̃` the bad degree of
the frozen child pair against the full child-pair mixture. -/
lemma qE_Tlaw_succ_branch (v : V) (k h : ℕ)
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    qE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
      = qE μ Rv v + rE μ Rv v
          * qE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp := by
  set qΞ := qE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp with hqΞ
  rw [Tlaw, qE_bind, ENNReal.tsum_prod']
  have hinner : ∀ w : V,
      (∑' k' : ℕ, freshQ μ ν (w, k')
        * qE (muM (varyK μ ν v0) (w, k') (h + 1)) (fullSim (labRel Rv) (h + 1))
            (branch (v, k) xp))
      = μ w * (if Rv v w then qΞ else 1) := by
    intro w
    by_cases hvw : Rv v w
    · rw [if_pos hvw]
      calc (∑' k' : ℕ, freshQ μ ν (w, k')
            * qE (muM (varyK μ ν v0) (w, k') (h + 1)) (fullSim (labRel Rv) (h + 1))
                (branch (v, k) xp))
          = ∑' k' : ℕ, μ w * (ν k'
              * qE (Xi μ ν v0 k' h) (SquareRel (fullSim (labRel Rv) h)) xp) := by
            refine tsum_congr fun k' => ?_
            rw [qE_succ_branch (varyK μ ν v0) (labRel Rv)
                (show labRel Rv (v, k) (w, k') from hvw) h xp,
              show pairMix (varyK μ ν v0) (w, k') h = Xi μ ν v0 k' h from rfl,
              show freshQ μ ν (w, k') = μ w * ν k' from rfl]
            ring
        _ = μ w * ∑' k' : ℕ, ν k'
              * qE (Xi μ ν v0 k' h) (SquareRel (fullSim (labRel Rv) h)) xp :=
            ENNReal.tsum_mul_left
        _ = μ w * qΞ := by rw [hqΞ, XiBar, qE_bind]
    · rw [if_neg hvw, mul_one]
      calc (∑' k' : ℕ, freshQ μ ν (w, k')
            * qE (muM (varyK μ ν v0) (w, k') (h + 1)) (fullSim (labRel Rv) (h + 1))
                (branch (v, k) xp))
          = ∑' k' : ℕ, μ w * ν k' := by
            refine tsum_congr fun k' => ?_
            rw [qE_succ_branch_mismatch (varyK μ ν v0) (labRel Rv)
                (show ¬ labRel Rv (v, k) (w, k') from hvw) h xp, mul_one]
            rfl
        _ = μ w := by rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  calc (∑' w, ∑' k', freshQ μ ν (w, k')
        * qE (muM (varyK μ ν v0) (w, k') (h + 1)) (fullSim (labRel Rv) (h + 1))
            (branch (v, k) xp))
      = ∑' w, μ w * (if Rv v w then qΞ else 1) := tsum_congr hinner
    _ = ∑' w, ((if Rv v w then μ w else 0) * qΞ + (if Rv v w then 0 else μ w)) := by
        refine tsum_congr fun w => ?_
        by_cases hvw : Rv v w
        · rw [if_pos hvw, if_pos hvw, if_pos hvw, add_zero]
        · rw [if_neg hvw, if_neg hvw, if_neg hvw, zero_mul, zero_add, mul_one]
    _ = (∑' w, (if Rv v w then μ w else 0)) * qΞ
          + ∑' w, (if Rv v w then 0 else μ w) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ = rE μ Rv v * qΞ + qE μ Rv v := by rw [rE, qE]
    _ = qE μ Rv v + rE μ Rv v * qΞ := add_comm _ _

/-! ### The split at the root -/

lemma phiE_branch_le (hα : 1 ≤ α) (v : V) (k h : ℕ)
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    phiE α (q (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp))
      ≤ phiE α (q μ Rv v)
        + phiE α (q (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp)
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v)
            * phiE α (q (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp)) := by
  have hkey : q (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
      = q μ Rv v + (1 - q μ Rv v)
          * q (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp := by
    have hre : (rE μ Rv v).toReal = 1 - q μ Rv v := by
      have h1 := toReal_rE_add_toReal_qE μ Rv v
      rw [q]
      linarith
    rw [q, qE_Tlaw_succ_branch Rv μ ν v0 v k h xp,
      ENNReal.toReal_add qE_ne_top (ENNReal.mul_ne_top rE_ne_top qE_ne_top),
      ENNReal.toReal_mul, hre]
    rfl
  rw [hkey]
  exact phiE_split hα q_nonneg q_le_one q_nonneg q_le_one

/-! ### The one-step recursion -/

lemma Theta_succ_le (hα : 1 ≤ α) (h : ℕ) :
    Theta α Rv μ ν v0 (h + 1)
      ≤ etaG α Rv μ
        + PhiD α (XiBar μ ν v0 h) (XiBar μ ν v0 h)
            (SquareRel (fullSim (labRel Rv) h))
        + ENNReal.ofReal (2 * α)
          * (etaG α Rv μ
            * PhiD α (XiBar μ ν v0 h) (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h))) := by
  set Ψ := PhiD α (XiBar μ ν v0 h) (XiBar μ ν v0 h)
    (SquareRel (fullSim (labRel Rv) h)) with hΨ
  have hcomp : ∀ s : V × ℕ,
      PhiD α (muM (varyK μ ν v0) s (h + 1)) (Tlaw μ ν v0 (h + 1))
          (fullSim (labRel Rv) (h + 1))
        ≤ phiE α (q μ Rv s.1)
          + PhiD α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h))
          + ENNReal.ofReal (2 * α)
            * (phiE α (q μ Rv s.1)
              * PhiD α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                  (SquareRel (fullSim (labRel Rv) h))) := by
    intro s
    obtain ⟨v, k⟩ := s
    rw [show muM (varyK μ ν v0) (v, k) (h + 1)
        = (Xi μ ν v0 k h).map (branch (v, k)) from rfl, PhiD_map_left]
    set A := phiE α (q μ Rv v) with hA
    set B := fun xp => phiE α
      (q (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp) with hB
    calc (∑' xp, Xi μ ν v0 k h xp
            * phiE α (q (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
                (branch (v, k) xp)))
        ≤ ∑' xp, Xi μ ν v0 k h xp
            * (A + B xp + ENNReal.ofReal (2 * α) * (A * B xp)) :=
          ENNReal.tsum_le_tsum fun xp =>
            mul_le_mul_right (phiE_branch_le α Rv μ ν v0 hα v k h xp) _
      _ = (∑' xp, Xi μ ν v0 k h xp * A) + (∑' xp, Xi μ ν v0 k h xp * B xp)
            + ∑' xp, ENNReal.ofReal (2 * α) * A * (Xi μ ν v0 k h xp * B xp) := by
          rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
          refine tsum_congr fun xp => ?_
          ring
      _ = A + PhiD α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h))
            + ENNReal.ofReal (2 * α)
              * (A * PhiD α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
                  (SquareRel (fullSim (labRel Rv) h))) := by
          have h1 : (∑' xp, Xi μ ν v0 k h xp * A) = A := by
            rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
          have h2 : (∑' xp, Xi μ ν v0 k h xp * B xp)
              = PhiD α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
                  (SquareRel (fullSim (labRel Rv) h)) := rfl
          have h3 : (∑' xp, ENNReal.ofReal (2 * α) * A * (Xi μ ν v0 k h xp * B xp))
              = ENNReal.ofReal (2 * α)
                * (A * PhiD α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
                    (SquareRel (fullSim (labRel Rv) h))) := by
            rw [ENNReal.tsum_mul_left, h2, mul_assoc]
          rw [h1, h2, h3]
  have hexp : Theta α Rv μ ν v0 (h + 1)
      = ∑' s : V × ℕ, freshQ μ ν s
          * PhiD α (muM (varyK μ ν v0) s (h + 1)) (Tlaw μ ν v0 (h + 1))
              (fullSim (labRel Rv) (h + 1)) := by
    rw [Theta, Tlaw, PhiD_bind_left]
  calc Theta α Rv μ ν v0 (h + 1)
      = ∑' s : V × ℕ, freshQ μ ν s
          * PhiD α (muM (varyK μ ν v0) s (h + 1)) (Tlaw μ ν v0 (h + 1))
              (fullSim (labRel Rv) (h + 1)) := hexp
    _ ≤ ∑' s : V × ℕ, freshQ μ ν s
          * (phiE α (q μ Rv s.1)
            + PhiD α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h))
            + ENNReal.ofReal (2 * α)
              * (phiE α (q μ Rv s.1)
                * PhiD α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                    (SquareRel (fullSim (labRel Rv) h)))) :=
        ENNReal.tsum_le_tsum fun s => mul_le_mul_right (hcomp s) _
    _ = (∑' s : V × ℕ, (μ s.1 * phiE α (q μ Rv s.1)) * ν s.2)
          + (∑' s : V × ℕ, μ s.1
            * (ν s.2 * PhiD α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h))))
          + ENNReal.ofReal (2 * α)
            * ∑' s : V × ℕ, (μ s.1 * phiE α (q μ Rv s.1))
                * (ν s.2 * PhiD α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                    (SquareRel (fullSim (labRel Rv) h))) := by
        rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        refine tsum_congr fun s => ?_
        rw [show freshQ μ ν s = μ s.1 * ν s.2 from rfl]
        ring
    _ = etaG α Rv μ + Ψ + ENNReal.ofReal (2 * α) * (etaG α Rv μ * Ψ) := by
        have hη : (∑' s : V × ℕ, (μ s.1 * phiE α (q μ Rv s.1)) * ν s.2)
            = etaG α Rv μ := by
          rw [tsum_prod_split (fun v => μ v * phiE α (q μ Rv v)) (fun k => ν k),
            PMF.tsum_coe, mul_one, etaG, PhiD]
        have hmix : (∑' k, ν k * PhiD α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h))) = Ψ := by
          rw [hΨ, PhiD_XiBar_eq]
        have hΨ' : (∑' s : V × ℕ, μ s.1
              * (ν s.2 * PhiD α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                  (SquareRel (fullSim (labRel Rv) h)))) = Ψ := by
          rw [tsum_prod_split (fun v => μ v)
              (fun k => ν k * PhiD α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h))),
            PMF.tsum_coe, one_mul, hmix]
        have hcross : (∑' s : V × ℕ, (μ s.1 * phiE α (q μ Rv s.1))
              * (ν s.2 * PhiD α (Xi μ ν v0 s.2 h) (XiBar μ ν v0 h)
                  (SquareRel (fullSim (labRel Rv) h))))
            = etaG α Rv μ * Ψ := by
          rw [tsum_prod_split (fun v => μ v * phiE α (q μ Rv v))
              (fun k => ν k * PhiD α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h))), hmix]
          rfl
        rw [hη, hΨ', hcross]

/-! ### Change of measure for the mixture potential -/

lemma PhiD_XiBar_le_prod (hα : 1 ≤ α) {cr Cr : ℝ} (hc0 : 0 < cr) (hC1 : 1 ≤ Cr)
    (h : ℕ)
    (hlow : ∀ x, ENNReal.ofReal cr * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x
        ≤ XiBar μ ν v0 h x)
    (hup : ∀ x, XiBar μ ν v0 h x
        ≤ ENNReal.ofReal Cr * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x) :
    PhiD α (XiBar μ ν v0 h) (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h))
      ≤ ENNReal.ofReal (Cr * (Cr / cr ^ α))
        * PhiD α (prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h))
            (prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h))
            (SquareRel (fullSim (labRel Rv) h)) := by
  have hCr0 : (0 : ℝ) ≤ Cr := by linarith
  rw [PhiD, PhiD, ENNReal.ofReal_mul hCr0, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun xp => ?_
  calc XiBar μ ν v0 h xp
        * phiE α (q (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp)
      ≤ (ENNReal.ofReal Cr * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) xp)
          * (ENNReal.ofReal (Cr / cr ^ α)
            * phiE α (q (prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h))
                (SquareRel (fullSim (labRel Rv) h)) xp)) :=
        mul_le_mul' (hup xp) (phiE_q_le_of_between hα hc0 hC1 hlow hup xp)
    _ = ENNReal.ofReal Cr * ENNReal.ofReal (Cr / cr ^ α)
          * (prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) xp
            * phiE α (q (prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h))
                (SquareRel (fullSim (labRel Rv) h)) xp)) := by ring

/-! ### The four-law at the product reference -/

lemma prodT_square_le {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (h : ℕ) :
    PhiD α (prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h))
        (prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h))
        (SquareRel (fullSim (labRel Rv) h))
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * Theta α Rv μ ν v0 h
        + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
          * Theta α Rv μ ν v0 h ^ 2 :=
  PhiD_fourlaw_le hα hδ hL0 hL hK0 hK (Tlaw μ ν v0 h) (Tlaw μ ν v0 h)
    (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) (fullSim (labRel Rv) h)
    (fullSim_symm (labRel Rv) (labRel_symm Rv hsymm) h) (Theta α Rv μ ν v0 h)
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl

/-! ### The full recursion, invariance, and the failure bound -/

/-- **The certified varying-offspring recursion**: with `D = Cr·(Cr/cr^α)`,

    `Θ_{h+1} ≤ η + D·(A·Θ_h + C·Θ_h²)·(1 + 2α·η)`. -/
theorem Theta_succ_le_full {δ L K cr Cr : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a)
    (hc0 : 0 < cr) (hC1 : 1 ≤ Cr)
    (hlow : ∀ h x, ENNReal.ofReal cr * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x
        ≤ XiBar μ ν v0 h x)
    (hup : ∀ h x, XiBar μ ν v0 h x
        ≤ ENNReal.ofReal Cr * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x)
    (h : ℕ) :
    Theta α Rv μ ν v0 (h + 1)
      ≤ etaG α Rv μ
        + ENNReal.ofReal (Cr * (Cr / cr ^ α))
          * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * Theta α Rv μ ν v0 h
            + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
              * Theta α Rv μ ν v0 h ^ 2)
        + ENNReal.ofReal (2 * α)
          * (etaG α Rv μ
            * (ENNReal.ofReal (Cr * (Cr / cr ^ α))
              * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * Theta α Rv μ ν v0 h
                + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
                  * Theta α Rv μ ν v0 h ^ 2))) := by
  have hΨle : PhiD α (XiBar μ ν v0 h) (XiBar μ ν v0 h)
        (SquareRel (fullSim (labRel Rv) h))
      ≤ ENNReal.ofReal (Cr * (Cr / cr ^ α))
        * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * Theta α Rv μ ν v0 h
          + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
            * Theta α Rv μ ν v0 h ^ 2) :=
    le_trans (PhiD_XiBar_le_prod α Rv μ ν v0 hα hc0 hC1 h (hlow h) (hup h))
      (mul_le_mul_right (prodT_square_le α Rv μ ν v0 hα hδ hL0 hL hK0 hK hsymm h) _)
  refine le_trans (Theta_succ_le α Rv μ ν v0 hα h) ?_
  exact add_le_add (add_le_add le_rfl hΨle)
    (mul_le_mul_right (mul_le_mul_right hΨle _) _)

/-- **Height-uniform invariance under a closure inequality.** -/
theorem Theta_le_of_closed {δ L K cr Cr : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a)
    (hc0 : 0 < cr) (hC1 : 1 ≤ Cr)
    (hlow : ∀ h x, ENNReal.ofReal cr * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x
        ≤ XiBar μ ν v0 h x)
    (hup : ∀ h x, XiBar μ ν v0 h x
        ≤ ENNReal.ofReal Cr * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x)
    (B : ℝ≥0∞)
    (hclose : etaG α Rv μ
        + ENNReal.ofReal (Cr * (Cr / cr ^ α))
          * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
            + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
              * B ^ 2)
        + ENNReal.ofReal (2 * α)
          * (etaG α Rv μ
            * (ENNReal.ofReal (Cr * (Cr / cr ^ α))
              * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
                + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
                  * B ^ 2))) ≤ B) :
    ∀ h, Theta α Rv μ ν v0 h ≤ B := by
  intro h
  induction h with
  | zero =>
      rw [Theta_zero α Rv μ ν v0]
      exact le_trans (le_trans le_self_add le_self_add) hclose
  | succ h ih =>
      refine le_trans (Theta_succ_le_full α Rv μ ν v0 hα hδ hL0 hL hK0 hK hsymm
        hc0 hC1 hlow hup h) (le_trans ?_ hclose)
      have hmono : ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * Theta α Rv μ ν v0 h
            + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
              * Theta α Rv μ ν v0 h ^ 2
          ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
            + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
              * B ^ 2 := by
        refine add_le_add (mul_le_mul_right ih _) (mul_le_mul_right ?_ _)
        rw [pow_two, pow_two]
        exact mul_le_mul' ih ih
      exact add_le_add (add_le_add le_rfl (mul_le_mul_right hmono _))
        (mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hmono _) _) _)

/-- **The matching failure bound**: under the closure inequality, two
independent fresh samples of height `h` fail to admit a matching
automorphism with probability at most `B`, uniformly in `h`. -/
theorem varyingMatching_failure_le {δ L K cr Cr : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a)
    (hc0 : 0 < cr) (hC1 : 1 ≤ Cr)
    (hlow : ∀ h x, ENNReal.ofReal cr * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x
        ≤ XiBar μ ν v0 h x)
    (hup : ∀ h x, XiBar μ ν v0 h x
        ≤ ENNReal.ofReal Cr * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x)
    (B : ℝ≥0∞)
    (hclose : etaG α Rv μ
        + ENNReal.ofReal (Cr * (Cr / cr ^ α))
          * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
            + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
              * B ^ 2)
        + ENNReal.ofReal (2 * α)
          * (etaG α Rv μ
            * (ENNReal.ofReal (Cr * (Cr / cr ^ α))
              * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
                + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
                  * B ^ 2))) ≤ B)
    (h : ℕ) :
    ∑' x, Tlaw μ ν v0 h x * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x ≤ B :=
  le_trans
    (tsum_qE_le_PhiD (by linarith) (Tlaw μ ν v0 h) (Tlaw μ ν v0 h)
      (fullSim (labRel Rv) h))
    (Theta_le_of_closed α Rv μ ν v0 hα hδ hL0 hL hK0 hK hsymm hc0 hC1
      hlow hup B hclose h)

/-! ### The halving-closed instantiation -/

/-- The lower comparison with the real constant `cr = (ν₂).toReal`. -/
lemma XiBar_ge' (h : ℕ) (x : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    ENNReal.ofReal (ν 2).toReal * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x
      ≤ XiBar μ ν v0 h x := by
  rw [ENNReal.ofReal_toReal (PMF.apply_ne_top ν 2)]
  exact XiBar_ge μ ν v0 h x

/-- The upper comparison with the real constant `Cr = C̄.toReal`. -/
lemma XiBar_le' (hcl : HalvingClosed μ ν v0) (hCB : CBar μ ν v0 ≠ ⊤) (h : ℕ)
    (x : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    XiBar μ ν v0 h x
      ≤ ENNReal.ofReal (CBar μ ν v0).toReal
          * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x := by
  rw [ENNReal.ofReal_toReal hCB]
  exact XiBar_le_CBar μ ν v0 hcl h x

/-- **The varying-offspring matching bound, halving-closed form**: with
`cr = ν₂` and `Cr = C̄` the comparison hypotheses are discharged, so under
the closure inequality the failure probability is at most `B`, uniformly in
the height. -/
theorem varyingMatching_failure_le_closed {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a)
    (hcl : HalvingClosed μ ν v0) (hν2 : ν 2 ≠ 0) (hCB : CBar μ ν v0 ≠ ⊤)
    (B : ℝ≥0∞)
    (hclose : etaG α Rv μ
        + ENNReal.ofReal ((CBar μ ν v0).toReal
            * ((CBar μ ν v0).toReal / (ν 2).toReal ^ α))
          * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
            + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
              * B ^ 2)
        + ENNReal.ofReal (2 * α)
          * (etaG α Rv μ
            * (ENNReal.ofReal ((CBar μ ν v0).toReal
                * ((CBar μ ν v0).toReal / (ν 2).toReal ^ α))
              * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
                + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
                  * B ^ 2))) ≤ B)
    (h : ℕ) :
    ∑' x, Tlaw μ ν v0 h x * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x ≤ B := by
  have hc0 : (0 : ℝ) < (ν 2).toReal :=
    ENNReal.toReal_pos hν2 (PMF.apply_ne_top ν 2)
  have hC1 : (1 : ℝ) ≤ (CBar μ ν v0).toReal := by
    have h1 := ENNReal.toReal_mono hCB (one_le_CBar μ ν v0)
    rwa [ENNReal.toReal_one] at h1
  exact varyingMatching_failure_le α Rv μ ν v0 hα hδ hL0 hL hK0 hK hsymm hc0 hC1
    (fun h x => XiBar_ge' μ ν v0 h x)
    (fun h x => XiBar_le' μ ν v0 hcl hCB h x) B hclose h

end GraphMarkovMatching
