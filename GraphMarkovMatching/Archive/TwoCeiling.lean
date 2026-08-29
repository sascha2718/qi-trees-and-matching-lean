/-
The two-ceiling refinement of the per-state step (`Step`, in β-weighted
form), and the closed invariance.

A uniform frozen-pattern ceiling cannot contract, because one-sided
patterns (only one pairing compatible) admit only the product bound. The
refinement splits the tilted kernel mixture: two-sided patterns are fed to
the certified four-law contraction (`fourLaw_tree`), one-sided ones to the
directed product lemma through relation monotonicity (the crossed case by a
column-swap reindex), weighted by the tilted one-sided mass, whose kernel
average is the budget `betaD`. The result:

    Φ_{n+1}(s,t) ≤ η(s,t) + Γ₂ + β(s,t)·Γ₁ + 2α·η(s,t)·(Γ₂ + Γ₁),

and with both ceilings discharged by the certified cell bounds, the
invariance `PhiM_le_of_invariant_closed` is unconditional: budgets plus one
closure inequality.
-/
import GraphMarkovMatching.FourLaw.Assembly
import GraphMarkovMatching.Archive.Reduction

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

set_option maxHeartbeats 800000

universe u
variable {X : Type u}

/-! ### Relation monotonicity and the one-sided cell bounds -/

/-- A larger relation has a smaller directed potential. -/
lemma PhiD_mono_rel {α : ℝ} (hα : 0 ≤ α) (μ ν : PMF X) {R R' : X → X → Prop}
    (h : ∀ a b, R a b → R' a b) : PhiD α μ ν R' ≤ PhiD α μ ν R := by
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  refine phiE_mono hα q_nonneg ?_
  refine ENNReal.toReal_mono qE_ne_top (ENNReal.tsum_le_tsum fun y => ?_)
  by_cases hy : R x y
  · rw [if_pos hy, if_pos (h x y hy)]
  · rw [if_neg hy]
    by_cases hy' : R' x y <;> simp [hy']

/-- Column-swap reindex: the crossed pair relation against `ν₀⊗ν₁` is the
straight tensor against `ν₁⊗ν₀`. -/
lemma qE_crossed (ν₀ ν₁ : PMF X) (R : X → X → Prop) (xp : X × X) :
    qE (prodPMF ν₀ ν₁) (fun a b => R a.1 b.2 ∧ R a.2 b.1) xp
      = qE (prodPMF ν₁ ν₀) (ProdRel R R) xp := by
  rw [qE_eq_tsum_mul, qE_eq_tsum_mul]
  calc (∑' yp : X × X, prodPMF ν₀ ν₁ yp
        * badInd (fun a b => R a.1 b.2 ∧ R a.2 b.1) xp yp)
      = ∑' yp : X × X, prodPMF ν₀ ν₁ (Equiv.prodComm X X yp)
          * badInd (fun a b => R a.1 b.2 ∧ R a.2 b.1) xp (Equiv.prodComm X X yp) :=
        (Equiv.tsum_eq (Equiv.prodComm X X)
          (fun yp => prodPMF ν₀ ν₁ yp
            * badInd (fun a b => R a.1 b.2 ∧ R a.2 b.1) xp yp)).symm
    _ = ∑' yp : X × X, prodPMF ν₁ ν₀ yp * badInd (ProdRel R R) xp yp := by
        refine tsum_congr fun yp => ?_
        have hb : badInd (fun a b => R a.1 b.2 ∧ R a.2 b.1) xp (Equiv.prodComm X X yp)
            = badInd (ProdRel R R) xp yp := by
          simp only [badInd]
          by_cases h : (fun a b : X × X => R a.1 b.2 ∧ R a.2 b.1) xp (Equiv.prodComm X X yp)
          · rw [if_pos h, if_pos (show ProdRel R R xp yp from h)]
          · rw [if_neg h, if_neg (show ¬ ProdRel R R xp yp from fun hc => h hc)]
        rw [hb]
        have hm : prodPMF ν₀ ν₁ (Equiv.prodComm X X yp) = prodPMF ν₁ ν₀ yp := by
          simp only [Equiv.prodComm_apply, prodPMF_apply, Prod.fst_swap, Prod.snd_swap]
          ring
        rw [hm]

/-- The one-sided cell bound, straight pairing: the square potential is at
most the straight tensor product bound. -/
theorem PhiD_square_straight_le {α : ℝ} (hα : 1 ≤ α)
    (μ₀ μ₁ ν₀ ν₁ : PMF X) (R : X → X → Prop) :
    PhiD α (prodPMF μ₀ μ₁) (prodPMF ν₀ ν₁) (SquareRel R)
      ≤ PhiD α μ₀ ν₀ R + PhiD α μ₁ ν₁ R
        + ENNReal.ofReal (2 * α) * (PhiD α μ₀ ν₀ R * PhiD α μ₁ ν₁ R) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  calc PhiD α (prodPMF μ₀ μ₁) (prodPMF ν₀ ν₁) (SquareRel R)
      ≤ PhiD α (prodPMF μ₀ μ₁) (prodPMF ν₀ ν₁) (ProdRel R R) :=
        PhiD_mono_rel hα0 _ _ (fun a b h => Or.inl h)
    _ ≤ PhiD α μ₀ ν₀ R + PhiD α μ₁ ν₁ R
          + ENNReal.ofReal (2 * α) * (PhiD α μ₀ ν₀ R * PhiD α μ₁ ν₁ R) :=
        PhiD_prodPMF_le hα μ₀ ν₀ μ₁ ν₁ R R

/-- The one-sided cell bound, crossed pairing. -/
theorem PhiD_square_crossed_le {α : ℝ} (hα : 1 ≤ α)
    (μ₀ μ₁ ν₀ ν₁ : PMF X) (R : X → X → Prop) :
    PhiD α (prodPMF μ₀ μ₁) (prodPMF ν₀ ν₁) (SquareRel R)
      ≤ PhiD α μ₀ ν₁ R + PhiD α μ₁ ν₀ R
        + ENNReal.ofReal (2 * α) * (PhiD α μ₀ ν₁ R * PhiD α μ₁ ν₀ R) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  calc PhiD α (prodPMF μ₀ μ₁) (prodPMF ν₀ ν₁) (SquareRel R)
      ≤ PhiD α (prodPMF μ₀ μ₁) (prodPMF ν₀ ν₁) (fun a b => R a.1 b.2 ∧ R a.2 b.1) :=
        PhiD_mono_rel hα0 _ _ (fun a b h => Or.inr h)
    _ = PhiD α (prodPMF μ₀ μ₁) (prodPMF ν₁ ν₀) (ProdRel R R) := by
        rw [PhiD, PhiD]
        exact tsum_congr fun xp => by
          rw [show q (prodPMF ν₀ ν₁) (fun a b => R a.1 b.2 ∧ R a.2 b.1) xp
              = q (prodPMF ν₁ ν₀) (ProdRel R R) xp from
            congrArg ENNReal.toReal (qE_crossed ν₀ ν₁ R xp)]
    _ ≤ PhiD α μ₀ ν₁ R + PhiD α μ₁ ν₀ R
          + ENNReal.ofReal (2 * α) * (PhiD α μ₀ ν₁ R * PhiD α μ₁ ν₀ R) :=
        PhiD_prodPMF_le hα μ₀ ν₁ μ₁ ν₀ R R

/-! ### Two-sidedness and the β budget -/

variable {S : Type u}
variable (α : ℝ) (P : S → PMF (S × S)) (R₀ : S → S → Prop)

/-- A pattern pair is two-sided if both pairings are compatible. -/
def TwoSided (R₀ : S → S → Prop) (σ τ : S × S) : Prop :=
  (R₀ σ.1 τ.1 ∧ R₀ σ.2 τ.2) ∧ (R₀ σ.1 τ.2 ∧ R₀ σ.2 τ.1)

/-- The tilted one-sided mass at an `x`-pattern. -/
noncomputable def oneSidedMass (t : S) (σ : S × S) : ℝ≥0∞ :=
  ∑' τ, if TwoSided R₀ σ τ then 0 else tiltW P R₀ t σ τ

/-- The β budget: the kernel average of the tilted one-sided mass. -/
noncomputable def betaD (s t : S) : ℝ≥0∞ :=
  ∑' σ, (P s) σ * oneSidedMass P R₀ t σ

/-- The tilted one-sided mass is a subprobability. -/
lemma oneSidedMass_le_one {t : S} {σ : S × S}
    (hD : rE (P t) (SquareRel R₀) σ ≠ 0) :
    oneSidedMass P R₀ t σ ≤ 1 := by
  rw [← tiltW_tsum_eq_one P R₀ hD, oneSidedMass]
  refine ENNReal.tsum_le_tsum fun τ => ?_
  by_cases h : TwoSided R₀ σ τ <;> simp [h]

/-! ### The refined conditional average -/

/-- The conditional part averages below the two-ceiling combination. -/
lemma tsum_Jmix_le_two {t : S} (n : ℕ) (σ : S × S) (Γ₂ Γ₁ : ℝ≥0∞)
    (hΓ₂ : ∀ τ : S × S, TwoSided R₀ σ τ →
      PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n)) (prodPMF (muM P τ.1 n) (muM P τ.2 n))
        (SquareRel (fullSim R₀ n)) ≤ Γ₂)
    (hΓ₁ : ∀ τ : S × S, SquareRel R₀ σ τ → ¬ TwoSided R₀ σ τ →
      PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n)) (prodPMF (muM P τ.1 n) (muM P τ.2 n))
        (SquareRel (fullSim R₀ n)) ≤ Γ₁)
    (hD : rE (P t) (SquareRel R₀) σ ≠ 0) :
    ∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp
      ≤ Γ₂ + oneSidedMass P R₀ t σ * Γ₁ := by
  have hswap : (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp)
      = ∑' τ, tiltW P R₀ t σ τ
          * PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n))
              (prodPMF (muM P τ.1 n) (muM P τ.2 n)) (SquareRel (fullSim R₀ n)) := by
    calc (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp)
        = ∑' xp, ∑' τ, tiltW P R₀ t σ τ
            * (prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
              * phiE α (q (prodPMF (muM P τ.1 n) (muM P τ.2 n))
                  (SquareRel (fullSim R₀ n)) xp)) := by
          refine tsum_congr fun xp => ?_
          rw [Jmix, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun τ => by ring
      _ = ∑' τ, ∑' xp, tiltW P R₀ t σ τ
            * (prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
              * phiE α (q (prodPMF (muM P τ.1 n) (muM P τ.2 n))
                  (SquareRel (fullSim R₀ n)) xp)) := ENNReal.tsum_comm
      _ = ∑' τ, tiltW P R₀ t σ τ
            * PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n))
                (prodPMF (muM P τ.1 n) (muM P τ.2 n)) (SquareRel (fullSim R₀ n)) := by
          refine tsum_congr fun τ => ?_
          rw [show PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n))
              (prodPMF (muM P τ.1 n) (muM P τ.2 n)) (SquareRel (fullSim R₀ n))
            = ∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
              * phiE α (q (prodPMF (muM P τ.1 n) (muM P τ.2 n))
                  (SquareRel (fullSim R₀ n)) xp) from rfl,
            ← ENNReal.tsum_mul_left]
  rw [hswap]
  calc (∑' τ, tiltW P R₀ t σ τ
        * PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n))
            (prodPMF (muM P τ.1 n) (muM P τ.2 n)) (SquareRel (fullSim R₀ n)))
      ≤ ∑' τ, ((if TwoSided R₀ σ τ then tiltW P R₀ t σ τ else 0) * Γ₂
          + (if TwoSided R₀ σ τ then 0 else tiltW P R₀ t σ τ) * Γ₁) := by
        refine ENNReal.tsum_le_tsum fun τ => ?_
        by_cases h2 : TwoSided R₀ σ τ
        · rw [if_pos h2, if_pos h2, zero_mul, add_zero]
          exact mul_le_mul_right (hΓ₂ τ h2) _
        · rw [if_neg h2, if_neg h2, zero_mul, zero_add]
          by_cases hsq : SquareRel R₀ σ τ
          · exact mul_le_mul_right (hΓ₁ τ hsq h2) _
          · have h0 : tiltW P R₀ t σ τ = 0 := by
              have e : tiltW P R₀ t σ τ
                  = (if SquareRel R₀ σ τ then (P t) τ else 0)
                    * (rE (P t) (SquareRel R₀) σ)⁻¹ := rfl
              rw [e, if_neg hsq, zero_mul]
            rw [h0, zero_mul, zero_mul]
    _ = (∑' τ, if TwoSided R₀ σ τ then tiltW P R₀ t σ τ else 0) * Γ₂
          + oneSidedMass P R₀ t σ * Γ₁ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, oneSidedMass]
    _ ≤ 1 * Γ₂ + oneSidedMass P R₀ t σ * Γ₁ := by
        gcongr
        rw [← tiltW_tsum_eq_one P R₀ hD]
        refine ENNReal.tsum_le_tsum fun τ => ?_
        by_cases h : TwoSided R₀ σ τ <;> simp [h]
    _ = Γ₂ + oneSidedMass P R₀ t σ * Γ₁ := by rw [one_mul]

/-! ### The refined per-pattern bound and step theorem -/

/-- The refined per-pattern averaged bound. -/
lemma tsum_pattern_le_two {t : S} {α : ℝ} (_hα : 1 ≤ α) (n : ℕ) (σ : S × S)
    (Γ₂ Γ₁ : ℝ≥0∞)
    (hΓ₂ : ∀ τ : S × S, TwoSided R₀ σ τ →
      PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n)) (prodPMF (muM P τ.1 n) (muM P τ.2 n))
        (SquareRel (fullSim R₀ n)) ≤ Γ₂)
    (hΓ₁ : ∀ τ : S × S, SquareRel R₀ σ τ → ¬ TwoSided R₀ σ τ →
      PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n)) (prodPMF (muM P τ.1 n) (muM P τ.2 n))
        (SquareRel (fullSim R₀ n)) ≤ Γ₁) :
    (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
      * (rootA α P R₀ t σ + Jmix α P R₀ t σ n xp
          + ENNReal.ofReal (2 * α) * (rootA α P R₀ t σ * Jmix α P R₀ t σ n xp)))
      ≤ rootA α P R₀ t σ + (Γ₂ + oneSidedMass P R₀ t σ * Γ₁)
          + ENNReal.ofReal (2 * α) * (rootA α P R₀ t σ * (Γ₂ + Γ₁)) := by
  by_cases hD : rE (P t) (SquareRel R₀) σ = 0
  · have hE1 : qE (P t) (SquareRel R₀) σ = 1 := by
      have h := rE_add_qE (P t) (SquareRel R₀) σ
      rw [hD, zero_add] at h
      exact h
    have htop : rootA α P R₀ t σ = ⊤ := by
      rw [rootA, q, hE1, ENNReal.toReal_one, phiE_one]
    rw [htop]
    simp
  · set A : ℝ≥0∞ := rootA α P R₀ t σ with hA
    set EJ : ℝ≥0∞ :=
      ∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp with hEJ
    have hexp : (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
        * (A + Jmix α P R₀ t σ n xp
            + ENNReal.ofReal (2 * α) * (A * Jmix α P R₀ t σ n xp)))
        = A + EJ + ENNReal.ofReal (2 * α) * A * EJ := by
      calc (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
          * (A + Jmix α P R₀ t σ n xp
              + ENNReal.ofReal (2 * α) * (A * Jmix α P R₀ t σ n xp)))
          = ∑' xp, (prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * A
              + prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp
              + (ENNReal.ofReal (2 * α) * A)
                  * (prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp)) :=
            tsum_congr fun xp => by ring
        _ = (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * A)
            + (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp)
            + ∑' xp, (ENNReal.ofReal (2 * α) * A)
                * (prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_add]
        _ = A + EJ + ENNReal.ofReal (2 * α) * A * EJ := by
            rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
              ENNReal.tsum_mul_left, ← hEJ, mul_assoc]
    rw [hexp]
    have hEJ1 : EJ ≤ Γ₂ + oneSidedMass P R₀ t σ * Γ₁ :=
      tsum_Jmix_le_two α P R₀ n σ Γ₂ Γ₁ hΓ₂ hΓ₁ hD
    have hEJ2 : EJ ≤ Γ₂ + Γ₁ := by
      refine le_trans hEJ1 ?_
      gcongr
      calc oneSidedMass P R₀ t σ * Γ₁ ≤ 1 * Γ₁ :=
            mul_le_mul_left (oneSidedMass_le_one P R₀ hD) _
        _ = Γ₁ := one_mul _
    calc A + EJ + ENNReal.ofReal (2 * α) * A * EJ
        ≤ A + (Γ₂ + oneSidedMass P R₀ t σ * Γ₁)
            + ENNReal.ofReal (2 * α) * A * (Γ₂ + Γ₁) := by gcongr
      _ = A + (Γ₂ + oneSidedMass P R₀ t σ * Γ₁)
            + ENNReal.ofReal (2 * α) * (A * (Γ₂ + Γ₁)) := by rw [mul_assoc]

/-- **The two-ceiling one-step bound**:

    Φ_{n+1}(s,t) ≤ η(s,t) + Γ₂ + β(s,t)·Γ₁ + 2α·η(s,t)·(Γ₂ + Γ₁). -/
theorem PhiM_succ_le_two {α : ℝ} (hα : 1 ≤ α) {s t : S} (hst : R₀ s t) (n : ℕ)
    (Γ₂ Γ₁ : ℝ≥0∞)
    (hΓ₂ : ∀ σ τ : S × S, TwoSided R₀ σ τ →
      PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n)) (prodPMF (muM P τ.1 n) (muM P τ.2 n))
        (SquareRel (fullSim R₀ n)) ≤ Γ₂)
    (hΓ₁ : ∀ σ τ : S × S, SquareRel R₀ σ τ → ¬ TwoSided R₀ σ τ →
      PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n)) (prodPMF (muM P τ.1 n) (muM P τ.2 n))
        (SquareRel (fullSim R₀ n)) ≤ Γ₁) :
    PhiM α P R₀ s t (n + 1)
      ≤ etaD α P R₀ s t + (Γ₂ + betaD P R₀ s t * Γ₁)
        + ENNReal.ofReal (2 * α) * (etaD α P R₀ s t * (Γ₂ + Γ₁)) := by
  have hstep1 : PhiM α P R₀ s t (n + 1)
      = ∑' xp, pairMix P s n xp
          * phiE α (q (pairMix P t n) (SquareRel (fullSim R₀ n)) xp) := by
    rw [PhiM, muM_succ, PhiD_map_left]
    refine tsum_congr fun xp => ?_
    congr 1
    have hq : q (muM P t (n + 1)) (fullSim R₀ (n + 1)) (branch s xp)
        = q (pairMix P t n) (SquareRel (fullSim R₀ n)) xp :=
      congrArg ENNReal.toReal (qE_succ_branch P R₀ hst n xp)
    rw [hq]
  have hstep2 : PhiM α P R₀ s t (n + 1)
      ≤ ∑' xp, pairMix P s n xp
          * (rootA α P R₀ t (rootPat n xp) + Jmix α P R₀ t (rootPat n xp) n xp
              + ENNReal.ofReal (2 * α)
                * (rootA α P R₀ t (rootPat n xp) * Jmix α P R₀ t (rootPat n xp) n xp)) := by
    rw [hstep1]
    exact ENNReal.tsum_le_tsum fun xp =>
      mul_le_mul_right (phiE_pairMix_le P R₀ hα t n xp) _
  have hstep3 : (∑' xp, pairMix P s n xp
      * (rootA α P R₀ t (rootPat n xp) + Jmix α P R₀ t (rootPat n xp) n xp
          + ENNReal.ofReal (2 * α)
            * (rootA α P R₀ t (rootPat n xp) * Jmix α P R₀ t (rootPat n xp) n xp)))
      = ∑' σ, (P s) σ * ∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
          * (rootA α P R₀ t σ + Jmix α P R₀ t σ n xp
              + ENNReal.ofReal (2 * α)
                * (rootA α P R₀ t σ * Jmix α P R₀ t σ n xp)) := by
    rw [show pairMix P s n
        = (P s).bind fun στ => prodPMF (muM P στ.1 n) (muM P στ.2 n) from rfl,
      tsum_bind_mul]
    refine tsum_congr fun σ => ?_
    congr 1
    refine tsum_congr fun xp => ?_
    by_cases hz : prodPMF (muM P σ.1 n) (muM P σ.2 n) xp = 0
    · rw [hz, zero_mul, zero_mul]
    · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp (by rwa [prodPMF_apply] at hz)
      have hpat : rootPat n xp = σ := by
        show (rootLab n xp.1, rootLab n xp.2) = σ
        rw [rootLab_of_ne_zero P n σ.1 xp.1 h1, rootLab_of_ne_zero P n σ.2 xp.2 h2]
      rw [hpat]
  calc PhiM α P R₀ s t (n + 1)
      ≤ ∑' σ, (P s) σ * ∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
          * (rootA α P R₀ t σ + Jmix α P R₀ t σ n xp
              + ENNReal.ofReal (2 * α)
                * (rootA α P R₀ t σ * Jmix α P R₀ t σ n xp)) := by
        rw [← hstep3]; exact hstep2
    _ ≤ ∑' σ, (P s) σ * (rootA α P R₀ t σ + (Γ₂ + oneSidedMass P R₀ t σ * Γ₁)
          + ENNReal.ofReal (2 * α) * (rootA α P R₀ t σ * (Γ₂ + Γ₁))) := by
        refine ENNReal.tsum_le_tsum fun σ => ?_
        exact mul_le_mul_right
          (tsum_pattern_le_two P R₀ hα n σ Γ₂ Γ₁ (fun τ => hΓ₂ σ τ) (fun τ => hΓ₁ σ τ)) _
    _ = etaD α P R₀ s t + (Γ₂ + betaD P R₀ s t * Γ₁)
          + ENNReal.ofReal (2 * α) * (etaD α P R₀ s t * (Γ₂ + Γ₁)) := by
        calc (∑' σ, (P s) σ * (rootA α P R₀ t σ + (Γ₂ + oneSidedMass P R₀ t σ * Γ₁)
              + ENNReal.ofReal (2 * α) * (rootA α P R₀ t σ * (Γ₂ + Γ₁))))
            = ∑' σ, ((P s) σ * rootA α P R₀ t σ
                + ((P s) σ * Γ₂ + ((P s) σ * oneSidedMass P R₀ t σ) * Γ₁)
                + (ENNReal.ofReal (2 * α))
                    * (((P s) σ * rootA α P R₀ t σ) * (Γ₂ + Γ₁))) :=
              tsum_congr fun σ => by ring
          _ = (∑' σ, (P s) σ * rootA α P R₀ t σ)
                + ((∑' σ, (P s) σ * Γ₂)
                  + (∑' σ, ((P s) σ * oneSidedMass P R₀ t σ) * Γ₁))
                + ∑' σ, (ENNReal.ofReal (2 * α))
                    * (((P s) σ * rootA α P R₀ t σ) * (Γ₂ + Γ₁)) := by
              rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
          _ = etaD α P R₀ s t + (Γ₂ + betaD P R₀ s t * Γ₁)
                + ENNReal.ofReal (2 * α) * (etaD α P R₀ s t * (Γ₂ + Γ₁)) := by
              have he : (∑' σ, (P s) σ * rootA α P R₀ t σ) = etaD α P R₀ s t := rfl
              rw [he, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
                ENNReal.tsum_mul_right, ← betaD,
                ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, he]

/-! ### The closed invariance -/

/-- **The unconditional invariance**: with the four-law and product cell
bounds certified, only the budgets and one closure inequality remain. Here
`Γ₂ = A'B + C'B²` and `Γ₁ = 2B + 2αB²` with the certified constants. -/
theorem PhiM_le_of_invariant_closed {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (ε β B : ℝ≥0∞)
    (hEta : ∀ s t, R₀ s t → etaD α P R₀ s t ≤ ε)
    (hBeta : ∀ s t, R₀ s t → betaD P R₀ s t ≤ β)
    (hclose : ε
        + ((ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
            + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * B ^ 2)
          + β * (B + B + ENNReal.ofReal (2 * α) * (B * B)))
        + ENNReal.ofReal (2 * α) * (ε
            * ((ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
                + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * B ^ 2)
              + (B + B + ENNReal.ofReal (2 * α) * (B * B)))) ≤ B) :
    ∀ n s t, R₀ s t → PhiM α P R₀ s t n ≤ B := by
  set Γ₂ : ℝ≥0∞ := ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
      + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * B ^ 2
    with hΓ₂def
  set Γ₁ : ℝ≥0∞ := B + B + ENNReal.ofReal (2 * α) * (B * B) with hΓ₁def
  intro n
  induction n with
  | zero =>
      intro s t hst
      rw [PhiM_zero α P R₀ hst]
      exact zero_le
  | succ n ih =>
      intro s t hst
      -- discharge the two-sided ceiling by the four-law theorem
      have hΓ₂h : ∀ σ τ : S × S, TwoSided R₀ σ τ →
          PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n))
            (prodPMF (muM P τ.1 n) (muM P τ.2 n)) (SquareRel (fullSim R₀ n)) ≤ Γ₂ := by
        intro σ τ h2
        obtain ⟨⟨hc00, hc11⟩, hc01, hc10⟩ := h2
        exact fourLaw_tree hα hδ hL0 hL hK0 hK P R₀ hsymm n σ τ B
          (ih σ.1 τ.1 hc00) (ih σ.1 τ.2 hc01) (ih σ.2 τ.1 hc10) (ih σ.2 τ.2 hc11)
          (ih τ.1 σ.1 (hsymm _ _ hc00)) (ih τ.1 σ.2 (hsymm _ _ hc10))
          (ih τ.2 σ.1 (hsymm _ _ hc01)) (ih τ.2 σ.2 (hsymm _ _ hc11))
      -- discharge the one-sided ceiling by the directed product bounds
      have hΓ₁h : ∀ σ τ : S × S, SquareRel R₀ σ τ → ¬ TwoSided R₀ σ τ →
          PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n))
            (prodPMF (muM P τ.1 n) (muM P τ.2 n)) (SquareRel (fullSim R₀ n)) ≤ Γ₁ := by
        intro σ τ hsq _
        rcases hsq with hstr | hcr
        · calc PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n))
                (prodPMF (muM P τ.1 n) (muM P τ.2 n)) (SquareRel (fullSim R₀ n))
              ≤ PhiM α P R₀ σ.1 τ.1 n + PhiM α P R₀ σ.2 τ.2 n
                  + ENNReal.ofReal (2 * α)
                    * (PhiM α P R₀ σ.1 τ.1 n * PhiM α P R₀ σ.2 τ.2 n) :=
                PhiD_square_straight_le hα _ _ _ _ _
            _ ≤ B + B + ENNReal.ofReal (2 * α) * (B * B) := by
                gcongr <;> [exact ih σ.1 τ.1 hstr.1; exact ih σ.2 τ.2 hstr.2;
                  exact ih σ.1 τ.1 hstr.1; exact ih σ.2 τ.2 hstr.2]
        · calc PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n))
                (prodPMF (muM P τ.1 n) (muM P τ.2 n)) (SquareRel (fullSim R₀ n))
              ≤ PhiM α P R₀ σ.1 τ.2 n + PhiM α P R₀ σ.2 τ.1 n
                  + ENNReal.ofReal (2 * α)
                    * (PhiM α P R₀ σ.1 τ.2 n * PhiM α P R₀ σ.2 τ.1 n) :=
                PhiD_square_crossed_le hα _ _ _ _ _
            _ ≤ B + B + ENNReal.ofReal (2 * α) * (B * B) := by
                gcongr <;> [exact ih σ.1 τ.2 hcr.1; exact ih σ.2 τ.1 hcr.2;
                  exact ih σ.1 τ.2 hcr.1; exact ih σ.2 τ.1 hcr.2]
      calc PhiM α P R₀ s t (n + 1)
          ≤ etaD α P R₀ s t + (Γ₂ + betaD P R₀ s t * Γ₁)
              + ENNReal.ofReal (2 * α) * (etaD α P R₀ s t * (Γ₂ + Γ₁)) :=
            PhiM_succ_le_two P R₀ hα hst n Γ₂ Γ₁ hΓ₂h hΓ₁h
        _ ≤ ε + (Γ₂ + β * Γ₁) + ENNReal.ofReal (2 * α) * (ε * (Γ₂ + Γ₁)) := by
            gcongr <;> [exact hEta s t hst; exact hBeta s t hst; exact hEta s t hst]
        _ ≤ B := hclose

/-- **The closed failure bound at height `n`**: budgets and one closure
inequality give `ℙ(no match) ≤ η_ι + B`, unconditionally. -/
theorem markovMatching_failure_le_closed {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (ε β B : ℝ≥0∞)
    (hEta : ∀ s t, R₀ s t → etaD α P R₀ s t ≤ ε)
    (hBeta : ∀ s t, R₀ s t → betaD P R₀ s t ≤ β)
    (hclose : ε
        + ((ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
            + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * B ^ 2)
          + β * (B + B + ENNReal.ofReal (2 * α) * (B * B)))
        + ENNReal.ofReal (2 * α) * (ε
            * ((ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B
                + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * B ^ 2)
              + (B + B + ENNReal.ofReal (2 * α) * (B * B)))) ≤ B)
    (ι : PMF S) (n : ℕ) :
    ∑' x, (ι.bind fun s => muM P s n) x
        * qE (ι.bind fun t => muM P t n) (fullSim R₀ n) x
      ≤ (∑' s, ι s * qE ι R₀ s) + B :=
  markovMatching_failure_le P R₀ hα ι n B
    (PhiM_le_of_invariant_closed P R₀ hα hδ hL0 hL hK0 hK hsymm ε β B hEta hBeta hclose n)

end GraphMarkovMatching
