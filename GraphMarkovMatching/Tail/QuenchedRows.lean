/-
The ordinary restricted-potential rows for the quenched target grammar.

Conditioning on the complete counter environment turns every child law into
an honest product of two component laws.  The root split therefore has the
same form as the finite-support proof, but it contains no aggregate
`XiBar` law and hence no inverse of a countable mixture degree.
-/
import GraphMarkovMatching.Tail.QuenchedGrammar
import GraphMarkovMatching.Process.Contraction
import GraphMarkovMatching.Process.Descent

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u

/-! ### Root/child degree identities -/

/-- Good degree toward an arbitrary child-pair law with a fixed root
attached. -/
lemma rE_map_branch_law {S : Type u} (ρ : PMF (FullLab S h × FullLab S h))
    (R₀ : S → S → Prop) (s t : S) (xp : FullLab S h × FullLab S h) :
    rE (ρ.map (branch t)) (fullSim R₀ (h + 1)) (branch s xp)
      = if R₀ s t then rE ρ (SquareRel (fullSim R₀ h)) xp else 0 := by
  by_cases hst : R₀ s t
  · rw [if_pos hst, rE_map, rE_eq_tsum_mul]
    refine tsum_congr fun yp => ?_
    congr 1
    rw [goodInd, goodInd]
    by_cases hxy : SquareRel (fullSim R₀ h) xp yp
    · rw [if_pos ((fullSim_branch R₀ h s t xp yp).mpr ⟨hst, hxy⟩), if_pos hxy]
    · rw [if_neg (fun hc => hxy ((fullSim_branch R₀ h s t xp yp).mp hc).2),
        if_neg hxy]
  · rw [if_neg hst, rE_map]
    refine ENNReal.tsum_eq_zero.mpr fun yp => ?_
    rw [goodInd,
      if_neg (fun hc => hst ((fullSim_branch R₀ h s t xp yp).mp hc).1),
      mul_zero]

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-- Raw directed failure is bounded by the restricted potential plus its
zero interface.  This is the final pointwise bridge used after averaging
the quenched environments. -/
lemma failureD_le_PhiDres_add_zMass {X : Type} (hα0 : 0 ≤ α)
    (ρs ρt : PMF X) (R : X → X → Prop) :
    failureD ρs ρt R ≤ PhiDres α ρs ρt R + zMass ρs ρt R := by
  rw [failureD, PhiDres, zMass, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hr : rE ρt R x = 0
  · simp only [hr, if_true, mul_zero, zero_add, mul_one]
    calc
      ρs x * qE ρt R x = qE ρt R x * ρs x := mul_comm _ _
      _ ≤ 1 * ρs x := mul_le_mul_left qE_le_one _
      _ = ρs x := one_mul _
  · simp only [hr, if_false]
    have hqE : qE ρt R x = ENNReal.ofReal (q ρt R x) :=
      (ENNReal.ofReal_toReal qE_ne_top).symm
    rw [hqE, mul_zero, add_zero]
    calc
      ρs x * ENNReal.ofReal (q ρt R x)
          = ENNReal.ofReal (q ρt R x) * ρs x := mul_comm _ _
      _ ≤ phiE α (q ρt R x) * ρs x :=
        mul_le_mul_left (ofReal_le_phiE hα0 q_nonneg q_le_one) _
      _ = ρs x * phiE α (q ρt R x) := mul_comm _ _

/-- Forced quenched target: the root indicator times its component child
degree. -/
lemma rE_qInterp_Z_succ_branch (v : V) (k j h : ℕ)
    (e : FullLab ℕ (h + 1))
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    rE (qInterp μ v0 (⟨QMode.Z j, e⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
      = if Rv v v0 then
          rE (qChildren μ v0 (⟨QMode.Z j, e⟩ : QTgt (h + 1)))
            (SquareRel (fullSim (labRel Rv) h)) xp
        else 0 := by
  rw [qInterp_Z_succ]
  exact rE_map_branch_law _ _ _ _ _

/-- Fresh quenched target: its only remaining mixture is the one-site root
law `μ`; the child degree is a single component product. -/
lemma rE_qInterp_F_succ_branch (v : V) (k h : ℕ)
    (e : FullLab ℕ (h + 1))
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    rE (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
      = rE μ Rv v
          * rE (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp := by
  rw [qInterp_F_succ, rE_bind]
  calc
    (∑' w, μ w * rE
      ((qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1))).map
        (branch (w, envRoot (h + 1) e)))
      (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp))
        = ∑' w, (if Rv v w then μ w else 0)
            * rE (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h)) xp := by
          refine tsum_congr fun w => ?_
          rw [rE_map_branch_law]
          by_cases hvw : Rv v w <;> simp [labRel, hvw]
    _ = (∑' w, if Rv v w then μ w else 0)
          * rE (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp := by
          rw [ENNReal.tsum_mul_right]
    _ = rE μ Rv v
          * rE (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp := rfl

/-- At a compatible forced root, the bad-degree real coordinate is exactly
the child-pair bad degree. -/
lemma q_qInterp_Z_succ_branch (hv : Rv v v0) (k j h : ℕ)
    (e : FullLab ℕ (h + 1))
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    q (qInterp μ v0 (⟨QMode.Z j, e⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
      = q (qChildren μ v0 (⟨QMode.Z j, e⟩ : QTgt (h + 1)))
          (SquareRel (fullSim (labRel Rv) h)) xp := by
  have hr := rE_qInterp_Z_succ_branch Rv μ v0 v k j h e xp
  rw [if_pos hv] at hr
  have hs := toReal_rE_eq
    (qInterp μ v0 (⟨QMode.Z j, e⟩ : QTgt (h + 1)))
    (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
  have hc := toReal_rE_eq
    (qChildren μ v0 (⟨QMode.Z j, e⟩ : QTgt (h + 1)))
    (SquareRel (fullSim (labRel Rv) h)) xp
  rw [hr] at hs
  linarith

/-- Exact root/child split of the fresh quenched bad degree. -/
lemma q_qInterp_F_succ_branch (v : V) (k h : ℕ)
    (e : FullLab ℕ (h + 1))
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    q (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
      = q μ Rv v + (1 - q μ Rv v)
          * q (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp := by
  have hr := rE_qInterp_F_succ_branch Rv μ v0 v k h e xp
  have hs := toReal_rE_eq
    (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
    (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
  have hv := toReal_rE_eq μ Rv v
  have hc := toReal_rE_eq
    (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
    (SquareRel (fullSim (labRel Rv) h)) xp
  rw [hr, ENNReal.toReal_mul, hv, hc] at hs
  nlinarith

/-- The safe potential obeys the standard root/child split componentwise. -/
lemma phiE_qInterp_F_succ_branch_le (hα : 1 ≤ α) (v : V) (k h : ℕ)
    (e : FullLab ℕ (h + 1))
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    phiE α (q (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp))
      ≤ phiE α (q μ Rv v)
        + phiE α (q (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
            (SquareRel (fullSim (labRel Rv) h)) xp)
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v)
            * phiE α (q (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h)) xp)) := by
  rw [q_qInterp_F_succ_branch Rv μ v0 v k h e xp]
  exact phiE_split hα q_nonneg q_le_one q_nonneg q_le_one

/-! ### Ordinary restricted-potential rows -/

/-- A fixed-root source row against a forced quenched target. -/
lemma PhiDres_map_branch_qInterp_Z_succ
    (ρs : PMF (FullLab (V × ℕ) h × FullLab (V × ℕ) h))
    (v : V) (k j : ℕ) (e : FullLab ℕ (h + 1)) :
    PhiDres α (ρs.map (branch (v, k)))
        (qInterp μ v0 (⟨QMode.Z j, e⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1))
      = if Rv v v0 then
          PhiDres α ρs
            (qChildren μ v0 (⟨QMode.Z j, e⟩ : QTgt (h + 1)))
            (SquareRel (fullSim (labRel Rv) h))
        else 0 := by
  rw [PhiDres, tsum_map_mul]
  by_cases hv : Rv v v0
  · rw [if_pos hv, PhiDres]
    refine tsum_congr fun xp => ?_
    congr 1
    have hr := rE_qInterp_Z_succ_branch Rv μ v0 v k j h e xp
    rw [if_pos hv] at hr
    rw [hr, q_qInterp_Z_succ_branch Rv μ v0 hv k j h e xp]
  · rw [if_neg hv]
    refine ENNReal.tsum_eq_zero.mpr fun xp => ?_
    have hr := rE_qInterp_Z_succ_branch Rv μ v0 v k j h e xp
    rw [if_neg hv] at hr
    rw [hr]
    simp

/-- A fixed-root source row against a fresh quenched target.  The child
coordinate is componentwise and carries no mixture normalization. -/
lemma PhiDres_map_branch_qInterp_F_succ (hα : 1 ≤ α)
    (ρs : PMF (FullLab (V × ℕ) h × FullLab (V × ℕ) h))
    (v : V) (k : ℕ) (e : FullLab ℕ (h + 1)) :
    PhiDres α (ρs.map (branch (v, k)))
        (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1))
      ≤ phiE α (q μ Rv v)
        + PhiDres α ρs
            (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
            (SquareRel (fullSim (labRel Rv) h))
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v)
            * PhiDres α ρs
                (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h))) := by
  rw [PhiDres, tsum_map_mul]
  have hpt : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      ρs xp * (if rE
          (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
          (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp) = 0 then 0
        else phiE α (q
          (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
          (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)))
      ≤ ρs xp * phiE α (q μ Rv v)
        + ρs xp * (if rE
            (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
            (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
          else phiE α (q
            (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
            (SquareRel (fullSim (labRel Rv) h)) xp))
        + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v)
          * (ρs xp * (if rE
              (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
            else phiE α (q
              (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp)))) := by
    intro xp
    by_cases hres : rE
        (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp) = 0
    · rw [if_pos hres, mul_zero]
      exact zero_le
    · rw [if_neg hres]
      have hfac := rE_qInterp_F_succ_branch Rv μ v0 v k h e xp
      rw [hfac] at hres
      obtain ⟨-, hchild⟩ := mul_ne_zero_iff.mp hres
      rw [if_neg hchild]
      calc
        ρs xp * phiE α (q
            (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
            (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp))
          ≤ ρs xp * (phiE α (q μ Rv v)
              + phiE α (q
                (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h)) xp)
              + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v)
                * phiE α (q
                  (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
                  (SquareRel (fullSim (labRel Rv) h)) xp))) :=
            mul_le_mul_right
              (phiE_qInterp_F_succ_branch_le α Rv μ v0 hα v k h e xp) _
        _ = ρs xp * phiE α (q μ Rv v)
              + ρs xp * phiE α (q
                (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h)) xp)
              + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v)
                * (ρs xp * phiE α (q
                  (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
                  (SquareRel (fullSim (labRel Rv) h)) xp))) := by ring
  calc
    (∑' xp, ρs xp * (if rE
          (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
          (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp) = 0 then 0
        else phiE α (q
          (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
          (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp))))
      ≤ ∑' xp, (ρs xp * phiE α (q μ Rv v)
        + ρs xp * (if rE
            (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
            (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
          else phiE α (q
            (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
            (SquareRel (fullSim (labRel Rv) h)) xp))
        + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v)
          * (ρs xp * (if rE
              (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 0
            else phiE α (q
              (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp))))) :=
        ENNReal.tsum_le_tsum hpt
    _ = phiE α (q μ Rv v)
        + PhiDres α ρs
            (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
            (SquareRel (fullSim (labRel Rv) h))
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v)
            * PhiDres α ρs
                (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h))) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
            PMF.tsum_coe, one_mul, ENNReal.tsum_mul_left,
            ENNReal.tsum_mul_left, PhiDres]

/-- Forced-to-forced quenched row: exact descent to the product children. -/
lemma PhiDres_qInterp_Z_Z_succ (hrefl : Rv v0 v0)
    (ks kt h : ℕ) (es et : FullLab ℕ (h + 1)) :
    PhiDres α (qInterp μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)))
        (qInterp μ v0 (⟨QMode.Z kt, et⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1))
      = PhiDres α
          (qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)))
          (qChildren μ v0 (⟨QMode.Z kt, et⟩ : QTgt (h + 1)))
          (SquareRel (fullSim (labRel Rv) h)) := by
  rw [qInterp_Z_succ,
    PhiDres_map_branch_qInterp_Z_succ α Rv μ v0 _ v0 ks kt et,
    if_pos hrefl]

/-- Forced-to-fresh quenched row. -/
lemma PhiDres_qInterp_Z_F_succ (hα : 1 ≤ α)
    (ks h : ℕ) (es et : FullLab ℕ (h + 1)) :
    PhiDres α (qInterp μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)))
        (qInterp μ v0 (⟨QMode.F, et⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1))
      ≤ phiE α (q μ Rv v0)
        + PhiDres α
            (qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)))
            (qChildren μ v0 (⟨QMode.F, et⟩ : QTgt (h + 1)))
            (SquareRel (fullSim (labRel Rv) h))
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v0)
            * PhiDres α
              (qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)))
              (qChildren μ v0 (⟨QMode.F, et⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h))) := by
  rw [qInterp_Z_succ]
  exact PhiDres_map_branch_qInterp_F_succ α Rv μ v0 hα _ v0 ks et

/-- Fresh-to-forced quenched row. -/
lemma PhiDres_qInterp_F_Z_succ (ks h : ℕ)
    (es et : FullLab ℕ (h + 1)) :
    PhiDres α (qInterp μ v0 (⟨QMode.F, es⟩ : QTgt (h + 1)))
        (qInterp μ v0 (⟨QMode.Z ks, et⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1))
      ≤ PhiDres α
          (qChildren μ v0 (⟨QMode.F, es⟩ : QTgt (h + 1)))
          (qChildren μ v0 (⟨QMode.Z ks, et⟩ : QTgt (h + 1)))
          (SquareRel (fullSim (labRel Rv) h)) := by
  rw [qInterp_F_succ, PhiDres_bind_left]
  let Ψ := PhiDres α
    (qChildren μ v0 (⟨QMode.F, es⟩ : QTgt (h + 1)))
    (qChildren μ v0 (⟨QMode.Z ks, et⟩ : QTgt (h + 1)))
    (SquareRel (fullSim (labRel Rv) h))
  calc
    (∑' v, μ v * PhiDres α
      ((qChildren μ v0 (⟨QMode.F, es⟩ : QTgt (h + 1))).map
        (branch (v, envRoot (h + 1) es)))
      (qInterp μ v0 (⟨QMode.Z ks, et⟩ : QTgt (h + 1)))
      (fullSim (labRel Rv) (h + 1)))
        = ∑' v, μ v * (if Rv v v0 then Ψ else 0) := by
          refine tsum_congr fun v => ?_
          rw [PhiDres_map_branch_qInterp_Z_succ α Rv μ v0 _ v
            (envRoot (h + 1) es) ks et]
    _ ≤ ∑' v, μ v * Ψ := by
          refine ENNReal.tsum_le_tsum fun v => mul_le_mul_right ?_ _
          split_ifs <;> simp
    _ = Ψ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Fresh-to-fresh quenched row.  Both child pairs remain fixed component
products while the one-site root term integrates to `etaG`. -/
lemma PhiDres_qInterp_F_F_succ (hα : 1 ≤ α)
    (h : ℕ) (es et : FullLab ℕ (h + 1)) :
    PhiDres α (qInterp μ v0 (⟨QMode.F, es⟩ : QTgt (h + 1)))
        (qInterp μ v0 (⟨QMode.F, et⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1))
      ≤ etaG α Rv μ
        + PhiDres α
            (qChildren μ v0 (⟨QMode.F, es⟩ : QTgt (h + 1)))
            (qChildren μ v0 (⟨QMode.F, et⟩ : QTgt (h + 1)))
            (SquareRel (fullSim (labRel Rv) h))
        + ENNReal.ofReal (2 * α)
          * (etaG α Rv μ
            * PhiDres α
              (qChildren μ v0 (⟨QMode.F, es⟩ : QTgt (h + 1)))
              (qChildren μ v0 (⟨QMode.F, et⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h))) := by
  rw [qInterp_F_succ, PhiDres_bind_left]
  let Ψ := PhiDres α
    (qChildren μ v0 (⟨QMode.F, es⟩ : QTgt (h + 1)))
    (qChildren μ v0 (⟨QMode.F, et⟩ : QTgt (h + 1)))
    (SquareRel (fullSim (labRel Rv) h))
  calc
    (∑' v, μ v * PhiDres α
      ((qChildren μ v0 (⟨QMode.F, es⟩ : QTgt (h + 1))).map
        (branch (v, envRoot (h + 1) es)))
      (qInterp μ v0 (⟨QMode.F, et⟩ : QTgt (h + 1)))
      (fullSim (labRel Rv) (h + 1)))
      ≤ ∑' v, μ v * (phiE α (q μ Rv v) + Ψ
        + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v) * Ψ)) := by
          refine ENNReal.tsum_le_tsum fun v => mul_le_mul_right ?_ _
          exact PhiDres_map_branch_qInterp_F_succ α Rv μ v0 hα _ v
            (envRoot (h + 1) es) et
    _ = etaG α Rv μ + Ψ
        + ENNReal.ofReal (2 * α) * (etaG α Rv μ * Ψ) := by
          rw [tsum_congr fun v => show μ v *
              (phiE α (q μ Rv v) + Ψ
                + ENNReal.ofReal (2 * α) * (phiE α (q μ Rv v) * Ψ))
              = μ v * phiE α (q μ Rv v) + μ v * Ψ
                + ENNReal.ofReal (2 * α) * ((μ v * phiE α (q μ Rv v)) * Ψ)
              from by ring,
            ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left,
            ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, PMF.tsum_coe,
            one_mul, etaG, PhiD]

end GraphMarkovMatching
