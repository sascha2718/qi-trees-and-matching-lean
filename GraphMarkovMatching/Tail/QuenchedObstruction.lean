/-
Why the fully quenched grammar does not by itself close the screened proof.

Two targets with mode `F` but different counter environments need not
interpret to the same law.  The diagonal-pruning step used by the finite
screen grammar therefore cannot identify them merely from their common
mode.  The theorem below gives a height-one screen with positive mass:
the source fresh component has counter 2 (two fresh children), while the
target fresh component has counter 3 (one forced child).  On the event that
both source children carry a label incompatible with the forced label, the
target good degree is zero.
-/
import GraphMarkovMatching.Tail.QuenchedRows

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 vf : V)

private lemma ne_zero_of_le' {a b : ℝ≥0∞} (hb : b ≠ 0) (hba : b ≤ a) :
    a ≠ 0 := fun ha => hb (le_antisymm (ha ▸ hba) zero_le)

/-- The height-one counter-2 environment used on the source side. -/
def qObsEnv2 : FullLab ℕ 1 := branch 2 (leaf 0, leaf 0)

/-- The height-one counter-3 environment used on the target side. -/
def qObsEnv3 : FullLab ℕ 1 := branch 3 (leaf 0, leaf 0)

/-- A source tree with compatible root `v0` and two far fresh children. -/
def qObsTree : FullLab (V × ℕ) 1 :=
  branch (v0, 2) (leaf (vf, 0), leaf (vf, 0))

private lemma qInterp_F_zero_apply_ge (v : V) (n : ℕ) :
    μ v ≤ qInterp μ v0 (⟨QMode.F, leaf n⟩ : QTgt 0) (leaf (v, n)) := by
  rw [qInterp_F, quenchedFresh, PMF.bind_apply]
  calc
    μ v = μ v * (PMF.pure (leaf (v, n))) (leaf (v, n)) := by simp
    _ ≤ ∑' w, μ w * (quenchedMuM μ v0 (w, n) 0 (leaf n)) (leaf (v, n)) := by
      exact ENNReal.le_tsum v

/-- The witness tree has positive source mass whenever both labels are
charged. -/
lemma qObsTree_source_ne_zero (hμ0 : μ v0 ≠ 0) (hμf : μ vf ≠ 0) :
    qInterp μ v0 (⟨QMode.F, qObsEnv2⟩ : QTgt 1)
        (qObsTree v0 vf) ≠ 0 := by
  rw [qInterp_F_succ, PMF.bind_apply]
  have hchild : qChildren μ v0 (⟨QMode.F, qObsEnv2⟩ : QTgt 1)
      (leaf (vf, 0), leaf (vf, 0)) ≠ 0 := by
    simp only [qChildren, qObsEnv2, qchild0, qchild1, QTgt.counter_F,
      envRoot_branch, show ¬4 ≤ 2 by omega, if_false, show 2 ≠ 3 by omega,
      qInterp_F, prodPMF_apply]
    exact mul_ne_zero
      (ne_zero_of_le' hμf (qInterp_F_zero_apply_ge μ v0 vf 0))
      (ne_zero_of_le' hμf (qInterp_F_zero_apply_ge μ v0 vf 0))
  have hterm : μ v0 *
      ((qChildren μ v0 (⟨QMode.F, qObsEnv2⟩ : QTgt 1)).map
        (branch (v0, envRoot 1 qObsEnv2))) (qObsTree v0 vf) ≠ 0 := by
    refine mul_ne_zero hμ0 ?_
    have hle : qChildren μ v0 (⟨QMode.F, qObsEnv2⟩ : QTgt 1)
        (leaf (vf, 0), leaf (vf, 0))
        ≤ ((qChildren μ v0 (⟨QMode.F, qObsEnv2⟩ : QTgt 1)).map
          (branch (v0, envRoot 1 qObsEnv2))) (qObsTree v0 vf) := by
      rw [PMF.map_apply]
      exact le_trans (by
        rw [if_pos (show qObsTree v0 vf = branch (v0, envRoot 1 qObsEnv2)
            (leaf (vf, 0), leaf (vf, 0)) from rfl)])
        (ENNReal.le_tsum (leaf (vf, 0), leaf (vf, 0)))
    exact ne_zero_of_le' hchild hle
  exact ne_zero_of_le' hterm (ENNReal.le_tsum v0)

/-- The witness has zero good degree toward the counter-3 fresh component. -/
lemma qObsTree_target_degree_zero (hfar : ¬ Rv vf v0) :
    rE (qInterp μ v0 (⟨QMode.F, qObsEnv3⟩ : QTgt 1))
        (fullSim (labRel Rv) 1) (qObsTree v0 vf) = 0 := by
  rw [show qObsTree v0 vf =
      branch (v0, 2) (leaf (vf, 0), leaf (vf, 0)) from rfl,
    rE_qInterp_F_succ_branch Rv μ v0]
  apply mul_eq_zero_of_right
  change rE
    (prodPMF
      (qInterp μ v0 (⟨QMode.Z 2, leaf 0⟩ : QTgt 0))
      (qInterp μ v0 (⟨QMode.F, leaf 0⟩ : QTgt 0)))
    (SquareRel (fullSim (labRel Rv) 0))
    (leaf (vf, 0), leaf (vf, 0)) = 0
  have hz : rE (qInterp μ v0 (⟨QMode.Z 2, leaf 0⟩ : QTgt 0))
      (fullSim (labRel Rv) 0) (leaf (vf, 0)) = 0 := by
    rw [qInterp_Z, quenchedMuM_zero, rE_eq_tsum_mul,
      tsum_pure_mul, goodInd, if_neg]
    exact fun hc => hfar ((fullSim_leaf (labRel Rv) (vf, 0) (v0, 2)).mp hc)
  rw [rE_square_eq_zero_iff]
  constructor <;> rw [hz, zero_mul]

/-- **Failure of mode-level diagonal pruning.**  Both source and target
have mode `F`, yet their singleton zero screen has positive mass. -/
theorem qFresh_mode_screen_ne_zero (hμ0 : μ v0 ≠ 0) (hμf : μ vf ≠ 0)
    (hfar : ¬ Rv vf v0) :
    screenE (qInterp μ v0 (⟨QMode.F, qObsEnv2⟩ : QTgt 1))
        (fullSim (labRel Rv) 1)
        [qInterp μ v0 (⟨QMode.F, qObsEnv3⟩ : QTgt 1)] (fun _ => 1) ≠ 0 := by
  let x := qObsTree v0 vf
  have hxmass : qInterp μ v0 (⟨QMode.F, qObsEnv2⟩ : QTgt 1) x ≠ 0 :=
    qObsTree_source_ne_zero μ v0 vf hμ0 hμf
  have hxzero : rE (qInterp μ v0 (⟨QMode.F, qObsEnv3⟩ : QTgt 1))
      (fullSim (labRel Rv) 1) x = 0 :=
    qObsTree_target_degree_zero Rv μ v0 vf hfar
  have hind : screenInd (fullSim (labRel Rv) 1)
      [qInterp μ v0 (⟨QMode.F, qObsEnv3⟩ : QTgt 1)] x = 1 := by
    rw [screenInd, if_pos]
    simpa using hxzero
  have hle : qInterp μ v0 (⟨QMode.F, qObsEnv2⟩ : QTgt 1) x
      ≤ screenE (qInterp μ v0 (⟨QMode.F, qObsEnv2⟩ : QTgt 1))
        (fullSim (labRel Rv) 1)
        [qInterp μ v0 (⟨QMode.F, qObsEnv3⟩ : QTgt 1)] (fun _ => 1) := by
    rw [screenE]
    refine le_trans ?_ (ENNReal.le_tsum x)
    rw [hind, mul_one, mul_one]
  exact ne_zero_of_le' hxmass hle

end GraphMarkovMatching
