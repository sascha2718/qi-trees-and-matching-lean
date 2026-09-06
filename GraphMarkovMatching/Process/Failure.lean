/-
The restricted failure bound and the two remaining mixed base coordinates
(`arbitrary_offspring_matching.tex`, `sec:rows`):

* `tsum_qE_le_PhiDres`: the expected failure mass `𝔼_ρ[q_ρ]` of a law
  against itself under a reflexive relation is at most the restricted
  diagonal potential: reflexivity keeps every charged point on the
  positive set, where `t ≤ φ_α(t)`;
* `PhiDres_Tlaw_Zlaw_zero`: the fresh-forced base coordinate vanishes:
  a compatible root sees the forced target with zero bad degree, an
  incompatible root is removed by the restriction;
* `PhiDres_Zlaw_Tlaw_zero`: the forced-fresh base coordinate is at most
  the root potential `φ_α(q(v0))`;
* `rE_pure`, `WresD_Tlaw_zero_le`, `rE_Zlaw_zero_eq`: the height-zero
  degrees: the good degree against a point mass, the fresh tilt as the
  label tilt, and the forced target dead exactly at far roots.
-/
import GraphMarkovMatching.Process.Descent

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u

section
variable {X : Type u}

/-- **The restricted failure bound**: under a reflexive relation the
expected bad degree of a law against itself is dominated by the
restricted diagonal potential. -/
lemma tsum_qE_le_PhiDres {α : ℝ} (hα : 0 ≤ α) (ρ : PMF X) (R : X → X → Prop)
    (hrefl : ∀ x, R x x) :
    ∑' x, ρ x * qE ρ R x ≤ PhiDres α ρ ρ R := by
  rw [PhiDres]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : ρ x = 0
  · rw [hx, zero_mul]
    exact zero_le
  · have hne : rE ρ R x ≠ 0 := fun h0 =>
      hx (le_antisymm (h0 ▸ le_rE_of_refl (hrefl x)) zero_le)
    rw [if_neg hne]
    refine mul_le_mul_right ?_ _
    have hqE : qE ρ R x = ENNReal.ofReal (q ρ R x) :=
      (ENNReal.ofReal_toReal qE_ne_top).symm
    rw [hqE]
    exact ofReal_le_phiE hα q_nonneg q_le_one

end

section
variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-- The good degree against a point mass. -/
lemma rE_pure {X : Type u} (b : X) (R : X → X → Prop) (z : X) :
    rE (PMF.pure b) R z = if R z b then 1 else 0 := by
  rw [rE_eq_tsum_mul, tsum_pure_mul b (goodInd R z), goodInd]

/-- The height-zero fresh tilt is the label tilt. -/
lemma WresD_Tlaw_zero_le (ν : PMF ℕ) (v : V) (k : ℕ) :
    WresD α (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0) (leaf (v, k))
      ≤ (rE μ Rv v) ^ (-α) := by
  by_cases hres : rE (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0)
      (leaf (v, k)) = 0
  · rw [WresD, if_pos hres]
    exact zero_le
  · rw [← rE_rpow_neg_eq_WresD (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0)
      (leaf (v, k)) hres, rE_Tlaw_zero Rv μ ν v0 v k]

/-- The height-zero forced target is dead exactly at far roots. -/
lemma rE_Zlaw_zero_eq (ν : PMF ℕ) (v : V) (k j : ℕ) :
    rE (Zlaw μ ν v0 j 0) (fullSim (labRel Rv) 0) (leaf (v, k))
      = if Rv v v0 then 1 else 0 := by
  rw [show Zlaw μ ν v0 j 0 = PMF.pure (leaf (v0, j)) from rfl,
    rE_pure]
  by_cases hv : Rv v v0
  · rw [if_pos ((fullSim_leaf (labRel Rv) (v, k) (v0, j)).mpr hv),
      if_pos hv]
  · rw [if_neg (fun hc =>
      hv ((fullSim_leaf (labRel Rv) (v, k) (v0, j)).mp hc)), if_neg hv]

end

section
variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (ν : PMF ℕ)
  (v0 : V)

/-- **The fresh-forced base coordinate vanishes**: at a compatible root
the forced target has zero bad degree, and an incompatible root is
removed by the restriction. -/
lemma PhiDres_Tlaw_Zlaw_zero (j : ℕ) :
    PhiDres α (Tlaw μ ν v0 0) (Zlaw μ ν v0 j 0) (fullSim (labRel Rv) 0)
      = 0 := by
  rw [show Tlaw μ ν v0 0
      = (freshQ μ ν).bind (fun s => muM (varyK μ ν v0) s 0) from rfl,
    PhiDres_bind_left]
  refine ENNReal.tsum_eq_zero.mpr fun s => ?_
  obtain ⟨v, k⟩ := s
  show freshQ μ ν (v, k) * PhiDres α (muM (varyK μ ν v0) (v, k) 0)
      (Zlaw μ ν v0 j 0) (fullSim (labRel Rv) 0) = 0
  have hP : PhiDres α (muM (varyK μ ν v0) (v, k) 0) (Zlaw μ ν v0 j 0)
      (fullSim (labRel Rv) 0) = 0 := by
    rw [show muM (varyK μ ν v0) (v, k) 0 = PMF.pure (leaf (v, k)) from rfl,
      PhiDres, tsum_pure_mul]
    by_cases hv : Rv v v0
    · have hne : rE (Zlaw μ ν v0 j 0) (fullSim (labRel Rv) 0)
          (leaf (v, k)) ≠ 0 := by
        rw [rE_Zlaw_zero_eq Rv μ v0 ν v k j, if_pos hv]
        exact one_ne_zero
      have h1 := rE_add_qE (Zlaw μ ν v0 j 0) (fullSim (labRel Rv) 0)
        (leaf (v, k))
      rw [rE_Zlaw_zero_eq Rv μ v0 ν v k j, if_pos hv, add_comm] at h1
      have hq0 : qE (Zlaw μ ν v0 j 0) (fullSim (labRel Rv) 0)
          (leaf (v, k)) = 0 := by
        have h2 := ENNReal.eq_sub_of_add_eq ENNReal.one_ne_top h1
        rwa [tsub_self] at h2
      rw [if_neg hne, q, hq0]
      simp
    · rw [rE_Zlaw_zero_eq Rv μ v0 ν v k j, if_neg hv, if_pos rfl]
  rw [hP, mul_zero]

/-- **The forced-fresh base coordinate**: at most the root potential. -/
lemma PhiDres_Zlaw_Tlaw_zero (k : ℕ) :
    PhiDres α (Zlaw μ ν v0 k 0) (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0)
      ≤ phiE α (q μ Rv v0) := by
  rw [show Zlaw μ ν v0 k 0 = PMF.pure (leaf (v0, k)) from rfl, PhiDres,
    tsum_pure_mul]
  have hq : q (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0) (leaf (v0, k))
      = q μ Rv v0 := by
    rw [q, q, qE_Tlaw_zero Rv μ ν v0 v0 k]
  by_cases hr : rE (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0)
      (leaf (v0, k)) = 0
  · rw [if_pos hr]
    exact zero_le
  · rw [if_neg hr, hq]

end

end GraphMarkovMatching
