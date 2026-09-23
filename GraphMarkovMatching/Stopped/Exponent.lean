/-
Monotonicity in the potential exponent and admissible scalar parameters at larger exponents.
-/
import GraphMarkovMatching.Stopped.Consequences

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

lemma phiE_mono_exponent {α α' t : ℝ} (hα : α ≤ α') (ht : 0 ≤ t) : phiE α t ≤ phiE α' t := by
  by_cases h1 : t < 1
  · rw [phiE_of_lt h1, phiE_of_lt h1]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold phi
    refine div_le_div_of_nonneg_left ht (rpow_denom_pos α' h1) ?_
    exact Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) hα
  · have h : phiE α' t = ⊤ := ite_eq_right h1
    rw [h]
    exact le_top

theorem PhiD_mono_exponent {X : Type} (μ ν : PMF X) (R : X → X → Prop) {α α' : ℝ}
    (hα : α ≤ α') : PhiD α μ ν R ≤ PhiD α' μ ν R :=
  ENNReal.tsum_le_tsum fun _ => mul_le_mul_right (phiE_mono_exponent hα q_nonneg) _

theorem Model.eta_mono {V I : Type} (M : Model V I) {α α' : ℝ} (hα : α ≤ α') :
    M.eta α ≤ M.eta α' :=
  PhiD_mono_exponent M.μ M.μ M.R hα

theorem Model.eta_two_le_eta_fiveHalf {V I : Type} (M : Model V I) : M.eta 2 ≤ M.eta (5 / 2) :=
  M.eta_mono (by norm_num)

/-- Increasing the exponent decreases the nonnegative summands defining the local bound. -/
lemma Lsummand_antitone_exponent {α α' β q : ℝ} (hα : α ≤ α') (hα0 : 0 ≤ α) (hβ : 0 ≤ β)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Lsummand α' β q ≤ Lsummand α β q := by
  unfold Lsummand
  apply add_le_add
  · exact div_le_div_of_nonneg_left hq0 (Real.rpow_pos_of_pos (by linarith) α)
      (Real.rpow_le_rpow_of_exponent_le (by linarith) hα)
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge' (by linarith) (by linarith) hα0 hα) hβ

/-- Scalar contraction parameters remain admissible at every larger exponent. The
quadratic coefficient is recomputed from the new exponent. -/
noncomputable def Params.raise (p : Params) (α : ℝ) (hα : p.α ≤ α) : Params where
  α := α
  β := p.β
  u := p.u
  L := p.L
  K := p.K
  L0 := p.L0
  hα := p.hα.trans hα
  hβ0 := p.hβ0
  hβ1 := p.hβ1
  hu0 := p.hu0
  hu1 := p.hu1
  hL := fun q hq0 hq1 => (Lsummand_antitone_exponent hα p.α_nonneg p.hβ0 hq0 hq1).trans
    (p.hL q hq0 hq1)
  hK := by
    intro q hq0 hq1
    by_cases hqβ : q ≤ p.β
    · exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hqβ)
        (Real.rpow_nonneg (by linarith) _)).trans p.K_nonneg
    · exact (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge' (by linarith) (by linarith) p.α_nonneg hα)
        (sub_nonneg.mpr (le_of_not_ge hqβ))).trans (p.hK q hq0 hq1)
  hL0 := fun q hq0 hq1 => (Lsummand_antitone_exponent hα p.α_nonneg le_rfl hq0 hq1).trans
    (p.hL0 q hq0 hq1)
  ha := p.ha

/-- Parameters at exponent `5/2`, for the one-site estimates in the geometric application. -/
noncomputable def paramsFiveHalf : Params := paramsTwo.raise (5 / 2) (by norm_num [paramsTwo])

@[simp] lemma paramsFiveHalf_α : paramsFiveHalf.α = 5 / 2 := rfl

end GraphMarkovMatching.Stopped
