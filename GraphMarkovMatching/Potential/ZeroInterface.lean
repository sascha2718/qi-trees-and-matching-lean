/-
The zero-interface estimates (`arbitrary_offspring_matching.tex`,
Lemma `thm:zero-interface`): the
one-site facts that bound far-label events of the varying-offspring block
recursion at `O(η)`, in tilted (inverse-moment) form.

With `η = Φ_α(μ → μ; R_v)` the one-site graph potential and `v0` the
distinguished label with `μ(v0) ≥ 1/2`:

* `phiE_eq_qE_mul_rpow`: the identity `φ_α(q(v)) = q(v)·r(v)^{-α}` in the
  safe convention: the potential summand is exactly the `r^{-α}`-tilted
  bad mass;
* `qE_zero_le`: the far tail `μ{v : ¬ v0 ∼ v} ≤ 2η`;
* `far_tilt_le`: the far-restricted inverse moment
  `∑_{v far} μ(v) r(v)^{-α} ≤ 2η`;
* `tilt_le_pow_add`: the inverse moment `∑_v μ(v) r(v)^{-α} ≤ 2^α + 2η`;
* `exceptional_pair_le`: the pair version: the `r^{-α} ⊗ r^{-α}`-tilted
  mass of `{some coordinate far}` is at most `2·(2η)·(2^α + 2η)`.

These estimates make the per-level exceptional charges of the block
recursion linear in `η`, uniformly over frozen cells.
-/
import GraphMarkovMatching.Process.Contraction

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-! ### Helpers -/

lemma rpow_neg_antitone {a b : ℝ≥0∞} {β : ℝ} (hβ : 0 ≤ β) (hab : a ≤ b) :
    b ^ (-β) ≤ a ^ (-β) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv' (ENNReal.rpow_le_rpow hab hβ)

lemma two_mul_inv_two : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-! ### The tilted summand identity -/

/-- In the safe convention the potential summand is exactly the
`r^{-α}`-tilted bad mass: `φ_α(q(v)) = q(v) · r(v)^{-α}`. -/
lemma phiE_eq_qE_mul_rpow (hα : 0 < α) (v : V) :
    phiE α (q μ Rv v) = qE μ Rv v * (rE μ Rv v) ^ (-α) := by
  by_cases hq : q μ Rv v < 1
  · have hr0 : (0 : ℝ) < 1 - q μ Rv v := by linarith
    have hrE : rE μ Rv v = ENNReal.ofReal (1 - q μ Rv v) := by
      have h1 := toReal_rE_add_toReal_qE μ Rv v
      rw [show (1 : ℝ) - q μ Rv v = (rE μ Rv v).toReal from by rw [q]; linarith,
        ENNReal.ofReal_toReal rE_ne_top]
    have hqE : qE μ Rv v = ENNReal.ofReal (q μ Rv v) := by
      rw [q, ENNReal.ofReal_toReal qE_ne_top]
    rw [phiE_of_lt hq, phi, hrE, hqE, ENNReal.rpow_neg,
      ENNReal.ofReal_rpow_of_pos hr0,
      ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hr0 α), div_eq_mul_inv]
  · have hq1 : q μ Rv v = 1 := le_antisymm q_le_one (not_lt.mp hq)
    have hqE1 : qE μ Rv v = 1 := by
      rw [← ENNReal.ofReal_toReal qE_ne_top, ← q, hq1, ENNReal.ofReal_one]
    have hrE0 : rE μ Rv v = 0 := by
      have h1 := rE_add_qE μ Rv v
      rw [hqE1] at h1
      calc rE μ Rv v = rE μ Rv v + 1 - 1 :=
            (ENNReal.add_sub_cancel_right ENNReal.one_ne_top).symm
        _ = 1 - 1 := by rw [h1]
        _ = 0 := tsub_self 1
    rw [hq1, phiE_one, hqE1, hrE0, one_mul,
      ENNReal.zero_rpow_of_neg (by linarith)]

/-! ### The far tail -/

/-- The far tail: `μ{v : ¬ v0 ∼ v} ≤ 2η` when `μ(v0) ≥ 1/2`. -/
lemma qE_zero_le (hα : 0 ≤ α) (hhalf : 2⁻¹ ≤ μ v0) :
    qE μ Rv v0 ≤ 2 * etaG α Rv μ := by
  have h2 : ENNReal.ofReal (q μ Rv v0) = qE μ Rv v0 := by
    rw [q, ENNReal.ofReal_toReal qE_ne_top]
  have h1 : μ v0 * qE μ Rv v0 ≤ etaG α Rv μ := by
    calc μ v0 * qE μ Rv v0
        = μ v0 * ENNReal.ofReal (q μ Rv v0) := by rw [h2]
      _ ≤ μ v0 * phiE α (q μ Rv v0) :=
          mul_le_mul_right (ofReal_le_phiE hα q_nonneg q_le_one) _
      _ ≤ etaG α Rv μ := by
          rw [etaG, PhiD]
          exact ENNReal.le_tsum v0
  calc qE μ Rv v0 = 2 * 2⁻¹ * qE μ Rv v0 := by rw [two_mul_inv_two, one_mul]
    _ = 2 * (2⁻¹ * qE μ Rv v0) := by rw [mul_assoc]
    _ ≤ 2 * (μ v0 * qE μ Rv v0) :=
        mul_le_mul_right (mul_le_mul_left hhalf _) _
    _ ≤ 2 * etaG α Rv μ := mul_le_mul_right h1 _

/-! ### The inverse moments -/

/-- Pointwise far bound: at a far label the tilted mass is dominated by
twice the potential summand. -/
lemma far_summand_le (hα : 0 < α) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0) {v : V} (hfar : ¬ Rv v0 v) :
    μ v * (rE μ Rv v) ^ (-α) ≤ 2 * (μ v * phiE α (q μ Rv v)) := by
  have hqv : 2⁻¹ ≤ qE μ Rv v := by
    refine le_trans hhalf ?_
    calc μ v0 = if Rv v v0 then 0 else μ v0 := by
          rw [if_neg (fun hc => hfar (hsymm _ _ hc))]
      _ ≤ ∑' y, if Rv v y then 0 else μ y := ENNReal.le_tsum v0
  calc μ v * (rE μ Rv v) ^ (-α)
      = μ v * (1 * (rE μ Rv v) ^ (-α)) := by rw [one_mul]
    _ ≤ μ v * (2 * qE μ Rv v * (rE μ Rv v) ^ (-α)) := by
        refine mul_le_mul_right (mul_le_mul_left ?_ _) _
        calc (1 : ℝ≥0∞) = 2 * 2⁻¹ := two_mul_inv_two.symm
          _ ≤ 2 * qE μ Rv v := mul_le_mul_right hqv _
    _ = 2 * (μ v * (qE μ Rv v * (rE μ Rv v) ^ (-α))) := by ring
    _ = 2 * (μ v * phiE α (q μ Rv v)) := by
        rw [phiE_eq_qE_mul_rpow α Rv μ hα v]

/-- The far-restricted inverse moment: `∑_{v far} μ(v) r(v)^{-α} ≤ 2η`. -/
lemma far_tilt_le (hα : 0 < α) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0) :
    (∑' v, if Rv v0 v then 0 else μ v * (rE μ Rv v) ^ (-α))
      ≤ 2 * etaG α Rv μ := by
  calc (∑' v, if Rv v0 v then 0 else μ v * (rE μ Rv v) ^ (-α))
      ≤ ∑' v, 2 * (μ v * phiE α (q μ Rv v)) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        by_cases hv : Rv v0 v
        · rw [if_pos hv]
          exact zero_le
        · rw [if_neg hv]
          exact far_summand_le α Rv μ v0 hα hsymm hhalf hv
    _ = 2 * etaG α Rv μ := by rw [ENNReal.tsum_mul_left, etaG, PhiD]

/-- The inverse moment: `∑_v μ(v) r(v)^{-α} ≤ 2^α + 2η`. -/
lemma tilt_le_pow_add (hα : 0 < α) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0) :
    (∑' v, μ v * (rE μ Rv v) ^ (-α)) ≤ (2 : ℝ≥0∞) ^ α + 2 * etaG α Rv μ := by
  have hnear : ∀ v, Rv v0 v → μ v * (rE μ Rv v) ^ (-α) ≤ μ v * 2 ^ α := by
    intro v hv
    refine mul_le_mul_right ?_ _
    have hr : 2⁻¹ ≤ rE μ Rv v := by
      refine le_trans hhalf ?_
      calc μ v0 = if Rv v v0 then μ v0 else 0 := by rw [if_pos (hsymm _ _ hv)]
        _ ≤ ∑' y, if Rv v y then μ y else 0 := ENNReal.le_tsum v0
    calc (rE μ Rv v) ^ (-α) ≤ ((2 : ℝ≥0∞)⁻¹) ^ (-α) :=
          rpow_neg_antitone (le_of_lt hα) hr
      _ = (2 : ℝ≥0∞) ^ α := by
          rw [ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]
  calc (∑' v, μ v * (rE μ Rv v) ^ (-α))
      ≤ ∑' v, (μ v * 2 ^ α
          + (if Rv v0 v then 0 else μ v * (rE μ Rv v) ^ (-α))) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        by_cases hv : Rv v0 v
        · rw [if_pos hv]
          rw [add_zero]
          exact hnear v hv
        · rw [if_neg hv]
          exact le_add_self
    _ = (∑' v, μ v * 2 ^ α)
          + ∑' v, (if Rv v0 v then 0 else μ v * (rE μ Rv v) ^ (-α)) :=
        ENNReal.tsum_add
    _ ≤ (2 : ℝ≥0∞) ^ α + 2 * etaG α Rv μ := by
        refine add_le_add ?_ (far_tilt_le α Rv μ v0 hα hsymm hhalf)
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ### The pair version -/

/-- **The exceptional pair bound**: the `r^{-α} ⊗ r^{-α}`-tilted mass of
pairs with some far coordinate is at most `2·(2η)·(2^α + 2η)`. -/
lemma exceptional_pair_le (hα : 0 < α) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0) :
    (∑' p : V × V, if ¬ Rv v0 p.1 ∨ ¬ Rv v0 p.2 then
        (μ p.1 * (rE μ Rv p.1) ^ (-α)) * (μ p.2 * (rE μ Rv p.2) ^ (-α)) else 0)
      ≤ 2 * ((2 * etaG α Rv μ) * ((2 : ℝ≥0∞) ^ α + 2 * etaG α Rv μ)) := by
  set f : V → ℝ≥0∞ := fun v => μ v * (rE μ Rv v) ^ (-α) with hf
  set g : V → ℝ≥0∞ := fun v => if Rv v0 v then 0 else μ v * (rE μ Rv v) ^ (-α)
    with hg
  have hsplit : ∀ p : V × V,
      (if ¬ Rv v0 p.1 ∨ ¬ Rv v0 p.2 then f p.1 * f p.2 else 0)
        ≤ g p.1 * f p.2 + f p.1 * g p.2 := by
    intro p
    by_cases h1 : Rv v0 p.1 <;> by_cases h2 : Rv v0 p.2
    · rw [if_neg (by tauto)]
      exact zero_le
    · rw [if_pos (by tauto), hg]
      simp only [if_neg h2]
      exact le_add_self
    · rw [if_pos (by tauto), hg]
      simp only [if_neg h1]
      exact le_self_add
    · rw [if_pos (by tauto), hg]
      simp only [if_neg h1]
      exact le_self_add
  calc (∑' p : V × V, if ¬ Rv v0 p.1 ∨ ¬ Rv v0 p.2 then f p.1 * f p.2 else 0)
      ≤ ∑' p : V × V, (g p.1 * f p.2 + f p.1 * g p.2) :=
        ENNReal.tsum_le_tsum hsplit
    _ = (∑' v, g v) * (∑' v, f v) + (∑' v, f v) * (∑' v, g v) := by
        rw [ENNReal.tsum_add, tsum_prod_split g f, tsum_prod_split f g]
    _ = 2 * ((∑' v, g v) * (∑' v, f v)) := by ring
    _ ≤ 2 * ((2 * etaG α Rv μ) * ((2 : ℝ≥0∞) ^ α + 2 * etaG α Rv μ)) := by
        refine mul_le_mul_right (mul_le_mul' ?_ ?_) _
        · exact far_tilt_le α Rv μ v0 hα hsymm hhalf
        · exact tilt_le_pow_add α Rv μ v0 hα hsymm hhalf

end GraphMarkovMatching
