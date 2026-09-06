/-
Bridging lemmas for the screen-row compositions
(`arbitrary_offspring_matching.tex`, `sec:rows`, screen rows):

* `screenE_bind_left`: screens are linear in a mixture source;
* `screenE_pair_self`: a duplicated zero list is the singleton list;
* `screenE_one_eq_zMass`: unit-tilt singleton screens are zero masses;
* `zMass_self`: the diagonal zero mass vanishes (reflexivity keeps every
  support atom's own mass in the good degree);
* `screenE_tilt_self`: a screen whose zero list is its own tilt law
  vanishes (the restricted tilt is zero exactly on the dead event the
  screen charges).
-/
import GraphMarkovMatching.Process.Screens
import GraphMarkovMatching.Process.Ledger

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

/-- Screens are linear in a mixture source. -/
lemma screenE_bind_left {A : Type u} (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) (zs : List (PMF X)) (g : X → ℝ≥0∞) :
    screenE (w.bind f) R zs g = ∑' a, w a * screenE (f a) R zs g := by
  rw [screenE]
  rw [tsum_congr fun x => show (w.bind f) x * screenInd R zs x * g x
      = (w.bind f) x * (screenInd R zs x * g x) from mul_assoc _ _ _,
    tsum_bind_mul]
  exact tsum_congr fun a => by
    rw [screenE]
    exact congrArg _ (tsum_congr fun x => (mul_assoc _ _ _).symm)

/-- A duplicated zero list is the singleton list. -/
lemma screenE_pair_self (ρs : PMF X) (R : X → X → Prop) (ρ : PMF X)
    (g : X → ℝ≥0∞) :
    screenE ρs R [ρ, ρ] g = screenE ρs R [ρ] g := by
  rw [screenE, screenE]
  refine tsum_congr fun x => ?_
  have h : screenInd R [ρ, ρ] x = screenInd R [ρ] x := by
    simp [screenInd]
  rw [h]

/-- Unit-tilt singleton screens are zero masses. -/
lemma screenE_one_eq_zMass (ρs : PMF X) (R : X → X → Prop) (ρ : PMF X) :
    screenE ρs R [ρ] (fun _ => 1) = zMass ρs ρ R := by
  rw [screenE, zMass]
  refine tsum_congr fun x => ?_
  have h : screenInd R [ρ] x = if rE ρ R x = 0 then 1 else 0 := by
    simp [screenInd]
  rw [h, mul_one]

/-- The diagonal zero mass vanishes. -/
lemma zMass_self (ρ : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x) :
    zMass ρ ρ R = 0 := by
  rw [zMass]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : ρ x = 0
  · rw [hx, zero_mul]
  · rw [if_neg (show ¬ rE ρ R x = 0 from fun h0 =>
      hx (le_antisymm (h0 ▸ le_rE_of_refl (hrefl x)) zero_le)), mul_zero]

/-- **The root-budget linearisation**: below bad degree `1/2` the
potential weight is at most `2^α` times the bad mass.  This bounds the
`δ₀ | μ` root direction linearly in `η` through `qE_zero_le`. -/
lemma phiE_le_of_qE_le_half {α : ℝ} (hα : 0 ≤ α) (μ : PMF X)
    (R : X → X → Prop) (x : X) (hq : qE μ R x ≤ 2⁻¹) :
    phiE α (q μ R x) ≤ ENNReal.ofReal (2 ^ α) * qE μ R x := by
  have h2t : ((2⁻¹ : ℝ≥0∞)).toReal = 2⁻¹ := by simp
  have hqr : q μ R x ≤ 2⁻¹ := by
    have := ENNReal.toReal_mono (by norm_num : (2⁻¹ : ℝ≥0∞) ≠ ⊤) hq
    rwa [h2t] at this
  have hq1 : q μ R x < 1 := lt_of_le_of_lt hqr (by norm_num)
  have hq0 : (0 : ℝ) ≤ q μ R x := q_nonneg
  have hbound : phi α (q μ R x) ≤ 2 ^ α * q μ R x := by
    rw [phi, div_le_iff₀ (by positivity : (0:ℝ) < (1 - q μ R x) ^ α)]
    have h2q : (1 : ℝ) ≤ 2 * (1 - q μ R x) := by
      have : (2⁻¹ : ℝ) = 1/2 := by norm_num
      linarith [hqr.trans_eq this]
    have hpow : (1 : ℝ) ≤ (2 * (1 - q μ R x)) ^ α := by
      calc (1:ℝ) = 1 ^ α := (Real.one_rpow α).symm
        _ ≤ (2 * (1 - q μ R x)) ^ α :=
            Real.rpow_le_rpow (by norm_num) h2q hα
    have hmul : (2 : ℝ) ^ α * (1 - q μ R x) ^ α
        = (2 * (1 - q μ R x)) ^ α :=
      (Real.mul_rpow (by norm_num) (by linarith)).symm
    calc q μ R x = q μ R x * 1 := (mul_one _).symm
      _ ≤ q μ R x * (2 * (1 - q μ R x)) ^ α :=
          mul_le_mul_of_nonneg_left hpow hq0
      _ = 2 ^ α * q μ R x * (1 - q μ R x) ^ α := by
          rw [← hmul]; ring
  calc phiE α (q μ R x)
      = ENNReal.ofReal (phi α (q μ R x)) := phiE_of_lt hq1
    _ ≤ ENNReal.ofReal (2 ^ α * q μ R x) := ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (2 ^ α) * ENNReal.ofReal (q μ R x) :=
        ENNReal.ofReal_mul (by positivity)
    _ = ENNReal.ofReal (2 ^ α) * qE μ R x := by
        rw [q, ENNReal.ofReal_toReal qE_ne_top]

/-- A screen whose zero list is its own tilt law vanishes: the
restricted tilt `WresD` is zero exactly on the dead event the screen
charges. -/
lemma screenE_tilt_self (α : ℝ) (ρs : PMF X) (R : X → X → Prop)
    (ρ : PMF X) :
    screenE ρs R [ρ] (WresD α ρ R) = 0 := by
  rw [screenE]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : rE ρ R x = 0
  · rw [WresD, if_pos hx, mul_zero]
  · rw [show screenInd R [ρ] x = 0 from by
      rw [screenInd,
        if_neg (fun hall => hx (hall ρ (List.mem_singleton_self ρ)))],
      mul_zero, zero_mul]

end GraphMarkovMatching
