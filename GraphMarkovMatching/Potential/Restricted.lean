/-
Directed potentials restricted to positive degree, their inverse moments and overlap identities.
-/
import GraphMarkovMatching.Support.Pairing

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

noncomputable def PhiDres (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, ρs x * (if rE ρt R x = 0 then 0 else phiE α (q ρt R x))

noncomputable def zMass (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' y, ρs y * (if rE ρt R y = 0 then 1 else 0)

noncomputable def failureD (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, ρs x * qE ρt R x

lemma failureD_le_PhiDres_add_zMass (α : ℝ) (hα0 : 0 ≤ α)
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

noncomputable def WresD (α : ℝ) (ρt : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  if rE ρt R x = 0 then 0 else WnnD α ρt R x

noncomputable def HresD (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, ρs x * (if ¬ R x y then WresD α ρt R x else 0)

noncomputable def KresD (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, ρs x * (if ¬ R x y then
    (if rE ρt R x = 0 then 0 else phiE α (q ρt R x)) else 0)

lemma q_lt_one_of_rE_ne_zero {ρ : PMF X} {R : X → X → Prop} {x : X}
    (h : rE ρ R x ≠ 0) : q ρ R x < 1 := by
  have hq1 : qE ρ R x ≠ 1 := by
    intro h1
    apply h
    have hr : rE ρ R x = 1 - qE ρ R x :=
      ENNReal.eq_sub_of_add_eq qE_ne_top (rE_add_qE ρ R x)
    rw [hr, h1, tsub_self]
  have hlt : qE ρ R x < 1 := lt_of_le_of_ne qE_le_one hq1
  have := (ENNReal.toReal_lt_toReal qE_ne_top ENNReal.one_ne_top).mpr hlt
  rwa [ENNReal.toReal_one] at this

lemma fubini_swap_two_gen (μ₀ μ₁ ν : PMF X) (R : X → X → Prop)
    (G₀ G₁ : X → ℝ≥0∞) :
    ∑' p : X × X, μ₀ p.1 * μ₁ p.2
        * (cOverlap ν R p.1 p.2 * (G₀ p.1 * G₁ p.2))
      = ∑' y, ν y * ((∑' x, μ₀ x * (if ¬ R x y then G₀ x else 0))
          * ∑' x, μ₁ x * (if ¬ R x y then G₁ x else 0)) := by
  have hstep : ∀ p : X × X,
      μ₀ p.1 * μ₁ p.2 * (cOverlap ν R p.1 p.2 * (G₀ p.1 * G₁ p.2))
        = ∑' y, μ₀ p.1 * μ₁ p.2 * (G₀ p.1 * G₁ p.2)
            * (if ¬ R p.1 y ∧ ¬ R p.2 y then ν y else 0) := by
    intro p; rw [cOverlap, ENNReal.tsum_mul_left]; ring
  simp_rw [hstep]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun y => ?_
  rw [tsum_congr fun p : X × X => show
      μ₀ p.1 * μ₁ p.2 * (G₀ p.1 * G₁ p.2)
          * (if ¬ R p.1 y ∧ ¬ R p.2 y then ν y else 0)
        = ν y * ((μ₀ p.1 * (if ¬ R p.1 y then G₀ p.1 else 0))
                 * (μ₁ p.2 * (if ¬ R p.2 y then G₁ p.2 else 0)))
      from by by_cases h1 : R p.1 y <;> by_cases h2 : R p.2 y <;>
        simp [h1, h2]; ring]
  rw [ENNReal.tsum_mul_left, tsum_prod_split
        (fun x => μ₀ x * (if ¬ R x y then G₀ x else 0))
        (fun x => μ₁ x * (if ¬ R x y then G₁ x else 0))]

lemma fubini_swap_two_res (α : ℝ) (μ₀ μ₁ νc ν₀ ν₁ : PMF X)
    (R : X → X → Prop) :
    ∑' p : X × X, μ₀ p.1 * μ₁ p.2
        * (cOverlap νc R p.1 p.2 * (WresD α ν₀ R p.1 * WresD α ν₁ R p.2))
      = ∑' y, νc y * (HresD α μ₀ ν₀ R y * HresD α μ₁ ν₁ R y) :=
  fubini_swap_two_gen μ₀ μ₁ νc R (WresD α ν₀ R) (WresD α ν₁ R)

lemma HresD_le {α : ℝ} (hα : 1 ≤ α) (ρs ρt : PMF X) (R : X → X → Prop)
    (hsymm : ∀ a b, R a b → R b a) (y : X) :
    HresD α ρs ρt R y ≤ qE ρs R y + ENNReal.ofReal α * KresD α ρs ρt R y := by
  have hbr : ∀ x, ρs x * (if ¬ R x y then WresD α ρt R x else 0)
      ≤ (if ¬ R x y then ρs x else 0)
        + ENNReal.ofReal α * (ρs x * (if ¬ R x y then
            (if rE ρt R x = 0 then 0 else phiE α (q ρt R x)) else 0)) := by
    intro x
    by_cases h : R x y
    · simp [h]
    · simp only [if_pos h]
      by_cases hres : rE ρt R x = 0
      · rw [WresD, if_pos hres, mul_zero, if_pos hres, mul_zero, mul_zero]
        exact zero_le
      · rw [WresD, if_neg hres, if_neg hres]
        calc ρs x * WnnD α ρt R x
            ≤ ρs x * (1 + ENNReal.ofReal α * phiE α (q ρt R x)) := by
              gcongr
              exact WnnD_le hα ρt R x
          _ = ρs x + ENNReal.ofReal α * (ρs x * phiE α (q ρt R x)) := by ring
  have hqe : (∑' x, if ¬ R x y then ρs x else 0) = qE ρs R y := by
    rw [← tsum_not_rel_eq_qE hsymm]
    exact tsum_congr fun x => by by_cases h : R x y <;> simp [h]
  calc HresD α ρs ρt R y
      ≤ ∑' x, ((if ¬ R x y then ρs x else 0)
          + ENNReal.ofReal α * (ρs x * (if ¬ R x y then
              (if rE ρt R x = 0 then 0 else phiE α (q ρt R x)) else 0))) :=
        ENNReal.tsum_le_tsum hbr
    _ = qE ρs R y + ENNReal.ofReal α * KresD α ρs ρt R y := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hqe, KresD]

lemma KresD_le_PhiDres (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X) :
    KresD α ρs ρt R y ≤ PhiDres α ρs ρt R := by
  rw [KresD, PhiDres]
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  by_cases h : R x y <;> simp [h]

lemma rpow_neg_le_one_add_phiE {α : ℝ} (hα : 1 ≤ α) {t : ℝ≥0∞}
    (ht0 : t ≠ 0) (ht1 : t ≤ 1) :
    t ^ (-α) ≤ 1 + ENNReal.ofReal α * phiE α (1 - t.toReal) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have htop : t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ht1
  have htpos : 0 < t.toReal := ENNReal.toReal_pos ht0 htop
  have htle : t.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top ht1
  set s : ℝ := 1 - t.toReal with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hs1 : s < 1 := by rw [hs]; linarith
  have hts : t = ENNReal.ofReal (1 - s) := by
    rw [show (1 : ℝ) - s = t.toReal from by rw [hs]; ring]
    exact (ENNReal.ofReal_toReal htop).symm
  have hφ : 0 ≤ phi α s := phi_nonneg hs0 hs1
  rw [hts, ENNReal.ofReal_rpow_of_pos (by linarith : (0 : ℝ) < 1 - s),
    phiE_of_lt hs1]
  calc ENNReal.ofReal ((1 - s) ^ (-α))
      ≤ ENNReal.ofReal (1 + α * phi α s) :=
        ENNReal.ofReal_le_ofReal (rpow_neg_alpha_le hα hs1)
    _ = 1 + ENNReal.ofReal α * ENNReal.ofReal (phi α s) := by
        rw [ENNReal.ofReal_add (by norm_num) (mul_nonneg hα0 hφ),
            ENNReal.ofReal_mul hα0, ENNReal.ofReal_one]

lemma tsum_wres_le {α : ℝ} (hα : 1 ≤ α) (ρ : PMF X)
    (r : X → ℝ≥0∞) (hr : ∀ x, r x ≤ 1) :
    ∑' x, ρ x * (if r x = 0 then 0 else (r x) ^ (-α))
      ≤ 1 + ENNReal.ofReal α
          * ∑' x, ρ x * (if r x = 0 then 0 else phiE α (1 - (r x).toReal)) := by
  have hpt : ∀ x, ρ x * (if r x = 0 then 0 else (r x) ^ (-α))
      ≤ ρ x + ENNReal.ofReal α
          * (ρ x * (if r x = 0 then 0 else phiE α (1 - (r x).toReal))) := by
    intro x
    by_cases h : r x = 0
    · simp [h]
    · rw [if_neg h, if_neg h]
      calc ρ x * (r x) ^ (-α)
          ≤ ρ x * (1 + ENNReal.ofReal α * phiE α (1 - (r x).toReal)) :=
            mul_le_mul_right (rpow_neg_le_one_add_phiE hα h (hr x)) _
        _ = ρ x + ENNReal.ofReal α * (ρ x * phiE α (1 - (r x).toReal)) := by
            ring
  calc ∑' x, ρ x * (if r x = 0 then 0 else (r x) ^ (-α))
      ≤ ∑' x, (ρ x + ENNReal.ofReal α
          * (ρ x * (if r x = 0 then 0 else phiE α (1 - (r x).toReal)))) :=
        ENNReal.tsum_le_tsum hpt
    _ = 1 + ENNReal.ofReal α
          * ∑' x, ρ x * (if r x = 0 then 0 else phiE α (1 - (r x).toReal)) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, PMF.tsum_coe]

lemma tsum_wres_restrict_le {α : ℝ} (hα : 1 ≤ α) (ρ : PMF X)
    (r : X → ℝ≥0∞) (hr : ∀ x, r x ≤ 1) (H : Set X) :
    ∑' x, ρ x * (if x ∈ H then (if r x = 0 then 0 else (r x) ^ (-α)) else 0)
      ≤ (∑' x, ρ x * (if x ∈ H then 1 else 0))
        + ENNReal.ofReal α
          * ∑' x, ρ x * (if x ∈ H then
              (if r x = 0 then 0 else phiE α (1 - (r x).toReal)) else 0) := by
  have hpt : ∀ x,
      ρ x * (if x ∈ H then (if r x = 0 then 0 else (r x) ^ (-α)) else 0)
      ≤ ρ x * (if x ∈ H then 1 else 0)
        + ENNReal.ofReal α
          * (ρ x * (if x ∈ H then
              (if r x = 0 then 0 else phiE α (1 - (r x).toReal)) else 0)) := by
    intro x
    by_cases hH : x ∈ H
    · rw [if_pos hH, if_pos hH, if_pos hH, mul_one]
      by_cases h : r x = 0
      · simp [h]
      · rw [if_neg h, if_neg h]
        calc ρ x * (r x) ^ (-α)
            ≤ ρ x * (1 + ENNReal.ofReal α * phiE α (1 - (r x).toReal)) :=
              mul_le_mul_right (rpow_neg_le_one_add_phiE hα h (hr x)) _
          _ = ρ x + ENNReal.ofReal α * (ρ x * phiE α (1 - (r x).toReal)) := by
              ring
    · simp [hH]
  calc ∑' x, ρ x * (if x ∈ H then (if r x = 0 then 0 else (r x) ^ (-α)) else 0)
      ≤ ∑' x, (ρ x * (if x ∈ H then 1 else 0)
          + ENNReal.ofReal α
            * (ρ x * (if x ∈ H then
                (if r x = 0 then 0 else phiE α (1 - (r x).toReal)) else 0))) :=
        ENNReal.tsum_le_tsum hpt
    _ = (∑' x, ρ x * (if x ∈ H then 1 else 0))
        + ENNReal.ofReal α
          * ∑' x, ρ x * (if x ∈ H then
              (if r x = 0 then 0 else phiE α (1 - (r x).toReal)) else 0) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]

lemma PhiDres_bind_left {A X : Type u} (α : ℝ) (w : PMF A) (f : A → PMF X)
    (ρt : PMF X) (R : X → X → Prop) :
    PhiDres α (w.bind f) ρt R = ∑' a, w a * PhiDres α (f a) ρt R := by
  rw [PhiDres, tsum_bind_mul]
  exact tsum_congr fun a => by rw [PhiDres]

section
variable {X : Type}

lemma rE_rpow_neg_eq_WresD {α : ℝ} (ρt : PMF X) (R : X → X → Prop) (x : X)
    (h : rE ρt R x ≠ 0) : (rE ρt R x) ^ (-α) = WresD α ρt R x := by
  rw [WresD, if_neg h, WnnD]
  have hq : q ρt R x < 1 := q_lt_one_of_rE_ne_zero h
  have h1 : rE ρt R x = ENNReal.ofReal (1 - q ρt R x) := by
    rw [← toReal_rE_eq ρt R x, ENNReal.ofReal_toReal rE_ne_top]
  rw [h1, ← ENNReal.ofReal_rpow_of_pos (by linarith)]

lemma tsum_WresD_le {α : ℝ} (hα : 1 ≤ α) (ρs ρt : PMF X) (R : X → X → Prop) :
    ∑' x, ρs x * WresD α ρt R x
      ≤ 1 + ENNReal.ofReal α * PhiDres α ρs ρt R := by
  have hW : ∀ x, WresD α ρt R x
      = (if rE ρt R x = 0 then 0 else (rE ρt R x) ^ (-α)) := by
    intro x
    by_cases h : rE ρt R x = 0
    · rw [WresD, if_pos h, if_pos h]
    · rw [if_neg h, rE_rpow_neg_eq_WresD ρt R x h]
  have hq : ∀ x, (if rE ρt R x = 0 then (0 : ℝ≥0∞)
        else phiE α (1 - (rE ρt R x).toReal))
      = (if rE ρt R x = 0 then 0 else phiE α (q ρt R x)) := by
    intro x
    by_cases h : rE ρt R x = 0
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h,
        show (1 : ℝ) - (rE ρt R x).toReal = q ρt R x from by
          rw [toReal_rE_eq]; ring]
  calc ∑' x, ρs x * WresD α ρt R x
      = ∑' x, ρs x * (if rE ρt R x = 0 then 0 else (rE ρt R x) ^ (-α)) :=
        tsum_congr fun x => by rw [hW]
    _ ≤ 1 + ENNReal.ofReal α * ∑' x, ρs x
          * (if rE ρt R x = 0 then 0 else phiE α (1 - (rE ρt R x).toReal)) :=
        tsum_wres_le hα ρs (rE ρt R) fun x => rE_le_one
    _ = 1 + ENNReal.ofReal α * PhiDres α ρs ρt R := by
        have hsum : (∑' x, ρs x * (if rE ρt R x = 0 then 0
              else phiE α (1 - (rE ρt R x).toReal)))
            = PhiDres α ρs ρt R := by
          rw [PhiDres]
          exact tsum_congr fun x => by rw [hq]
        rw [hsum]

lemma WresD_square_le_sum {α : ℝ} (hα0 : 0 ≤ α) (ρe ρf : PMF X)
    (R : X → X → Prop) (xp : X × X) :
    WresD α (prodPMF ρe ρf) (SquareRel R) xp
      ≤ WresD α ρe R xp.1 * WresD α ρf R xp.2
        + WresD α ρf R xp.1 * WresD α ρe R xp.2 := by
  obtain ⟨x₀, x₁⟩ := xp
  by_cases halive : rE (prodPMF ρe ρf) (SquareRel R) (x₀, x₁) = 0
  · rw [WresD, if_pos halive]
    exact zero_le
  · have hnb : ¬ (rE ρe R x₀ * rE ρf R x₁ = 0
        ∧ rE ρe R x₁ * rE ρf R x₀ = 0) := fun hc =>
      halive ((rE_square_eq_zero_iff ρe ρf R x₀ x₁).mpr hc)
    rw [← rE_rpow_neg_eq_WresD (prodPMF ρe ρf) (SquareRel R) (x₀, x₁) halive]
    rcases not_and_or.mp hnb with hst | hcr
    · obtain ⟨he0, hf1⟩ := mul_ne_zero_iff.mp hst
      refine le_trans ?_ le_self_add
      calc (rE (prodPMF ρe ρf) (SquareRel R) (x₀, x₁)) ^ (-α)
          ≤ (rE ρe R x₀ * rE ρf R x₁) ^ (-α) :=
            rpow_neg_antitone hα0 (straight_le_rE_square ρe ρf R x₀ x₁)
        _ = (rE ρe R x₀) ^ (-α) * (rE ρf R x₁) ^ (-α) :=
            ENNReal.mul_rpow_of_ne_zero he0 hf1 (-α)
        _ = WresD α ρe R x₀ * WresD α ρf R x₁ := by
            rw [rE_rpow_neg_eq_WresD ρe R x₀ he0,
              rE_rpow_neg_eq_WresD ρf R x₁ hf1]
    · obtain ⟨he1, hf0⟩ := mul_ne_zero_iff.mp hcr
      refine le_trans ?_ le_add_self
      calc (rE (prodPMF ρe ρf) (SquareRel R) (x₀, x₁)) ^ (-α)
          ≤ (rE ρe R x₁ * rE ρf R x₀) ^ (-α) :=
            rpow_neg_antitone hα0 (crossed_le_rE_square ρe ρf R x₀ x₁)
        _ = (rE ρe R x₁) ^ (-α) * (rE ρf R x₀) ^ (-α) :=
            ENNReal.mul_rpow_of_ne_zero he1 hf0 (-α)
        _ = WresD α ρf R x₀ * WresD α ρe R x₁ := by
            rw [rE_rpow_neg_eq_WresD ρe R x₁ he1,
              rE_rpow_neg_eq_WresD ρf R x₀ hf0, mul_comm]

end

end GraphMarkovMatching
