/-
The numeric closure of the `ν = δ₃` matching theorem
(`arbitrary_offspring_matching.tex`, the sharp `δ₃` bound of
`rem:delta3` and `rem:constants`, explicit constants): the closure inequalities of
`delta3_failure_uniform_assembled` hold at `α = 5/2`, `δ = 1/8`,
`L = 1/4`, `K = 4/27` with the explicit levels `Kc = 16384`,
`u = 16·η`, `Ξ = 320·η` whenever `2³⁰·η ≤ 1`, where `η` is the label
budget `etaG`.

* `delta3Far_le` / `delta3FarMass_le`: the far masses are at most
  `2η` (the zero-interface far tail, with the root condition swapped
  by symmetry);
* `delta3CB_le_small`: the square-cell bound at the closure levels is
  at most `(5/6)·Kc·η + 2280·η`;
* `delta3_failure_le`: **the `δ₃` matching theorem with explicit
  constants**: if `μ(v0) ≥ 1/2` and `2³⁰·η ≤ 1`, the matching failure
  at every height is at most `16384·η`.
-/
import GraphMarkovMatching.Delta3.Assembled
import GraphMarkovMatching.Potential.Numerals

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-! ### The far masses -/

/-- The tilted far mass is at most `2η`. -/
lemma delta3Far_le {α : ℝ} (hα : 0 < α)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0) :
    delta3Far α Rv μ v0 ≤ 2 * etaG α Rv μ := by
  have hswap : delta3Far α Rv μ v0
      = ∑' v, if Rv v0 v then 0 else μ v * (rE μ Rv v) ^ (-α) := by
    rw [delta3Far]
    refine tsum_congr fun v => ?_
    by_cases hv : Rv v v0
    · rw [if_pos hv, if_pos (hsymm _ _ hv)]
    · rw [if_neg hv, if_neg (fun hc => hv (hsymm _ _ hc))]
  rw [hswap]
  exact far_tilt_le α Rv μ v0 hα hsymm hhalf

/-- The untilted far mass is at most `2η`. -/
lemma delta3FarMass_le {α : ℝ} (hα : 0 ≤ α)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0) :
    delta3FarMass Rv μ v0 ≤ 2 * etaG α Rv μ := by
  have hswap : delta3FarMass Rv μ v0 = qE μ Rv v0 := by
    rw [delta3FarMass, qE]
    refine tsum_congr fun v => ?_
    by_cases hv : Rv v v0
    · rw [if_pos hv, if_pos (hsymm _ _ hv)]
    · rw [if_neg hv, if_neg (fun hc => hv (hsymm _ _ hc))]
  rw [hswap]
  exact qE_zero_le α Rv μ v0 hα hhalf

/-! ### The square-cell bound at the closure levels -/

/-- The square-cell bound at the closure levels `a = 16384·x`,
`b = 320·x`: at most `(5/6)·16384·x + 2280·x` once `2³⁰·x ≤ 1`. -/
lemma delta3CB_le_small {x : ℝ≥0∞} (hx : (2 : ℝ≥0∞) ^ (30 : ℕ) * x ≤ 1) :
    delta3CB (5 / 2) (1 / 8) (1 / 4) (4 / 27) (16384 * x) (320 * x)
      ≤ ENNReal.ofReal (5 / 6) * (16384 * x) + 2280 * x := by
  have hx' : (1073741824 : ℝ≥0∞) * x ≤ 1 := by
    rw [show (1073741824 : ℝ≥0∞) = 2 ^ (30 : ℕ) from by norm_num]
    exact hx
  have hlin : ∀ c : ℝ≥0∞, c ≤ 1073741824 → c * x ≤ 1 := fun c hc =>
    le_trans (mul_le_mul_left hc x) hx'
  have hB160 : ENNReal.ofReal
      (2 * (1 / 4) * chordConst ((5 : ℝ) / 2) + 20
        + 2 * (1 + ((1 : ℝ) / 8)⁻¹) * ((5 : ℝ) / 2) ^ 2) ≤ 160 := by
    rw [show ((160 : ℝ≥0∞)) = ENNReal.ofReal (160 : ℝ) from by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith [chordConst_five_half_le])
  have hof3 : ENNReal.ofReal ((5 : ℝ) / 2) ≤ 3 := by
    rw [show ((3 : ℝ≥0∞)) = ENNReal.ofReal (3 : ℝ) from by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have h1 : ENNReal.ofReal
        (2 * (1 / 4) + 2 * (1 + (1 : ℝ) / 8) * (4 / 27)) * (16384 * x)
      ≤ ENNReal.ofReal (5 / 6) * (16384 * x) :=
    mul_le_mul_left (ENNReal.ofReal_le_ofReal (by norm_num)) _
  have h2 : ENNReal.ofReal
        (2 * (1 / 4) * chordConst ((5 : ℝ) / 2) + 20
          + 2 * (1 + ((1 : ℝ) / 8)⁻¹) * ((5 : ℝ) / 2) ^ 2)
        * (16384 * x) ^ 2
      ≤ 40 * x := by
    calc ENNReal.ofReal
          (2 * (1 / 4) * chordConst ((5 : ℝ) / 2) + 20
            + 2 * (1 + ((1 : ℝ) / 8)⁻¹) * ((5 : ℝ) / 2) ^ 2)
          * (16384 * x) ^ 2
        ≤ 160 * (16384 * x) ^ 2 := mul_le_mul_left hB160 _
      _ = 40 * ((1073741824 * x) * x) := by ring
      _ ≤ 40 * (1 * x) :=
          mul_le_mul_right (mul_le_mul_left hx' x) 40
      _ = 40 * x := by rw [one_mul]
  have h3 : ENNReal.ofReal (2 * (1 + (1 : ℝ) / 8)) * (320 * x)
      ≤ 960 * x := by
    have hof94 : ENNReal.ofReal (2 * (1 + (1 : ℝ) / 8)) ≤ 3 := by
      rw [show ((3 : ℝ≥0∞)) = ENNReal.ofReal (3 : ℝ) from by simp]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    calc ENNReal.ofReal (2 * (1 + (1 : ℝ) / 8)) * (320 * x)
        ≤ 3 * (320 * x) := mul_le_mul_left hof94 _
      _ = 960 * x := by ring
  have hinner : ENNReal.ofReal ((5 : ℝ) / 2) * (16384 * x) ≤ 1 := by
    calc ENNReal.ofReal ((5 : ℝ) / 2) * (16384 * x)
        ≤ 3 * (16384 * x) := mul_le_mul_left hof3 _
      _ = 49152 * x := by ring
      _ ≤ 1 := hlin 49152 (by norm_num)
  have h4 : 2 * (320 * x)
        * (1 + ENNReal.ofReal ((5 : ℝ) / 2) * (16384 * x))
      ≤ 1280 * x := by
    calc 2 * (320 * x)
          * (1 + ENNReal.ofReal ((5 : ℝ) / 2) * (16384 * x))
        ≤ 2 * (320 * x) * (1 + 1) :=
          mul_le_mul_right (add_le_add le_rfl hinner) _
      _ = 1280 * x := by ring
  calc delta3CB (5 / 2) (1 / 8) (1 / 4) (4 / 27) (16384 * x) (320 * x)
      = ENNReal.ofReal
          (2 * (1 / 4) + 2 * (1 + (1 : ℝ) / 8) * (4 / 27)) * (16384 * x)
        + ENNReal.ofReal
            (2 * (1 / 4) * chordConst ((5 : ℝ) / 2) + 20
              + 2 * (1 + ((1 : ℝ) / 8)⁻¹) * ((5 : ℝ) / 2) ^ 2)
          * (16384 * x) ^ 2
        + ENNReal.ofReal (2 * (1 + (1 : ℝ) / 8)) * (320 * x)
        + 2 * (320 * x)
          * (1 + ENNReal.ofReal ((5 : ℝ) / 2) * (16384 * x)) := by
        rw [delta3CB]
    _ ≤ ENNReal.ofReal (5 / 6) * (16384 * x) + 40 * x + 960 * x
        + 1280 * x :=
        add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = ENNReal.ofReal (5 / 6) * (16384 * x) + 2280 * x := by ring

/-! ### The main theorem -/

/-- **The `δ₃` matching theorem with explicit constants**: on any
countable label graph with reflexive symmetric relation, if the root
label carries at least half the mass and the label budget satisfies
`2³⁰·η ≤ 1`, then the pure-ternary varying-offspring labellings of the
binary tree admit, at every height, a coupling with matching failure
at most `16384·η`. -/
theorem delta3_failure_le (hRv : ∀ v, Rv v v)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0)
    (hsmall : (2 : ℝ≥0∞) ^ (30 : ℕ) * etaG (5 / 2) Rv μ ≤ 1) :
    ∀ h, (∑' x, Tlaw μ (PMF.pure 3) v0 h x
        * qE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) x)
      ≤ 16384 * etaG (5 / 2) Rv μ := by
  set η := etaG (5 / 2 : ℝ) Rv μ with hηdef
  have hx' : (1073741824 : ℝ≥0∞) * η ≤ 1 := by
    rw [show (1073741824 : ℝ≥0∞) = 2 ^ (30 : ℕ) from by norm_num]
    exact hsmall
  have hlin : ∀ c : ℝ≥0∞, c ≤ 1073741824 → c * η ≤ 1 := fun c hc =>
    le_trans (mul_le_mul_left hc η) hx'
  have hquad : ∀ c : ℝ≥0∞, c ≤ 1073741824 → c * (η * η) ≤ η := by
    intro c hc
    calc c * (η * η) ≤ 1073741824 * (η * η) := mul_le_mul_left hc _
      _ = (1073741824 * η) * η := by ring
      _ ≤ 1 * η := mul_le_mul_left hx' η
      _ = η := one_mul η
  have hof3 : ENNReal.ofReal ((5 : ℝ) / 2) ≤ 3 := by
    rw [show ((3 : ℝ≥0∞)) = ENNReal.ofReal (3 : ℝ) from by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hof8 : ENNReal.ofReal ((2 : ℝ) ^ ((5 : ℝ) / 2)) ≤ 8 := by
    rw [show ((8 : ℝ≥0∞)) = ENNReal.ofReal (8 : ℝ) from by simp]
    exact ENNReal.ofReal_le_ofReal two_rpow_five_half_le_eight
  have hof5 : ENNReal.ofReal (2 * ((5 : ℝ) / 2)) ≤ 5 := by
    rw [show ((5 : ℝ≥0∞)) = ENNReal.ofReal (5 : ℝ) from by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  -- the far masses and the tilt
  have hfar : delta3Far (5 / 2) Rv μ v0 ≤ 2 * η :=
    delta3Far_le Rv μ v0 (by norm_num) hsymm hhalf
  have hfm : delta3FarMass Rv μ v0 ≤ 2 * η :=
    delta3FarMass_le Rv μ v0 (α := 5 / 2) (by norm_num) hsymm hhalf
  have htilt : delta3Tilt (5 / 2) Rv μ ≤ 9 := by
    refine le_trans (show delta3Tilt (5 / 2 : ℝ) Rv μ ≤ _ from
      tilt_le_pow_add (5 / 2) Rv μ v0 (by norm_num) hsymm hhalf) ?_
    calc (2 : ℝ≥0∞) ^ ((5 : ℝ) / 2) + 2 * η
        ≤ 8 + 1 :=
          add_le_add ennreal_two_rpow_five_half_le_eight
            (hlin 2 (by norm_num))
      _ = 9 := by norm_num
  -- the root budgets
  have hq2 : qE μ Rv v0 ≤ 2 * η := qE_zero_le (5 / 2) Rv μ v0 (by norm_num) hhalf
  have h4x : (4 : ℝ≥0∞) * η ≤ 1 := hlin 4 (by norm_num)
  have hqhalf : qE μ Rv v0 ≤ 2⁻¹ := by
    refine le_trans hq2 (ENNReal.le_inv_iff_mul_le.mpr ?_)
    calc (2 : ℝ≥0∞) * η * 2 = 4 * η := by ring
      _ ≤ 1 := h4x
  have hphi : phiE (5 / 2) (q μ Rv v0) ≤ 16 * η := by
    calc phiE (5 / 2) (q μ Rv v0)
        ≤ ENNReal.ofReal (2 ^ ((5 : ℝ) / 2)) * qE μ Rv v0 :=
          phiE_le_of_qE_le_half (by norm_num) μ Rv v0 hqhalf
      _ ≤ 8 * (2 * η) := mul_le_mul' hof8 hq2
      _ = 16 * η := by ring
  have hroot : η + phiE (5 / 2) (q μ Rv v0) ≤ 17 * η := by
    calc η + phiE (5 / 2) (q μ Rv v0) ≤ η + 16 * η :=
        add_le_add le_rfl hphi
      _ = 17 * η := by ring
  -- the square-cell bound and its crude linearization
  have hCB := delta3CB_le_small (x := η) hsmall
  have hCBcrude : delta3CB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
      (16384 * η) (320 * η) ≤ 18664 * η := by
    refine le_trans hCB ?_
    calc ENNReal.ofReal (5 / 6) * (16384 * η) + 2280 * η
        ≤ 1 * (16384 * η) + 2280 * η :=
          add_le_add
            (mul_le_mul_left (ENNReal.ofReal_le_one.mpr (by norm_num)) _)
            le_rfl
      _ = 18664 * η := by ring
  -- the ordinary closure inequality
  have hofsum : ENNReal.ofReal (5 / 6) + ENNReal.ofReal (1 / 6) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      show (5 / 6 + 1 / 6 : ℝ) = 1 from by norm_num, ENNReal.ofReal_one]
  have hsplit : (16384 : ℝ≥0∞) * η
      = ENNReal.ofReal (5 / 6) * (16384 * η)
        + ENNReal.ofReal (1 / 6) * (16384 * η) := by
    rw [← add_mul, hofsum, one_mul]
  have h2298 : (2298 : ℝ≥0∞) * η
      ≤ ENNReal.ofReal (1 / 6) * (16384 * η) := by
    have hc : (2298 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 6) * 16384 := by
      rw [show (16384 : ℝ≥0∞) = ENNReal.ofReal 16384 from by simp,
        ← ENNReal.ofReal_mul (by norm_num),
        show (2298 : ℝ≥0∞) = ENNReal.ofReal 2298 from by simp]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    calc (2298 : ℝ≥0∞) * η ≤ (ENNReal.ofReal (1 / 6) * 16384) * η :=
        mul_le_mul_left hc η
      _ = ENNReal.ofReal (1 / 6) * (16384 * η) := by rw [mul_assoc]
  have hclose : delta3F (5 / 2) Rv μ v0 (1 / 8) (1 / 4) (4 / 27)
      (16384 * η) (320 * η) ≤ 16384 * η := by
    rw [delta3F]
    have hcross : ENNReal.ofReal (2 * (5 / 2))
        * ((etaG (5 / 2) Rv μ + phiE (5 / 2) (q μ Rv v0))
          * delta3CB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
              (16384 * η) (320 * η))
        ≤ η := by
      calc ENNReal.ofReal (2 * (5 / 2))
            * ((etaG (5 / 2) Rv μ + phiE (5 / 2) (q μ Rv v0))
              * delta3CB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
                  (16384 * η) (320 * η))
          ≤ 5 * ((17 * η) * (18664 * η)) :=
            mul_le_mul' hof5 (mul_le_mul' hroot hCBcrude)
        _ = 1586440 * (η * η) := by ring
        _ ≤ η := hquad 1586440 (by norm_num)
    calc etaG (5 / 2) Rv μ + phiE (5 / 2) (q μ Rv v0)
          + delta3CB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
              (16384 * η) (320 * η)
          + ENNReal.ofReal (2 * (5 / 2))
            * ((etaG (5 / 2) Rv μ + phiE (5 / 2) (q μ Rv v0))
              * delta3CB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
                  (16384 * η) (320 * η))
        ≤ 17 * η
          + (ENNReal.ofReal (5 / 6) * (16384 * η) + 2280 * η)
          + η :=
          add_le_add (add_le_add hroot hCB) hcross
      _ = ENNReal.ofReal (5 / 6) * (16384 * η) + 2298 * η := by ring
      _ ≤ ENNReal.ofReal (5 / 6) * (16384 * η)
          + ENNReal.ofReal (1 / 6) * (16384 * η) :=
          add_le_add le_rfl h2298
      _ = 16384 * η := hsplit.symm
  -- the screen closure inequality
  have hu : delta3G (5 / 2) Rv μ v0 (1 / 8) (1 / 4) (4 / 27)
      (16384 * η) (320 * η) ≤ 16 * η := by
    rw [delta3G]
    have hg1 : delta3Far (5 / 2) Rv μ v0
        * (1 + ENNReal.ofReal (5 / 2)
            * delta3CB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
                (16384 * η) (320 * η))
        ≤ 4 * η := by
      have hfac : ENNReal.ofReal ((5 : ℝ) / 2)
          * delta3CB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
              (16384 * η) (320 * η) ≤ 1 := by
        calc ENNReal.ofReal ((5 : ℝ) / 2)
              * delta3CB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
                  (16384 * η) (320 * η)
            ≤ 3 * (18664 * η) := mul_le_mul' hof3 hCBcrude
          _ = 55992 * η := by ring
          _ ≤ 1 := hlin 55992 (by norm_num)
      calc delta3Far (5 / 2) Rv μ v0
            * (1 + ENNReal.ofReal (5 / 2)
                * delta3CB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
                    (16384 * η) (320 * η))
          ≤ (2 * η) * (1 + 1) :=
            mul_le_mul' hfar (add_le_add le_rfl hfac)
        _ = 4 * η := by ring
    have hg2 : 4 * (ENNReal.ofReal (5 / 2)
          * (delta3Tilt (5 / 2) Rv μ * ((16384 * η) * (320 * η))))
        ≤ η := by
      calc 4 * (ENNReal.ofReal (5 / 2)
            * (delta3Tilt (5 / 2) Rv μ * ((16384 * η) * (320 * η))))
          ≤ 4 * (3 * (9 * ((16384 * η) * (320 * η)))) :=
            mul_le_mul_right
              (mul_le_mul' hof3 (mul_le_mul_left htilt _)) 4
        _ = 566231040 * (η * η) := by ring
        _ ≤ η := hquad 566231040 (by norm_num)
    have hg4 : (3 : ℝ≥0∞) * (320 * η) ^ 2 ≤ η := by
      calc (3 : ℝ≥0∞) * (320 * η) ^ 2 = 307200 * (η * η) := by ring
        _ ≤ η := hquad 307200 (by norm_num)
    calc delta3Far (5 / 2) Rv μ v0
          * (1 + ENNReal.ofReal (5 / 2)
              * delta3CB (5 / 2) (1 / 8) (1 / 4) (4 / 27)
                  (16384 * η) (320 * η))
        + 4 * (ENNReal.ofReal (5 / 2)
            * (delta3Tilt (5 / 2) Rv μ * ((16384 * η) * (320 * η))))
        + 3 * (320 * η) ^ 2
        + delta3FarMass Rv μ v0
        ≤ 4 * η + η + η + 2 * η :=
          add_le_add (add_le_add (add_le_add hg1 hg2) hg4) hfm
      _ = 8 * η := by ring
      _ ≤ 16 * η := mul_le_mul_left (by norm_num) η
  -- the invariant bound
  have hXi : (16 * η) * (2 + 2 * delta3Tilt (5 / 2) Rv μ)
      ≤ 320 * η := by
    calc (16 * η) * (2 + 2 * delta3Tilt (5 / 2) Rv μ)
        ≤ (16 * η) * (2 + 2 * 9) :=
          mul_le_mul_right (add_le_add le_rfl (mul_le_mul_right htilt 2)) _
      _ = 320 * η := by ring
  -- assemble
  exact delta3_failure_uniform_assembled (5 / 2) Rv μ v0
    (δ := 1 / 8) (L := 1 / 4) (K := 4 / 27)
    (by norm_num) (by norm_num) (by norm_num) quarter_L_bound
    (by norm_num) fourTwentySeventh_K_bound hRv hsymm hhalf
    16384 η (16 * η) (320 * η) hXi
    (by calc η = 1 * η := (one_mul η).symm
      _ ≤ 16384 * η := mul_le_mul_left (by norm_num) η)
    (le_trans hphi (mul_le_mul_left (by norm_num) η))
    (mul_le_mul_left (by norm_num) η) hu hclose

end GraphMarkovMatching
