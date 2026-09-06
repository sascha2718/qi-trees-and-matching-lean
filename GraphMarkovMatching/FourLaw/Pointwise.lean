/-
The pointwise main bound of the four-law contraction: on a good pair
(all four directed degrees below one),

    φ_α(Q) ≤ (L/2)·T + (Lc_α/2 + 5)·S₀S₁ + c₀·W₀⁰W₁¹ + c₁·W₀¹W₁⁰,

where `T = S₀ + S₁`, `Sᵢ` is the `φ`-sum of row `i`, and the `W`'s are the
straight and crossed inverse-power weights. The sorted row analysis of
`FourLaw/Base.lean` is converted to per-row quantities by `sorted_bound_to_S`,
whose four sign cases encode the rearrangement facts once more at the level
of `φ`-values.
-/
import GraphMarkovMatching.FourLaw.Square

namespace GraphMarkovMatching

open GraphMarkovMatching.Support Real
open scoped ENNReal Classical

universe u
variable {X : Type u}

/-! ### Sorted-to-rows conversion -/

/-- `φ` commutes with `max` on `[0,1)`. -/
lemma phi_max {α a b : ℝ} (hα : 0 ≤ α) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha1 : a < 1) (hb1 : b < 1) :
    phi α (max a b) = max (phi α a) (phi α b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (phi_mono hα ha0 h hb1)]
  · rw [max_eq_left h, max_eq_left (phi_mono hα hb0 h ha1)]

/-- `φ` commutes with `min` on `[0,1)`. -/
lemma phi_min {α a b : ℝ} (hα : 0 ≤ α) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha1 : a < 1) (hb1 : b < 1) :
    phi α (min a b) = min (phi α a) (phi α b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (phi_mono hα ha0 h hb1)]
  · rw [min_eq_right h, min_eq_right (phi_mono hα hb0 h ha1)]

/-- The sorted row bound is dominated by the per-row form: with `A`'s the
`φ`-values of row `0` and `B`'s of row `1` (one per column),

    (L/2)(max-sum) + (Lc/2)(min-sum)(max-sum) + 4·cross + single
      ≤ (L/2)(A+B-sum) + (Lc/2+5)·(A-sum)(B-sum). -/
lemma sorted_bound_to_S {α L A0 A1 B0 B1 : ℝ}
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hL0 : 0 ≤ L) (hc : 0 ≤ chordConst α) :
    L / 2 * (max A0 B0 + max A1 B1)
      + L * chordConst α / 2 * ((min A0 B0 + min A1 B1) * (max A0 B0 + max A1 B1))
      + 4 * (max A0 B0 * min A1 B1 + max A1 B1 * min A0 B0)
      + max A0 B0 * min A1 B1
    ≤ L / 2 * ((A0 + A1) + (B0 + B1))
      + (L * chordConst α / 2 + 5) * ((A0 + A1) * (B0 + B1)) := by
  have hLc : 0 ≤ L * chordConst α / 2 := by positivity
  rcases le_total A0 B0 with h0 | h0 <;> rcases le_total A1 B1 with h1 | h1 <;>
    simp only [max_eq_right, max_eq_left, min_eq_left, min_eq_right, h0, h1] <;>
    nlinarith [mul_nonneg hA0 hB0, mul_nonneg hA0 hB1, mul_nonneg hA1 hB0,
      mul_nonneg hA1 hB1, mul_nonneg hA0 hA1, mul_nonneg hB0 hB1,
      mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1),
      mul_nonneg hLc (mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)),
      mul_nonneg hL0 hA0, mul_nonneg hL0 hA1, mul_nonneg hL0 hB0, mul_nonneg hL0 hB1]

/-! ### The pointwise main bound -/

set_option maxHeartbeats 1600000 in
/-- **The pointwise four-law bound** on a good pair. -/
lemma phi_Q_split_four {α L : ℝ} (hα1 : 1 ≤ α)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (ν₀ ν₁ : PMF X) (R : X → X → Prop) (x₀ x₁ : X)
    (h00 : q ν₀ R x₀ < 1) (h01 : q ν₁ R x₀ < 1)
    (h10 : q ν₀ R x₁ < 1) (h11 : q ν₁ R x₁ < 1) :
    phi α (q (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁))
      ≤ L / 2 * ((phi α (q ν₀ R x₀) + phi α (q ν₁ R x₀))
            + (phi α (q ν₀ R x₁) + phi α (q ν₁ R x₁)))
        + (L * chordConst α / 2 + 5)
          * ((phi α (q ν₀ R x₀) + phi α (q ν₁ R x₀))
              * (phi α (q ν₀ R x₁) + phi α (q ν₁ R x₁)))
        + (cOverlap ν₀ R x₀ x₁).toReal
          * ((1 - q ν₀ R x₀) ^ (-α) * (1 - q ν₁ R x₁) ^ (-α))
        + (cOverlap ν₁ R x₀ x₁).toReal
          * ((1 - q ν₁ R x₀) ^ (-α) * (1 - q ν₀ R x₁) ^ (-α)) := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα1
  set q00 := q ν₀ R x₀ with hq00
  set q01 := q ν₁ R x₀ with hq01
  set q10 := q ν₀ R x₁ with hq10
  set q11 := q ν₁ R x₁ with hq11
  have hq000 : 0 ≤ q00 := q_nonneg
  have hq010 : 0 ≤ q01 := q_nonneg
  have hq100 : 0 ≤ q10 := q_nonneg
  have hq110 : 0 ≤ q11 := q_nonneg
  set d0 : ℝ := max q00 q10 with hd0
  set e0 : ℝ := min q00 q10 with he0
  set d1 : ℝ := max q01 q11 with hd1
  set e1 : ℝ := min q01 q11 with he1
  have hd01 : d0 < 1 := max_lt h00 h10
  have hd11 : d1 < 1 := max_lt h01 h11
  have he00 : 0 ≤ e0 := le_min hq000 hq100
  have he10 : 0 ≤ e1 := le_min hq010 hq110
  have hed0 : e0 ≤ d0 := min_le_max
  have hed1 : e1 ≤ d1 := min_le_max
  -- real degrees and overlaps
  set Q := q (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁) with hQ
  set Rg := (rE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)).toReal with hRg
  set a0 := (aOverlap ν₀ R x₀ x₁).toReal with ha0
  set a1 := (aOverlap ν₁ R x₀ x₁).toReal with ha1
  set c0 := (cOverlap ν₀ R x₀ x₁).toReal with hc0
  set c1 := (cOverlap ν₁ R x₀ x₁).toReal with hc1
  have hr00 : (rE ν₀ R x₀).toReal = 1 - q00 := toReal_rE_eq ν₀ R x₀
  have hr01 : (rE ν₁ R x₀).toReal = 1 - q01 := toReal_rE_eq ν₁ R x₀
  have hr10 : (rE ν₀ R x₁).toReal = 1 - q10 := toReal_rE_eq ν₀ R x₁
  have hr11 : (rE ν₁ R x₁).toReal = 1 - q11 := toReal_rE_eq ν₁ R x₁
  have hRgQ : Rg = 1 - Q := toReal_rE_eq (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)
  -- the identity and the union bound, in ℝ
  have hident : Rg + a0 * a1 = (1 - q00) * (1 - q11) + (1 - q01) * (1 - q10) := by
    have h := rE_square_two_toReal ν₀ ν₁ R x₀ x₁
    rw [hr00, hr01, hr10, hr11] at h
    exact h
  have hunion : Q ≤ q00 * q01 + q10 * q11 + c0 + c1 := by
    have h := qE_square_two_toReal ν₀ ν₁ R x₀ x₁
    exact h
  -- overlap `a` bounds
  have ha00 : 0 ≤ a0 := ENNReal.toReal_nonneg
  have ha10 : 0 ≤ a1 := ENNReal.toReal_nonneg
  have ha0l : a0 ≤ 1 - q00 :=
    hr00 ▸ ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_left ν₀ R x₀ x₁)
  have ha0r : a0 ≤ 1 - q10 :=
    hr10 ▸ ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_right ν₀ R x₀ x₁)
  have ha1l : a1 ≤ 1 - q01 :=
    hr01 ▸ ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_left ν₁ R x₀ x₁)
  have ha1r : a1 ≤ 1 - q11 :=
    hr11 ▸ ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_right ν₁ R x₀ x₁)
  -- straight and crossed lower bounds for Rg
  have hRg_straight : (1 - q00) * (1 - q11) ≤ Rg := by
    nlinarith [mul_le_mul ha0r ha1l ha10 (by linarith : (0:ℝ) ≤ 1 - q10)]
  have hRg_crossed : (1 - q01) * (1 - q10) ≤ Rg := by
    nlinarith [mul_le_mul ha0l ha1r ha10 (by linarith : (0:ℝ) ≤ 1 - q00)]
  -- the 𝔰 lower bound via the sorted quantities
  have hs_lower : (1 - d0 * d1) - e0 * (1 - d1) - e1 * (1 - d0) ≤ Rg := by
    have hdl := diag_lower (r00 := 1 - q00) (r01 := 1 - q01) (r10 := 1 - q10)
      (r11 := 1 - q11) (a0 := a0) (a1 := a1)
      (by linarith) (by linarith) (by linarith) (by linarith)
      ha00 (le_min ha0l ha0r) ha10 (le_min ha1l ha1r)
    have hmin0 : min (1 - q00) (1 - q10) = 1 - d0 := by
      rw [hd0]; rcases le_total q00 q10 with h | h
      · rw [max_eq_right h, min_eq_right (by linarith)]
      · rw [max_eq_left h, min_eq_left (by linarith)]
    have hmax0 : max (1 - q00) (1 - q10) = 1 - e0 := by
      rw [he0]; rcases le_total q00 q10 with h | h
      · rw [min_eq_left h, max_eq_left (by linarith)]
      · rw [min_eq_right h, max_eq_right (by linarith)]
    have hmin1 : min (1 - q01) (1 - q11) = 1 - d1 := by
      rw [hd1]; rcases le_total q01 q11 with h | h
      · rw [max_eq_right h, min_eq_right (by linarith)]
      · rw [max_eq_left h, min_eq_left (by linarith)]
    have hmax1 : max (1 - q01) (1 - q11) = 1 - e1 := by
      rw [he1]; rcases le_total q01 q11 with h | h
      · rw [min_eq_left h, max_eq_left (by linarith)]
      · rw [min_eq_right h, max_eq_right (by linarith)]
    rw [hmin0, hmax0, hmin1, hmax1] at hdl
    nlinarith [hdl, hident]
  -- positivity of Rg and the φ(Q) = Q/Rg^α form
  have hu0 : (0 : ℝ) < 1 - d0 := by linarith
  have hv1 : (0 : ℝ) < 1 - e1 := by linarith
  have hRgpos : (0 : ℝ) < Rg :=
    lt_of_lt_of_le (by nlinarith : (0:ℝ) < (1 - q00) * (1 - q11)) hRg_straight
  have hQ1 : Q < 1 := by
    have h := hRgpos
    rw [hRgQ] at h
    linarith
  have hQ0 : 0 ≤ Q := q_nonneg
  have hphiQ : phi α Q = Q / Rg ^ α := by rw [phi, hRgQ]
  have hRgα : (0 : ℝ) < Rg ^ α := Real.rpow_pos_of_pos hRgpos _
  -- rows: rearrangement, then the certified sorted bound, then conversion
  have hrows : (q00 * q01 + q10 * q11) / Rg ^ α ≤ (d0 * d1 + e0 * e1) / Rg ^ α := by
    have h := rows_rearrange (q00 := q00) (q01 := q01) (q10 := q10) (q11 := q11)
    exact div_le_div_of_nonneg_right h hRgα.le
  have hsorted := fourlaw_rows_le (α := α) (L := L) (d0 := d0) (d1 := d1)
    (e0 := e0) (e1 := e1) (R := Rg) hα1 hL0 hL he00 hed0 hd01 he10 hed1 hd11 hs_lower
  have hphimax0 : phi α d0 = max (phi α q00) (phi α q10) :=
    phi_max hα0 hq000 hq100 h00 h10
  have hphimax1 : phi α d1 = max (phi α q01) (phi α q11) :=
    phi_max hα0 hq010 hq110 h01 h11
  have hphimin0 : phi α e0 = min (phi α q00) (phi α q10) :=
    phi_min hα0 hq000 hq100 h00 h10
  have hphimin1 : phi α e1 = min (phi α q01) (phi α q11) :=
    phi_min hα0 hq010 hq110 h01 h11
  have hconv := sorted_bound_to_S (α := α) (L := L)
    (A0 := phi α q00) (A1 := phi α q01) (B0 := phi α q10) (B1 := phi α q11)
    (phi_nonneg hq000 h00) (phi_nonneg hq010 h01)
    (phi_nonneg hq100 h10) (phi_nonneg hq110 h11) hL0 (chordConst_nonneg hα0)
  rw [← hphimax0, ← hphimax1, ← hphimin0, ← hphimin1] at hconv
  have hrowbound : (d0 * d1 + e0 * e1) / Rg ^ α
      ≤ L / 2 * ((phi α q00 + phi α q01) + (phi α q10 + phi α q11))
        + (L * chordConst α / 2 + 5) * ((phi α q00 + phi α q01) * (phi α q10 + phi α q11)) := by
    calc (d0 * d1 + e0 * e1) / Rg ^ α
        ≤ L / 2 * (phi α d0 + phi α d1)
            + L * chordConst α / 2 * ((phi α e0 + phi α e1) * (phi α d0 + phi α d1))
            + 4 * (phi α d0 * phi α e1 + phi α d1 * phi α e0)
            + phi α d0 * phi α e1 := hsorted
      _ ≤ L / 2 * ((phi α q00 + phi α q01) + (phi α q10 + phi α q11))
            + (L * chordConst α / 2 + 5)
              * ((phi α q00 + phi α q01) * (phi α q10 + phi α q11)) := by
          have h := hconv
          linarith [h]
  -- the overlap terms
  have hc00 : 0 ≤ c0 := ENNReal.toReal_nonneg
  have hc10 : 0 ≤ c1 := ENNReal.toReal_nonneg
  have hovl0 : c0 / Rg ^ α ≤ c0 * ((1 - q00) ^ (-α) * (1 - q11) ^ (-α)) := by
    have hden : (1 - q00) ^ α * (1 - q11) ^ α ≤ Rg ^ α := by
      rw [← Real.mul_rpow (by linarith) (by linarith)]
      exact Real.rpow_le_rpow (by nlinarith) hRg_straight hα0
    have hpos : (0 : ℝ) < (1 - q00) ^ α * (1 - q11) ^ α := by
      have h1 : (0:ℝ) < (1 - q00) ^ α := Real.rpow_pos_of_pos (by linarith) _
      have h2 : (0:ℝ) < (1 - q11) ^ α := Real.rpow_pos_of_pos (by linarith) _
      positivity
    calc c0 / Rg ^ α
        ≤ c0 / ((1 - q00) ^ α * (1 - q11) ^ α) :=
          div_le_div_of_nonneg_left hc00 hpos hden
      _ = c0 * ((1 - q00) ^ (-α) * (1 - q11) ^ (-α)) := by
          rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith)]
          field_simp
  have hovl1 : c1 / Rg ^ α ≤ c1 * ((1 - q01) ^ (-α) * (1 - q10) ^ (-α)) := by
    have hden : (1 - q01) ^ α * (1 - q10) ^ α ≤ Rg ^ α := by
      rw [← Real.mul_rpow (by linarith) (by linarith)]
      exact Real.rpow_le_rpow (by nlinarith) hRg_crossed hα0
    have hpos : (0 : ℝ) < (1 - q01) ^ α * (1 - q10) ^ α := by
      have h1 : (0:ℝ) < (1 - q01) ^ α := Real.rpow_pos_of_pos (by linarith) _
      have h2 : (0:ℝ) < (1 - q10) ^ α := Real.rpow_pos_of_pos (by linarith) _
      positivity
    calc c1 / Rg ^ α
        ≤ c1 / ((1 - q01) ^ α * (1 - q10) ^ α) :=
          div_le_div_of_nonneg_left hc10 hpos hden
      _ = c1 * ((1 - q01) ^ (-α) * (1 - q10) ^ (-α)) := by
          rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith)]
          field_simp
  -- combine
  rw [hphiQ]
  calc Q / Rg ^ α
      ≤ (q00 * q01 + q10 * q11 + c0 + c1) / Rg ^ α :=
        div_le_div_of_nonneg_right hunion hRgα.le
    _ = (q00 * q01 + q10 * q11) / Rg ^ α + c0 / Rg ^ α + c1 / Rg ^ α := by
        rw [add_div, add_div]
    _ ≤ (d0 * d1 + e0 * e1) / Rg ^ α + c0 / Rg ^ α + c1 / Rg ^ α := by
        linarith [hrows]
    _ ≤ L / 2 * ((phi α q00 + phi α q01) + (phi α q10 + phi α q11))
          + (L * chordConst α / 2 + 5)
            * ((phi α q00 + phi α q01) * (phi α q10 + phi α q11))
          + c0 * ((1 - q00) ^ (-α) * (1 - q11) ^ (-α))
          + c1 * ((1 - q01) ^ (-α) * (1 - q10) ^ (-α)) := by
        linarith [hrowbound, hovl0, hovl1]

end GraphMarkovMatching
