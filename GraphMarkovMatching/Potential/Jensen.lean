/-
Countable Jensen for `φ_α`, the mixture step of the one-step bounds
(`Process/Descent.lean`, `Composite/Assembly.lean`, and
`Archive/Step.lean`).

The convexity input is packaged as a *supporting line*: at every `p ∈ [0,1)`
the explicit slope `c_p = ((1-p) + αp)/(1-p)^{α+1}` satisfies

    φ_α(p) + c_p (z - p) ≤ φ_α(z)          (z ∈ [0,1)).

This reduces, after clearing denominators in the variables `u = 1-z`,
`v = 1-p`, to Bernoulli's inequality `v^α ≥ u^α + α u^{α-1}(v-u)` plus the
polynomial identity whose defect is `α u^{α-1}(v-u)² ≥ 0`. No derivative
machinery and no finite-approximation limits are needed: the supporting line
turns the countable Jensen inequality into a termwise bound followed by the
cancellation of one finite summand.

The mixture Jensen `phiE_tsum_jensen` is stated in the safe `phiE` convention:
if the mixture charges a component with bad degree `1`, the right side is `⊤`
and the bound is trivial, which is exactly how mismatch patterns are meant to
be handled a level up.
-/
import GraphMarkovMatching.Potential.Directed

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

/-! ### The supporting line -/

/-- The core inequality in the substituted variables `u = 1-z`, `v = 1-p`:

    (1-v)/v^α + ((v + α(1-v))/v^{α+1})·(v-u) ≤ (1-u)/u^α. -/
lemma supportLine_uv {α u v : ℝ} (hα : 1 ≤ α) (hu : 0 < u) (hu1 : u ≤ 1)
    (hv : 0 < v) (_hv1 : v ≤ 1) :
    (1 - v) / v ^ α + (v + α * (1 - v)) / v ^ (α + 1) * (v - u)
      ≤ (1 - u) / u ^ α := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hA : (0 : ℝ) < u ^ α := Real.rpow_pos_of_pos hu α
  have hD : (0 : ℝ) < u ^ (α - 1) := Real.rpow_pos_of_pos hu _
  have hBv : (0 : ℝ) < v ^ α := Real.rpow_pos_of_pos hv α
  have hCv : v ^ (α + 1) = v ^ α * v := Real.rpow_add_one hv.ne' α
  have hADu : u ^ (α - 1) * u = u ^ α := by
    rw [← Real.rpow_add_one hu.ne' (α - 1), sub_add_cancel]
  -- Bernoulli: v^α ≥ u^α + α u^{α-1} (v - u)
  have hB : u ^ α + α * (u ^ (α - 1) * (v - u)) ≤ v ^ α := by
    have hs : (-1 : ℝ) ≤ (v - u) / u := by
      rw [le_div_iff₀ hu]; nlinarith
    have hB0 := one_add_mul_self_le_rpow_one_add hs hα
    have h1p : (1 : ℝ) + (v - u) / u = v / u := by field_simp; ring
    rw [h1p, Real.div_rpow hv.le hu.le] at hB0
    have h2 := mul_le_mul_of_nonneg_right hB0 hA.le
    have h3 : v ^ α / u ^ α * u ^ α = v ^ α := div_mul_cancel₀ _ hA.ne'
    rw [h3] at h2
    have h4 : (1 + α * ((v - u) / u)) * u ^ α = u ^ α + α * (u ^ (α - 1) * (v - u)) := by
      rw [← hADu]; field_simp
    rw [h4] at h2
    exact h2
  -- clear denominators
  rw [hCv]
  have hLHS : (1 - v) / v ^ α + (v + α * (1 - v)) / (v ^ α * v) * (v - u)
      = (v * (1 - u) + α * (1 - v) * (v - u)) / (v ^ α * v) := by
    field_simp
    ring
  rw [hLHS, div_le_div_iff₀ (by positivity) hA]
  -- goal: (v(1-u) + α(1-v)(v-u)) u^α ≤ (1-u) (v^α v)
  have key1 : (1 - u) * v * (u ^ α + α * (u ^ (α - 1) * (v - u)))
      ≤ (1 - u) * v * v ^ α :=
    mul_le_mul_of_nonneg_left hB (by nlinarith)
  have key2 : (v * (1 - u) + α * (1 - v) * (v - u)) * u ^ α
      ≤ (1 - u) * v * (u ^ α + α * (u ^ (α - 1) * (v - u))) := by
    rw [← hADu]
    nlinarith [mul_nonneg (mul_nonneg hα0 hD.le) (sq_nonneg (v - u))]
  nlinarith [key1, key2]

/-- **The supporting line of `φ_α`** at `p ∈ [0,1)`: an explicit nonnegative
slope `c` with `φ_α(p) + c(z-p) ≤ φ_α(z)` for all `z ∈ [0,1)`. -/
lemma exists_supportLine {α p : ℝ} (hα : 1 ≤ α) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ z, 0 ≤ z → z < 1 → phi α p + c * (z - p) ≤ phi α z := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hv : (0 : ℝ) < 1 - p := by linarith
  refine ⟨((1 - p) + α * p) / (1 - p) ^ (α + 1), by positivity, ?_⟩
  intro z hz0 hz1
  have hu : (0 : ℝ) < 1 - z := by linarith
  have h := supportLine_uv (u := 1 - z) (v := 1 - p) hα hu (by linarith) hv (by linarith)
  have e1 : (1 : ℝ) - (1 - p) = p := by ring
  have e2 : (1 : ℝ) - (1 - z) = z := by ring
  have e3 : (1 - p) - (1 - z) = z - p := by ring
  rw [e1, e2, e3] at h
  rw [phi, phi]
  exact h

/-! ### Countable Jensen for `phiE` -/

/-- **Mixture Jensen**: for probability weights `w` in `ℝ≥0∞` and values
`Q i ∈ [0,1]`, the safe weight of the mixture mean is at most the mixture of
safe weights,

    `phiE α (∑' w_i Q_i) ≤ ∑' w_i · phiE α (Q_i)`.

If some charged component has `Q_i = 1` the right side is `⊤`. -/
lemma phiE_tsum_jensen {ι : Type*} {α : ℝ} (hα : 1 ≤ α)
    (w : ι → ℝ≥0∞) (Q : ι → ℝ)
    (hw : ∑' i, w i = 1) (hQ0 : ∀ i, 0 ≤ Q i) (hQ1 : ∀ i, Q i ≤ 1) :
    phiE α (∑' i, w i * ENNReal.ofReal (Q i)).toReal
      ≤ ∑' i, w i * phiE α (Q i) := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  set m : ℝ≥0∞ := ∑' i, w i * ENNReal.ofReal (Q i) with hm_def
  -- the mean is a subprobability
  have hm1 : m ≤ 1 := by
    rw [hm_def, ← hw]
    refine ENNReal.tsum_le_tsum fun i => ?_
    calc w i * ENNReal.ofReal (Q i) ≤ w i * 1 := by
          exact mul_le_mul_right (by simpa using ENNReal.ofReal_le_ofReal (hQ1 i)) _
      _ = w i := mul_one _
  have hm_top : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hm1
  have hq0 : (0 : ℝ) ≤ m.toReal := ENNReal.toReal_nonneg
  have hq1 : m.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hm1
    simpa using this
  -- Case: some charged component sits at Q = 1
  by_cases hbad : ∃ i, w i ≠ 0 ∧ ¬ Q i < 1
  · obtain ⟨i₀, hw₀, hQ₀⟩ := hbad
    have htop : phiE α (Q i₀) = ⊤ := ite_eq_right hQ₀
    have : (⊤ : ℝ≥0∞) ≤ ∑' i, w i * phiE α (Q i) := by
      calc (⊤ : ℝ≥0∞) = w i₀ * phiE α (Q i₀) := by
            rw [htop, ENNReal.mul_top hw₀]
        _ ≤ ∑' i, w i * phiE α (Q i) :=
              ENNReal.le_tsum (f := fun i => w i * phiE α (Q i)) i₀
    exact le_trans le_top this
  -- Main case: Q < 1 wherever w charges
  push Not at hbad
  -- the mean is strictly below 1
  have hqlt : m.toReal < 1 := by
    rcases lt_or_eq_of_le hq1 with h | h
    · exact h
    -- m = 1 forces a charged component at Q = 1: contradiction
    exfalso
    have hm_one : m = 1 := by
      have := ENNReal.ofReal_toReal hm_top
      rw [← this, h, ENNReal.ofReal_one]
    obtain ⟨i₀, hw₀⟩ : ∃ i, w i ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [hm_def] at hm_one
      have : (∑' i, w i * ENNReal.ofReal (Q i)) = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun i => ?_
        rw [hc i, zero_mul]
      rw [this] at hm_one
      exact zero_ne_one hm_one
    have hQi₀ : Q i₀ < 1 := hbad i₀ hw₀
    -- split both sums at i₀
    have hsplit_m : m = w i₀ * ENNReal.ofReal (Q i₀)
        + ∑' i, if i = i₀ then 0 else w i * ENNReal.ofReal (Q i) := by
      rw [hm_def]; exact ENNReal.tsum_eq_add_tsum_ite i₀
    have hsplit_w : (1 : ℝ≥0∞) = w i₀ + ∑' i, if i = i₀ then 0 else w i := by
      rw [← hw]; exact ENNReal.tsum_eq_add_tsum_ite i₀
    have hrest : (∑' i, if i = i₀ then 0 else w i * ENNReal.ofReal (Q i))
        ≤ ∑' i, if i = i₀ then 0 else w i := by
      refine ENNReal.tsum_le_tsum fun i => ?_
      by_cases h' : i = i₀
      · simp [h']
      · simp only [h', ite_false]
        calc w i * ENNReal.ofReal (Q i) ≤ w i * 1 :=
              mul_le_mul_right (by simpa using ENNReal.ofReal_le_ofReal (hQ1 i)) _
          _ = w i := mul_one _
    -- all pieces are finite; compare in ℝ
    have hw₀_le : w i₀ ≤ 1 := by
      rw [hsplit_w]; exact le_self_add
    have hw₀_top : w i₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw₀_le
    have hrw_top : (∑' i, if i = i₀ then 0 else w i) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      rw [hsplit_w]; exact le_add_self
    have hkey : m < 1 := by
      rw [hsplit_m, hsplit_w]
      have h1 : w i₀ * ENNReal.ofReal (Q i₀) < w i₀ := by
        have hlt : ENNReal.ofReal (Q i₀) < 1 := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hQ0 i₀) |>.mpr hQi₀
        have h' := ENNReal.mul_lt_mul_left hw₀ hw₀_top hlt
        calc w i₀ * ENNReal.ofReal (Q i₀)
            = ENNReal.ofReal (Q i₀) * w i₀ := mul_comm _ _
          _ < 1 * w i₀ := h'
          _ = w i₀ := one_mul _
      exact ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top hrw_top hrest) h1 hrest
    rw [hm_one] at hkey
    exact lt_irrefl _ hkey
  -- supporting line at the mean
  obtain ⟨c, hc0, hSL⟩ := exists_supportLine hα hq0 hqlt
  set p : ℝ := m.toReal with hp_def
  have hK_top : ENNReal.ofReal (c * p) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the termwise supporting-line bound, where w charges
  have hterm2 : ∀ i, w i * (ENNReal.ofReal (phi α p) + ENNReal.ofReal c * ENNReal.ofReal (Q i))
      ≤ w i * (phiE α (Q i) + ENNReal.ofReal (c * p)) := by
    intro i
    by_cases hwi : w i = 0
    · rw [hwi, zero_mul, zero_mul]
    · have hQi : Q i < 1 := hbad i hwi
      refine mul_le_mul_right ?_ _
      have hreal : phi α p + c * Q i ≤ phi α (Q i) + c * p := by
        have := hSL (Q i) (hQ0 i) hQi
        nlinarith
      have hphiE : phiE α (Q i) = ENNReal.ofReal (phi α (Q i)) := phiE_of_lt hQi
      rw [hphiE, ← ENNReal.ofReal_mul hc0]
      calc ENNReal.ofReal (phi α p) + ENNReal.ofReal (c * Q i)
          = ENNReal.ofReal (phi α p + c * Q i) := by
            rw [ENNReal.ofReal_add (phi_nonneg hq0 hqlt) (mul_nonneg hc0 (hQ0 i))]
        _ ≤ ENNReal.ofReal (phi α (Q i) + c * p) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (phi α (Q i)) + ENNReal.ofReal (c * p) := by
            rw [ENNReal.ofReal_add (phi_nonneg (hQ0 i) hQi) (mul_nonneg hc0 hq0)]
  -- sum the termwise bound
  have hsum : (∑' i, w i * (ENNReal.ofReal (phi α p) + ENNReal.ofReal c * ENNReal.ofReal (Q i)))
      ≤ ∑' i, w i * (phiE α (Q i) + ENNReal.ofReal (c * p)) :=
    ENNReal.tsum_le_tsum hterm2
  -- identify both sides
  have hLHS : (∑' i, w i * (ENNReal.ofReal (phi α p) + ENNReal.ofReal c * ENNReal.ofReal (Q i)))
      = ENNReal.ofReal (phi α p) + ENNReal.ofReal c * m := by
    calc (∑' i, w i * (ENNReal.ofReal (phi α p) + ENNReal.ofReal c * ENNReal.ofReal (Q i)))
        = ∑' i, (w i * ENNReal.ofReal (phi α p)
            + ENNReal.ofReal c * (w i * ENNReal.ofReal (Q i))) := by
          exact tsum_congr fun i => by ring
      _ = (∑' i, w i * ENNReal.ofReal (phi α p))
            + ∑' i, ENNReal.ofReal c * (w i * ENNReal.ofReal (Q i)) := ENNReal.tsum_add
      _ = ENNReal.ofReal (phi α p) + ENNReal.ofReal c * m := by
          rw [ENNReal.tsum_mul_right, hw, one_mul, ENNReal.tsum_mul_left, ← hm_def]
  have hRHS : (∑' i, w i * (phiE α (Q i) + ENNReal.ofReal (c * p)))
      = (∑' i, w i * phiE α (Q i)) + ENNReal.ofReal (c * p) := by
    calc (∑' i, w i * (phiE α (Q i) + ENNReal.ofReal (c * p)))
        = ∑' i, (w i * phiE α (Q i) + w i * ENNReal.ofReal (c * p)) := by
          exact tsum_congr fun i => by ring
      _ = (∑' i, w i * phiE α (Q i)) + ∑' i, w i * ENNReal.ofReal (c * p) := ENNReal.tsum_add
      _ = (∑' i, w i * phiE α (Q i)) + ENNReal.ofReal (c * p) := by
          rw [ENNReal.tsum_mul_right, hw, one_mul]
  rw [hLHS, hRHS] at hsum
  -- rewrite `ofReal c * m` as `ofReal (c * p)` and cancel
  have hm_or : ENNReal.ofReal c * m = ENNReal.ofReal (c * p) := by
    rw [ENNReal.ofReal_mul hc0, hp_def, ENNReal.ofReal_toReal hm_top]
  rw [hm_or] at hsum
  have hfinal : ENNReal.ofReal (phi α p) ≤ ∑' i, w i * phiE α (Q i) :=
    (ENNReal.add_le_add_iff_right hK_top).mp hsum
  rw [phiE_of_lt hqlt]
  exact hfinal

end GraphMarkovMatching
