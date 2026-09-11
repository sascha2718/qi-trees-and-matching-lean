/-
The one-site quantities of `markov_matching_new_proof.tex` (`eq:root-defect`,
`sec:root-contributions`, `sec:independent-root`) and their bounds:

* `eta`, `delta`, `e0`, `zeta`: the graph potential `η_{G,α}(μ)`, the incompatible root
  mass `δ = 1 - b(0)`, the forced-state term `φ_α(δ)` and the defect
  `ζ_α = max{η_α, φ_α(δ)}`, infinite when `b(0) = 0`;
* `fRoot`, `RmuC`, `DmuC`: the root factors `f`, `R_μ` and `D_μ`;
* `delta_le_zeta`, `fRoot_le`, `fRoot_le_zeta`, `RmuC_le`, `DmuC_le`
  (`eq:root-parameter-bounds` and `D_μ ≤ 1 + (2α-1)ζ`);
* `e0_le_eta_div`, `fRoot_le_eta_div`, `delta_le_eta_div`, `zeta_le_eta_div`: the bounds
  through `η` when `μ(0) ≥ p > 0`.
-/
import GraphMarkovMatching.Stopped.Model

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

/-! ### Pointwise weight bounds (`sec:quantitative-stopping`, `sec:independent-root`) -/

/-- The restricted weight is at most `1 + α φ_α(q)`: the tangent bound
`(1-q)^{-α} ≤ 1 + α φ_α(q)` of `sec:quantitative-stopping` on the positive set. -/
private lemma WresD_le_one_add {X : Type} {α : ℝ} (hα : 1 ≤ α) (ρ : PMF X)
    (R : X → X → Prop) (x : X) :
    WresD α ρ R x ≤ 1 + ENNReal.ofReal α * phiE α (q ρ R x) := by
  by_cases h : rE ρ R x = 0
  · rw [WresD, if_pos h]
    exact zero_le
  · rw [WresD, if_neg h]
    exact WnnD_le hα ρ R x

/-- On the positive set the bad degree times the restricted weight is the potential weight:
`q (1-q)^{-α} = φ_α(q)`. -/
private lemma qE_mul_WresD_eq {X : Type} (α : ℝ) (ρ : PMF X) (R : X → X → Prop) (x : X)
    (h : rE ρ R x ≠ 0) : qE ρ R x * WresD α ρ R x = phiE α (q ρ R x) := by
  have hq : q ρ R x < 1 := q_lt_one_of_rE_ne_zero h
  have hqE : qE ρ R x = ENNReal.ofReal (q ρ R x) := by
    rw [q, ENNReal.ofReal_toReal qE_ne_top]
  rw [WresD, if_neg h, WnnD, phiE_of_lt hq, hqE, ← ENNReal.ofReal_mul q_nonneg]
  congr 1
  rw [phi, Real.rpow_neg (by linarith), div_eq_mul_inv]

/-- `s^{1-α} ≤ 1 + (α-1)(1-s)/s^α` for `0 < s` (`sec:independent-root`), from Bernoulli's
inequality `1 - s^α ≤ α (1-s)`. -/
private lemma rpow_one_sub_le_real {α s : ℝ} (hα : 1 ≤ α) (hs0 : 0 < s) :
    s ^ (1 - α) ≤ 1 + (α - 1) * ((1 - s) / s ^ α) := by
  have hp : 0 < s ^ α := Real.rpow_pos_of_pos hs0 α
  have h1 : s ^ (1 - α) = s / s ^ α := by
    rw [Real.rpow_sub hs0, Real.rpow_one]
  have hB := one_sub_rpow_le hα hs0.le
  have h2 : (1 + (α - 1) * ((1 - s) / s ^ α)) * s ^ α = s ^ α + (α - 1) * (1 - s) := by
    field_simp
  rw [h1, div_le_iff₀ hp, h2]
  nlinarith

/-- The safe form of `s^{1-α} ≤ 1 + (α-1) φ_α(1-s)` for a degree `t ∈ (0,1]`
(`sec:independent-root`). -/
private lemma rpow_one_sub_le_one_add_phiE {α : ℝ} (hα : 1 ≤ α) {t : ℝ≥0∞}
    (ht0 : t ≠ 0) (ht1 : t ≤ 1) :
    t ^ (1 - α) ≤ 1 + ENNReal.ofReal (α - 1) * phiE α (1 - t.toReal) := by
  have hα1 : (0 : ℝ) ≤ α - 1 := by linarith
  have htop : t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ht1
  have htpos : 0 < t.toReal := ENNReal.toReal_pos ht0 htop
  have htle : t.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top ht1
  have hs1 : 1 - t.toReal < 1 := by linarith
  have hφ : 0 ≤ phi α (1 - t.toReal) := phi_nonneg (by linarith) hs1
  have hphi : phi α (1 - t.toReal) = (1 - t.toReal) / t.toReal ^ α := by
    rw [phi, sub_sub_cancel]
  calc t ^ (1 - α) = (ENNReal.ofReal t.toReal) ^ (1 - α) := by
        rw [ENNReal.ofReal_toReal htop]
    _ = ENNReal.ofReal (t.toReal ^ (1 - α)) := ENNReal.ofReal_rpow_of_pos htpos
    _ ≤ ENNReal.ofReal (1 + (α - 1) * phi α (1 - t.toReal)) := by
        rw [hphi]
        exact ENNReal.ofReal_le_ofReal (rpow_one_sub_le_real hα htpos)
    _ = 1 + ENNReal.ofReal (α - 1) * phiE α (1 - t.toReal) := by
        rw [phiE_of_lt hs1, ENNReal.ofReal_add (by norm_num) (mul_nonneg hα1 hφ),
          ENNReal.ofReal_mul hα1, ENNReal.ofReal_one]

namespace Model

variable {V I : Type} (M : Model V I)

/-! ### The one-site quantities (`eq:root-defect`, `sec:root-contributions`) -/

/-- The graph potential `η_{G,α}(μ) = ∑_v μ(v) φ_α(1 - b(v))`. -/
noncomputable def eta (α : ℝ) : ℝ≥0∞ := PhiD α M.μ M.μ M.R

/-- The incompatible root mass `δ = 1 - b(0) = μ{v : v ≁ 0}`. -/
noncomputable def delta : ℝ≥0∞ := qE M.μ M.R M.zero

/-- The forced-state term `e_0 = φ_α(δ)`, infinite when `b(0) = 0`. -/
noncomputable def e0 (α : ℝ) : ℝ≥0∞ := phiE α (q M.μ M.R M.zero)

/-- The one-site defect `ζ_α = max{η_α, φ_α(δ)}`. -/
noncomputable def zeta (α : ℝ) : ℝ≥0∞ := max (M.eta α) (M.e0 α)

/-- The integrated inverse-degree weight of an incompatible fresh root,
`f = ∑_{v ≁ 0} μ(v) b(v)^{-α}`. -/
noncomputable def fRoot (α : ℝ) : ℝ≥0∞ :=
  ∑' v, M.μ v * (if M.R v M.zero then 0 else WresD α M.μ M.R v)

/-- The compatible-root factor
`R_μ = max{1, b(0)^{-α}, ∑_{v ∼ 0} μ(v) b(v)^{-α}}`. -/
noncomputable def RmuC (α : ℝ) : ℝ≥0∞ :=
  max 1 (max (WresD α M.μ M.R M.zero)
    (∑' v, M.μ v * (if M.R v M.zero then WresD α M.μ M.R v else 0)))

/-- The integrated root coefficient
`D_μ = max{1, α η + ∑_v μ(v) b(v)^{1-α}, α e_0 + b(0)^{1-α}}`. -/
noncomputable def DmuC (α : ℝ) : ℝ≥0∞ :=
  max 1 (max (ENNReal.ofReal α * M.eta α + ∑' v, M.μ v * (rE M.μ M.R v) ^ (1 - α))
    (ENNReal.ofReal α * M.e0 α + (rE M.μ M.R M.zero) ^ (1 - α)))

lemma one_le_RmuC (α : ℝ) : 1 ≤ M.RmuC α := le_max_left _ _

lemma one_le_DmuC (α : ℝ) : 1 ≤ M.DmuC α := le_max_left _ _

lemma eta_le_zeta (α : ℝ) : M.eta α ≤ M.zeta α := le_max_left _ _

lemma e0_le_zeta (α : ℝ) : M.e0 α ≤ M.zeta α := le_max_right _ _

/-- A finite defect forces `b(0) > 0`. -/
lemma rE_zero_ne_zero_of_zeta_ne_top {α : ℝ} (hζ : M.zeta α ≠ ⊤) :
    rE M.μ M.R M.zero ≠ 0 := by
  intro h0
  apply hζ
  have hq : q M.μ M.R M.zero = 1 := by
    have h := rE_add_qE M.μ M.R M.zero
    rw [h0, zero_add] at h
    rw [q, h, ENNReal.toReal_one]
  rw [zeta, e0, hq, phiE_one, max_eq_right le_top]

/-- When `δ = 0` the forced-state term vanishes and `ζ_α = η_α`. -/
lemma zeta_eq_eta_of_delta_zero {α : ℝ} (hδ : M.delta = 0) : M.zeta α = M.eta α := by
  have hq : q M.μ M.R M.zero = 0 := by
    rw [delta] at hδ
    rw [q, hδ, ENNReal.toReal_zero]
  rw [zeta, e0, hq, phiE_zero, max_eq_left (zero_le)]

/-- `δ ≤ ζ_α` (`eq:root-parameter-bounds`). -/
lemma delta_le_zeta {α : ℝ} (hα : 0 ≤ α) : M.delta ≤ M.zeta α := by
  calc M.delta = ENNReal.ofReal (q M.μ M.R M.zero) := by
        rw [delta, q, ENNReal.ofReal_toReal qE_ne_top]
    _ ≤ M.e0 α := ofReal_le_phiE hα q_nonneg q_le_one
    _ ≤ M.zeta α := M.e0_le_zeta α

/-- `f ≤ δ + α η` (`eq:root-parameter-bounds`). -/
lemma fRoot_le (hc : M.IsCompat) {α : ℝ} (hα : 1 ≤ α) :
    M.fRoot α ≤ M.delta + ENNReal.ofReal α * M.eta α := by
  calc M.fRoot α
      ≤ ∑' v, ((if M.R v M.zero then 0 else M.μ v)
          + ENNReal.ofReal α * (M.μ v * phiE α (q M.μ M.R v))) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        by_cases hv : M.R v M.zero
        · simp [hv]
        · rw [if_neg hv, if_neg hv]
          calc M.μ v * WresD α M.μ M.R v
              ≤ M.μ v * (1 + ENNReal.ofReal α * phiE α (q M.μ M.R v)) := by
                gcongr
                exact WresD_le_one_add hα _ _ _
            _ = M.μ v + ENNReal.ofReal α * (M.μ v * phiE α (q M.μ M.R v)) := by ring
    _ = M.delta + ENNReal.ofReal α * M.eta α := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, tsum_not_rel_eq_qE hc.symm, delta, eta,
          PhiD]

/-- `f ≤ (1 + α) ζ_α` (`eq:root-parameter-bounds`). -/
lemma fRoot_le_zeta (hc : M.IsCompat) {α : ℝ} (hα : 1 ≤ α) :
    M.fRoot α ≤ ENNReal.ofReal (1 + α) * M.zeta α := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  calc M.fRoot α ≤ M.delta + ENNReal.ofReal α * M.eta α := M.fRoot_le hc hα
    _ ≤ M.zeta α + ENNReal.ofReal α * M.zeta α := by
        gcongr
        · exact M.delta_le_zeta hα0
        · exact M.eta_le_zeta α
    _ = ENNReal.ofReal (1 + α) * M.zeta α := by
        rw [ENNReal.ofReal_add zero_le_one hα0, ENNReal.ofReal_one, add_mul, one_mul]

/-- `R_μ ≤ 1 + α ζ_α` (`eq:root-parameter-bounds`). -/
lemma RmuC_le (hc : M.IsCompat) {α : ℝ} (hα : 1 ≤ α) :
    M.RmuC α ≤ 1 + ENNReal.ofReal α * M.zeta α := by
  have _ := hc
  refine max_le le_self_add (max_le ?_ ?_)
  · calc WresD α M.μ M.R M.zero ≤ 1 + ENNReal.ofReal α * M.e0 α :=
          WresD_le_one_add hα _ _ _
      _ ≤ 1 + ENNReal.ofReal α * M.zeta α := by
          gcongr
          exact M.e0_le_zeta α
  · calc ∑' v, M.μ v * (if M.R v M.zero then WresD α M.μ M.R v else 0)
        ≤ ∑' v, (M.μ v + ENNReal.ofReal α * (M.μ v * phiE α (q M.μ M.R v))) := by
          refine ENNReal.tsum_le_tsum fun v => ?_
          calc M.μ v * (if M.R v M.zero then WresD α M.μ M.R v else 0)
              ≤ M.μ v * (1 + ENNReal.ofReal α * phiE α (q M.μ M.R v)) := by
                gcongr
                split_ifs
                · exact WresD_le_one_add hα _ _ _
                · exact zero_le
            _ = M.μ v + ENNReal.ofReal α * (M.μ v * phiE α (q M.μ M.R v)) := by ring
      _ = 1 + ENNReal.ofReal α * M.eta α := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, PMF.tsum_coe, eta, PhiD]
      _ ≤ 1 + ENNReal.ofReal α * M.zeta α := by
          gcongr
          exact M.eta_le_zeta α

/-- The integrated `b(v)^{1-α}` is at most `1 + (α-1) η` (`sec:independent-root`). -/
private lemma tsum_rpow_one_sub_le (hc : M.IsCompat) {α : ℝ} (hα : 1 ≤ α) :
    ∑' v, M.μ v * (rE M.μ M.R v) ^ (1 - α) ≤ 1 + ENNReal.ofReal (α - 1) * M.eta α := by
  have hpt : ∀ v, M.μ v * (rE M.μ M.R v) ^ (1 - α)
      ≤ M.μ v + ENNReal.ofReal (α - 1) * (M.μ v * phiE α (q M.μ M.R v)) := by
    intro v
    by_cases h : rE M.μ M.R v = 0
    · have hv : M.μ v = 0 := by
        have hle := le_rE_of_refl (μ := M.μ) (hc.refl v)
        rw [h] at hle
        exact le_antisymm hle (zero_le)
      simp [hv]
    · calc M.μ v * (rE M.μ M.R v) ^ (1 - α)
          ≤ M.μ v * (1 + ENNReal.ofReal (α - 1) * phiE α (q M.μ M.R v)) := by
            gcongr
            have h1 := rpow_one_sub_le_one_add_phiE hα h rE_le_one
            rwa [toReal_rE_eq, sub_sub_cancel] at h1
        _ = M.μ v + ENNReal.ofReal (α - 1) * (M.μ v * phiE α (q M.μ M.R v)) := by ring
  calc ∑' v, M.μ v * (rE M.μ M.R v) ^ (1 - α)
      ≤ ∑' v, (M.μ v + ENNReal.ofReal (α - 1) * (M.μ v * phiE α (q M.μ M.R v))) :=
        ENNReal.tsum_le_tsum hpt
    _ = 1 + ENNReal.ofReal (α - 1) * M.eta α := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, PMF.tsum_coe, eta, PhiD]

/-- `D_μ ≤ 1 + (2α - 1) ζ_α` (`sec:independent-root`), from
`s^{1-α} ≤ 1 + (α-1)(1-s)/s^α`. -/
lemma DmuC_le (hc : M.IsCompat) {α : ℝ} (hα : 1 ≤ α) :
    M.DmuC α ≤ 1 + ENNReal.ofReal (2 * α - 1) * M.zeta α := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hα1 : (0 : ℝ) ≤ α - 1 := by linarith
  have hsum : ENNReal.ofReal α + ENNReal.ofReal (α - 1) = ENNReal.ofReal (2 * α - 1) := by
    rw [← ENNReal.ofReal_add hα0 hα1]
    congr 1
    ring
  by_cases hb0 : rE M.μ M.R M.zero = 0
  · have hζ : M.zeta α = ⊤ := by
      by_contra h
      exact M.rE_zero_ne_zero_of_zeta_ne_top h hb0
    rw [hζ, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by linarith : (0 : ℝ) < 2 * α - 1)).ne',
      add_top]
    exact le_top
  refine max_le le_self_add (max_le ?_ ?_)
  · calc ENNReal.ofReal α * M.eta α + ∑' v, M.μ v * (rE M.μ M.R v) ^ (1 - α)
        ≤ ENNReal.ofReal α * M.eta α + (1 + ENNReal.ofReal (α - 1) * M.eta α) := by
          gcongr
          exact M.tsum_rpow_one_sub_le hc hα
      _ = 1 + ENNReal.ofReal (2 * α - 1) * M.eta α := by
          rw [← hsum]
          ring
      _ ≤ 1 + ENNReal.ofReal (2 * α - 1) * M.zeta α := by
          gcongr
          exact M.eta_le_zeta α
  · have h1 := rpow_one_sub_le_one_add_phiE hα hb0 rE_le_one
    rw [toReal_rE_eq, sub_sub_cancel] at h1
    calc ENNReal.ofReal α * M.e0 α + (rE M.μ M.R M.zero) ^ (1 - α)
        ≤ ENNReal.ofReal α * M.e0 α + (1 + ENNReal.ofReal (α - 1) * M.e0 α) := by
          gcongr
          exact h1
      _ = 1 + ENNReal.ofReal (2 * α - 1) * M.e0 α := by
          rw [← hsum]
          ring
      _ ≤ 1 + ENNReal.ofReal (2 * α - 1) * M.zeta α := by
          gcongr
          exact M.e0_le_zeta α

/-! ### The bounds through `η` at `μ(0) ≥ p > 0` (`sec:root-contributions`) -/

/-- A state incompatible with `0` has bad degree at least `μ(0)` (`sec:root-contributions`). -/
private lemma mu_zero_le_qE {v : V} (hv : ¬ M.R v M.zero) : M.μ M.zero ≤ qE M.μ M.R v := by
  rw [qE]
  calc M.μ M.zero = if M.R v M.zero then 0 else M.μ M.zero := by rw [if_neg hv]
    _ ≤ ∑' y, if M.R v y then 0 else M.μ y := ENNReal.le_tsum M.zero

/-- With `μ(0) ≥ p > 0`: `φ_α(δ) ≤ η/p`, from the summand of `η` at `0`. -/
lemma e0_le_eta_div (hc : M.IsCompat) {α : ℝ} (hα : 0 ≤ α) {p : ℝ≥0∞} (hp : p ≠ 0)
    (hμ0 : p ≤ M.μ M.zero) : M.e0 α ≤ M.eta α / p := by
  have _ := hc
  have _ := hα
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top (PMF.apply_ne_top _ _) hμ0
  rw [ENNReal.le_div_iff_mul_le (Or.inl hp) (Or.inl hpt)]
  calc M.e0 α * p ≤ phiE α (q M.μ M.R M.zero) * M.μ M.zero := by
        rw [e0]
        gcongr
    _ = M.μ M.zero * phiE α (q M.μ M.R M.zero) := mul_comm _ _
    _ ≤ M.eta α := by
        rw [eta, PhiD]
        exact ENNReal.le_tsum M.zero

/-- With `μ(0) ≥ p > 0`: `f ≤ η/p`, since a state incompatible with `0` has
`1 - b(v) ≥ p`. -/
lemma fRoot_le_eta_div (hc : M.IsCompat) {α : ℝ} (hα : 0 ≤ α) {p : ℝ≥0∞} (hp : p ≠ 0)
    (hμ0 : p ≤ M.μ M.zero) : M.fRoot α ≤ M.eta α / p := by
  have _ := hc
  have _ := hα
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top (PMF.apply_ne_top _ _) hμ0
  rw [ENNReal.le_div_iff_mul_le (Or.inl hp) (Or.inl hpt)]
  calc M.fRoot α * p
      = ∑' v, M.μ v * ((if M.R v M.zero then 0 else WresD α M.μ M.R v) * p) := by
        rw [fRoot, ← ENNReal.tsum_mul_right]
        exact tsum_congr fun v => by ring
    _ ≤ ∑' v, M.μ v * phiE α (q M.μ M.R v) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        gcongr
        split_ifs with hv
        · rw [zero_mul]
          exact zero_le
        · by_cases h : rE M.μ M.R v = 0
          · rw [WresD, if_pos h, zero_mul]
            exact zero_le
          · calc WresD α M.μ M.R v * p ≤ WresD α M.μ M.R v * qE M.μ M.R v := by
                  gcongr
                  exact hμ0.trans (M.mu_zero_le_qE hv)
              _ = phiE α (q M.μ M.R v) := by rw [mul_comm, qE_mul_WresD_eq α _ _ _ h]
    _ = M.eta α := by rw [eta, PhiD]

/-- With `μ(0) ≥ p > 0`: `δ ≤ (1-p)^α η/p`, since a state incompatible with `0` has
`b(v) ≤ 1 - p`. -/
lemma delta_le_eta_div (hc : M.IsCompat) {α : ℝ} (hα : 0 ≤ α) {p : ℝ≥0∞} (hp : p ≠ 0)
    (hμ0 : p ≤ M.μ M.zero) : M.delta ≤ (1 - p) ^ α * M.eta α / p := by
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top (PMF.apply_ne_top _ _) hμ0
  have hp1 : p ≤ 1 := hμ0.trans (PMF.coe_le_one _ _)
  have hpr0 : 0 < p.toReal := ENNReal.toReal_pos hp hpt
  have hpr1 : p.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hp1
  have hp_eq : p = ENNReal.ofReal p.toReal := (ENNReal.ofReal_toReal hpt).symm
  have h1p : (1 - p) ^ α = ENNReal.ofReal ((1 - p.toReal) ^ α) := by
    have h : (1 : ℝ≥0∞) - p = ENNReal.ofReal (1 - p.toReal) := by
      rw [ENNReal.ofReal_sub 1 hpr0.le, ENNReal.ofReal_one, ENNReal.ofReal_toReal hpt]
    rw [h, ENNReal.ofReal_rpow_of_nonneg (by linarith) hα]
  have hpw : ∀ v, ¬ M.R M.zero v → M.μ v ≠ 0 →
      p ≤ (1 - p) ^ α * phiE α (q M.μ M.R v) := by
    intro v hv hv0
    have hv' : ¬ M.R v M.zero := fun h => hv (hc.symm _ _ h)
    have hq1 : q M.μ M.R v < 1 := q_lt_one (hc.refl v) hv0
    have hqp : p.toReal ≤ q M.μ M.R v := by
      rw [q]
      exact ENNReal.toReal_mono qE_ne_top (hμ0.trans (M.mu_zero_le_qE hv'))
    have hd : 0 < (1 - q M.μ M.R v) ^ α := rpow_denom_pos α hq1
    have hle : (1 - q M.μ M.R v) ^ α ≤ (1 - p.toReal) ^ α :=
      Real.rpow_le_rpow (by linarith) (by linarith) hα
    have hφ : 0 ≤ phi α (q M.μ M.R v) := phi_nonneg q_nonneg hq1
    rw [h1p, phiE_of_lt hq1, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) α)]
    calc p = ENNReal.ofReal p.toReal := hp_eq
      _ ≤ ENNReal.ofReal ((1 - p.toReal) ^ α * phi α (q M.μ M.R v)) := by
          apply ENNReal.ofReal_le_ofReal
          calc p.toReal ≤ q M.μ M.R v := hqp
            _ = (1 - q M.μ M.R v) ^ α * phi α (q M.μ M.R v) := by
                rw [phi]
                field_simp
            _ ≤ (1 - p.toReal) ^ α * phi α (q M.μ M.R v) := by gcongr
  rw [ENNReal.le_div_iff_mul_le (Or.inl hp) (Or.inl hpt)]
  calc M.delta * p = ∑' v, (if M.R M.zero v then 0 else M.μ v * p) := by
        rw [delta, qE, ← ENNReal.tsum_mul_right]
        exact tsum_congr fun v => by split_ifs <;> simp
    _ ≤ ∑' v, (1 - p) ^ α * (M.μ v * phiE α (q M.μ M.R v)) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        split_ifs with hv
        · exact zero_le
        · by_cases hv0 : M.μ v = 0
          · simp [hv0]
          · calc M.μ v * p ≤ M.μ v * ((1 - p) ^ α * phiE α (q M.μ M.R v)) := by
                  gcongr
                  exact hpw v hv hv0
              _ = (1 - p) ^ α * (M.μ v * phiE α (q M.μ M.R v)) := by ring
    _ = (1 - p) ^ α * M.eta α := by rw [ENNReal.tsum_mul_left, eta, PhiD]

/-- With `μ(0) ≥ p > 0`: `ζ_α ≤ η_α / p`. -/
lemma zeta_le_eta_div (hc : M.IsCompat) {α : ℝ} (hα : 0 ≤ α) {p : ℝ≥0∞} (hp : p ≠ 0)
    (hp1 : p ≤ 1) (hμ0 : p ≤ M.μ M.zero) : M.zeta α ≤ M.eta α / p := by
  refine max_le ?_ (M.e0_le_eta_div hc hα hp hμ0)
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  rw [ENNReal.le_div_iff_mul_le (Or.inl hp) (Or.inl hpt)]
  exact mul_le_of_le_one_right' hp1

end Model

end GraphMarkovMatching.Stopped
