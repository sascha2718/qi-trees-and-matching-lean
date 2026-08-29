/-
The one-law contraction lemma at a free
exponent `α ≥ 1` and weight `δ > 0`, with abstract calculus constants:

    Φ_α(R^□, μ²) ≤ A·Φ_α + C·Φ_α²,
    A = 2L + 2(1+δ)K,          C = 2L·c_α + 5/2 + 2(1+δ⁻¹)α²,

for ANY `L` with `t/(1+t)^α ≤ L` on `[0,∞)` and ANY `K` with `t(1-t)^α ≤ K` on
`[0,1]`. The callers instantiate `L = K = 1/(2α)` (`Maxima.lean`) for `α ≥ 2`,
or the sharp pair `(1/4, 4/27)` at `α = 2`.

Built in stages:

* the weighted `ℝ≥0∞` mean inequality `(a+b)² ≤ (1+δ)a² + (1+δ⁻¹)b²`;
* real pointwise facts: `q_sq_le` (the `K`-step), `rowBound_symm`;
* the pointwise split `φ(Q) ≤ (q₀²+q₁²)/(u^α s^α) + 2c/(u^α s^α)`;
* the first-term average `≤ 2L·Φ + (2L c_α + 5/2)·Φ²`;
* the second-term average `≤ 2(1+δ)K·Φ + 2(1+δ⁻¹)α²·Φ²`, via the Fubini
  identity `𝔼[c·W(X₀)W(X₁)] = 𝔼_Y[H(Y)²]`;
* the combination.
-/
import GraphMarkovMatching.Support.Square
import GraphMarkovMatching.Support.RowBound

namespace GraphMarkovMatching.Support

open Real
open scoped ENNReal Classical

/-! ### ℝ≥0∞ arithmetic helper -/

/-- The weighted mean inequality in `ℝ≥0∞`:
`(a+b)² ≤ (1+δ)a² + (1+δ⁻¹)b²` for real `δ > 0`. Proved by reducing the
finite case through `toReal` to `add_sq_le_weighted`. -/
theorem ennreal_add_sq_le_weighted {δ : ℝ} (hδ : 0 < δ) (a b : ℝ≥0∞) :
    (a + b) ^ 2 ≤ ENNReal.ofReal (1 + δ) * a ^ 2 + ENNReal.ofReal (1 + δ⁻¹) * b ^ 2 := by
  have hδ' : 0 < δ⁻¹ := inv_pos.mpr hδ
  rcases eq_top_or_lt_top a with rfl | ha
  · have hne : ENNReal.ofReal (1 + δ) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    simp [pow_two, ENNReal.mul_top, hne]
  rcases eq_top_or_lt_top b with rfl | hb
  · have hne : ENNReal.ofReal (1 + δ⁻¹) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    simp [pow_two, ENNReal.mul_top, hne]
  have hL : (a + b) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.add_ne_top.mpr ⟨ha.ne, hb.ne⟩)
  have hR : ENNReal.ofReal (1 + δ) * a ^ 2 + ENNReal.ofReal (1 + δ⁻¹) * b ^ 2 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ha.ne),
       ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hb.ne)⟩
  rw [← ENNReal.toReal_le_toReal hL hR, ENNReal.toReal_pow,
     ENNReal.toReal_add ha.ne hb.ne,
     ENNReal.toReal_add
       (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ha.ne))
       (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hb.ne)),
     ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
     ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 + δ),
     ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 + δ⁻¹)]
  exact add_sq_le_weighted hδ

/-! ### Real pointwise facts -/

/-- The `K`-step: `q² ≤ K·φ_α(q)` on `[0,1)`, from `q² = φ_α(q)·q(1-q)^α` and the
hypothesis `q(1-q)^α ≤ K`. -/
lemma q_sq_le {α K t : ℝ} (hK : t * (1 - t) ^ α ≤ K) (h0 : 0 ≤ t) (h1 : t < 1) :
    t ^ 2 ≤ K * phi α t := by
  have hpos : 0 < (1 - t) ^ α := rpow_denom_pos α h1
  have heq : t ^ 2 = phi α t * (t * (1 - t) ^ α) := by
    rw [phi]; field_simp
  rw [heq]
  have hphi0 : 0 ≤ phi α t := phi_nonneg h0 h1
  have := mul_le_mul_of_nonneg_left hK hphi0
  nlinarith [this, hphi0]

/-- The row bound with `q₀, q₁` in either order, the denominator built from
`d = max`, `e = min`. Both sides are symmetric in `d,e`, so this follows from
`rowBound` by a case split. -/
lemma rowBound_symm {α L q₀ q₁ : ℝ} (hα : 1 ≤ α) (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (h₀0 : 0 ≤ q₀) (h₀1 : q₀ < 1) (h₁0 : 0 ≤ q₁) (h₁1 : q₁ < 1) :
    (q₀ ^ 2 + q₁ ^ 2)
        / ((1 - max q₀ q₁) ^ α * (1 + max q₀ q₁ - 2 * min q₀ q₁) ^ α)
      ≤ L * (phi α q₀ + phi α q₁)
        + (2 * L * chordConst α + 5 / 2) * (phi α q₀ * phi α q₁) := by
  rcases le_total q₀ q₁ with h | h
  · rw [max_eq_right h, min_eq_left h, add_comm (q₀ ^ 2) (q₁ ^ 2)]
    nlinarith [rowBound hα hL0 (hL q₁ h₁0) h₀0 h h₁1]
  · rw [max_eq_left h, min_eq_right h]
    nlinarith [rowBound hα hL0 (hL q₀ h₀0) h₁0 h h₀1]

/-! ### The degrees (13),(14) transported to `ℝ` -/

variable {X : Type*}

lemma cOverlap_le_one (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    cOverlap μ R x₀ x₁ ≤ 1 := by
  rw [cOverlap, ← μ.tsum_coe]
  exact ENNReal.tsum_le_tsum fun y => by split_ifs <;> simp

lemma aOverlap_ne_top (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    aOverlap μ R x₀ x₁ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top ((aOverlap_le_rE_left μ R x₀ x₁).trans rE_le_one)

lemma cOverlap_ne_top (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    cOverlap μ R x₀ x₁ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (cOverlap_le_one μ R x₀ x₁)

/-- Good-degree identity in `ℝ`: `R + a² = 2 r₀ r₁` (real degrees), from the
additive `ℝ≥0∞` identity by `toReal`. -/
lemma rE_square_toReal_add (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    (rE (prodPMF μ μ) (SquareRel R) (x₀, x₁)).toReal + (aOverlap μ R x₀ x₁).toReal ^ 2
      = 2 * ((rE μ R x₀).toReal * (rE μ R x₁).toReal) := by
  have h := rE_square_add_aOverlap_sq μ R x₀ x₁
  apply_fun ENNReal.toReal at h
  rw [ENNReal.toReal_add rE_ne_top (ENNReal.pow_ne_top (aOverlap_ne_top μ R x₀ x₁)),
      ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_mul] at h
  simpa using h

/-- Bad-degree union bound in `ℝ`: `Q ≤ q₀² + q₁² + 2c` (real degrees). -/
lemma qE_square_toReal_le (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    (qE (prodPMF μ μ) (SquareRel R) (x₀, x₁)).toReal
      ≤ (qE μ R x₀).toReal ^ 2 + (qE μ R x₁).toReal ^ 2 + 2 * (cOverlap μ R x₀ x₁).toReal := by
  have h := qE_square_le μ R x₀ x₁
  have h2c : (2 : ℝ≥0∞) * cOverlap μ R x₀ x₁ ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (cOverlap_ne_top μ R x₀ x₁)
  have hpow : ∀ z : X, qE μ R z ^ 2 ≠ ⊤ := fun z => ENNReal.pow_ne_top qE_ne_top
  have hRHS : qE μ R x₀ ^ 2 + qE μ R x₁ ^ 2 + 2 * cOverlap μ R x₀ x₁ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hpow x₀, hpow x₁⟩, h2c⟩
  have hmono := ENNReal.toReal_mono hRHS h
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hpow x₀, hpow x₁⟩) h2c,
      ENNReal.toReal_add (hpow x₀) (hpow x₁), ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_mul] at hmono
  simpa using hmono

/-! ### The pointwise split -/

/-- The pointwise decomposition on the support. With `d = max`, `e = min`,
`u = 1-d`, `s = 1+d-2e` and `c` the column overlap,

    φ_α(Q) = Q/R^α ≤ (q₀²+q₁²)/(u^α s^α) + 2c/(u^α s^α).

The good degree `R ≥ u s` comes from the identity and `a ≤ u`; the bad degree
bound is the union bound; and `R = 1 - Q` turns `φ_α(Q)` into `Q/R^α`. -/
lemma phi_Q_split {α : ℝ} (hα0 : 0 ≤ α) {μ : PMF X} {R : X → X → Prop}
    (hrefl : ∀ x, R x x)
    {x₀ x₁ : X} (hx₀ : μ x₀ ≠ 0) (hx₁ : μ x₁ ≠ 0) :
    phi α (q (prodPMF μ μ) (SquareRel R) (x₀, x₁))
      ≤ (q μ R x₀ ^ 2 + q μ R x₁ ^ 2)
          / ((1 - max (q μ R x₀) (q μ R x₁)) ^ α
             * (1 + max (q μ R x₀) (q μ R x₁) - 2 * min (q μ R x₀) (q μ R x₁)) ^ α)
        + 2 * (cOverlap μ R x₀ x₁).toReal
          * (1 - q μ R x₀) ^ (-α) * (1 - q μ R x₁) ^ (-α) := by
  set q₀ := q μ R x₀ with hq₀def
  set q₁ := q μ R x₁ with hq₁def
  set Q := q (prodPMF μ μ) (SquareRel R) (x₀, x₁) with hQdef
  have hq₀1 : q₀ < 1 := q_lt_one (hrefl x₀) hx₀
  have hq₁1 : q₁ < 1 := q_lt_one (hrefl x₁) hx₁
  have hpx : (prodPMF μ μ) (x₀, x₁) ≠ 0 := by rw [prodPMF_apply]; exact mul_ne_zero hx₀ hx₁
  have hQ1 : Q < 1 := q_lt_one (SquareRel_refl hrefl (x₀, x₁)) hpx
  have hQ0 : 0 ≤ Q := q_nonneg
  set d := max q₀ q₁ with hddef
  set e := min q₀ q₁ with hedef
  set u := 1 - d with hudef
  set v := 1 - e with hvdef
  set s := 1 + d - 2 * e with hsdef
  have hd1 : d < 1 := max_lt hq₀1 hq₁1
  have hde : e ≤ d := min_le_max
  have hu0 : 0 < u := by rw [hudef]; linarith
  have hs0 : 0 < s := by rw [hsdef]; linarith
  -- real degrees
  have hr₀eq : (rE μ R x₀).toReal = 1 - q₀ := toReal_rE_eq μ R x₀
  have hr₁eq : (rE μ R x₁).toReal = 1 - q₁ := toReal_rE_eq μ R x₁
  have hRgeq : (rE (prodPMF μ μ) (SquareRel R) (x₀, x₁)).toReal = 1 - Q :=
    toReal_rE_eq (prodPMF μ μ) (SquareRel R) (x₀, x₁)
  set a := (aOverlap μ R x₀ x₁).toReal with hadef
  set c := (cOverlap μ R x₀ x₁).toReal with hcdef
  set Rg := (rE (prodPMF μ μ) (SquareRel R) (x₀, x₁)).toReal with hRgdef
  have h13 : Rg + a ^ 2 = 2 * ((rE μ R x₀).toReal * (rE μ R x₁).toReal) :=
    rE_square_toReal_add μ R x₀ x₁
  rw [hr₀eq, hr₁eq] at h13
  have h14 : Q ≤ q₀ ^ 2 + q₁ ^ 2 + 2 * c := qE_square_toReal_le μ R x₀ x₁
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have haq₀ : a ≤ 1 - q₀ := hr₀eq ▸ ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_left μ R x₀ x₁)
  have haq₁ : a ≤ 1 - q₁ := hr₁eq ▸ ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_right μ R x₀ x₁)
  have hau : a ≤ u := by
    rw [hudef, hddef]
    have : max q₀ q₁ ≤ 1 - a := max_le (by linarith) (by linarith)
    linarith
  have hrr : (1 - q₀) * (1 - q₁) = u * v := by
    rw [hudef, hvdef, hddef, hedef]
    rcases le_total q₀ q₁ with h | h
    · rw [max_eq_right h, min_eq_left h]; ring
    · rw [max_eq_left h, min_eq_right h]
  have hsv : u * s = 2 * (u * v) - u ^ 2 := by rw [hsdef, hvdef, hudef]; ring
  have ha2 : a ^ 2 ≤ u ^ 2 := by nlinarith [hau, ha0]
  have hRgus : u * s ≤ Rg := by nlinarith [h13, hrr, ha2, hsv]
  -- turn φ(Q) into Q / R^α and bound the denominator below by u^α s^α
  have hphiQ : phi α Q = Q / Rg ^ α := by rw [phi, ← hRgeq]
  have hus0 : 0 < u * s := mul_pos hu0 hs0
  have hpow : u ^ α * s ^ α ≤ Rg ^ α := by
    rw [← Real.mul_rpow hu0.le hs0.le]
    exact Real.rpow_le_rpow hus0.le hRgus hα0
  have huspos : 0 < u ^ α * s ^ α := by
    rw [← Real.mul_rpow hu0.le hs0.le]; exact Real.rpow_pos_of_pos hus0 α
  -- the second term: `s ≥ v` lowers the denominator to `u^α v^α = r₀^α r₁^α`
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have he1 : e < 1 := lt_of_le_of_lt (min_le_left q₀ q₁) hq₀1
  have hv0 : 0 < v := by rw [hvdef]; linarith
  have hvs : v ^ α ≤ s ^ α :=
    Real.rpow_le_rpow hv0.le (by rw [hvdef, hsdef]; linarith) hα0
  have hvpos : 0 < u ^ α * v ^ α := by
    rw [← Real.mul_rpow hu0.le hv0.le]; exact Real.rpow_pos_of_pos (mul_pos hu0 hv0) α
  have huv_eq : u ^ α * v ^ α = (1 - q₀) ^ α * (1 - q₁) ^ α := by
    rw [← Real.mul_rpow hu0.le hv0.le, ← hrr, Real.mul_rpow (by linarith) (by linarith)]
  have hsecond : 2 * c / (u ^ α * s ^ α)
      ≤ 2 * c * (1 - q₀) ^ (-α) * (1 - q₁) ^ (-α) := by
    have h1 : 2 * c / (u ^ α * s ^ α) ≤ 2 * c / (u ^ α * v ^ α) :=
      div_le_div_of_nonneg_left (by linarith) hvpos
        (mul_le_mul_of_nonneg_left hvs (Real.rpow_pos_of_pos hu0 α).le)
    have h2 : 2 * c / (u ^ α * v ^ α)
        = 2 * c * (1 - q₀) ^ (-α) * (1 - q₁) ^ (-α) := by
      rw [huv_eq, Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 - q₀),
          Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 - q₁)]; ring
    linarith [h1, h2]
  rw [hphiQ]
  calc Q / Rg ^ α
      ≤ Q / (u ^ α * s ^ α) := div_le_div_of_nonneg_left hQ0 huspos hpow
    _ ≤ (q₀ ^ 2 + q₁ ^ 2 + 2 * c) / (u ^ α * s ^ α) :=
        div_le_div_of_nonneg_right h14 huspos.le
    _ = (q₀ ^ 2 + q₁ ^ 2) / (u ^ α * s ^ α) + 2 * c / (u ^ α * s ^ α) := by
        rw [add_div]
    _ ≤ (q₀ ^ 2 + q₁ ^ 2) / (u ^ α * s ^ α)
          + 2 * c * (1 - q₀) ^ (-α) * (1 - q₁) ^ (-α) := by gcongr

/-! ### Averaging machinery -/

/-- A product average splits: `𝔼_{X₀,X₁}[f(X₀) g(X₁)] = 𝔼[f]·𝔼[g]`, free in
`ℝ≥0∞` by Fubini's theorem. -/
lemma prod_avg (μ : PMF X) (f g : X → ℝ≥0∞) :
    ∑' p : X × X, μ p.1 * μ p.2 * (f p.1 * g p.2)
      = (∑' x, μ x * f x) * (∑' x, μ x * g x) := by
  rw [tsum_congr fun p : X × X => show
      μ p.1 * μ p.2 * (f p.1 * g p.2) = (μ p.1 * f p.1) * (μ p.2 * g p.2) from by ring]
  exact tsum_prod_split (fun x => μ x * f x) (fun x => μ x * g x)

/-- `Φ_α` as an average of `φ_α ∘ q`. -/
lemma Phi_eq_tsum (α : ℝ) (μ : PMF X) (R : X → X → Prop) :
    Phi α μ R = ∑' x, μ x * ENNReal.ofReal (phi α (q μ R x)) := rfl

/-- The `ℝ≥0∞` form of `rowBound_symm`: the pointwise first-term bound with `φ`
weights already coerced. -/
lemma rowBound_ofReal {α L : ℝ} (hα : 1 ≤ α) (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    {μ : PMF X} {R : X → X → Prop} (hrefl : ∀ x, R x x)
    {x₀ x₁ : X} (hx₀ : μ x₀ ≠ 0) (hx₁ : μ x₁ ≠ 0) :
    ENNReal.ofReal ((q μ R x₀ ^ 2 + q μ R x₁ ^ 2)
        / ((1 - max (q μ R x₀) (q μ R x₁)) ^ α
           * (1 + max (q μ R x₀) (q μ R x₁) - 2 * min (q μ R x₀) (q μ R x₁)) ^ α))
      ≤ ENNReal.ofReal L
          * (ENNReal.ofReal (phi α (q μ R x₀)) + ENNReal.ofReal (phi α (q μ R x₁)))
        + ENNReal.ofReal (2 * L * chordConst α + 5 / 2)
          * (ENNReal.ofReal (phi α (q μ R x₀)) * ENNReal.ofReal (phi α (q μ R x₁))) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hq₀1 : q μ R x₀ < 1 := q_lt_one (hrefl x₀) hx₀
  have hq₁1 : q μ R x₁ < 1 := q_lt_one (hrefl x₁) hx₁
  have hp₀ : 0 ≤ phi α (q μ R x₀) := phi_nonneg q_nonneg hq₀1
  have hp₁ : 0 ≤ phi α (q μ R x₁) := phi_nonneg q_nonneg hq₁1
  have hB0 : (0 : ℝ) ≤ 2 * L * chordConst α + 5 / 2 := by
    have := chordConst_nonneg hα0
    nlinarith
  have hreal := rowBound_symm hα hL0 hL q_nonneg hq₀1 q_nonneg hq₁1
  calc ENNReal.ofReal _
      ≤ ENNReal.ofReal (L * (phi α (q μ R x₀) + phi α (q μ R x₁))
          + (2 * L * chordConst α + 5 / 2) * (phi α (q μ R x₀) * phi α (q μ R x₁))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal L
          * (ENNReal.ofReal (phi α (q μ R x₀)) + ENNReal.ofReal (phi α (q μ R x₁)))
        + ENNReal.ofReal (2 * L * chordConst α + 5 / 2)
          * (ENNReal.ofReal (phi α (q μ R x₀)) * ENNReal.ofReal (phi α (q μ R x₁))) := by
        rw [ENNReal.ofReal_add (mul_nonneg hL0 (add_nonneg hp₀ hp₁))
              (mul_nonneg hB0 (mul_nonneg hp₀ hp₁)),
            ENNReal.ofReal_mul hL0, ENNReal.ofReal_add hp₀ hp₁,
            ENNReal.ofReal_mul hB0, ENNReal.ofReal_mul hp₀]

/-- The average of the first term is `≤ 2L·Φ + (2L c_α + 5/2)·Φ²`. -/
lemma firstTerm_le {α L : ℝ} (hα : 1 ≤ α) (hL0 : 0 ≤ L)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (μ : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x) :
    ∑' p : X × X, μ p.1 * μ p.2 * ENNReal.ofReal
        ((q μ R p.1 ^ 2 + q μ R p.2 ^ 2)
          / ((1 - max (q μ R p.1) (q μ R p.2)) ^ α
             * (1 + max (q μ R p.1) (q μ R p.2) - 2 * min (q μ R p.1) (q μ R p.2)) ^ α))
      ≤ 2 * ENNReal.ofReal L * Phi α μ R
        + ENNReal.ofReal (2 * L * chordConst α + 5 / 2) * Phi α μ R ^ 2 := by
  set F : X → ℝ≥0∞ := fun x => ENNReal.ofReal (phi α (q μ R x)) with hF
  set B : ℝ≥0∞ := ENNReal.ofReal (2 * L * chordConst α + 5 / 2) with hB
  -- pointwise bound into a sum of three product-form terms
  have hpt : ∀ p : X × X, μ p.1 * μ p.2 * ENNReal.ofReal
        ((q μ R p.1 ^ 2 + q μ R p.2 ^ 2)
          / ((1 - max (q μ R p.1) (q μ R p.2)) ^ α
             * (1 + max (q μ R p.1) (q μ R p.2) - 2 * min (q μ R p.1) (q μ R p.2)) ^ α))
      ≤ ENNReal.ofReal L * (μ p.1 * μ p.2 * (F p.1 * 1))
        + ENNReal.ofReal L * (μ p.1 * μ p.2 * (1 * F p.2))
        + B * (μ p.1 * μ p.2 * (F p.1 * F p.2)) := by
    intro p
    by_cases hx₀ : μ p.1 = 0
    · simp [hx₀]
    by_cases hx₁ : μ p.2 = 0
    · simp [hx₁]
    have hb := rowBound_ofReal hα hL0 hL hrefl hx₀ hx₁
    calc μ p.1 * μ p.2 * ENNReal.ofReal _
        ≤ μ p.1 * μ p.2 * (ENNReal.ofReal L * (F p.1 + F p.2) + B * (F p.1 * F p.2)) := by
          gcongr
      _ = _ := by rw [hF]; ring
  calc ∑' p : X × X, _
      ≤ ∑' p : X × X, (ENNReal.ofReal L * (μ p.1 * μ p.2 * (F p.1 * 1))
          + ENNReal.ofReal L * (μ p.1 * μ p.2 * (1 * F p.2))
          + B * (μ p.1 * μ p.2 * (F p.1 * F p.2))) := ENNReal.tsum_le_tsum hpt
    _ = 2 * ENNReal.ofReal L * Phi α μ R + B * Phi α μ R ^ 2 := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
            ENNReal.tsum_mul_left, prod_avg μ F (fun _ => 1), prod_avg μ (fun _ => 1) F,
            prod_avg μ F F]
        have hΦ : (∑' x, μ x * F x) = Phi α μ R := rfl
        have h1 : (∑' x, μ x * (fun _ : X => (1 : ℝ≥0∞)) x) = 1 := by
          simp only [mul_one]; exact μ.tsum_coe
        rw [hΦ, h1]; ring

/-! ### The second term: `W`, `H`, `K` and the Fubini swap -/

/-- `W(x) = r(x)^{-α} = (1-q)^{-α}`, as `ℝ≥0∞`. -/
noncomputable def Wnn (α : ℝ) (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - q μ R x) ^ (-α))

/-- `H(y) = 𝔼_X[𝟙_{X⋠y} W(X)]`. -/
noncomputable def Hnn (α : ℝ) (μ : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, μ x * (if ¬ R x y then Wnn α μ R x else 0)

/-- `Λ(y) = 𝔼_X[𝟙_{X⋠y} φ_α(q(X))]`, the dead-set weight sum. -/
noncomputable def Lam (α : ℝ) (μ : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, μ x * (if ¬ R x y then ENNReal.ofReal (phi α (q μ R x)) else 0)

/-- The Fubini swap: `𝔼[c·W(X₀)W(X₁)] = 𝔼_Y[H(Y)²]`. Expand `c` as a `Y`-sum,
pull it out, `tsum_comm`, then split the pair-sum as a square. -/
lemma fubini_swap (α : ℝ) (μ : PMF X) (R : X → X → Prop) :
    ∑' p : X × X, μ p.1 * μ p.2 * (cOverlap μ R p.1 p.2 * (Wnn α μ R p.1 * Wnn α μ R p.2))
      = ∑' y, μ y * Hnn α μ R y ^ 2 := by
  have hstep : ∀ p : X × X,
      μ p.1 * μ p.2 * (cOverlap μ R p.1 p.2 * (Wnn α μ R p.1 * Wnn α μ R p.2))
        = ∑' y, μ p.1 * μ p.2 * (Wnn α μ R p.1 * Wnn α μ R p.2)
            * (if ¬ R p.1 y ∧ ¬ R p.2 y then μ y else 0) := by
    intro p; rw [cOverlap, ENNReal.tsum_mul_left]; ring
  simp_rw [hstep]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun y => ?_
  rw [tsum_congr fun p : X × X => show
      μ p.1 * μ p.2 * (Wnn α μ R p.1 * Wnn α μ R p.2)
          * (if ¬ R p.1 y ∧ ¬ R p.2 y then μ y else 0)
        = μ y * ((μ p.1 * (if ¬ R p.1 y then Wnn α μ R p.1 else 0))
                 * (μ p.2 * (if ¬ R p.2 y then Wnn α μ R p.2 else 0)))
      from by by_cases h1 : R p.1 y <;> by_cases h2 : R p.2 y <;> simp [h1, h2]; ring]
  rw [ENNReal.tsum_mul_left, tsum_prod_split
        (fun x => μ x * (if ¬ R x y then Wnn α μ R x else 0))
        (fun x => μ x * (if ¬ R x y then Wnn α μ R x else 0)), ← pow_two, Hnn]

/-- The tangent bound `W(x) ≤ 1 + α·φ_α(q(x))`, coerced to `ℝ≥0∞`. Holds for
all `x`: on the support by `rpow_neg_alpha_le`, and where `q = 1` (`W = 0`)
trivially, using `α ≥ 1` to know `-α ≠ 0`. -/
lemma Wnn_le {α : ℝ} (hα : 1 ≤ α) (μ : PMF X) (R : X → X → Prop) (x : X) :
    Wnn α μ R x ≤ 1 + ENNReal.ofReal α * ENNReal.ofReal (phi α (q μ R x)) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  rw [Wnn]
  by_cases hq : q μ R x < 1
  · have hφ : 0 ≤ phi α (q μ R x) := phi_nonneg q_nonneg hq
    calc ENNReal.ofReal ((1 - q μ R x) ^ (-α))
        ≤ ENNReal.ofReal (1 + α * phi α (q μ R x)) :=
          ENNReal.ofReal_le_ofReal (rpow_neg_alpha_le hα hq)
      _ = 1 + ENNReal.ofReal α * ENNReal.ofReal (phi α (q μ R x)) := by
          rw [ENNReal.ofReal_add (by norm_num) (mul_nonneg hα0 hφ),
              ENNReal.ofReal_mul hα0, ENNReal.ofReal_one]
  · have hq1 : q μ R x = 1 := le_antisymm q_le_one (not_lt.mp hq)
    have h0 : (1 : ℝ) - q μ R x = 0 := by rw [hq1]; ring
    rw [h0, Real.zero_rpow (ne_of_lt (by linarith : (-α : ℝ) < 0)), ENNReal.ofReal_zero]
    exact zero_le

/-- `Λ(y) ≤ Φ_α`: drop the indicator. -/
lemma Lam_le_Phi (α : ℝ) (μ : PMF X) (R : X → X → Prop) (y : X) :
    Lam α μ R y ≤ Phi α μ R := by
  rw [Lam, Phi_eq_tsum]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases h : R x y <;> simp [h]

/-- `H(y) ≤ q(y) + α·K(y)`. Uses `Wnn_le` per `x` and symmetry of `R` (via
`tsum_not_rel_eq_qE`) to identify `𝔼_X 𝟙_{X⋠y}` with `q(y)`. -/
lemma Hnn_le {α : ℝ} (hα : 1 ≤ α) (μ : PMF X) (R : X → X → Prop)
    (hsymm : ∀ a b, R a b → R b a) (y : X) :
    Hnn α μ R y ≤ qE μ R y + ENNReal.ofReal α * Lam α μ R y := by
  have hbr : ∀ x, μ x * (if ¬ R x y then Wnn α μ R x else 0)
      ≤ (if ¬ R x y then μ x else 0)
        + ENNReal.ofReal α
          * (μ x * (if ¬ R x y then ENNReal.ofReal (phi α (q μ R x)) else 0)) := by
    intro x
    by_cases h : R x y
    · simp [h]
    · simp only [if_pos h]
      calc μ x * Wnn α μ R x
          ≤ μ x * (1 + ENNReal.ofReal α * ENNReal.ofReal (phi α (q μ R x))) := by
            gcongr; exact Wnn_le hα μ R x
        _ = μ x + ENNReal.ofReal α * (μ x * ENNReal.ofReal (phi α (q μ R x))) := by ring
  have hqe : (∑' x, if ¬ R x y then μ x else 0) = qE μ R y := by
    rw [← tsum_not_rel_eq_qE hsymm]
    exact tsum_congr fun x => by by_cases h : R x y <;> simp [h]
  calc Hnn α μ R y
      ≤ ∑' x, ((if ¬ R x y then μ x else 0)
          + ENNReal.ofReal α
            * (μ x * (if ¬ R x y then ENNReal.ofReal (phi α (q μ R x)) else 0))) :=
        ENNReal.tsum_le_tsum hbr
    _ = qE μ R y + ENNReal.ofReal α * Lam α μ R y := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hqe, Lam]

/-! ### Averaged second-term bounds -/

/-- `𝔼[Λ(Y)²] ≤ Φ²`. -/
lemma ELamsq_le (α : ℝ) (μ : PMF X) (R : X → X → Prop) :
    ∑' y, μ y * Lam α μ R y ^ 2 ≤ Phi α μ R ^ 2 := by
  calc ∑' y, μ y * Lam α μ R y ^ 2
      ≤ ∑' y, μ y * Phi α μ R ^ 2 :=
        ENNReal.tsum_le_tsum fun y => by gcongr; exact Lam_le_Phi α μ R y
    _ = Phi α μ R ^ 2 := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- `𝔼[q(Y)²] ≤ K·Φ` (uses reflexivity, via `q_lt_one` on the support, and the
`K`-hypothesis). -/
lemma Eqsq_le {α K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (μ : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x) :
    ∑' y, μ y * qE μ R y ^ 2 ≤ ENNReal.ofReal K * Phi α μ R := by
  have hpt : ∀ y, μ y * qE μ R y ^ 2
      ≤ ENNReal.ofReal K * (μ y * ENNReal.ofReal (phi α (q μ R y))) := by
    intro y
    by_cases hy : μ y = 0
    · simp [hy]
    · have hq1 : q μ R y < 1 := q_lt_one (hrefl y) hy
      have hqE : qE μ R y = ENNReal.ofReal (q μ R y) := (ENNReal.ofReal_toReal qE_ne_top).symm
      rw [hqE, ← ENNReal.ofReal_pow q_nonneg]
      calc μ y * ENNReal.ofReal (q μ R y ^ 2)
          ≤ μ y * ENNReal.ofReal (K * phi α (q μ R y)) := by
            gcongr
            exact q_sq_le (hK _ q_nonneg q_le_one) q_nonneg hq1
        _ = ENNReal.ofReal K * (μ y * ENNReal.ofReal (phi α (q μ R y))) := by
            rw [ENNReal.ofReal_mul hK0]; ring
  calc ∑' y, μ y * qE μ R y ^ 2
      ≤ ∑' y, ENNReal.ofReal K * (μ y * ENNReal.ofReal (phi α (q μ R y))) :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal K * Phi α μ R := by rw [ENNReal.tsum_mul_left, ← Phi_eq_tsum]

/-- The averaged `H²`-bound:
`2·𝔼[H(Y)²] ≤ 2(1+δ)K·Φ + 2(1+δ⁻¹)α²·Φ²`. Combines `Hnn_le`, the weighted
mean inequality, `ELamsq_le` and `Eqsq_le`. -/
lemma two_EHsq_le {α δ K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ) (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (μ : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (hsymm : ∀ a b, R a b → R b a) :
    2 * ∑' y, μ y * Hnn α μ R y ^ 2
      ≤ ENNReal.ofReal (2 * (1 + δ) * K) * Phi α μ R
        + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * Phi α μ R ^ 2 := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hδ' : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδ
  have hHsq : ∀ y, Hnn α μ R y ^ 2
      ≤ ENNReal.ofReal (1 + δ) * qE μ R y ^ 2
        + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α * Lam α μ R y) ^ 2 := by
    intro y
    calc Hnn α μ R y ^ 2
        ≤ (qE μ R y + ENNReal.ofReal α * Lam α μ R y) ^ 2 :=
          pow_le_pow_left' (Hnn_le hα μ R hsymm y) 2
      _ ≤ ENNReal.ofReal (1 + δ) * qE μ R y ^ 2
            + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α * Lam α μ R y) ^ 2 :=
          ennreal_add_sq_le_weighted hδ _ _
  have hdist : ∑' y, μ y * (ENNReal.ofReal (1 + δ) * qE μ R y ^ 2
        + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α * Lam α μ R y) ^ 2)
      = ENNReal.ofReal (1 + δ) * (∑' y, μ y * qE μ R y ^ 2)
        + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2
          * ∑' y, μ y * Lam α μ R y ^ 2 := by
    rw [tsum_congr fun y => show
        μ y * (ENNReal.ofReal (1 + δ) * qE μ R y ^ 2
            + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α * Lam α μ R y) ^ 2)
          = ENNReal.ofReal (1 + δ) * (μ y * qE μ R y ^ 2)
            + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2
              * (μ y * Lam α μ R y ^ 2) from by ring,
      ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  have c₁ : ENNReal.ofReal (2 * (1 + δ) * K)
      = 2 * (ENNReal.ofReal (1 + δ) * ENNReal.ofReal K) := by
    rw [show (2 : ℝ) * (1 + δ) * K = 2 * ((1 + δ) * K) from by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 + δ), ENNReal.ofReal_ofNat]
  have c₂ : ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2)
      = 2 * (ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2) := by
    rw [show (2 : ℝ) * (1 + δ⁻¹) * α ^ 2 = 2 * ((1 + δ⁻¹) * α ^ 2) from by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 + δ⁻¹),
        ENNReal.ofReal_pow hα0, ENNReal.ofReal_ofNat]
  calc 2 * ∑' y, μ y * Hnn α μ R y ^ 2
      ≤ 2 * ∑' y, μ y * (ENNReal.ofReal (1 + δ) * qE μ R y ^ 2
          + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α * Lam α μ R y) ^ 2) := by
        gcongr with y; exact hHsq y
    _ = 2 * ENNReal.ofReal (1 + δ) * (∑' y, μ y * qE μ R y ^ 2)
          + 2 * (ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2)
            * ∑' y, μ y * Lam α μ R y ^ 2 := by rw [hdist]; ring
    _ ≤ 2 * ENNReal.ofReal (1 + δ) * (ENNReal.ofReal K * Phi α μ R)
          + 2 * (ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2) * Phi α μ R ^ 2 := by
        gcongr
        · exact Eqsq_le hK0 hK μ R hrefl
        · exact ELamsq_le α μ R
    _ = ENNReal.ofReal (2 * (1 + δ) * K) * Phi α μ R
          + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * Phi α μ R ^ 2 := by
        rw [c₁, c₂]; ring

/-- The average of the second term is `≤ 2(1+δ)K·Φ + 2(1+δ⁻¹)α²·Φ²`. -/
lemma secondTerm_le {α δ K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ) (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (μ : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (hsymm : ∀ a b, R a b → R b a) :
    ∑' p : X × X, μ p.1 * μ p.2 * ENNReal.ofReal
        (2 * (cOverlap μ R p.1 p.2).toReal
          * (1 - q μ R p.1) ^ (-α) * (1 - q μ R p.2) ^ (-α))
      ≤ ENNReal.ofReal (2 * (1 + δ) * K) * Phi α μ R
        + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * Phi α μ R ^ 2 := by
  have hpt : ∀ p : X × X, μ p.1 * μ p.2 * ENNReal.ofReal
        (2 * (cOverlap μ R p.1 p.2).toReal
          * (1 - q μ R p.1) ^ (-α) * (1 - q μ R p.2) ^ (-α))
      = 2 * (μ p.1 * μ p.2 * (cOverlap μ R p.1 p.2 * (Wnn α μ R p.1 * Wnn α μ R p.2))) := by
    intro p
    have hW₀ : (0 : ℝ) ≤ (1 - q μ R p.1) ^ (-α) :=
      Real.rpow_nonneg (sub_nonneg.mpr q_le_one) _
    simp only [Wnn]
    rw [show (2 : ℝ) * (cOverlap μ R p.1 p.2).toReal
          * (1 - q μ R p.1) ^ (-α) * (1 - q μ R p.2) ^ (-α)
        = 2 * ((cOverlap μ R p.1 p.2).toReal
          * ((1 - q μ R p.1) ^ (-α) * (1 - q μ R p.2) ^ (-α))) from by ring,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_mul hW₀, ENNReal.ofReal_toReal (cOverlap_ne_top μ R p.1 p.2),
      ENNReal.ofReal_ofNat]
    ring
  simp_rw [hpt]
  rw [ENNReal.tsum_mul_left, fubini_swap]
  exact two_EHsq_le hα hδ hK0 hK μ R hrefl hsymm

/-! ### The contraction lemma -/

/-- **The one-law contraction lemma at exponent `α`**:

    Φ_α(R^□, μ²) ≤ (2L + 2(1+δ)K)·Φ_α + (2L c_α + 5/2 + 2(1+δ⁻¹)α²)·Φ_α²,

for any `L` bounding `t/(1+t)^α` on `[0,∞)` and any `K` bounding `t(1-t)^α` on
`[0,1]`. The linear coefficient `A_δ(α) = 2L + 2(1+δ)K` is the same as the
linear four-law constant of `arbitrary_offspring_matching.tex` `thm:four-law`. -/
theorem Phi_square_le {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hK0 : 0 ≤ K)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (μ : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (hsymm : ∀ a b, R a b → R b a) :
    Phi α (prodPMF μ μ) (SquareRel R)
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * Phi α μ R
        + ENNReal.ofReal (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
          * Phi α μ R ^ 2 := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hδ' : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδ
  have hpt : ∀ p : X × X,
      prodPMF μ μ p * ENNReal.ofReal (phi α (q (prodPMF μ μ) (SquareRel R) p))
        ≤ μ p.1 * μ p.2 * ENNReal.ofReal
            ((q μ R p.1 ^ 2 + q μ R p.2 ^ 2)
              / ((1 - max (q μ R p.1) (q μ R p.2)) ^ α
                 * (1 + max (q μ R p.1) (q μ R p.2) - 2 * min (q μ R p.1) (q μ R p.2)) ^ α))
          + μ p.1 * μ p.2 * ENNReal.ofReal
            (2 * (cOverlap μ R p.1 p.2).toReal
              * (1 - q μ R p.1) ^ (-α) * (1 - q μ R p.2) ^ (-α)) := by
    intro p
    by_cases hx₀ : μ p.1 = 0
    · simp [prodPMF_apply, hx₀]
    by_cases hx₁ : μ p.2 = 0
    · simp [prodPMF_apply, hx₁]
    rw [prodPMF_apply, ← mul_add]
    gcongr
    calc ENNReal.ofReal (phi α (q (prodPMF μ μ) (SquareRel R) p))
        ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal (phi_Q_split hα0 hrefl hx₀ hx₁)
      _ ≤ _ := ENNReal.ofReal_add_le
  have hmerge₁ : 2 * ENNReal.ofReal L * Phi α μ R
        + ENNReal.ofReal (2 * (1 + δ) * K) * Phi α μ R
      = ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * Phi α μ R := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ← add_mul]
    congr 2
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hmerge₂ : ENNReal.ofReal (2 * L * chordConst α + 5 / 2) * Phi α μ R ^ 2
        + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * Phi α μ R ^ 2
      = ENNReal.ofReal (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
          * Phi α μ R ^ 2 := by
    have hB0 : (0 : ℝ) ≤ 2 * L * chordConst α + 5 / 2 := by
      have := chordConst_nonneg hα0
      nlinarith
    rw [ENNReal.ofReal_add hB0 (by positivity), ← add_mul]
  calc Phi α (prodPMF μ μ) (SquareRel R)
      ≤ ∑' p : X × X, (μ p.1 * μ p.2 * ENNReal.ofReal
            ((q μ R p.1 ^ 2 + q μ R p.2 ^ 2)
              / ((1 - max (q μ R p.1) (q μ R p.2)) ^ α
                 * (1 + max (q μ R p.1) (q μ R p.2) - 2 * min (q μ R p.1) (q μ R p.2)) ^ α))
          + μ p.1 * μ p.2 * ENNReal.ofReal
            (2 * (cOverlap μ R p.1 p.2).toReal
              * (1 - q μ R p.1) ^ (-α) * (1 - q μ R p.2) ^ (-α))) :=
        ENNReal.tsum_le_tsum hpt
    _ = (∑' p : X × X, μ p.1 * μ p.2 * ENNReal.ofReal
            ((q μ R p.1 ^ 2 + q μ R p.2 ^ 2)
              / ((1 - max (q μ R p.1) (q μ R p.2)) ^ α
                 * (1 + max (q μ R p.1) (q μ R p.2) - 2 * min (q μ R p.1) (q μ R p.2)) ^ α)))
          + ∑' p : X × X, μ p.1 * μ p.2 * ENNReal.ofReal
            (2 * (cOverlap μ R p.1 p.2).toReal
              * (1 - q μ R p.1) ^ (-α) * (1 - q μ R p.2) ^ (-α)) := ENNReal.tsum_add
    _ ≤ (2 * ENNReal.ofReal L * Phi α μ R
            + ENNReal.ofReal (2 * L * chordConst α + 5 / 2) * Phi α μ R ^ 2)
          + (ENNReal.ofReal (2 * (1 + δ) * K) * Phi α μ R
            + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * Phi α μ R ^ 2) := by
        gcongr
        · exact firstTerm_le hα hL0 hL μ R hrefl
        · exact secondTerm_le hα hδ hK0 hK μ R hrefl hsymm
    _ = ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * Phi α μ R
          + ENNReal.ofReal (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
            * Phi α μ R ^ 2 := by
        rw [← hmerge₁, ← hmerge₂]; ring

end GraphMarkovMatching.Support
