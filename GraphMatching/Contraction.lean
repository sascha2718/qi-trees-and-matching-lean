/-
`sec:contraction` of `graph_matching_selfcontained.tex`, the contraction `thm:contraction`
(eqs `eq:one-step`,`eq:strict`). This assembles the pieces proved in `Square.lean` (the good and
bad degrees `eq:R-exact`, `eq:Q-union`) and `RowBound.lean` (the row-bound
`eq:row-bound`) into

    Φ_α(R^□, μ²) ≤ A_α·Φ_α + B_α·Φ_α²,     A_α = 2L_α + 4K_α,  B_α = M_α + 4α²,

and, at `alpha = 5/2`, where `A_α < 7/8` and `B_α < 29`, the corollary
`Φ ≤ 1/256 ⇒ Φ(R^□,μ²) ≤ (253/256) Φ`.

Built in stages:

* real pointwise facts: `ennreal_add_sq_le`, `q_sq_le`, `rowBound_symm`;
* the pointwise split `φ(q^□) ≤ (q₀²+q₁²)/(u^α s^α) + 2c/(u^α s^α)`;
* the first-term average `≤ 2L_αΦ + M_αΦ²`;
* the second-term average `≤ 4K_αΦ + 4α²Φ²`, via the Fubini identity
  `𝔼[c·W(X₀)W(X₁)] = 𝔼_Y[H(Y)²]`;
* the combination.
-/
import GraphMatching.Square
import GraphMatching.RowBound

namespace GraphMatching

open Real
open scoped ENNReal Classical

variable {α : ℝ}

/-! ### ℝ≥0∞ arithmetic helper -/

/-- AM-GM in `ℝ≥0∞`: `(a+b)² ≤ 2(a²+b²)`. Not covered by `add_sq_le` (which needs
a strict-ordered ring); proved by reducing the finite case through `toReal`. -/
theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  rcases eq_top_or_lt_top a with rfl | ha
  · simp [pow_two]
  rcases eq_top_or_lt_top b with rfl | hb
  · simp [pow_two]
  have hL : (a + b) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.add_ne_top.mpr ⟨ha.ne, hb.ne⟩)
  have hR : 2 * (a ^ 2 + b ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp)
      (ENNReal.add_ne_top.mpr ⟨ENNReal.pow_ne_top ha.ne, ENNReal.pow_ne_top hb.ne⟩)
  rw [← ENNReal.toReal_le_toReal hL hR, ENNReal.toReal_pow,
     ENNReal.toReal_add ha.ne hb.ne, ENNReal.toReal_mul,
     ENNReal.toReal_add (ENNReal.pow_ne_top ha.ne) (ENNReal.pow_ne_top hb.ne),
     ENNReal.toReal_pow, ENNReal.toReal_pow]
  nlinarith [sq_nonneg (a.toReal - b.toReal), ENNReal.toReal_nonneg (a := a),
    ENNReal.toReal_nonneg (a := b), show ((2 : ℝ≥0∞).toReal = 2) by simp]

/-! ### Real pointwise facts -/

/-- **`eq:kappa` in use**: `q² ≤ (1/8)·φ(q)` on `[0,1)`. From `q² = φ(q)·q(1-q)^α`
and `K_bound` (`q(1-q)^α ≤ 1/8`). This is the step `𝔼[q²] ≤ K_αΦ` in
one-summand form, with the rational `K_α ≤ 1/8`. -/
lemma q_sq_le (hα : 1 ≤ α) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    t ^ 2 ≤ KA α * phiA α t := by
  have hα0 : (0:ℝ) ≤ α := by linarith
  have hk := le_KA hα0 h0 h1.le
  have hpos : 0 < (1 - t) ^ α := phiA_denom_pos α h1
  have heq : t ^ 2 = phiA α t * (t * (1 - t) ^ α) := by
    rw [phiA]; field_simp
  rw [heq]
  have := mul_le_mul_of_nonneg_left hk (phiA_nonneg α h0 h1)
  nlinarith [this, phiA_nonneg α h0 h1]

/-- **`eq:W-bound` in use**: the tangent bound `W(x) = (1-q)^{-α} ≤ 1 + α·φ(q)` on
`[0,1)`. This is `rpow_neg_alpha_le`. -/
lemma W_le (hα : 1 ≤ α) {t : ℝ} (h1 : t < 1) : (1 - t) ^ (-α) ≤ 1 + α * phiA α t :=
  rpow_neg_alpha_leA hα h1

/-- **`eq:row-bound` symmetrised**: the row-bound with `q₀, q₁` in either order, the
denominator built from `d = max`, `e = min`. Both sides of `eq:row-bound` are symmetric in
`d,e`, so this follows from `rowBound` by a case split. -/
lemma rowBound_symm (hα : 1 ≤ α) {q₀ q₁ : ℝ} (h₀0 : 0 ≤ q₀) (h₀1 : q₀ < 1)
    (h₁0 : 0 ≤ q₁) (h₁1 : q₁ < 1) :
    (q₀ ^ 2 + q₁ ^ 2)
        / ((1 - max q₀ q₁) ^ α * (1 + max q₀ q₁ - 2 * min q₀ q₁) ^ α)
      ≤ LA α * (phiA α q₀ + phiA α q₁) + MA α * (phiA α q₀ * phiA α q₁) := by
  rcases le_total q₀ q₁ with h | h
  · rw [max_eq_right h, min_eq_left h, add_comm (q₀ ^ 2) (q₁ ^ 2)]
    nlinarith [rowBoundA hα h₀0 h h₁1]
  · rw [max_eq_left h, min_eq_right h]
    exact rowBoundA hα h₁0 h h₀1

/-! ### The degrees `eq:R-exact`, `eq:Q-union` transported to `ℝ` -/

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

/-- **`eq:R-exact`** in `ℝ`: `r^□ + a² = 2 r₀ r₁` (real degrees), from the additive
`ℝ≥0∞` identity by `toReal`. -/
lemma rE_square_toReal_add (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    (rE (prodPMF μ μ) (SquareRel R) (x₀, x₁)).toReal + (aOverlap μ R x₀ x₁).toReal ^ 2
      = 2 * ((rE μ R x₀).toReal * (rE μ R x₁).toReal) := by
  have h := rE_square_add_aOverlap_sq μ R x₀ x₁
  apply_fun ENNReal.toReal at h
  rw [ENNReal.toReal_add rE_ne_top (ENNReal.pow_ne_top (aOverlap_ne_top μ R x₀ x₁)),
      ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_mul] at h
  simpa using h

/-- **`eq:Q-union`** in `ℝ`: `q^□ ≤ q₀² + q₁² + 2c` (real degrees), from the `ℝ≥0∞`
union bound by `toReal` monotonicity. -/
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

/-! ### The pointwise split, `eq:iid-split` -/

/-- **`eq:iid-split`**: the pointwise decomposition on the support. With `d = max`,
`e = min`, `u = 1-d`, `s = 1+d-2e` and `c` the column overlap,

    φ(q^□) = q^□/(r^□)^α ≤ (q₀²+q₁²)/(u^α s^α) + 2c/(u^α s^α).

The good degree `r^□ ≥ u s` comes from `eq:R-exact` and `a ≤ u`; the bad degree bound
is `eq:Q-union`; and `r^□ = 1 - q^□` turns `φ(q^□)` into `q^□/(r^□)^α`. -/
lemma phi_Q_split (hα : 1 ≤ α) {μ : PMF X} {R : X → X → Prop} (hrefl : ∀ x, R x x)
    {x₀ x₁ : X} (hx₀ : μ x₀ ≠ 0) (hx₁ : μ x₁ ≠ 0) :
    phiA α (q (prodPMF μ μ) (SquareRel R) (x₀, x₁))
      ≤ (q μ R x₀ ^ 2 + q μ R x₁ ^ 2)
          / ((1 - max (q μ R x₀) (q μ R x₁)) ^ α
             * (1 + max (q μ R x₀) (q μ R x₁) - 2 * min (q μ R x₀) (q μ R x₁)) ^ α)
        + 2 * (cOverlap μ R x₀ x₁).toReal
          * (1 - q μ R x₀) ^ (-α) * (1 - q μ R x₁) ^ (-α) := by
  set q₀ := q μ R x₀ with hq₀def
  set q₁ := q μ R x₁ with hq₁def
  set qSq := q (prodPMF μ μ) (SquareRel R) (x₀, x₁) with hqSqdef
  have hq₀1 : q₀ < 1 := q_lt_one (hrefl x₀) hx₀
  have hq₁1 : q₁ < 1 := q_lt_one (hrefl x₁) hx₁
  have hpx : (prodPMF μ μ) (x₀, x₁) ≠ 0 := by rw [prodPMF_apply]; exact mul_ne_zero hx₀ hx₁
  have hqSq1 : qSq < 1 := q_lt_one (SquareRel_refl hrefl (x₀, x₁)) hpx
  have hqSq0 : 0 ≤ qSq := q_nonneg
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
  have hrSqeq : (rE (prodPMF μ μ) (SquareRel R) (x₀, x₁)).toReal = 1 - qSq :=
    toReal_rE_eq (prodPMF μ μ) (SquareRel R) (x₀, x₁)
  set a := (aOverlap μ R x₀ x₁).toReal with hadef
  set c := (cOverlap μ R x₀ x₁).toReal with hcdef
  set rSq := (rE (prodPMF μ μ) (SquareRel R) (x₀, x₁)).toReal with hrSqdef
  have h13 : rSq + a ^ 2 = 2 * ((rE μ R x₀).toReal * (rE μ R x₁).toReal) :=
    rE_square_toReal_add μ R x₀ x₁
  rw [hr₀eq, hr₁eq] at h13
  have h14 : qSq ≤ q₀ ^ 2 + q₁ ^ 2 + 2 * c := qE_square_toReal_le μ R x₀ x₁
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
  have hrSqus : u * s ≤ rSq := by nlinarith [h13, hrr, ha2, hsv]
  -- turn φ(q^□) into q^□/(r^□)^α and bound the denominator below by u^α s^α
  have hphiqSq : phiA α qSq = qSq / rSq ^ α := by rw [phiA, ← hrSqeq]
  have hus0 : 0 < u * s := mul_pos hu0 hs0
  have hpow : u ^ α * s ^ α ≤ rSq ^ α := by
    rw [← Real.mul_rpow hu0.le hs0.le]
    exact Real.rpow_le_rpow hus0.le hrSqus (le_trans zero_le_one hα)
  have huspos : 0 < u ^ α * s ^ α := by
    rw [← Real.mul_rpow hu0.le hs0.le]; exact Real.rpow_pos_of_pos hus0 α
  -- the second term: `s ≥ v` lowers the denominator to `u^α v^α = r₀^α r₁^α`
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have he1 : e < 1 := lt_of_le_of_lt (min_le_left q₀ q₁) hq₀1
  have hv0 : 0 < v := by rw [hvdef]; linarith
  have hvs : v ^ α ≤ s ^ α :=
    Real.rpow_le_rpow hv0.le (by rw [hvdef, hsdef]; linarith) (le_trans zero_le_one hα)
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
  rw [hphiqSq]
  calc qSq / rSq ^ α
      ≤ qSq / (u ^ α * s ^ α) := div_le_div_of_nonneg_left hqSq0 huspos hpow
    _ ≤ (q₀ ^ 2 + q₁ ^ 2 + 2 * c) / (u ^ α * s ^ α) :=
        div_le_div_of_nonneg_right h14 huspos.le
    _ = (q₀ ^ 2 + q₁ ^ 2) / (u ^ α * s ^ α) + 2 * c / (u ^ α * s ^ α) := by
        rw [add_div]
    _ ≤ (q₀ ^ 2 + q₁ ^ 2) / (u ^ α * s ^ α)
          + 2 * c * (1 - q₀) ^ (-α) * (1 - q₁) ^ (-α) := by gcongr

/-! ### Averaging machinery -/

/-- A product average splits: `𝔼_{X₀,X₁}[f(X₀) g(X₁)] = 𝔼[f]·𝔼[g]`, the paper's
"independence of `X₀,X₁`", free in `ℝ≥0∞` by Fubini's theorem. -/
lemma prod_avg (μ : PMF X) (f g : X → ℝ≥0∞) :
    ∑' p : X × X, μ p.1 * μ p.2 * (f p.1 * g p.2)
      = (∑' x, μ x * f x) * (∑' x, μ x * g x) := by
  rw [tsum_congr fun p : X × X => show
      μ p.1 * μ p.2 * (f p.1 * g p.2) = (μ p.1 * f p.1) * (μ p.2 * g p.2) from by ring]
  exact tsum_prod_split (fun x => μ x * f x) (fun x => μ x * g x)

/-- `Φ` as an average of `φ∘q`. -/
lemma PhiA_eq_tsum (α : ℝ) (μ : PMF X) (R : X → X → Prop) :
    PhiA α μ R = ∑' x, μ x * ENNReal.ofReal (phiA α (q μ R x)) := rfl

/-- The `ℝ≥0∞` form of `rowBound_symm`: the pointwise first-term bound with `φ`
weights already coerced. -/
lemma rowBound_ofReal (hα : 1 ≤ α) {μ : PMF X} {R : X → X → Prop} (hrefl : ∀ x, R x x)
    {x₀ x₁ : X} (hx₀ : μ x₀ ≠ 0) (hx₁ : μ x₁ ≠ 0) :
    ENNReal.ofReal ((q μ R x₀ ^ 2 + q μ R x₁ ^ 2)
        / ((1 - max (q μ R x₀) (q μ R x₁)) ^ α
           * (1 + max (q μ R x₀) (q μ R x₁) - 2 * min (q μ R x₀) (q μ R x₁)) ^ α))
      ≤ ENNReal.ofReal (LA α)
          * (ENNReal.ofReal (phiA α (q μ R x₀)) + ENNReal.ofReal (phiA α (q μ R x₁)))
        + ENNReal.ofReal (MA α)
          * (ENNReal.ofReal (phiA α (q μ R x₀)) * ENNReal.ofReal (phiA α (q μ R x₁))) := by
  have hα0 : (0:ℝ) ≤ α := by linarith
  have hL : (0:ℝ) ≤ LA α := LA_nonneg hα0
  have hM : (0:ℝ) ≤ MA α := MA_nonneg α
  have hq₀1 : q μ R x₀ < 1 := q_lt_one (hrefl x₀) hx₀
  have hq₁1 : q μ R x₁ < 1 := q_lt_one (hrefl x₁) hx₁
  have hp₀ : 0 ≤ phiA α (q μ R x₀) := phiA_nonneg α q_nonneg hq₀1
  have hp₁ : 0 ≤ phiA α (q μ R x₁) := phiA_nonneg α q_nonneg hq₁1
  have hreal := rowBound_symm hα q_nonneg hq₀1 q_nonneg hq₁1
  calc ENNReal.ofReal _
      ≤ ENNReal.ofReal (LA α * (phiA α (q μ R x₀) + phiA α (q μ R x₁))
          + MA α * (phiA α (q μ R x₀) * phiA α (q μ R x₁))) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (LA α)
          * (ENNReal.ofReal (phiA α (q μ R x₀)) + ENNReal.ofReal (phiA α (q μ R x₁)))
        + ENNReal.ofReal (MA α)
          * (ENNReal.ofReal (phiA α (q μ R x₀)) * ENNReal.ofReal (phiA α (q μ R x₁))) := by
        rw [ENNReal.ofReal_add (mul_nonneg hL (add_nonneg hp₀ hp₁))
              (mul_nonneg hM (mul_nonneg hp₀ hp₁)),
            ENNReal.ofReal_mul hL, ENNReal.ofReal_add hp₀ hp₁,
            ENNReal.ofReal_mul hM, ENNReal.ofReal_mul hp₀]

/-- **`eq:first-final`**: the average of the first term is `≤ 2L_αΦ + 4Φ²`. -/
lemma firstTerm_le (hα : 1 ≤ α) (μ : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x) :
    ∑' p : X × X, μ p.1 * μ p.2 * ENNReal.ofReal
        ((q μ R p.1 ^ 2 + q μ R p.2 ^ 2)
          / ((1 - max (q μ R p.1) (q μ R p.2)) ^ α
             * (1 + max (q μ R p.1) (q μ R p.2) - 2 * min (q μ R p.1) (q μ R p.2)) ^ α))
      ≤ 2 * ENNReal.ofReal (LA α) * PhiA α μ R + ENNReal.ofReal (MA α) * PhiA α μ R ^ 2 := by
  set F : X → ℝ≥0∞ := fun x => ENNReal.ofReal (phiA α (q μ R x)) with hF
  -- pointwise bound into a sum of three product-form terms
  have hpt : ∀ p : X × X, μ p.1 * μ p.2 * ENNReal.ofReal
        ((q μ R p.1 ^ 2 + q μ R p.2 ^ 2)
          / ((1 - max (q μ R p.1) (q μ R p.2)) ^ α
             * (1 + max (q μ R p.1) (q μ R p.2) - 2 * min (q μ R p.1) (q μ R p.2)) ^ α))
      ≤ ENNReal.ofReal (LA α) * (μ p.1 * μ p.2 * (F p.1 * 1))
        + ENNReal.ofReal (LA α) * (μ p.1 * μ p.2 * (1 * F p.2))
        + ENNReal.ofReal (MA α) * (μ p.1 * μ p.2 * (F p.1 * F p.2)) := by
    intro p
    by_cases hx₀ : μ p.1 = 0
    · simp [hx₀]
    by_cases hx₁ : μ p.2 = 0
    · simp [hx₁]
    have hb := rowBound_ofReal hα hrefl hx₀ hx₁
    calc μ p.1 * μ p.2 * ENNReal.ofReal _
        ≤ μ p.1 * μ p.2 * (ENNReal.ofReal (LA α) * (F p.1 + F p.2) + ENNReal.ofReal (MA α) * (F p.1 * F p.2)) := by
          gcongr
      _ = _ := by rw [hF]; ring
  calc ∑' p : X × X, _
      ≤ ∑' p : X × X, (ENNReal.ofReal (LA α) * (μ p.1 * μ p.2 * (F p.1 * 1))
          + ENNReal.ofReal (LA α) * (μ p.1 * μ p.2 * (1 * F p.2))
          + ENNReal.ofReal (MA α) * (μ p.1 * μ p.2 * (F p.1 * F p.2))) := ENNReal.tsum_le_tsum hpt
    _ = 2 * ENNReal.ofReal (LA α) * PhiA α μ R + ENNReal.ofReal (MA α) * PhiA α μ R ^ 2 := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
            ENNReal.tsum_mul_left, prod_avg μ F (fun _ => 1), prod_avg μ (fun _ => 1) F,
            prod_avg μ F F]
        have hΦ : (∑' x, μ x * F x) = PhiA α μ R := rfl
        have h1 : (∑' x, μ x * (fun _ : X => (1 : ℝ≥0∞)) x) = 1 := by
          simp only [mul_one]; exact μ.tsum_coe
        rw [hΦ, h1]; ring

/-! ### The second term: `W`, `H`, `Λ` and the Fubini swap -/

/-- `W(x) = r(x)^{-α} = (1-q)^{-α}`, as `ℝ≥0∞`. -/
noncomputable def Wnn (α : ℝ) (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - q μ R x) ^ (-α))

/-- `H(y) = 𝔼_X[𝟙_{X⋠y} W(X)]`. -/
noncomputable def Hnn (α : ℝ) (μ : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, μ x * (if ¬ R x y then Wnn α μ R x else 0)

/-- `Λ(y) = 𝔼_X[𝟙_{X⋠y} φ(q(X))]`, the dead-set weight sum. -/
noncomputable def Lam (α : ℝ) (μ : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, μ x * (if ¬ R x y then ENNReal.ofReal (phiA α (q μ R x)) else 0)

/-- **`eq:overlap-id`**, the Fubini swap: `𝔼[c·W(X₀)W(X₁)] = 𝔼_Y[H(Y)²]`. Expand
`c` as a `Y`-sum, pull it out, `tsum_comm`, then split the pair-sum as a square
(the two coordinate factors coincide). -/
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

/-- **`eq:W-bound`**: `W(x) ≤ 1 + α·φ(q(x))`, coerced to `ℝ≥0∞`. Holds for all
`x`: on the support by `rpow_neg_alpha_le`, and where `q = 1` (`W = 0`) trivially. -/
lemma Wnn_le (hα : 1 ≤ α) (μ : PMF X) (R : X → X → Prop) (x : X) :
    Wnn α μ R x ≤ 1 + ENNReal.ofReal α * ENNReal.ofReal (phiA α (q μ R x)) := by
  rw [Wnn]
  by_cases hq : q μ R x < 1
  · have hα0 : (0:ℝ) ≤ α := by linarith
    have hφ : 0 ≤ phiA α (q μ R x) := phiA_nonneg α q_nonneg hq
    calc ENNReal.ofReal ((1 - q μ R x) ^ (-α))
        ≤ ENNReal.ofReal (1 + α * phiA α (q μ R x)) := ENNReal.ofReal_le_ofReal (W_le hα hq)
      _ = 1 + ENNReal.ofReal α * ENNReal.ofReal (phiA α (q μ R x)) := by
          rw [ENNReal.ofReal_add (by norm_num) (mul_nonneg hα0 hφ),
              ENNReal.ofReal_mul hα0, ENNReal.ofReal_one]
  · have hq1 : q μ R x = 1 := le_antisymm q_le_one (not_lt.mp hq)
    have h0 : (1 : ℝ) - q μ R x = 0 := by rw [hq1]; ring
    rw [h0, Real.zero_rpow (ne_of_lt (by linarith : (-α : ℝ) < 0)), ENNReal.ofReal_zero]
    exact zero_le

/-- `Λ(y) ≤ Φ`: drop the indicator. -/
lemma Lam_le_Phi (α : ℝ) (μ : PMF X) (R : X → X → Prop) (y : X) : Lam α μ R y ≤ PhiA α μ R := by
  rw [Lam, PhiA_eq_tsum α]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases h : R x y <;> simp [h]

/-- `H(y) ≤ q(y) + α·Λ(y)`. Uses `Wnn_le` per `x` and symmetry of `R` (via
`tsum_not_rel_eq_qE`) to identify `𝔼_X 𝟙_{X⋠y}` with `q(y)`. -/
lemma Hnn_le (hα : 1 ≤ α) (μ : PMF X) (R : X → X → Prop) (hsymm : ∀ a b, R a b → R b a) (y : X) :
    Hnn α μ R y ≤ qE μ R y + ENNReal.ofReal α * Lam α μ R y := by
  have hbr : ∀ x, μ x * (if ¬ R x y then Wnn α μ R x else 0)
      ≤ (if ¬ R x y then μ x else 0)
        + ENNReal.ofReal α
          * (μ x * (if ¬ R x y then ENNReal.ofReal (phiA α (q μ R x)) else 0)) := by
    intro x
    by_cases h : R x y
    · simp [h]
    · simp only [if_pos h]
      calc μ x * Wnn α μ R x
          ≤ μ x * (1 + ENNReal.ofReal α * ENNReal.ofReal (phiA α (q μ R x))) := by
            gcongr; exact Wnn_le hα μ R x
        _ = μ x + ENNReal.ofReal α * (μ x * ENNReal.ofReal (phiA α (q μ R x))) := by ring
  have hqe : (∑' x, if ¬ R x y then μ x else 0) = qE μ R y := by
    rw [← tsum_not_rel_eq_qE hsymm]
    exact tsum_congr fun x => by by_cases h : R x y <;> simp [h]
  calc Hnn α μ R y
      ≤ ∑' x, ((if ¬ R x y then μ x else 0)
          + ENNReal.ofReal α
            * (μ x * (if ¬ R x y then ENNReal.ofReal (phiA α (q μ R x)) else 0))) :=
        ENNReal.tsum_le_tsum hbr
    _ = qE μ R y + ENNReal.ofReal α * Lam α μ R y := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hqe, Lam]

/-! ### Averaged second-term bounds -/

/-- `𝔼[Λ(Y)²] ≤ Φ²`. -/
lemma ELamsq_le (α : ℝ) (μ : PMF X) (R : X → X → Prop) :
    ∑' y, μ y * Lam α μ R y ^ 2 ≤ PhiA α μ R ^ 2 := by
  calc ∑' y, μ y * Lam α μ R y ^ 2
      ≤ ∑' y, μ y * PhiA α μ R ^ 2 :=
        ENNReal.tsum_le_tsum fun y => by gcongr; exact Lam_le_Phi α μ R y
    _ = PhiA α μ R ^ 2 := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- `ENNReal.ofReal (1/8) = 1/8`, as an `ℝ≥0∞` numeral. -/
lemma ofReal_one_eighth : ENNReal.ofReal (1 / 8) = 1 / 8 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
  norm_num [ENNReal.ofReal_ofNat]

/-- `𝔼[q(Y)²] ≤ (1/8)Φ` (uses reflexivity, via `q_lt_one` on the support). -/
lemma Eqsq_le (hα : 1 ≤ α) (μ : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x) :
    ∑' y, μ y * qE μ R y ^ 2 ≤ ENNReal.ofReal (KA α) * PhiA α μ R := by
  have hpt : ∀ y, μ y * qE μ R y ^ 2
      ≤ ENNReal.ofReal (KA α) * (μ y * ENNReal.ofReal (phiA α (q μ R y))) := by
    intro y
    by_cases hy : μ y = 0
    · simp [hy]
    · have hq1 : q μ R y < 1 := q_lt_one (hrefl y) hy
      have hqE : qE μ R y = ENNReal.ofReal (q μ R y) := (ENNReal.ofReal_toReal qE_ne_top).symm
      rw [hqE, ← ENNReal.ofReal_pow q_nonneg]
      calc μ y * ENNReal.ofReal (q μ R y ^ 2)
          ≤ μ y * ENNReal.ofReal (KA α * phiA α (q μ R y)) := by
            gcongr; exact q_sq_le hα q_nonneg hq1
        _ = ENNReal.ofReal (KA α) * (μ y * ENNReal.ofReal (phiA α (q μ R y))) := by
            rw [ENNReal.ofReal_mul (KA_nonneg (le_trans zero_le_one hα))]; ring
  calc ∑' y, μ y * qE μ R y ^ 2
      ≤ ∑' y, ENNReal.ofReal (KA α) * (μ y * ENNReal.ofReal (phiA α (q μ R y))) := ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (KA α) * PhiA α μ R := by rw [ENNReal.tsum_mul_left, ← PhiA_eq_tsum α]

/-- **`eq:iid-H-bound`** averaged: `2·𝔼[H(Y)²] ≤ (1/2)Φ + 25Φ²`. Combines `Hnn_le`,
the AM-GM `H² ≤ 2q² + 2α²Λ²`, `ELamsq_le` and `Eqsq_le`, with `4·(1/8)=1/2`,
`4α²=25`. -/
lemma two_EHsq_le (hα : 1 ≤ α) (μ : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (hsymm : ∀ a b, R a b → R b a) :
    2 * ∑' y, μ y * Hnn α μ R y ^ 2
      ≤ 4 * ENNReal.ofReal (KA α) * PhiA α μ R
        + 4 * ENNReal.ofReal α ^ 2 * PhiA α μ R ^ 2 := by
  have hHsq : ∀ y, Hnn α μ R y ^ 2
      ≤ 2 * (qE μ R y ^ 2 + (ENNReal.ofReal α * Lam α μ R y) ^ 2) := by
    intro y
    calc Hnn α μ R y ^ 2
        ≤ (qE μ R y + ENNReal.ofReal α * Lam α μ R y) ^ 2 :=
          pow_le_pow_left' (Hnn_le hα μ R hsymm y) 2
      _ ≤ 2 * (qE μ R y ^ 2 + (ENNReal.ofReal α * Lam α μ R y) ^ 2) := ennreal_add_sq_le _ _
  have hdist : ∑' y, μ y * (2 * (qE μ R y ^ 2 + (ENNReal.ofReal α * Lam α μ R y) ^ 2))
      = 2 * (∑' y, μ y * qE μ R y ^ 2)
        + 2 * (ENNReal.ofReal α) ^ 2 * ∑' y, μ y * Lam α μ R y ^ 2 := by
    rw [tsum_congr fun y => show
        μ y * (2 * (qE μ R y ^ 2 + (ENNReal.ofReal α * Lam α μ R y) ^ 2))
          = 2 * (μ y * qE μ R y ^ 2)
            + 2 * (ENNReal.ofReal α) ^ 2 * (μ y * Lam α μ R y ^ 2) from by ring,
      ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  calc 2 * ∑' y, μ y * Hnn α μ R y ^ 2
      ≤ 2 * ∑' y, μ y * (2 * (qE μ R y ^ 2 + (ENNReal.ofReal α * Lam α μ R y) ^ 2)) := by
        gcongr with y; exact hHsq y
    _ = 4 * (∑' y, μ y * qE μ R y ^ 2)
          + 4 * (ENNReal.ofReal α) ^ 2 * ∑' y, μ y * Lam α μ R y ^ 2 := by rw [hdist]; ring
    _ ≤ 4 * ENNReal.ofReal (KA α) * PhiA α μ R
          + 4 * ENNReal.ofReal α ^ 2 * PhiA α μ R ^ 2 := by
        rw [mul_assoc (4 : ℝ≥0∞) (ENNReal.ofReal (KA α)) (PhiA α μ R)]
        gcongr
        · exact Eqsq_le hα μ R hrefl
        · exact ELamsq_le α μ R

/-- **`eq:overlap-final`**: the average of the second term is `≤ (1/2)Φ + 25Φ²`.
The pointwise `ofReal` distributes into `2·c·W(x₀)W(x₁)`, then the Fubini swap and
`two_EHsq_le`. -/
lemma secondTerm_le (hα : 1 ≤ α) (μ : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (hsymm : ∀ a b, R a b → R b a) :
    ∑' p : X × X, μ p.1 * μ p.2 * ENNReal.ofReal
        (2 * (cOverlap μ R p.1 p.2).toReal
          * (1 - q μ R p.1) ^ (-α) * (1 - q μ R p.2) ^ (-α))
      ≤ 4 * ENNReal.ofReal (KA α) * PhiA α μ R
        + 4 * ENNReal.ofReal α ^ 2 * PhiA α μ R ^ 2 := by
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
  rw [ENNReal.tsum_mul_left, fubini_swap α]
  exact two_EHsq_le hα μ R hrefl hsymm

/-- `ofReal` splits the linear constant `A_α = 2L_α + 4K_α`. -/
lemma ofReal_AA (hα : 1 ≤ α) :
    ENNReal.ofReal (AA α) = 2 * ENNReal.ofReal (LA α) + 4 * ENNReal.ofReal (KA α) := by
  have hα0 : (0:ℝ) ≤ α := by linarith
  rw [AA, ENNReal.ofReal_add (by linarith [LA_nonneg hα0]) (by linarith [KA_nonneg hα0]),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
  simp [ENNReal.ofReal_ofNat]

/-- `ofReal` splits the quadratic constant `B_α = M_α + 4α²`. -/
lemma ofReal_BA (hα : 1 ≤ α) :
    ENNReal.ofReal (BA α) = ENNReal.ofReal (MA α) + 4 * ENNReal.ofReal α ^ 2 := by
  have hα0 : (0:ℝ) ≤ α := by linarith
  rw [BA, ENNReal.ofReal_add (MA_nonneg α) (by positivity),
      show (4:ℝ) * α ^ 2 = 4 * α ^ 2 from rfl,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4), ENNReal.ofReal_pow hα0]
  simp [ENNReal.ofReal_ofNat]

/-! ### `thm:contraction`: the contraction -/

/-- **`thm:contraction`**, `eq:one-step`: `Φ(R^□, μ²) ≤ A·Φ + 29Φ²` with `A = 2L_α + 4K_α`
(here `A = 2·(14/75) + 1/2`). Adds the two averages `firstTerm_le` and
`secondTerm_le` through the pointwise split `phi_Q_split hα`. -/
theorem Phi_square_leA (hα : 1 ≤ α) (μ : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (hsymm : ∀ a b, R a b → R b a) :
    PhiA α (prodPMF μ μ) (SquareRel R)
      ≤ ENNReal.ofReal (AA α) * PhiA α μ R + ENNReal.ofReal (BA α) * PhiA α μ R ^ 2 := by
  have hpt : ∀ p : X × X,
      prodPMF μ μ p * ENNReal.ofReal (phiA α (q (prodPMF μ μ) (SquareRel R) p))
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
    calc ENNReal.ofReal (phiA α (q (prodPMF μ μ) (SquareRel R) p))
        ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal (phi_Q_split hα hrefl hx₀ hx₁)
      _ ≤ _ := ENNReal.ofReal_add_le
  calc PhiA α (prodPMF μ μ) (SquareRel R)
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
    _ ≤ (2 * ENNReal.ofReal (LA α) * PhiA α μ R + ENNReal.ofReal (MA α) * PhiA α μ R ^ 2)
          + (4 * ENNReal.ofReal (KA α) * PhiA α μ R
             + 4 * ENNReal.ofReal α ^ 2 * PhiA α μ R ^ 2) := by
        gcongr
        · exact firstTerm_le hα μ R hrefl
        · exact secondTerm_le hα μ R hrefl hsymm
    _ = ENNReal.ofReal (AA α) * PhiA α μ R + ENNReal.ofReal (BA α) * PhiA α μ R ^ 2 := by
        rw [ofReal_AA hα, ofReal_BA hα]; ring

/-- **`eq:strict`**: if `A_α + B_α Φ ≤ ρ` then `Φ(R^□, μ²) ≤ ρ Φ`. -/
theorem Phi_square_le_of_smallA (hα : 1 ≤ α) {ρ : ℝ≥0∞} (μ : PMF X) (R : X → X → Prop)
    (hrefl : ∀ x, R x x) (hsymm : ∀ a b, R a b → R b a)
    (hΦ : ENNReal.ofReal (AA α) + ENNReal.ofReal (BA α) * PhiA α μ R ≤ ρ) :
    PhiA α (prodPMF μ μ) (SquareRel R) ≤ ρ * PhiA α μ R := by
  calc PhiA α (prodPMF μ μ) (SquareRel R)
      ≤ ENNReal.ofReal (AA α) * PhiA α μ R + ENNReal.ofReal (BA α) * PhiA α μ R ^ 2 :=
        Phi_square_leA hα μ R hrefl hsymm
    _ = (ENNReal.ofReal (AA α) + ENNReal.ofReal (BA α) * PhiA α μ R) * PhiA α μ R := by ring
    _ ≤ ρ * PhiA α μ R := by gcongr

/-! ### The instances at `α = 5/2` -/

lemma ofReal_AA_alpha_le : ENNReal.ofReal (AA alpha) ≤ (7 : ℝ≥0∞) / 8 := by
  rw [show (7 : ℝ≥0∞) / 8 = ENNReal.ofReal (7 / 8) from by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]]
  exact ENNReal.ofReal_le_ofReal AA_alpha_le

lemma ofReal_BA_alpha_le : ENNReal.ofReal (BA alpha) ≤ (29 : ℝ≥0∞) := by
  rw [show (29 : ℝ≥0∞) = ENNReal.ofReal 29 from by rw [ENNReal.ofReal_ofNat]]
  exact ENNReal.ofReal_le_ofReal BA_alpha_le

/-- **`thm:contraction`** at `α = 5/2`: `Φ(R^□, μ²) ≤ (7/8)Φ + 29Φ²`. -/
theorem Phi_square_le (μ : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (hsymm : ∀ a b, R a b → R b a) :
    Phi (prodPMF μ μ) (SquareRel R) ≤ 7 / 8 * Phi μ R + 29 * Phi μ R ^ 2 := by
  have h := Phi_square_leA one_le_alpha μ R hrefl hsymm
  calc Phi (prodPMF μ μ) (SquareRel R)
      ≤ ENNReal.ofReal (AA alpha) * Phi μ R + ENNReal.ofReal (BA alpha) * Phi μ R ^ 2 := h
    _ ≤ 7 / 8 * Phi μ R + 29 * Phi μ R ^ 2 := by
        gcongr
        · exact ofReal_AA_alpha_le
        · exact ofReal_BA_alpha_le

/-- **`eq:strict`** at `α = 5/2`: `Φ ≤ 1/256` gives `Φ(R^□, μ²) ≤ (253/256)Φ`. -/
theorem Phi_square_le_of_small (μ : PMF X) (R : X → X → Prop) (hrefl : ∀ x, R x x)
    (hsymm : ∀ a b, R a b → R b a) (hΦ : Phi μ R ≤ 1 / 256) :
    Phi (prodPMF μ μ) (SquareRel R) ≤ 253 / 256 * Phi μ R := by
  have he : (7 : ℝ≥0∞) / 8 + 29 * (1 / 256) = 253 / 256 := by
    rw [show (7 : ℝ≥0∞) / 8 = ENNReal.ofReal (7 / 8) from by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat],
        show (1 : ℝ≥0∞) / 256 = ENNReal.ofReal (1 / 256) from by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat],
        show (29 : ℝ≥0∞) = ENNReal.ofReal 29 from by rw [ENNReal.ofReal_ofNat],
        show (253 : ℝ≥0∞) / 256 = ENNReal.ofReal (253 / 256) from by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    congr 1; norm_num
  calc Phi (prodPMF μ μ) (SquareRel R)
      ≤ 7 / 8 * Phi μ R + 29 * Phi μ R ^ 2 := Phi_square_le μ R hrefl hsymm
    _ = (7 / 8 + 29 * Phi μ R) * Phi μ R := by ring
    _ ≤ (7 / 8 + 29 * (1 / 256)) * Phi μ R := by gcongr
    _ = 253 / 256 * Phi μ R := by rw [he]

end GraphMatching
