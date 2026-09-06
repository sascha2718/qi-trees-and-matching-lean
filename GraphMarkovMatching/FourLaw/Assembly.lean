/-
The measure-level four-law directed contraction
(`arbitrary_offspring_matching.tex`, Theorem `thm:four-law`):

    Φ_α(μ₀⊗μ₁ → ν₀⊗ν₁; R^{(2)})
      ≤ (2L + 2(1+δ)K)·M + (2Lc_α + 20 + 2(1+δ⁻¹)α²)·M²

whenever the eight directed potentials between rows and columns are at most
`M`. The linear constant is the same `A = 2L + 2(1+δ)K` as the one-law
contraction lemma. The quadratic constant `20` is the coarse `S₀S₁`-averaged
form of the prose bound.

The proof: the pointwise main bound (`phi_Q_split_four`), averaged; the
first term through the product-shape lemma, the two overlap terms through
the directed `W`/`H`/`Λ` machinery and the Fubini swap, with the reversed
potentials entering exactly where symmetry of `R` identifies in-degrees with
bad degrees.
-/
import GraphMarkovMatching.FourLaw.Pointwise

namespace GraphMarkovMatching

open GraphMarkovMatching.Support Real
open scoped ENNReal Classical

universe u
variable {X : Type u}

/-! ### Helpers -/

/-- On charged points of a row with finite directed potential, the bad degree
is below one. -/
lemma q_lt_one_of_charged {α : ℝ} {μ ν : PMF X} {R : X → X → Prop}
    (hfin : PhiD α μ ν R ≠ ⊤) {x : X} (hx : μ x ≠ 0) : q ν R x < 1 := by
  by_contra h
  have htop : phiE α (q ν R x) = ⊤ := by rw [phiE, if_neg h]
  have hle : μ x * phiE α (q ν R x) ≤ PhiD α μ ν R := ENNReal.le_tsum x
  rw [htop, ENNReal.mul_top hx] at hle
  exact hfin (top_le_iff.mp hle)

/-- The good degree of the square dominates the straight product. -/
lemma rE_square_ge_straight (ν₀ ν₁ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    rE ν₀ R x₀ * rE ν₁ R x₁ ≤ rE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁) := by
  have hA : (∑' p : X × X, if R x₀ p.1 ∧ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
      = rE ν₀ R x₀ * rE ν₁ R x₁ := by
    rw [tsum_congr fun p : X × X => show
        (if R x₀ p.1 ∧ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          = (if R x₀ p.1 then ν₀ p.1 else 0) * (if R x₁ p.2 then ν₁ p.2 else 0)
        by by_cases ha : R x₀ p.1 <;> by_cases hb : R x₁ p.2 <;> simp [ha, hb]]
    exact tsum_prod_split (fun y => if R x₀ y then ν₀ y else 0)
      (fun y => if R x₁ y then ν₁ y else 0)
  rw [← hA, show rE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)
      = ∑' p : X × X, if SquareRel R (x₀, x₁) p then ν₀ p.1 * ν₁ p.2 else 0 from by
    rw [rE]; simp_rw [prodPMF_apply]]
  refine ENNReal.tsum_le_tsum fun p => ?_
  by_cases h : R x₀ p.1 ∧ R x₁ p.2
  · rw [if_pos h, if_pos (show SquareRel R (x₀, x₁) p from Or.inl h)]
  · rw [if_neg h]; exact zero_le

/-! ### The directed `W`, `H`, `Λ` -/

/-- The inverse-power weight of a row point against a column law. -/
noncomputable def WnnD (α : ℝ) (ν : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - q ν R x) ^ (-α))

/-- `H(y) = 𝔼_{X∼μ}[𝟙_{X⋠y} W_ν(X)]`. -/
noncomputable def HnnD (α : ℝ) (μ ν : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, μ x * (if ¬ R x y then WnnD α ν R x else 0)

/-- `Λ(y) = 𝔼_{X∼μ}[𝟙_{X⋠y} φ_α(q_ν(X))]`, the dead-set weight sum. -/
noncomputable def LamD (α : ℝ) (μ ν : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, μ x * (if ¬ R x y then phiE α (q ν R x) else 0)

/-- The directed Fubini swap:
`𝔼[c_{ν_c}·W_{ν₀}(X₀)W_{ν₁}(X₁)] = 𝔼_{Y∼ν_c}[H_{μ₀,ν₀}(Y)·H_{μ₁,ν₁}(Y)]`. -/
lemma fubini_swap_two (α : ℝ) (μ₀ μ₁ νc ν₀ ν₁ : PMF X) (R : X → X → Prop) :
    ∑' p : X × X, μ₀ p.1 * μ₁ p.2
        * (cOverlap νc R p.1 p.2 * (WnnD α ν₀ R p.1 * WnnD α ν₁ R p.2))
      = ∑' y, νc y * (HnnD α μ₀ ν₀ R y * HnnD α μ₁ ν₁ R y) := by
  have hstep : ∀ p : X × X,
      μ₀ p.1 * μ₁ p.2 * (cOverlap νc R p.1 p.2 * (WnnD α ν₀ R p.1 * WnnD α ν₁ R p.2))
        = ∑' y, μ₀ p.1 * μ₁ p.2 * (WnnD α ν₀ R p.1 * WnnD α ν₁ R p.2)
            * (if ¬ R p.1 y ∧ ¬ R p.2 y then νc y else 0) := by
    intro p; rw [cOverlap, ENNReal.tsum_mul_left]; ring
  simp_rw [hstep]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun y => ?_
  rw [tsum_congr fun p : X × X => show
      μ₀ p.1 * μ₁ p.2 * (WnnD α ν₀ R p.1 * WnnD α ν₁ R p.2)
          * (if ¬ R p.1 y ∧ ¬ R p.2 y then νc y else 0)
        = νc y * ((μ₀ p.1 * (if ¬ R p.1 y then WnnD α ν₀ R p.1 else 0))
                 * (μ₁ p.2 * (if ¬ R p.2 y then WnnD α ν₁ R p.2 else 0)))
      from by by_cases h1 : R p.1 y <;> by_cases h2 : R p.2 y <;> simp [h1, h2]; ring]
  rw [ENNReal.tsum_mul_left, tsum_prod_split
        (fun x => μ₀ x * (if ¬ R x y then WnnD α ν₀ R x else 0))
        (fun x => μ₁ x * (if ¬ R x y then WnnD α ν₁ R x else 0)), HnnD, HnnD]

/-- The tangent bound for the directed weight. -/
lemma WnnD_le {α : ℝ} (hα : 1 ≤ α) (ν : PMF X) (R : X → X → Prop) (x : X) :
    WnnD α ν R x ≤ 1 + ENNReal.ofReal α * phiE α (q ν R x) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  rw [WnnD]
  by_cases hq : q ν R x < 1
  · have hφ : 0 ≤ phi α (q ν R x) := phi_nonneg q_nonneg hq
    rw [phiE_of_lt hq]
    calc ENNReal.ofReal ((1 - q ν R x) ^ (-α))
        ≤ ENNReal.ofReal (1 + α * phi α (q ν R x)) :=
          ENNReal.ofReal_le_ofReal (rpow_neg_alpha_le hα hq)
      _ = 1 + ENNReal.ofReal α * ENNReal.ofReal (phi α (q ν R x)) := by
          rw [ENNReal.ofReal_add (by norm_num) (mul_nonneg hα0 hφ),
              ENNReal.ofReal_mul hα0, ENNReal.ofReal_one]
  · have hq1 : q ν R x = 1 := le_antisymm q_le_one (not_lt.mp hq)
    have h0 : (1 : ℝ) - q ν R x = 0 := by rw [hq1]; ring
    rw [h0, Real.zero_rpow (ne_of_lt (by linarith : (-α : ℝ) < 0)), ENNReal.ofReal_zero]
    exact zero_le

/-- `Λ(y) ≤ Φ(μ → ν)`: drop the indicator. -/
lemma LamD_le_PhiD (α : ℝ) (μ ν : PMF X) (R : X → X → Prop) (y : X) :
    LamD α μ ν R y ≤ PhiD α μ ν R := by
  rw [LamD, PhiD]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases h : R x y <;> simp [h]

/-- `H(y) ≤ q_μ(y) + α·Λ(y)`, via symmetry of `R`. -/
lemma HnnD_le {α : ℝ} (hα : 1 ≤ α) (μ ν : PMF X) (R : X → X → Prop)
    (hsymm : ∀ a b, R a b → R b a) (y : X) :
    HnnD α μ ν R y ≤ qE μ R y + ENNReal.ofReal α * LamD α μ ν R y := by
  have hbr : ∀ x, μ x * (if ¬ R x y then WnnD α ν R x else 0)
      ≤ (if ¬ R x y then μ x else 0)
        + ENNReal.ofReal α * (μ x * (if ¬ R x y then phiE α (q ν R x) else 0)) := by
    intro x
    by_cases h : R x y
    · simp [h]
    · simp only [if_pos h]
      calc μ x * WnnD α ν R x
          ≤ μ x * (1 + ENNReal.ofReal α * phiE α (q ν R x)) := by
            gcongr; exact WnnD_le hα ν R x
        _ = μ x + ENNReal.ofReal α * (μ x * phiE α (q ν R x)) := by ring
  have hqe : (∑' x, if ¬ R x y then μ x else 0) = qE μ R y := by
    rw [← tsum_not_rel_eq_qE hsymm]
    exact tsum_congr fun x => by by_cases h : R x y <;> simp [h]
  calc HnnD α μ ν R y
      ≤ ∑' x, ((if ¬ R x y then μ x else 0)
          + ENNReal.ofReal α * (μ x * (if ¬ R x y then phiE α (q ν R x) else 0))) :=
        ENNReal.tsum_le_tsum hbr
    _ = qE μ R y + ENNReal.ofReal α * LamD α μ ν R y := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hqe, LamD]

/-- `𝔼_{Y∼ν}[q_μ(Y)²] ≤ K·Φ(ν → μ)`, in the safe convention. -/
lemma EqsqD_le {α K : ℝ} (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (ν μ : PMF X) (R : X → X → Prop) :
    ∑' y, ν y * qE μ R y ^ 2 ≤ ENNReal.ofReal K * PhiD α ν μ R := by
  have hpt : ∀ y, ν y * qE μ R y ^ 2
      ≤ ENNReal.ofReal K * (ν y * phiE α (q μ R y)) := by
    intro y
    by_cases hq : q μ R y < 1
    · have hqE : qE μ R y = ENNReal.ofReal (q μ R y) := (ENNReal.ofReal_toReal qE_ne_top).symm
      rw [hqE, ← ENNReal.ofReal_pow q_nonneg, phiE_of_lt hq]
      calc ν y * ENNReal.ofReal (q μ R y ^ 2)
          ≤ ν y * ENNReal.ofReal (K * phi α (q μ R y)) := by
            gcongr
            exact q_sq_le (hK _ q_nonneg q_le_one) q_nonneg hq
        _ = ENNReal.ofReal K * (ν y * ENNReal.ofReal (phi α (q μ R y))) := by
            rw [ENNReal.ofReal_mul hK0.le]; ring
    · have htop : phiE α (q μ R y) = ⊤ := by rw [phiE, if_neg hq]
      by_cases hy : ν y = 0
      · simp [hy]
      · rw [htop, ENNReal.mul_top hy, ENNReal.mul_top (by
          simp [ENNReal.ofReal_eq_zero, not_le, hK0])]
        exact le_top
  calc ∑' y, ν y * qE μ R y ^ 2
      ≤ ∑' y, ENNReal.ofReal K * (ν y * phiE α (q μ R y)) :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal K * PhiD α ν μ R := by rw [ENNReal.tsum_mul_left, PhiD]

/-- `𝔼_{Y∼ν}[Λ(Y)²] ≤ Φ(μ → ν_c)²`. -/
lemma ELamsqD_le (α : ℝ) (ν μ νc : PMF X) (R : X → X → Prop) :
    ∑' y, ν y * LamD α μ νc R y ^ 2 ≤ PhiD α μ νc R ^ 2 := by
  calc ∑' y, ν y * LamD α μ νc R y ^ 2
      ≤ ∑' y, ν y * PhiD α μ νc R ^ 2 :=
        ENNReal.tsum_le_tsum fun y => by gcongr; exact LamD_le_PhiD α μ νc R y
    _ = PhiD α μ νc R ^ 2 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The averaged `H²`-bound for one row-column pair. -/
lemma EHsqD_le {α δ K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ) (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (ν μ νc : PMF X) (R : X → X → Prop)
    (hsymm : ∀ a b, R a b → R b a) :
    ∑' y, ν y * HnnD α μ νc R y ^ 2
      ≤ ENNReal.ofReal ((1 + δ) * K) * PhiD α ν μ R
        + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * PhiD α μ νc R ^ 2 := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hHsq : ∀ y, HnnD α μ νc R y ^ 2
      ≤ ENNReal.ofReal (1 + δ) * qE μ R y ^ 2
        + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α * LamD α μ νc R y) ^ 2 := by
    intro y
    calc HnnD α μ νc R y ^ 2
        ≤ (qE μ R y + ENNReal.ofReal α * LamD α μ νc R y) ^ 2 :=
          pow_le_pow_left' (HnnD_le hα μ νc R hsymm y) 2
      _ ≤ ENNReal.ofReal (1 + δ) * qE μ R y ^ 2
            + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α * LamD α μ νc R y) ^ 2 :=
          ennreal_add_sq_le_weighted hδ _ _
  have hdist : ∑' y, ν y * (ENNReal.ofReal (1 + δ) * qE μ R y ^ 2
        + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α * LamD α μ νc R y) ^ 2)
      = ENNReal.ofReal (1 + δ) * (∑' y, ν y * qE μ R y ^ 2)
        + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2
          * ∑' y, ν y * LamD α μ νc R y ^ 2 := by
    rw [tsum_congr fun y => show
        ν y * (ENNReal.ofReal (1 + δ) * qE μ R y ^ 2
            + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α * LamD α μ νc R y) ^ 2)
          = ENNReal.ofReal (1 + δ) * (ν y * qE μ R y ^ 2)
            + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2
              * (ν y * LamD α μ νc R y ^ 2) from by ring,
      ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  have c₁ : ENNReal.ofReal ((1 + δ) * K)
      = ENNReal.ofReal (1 + δ) * ENNReal.ofReal K :=
    ENNReal.ofReal_mul (by linarith)
  have c₂ : ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2)
      = ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2 := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hα0]
  calc ∑' y, ν y * HnnD α μ νc R y ^ 2
      ≤ ∑' y, ν y * (ENNReal.ofReal (1 + δ) * qE μ R y ^ 2
          + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α * LamD α μ νc R y) ^ 2) := by
        gcongr with y; exact hHsq y
    _ = ENNReal.ofReal (1 + δ) * (∑' y, ν y * qE μ R y ^ 2)
          + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2
            * ∑' y, ν y * LamD α μ νc R y ^ 2 := hdist
    _ ≤ ENNReal.ofReal (1 + δ) * (ENNReal.ofReal K * PhiD α ν μ R)
          + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2 * PhiD α μ νc R ^ 2 := by
        gcongr
        · exact EqsqD_le hK0 hK ν μ R
        · exact ELamsqD_le α ν μ νc R
    _ = ENNReal.ofReal ((1 + δ) * K) * PhiD α ν μ R
          + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * PhiD α μ νc R ^ 2 := by
        rw [c₁, c₂]; ring

/-! ### The four-law contraction theorem -/

/-- Marginal collapse: averaging a function of one coordinate. -/
lemma tsum_mass_left (μ₀ μ₁ : PMF X) (F : X → ℝ≥0∞) :
    ∑' p : X × X, prodPMF μ₀ μ₁ p * F p.1 = ∑' x, μ₀ x * F x := by
  rw [tsum_congr fun p : X × X => show prodPMF μ₀ μ₁ p * F p.1
      = (μ₀ p.1 * F p.1) * μ₁ p.2 from by rw [prodPMF_apply]; ring,
    tsum_prod_split (fun x => μ₀ x * F x) (fun x => μ₁ x), PMF.tsum_coe, mul_one]

/-- Marginal collapse, second coordinate. -/
lemma tsum_mass_right (μ₀ μ₁ : PMF X) (F : X → ℝ≥0∞) :
    ∑' p : X × X, prodPMF μ₀ μ₁ p * F p.2 = ∑' x, μ₁ x * F x := by
  rw [tsum_congr fun p : X × X => show prodPMF μ₀ μ₁ p * F p.2
      = μ₀ p.1 * (μ₁ p.2 * F p.2) from by rw [prodPMF_apply]; ring,
    tsum_prod_split (fun x => μ₀ x) (fun x => μ₁ x * F x), PMF.tsum_coe, one_mul]

/-- Marginal collapse for products of one-coordinate functions. -/
lemma tsum_mass_prod (μ₀ μ₁ : PMF X) (F G : X → ℝ≥0∞) :
    ∑' p : X × X, prodPMF μ₀ μ₁ p * (F p.1 * G p.2)
      = (∑' x, μ₀ x * F x) * (∑' x, μ₁ x * G x) := by
  rw [tsum_congr fun p : X × X => show prodPMF μ₀ μ₁ p * (F p.1 * G p.2)
      = (μ₀ p.1 * F p.1) * (μ₁ p.2 * G p.2) from by rw [prodPMF_apply]; ring]
  exact tsum_prod_split (fun x => μ₀ x * F x) (fun x => μ₁ x * G x)

/-- The row `φ`-sum against a row law is the sum of the two forward
potentials. -/
lemma tsum_rowsum (μ ν₀ ν₁ : PMF X) (α : ℝ) (R : X → X → Prop) :
    ∑' x, μ x * (phiE α (q ν₀ R x) + phiE α (q ν₁ R x))
      = PhiD α μ ν₀ R + PhiD α μ ν₁ R := by
  rw [tsum_congr fun x => show μ x * (phiE α (q ν₀ R x) + phiE α (q ν₁ R x))
      = μ x * phiE α (q ν₀ R x) + μ x * phiE α (q ν₁ R x) from by ring,
    ENNReal.tsum_add, PhiD, PhiD]

/-- **The four-law directed contraction** (`arbitrary_offspring_matching.tex`,
Theorem `thm:four-law`): if all eight directed potentials between the rows
`μ₀, μ₁` and the columns `ν₀, ν₁` are at most `M`, then

    Φ(μ₀⊗μ₁ → ν₀⊗ν₁; R⁽²⁾) ≤ (2L + 2(1+δ)K)·M + (2Lc_α + 20 + 2(1+δ⁻¹)α²)·M². -/
theorem PhiD_fourlaw_le {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (μ₀ μ₁ ν₀ ν₁ : PMF X) (R : X → X → Prop)
    (hsymm : ∀ a b, R a b → R b a) (M : ℝ≥0∞)
    (h00 : PhiD α μ₀ ν₀ R ≤ M) (h01 : PhiD α μ₀ ν₁ R ≤ M)
    (h10 : PhiD α μ₁ ν₀ R ≤ M) (h11 : PhiD α μ₁ ν₁ R ≤ M)
    (hr00 : PhiD α ν₀ μ₀ R ≤ M) (hr10 : PhiD α ν₀ μ₁ R ≤ M)
    (hr01 : PhiD α ν₁ μ₀ R ≤ M) (hr11 : PhiD α ν₁ μ₁ R ≤ M) :
    PhiD α (prodPMF μ₀ μ₁) (prodPMF ν₀ ν₁) (SquareRel R)
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2 := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hcc : 0 ≤ chordConst α := chordConst_nonneg hα0
  -- degenerate ceiling
  by_cases hM : M = ⊤
  · have hApos : (0 : ℝ) < 2 * L + 2 * (1 + δ) * K := by nlinarith
    rw [hM]
    have : ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * ⊤ = ⊤ :=
      ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero, not_le, hApos])
    rw [this, top_add]
    exact le_top
  -- finiteness of the forward potentials
  have hf00 : PhiD α μ₀ ν₀ R ≠ ⊤ := ne_top_of_le_ne_top hM h00
  have hf01 : PhiD α μ₀ ν₁ R ≠ ⊤ := ne_top_of_le_ne_top hM h01
  have hf10 : PhiD α μ₁ ν₀ R ≠ ⊤ := ne_top_of_le_ne_top hM h10
  have hf11 : PhiD α μ₁ ν₁ R ≠ ⊤ := ne_top_of_le_ne_top hM h11
  -- the global summand functions
  set F : X → ℝ≥0∞ := fun x => phiE α (q ν₀ R x) + phiE α (q ν₁ R x) with hF
  set cL : ℝ≥0∞ := ENNReal.ofReal (L / 2) with hcL
  set c₅ : ℝ≥0∞ := ENNReal.ofReal (L * chordConst α / 2 + 5) with hc₅
  -- termwise main bound
  have hterm : ∀ p : X × X,
      prodPMF μ₀ μ₁ p * phiE α (q (prodPMF ν₀ ν₁) (SquareRel R) p)
        ≤ prodPMF μ₀ μ₁ p * (cL * (F p.1 + F p.2) + c₅ * (F p.1 * F p.2)
            + cOverlap ν₀ R p.1 p.2 * (WnnD α ν₀ R p.1 * WnnD α ν₁ R p.2)
            + cOverlap ν₁ R p.1 p.2 * (WnnD α ν₁ R p.1 * WnnD α ν₀ R p.2)) := by
    intro p
    by_cases hz : prodPMF μ₀ μ₁ p = 0
    · rw [hz, zero_mul, zero_mul]
    · obtain ⟨hx₀, hx₁⟩ := mul_ne_zero_iff.mp (by rwa [prodPMF_apply] at hz)
      refine mul_le_mul_right ?_ _
      have hq00 : q ν₀ R p.1 < 1 := q_lt_one_of_charged hf00 hx₀
      have hq01 : q ν₁ R p.1 < 1 := q_lt_one_of_charged hf01 hx₀
      have hq10 : q ν₀ R p.2 < 1 := q_lt_one_of_charged hf10 hx₁
      have hq11 : q ν₁ R p.2 < 1 := q_lt_one_of_charged hf11 hx₁
      -- the pair degree is below one
      have hqp : q (prodPMF ν₀ ν₁) (SquareRel R) p < 1 := by
        have h := ENNReal.toReal_mono rE_ne_top (rE_square_ge_straight ν₀ ν₁ R p.1 p.2)
        rw [ENNReal.toReal_mul, toReal_rE_eq, toReal_rE_eq] at h
        have hp : (rE (prodPMF ν₀ ν₁) (SquareRel R) (p.1, p.2)).toReal
            = 1 - q (prodPMF ν₀ ν₁) (SquareRel R) (p.1, p.2) :=
          toReal_rE_eq (prodPMF ν₀ ν₁) (SquareRel R) (p.1, p.2)
        rw [hp] at h
        have hpos : (0:ℝ) < (1 - q ν₀ R p.1) * (1 - q ν₁ R p.2) := by nlinarith
        have : q (prodPMF ν₀ ν₁) (SquareRel R) (p.1, p.2) < 1 := by nlinarith
        simpa using this
      have hmain := phi_Q_split_four (α := α) (L := L) hα hL0 hL ν₀ ν₁ R p.1 p.2
        hq00 hq01 hq10 hq11
      -- nonnegativity of the main-bound pieces
      have hφ00 : 0 ≤ phi α (q ν₀ R p.1) := phi_nonneg q_nonneg hq00
      have hφ01 : 0 ≤ phi α (q ν₁ R p.1) := phi_nonneg q_nonneg hq01
      have hφ10 : 0 ≤ phi α (q ν₀ R p.2) := phi_nonneg q_nonneg hq10
      have hφ11 : 0 ≤ phi α (q ν₁ R p.2) := phi_nonneg q_nonneg hq11
      have hW00 : (0:ℝ) ≤ (1 - q ν₀ R p.1) ^ (-α) :=
        Real.rpow_nonneg (by linarith) _
      have hW01 : (0:ℝ) ≤ (1 - q ν₁ R p.1) ^ (-α) :=
        Real.rpow_nonneg (by linarith) _
      have hW10 : (0:ℝ) ≤ (1 - q ν₀ R p.2) ^ (-α) :=
        Real.rpow_nonneg (by linarith) _
      have hW11 : (0:ℝ) ≤ (1 - q ν₁ R p.2) ^ (-α) :=
        Real.rpow_nonneg (by linarith) _
      have hc00 : (0:ℝ) ≤ (cOverlap ν₀ R p.1 p.2).toReal := ENNReal.toReal_nonneg
      have hc10 : (0:ℝ) ≤ (cOverlap ν₁ R p.1 p.2).toReal := ENNReal.toReal_nonneg
      -- pass to ℝ≥0∞
      have hphiEq : phiE α (q (prodPMF ν₀ ν₁) (SquareRel R) p)
          = ENNReal.ofReal (phi α (q (prodPMF ν₀ ν₁) (SquareRel R) (p.1, p.2))) := by
        rw [show p = (p.1, p.2) from rfl] at *
        exact phiE_of_lt (by simpa using hqp)
      rw [hphiEq]
      calc ENNReal.ofReal (phi α (q (prodPMF ν₀ ν₁) (SquareRel R) (p.1, p.2)))
          ≤ ENNReal.ofReal (L / 2 * ((phi α (q ν₀ R p.1) + phi α (q ν₁ R p.1))
                + (phi α (q ν₀ R p.2) + phi α (q ν₁ R p.2)))
              + (L * chordConst α / 2 + 5)
                * ((phi α (q ν₀ R p.1) + phi α (q ν₁ R p.1))
                    * (phi α (q ν₀ R p.2) + phi α (q ν₁ R p.2)))
              + (cOverlap ν₀ R p.1 p.2).toReal
                * ((1 - q ν₀ R p.1) ^ (-α) * (1 - q ν₁ R p.2) ^ (-α))
              + (cOverlap ν₁ R p.1 p.2).toReal
                * ((1 - q ν₁ R p.1) ^ (-α) * (1 - q ν₀ R p.2) ^ (-α))) :=
            ENNReal.ofReal_le_ofReal hmain
        _ ≤ cL * (F p.1 + F p.2) + c₅ * (F p.1 * F p.2)
              + cOverlap ν₀ R p.1 p.2 * (WnnD α ν₀ R p.1 * WnnD α ν₁ R p.2)
              + cOverlap ν₁ R p.1 p.2 * (WnnD α ν₁ R p.1 * WnnD α ν₀ R p.2) := by
            have e1 : ENNReal.ofReal (L / 2 * ((phi α (q ν₀ R p.1) + phi α (q ν₁ R p.1))
                  + (phi α (q ν₀ R p.2) + phi α (q ν₁ R p.2))))
                = cL * (F p.1 + F p.2) := by
              simp only [hF]
              rw [hcL, ENNReal.ofReal_mul (by linarith),
                ENNReal.ofReal_add (by linarith) (by linarith),
                ENNReal.ofReal_add hφ00 hφ01, ENNReal.ofReal_add hφ10 hφ11,
                phiE_of_lt hq00, phiE_of_lt hq01, phiE_of_lt hq10, phiE_of_lt hq11]
            have e2 : ENNReal.ofReal ((L * chordConst α / 2 + 5)
                  * ((phi α (q ν₀ R p.1) + phi α (q ν₁ R p.1))
                      * (phi α (q ν₀ R p.2) + phi α (q ν₁ R p.2))))
                = c₅ * (F p.1 * F p.2) := by
              simp only [hF]
              rw [hc₅, ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_mul (by linarith),
                ENNReal.ofReal_add hφ00 hφ01, ENNReal.ofReal_add hφ10 hφ11,
                phiE_of_lt hq00, phiE_of_lt hq01, phiE_of_lt hq10, phiE_of_lt hq11]
            have e3 : ENNReal.ofReal ((cOverlap ν₀ R p.1 p.2).toReal
                  * ((1 - q ν₀ R p.1) ^ (-α) * (1 - q ν₁ R p.2) ^ (-α)))
                = cOverlap ν₀ R p.1 p.2 * (WnnD α ν₀ R p.1 * WnnD α ν₁ R p.2) := by
              rw [ENNReal.ofReal_mul hc00, ENNReal.ofReal_mul hW00,
                ENNReal.ofReal_toReal (cOverlap_ne_top ν₀ R p.1 p.2), WnnD, WnnD]
            have e4 : ENNReal.ofReal ((cOverlap ν₁ R p.1 p.2).toReal
                  * ((1 - q ν₁ R p.1) ^ (-α) * (1 - q ν₀ R p.2) ^ (-α)))
                = cOverlap ν₁ R p.1 p.2 * (WnnD α ν₁ R p.1 * WnnD α ν₀ R p.2) := by
              rw [ENNReal.ofReal_mul hc10, ENNReal.ofReal_mul hW01,
                ENNReal.ofReal_toReal (cOverlap_ne_top ν₁ R p.1 p.2), WnnD, WnnD]
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity), e1, e2, e3, e4]
  -- sum the termwise bound and split into four totals
  have hsplit : PhiD α (prodPMF μ₀ μ₁) (prodPMF ν₀ ν₁) (SquareRel R)
      ≤ cL * ((∑' x, μ₀ x * F x) + ∑' x, μ₁ x * F x)
        + c₅ * ((∑' x, μ₀ x * F x) * ∑' x, μ₁ x * F x)
        + (∑' y, ν₀ y * (HnnD α μ₀ ν₀ R y * HnnD α μ₁ ν₁ R y))
        + (∑' y, ν₁ y * (HnnD α μ₀ ν₁ R y * HnnD α μ₁ ν₀ R y)) := by
    calc PhiD α (prodPMF μ₀ μ₁) (prodPMF ν₀ ν₁) (SquareRel R)
        ≤ ∑' p : X × X, prodPMF μ₀ μ₁ p
            * (cL * (F p.1 + F p.2) + c₅ * (F p.1 * F p.2)
              + cOverlap ν₀ R p.1 p.2 * (WnnD α ν₀ R p.1 * WnnD α ν₁ R p.2)
              + cOverlap ν₁ R p.1 p.2 * (WnnD α ν₁ R p.1 * WnnD α ν₀ R p.2)) := by
          rw [PhiD]
          exact ENNReal.tsum_le_tsum hterm
      _ = cL * ((∑' x, μ₀ x * F x) + ∑' x, μ₁ x * F x)
            + c₅ * ((∑' x, μ₀ x * F x) * ∑' x, μ₁ x * F x)
            + (∑' y, ν₀ y * (HnnD α μ₀ ν₀ R y * HnnD α μ₁ ν₁ R y))
            + (∑' y, ν₁ y * (HnnD α μ₀ ν₁ R y * HnnD α μ₁ ν₀ R y)) := by
          rw [tsum_congr fun p : X × X => show prodPMF μ₀ μ₁ p
              * (cL * (F p.1 + F p.2) + c₅ * (F p.1 * F p.2)
                + cOverlap ν₀ R p.1 p.2 * (WnnD α ν₀ R p.1 * WnnD α ν₁ R p.2)
                + cOverlap ν₁ R p.1 p.2 * (WnnD α ν₁ R p.1 * WnnD α ν₀ R p.2))
              = cL * (prodPMF μ₀ μ₁ p * F p.1 + prodPMF μ₀ μ₁ p * F p.2)
                + c₅ * (prodPMF μ₀ μ₁ p * (F p.1 * F p.2))
                + μ₀ p.1 * μ₁ p.2
                  * (cOverlap ν₀ R p.1 p.2 * (WnnD α ν₀ R p.1 * WnnD α ν₁ R p.2))
                + μ₀ p.1 * μ₁ p.2
                  * (cOverlap ν₁ R p.1 p.2 * (WnnD α ν₁ R p.1 * WnnD α ν₀ R p.2))
              from by rw [prodPMF_apply]; ring,
            ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add,
            ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_add,
            tsum_mass_left, tsum_mass_right, tsum_mass_prod,
            fubini_swap_two, fubini_swap_two]
  -- bound the four totals
  have hFsum₀ : (∑' x, μ₀ x * F x) ≤ 2 * M := by
    simp only [hF]
    rw [tsum_rowsum]
    calc PhiD α μ₀ ν₀ R + PhiD α μ₀ ν₁ R ≤ M + M := add_le_add h00 h01
      _ = 2 * M := (two_mul M).symm
  have hFsum₁ : (∑' x, μ₁ x * F x) ≤ 2 * M := by
    simp only [hF]
    rw [tsum_rowsum]
    calc PhiD α μ₁ ν₀ R + PhiD α μ₁ ν₁ R ≤ M + M := add_le_add h10 h11
      _ = 2 * M := (two_mul M).symm
  have hEH : ∀ (νc ν₀' ν₁' : PMF X), PhiD α νc μ₀ R ≤ M → PhiD α νc μ₁ R ≤ M →
      PhiD α μ₀ ν₀' R ≤ M → PhiD α μ₁ ν₁' R ≤ M →
      2 * ∑' y, νc y * (HnnD α μ₀ ν₀' R y * HnnD α μ₁ ν₁' R y)
        ≤ ENNReal.ofReal (2 * (1 + δ) * K) * M
          + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2 := by
    intro νc ν₀' ν₁' hv0 hv1 hk0 hk1
    have hsq : 2 * ∑' y, νc y * (HnnD α μ₀ ν₀' R y * HnnD α μ₁ ν₁' R y)
        ≤ (∑' y, νc y * HnnD α μ₀ ν₀' R y ^ 2) + ∑' y, νc y * HnnD α μ₁ ν₁' R y ^ 2 := by
      rw [ENNReal.tsum_mul_left.symm, ← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun y => ?_
      calc 2 * (νc y * (HnnD α μ₀ ν₀' R y * HnnD α μ₁ ν₁' R y))
          = νc y * (2 * (HnnD α μ₀ ν₀' R y * HnnD α μ₁ ν₁' R y)) := by ring
        _ ≤ νc y * (HnnD α μ₀ ν₀' R y ^ 2 + HnnD α μ₁ ν₁' R y ^ 2) :=
            mul_le_mul_right (ennreal_two_mul_le_add_sq _ _) _
        _ = νc y * HnnD α μ₀ ν₀' R y ^ 2 + νc y * HnnD α μ₁ ν₁' R y ^ 2 := by ring
    have hH₀ := EHsqD_le hα hδ hK0 hK νc μ₀ ν₀' R hsymm
    have hH₁ := EHsqD_le hα hδ hK0 hK νc μ₁ ν₁' R hsymm
    have hMsq : ∀ (A B : PMF X), PhiD α νc A R ≤ M → PhiD α A B R ≤ M →
        ENNReal.ofReal ((1 + δ) * K) * PhiD α νc A R
            + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * PhiD α A B R ^ 2
          ≤ ENNReal.ofReal ((1 + δ) * K) * M
            + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * M ^ 2 := by
      intro A B hA hB
      gcongr
    calc 2 * ∑' y, νc y * (HnnD α μ₀ ν₀' R y * HnnD α μ₁ ν₁' R y)
        ≤ (ENNReal.ofReal ((1 + δ) * K) * PhiD α νc μ₀ R
              + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * PhiD α μ₀ ν₀' R ^ 2)
            + (ENNReal.ofReal ((1 + δ) * K) * PhiD α νc μ₁ R
              + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * PhiD α μ₁ ν₁' R ^ 2) :=
          le_trans hsq (add_le_add hH₀ hH₁)
      _ ≤ (ENNReal.ofReal ((1 + δ) * K) * M
              + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * M ^ 2)
            + (ENNReal.ofReal ((1 + δ) * K) * M
              + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * M ^ 2) :=
          add_le_add (hMsq μ₀ ν₀' hv0 hk0) (hMsq μ₁ ν₁' hv1 hk1)
      _ = ENNReal.ofReal (2 * (1 + δ) * K) * M
            + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2 := by
          rw [show (2:ℝ) * (1 + δ) * K = 2 * ((1 + δ) * K) from by ring,
            show (2:ℝ) * (1 + δ⁻¹) * α ^ 2 = 2 * ((1 + δ⁻¹) * α ^ 2) from by ring,
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
          ring
  have hOVL : (∑' y, ν₀ y * (HnnD α μ₀ ν₀ R y * HnnD α μ₁ ν₁ R y))
        + (∑' y, ν₁ y * (HnnD α μ₀ ν₁ R y * HnnD α μ₁ ν₀ R y))
      ≤ ENNReal.ofReal (2 * (1 + δ) * K) * M
        + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2 := by
    have h2 : 2 * ((∑' y, ν₀ y * (HnnD α μ₀ ν₀ R y * HnnD α μ₁ ν₁ R y))
          + ∑' y, ν₁ y * (HnnD α μ₀ ν₁ R y * HnnD α μ₁ ν₀ R y))
        ≤ 2 * (ENNReal.ofReal (2 * (1 + δ) * K) * M
          + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2) := by
      calc 2 * ((∑' y, ν₀ y * (HnnD α μ₀ ν₀ R y * HnnD α μ₁ ν₁ R y))
            + ∑' y, ν₁ y * (HnnD α μ₀ ν₁ R y * HnnD α μ₁ ν₀ R y))
          = 2 * (∑' y, ν₀ y * (HnnD α μ₀ ν₀ R y * HnnD α μ₁ ν₁ R y))
            + 2 * ∑' y, ν₁ y * (HnnD α μ₀ ν₁ R y * HnnD α μ₁ ν₀ R y) := by ring
        _ ≤ (ENNReal.ofReal (2 * (1 + δ) * K) * M
              + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2)
            + (ENNReal.ofReal (2 * (1 + δ) * K) * M
              + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2) :=
            add_le_add (hEH ν₀ ν₀ ν₁ hr00 hr10 h00 h11)
              (hEH ν₁ ν₁ ν₀ hr01 hr11 h01 h10)
        _ = 2 * (ENNReal.ofReal (2 * (1 + δ) * K) * M
            + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2) := by ring
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2
  -- collect the constants
  calc PhiD α (prodPMF μ₀ μ₁) (prodPMF ν₀ ν₁) (SquareRel R)
      ≤ cL * (2 * M + 2 * M) + c₅ * (2 * M * (2 * M))
        + (ENNReal.ofReal (2 * (1 + δ) * K) * M
          + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2) := by
        refine le_trans hsplit ?_
        have hstep := add_le_add (add_le_add
          (mul_le_mul_right (add_le_add hFsum₀ hFsum₁) cL)
          (mul_le_mul_right (mul_le_mul' hFsum₀ hFsum₁) c₅)) hOVL
        calc cL * ((∑' x, μ₀ x * F x) + ∑' x, μ₁ x * F x)
              + c₅ * ((∑' x, μ₀ x * F x) * ∑' x, μ₁ x * F x)
              + (∑' y, ν₀ y * (HnnD α μ₀ ν₀ R y * HnnD α μ₁ ν₁ R y))
              + (∑' y, ν₁ y * (HnnD α μ₀ ν₁ R y * HnnD α μ₁ ν₀ R y))
            = (cL * ((∑' x, μ₀ x * F x) + ∑' x, μ₁ x * F x)
                + c₅ * ((∑' x, μ₀ x * F x) * ∑' x, μ₁ x * F x))
              + ((∑' y, ν₀ y * (HnnD α μ₀ ν₀ R y * HnnD α μ₁ ν₁ R y))
                + ∑' y, ν₁ y * (HnnD α μ₀ ν₁ R y * HnnD α μ₁ ν₀ R y)) := by ring
          _ ≤ (cL * (2 * M + 2 * M) + c₅ * (2 * M * (2 * M)))
              + (ENNReal.ofReal (2 * (1 + δ) * K) * M
                + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2) := hstep
          _ = cL * (2 * M + 2 * M) + c₅ * (2 * M * (2 * M))
              + (ENNReal.ofReal (2 * (1 + δ) * K) * M
                + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2) := by ring
    _ ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
          + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2 := by
        have e1 : cL * (2 * M + 2 * M) = ENNReal.ofReal (2 * L) * M := by
          rw [hcL, show (2:ℝ≥0∞) * M + 2 * M = 4 * M from by ring,
            show ENNReal.ofReal (L / 2) * (4 * M) = (ENNReal.ofReal (L / 2) * 4) * M
              from by ring,
            show (4:ℝ≥0∞) = ENNReal.ofReal (4:ℝ) from by
              rw [ENNReal.ofReal_ofNat],
            ← ENNReal.ofReal_mul (by linarith),
            show (L / 2 * 4 : ℝ) = 2 * L from by ring]
        have e2 : c₅ * (2 * M * (2 * M))
            = ENNReal.ofReal (2 * L * chordConst α + 20) * M ^ 2 := by
          rw [hc₅, show (2:ℝ≥0∞) * M * (2 * M) = 4 * M ^ 2 from by ring,
            show ENNReal.ofReal (L * chordConst α / 2 + 5) * (4 * M ^ 2)
              = (ENNReal.ofReal (L * chordConst α / 2 + 5) * 4) * M ^ 2 from by ring,
            show (4:ℝ≥0∞) = ENNReal.ofReal (4:ℝ) from by
              rw [ENNReal.ofReal_ofNat],
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
        rw [e1, e2]
        have hsplitA : ENNReal.ofReal (2 * L + 2 * (1 + δ) * K)
            = ENNReal.ofReal (2 * L) + ENNReal.ofReal (2 * (1 + δ) * K) := by
          rw [← ENNReal.ofReal_add (by linarith) (by positivity)]
        have hsplitC : ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
            = ENNReal.ofReal (2 * L * chordConst α + 20)
              + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        rw [hsplitA, hsplitC]
        exact le_of_eq (by ring)

end GraphMarkovMatching
