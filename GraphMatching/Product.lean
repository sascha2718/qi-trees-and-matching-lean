/-
`sec:contraction` of `graph_matching_selfcontained.tex`: `thm:product`, the product of
relations.

    Phi(R1 (x) R2, mu1 (x) mu2)  <=  Phi1 + Phi2 + 5 * Phi1 * Phi2

Mathlib has no `PMF.prod`, so `prodPMF` is built here from the `HasSum`
characterisation.

The constant `5` is `2 * alpha`, and the paper's proof is: the good set of
`(x1,x2)` is a rectangle of mass `r1 * r2`, so `q = 1 - r1 r2 <= q1 + q2`,
whence `phi q <= phi q1 * r2^(-alpha) + phi q2 * r1^(-alpha)`; then apply
`eq:W-bound` to each `r^(-alpha)` and use independence.
-/
import GraphMatching.Potential

namespace GraphMatching

open scoped ENNReal Classical

variable {X₁ X₂ : Type*}

/-! ### The product measure and the product relation -/

/-- The product PMF, `(μ₁ ⊗ μ₂)(x₁,x₂) = μ₁ x₁ · μ₂ x₂`. Not in Mathlib, so
constructed here: in `ℝ≥0∞` summability is automatic, so only the total mass
needs checking. -/
noncomputable def prodPMF (μ₁ : PMF X₁) (μ₂ : PMF X₂) : PMF (X₁ × X₂) :=
  ⟨fun p => μ₁ p.1 * μ₂ p.2, by
    have h : ∑' p : X₁ × X₂, μ₁ p.1 * μ₂ p.2 = 1 := by
      rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left, μ₂.tsum_coe, mul_one]
      exact μ₁.tsum_coe
    rw [← h]
    exact ENNReal.summable.hasSum⟩

@[simp] lemma prodPMF_apply (μ₁ : PMF X₁) (μ₂ : PMF X₂) (p : X₁ × X₂) :
    prodPMF μ₁ μ₂ p = μ₁ p.1 * μ₂ p.2 := rfl

/-- The tensor product of relations, `(x₁,x₂) R₁⊗R₂ (y₁,y₂) ↔ x₁ R₁ y₁ ∧ x₂ R₂ y₂`. -/
def ProdRel (R₁ : X₁ → X₁ → Prop) (R₂ : X₂ → X₂ → Prop) : X₁ × X₂ → X₁ × X₂ → Prop :=
  fun x y => R₁ x.1 y.1 ∧ R₂ x.2 y.2

lemma ProdRel_refl {R₁ : X₁ → X₁ → Prop} {R₂ : X₂ → X₂ → Prop}
    (h₁ : ∀ x, R₁ x x) (h₂ : ∀ x, R₂ x x) (x : X₁ × X₂) : ProdRel R₁ R₂ x x :=
  ⟨h₁ x.1, h₂ x.2⟩

lemma ProdRel_symm {R₁ : X₁ → X₁ → Prop} {R₂ : X₂ → X₂ → Prop}
    (h₁ : ∀ a b, R₁ a b → R₁ b a) (h₂ : ∀ a b, R₂ a b → R₂ b a) (x y : X₁ × X₂) :
    ProdRel R₁ R₂ x y → ProdRel R₁ R₂ y x :=
  fun h => ⟨h₁ _ _ h.1, h₂ _ _ h.2⟩

/-! ### The good degree of a product is a product -/

/-- A double `tsum` of a separated product splits. This is the application of
Fubini's theorem that the paper uses; in `ℝ≥0∞` it is unconditional. -/
lemma tsum_prod_split (f₁ : X₁ → ℝ≥0∞) (f₂ : X₂ → ℝ≥0∞) :
    ∑' p : X₁ × X₂, f₁ p.1 * f₂ p.2 = (∑' x, f₁ x) * (∑' y, f₂ y) := by
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]

/-- **The rectangle step**: under `R₁ ⊗ R₂` the labels compatible with
`(x₁,x₂)` form a rectangle, so the good degree is `r₁ · r₂`. -/
lemma rE_prodPMF (μ₁ : PMF X₁) (μ₂ : PMF X₂) (R₁ : X₁ → X₁ → Prop) (R₂ : X₂ → X₂ → Prop)
    (x : X₁ × X₂) :
    rE (prodPMF μ₁ μ₂) (ProdRel R₁ R₂) x = rE μ₁ R₁ x.1 * rE μ₂ R₂ x.2 := by
  simp only [rE]
  rw [← tsum_prod_split (fun y₁ => if R₁ x.1 y₁ then μ₁ y₁ else 0)
        (fun y₂ => if R₂ x.2 y₂ then μ₂ y₂ else 0)]
  refine tsum_congr fun p => ?_
  by_cases h₁ : R₁ x.1 p.1 <;> by_cases h₂ : R₂ x.2 p.2 <;>
    simp [ProdRel, h₁, h₂]

/-! ### The pointwise estimate -/

/-- `(rE).toReal = 1 - q`, the real form of `r = 1 - q`. -/
lemma toReal_rE_eq (μ : PMF X₁) (R : X₁ → X₁ → Prop) (x : X₁) :
    (rE μ R x).toReal = 1 - q μ R x := by
  have h := toReal_rE_add_toReal_qE μ R x
  rw [q]; linarith

/-- The bad degree of a product: `q = 1 - r₁r₂`, i.e. `q₁ + q₂ - q₁q₂`. -/
lemma q_prodPMF (μ₁ : PMF X₁) (μ₂ : PMF X₂) (R₁ : X₁ → X₁ → Prop) (R₂ : X₂ → X₂ → Prop)
    (x : X₁ × X₂) :
    q (prodPMF μ₁ μ₂) (ProdRel R₁ R₂) x = 1 - (1 - q μ₁ R₁ x.1) * (1 - q μ₂ R₂ x.2) := by
  have h1 := toReal_rE_add_toReal_qE (prodPMF μ₁ μ₂) (ProdRel R₁ R₂) x
  rw [rE_prodPMF, ENNReal.toReal_mul, toReal_rE_eq, toReal_rE_eq] at h1
  rw [q]; linarith

/-- The pointwise heart of `thm:product`, in `ℝ`: with `q = 1 - r₁r₂`,

    φ_α(q) ≤ φ_α(q₁) + φ_α(q₂) + 2α φ_α(q₁) φ_α(q₂).

The paper reaches this in two steps: first `φ_α(q) ≤ φ_α(q₁)r₂^{-α} + φ_α(q₂)r₁^{-α}`
(from `q ≤ q₁ + q₂` and `(r₁r₂)^α = r₁^α r₂^α`), then `eq:W-bound` on each
`r^{-α}`. Both steps are exact at any `α ≥ 1`, which is why the constant comes out
as `2α` rather than as a number. -/
lemma phiA_prod_le {α : ℝ} (hα : 1 ≤ α)
    {q₁ q₂ : ℝ} (h₁0 : 0 ≤ q₁) (h₁1 : q₁ < 1) (h₂0 : 0 ≤ q₂) (h₂1 : q₂ < 1) :
    phiA α (1 - (1 - q₁) * (1 - q₂))
      ≤ phiA α q₁ + phiA α q₂ + (2 * α) * (phiA α q₁ * phiA α q₂) := by
  have hr₁ : (0 : ℝ) < 1 - q₁ := by linarith
  have hr₂ : (0 : ℝ) < 1 - q₂ := by linarith
  have hp₁ : (0 : ℝ) < (1 - q₁) ^ α := Real.rpow_pos_of_pos hr₁ α
  have hp₂ : (0 : ℝ) < (1 - q₂) ^ α := Real.rpow_pos_of_pos hr₂ α
  -- `1 - (1 - (1-q₁)(1-q₂)) = (1-q₁)(1-q₂)`, so the denominator factors
  have hden : (1 - (1 - (1 - q₁) * (1 - q₂))) ^ α = (1 - q₁) ^ α * (1 - q₂) ^ α := by
    have : (1 : ℝ) - (1 - (1 - q₁) * (1 - q₂)) = (1 - q₁) * (1 - q₂) := by ring
    rw [this, Real.mul_rpow hr₁.le hr₂.le]
  -- step 1: `φ_α(q) ≤ φ_α(q₁)·r₂^{-α} + φ_α(q₂)·r₁^{-α}`; both sides over `r₁^α r₂^α`
  have hkey : phiA α q₁ * (1 - q₂) ^ (-α) + phiA α q₂ * (1 - q₁) ^ (-α)
      = (q₁ + q₂) / ((1 - q₁) ^ α * (1 - q₂) ^ α) := by
    rw [phiA, phiA, Real.rpow_neg hr₁.le, Real.rpow_neg hr₂.le]
    field_simp
  have step1 : phiA α (1 - (1 - q₁) * (1 - q₂))
      ≤ phiA α q₁ * (1 - q₂) ^ (-α) + phiA α q₂ * (1 - q₁) ^ (-α) := by
    rw [hkey, phiA, hden]
    gcongr
    nlinarith [mul_nonneg h₁0 h₂0]
  -- step 2: `eq:W-bound` on each factor
  have e₁ := rpow_neg_alpha_leA hα h₁1
  have e₂ := rpow_neg_alpha_leA hα h₂1
  have hq₁ : 0 ≤ phiA α q₁ := phiA_nonneg α h₁0 h₁1
  have hq₂ : 0 ≤ phiA α q₂ := phiA_nonneg α h₂0 h₂1
  nlinarith [step1, e₁, e₂, hq₁, hq₂, mul_nonneg hq₁ hq₂]

/-- `thm:product` pointwise at the pinned exponent, where `2α = 5`. -/
lemma phi_prod_le {q₁ q₂ : ℝ} (h₁0 : 0 ≤ q₁) (h₁1 : q₁ < 1) (h₂0 : 0 ≤ q₂) (h₂1 : q₂ < 1) :
    phi (1 - (1 - q₁) * (1 - q₂)) ≤ phi q₁ + phi q₂ + 5 * (phi q₁ * phi q₂) := by
  have h := phiA_prod_le one_le_alpha h₁0 h₁1 h₂0 h₂1
  simp only [← phi_eq_phiA] at h
  have : (2 : ℝ) * alpha = 5 := by norm_num [alpha]
  rwa [this] at h

/-! ### `thm:product` -/

/-- `ofReal` distributes over the shape of the pointwise bound, for nonnegative
arguments and a nonnegative coefficient. -/
lemma ofReal_expandA {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (a + b + c * (a * b))
      = ENNReal.ofReal a + ENNReal.ofReal b
        + ENNReal.ofReal c * (ENNReal.ofReal a * ENNReal.ofReal b) := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add ha hb,
    ENNReal.ofReal_mul hc, ENNReal.ofReal_mul ha]

/-- `ofReal_expandA` at the pinned coefficient `5 = 2α`. -/
lemma ofReal_expand {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (a + b + 5 * (a * b))
      = ENNReal.ofReal a + ENNReal.ofReal b
        + 5 * (ENNReal.ofReal a * ENNReal.ofReal b) := by
  rw [ofReal_expandA (by norm_num : (0 : ℝ) ≤ 5) ha hb]
  norm_num

/-- **`thm:product`** (product of relations):

    Φ(R₁ ⊗ R₂, μ₁ ⊗ μ₂) ≤ Φ₁ + Φ₂ + 5 Φ₁ Φ₂.

Reflexivity of each factor is needed exactly where the paper needs it: to know
`q_i < 1` on the support, so that `φ(q_i)` is defined and the pointwise bound
applies. Symmetry is *not* needed here, and is not assumed. -/
theorem PhiA_prodPMF_le {α : ℝ} (hα : 1 ≤ α) (μ₁ : PMF X₁) (μ₂ : PMF X₂)
    (R₁ : X₁ → X₁ → Prop) (R₂ : X₂ → X₂ → Prop)
    (hrefl₁ : ∀ x, R₁ x x) (hrefl₂ : ∀ x, R₂ x x) :
    PhiA α (prodPMF μ₁ μ₂) (ProdRel R₁ R₂)
      ≤ PhiA α μ₁ R₁ + PhiA α μ₂ R₂
        + ENNReal.ofReal (2 * α) * (PhiA α μ₁ R₁ * PhiA α μ₂ R₂) := by
  have hc : (0 : ℝ) ≤ 2 * α := by linarith
  set C : ℝ≥0∞ := ENNReal.ofReal (2 * α) with hC
  -- the summands of `Φ₁` and `Φ₂`
  set A₁ : X₁ → ℝ≥0∞ := fun x => μ₁ x * ENNReal.ofReal (phiA α (q μ₁ R₁ x)) with hA₁
  set A₂ : X₂ → ℝ≥0∞ := fun x => μ₂ x * ENNReal.ofReal (phiA α (q μ₂ R₂ x)) with hA₂
  -- the pointwise bound, with the off-support cases handled by `μ x = 0`
  have key : ∀ p : X₁ × X₂,
      prodPMF μ₁ μ₂ p * ENNReal.ofReal (phiA α (q (prodPMF μ₁ μ₂) (ProdRel R₁ R₂) p))
        ≤ A₁ p.1 * μ₂ p.2 + μ₁ p.1 * A₂ p.2 + C * (A₁ p.1 * A₂ p.2) := by
    rintro ⟨x₁, x₂⟩
    by_cases hx₁ : μ₁ x₁ = 0
    · simp [hA₁, hx₁]
    by_cases hx₂ : μ₂ x₂ = 0
    · simp [hA₂, hx₂]
    have hb := phiA_prod_le hα (q_nonneg (μ := μ₁) (R := R₁) (x := x₁))
      (q_lt_one (hrefl₁ x₁) hx₁)
      (q_nonneg (μ := μ₂) (R := R₂) (x := x₂)) (q_lt_one (hrefl₂ x₂) hx₂)
    have hp₁ : 0 ≤ phiA α (q μ₁ R₁ x₁) := phiA_nonneg α q_nonneg (q_lt_one (hrefl₁ x₁) hx₁)
    have hp₂ : 0 ≤ phiA α (q μ₂ R₂ x₂) := phiA_nonneg α q_nonneg (q_lt_one (hrefl₂ x₂) hx₂)
    calc prodPMF μ₁ μ₂ (x₁, x₂)
          * ENNReal.ofReal (phiA α (q (prodPMF μ₁ μ₂) (ProdRel R₁ R₂) (x₁, x₂)))
        = μ₁ x₁ * μ₂ x₂
            * ENNReal.ofReal (phiA α (1 - (1 - q μ₁ R₁ x₁) * (1 - q μ₂ R₂ x₂))) := by
          rw [q_prodPMF]; rfl
      _ ≤ μ₁ x₁ * μ₂ x₂
            * ENNReal.ofReal (phiA α (q μ₁ R₁ x₁) + phiA α (q μ₂ R₂ x₂)
              + (2 * α) * (phiA α (q μ₁ R₁ x₁) * phiA α (q μ₂ R₂ x₂))) := by
          gcongr
      _ = A₁ x₁ * μ₂ x₂ + μ₁ x₁ * A₂ x₂ + C * (A₁ x₁ * A₂ x₂) := by
          rw [ofReal_expandA hc hp₁ hp₂, hA₁, hA₂, hC]; ring
  calc PhiA α (prodPMF μ₁ μ₂) (ProdRel R₁ R₂)
      ≤ ∑' p : X₁ × X₂, (A₁ p.1 * μ₂ p.2 + μ₁ p.1 * A₂ p.2 + C * (A₁ p.1 * A₂ p.2)) :=
        ENNReal.tsum_le_tsum key
    _ = PhiA α μ₁ R₁ + PhiA α μ₂ R₂ + C * (PhiA α μ₁ R₁ * PhiA α μ₂ R₂) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
        rw [tsum_prod_split A₁ (fun x => μ₂ x), tsum_prod_split (fun x => μ₁ x) A₂]
        simp_rw [show ∀ p : X₁ × X₂, C * (A₁ p.1 * A₂ p.2) = (C * A₁ p.1) * A₂ p.2 from
          fun p => by ring]
        rw [tsum_prod_split (fun x => C * A₁ x) A₂, ENNReal.tsum_mul_left]
        rw [μ₁.tsum_coe, μ₂.tsum_coe]
        simp only [PhiA, hA₁, hA₂, mul_one, one_mul]
        ring

/-- **`thm:product`** at the pinned exponent, where the product term carries `2α = 5`. -/
theorem Phi_prodPMF_le (μ₁ : PMF X₁) (μ₂ : PMF X₂)
    (R₁ : X₁ → X₁ → Prop) (R₂ : X₂ → X₂ → Prop)
    (hrefl₁ : ∀ x, R₁ x x) (hrefl₂ : ∀ x, R₂ x x) :
    Phi (prodPMF μ₁ μ₂) (ProdRel R₁ R₂)
      ≤ Phi μ₁ R₁ + Phi μ₂ R₂ + 5 * (Phi μ₁ R₁ * Phi μ₂ R₂) := by
  have h := PhiA_prodPMF_le one_le_alpha μ₁ μ₂ R₁ R₂ hrefl₁ hrefl₂
  have hc : ENNReal.ofReal (2 * alpha) = 5 := by
    rw [show (2 : ℝ) * alpha = 5 from by norm_num [alpha]]; simp
  rw [hc] at h
  simpa only [Phi_eq_PhiA] using h

end GraphMatching
