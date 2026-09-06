/-
The transfer ledger, part 1: the **restricted four-law**
(`arbitrary_offspring_matching.tex`, `thm:res-four-law` in `sec:rows`).

The screened design never evaluates `φ_α` on a zero-degree point, so the
four-law must be averaged over the doubly-positive set only, against the
positive-set restricted potentials `(†)`.  The pointwise main bound
`phi_Q_split_four` carries over verbatim (positivity now comes from the
restriction, not from finiteness of full potentials); in the overlap
estimate the reversed bad degree can equal one on the reversed zero
interface, whose mass is the extra additive term: these are the
`B`-entries toward reverse-directed screens (`zMass ≤ screen` by
`eq:screen-mass`).

* `PhiDres`: the restricted directed potential `(†)`;
* `zMass`: the zero-interface mass `z(ρ_s,ρ_t)` of a source law against a
  target law;
* `failureD`: the directed mismatch mass `∑ ρ_s(x) q_{ρ_t}(x)`, at most
  the restricted potential plus the zero-interface mass
  (`failureD_le_PhiDres_add_zMass`);
* `q_lt_one_of_rE_ne_zero`: positivity gives `q < 1` pointwise;
* `phiE_square_main_le`: the pointwise main bound on doubly-positive
  pairs, in the safe `ℝ≥0∞` form;
* `PhiDres_fourlaw_le` (part 2 below): the averaged restricted four-law
  with linear constant `2L + 2(1+δ)K`, quadratic constant
  `2L·c_α + 20 + 2(1+δ⁻¹)α²`, and reversed-zero-mass constant `2(1+δ)`.
-/
import GraphMarkovMatching.FourLaw.Assembly
import GraphMarkovMatching.Process.Screens
import GraphMarkovMatching.Process.Hall

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

/-! ### Restricted coordinates -/

/-- The positive-set restricted directed potential `(†)`:
`Φres(ρ_s → ρ_t) = 𝔼_{X∼ρ_s}[𝟙_{r_{ρ_t}(X)>0} φ_α(q_{ρ_t}(X))]`. -/
noncomputable def PhiDres (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, ρs x * (if rE ρt R x = 0 then 0 else phiE α (q ρt R x))

/-- The zero-interface mass `z(ρ_s,ρ_t)`: the `ρ_s`-mass of points with
zero good degree toward `ρ_t`. -/
noncomputable def zMass (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' y, ρs y * (if rE ρt R y = 0 then 1 else 0)

/-- The directed mismatch mass `∑_x ρ_s(x) q_{ρ_t}(x)` between two laws. -/
noncomputable def failureD (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, ρs x * qE ρt R x

/-- Raw directed failure is bounded by the restricted potential plus its
zero interface: on the positive set `q ≤ φ_α(q)`, and on the zero
interface the bad degree is at most one. -/
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

/-- The restricted inverse-power weight. -/
noncomputable def WresD (α : ℝ) (ρt : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  if rE ρt R x = 0 then 0 else WnnD α ρt R x

/-- The restricted `H`-function of the overlap estimate. -/
noncomputable def HresD (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, ρs x * (if ¬ R x y then WresD α ρt R x else 0)

/-- The restricted `K`-function. -/
noncomputable def KresD (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, ρs x * (if ¬ R x y then
    (if rE ρt R x = 0 then 0 else phiE α (q ρt R x)) else 0)

/-- On the positive set the bad degree is below one. -/
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

/-! ### The pointwise main bound on doubly-positive pairs -/

/-- **The restricted pointwise main bound**: on a pair whose four
directed degrees are positive, the square potential summand obeys the
four-law main estimate, in the safe `ℝ≥0∞` form.  Positivity of the
degrees replaces finiteness of the full potentials. -/
lemma phiE_square_main_le {α L : ℝ} (hα : 1 ≤ α)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (ν₀ ν₁ : PMF X) (R : X → X → Prop) (x₀ x₁ : X)
    (h00 : rE ν₀ R x₀ ≠ 0) (h01 : rE ν₁ R x₀ ≠ 0)
    (h10 : rE ν₀ R x₁ ≠ 0) (h11 : rE ν₁ R x₁ ≠ 0) :
    phiE α (q (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁))
      ≤ ENNReal.ofReal (L / 2)
          * ((phiE α (q ν₀ R x₀) + phiE α (q ν₁ R x₀))
            + (phiE α (q ν₀ R x₁) + phiE α (q ν₁ R x₁)))
        + ENNReal.ofReal (L * chordConst α / 2 + 5)
          * ((phiE α (q ν₀ R x₀) + phiE α (q ν₁ R x₀))
            * (phiE α (q ν₀ R x₁) + phiE α (q ν₁ R x₁)))
        + cOverlap ν₀ R x₀ x₁ * (WnnD α ν₀ R x₀ * WnnD α ν₁ R x₁)
        + cOverlap ν₁ R x₀ x₁ * (WnnD α ν₁ R x₀ * WnnD α ν₀ R x₁) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hq00 : q ν₀ R x₀ < 1 := q_lt_one_of_rE_ne_zero h00
  have hq01 : q ν₁ R x₀ < 1 := q_lt_one_of_rE_ne_zero h01
  have hq10 : q ν₀ R x₁ < 1 := q_lt_one_of_rE_ne_zero h10
  have hq11 : q ν₁ R x₁ < 1 := q_lt_one_of_rE_ne_zero h11
  -- the pair degree is below one
  have hqp : q (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁) < 1 := by
    have h := ENNReal.toReal_mono rE_ne_top (rE_square_ge_straight ν₀ ν₁ R x₀ x₁)
    rw [ENNReal.toReal_mul, toReal_rE_eq, toReal_rE_eq] at h
    have hp : (rE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)).toReal
        = 1 - q (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁) :=
      toReal_rE_eq (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)
    rw [hp] at h
    have hpos : (0:ℝ) < (1 - q ν₀ R x₀) * (1 - q ν₁ R x₁) := by nlinarith
    nlinarith
  have hmain := phi_Q_split_four (α := α) (L := L) hα hL0 hL ν₀ ν₁ R x₀ x₁
    hq00 hq01 hq10 hq11
  have hφ00 : 0 ≤ phi α (q ν₀ R x₀) := phi_nonneg q_nonneg hq00
  have hφ01 : 0 ≤ phi α (q ν₁ R x₀) := phi_nonneg q_nonneg hq01
  have hφ10 : 0 ≤ phi α (q ν₀ R x₁) := phi_nonneg q_nonneg hq10
  have hφ11 : 0 ≤ phi α (q ν₁ R x₁) := phi_nonneg q_nonneg hq11
  have hW00 : (0:ℝ) ≤ (1 - q ν₀ R x₀) ^ (-α) := Real.rpow_nonneg (by linarith) _
  have hW01 : (0:ℝ) ≤ (1 - q ν₁ R x₀) ^ (-α) := Real.rpow_nonneg (by linarith) _
  have hc00 : (0:ℝ) ≤ (cOverlap ν₀ R x₀ x₁).toReal := ENNReal.toReal_nonneg
  have hc10 : (0:ℝ) ≤ (cOverlap ν₁ R x₀ x₁).toReal := ENNReal.toReal_nonneg
  have hcc : 0 ≤ chordConst α := chordConst_nonneg hα0
  rw [phiE_of_lt hqp]
  calc ENNReal.ofReal (phi α (q (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)))
      ≤ ENNReal.ofReal (L / 2 * ((phi α (q ν₀ R x₀) + phi α (q ν₁ R x₀))
            + (phi α (q ν₀ R x₁) + phi α (q ν₁ R x₁)))
          + (L * chordConst α / 2 + 5)
            * ((phi α (q ν₀ R x₀) + phi α (q ν₁ R x₀))
                * (phi α (q ν₀ R x₁) + phi α (q ν₁ R x₁)))
          + (cOverlap ν₀ R x₀ x₁).toReal
            * ((1 - q ν₀ R x₀) ^ (-α) * (1 - q ν₁ R x₁) ^ (-α))
          + (cOverlap ν₁ R x₀ x₁).toReal
            * ((1 - q ν₁ R x₀) ^ (-α) * (1 - q ν₀ R x₁) ^ (-α))) :=
        ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal (L / 2)
          * ((phiE α (q ν₀ R x₀) + phiE α (q ν₁ R x₀))
            + (phiE α (q ν₀ R x₁) + phiE α (q ν₁ R x₁)))
        + ENNReal.ofReal (L * chordConst α / 2 + 5)
          * ((phiE α (q ν₀ R x₀) + phiE α (q ν₁ R x₀))
            * (phiE α (q ν₀ R x₁) + phiE α (q ν₁ R x₁)))
        + cOverlap ν₀ R x₀ x₁ * (WnnD α ν₀ R x₀ * WnnD α ν₁ R x₁)
        + cOverlap ν₁ R x₀ x₁ * (WnnD α ν₁ R x₀ * WnnD α ν₀ R x₁) := by
        have e1 : ENNReal.ofReal (L / 2 * ((phi α (q ν₀ R x₀) + phi α (q ν₁ R x₀))
              + (phi α (q ν₀ R x₁) + phi α (q ν₁ R x₁))))
            = ENNReal.ofReal (L / 2)
              * ((phiE α (q ν₀ R x₀) + phiE α (q ν₁ R x₀))
                + (phiE α (q ν₀ R x₁) + phiE α (q ν₁ R x₁))) := by
          rw [ENNReal.ofReal_mul (by linarith),
            ENNReal.ofReal_add (by linarith) (by linarith),
            ENNReal.ofReal_add hφ00 hφ01, ENNReal.ofReal_add hφ10 hφ11,
            phiE_of_lt hq00, phiE_of_lt hq01, phiE_of_lt hq10, phiE_of_lt hq11]
        have e2 : ENNReal.ofReal ((L * chordConst α / 2 + 5)
              * ((phi α (q ν₀ R x₀) + phi α (q ν₁ R x₀))
                  * (phi α (q ν₀ R x₁) + phi α (q ν₁ R x₁))))
            = ENNReal.ofReal (L * chordConst α / 2 + 5)
              * ((phiE α (q ν₀ R x₀) + phiE α (q ν₁ R x₀))
                * (phiE α (q ν₀ R x₁) + phiE α (q ν₁ R x₁))) := by
          rw [ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by linarith),
            ENNReal.ofReal_add hφ00 hφ01, ENNReal.ofReal_add hφ10 hφ11,
            phiE_of_lt hq00, phiE_of_lt hq01, phiE_of_lt hq10, phiE_of_lt hq11]
        have e3 : ENNReal.ofReal ((cOverlap ν₀ R x₀ x₁).toReal
              * ((1 - q ν₀ R x₀) ^ (-α) * (1 - q ν₁ R x₁) ^ (-α)))
            = cOverlap ν₀ R x₀ x₁ * (WnnD α ν₀ R x₀ * WnnD α ν₁ R x₁) := by
          rw [ENNReal.ofReal_mul hc00, ENNReal.ofReal_mul hW00,
            ENNReal.ofReal_toReal (cOverlap_ne_top ν₀ R x₀ x₁), WnnD, WnnD]
        have e4 : ENNReal.ofReal ((cOverlap ν₁ R x₀ x₁).toReal
              * ((1 - q ν₁ R x₀) ^ (-α) * (1 - q ν₀ R x₁) ^ (-α)))
            = cOverlap ν₁ R x₀ x₁ * (WnnD α ν₁ R x₀ * WnnD α ν₀ R x₁) := by
          rw [ENNReal.ofReal_mul hc10, ENNReal.ofReal_mul hW01,
            ENNReal.ofReal_toReal (cOverlap_ne_top ν₁ R x₀ x₁), WnnD, WnnD]
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity), e1, e2, e3, e4]

/-! ### Restricted averaging -/

/-- The directed Fubini swap for arbitrary weights. -/
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

/-- The restricted Fubini swap. -/
lemma fubini_swap_two_res (α : ℝ) (μ₀ μ₁ νc ν₀ ν₁ : PMF X)
    (R : X → X → Prop) :
    ∑' p : X × X, μ₀ p.1 * μ₁ p.2
        * (cOverlap νc R p.1 p.2 * (WresD α ν₀ R p.1 * WresD α ν₁ R p.2))
      = ∑' y, νc y * (HresD α μ₀ ν₀ R y * HresD α μ₁ ν₁ R y) :=
  fubini_swap_two_gen μ₀ μ₁ νc R (WresD α ν₀ R) (WresD α ν₁ R)

/-- `Hres(y) ≤ q_{ρ_s}(y) + α·Kres(y)`, via symmetry of `R`. -/
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

/-- `Kres(y) ≤ Φres(ρs → ρt)`. -/
lemma KresD_le_PhiDres (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X) :
    KresD α ρs ρt R y ≤ PhiDres α ρs ρt R := by
  rw [KresD, PhiDres]
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  by_cases h : R x y <;> simp [h]

/-- `𝔼_{Y∼ρ_s}[q_{ρ_t}(Y)²] ≤ K·Φres(ρ_s → ρ_t) + z(ρ_s,ρ_t)`: the reversed square
splits into its positive part and the reversed zero-interface mass. -/
lemma EqsqD_res_le {α K : ℝ} (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (ρs ρt : PMF X) (R : X → X → Prop) :
    ∑' y, ρs y * qE ρt R y ^ 2
      ≤ ENNReal.ofReal K * PhiDres α ρs ρt R + zMass ρs ρt R := by
  have hpt : ∀ y, ρs y * qE ρt R y ^ 2
      ≤ ENNReal.ofReal K
          * (ρs y * (if rE ρt R y = 0 then 0 else phiE α (q ρt R y)))
        + ρs y * (if rE ρt R y = 0 then 1 else 0) := by
    intro y
    by_cases hres : rE ρt R y = 0
    · rw [if_pos hres, if_pos hres, mul_zero, mul_zero, zero_add]
      refine mul_le_mul_right ?_ _
      calc qE ρt R y ^ 2 ≤ 1 ^ 2 := pow_le_pow_left' qE_le_one 2
        _ = 1 := one_pow 2
    · rw [if_neg hres, if_neg hres]
      have hq : q ρt R y < 1 := q_lt_one_of_rE_ne_zero hres
      have hqE : qE ρt R y = ENNReal.ofReal (q ρt R y) :=
        (ENNReal.ofReal_toReal qE_ne_top).symm
      refine le_trans ?_ le_self_add
      rw [hqE, ← ENNReal.ofReal_pow q_nonneg, phiE_of_lt hq]
      calc ρs y * ENNReal.ofReal (q ρt R y ^ 2)
          ≤ ρs y * ENNReal.ofReal (K * phi α (q ρt R y)) := by
            gcongr
            exact q_sq_le (hK _ q_nonneg q_le_one) q_nonneg hq
        _ = ENNReal.ofReal K * (ρs y * ENNReal.ofReal (phi α (q ρt R y))) := by
            rw [ENNReal.ofReal_mul hK0.le]; ring
  calc ∑' y, ρs y * qE ρt R y ^ 2
      ≤ ∑' y, (ENNReal.ofReal K
            * (ρs y * (if rE ρt R y = 0 then 0 else phiE α (q ρt R y)))
          + ρs y * (if rE ρt R y = 0 then 1 else 0)) :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal K * PhiDres α ρs ρt R + zMass ρs ρt R := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, PhiDres, zMass]

/-- The averaged restricted `H²`-bound: the reversed potential enters in
restricted form and the reversed zero-interface mass appears additively. -/
lemma EHsqD_res_le {α δ K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ) (hK0 : 0 < K)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (ρ ρs ρt : PMF X) (R : X → X → Prop)
    (hsymm : ∀ a b, R a b → R b a) :
    ∑' y, ρ y * HresD α ρs ρt R y ^ 2
      ≤ ENNReal.ofReal ((1 + δ) * K) * PhiDres α ρ ρs R
        + ENNReal.ofReal (1 + δ) * zMass ρ ρs R
        + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * PhiDres α ρs ρt R ^ 2 := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hHsq : ∀ y, HresD α ρs ρt R y ^ 2
      ≤ ENNReal.ofReal (1 + δ) * qE ρs R y ^ 2
        + ENNReal.ofReal (1 + δ⁻¹)
          * (ENNReal.ofReal α * KresD α ρs ρt R y) ^ 2 := by
    intro y
    calc HresD α ρs ρt R y ^ 2
        ≤ (qE ρs R y + ENNReal.ofReal α * KresD α ρs ρt R y) ^ 2 :=
          pow_le_pow_left' (HresD_le hα ρs ρt R hsymm y) 2
      _ ≤ _ := ennreal_add_sq_le_weighted hδ _ _
  have hKsq : ∑' y, ρ y * KresD α ρs ρt R y ^ 2 ≤ PhiDres α ρs ρt R ^ 2 := by
    calc ∑' y, ρ y * KresD α ρs ρt R y ^ 2
        ≤ ∑' y, ρ y * PhiDres α ρs ρt R ^ 2 :=
          ENNReal.tsum_le_tsum fun y => by
            gcongr
            exact KresD_le_PhiDres α ρs ρt R y
      _ = PhiDres α ρs ρt R ^ 2 := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hdist : ∑' y, ρ y * (ENNReal.ofReal (1 + δ) * qE ρs R y ^ 2
        + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α * KresD α ρs ρt R y) ^ 2)
      = ENNReal.ofReal (1 + δ) * (∑' y, ρ y * qE ρs R y ^ 2)
        + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2
          * ∑' y, ρ y * KresD α ρs ρt R y ^ 2 := by
    rw [tsum_congr fun y => show
        ρ y * (ENNReal.ofReal (1 + δ) * qE ρs R y ^ 2
            + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α * KresD α ρs ρt R y) ^ 2)
          = ENNReal.ofReal (1 + δ) * (ρ y * qE ρs R y ^ 2)
            + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2
              * (ρ y * KresD α ρs ρt R y ^ 2) from by ring,
      ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  have c₁ : ENNReal.ofReal ((1 + δ) * K)
      = ENNReal.ofReal (1 + δ) * ENNReal.ofReal K :=
    ENNReal.ofReal_mul (by linarith)
  have c₂ : ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2)
      = ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2 := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hα0]
  calc ∑' y, ρ y * HresD α ρs ρt R y ^ 2
      ≤ ∑' y, ρ y * (ENNReal.ofReal (1 + δ) * qE ρs R y ^ 2
          + ENNReal.ofReal (1 + δ⁻¹)
            * (ENNReal.ofReal α * KresD α ρs ρt R y) ^ 2) := by
        gcongr with y
        exact hHsq y
    _ = ENNReal.ofReal (1 + δ) * (∑' y, ρ y * qE ρs R y ^ 2)
          + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2
            * ∑' y, ρ y * KresD α ρs ρt R y ^ 2 := hdist
    _ ≤ ENNReal.ofReal (1 + δ)
          * (ENNReal.ofReal K * PhiDres α ρ ρs R + zMass ρ ρs R)
        + ENNReal.ofReal (1 + δ⁻¹) * (ENNReal.ofReal α) ^ 2
          * PhiDres α ρs ρt R ^ 2 := by
        exact add_le_add
          (mul_le_mul_right (EqsqD_res_le hK0 hK ρ ρs R) _)
          (mul_le_mul_right hKsq _)
    _ = ENNReal.ofReal ((1 + δ) * K) * PhiDres α ρ ρs R
        + ENNReal.ofReal (1 + δ) * zMass ρ ρs R
        + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * PhiDres α ρs ρt R ^ 2 := by
        rw [c₁, c₂]; ring

/-! ### The restricted four-law -/

/-- **The restricted four-law contraction**
(`arbitrary_offspring_matching.tex`, `thm:res-four-law` in
`sec:rows`): the square potential averaged over the doubly-positive
set contracts against the eight *restricted* directed potentials, with
the reversed zero-interface masses as the only additional linear input.
The linear constant `2L + 2(1+δ)K` and the quadratic constant match the
unrestricted four-law; the zero masses carry the coefficient `2(1+δ)`. -/
theorem PhiDres_fourlaw_le {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (μ₀ μ₁ ν₀ ν₁ : PMF X) (R : X → X → Prop)
    (hsymm : ∀ a b, R a b → R b a) (M Z : ℝ≥0∞)
    (h00 : PhiDres α μ₀ ν₀ R ≤ M) (h01 : PhiDres α μ₀ ν₁ R ≤ M)
    (h10 : PhiDres α μ₁ ν₀ R ≤ M) (h11 : PhiDres α μ₁ ν₁ R ≤ M)
    (hr00 : PhiDres α ν₀ μ₀ R ≤ M) (hr10 : PhiDres α ν₀ μ₁ R ≤ M)
    (hr01 : PhiDres α ν₁ μ₀ R ≤ M) (hr11 : PhiDres α ν₁ μ₁ R ≤ M)
    (hz00 : zMass ν₀ μ₀ R ≤ Z) (hz10 : zMass ν₀ μ₁ R ≤ Z)
    (hz01 : zMass ν₁ μ₀ R ≤ Z) (hz11 : zMass ν₁ μ₁ R ≤ Z) :
    ∑' p : X × X, prodPMF μ₀ μ₁ p
        * ((if rE ν₀ R p.1 = 0 ∨ rE ν₁ R p.1 = 0 ∨ rE ν₀ R p.2 = 0
              ∨ rE ν₁ R p.2 = 0 then 0 else 1)
          * phiE α (q (prodPMF ν₀ ν₁) (SquareRel R) p))
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
          * M ^ 2
        + ENNReal.ofReal (2 * (1 + δ)) * Z := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hcc : 0 ≤ chordConst α := chordConst_nonneg hα0
  -- degenerate bound
  by_cases hM : M = ⊤
  · have hApos : (0 : ℝ) < 2 * L + 2 * (1 + δ) * K := by nlinarith
    rw [hM]
    have htop : ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * ⊤ = ⊤ :=
      ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero, not_le, hApos])
    rw [htop, top_add, top_add]
    exact le_top
  set Fr : X → ℝ≥0∞ := fun x =>
    (if rE ν₀ R x = 0 then 0 else phiE α (q ν₀ R x))
      + (if rE ν₁ R x = 0 then 0 else phiE α (q ν₁ R x)) with hFr
  set cL : ℝ≥0∞ := ENNReal.ofReal (L / 2) with hcL
  set c₅ : ℝ≥0∞ := ENNReal.ofReal (L * chordConst α / 2 + 5) with hc₅
  -- termwise main bound on the doubly-positive set
  have hterm : ∀ p : X × X, prodPMF μ₀ μ₁ p
      * ((if rE ν₀ R p.1 = 0 ∨ rE ν₁ R p.1 = 0 ∨ rE ν₀ R p.2 = 0
            ∨ rE ν₁ R p.2 = 0 then 0 else 1)
        * phiE α (q (prodPMF ν₀ ν₁) (SquareRel R) p))
      ≤ prodPMF μ₀ μ₁ p * (cL * (Fr p.1 + Fr p.2) + c₅ * (Fr p.1 * Fr p.2)
          + cOverlap ν₀ R p.1 p.2 * (WresD α ν₀ R p.1 * WresD α ν₁ R p.2)
          + cOverlap ν₁ R p.1 p.2 * (WresD α ν₁ R p.1 * WresD α ν₀ R p.2)) := by
    rintro ⟨x₀, x₁⟩
    by_cases hreg : rE ν₀ R x₀ = 0 ∨ rE ν₁ R x₀ = 0 ∨ rE ν₀ R x₁ = 0
        ∨ rE ν₁ R x₁ = 0
    · rw [if_pos hreg, zero_mul, mul_zero]
      exact zero_le
    · rw [if_neg hreg, one_mul]
      push Not at hreg
      obtain ⟨hne00, hne01, hne10, hne11⟩ := hreg
      refine mul_le_mul_right ?_ _
      have hmain := phiE_square_main_le hα hL0 hL ν₀ ν₁ R x₀ x₁
        hne00 hne01 hne10 hne11
      simp only [hFr, WresD, if_neg hne00, if_neg hne01, if_neg hne10,
        if_neg hne11, hcL, hc₅]
      exact hmain
  -- sum the termwise bound and split into four totals
  have hsplit : (∑' p : X × X, prodPMF μ₀ μ₁ p
        * ((if rE ν₀ R p.1 = 0 ∨ rE ν₁ R p.1 = 0 ∨ rE ν₀ R p.2 = 0
              ∨ rE ν₁ R p.2 = 0 then 0 else 1)
          * phiE α (q (prodPMF ν₀ ν₁) (SquareRel R) p)))
      ≤ cL * ((∑' x, μ₀ x * Fr x) + ∑' x, μ₁ x * Fr x)
        + c₅ * ((∑' x, μ₀ x * Fr x) * ∑' x, μ₁ x * Fr x)
        + (∑' y, ν₀ y * (HresD α μ₀ ν₀ R y * HresD α μ₁ ν₁ R y))
        + (∑' y, ν₁ y * (HresD α μ₀ ν₁ R y * HresD α μ₁ ν₀ R y)) := by
    calc (∑' p : X × X, prodPMF μ₀ μ₁ p
          * ((if rE ν₀ R p.1 = 0 ∨ rE ν₁ R p.1 = 0 ∨ rE ν₀ R p.2 = 0
                ∨ rE ν₁ R p.2 = 0 then 0 else 1)
            * phiE α (q (prodPMF ν₀ ν₁) (SquareRel R) p)))
        ≤ ∑' p : X × X, prodPMF μ₀ μ₁ p
            * (cL * (Fr p.1 + Fr p.2) + c₅ * (Fr p.1 * Fr p.2)
              + cOverlap ν₀ R p.1 p.2 * (WresD α ν₀ R p.1 * WresD α ν₁ R p.2)
              + cOverlap ν₁ R p.1 p.2
                * (WresD α ν₁ R p.1 * WresD α ν₀ R p.2)) :=
          ENNReal.tsum_le_tsum hterm
      _ = cL * ((∑' x, μ₀ x * Fr x) + ∑' x, μ₁ x * Fr x)
            + c₅ * ((∑' x, μ₀ x * Fr x) * ∑' x, μ₁ x * Fr x)
            + (∑' y, ν₀ y * (HresD α μ₀ ν₀ R y * HresD α μ₁ ν₁ R y))
            + (∑' y, ν₁ y * (HresD α μ₀ ν₁ R y * HresD α μ₁ ν₀ R y)) := by
          rw [tsum_congr fun p : X × X => show prodPMF μ₀ μ₁ p
              * (cL * (Fr p.1 + Fr p.2) + c₅ * (Fr p.1 * Fr p.2)
                + cOverlap ν₀ R p.1 p.2 * (WresD α ν₀ R p.1 * WresD α ν₁ R p.2)
                + cOverlap ν₁ R p.1 p.2
                  * (WresD α ν₁ R p.1 * WresD α ν₀ R p.2))
              = cL * (prodPMF μ₀ μ₁ p * Fr p.1 + prodPMF μ₀ μ₁ p * Fr p.2)
                + c₅ * (prodPMF μ₀ μ₁ p * (Fr p.1 * Fr p.2))
                + μ₀ p.1 * μ₁ p.2
                  * (cOverlap ν₀ R p.1 p.2
                    * (WresD α ν₀ R p.1 * WresD α ν₁ R p.2))
                + μ₀ p.1 * μ₁ p.2
                  * (cOverlap ν₁ R p.1 p.2
                    * (WresD α ν₁ R p.1 * WresD α ν₀ R p.2))
              from by rw [prodPMF_apply]; ring,
            ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add,
            ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_add,
            tsum_mass_left, tsum_mass_right, tsum_mass_prod,
            fubini_swap_two_res, fubini_swap_two_res]
  -- the two row totals
  have hFrow : ∀ μ' : PMF X, (∑' x, μ' x * Fr x)
      = PhiDres α μ' ν₀ R + PhiDres α μ' ν₁ R := by
    intro μ'
    simp only [hFr]
    rw [tsum_congr fun x => show
        μ' x * ((if rE ν₀ R x = 0 then 0 else phiE α (q ν₀ R x))
            + (if rE ν₁ R x = 0 then 0 else phiE α (q ν₁ R x)))
          = μ' x * (if rE ν₀ R x = 0 then 0 else phiE α (q ν₀ R x))
            + μ' x * (if rE ν₁ R x = 0 then 0 else phiE α (q ν₁ R x))
        from by ring,
      ENNReal.tsum_add, PhiDres, PhiDres]
  have hFsum₀ : (∑' x, μ₀ x * Fr x) ≤ 2 * M := by
    rw [hFrow μ₀]
    calc PhiDres α μ₀ ν₀ R + PhiDres α μ₀ ν₁ R ≤ M + M := add_le_add h00 h01
      _ = 2 * M := (two_mul M).symm
  have hFsum₁ : (∑' x, μ₁ x * Fr x) ≤ 2 * M := by
    rw [hFrow μ₁]
    calc PhiDres α μ₁ ν₀ R + PhiDres α μ₁ ν₁ R ≤ M + M := add_le_add h10 h11
      _ = 2 * M := (two_mul M).symm
  -- the overlap totals
  have hEH : ∀ (νc ν₀' ν₁' : PMF X), PhiDres α νc μ₀ R ≤ M → PhiDres α νc μ₁ R ≤ M →
      zMass νc μ₀ R ≤ Z → zMass νc μ₁ R ≤ Z →
      PhiDres α μ₀ ν₀' R ≤ M → PhiDres α μ₁ ν₁' R ≤ M →
      2 * ∑' y, νc y * (HresD α μ₀ ν₀' R y * HresD α μ₁ ν₁' R y)
        ≤ ENNReal.ofReal (2 * (1 + δ) * K) * M
          + ENNReal.ofReal (2 * (1 + δ)) * Z
          + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2 := by
    intro νc ν₀' ν₁' hv0 hv1 hzv0 hzv1 hk0 hk1
    have hsq : 2 * ∑' y, νc y * (HresD α μ₀ ν₀' R y * HresD α μ₁ ν₁' R y)
        ≤ (∑' y, νc y * HresD α μ₀ ν₀' R y ^ 2)
          + ∑' y, νc y * HresD α μ₁ ν₁' R y ^ 2 := by
      rw [ENNReal.tsum_mul_left.symm, ← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun y => ?_
      calc 2 * (νc y * (HresD α μ₀ ν₀' R y * HresD α μ₁ ν₁' R y))
          = νc y * (2 * (HresD α μ₀ ν₀' R y * HresD α μ₁ ν₁' R y)) := by ring
        _ ≤ νc y * (HresD α μ₀ ν₀' R y ^ 2 + HresD α μ₁ ν₁' R y ^ 2) :=
            mul_le_mul_right (ennreal_two_mul_le_add_sq _ _) _
        _ = νc y * HresD α μ₀ ν₀' R y ^ 2 + νc y * HresD α μ₁ ν₁' R y ^ 2 := by
            ring
    have hH₀ := EHsqD_res_le hα hδ hK0 hK νc μ₀ ν₀' R hsymm
    have hH₁ := EHsqD_res_le hα hδ hK0 hK νc μ₁ ν₁' R hsymm
    calc 2 * ∑' y, νc y * (HresD α μ₀ ν₀' R y * HresD α μ₁ ν₁' R y)
        ≤ (ENNReal.ofReal ((1 + δ) * K) * PhiDres α νc μ₀ R
            + ENNReal.ofReal (1 + δ) * zMass νc μ₀ R
            + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * PhiDres α μ₀ ν₀' R ^ 2)
          + (ENNReal.ofReal ((1 + δ) * K) * PhiDres α νc μ₁ R
            + ENNReal.ofReal (1 + δ) * zMass νc μ₁ R
            + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * PhiDres α μ₁ ν₁' R ^ 2) :=
          le_trans hsq (add_le_add hH₀ hH₁)
      _ ≤ (ENNReal.ofReal ((1 + δ) * K) * M + ENNReal.ofReal (1 + δ) * Z
            + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * M ^ 2)
          + (ENNReal.ofReal ((1 + δ) * K) * M + ENNReal.ofReal (1 + δ) * Z
            + ENNReal.ofReal ((1 + δ⁻¹) * α ^ 2) * M ^ 2) :=
          add_le_add
            (add_le_add (add_le_add (mul_le_mul_right hv0 _)
              (mul_le_mul_right hzv0 _))
              (mul_le_mul_right (pow_le_pow_left' hk0 2) _))
            (add_le_add (add_le_add (mul_le_mul_right hv1 _)
              (mul_le_mul_right hzv1 _))
              (mul_le_mul_right (pow_le_pow_left' hk1 2) _))
      _ = ENNReal.ofReal (2 * (1 + δ) * K) * M
          + ENNReal.ofReal (2 * (1 + δ)) * Z
          + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2 := by
          rw [show (2:ℝ) * (1 + δ) * K = 2 * ((1 + δ) * K) from by ring,
            show (2:ℝ) * (1 + δ⁻¹) * α ^ 2 = 2 * ((1 + δ⁻¹) * α ^ 2)
              from by ring,
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            ENNReal.ofReal_ofNat]
          ring
  have hOVL : (∑' y, ν₀ y * (HresD α μ₀ ν₀ R y * HresD α μ₁ ν₁ R y))
        + (∑' y, ν₁ y * (HresD α μ₀ ν₁ R y * HresD α μ₁ ν₀ R y))
      ≤ ENNReal.ofReal (2 * (1 + δ) * K) * M
        + ENNReal.ofReal (2 * (1 + δ)) * Z
        + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2 := by
    have h2 : 2 * ((∑' y, ν₀ y * (HresD α μ₀ ν₀ R y * HresD α μ₁ ν₁ R y))
          + ∑' y, ν₁ y * (HresD α μ₀ ν₁ R y * HresD α μ₁ ν₀ R y))
        ≤ 2 * (ENNReal.ofReal (2 * (1 + δ) * K) * M
          + ENNReal.ofReal (2 * (1 + δ)) * Z
          + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2) := by
      calc 2 * ((∑' y, ν₀ y * (HresD α μ₀ ν₀ R y * HresD α μ₁ ν₁ R y))
            + ∑' y, ν₁ y * (HresD α μ₀ ν₁ R y * HresD α μ₁ ν₀ R y))
          = 2 * (∑' y, ν₀ y * (HresD α μ₀ ν₀ R y * HresD α μ₁ ν₁ R y))
            + 2 * ∑' y, ν₁ y * (HresD α μ₀ ν₁ R y * HresD α μ₁ ν₀ R y) := by
            ring
        _ ≤ (ENNReal.ofReal (2 * (1 + δ) * K) * M
              + ENNReal.ofReal (2 * (1 + δ)) * Z
              + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2)
            + (ENNReal.ofReal (2 * (1 + δ) * K) * M
              + ENNReal.ofReal (2 * (1 + δ)) * Z
              + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2) :=
            add_le_add (hEH ν₀ ν₀ ν₁ hr00 hr10 hz00 hz10 h00 h11)
              (hEH ν₁ ν₁ ν₀ hr01 hr11 hz01 hz11 h01 h10)
        _ = 2 * (ENNReal.ofReal (2 * (1 + δ) * K) * M
            + ENNReal.ofReal (2 * (1 + δ)) * Z
            + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2) := by ring
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2
  -- collect the constants
  calc (∑' p : X × X, prodPMF μ₀ μ₁ p
        * ((if rE ν₀ R p.1 = 0 ∨ rE ν₁ R p.1 = 0 ∨ rE ν₀ R p.2 = 0
              ∨ rE ν₁ R p.2 = 0 then 0 else 1)
          * phiE α (q (prodPMF ν₀ ν₁) (SquareRel R) p)))
      ≤ cL * (2 * M + 2 * M) + c₅ * (2 * M * (2 * M))
        + (ENNReal.ofReal (2 * (1 + δ) * K) * M
          + ENNReal.ofReal (2 * (1 + δ)) * Z
          + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2) := by
        refine le_trans hsplit ?_
        calc cL * ((∑' x, μ₀ x * Fr x) + ∑' x, μ₁ x * Fr x)
              + c₅ * ((∑' x, μ₀ x * Fr x) * ∑' x, μ₁ x * Fr x)
              + (∑' y, ν₀ y * (HresD α μ₀ ν₀ R y * HresD α μ₁ ν₁ R y))
              + (∑' y, ν₁ y * (HresD α μ₀ ν₁ R y * HresD α μ₁ ν₀ R y))
            = (cL * ((∑' x, μ₀ x * Fr x) + ∑' x, μ₁ x * Fr x)
                + c₅ * ((∑' x, μ₀ x * Fr x) * ∑' x, μ₁ x * Fr x))
              + ((∑' y, ν₀ y * (HresD α μ₀ ν₀ R y * HresD α μ₁ ν₁ R y))
                + ∑' y, ν₁ y * (HresD α μ₀ ν₁ R y * HresD α μ₁ ν₀ R y)) := by
              ring
          _ ≤ (cL * (2 * M + 2 * M) + c₅ * (2 * M * (2 * M)))
              + (ENNReal.ofReal (2 * (1 + δ) * K) * M
                + ENNReal.ofReal (2 * (1 + δ)) * Z
                + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2) :=
              add_le_add (add_le_add
                (mul_le_mul_right (add_le_add hFsum₀ hFsum₁) cL)
                (mul_le_mul_right (mul_le_mul' hFsum₀ hFsum₁) c₅)) hOVL
          _ = cL * (2 * M + 2 * M) + c₅ * (2 * M * (2 * M))
              + (ENNReal.ofReal (2 * (1 + δ) * K) * M
                + ENNReal.ofReal (2 * (1 + δ)) * Z
                + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2) := by ring
    _ ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
          * M ^ 2
        + ENNReal.ofReal (2 * (1 + δ)) * Z := by
      have e1 : cL * (2 * M + 2 * M) = ENNReal.ofReal (2 * L) * M := by
        rw [hcL, show (2:ℝ≥0∞) * M + 2 * M = 4 * M from by ring,
          show ENNReal.ofReal (L / 2) * (4 * M)
            = (ENNReal.ofReal (L / 2) * 4) * M from by ring,
          show (4:ℝ≥0∞) = ENNReal.ofReal (4:ℝ) from by rw [ENNReal.ofReal_ofNat],
          ← ENNReal.ofReal_mul (by linarith),
          show (L / 2 * 4 : ℝ) = 2 * L from by ring]
      have e2 : c₅ * (2 * M * (2 * M))
          = ENNReal.ofReal (2 * L * chordConst α + 20) * M ^ 2 := by
        rw [hc₅, show (2:ℝ≥0∞) * M * (2 * M) = 4 * M ^ 2 from by ring,
          show ENNReal.ofReal (L * chordConst α / 2 + 5) * (4 * M ^ 2)
            = (ENNReal.ofReal (L * chordConst α / 2 + 5) * 4) * M ^ 2
            from by ring,
          show (4:ℝ≥0∞) = ENNReal.ofReal (4:ℝ) from by rw [ENNReal.ofReal_ofNat],
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
      rw [e1, e2]
      have hsplitA : ENNReal.ofReal (2 * L + 2 * (1 + δ) * K)
          = ENNReal.ofReal (2 * L) + ENNReal.ofReal (2 * (1 + δ) * K) := by
        rw [← ENNReal.ofReal_add (by linarith) (by positivity)]
      have hsplitC : ENNReal.ofReal
            (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
          = ENNReal.ofReal (2 * L * chordConst α + 20)
            + ENNReal.ofReal (2 * (1 + δ⁻¹) * α ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      rw [hsplitA, hsplitC]
      exact le_of_eq (by ring)

/-! ### The abstract restricted inverse moment (`thm:inverse-moment`) -/

/-- The tangent bound for an abstract degree `t ∈ (0,1]` in the safe
form: `t^{-α} ≤ 1 + α·φ_α(1-t)`. -/
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

/-- **The restricted inverse moment** (`thm:inverse-moment`), for an
abstract degree function `r : X → [0,1]`:
`𝔼_ρ[Wres_r] ≤ 1 + α·𝔼_ρ[𝟙_{r>0} φ_α(1-r)]`. -/
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

/-- The `H`-restricted inverse moment (`thm:inverse-moment`, restricted
form): restricting both sums to `H` replaces the constant `1` by
`ρ(H)`. -/
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

/-! ### The one-cell ledger row -/

section CellRow

/- The Hall layer (`Process/Hall.lean`) lives at universe zero, pinned by
`ZeroInterface`; the cell row is used at the process laws, which are
also at universe zero. -/
variable {X : Type}

/-- On a positive edge the inverse degree is the `W`-weight. -/
lemma rE_rpow_neg_eq_WresD {α : ℝ} (ρt : PMF X) (R : X → X → Prop) (x : X)
    (h : rE ρt R x ≠ 0) : (rE ρt R x) ^ (-α) = WresD α ρt R x := by
  rw [WresD, if_neg h, WnnD]
  have hq : q ρt R x < 1 := q_lt_one_of_rE_ne_zero h
  have h1 : rE ρt R x = ENNReal.ofReal (1 - q ρt R x) := by
    rw [← toReal_rE_eq ρt R x, ENNReal.ofReal_toReal rE_ne_top]
  rw [h1, ← ENNReal.ofReal_rpow_of_pos (by linarith)]

/-- The restricted inverse moment: `𝔼_{ρ_s}[Wres_{ρ_t}] ≤ 1 + α·Φres(ρ_s → ρ_t)`.
The good-degree instance of `tsum_wres_le` at `r = rE ρt R`. -/
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

/-- **Integrated screened inverse moment.**  A zero-list restriction is
kept inside the source integral before the inverse moment is estimated.
Consequently the constant term is the unit-normalized screen, while the
potential term is bounded by the ordinary restricted potential.  In
particular this estimate introduces no inverse mixture atoms. -/
lemma screenE_WresD_le {α : ℝ} (hα : 1 ≤ α) (ρs ρt : PMF X)
    (R : X → X → Prop) (zs : List (PMF X)) :
    screenE ρs R zs (WresD α ρt R)
      ≤ screenE ρs R zs (fun _ => 1)
        + ENNReal.ofReal α * PhiDres α ρs ρt R := by
  rw [screenE, screenE, PhiDres]
  calc
    (∑' x, ρs x * screenInd R zs x * WresD α ρt R x)
        ≤ ∑' x, (ρs x * screenInd R zs x * 1
          + ENNReal.ofReal α *
              (ρs x * (if rE ρt R x = 0 then 0
                else phiE α (q ρt R x)))) := by
            refine ENNReal.tsum_le_tsum fun x => ?_
            by_cases ht : rE ρt R x = 0
            · simp [WresD, ht]
            · have hind : screenInd R zs x ≤ 1 := by
                rw [screenInd]
                split_ifs <;> simp
              have hW : WresD α ρt R x
                  ≤ 1 + ENNReal.ofReal α * phiE α (q ρt R x) := by
                rw [← rE_rpow_neg_eq_WresD ρt R x ht]
                convert rpow_neg_le_one_add_phiE hα ht rE_le_one using 1
                rw [toReal_rE_eq]
                ring_nf
              calc
                ρs x * screenInd R zs x * WresD α ρt R x
                    ≤ ρs x * screenInd R zs x
                        * (1 + ENNReal.ofReal α * phiE α (q ρt R x)) :=
                      mul_le_mul_right hW _
                _ = ρs x * screenInd R zs x * 1
                      + ENNReal.ofReal α
                        * (ρs x * screenInd R zs x * phiE α (q ρt R x)) := by
                      ring
                _ ≤ ρs x * screenInd R zs x * 1
                      + ENNReal.ofReal α
                        * (ρs x * (if rE ρt R x = 0 then 0
                          else phiE α (q ρt R x))) := by
                      rw [if_neg ht]
                      have hcore : ρs x * screenInd R zs x
                            * phiE α (q ρt R x)
                          ≤ ρs x * phiE α (q ρt R x) := by
                        calc
                          ρs x * screenInd R zs x * phiE α (q ρt R x)
                              ≤ ρs x * 1 * phiE α (q ρt R x) :=
                                mul_le_mul_left
                                  (mul_le_mul_right hind (ρs x)) _
                          _ = ρs x * phiE α (q ρt R x) := by rw [mul_one]
                      exact add_le_add le_rfl (mul_le_mul_right hcore _)
    _ = (∑' x, ρs x * screenInd R zs x * 1)
          + ENNReal.ofReal α
              * ∑' x, ρs x * (if rE ρt R x = 0 then 0
                else phiE α (q ρt R x)) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]

/-- Singleton screens in indicator form. -/
lemma screenE_singleton (ρs : PMF X) (R : X → X → Prop) (ρc : PMF X)
    (g : X → ℝ≥0∞) :
    screenE ρs R [ρc] g
      = ∑' x, ρs x * ((if rE ρc R x = 0 then 1 else 0) * g x) := by
  rw [screenE]
  refine tsum_congr fun x => ?_
  have hind : screenInd R [ρc] x = if rE ρc R x = 0 then 1 else 0 := by
    simp [screenInd]
  rw [hind, mul_assoc]

/-- **The one-cell ledger row** (`sec:rows`, `thm:one-cell`): the restricted square potential of a product cell is
bounded by the restricted four-law output plus four resolved charges,
each a singleton screen times a restricted inverse moment.  Zero rows and
zero columns of the cell lie outside the restriction and contribute nothing
here; their mass is counted by the screen rows. -/
theorem PhiDres_square_le {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (ρa ρb ρc ρd : PMF X) (R : X → X → Prop)
    (hsymm : ∀ a b, R a b → R b a) (M Z : ℝ≥0∞)
    (hac : PhiDres α ρa ρc R ≤ M) (had : PhiDres α ρa ρd R ≤ M)
    (hbc : PhiDres α ρb ρc R ≤ M) (hbd : PhiDres α ρb ρd R ≤ M)
    (hca : PhiDres α ρc ρa R ≤ M) (hcb : PhiDres α ρc ρb R ≤ M)
    (hda : PhiDres α ρd ρa R ≤ M) (hdb : PhiDres α ρd ρb R ≤ M)
    (hzca : zMass ρc ρa R ≤ Z) (hzcb : zMass ρc ρb R ≤ Z)
    (hzda : zMass ρd ρa R ≤ Z) (hzdb : zMass ρd ρb R ≤ Z) :
    PhiDres α (prodPMF ρa ρb) (prodPMF ρc ρd) (SquareRel R)
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
          * M ^ 2
        + ENNReal.ofReal (2 * (1 + δ)) * Z
        + (screenE ρa R [ρc] (WresD α ρd R)
            + screenE ρa R [ρd] (WresD α ρc R)
            + screenE ρb R [ρc] (WresD α ρd R)
            + screenE ρb R [ρd] (WresD α ρc R))
          * (1 + ENNReal.ofReal α * M) := by
  have hαpos : (0 : ℝ) < α := lt_of_lt_of_le one_pos hα
  -- pointwise five-way split
  have hpt : ∀ p : X × X, prodPMF ρa ρb p
      * (if rE (prodPMF ρc ρd) (SquareRel R) p = 0 then 0
          else phiE α (q (prodPMF ρc ρd) (SquareRel R) p))
      ≤ prodPMF ρa ρb p
          * ((if rE ρc R p.1 = 0 ∨ rE ρd R p.1 = 0 ∨ rE ρc R p.2 = 0
                ∨ rE ρd R p.2 = 0 then 0 else 1)
            * phiE α (q (prodPMF ρc ρd) (SquareRel R) p))
        + prodPMF ρa ρb p * ((if rE ρc R p.1 = 0 then 1 else 0)
            * (WresD α ρd R p.1 * WresD α ρc R p.2))
        + prodPMF ρa ρb p * ((if rE ρd R p.1 = 0 then 1 else 0)
            * (WresD α ρc R p.1 * WresD α ρd R p.2))
        + prodPMF ρa ρb p * ((if rE ρc R p.2 = 0 then 1 else 0)
            * (WresD α ρc R p.1 * WresD α ρd R p.2))
        + prodPMF ρa ρb p * ((if rE ρd R p.2 = 0 then 1 else 0)
            * (WresD α ρd R p.1 * WresD α ρc R p.2)) := by
    rintro ⟨x₀, x₁⟩
    by_cases hsq : rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) = 0
    · rw [if_pos hsq, mul_zero]
      exact zero_le
    · rw [if_neg hsq]
      by_cases hd4 : rE ρc R x₀ = 0 ∨ rE ρd R x₀ = 0 ∨ rE ρc R x₁ = 0
          ∨ rE ρd R x₁ = 0
      · rcases hd4 with h | h | h | h
        · -- straight blocked, crossed survives
          have hcr : rE ρc R x₁ * rE ρd R x₀ ≠ 0 := fun hc =>
            hsq ((rE_square_eq_zero_iff ρc ρd R x₀ x₁).mpr
              ⟨by rw [h, zero_mul], hc⟩)
          obtain ⟨hc1, hd0⟩ := mul_ne_zero_iff.mp hcr
          have hb := phiE_square_resolved_le_crossed hαpos ρc ρd R x₀ x₁
            hc1 hd0
          rw [rE_rpow_neg_eq_WresD ρc R x₁ hc1,
            rE_rpow_neg_eq_WresD ρd R x₀ hd0, mul_comm] at hb
          refine le_trans (le_trans (mul_le_mul_right hb _) ?_)
            (le_trans le_add_self (le_trans le_self_add
              (le_trans le_self_add le_self_add)))
          rw [if_pos h, one_mul]
        · -- crossed blocked, straight survives
          have hst : rE ρc R x₀ * rE ρd R x₁ ≠ 0 := fun hc =>
            hsq ((rE_square_eq_zero_iff ρc ρd R x₀ x₁).mpr
              ⟨hc, by rw [h, mul_zero]⟩)
          obtain ⟨hc0, hd1⟩ := mul_ne_zero_iff.mp hst
          have hb := phiE_square_resolved_le hαpos ρc ρd R x₀ x₁ hc0 hd1
          rw [rE_rpow_neg_eq_WresD ρc R x₀ hc0,
            rE_rpow_neg_eq_WresD ρd R x₁ hd1] at hb
          refine le_trans (le_trans (mul_le_mul_right hb _) ?_)
            (le_trans (le_add_self)
              (le_trans le_self_add le_self_add))
          rw [if_pos h, one_mul]
        · -- crossed blocked, straight survives
          have hst : rE ρc R x₀ * rE ρd R x₁ ≠ 0 := fun hc =>
            hsq ((rE_square_eq_zero_iff ρc ρd R x₀ x₁).mpr
              ⟨hc, by rw [h, zero_mul]⟩)
          obtain ⟨hc0, hd1⟩ := mul_ne_zero_iff.mp hst
          have hb := phiE_square_resolved_le hαpos ρc ρd R x₀ x₁ hc0 hd1
          rw [rE_rpow_neg_eq_WresD ρc R x₀ hc0,
            rE_rpow_neg_eq_WresD ρd R x₁ hd1] at hb
          refine le_trans (le_trans (mul_le_mul_right hb _) ?_)
            (le_trans le_add_self le_self_add)
          rw [if_pos h, one_mul]
        · -- straight blocked, crossed survives
          have hcr : rE ρc R x₁ * rE ρd R x₀ ≠ 0 := fun hc =>
            hsq ((rE_square_eq_zero_iff ρc ρd R x₀ x₁).mpr
              ⟨by rw [h, mul_zero], hc⟩)
          obtain ⟨hc1, hd0⟩ := mul_ne_zero_iff.mp hcr
          have hb := phiE_square_resolved_le_crossed hαpos ρc ρd R x₀ x₁
            hc1 hd0
          rw [rE_rpow_neg_eq_WresD ρc R x₁ hc1,
            rE_rpow_neg_eq_WresD ρd R x₀ hd0, mul_comm] at hb
          refine le_trans (le_trans (mul_le_mul_right hb _) ?_) le_add_self
          rw [if_pos h, one_mul]
      · refine le_trans (le_of_eq ?_)
          (le_trans le_self_add (le_trans le_self_add
            (le_trans le_self_add le_self_add)))
        rw [if_neg hd4, one_mul]
  -- sum and split into the five totals
  have hT1 : ∑' p : X × X, prodPMF ρa ρb p
        * ((if rE ρc R p.1 = 0 then 1 else 0)
          * (WresD α ρd R p.1 * WresD α ρc R p.2))
      ≤ screenE ρa R [ρc] (WresD α ρd R) * (1 + ENNReal.ofReal α * M) := by
    rw [tsum_congr fun p : X × X => show prodPMF ρa ρb p
        * ((if rE ρc R p.1 = 0 then 1 else 0)
          * (WresD α ρd R p.1 * WresD α ρc R p.2))
        = (ρa p.1 * ((if rE ρc R p.1 = 0 then 1 else 0) * WresD α ρd R p.1))
          * (ρb p.2 * WresD α ρc R p.2)
        from by rw [prodPMF_apply]; ring,
      tsum_prod_split
        (fun x => ρa x * ((if rE ρc R x = 0 then 1 else 0) * WresD α ρd R x))
        (fun x => ρb x * WresD α ρc R x), ← screenE_singleton]
    exact mul_le_mul' le_rfl (le_trans (tsum_WresD_le hα ρb ρc R)
      (add_le_add le_rfl (mul_le_mul_right hbc _)))
  have hT2 : ∑' p : X × X, prodPMF ρa ρb p
        * ((if rE ρd R p.1 = 0 then 1 else 0)
          * (WresD α ρc R p.1 * WresD α ρd R p.2))
      ≤ screenE ρa R [ρd] (WresD α ρc R) * (1 + ENNReal.ofReal α * M) := by
    rw [tsum_congr fun p : X × X => show prodPMF ρa ρb p
        * ((if rE ρd R p.1 = 0 then 1 else 0)
          * (WresD α ρc R p.1 * WresD α ρd R p.2))
        = (ρa p.1 * ((if rE ρd R p.1 = 0 then 1 else 0) * WresD α ρc R p.1))
          * (ρb p.2 * WresD α ρd R p.2)
        from by rw [prodPMF_apply]; ring,
      tsum_prod_split
        (fun x => ρa x * ((if rE ρd R x = 0 then 1 else 0) * WresD α ρc R x))
        (fun x => ρb x * WresD α ρd R x), ← screenE_singleton]
    exact mul_le_mul' le_rfl (le_trans (tsum_WresD_le hα ρb ρd R)
      (add_le_add le_rfl (mul_le_mul_right hbd _)))
  have hT3 : ∑' p : X × X, prodPMF ρa ρb p
        * ((if rE ρc R p.2 = 0 then 1 else 0)
          * (WresD α ρc R p.1 * WresD α ρd R p.2))
      ≤ screenE ρb R [ρc] (WresD α ρd R) * (1 + ENNReal.ofReal α * M) := by
    rw [tsum_congr fun p : X × X => show prodPMF ρa ρb p
        * ((if rE ρc R p.2 = 0 then 1 else 0)
          * (WresD α ρc R p.1 * WresD α ρd R p.2))
        = (ρa p.1 * WresD α ρc R p.1)
          * (ρb p.2 * ((if rE ρc R p.2 = 0 then 1 else 0) * WresD α ρd R p.2))
        from by rw [prodPMF_apply]; ring,
      tsum_prod_split
        (fun x => ρa x * WresD α ρc R x)
        (fun x => ρb x * ((if rE ρc R x = 0 then 1 else 0) * WresD α ρd R x)),
      ← screenE_singleton, mul_comm]
    exact mul_le_mul' le_rfl (le_trans (tsum_WresD_le hα ρa ρc R)
      (add_le_add le_rfl (mul_le_mul_right hac _)))
  have hT4 : ∑' p : X × X, prodPMF ρa ρb p
        * ((if rE ρd R p.2 = 0 then 1 else 0)
          * (WresD α ρd R p.1 * WresD α ρc R p.2))
      ≤ screenE ρb R [ρd] (WresD α ρc R) * (1 + ENNReal.ofReal α * M) := by
    rw [tsum_congr fun p : X × X => show prodPMF ρa ρb p
        * ((if rE ρd R p.2 = 0 then 1 else 0)
          * (WresD α ρd R p.1 * WresD α ρc R p.2))
        = (ρa p.1 * WresD α ρd R p.1)
          * (ρb p.2 * ((if rE ρd R p.2 = 0 then 1 else 0) * WresD α ρc R p.2))
        from by rw [prodPMF_apply]; ring,
      tsum_prod_split
        (fun x => ρa x * WresD α ρd R x)
        (fun x => ρb x * ((if rE ρd R x = 0 then 1 else 0) * WresD α ρc R x)),
      ← screenE_singleton, mul_comm]
    exact mul_le_mul' le_rfl (le_trans (tsum_WresD_le hα ρa ρd R)
      (add_le_add le_rfl (mul_le_mul_right had _)))
  have hFL := PhiDres_fourlaw_le hα hδ hL0 hL hK0 hK ρa ρb ρc ρd R hsymm M Z
    hac had hbc hbd hca hcb hda hdb hzca hzcb hzda hzdb
  calc PhiDres α (prodPMF ρa ρb) (prodPMF ρc ρd) (SquareRel R)
      ≤ (∑' p : X × X, prodPMF ρa ρb p
          * ((if rE ρc R p.1 = 0 ∨ rE ρd R p.1 = 0 ∨ rE ρc R p.2 = 0
                ∨ rE ρd R p.2 = 0 then 0 else 1)
            * phiE α (q (prodPMF ρc ρd) (SquareRel R) p)))
        + (∑' p : X × X, prodPMF ρa ρb p
            * ((if rE ρc R p.1 = 0 then 1 else 0)
              * (WresD α ρd R p.1 * WresD α ρc R p.2)))
        + (∑' p : X × X, prodPMF ρa ρb p
            * ((if rE ρd R p.1 = 0 then 1 else 0)
              * (WresD α ρc R p.1 * WresD α ρd R p.2)))
        + (∑' p : X × X, prodPMF ρa ρb p
            * ((if rE ρc R p.2 = 0 then 1 else 0)
              * (WresD α ρc R p.1 * WresD α ρd R p.2)))
        + (∑' p : X × X, prodPMF ρa ρb p
            * ((if rE ρd R p.2 = 0 then 1 else 0)
              * (WresD α ρd R p.1 * WresD α ρc R p.2))) := by
        rw [PhiDres, ← ENNReal.tsum_add, ← ENNReal.tsum_add,
          ← ENNReal.tsum_add, ← ENNReal.tsum_add]
        exact ENNReal.tsum_le_tsum hpt
    _ ≤ (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
          + ENNReal.ofReal
              (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
          + ENNReal.ofReal (2 * (1 + δ)) * Z)
        + screenE ρa R [ρc] (WresD α ρd R) * (1 + ENNReal.ofReal α * M)
        + screenE ρa R [ρd] (WresD α ρc R) * (1 + ENNReal.ofReal α * M)
        + screenE ρb R [ρc] (WresD α ρd R) * (1 + ENNReal.ofReal α * M)
        + screenE ρb R [ρd] (WresD α ρc R) * (1 + ENNReal.ofReal α * M) :=
        add_le_add (add_le_add (add_le_add (add_le_add hFL hT1) hT2) hT3) hT4
    _ = ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
        + ENNReal.ofReal
            (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2) * M ^ 2
        + ENNReal.ofReal (2 * (1 + δ)) * Z
        + (screenE ρa R [ρc] (WresD α ρd R)
            + screenE ρa R [ρd] (WresD α ρc R)
            + screenE ρb R [ρc] (WresD α ρd R)
            + screenE ρb R [ρd] (WresD α ρc R))
          * (1 + ENNReal.ofReal α * M) := by ring

/-- Two-element screens in indicator form. -/
lemma screenE_pair (ρs : PMF X) (R : X → X → Prop) (ρc ρd : PMF X)
    (g : X → ℝ≥0∞) :
    screenE ρs R [ρc, ρd] g
      = ∑' x, ρs x
          * ((if rE ρc R x = 0 ∧ rE ρd R x = 0 then 1 else 0) * g x) := by
  rw [screenE]
  refine tsum_congr fun x => ?_
  have hind : screenInd R [ρc, ρd] x
      = if rE ρc R x = 0 ∧ rE ρd R x = 0 then 1 else 0 := by
    simp [screenInd]
  rw [hind, mul_assoc]

/-- **The survivor split of an alternative tilt**: the inverse square
degree of a product alternative is dominated by the sum of the two
pairings' factorized tilts; the dead pairing contributes a vanishing
factor. -/
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

/-- **Generic Hall factorization of a dead-target screen**: for any
per-coordinate tilts, the tilted mass of a dead product target splits
into a two-list screen times a tilted moment (zero rows) plus products
of singleton screens (zero columns). -/
lemma deadScreen_factorize (ρa ρb ρc ρd : PMF X) (R : X → X → Prop)
    (G₀ G₁ : X → ℝ≥0∞) :
    ∑' xp : X × X, prodPMF ρa ρb xp
        * ((if rE (prodPMF ρc ρd) (SquareRel R) xp = 0 then 1 else 0)
          * (G₀ xp.1 * G₁ xp.2))
      ≤ screenE ρa R [ρc, ρd] G₀ * (∑' x, ρb x * G₁ x)
        + (∑' x, ρa x * G₀ x) * screenE ρb R [ρc, ρd] G₁
        + screenE ρa R [ρc] G₀ * screenE ρb R [ρc] G₁
        + screenE ρa R [ρd] G₀ * screenE ρb R [ρd] G₁ := by
  have hpt : ∀ xp : X × X, prodPMF ρa ρb xp
      * ((if rE (prodPMF ρc ρd) (SquareRel R) xp = 0 then 1 else 0)
        * (G₀ xp.1 * G₁ xp.2))
      ≤ prodPMF ρa ρb xp
          * (((if rE ρc R xp.1 = 0 ∧ rE ρd R xp.1 = 0 then 1 else 0)
              * G₀ xp.1) * G₁ xp.2)
        + prodPMF ρa ρb xp
          * (G₀ xp.1 * ((if rE ρc R xp.2 = 0 ∧ rE ρd R xp.2 = 0
              then 1 else 0) * G₁ xp.2))
        + prodPMF ρa ρb xp
          * (((if rE ρc R xp.1 = 0 then 1 else 0) * G₀ xp.1)
            * ((if rE ρc R xp.2 = 0 then 1 else 0) * G₁ xp.2))
        + prodPMF ρa ρb xp
          * (((if rE ρd R xp.1 = 0 then 1 else 0) * G₀ xp.1)
            * ((if rE ρd R xp.2 = 0 then 1 else 0) * G₁ xp.2)) := by
    rintro ⟨x₀, x₁⟩
    by_cases hdead : rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) = 0
    · rw [if_pos hdead, one_mul]
      rcases (rE_square_eq_zero_iff_hall ρc ρd R x₀ x₁).mp hdead with
        (hrow | hrow) | (hcol | hcol)
      · refine le_trans (le_of_eq ?_)
          (le_trans le_self_add (le_trans le_self_add le_self_add))
        rw [if_pos hrow, one_mul]
      · refine le_trans (le_of_eq ?_)
          (le_trans le_add_self (le_trans le_self_add le_self_add))
        rw [if_pos hrow, one_mul]
      · refine le_trans (le_of_eq ?_) (le_trans le_add_self le_self_add)
        rw [if_pos hcol.1, if_pos hcol.2, one_mul, one_mul]
      · refine le_trans (le_of_eq ?_) le_add_self
        rw [if_pos hcol.1, if_pos hcol.2, one_mul, one_mul]
    · rw [if_neg hdead, zero_mul, mul_zero]
      exact zero_le
  calc ∑' xp : X × X, prodPMF ρa ρb xp
        * ((if rE (prodPMF ρc ρd) (SquareRel R) xp = 0 then 1 else 0)
          * (G₀ xp.1 * G₁ xp.2))
      ≤ (∑' xp : X × X, prodPMF ρa ρb xp
          * (((if rE ρc R xp.1 = 0 ∧ rE ρd R xp.1 = 0 then 1 else 0)
              * G₀ xp.1) * G₁ xp.2))
        + (∑' xp : X × X, prodPMF ρa ρb xp
          * (G₀ xp.1 * ((if rE ρc R xp.2 = 0 ∧ rE ρd R xp.2 = 0
              then 1 else 0) * G₁ xp.2)))
        + (∑' xp : X × X, prodPMF ρa ρb xp
          * (((if rE ρc R xp.1 = 0 then 1 else 0) * G₀ xp.1)
            * ((if rE ρc R xp.2 = 0 then 1 else 0) * G₁ xp.2)))
        + (∑' xp : X × X, prodPMF ρa ρb xp
          * (((if rE ρd R xp.1 = 0 then 1 else 0) * G₀ xp.1)
            * ((if rE ρd R xp.2 = 0 then 1 else 0) * G₁ xp.2))) := by
        rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
        exact ENNReal.tsum_le_tsum hpt
    _ = screenE ρa R [ρc, ρd] G₀ * (∑' x, ρb x * G₁ x)
        + (∑' x, ρa x * G₀ x) * screenE ρb R [ρc, ρd] G₁
        + screenE ρa R [ρc] G₀ * screenE ρb R [ρc] G₁
        + screenE ρa R [ρd] G₀ * screenE ρb R [ρd] G₁ := by
        have e0 : (∑' xp : X × X, prodPMF ρa ρb xp
            * (((if rE ρc R xp.1 = 0 ∧ rE ρd R xp.1 = 0 then 1 else 0)
                * G₀ xp.1) * G₁ xp.2))
            = screenE ρa R [ρc, ρd] G₀ * (∑' x, ρb x * G₁ x) := by
          rw [tsum_congr fun xp : X × X => show prodPMF ρa ρb xp
              * (((if rE ρc R xp.1 = 0 ∧ rE ρd R xp.1 = 0 then 1 else 0)
                  * G₀ xp.1) * G₁ xp.2)
              = (ρa xp.1 * ((if rE ρc R xp.1 = 0 ∧ rE ρd R xp.1 = 0
                    then 1 else 0) * G₀ xp.1)) * (ρb xp.2 * G₁ xp.2)
              from by rw [prodPMF_apply]; ring,
            tsum_prod_split
              (fun x => ρa x * ((if rE ρc R x = 0 ∧ rE ρd R x = 0
                then 1 else 0) * G₀ x))
              (fun x => ρb x * G₁ x), ← screenE_pair]
        have e1 : (∑' xp : X × X, prodPMF ρa ρb xp
            * (G₀ xp.1 * ((if rE ρc R xp.2 = 0 ∧ rE ρd R xp.2 = 0
                then 1 else 0) * G₁ xp.2)))
            = (∑' x, ρa x * G₀ x) * screenE ρb R [ρc, ρd] G₁ := by
          rw [tsum_congr fun xp : X × X => show prodPMF ρa ρb xp
              * (G₀ xp.1 * ((if rE ρc R xp.2 = 0 ∧ rE ρd R xp.2 = 0
                  then 1 else 0) * G₁ xp.2))
              = (ρa xp.1 * G₀ xp.1)
                * (ρb xp.2 * ((if rE ρc R xp.2 = 0 ∧ rE ρd R xp.2 = 0
                    then 1 else 0) * G₁ xp.2))
              from by rw [prodPMF_apply]; ring,
            tsum_prod_split (fun x => ρa x * G₀ x)
              (fun x => ρb x * ((if rE ρc R x = 0 ∧ rE ρd R x = 0
                then 1 else 0) * G₁ x)), ← screenE_pair]
        have e2 : (∑' xp : X × X, prodPMF ρa ρb xp
            * (((if rE ρc R xp.1 = 0 then 1 else 0) * G₀ xp.1)
              * ((if rE ρc R xp.2 = 0 then 1 else 0) * G₁ xp.2)))
            = screenE ρa R [ρc] G₀ * screenE ρb R [ρc] G₁ := by
          rw [tsum_congr fun xp : X × X => show prodPMF ρa ρb xp
              * (((if rE ρc R xp.1 = 0 then 1 else 0) * G₀ xp.1)
                * ((if rE ρc R xp.2 = 0 then 1 else 0) * G₁ xp.2))
              = (ρa xp.1 * ((if rE ρc R xp.1 = 0 then 1 else 0) * G₀ xp.1))
                * (ρb xp.2 * ((if rE ρc R xp.2 = 0 then 1 else 0)
                  * G₁ xp.2))
              from by rw [prodPMF_apply]; ring,
            tsum_prod_split
              (fun x => ρa x * ((if rE ρc R x = 0 then 1 else 0) * G₀ x))
              (fun x => ρb x * ((if rE ρc R x = 0 then 1 else 0) * G₁ x)),
            ← screenE_singleton, ← screenE_singleton]
        have e3 : (∑' xp : X × X, prodPMF ρa ρb xp
            * (((if rE ρd R xp.1 = 0 then 1 else 0) * G₀ xp.1)
              * ((if rE ρd R xp.2 = 0 then 1 else 0) * G₁ xp.2)))
            = screenE ρa R [ρd] G₀ * screenE ρb R [ρd] G₁ := by
          rw [tsum_congr fun xp : X × X => show prodPMF ρa ρb xp
              * (((if rE ρd R xp.1 = 0 then 1 else 0) * G₀ xp.1)
                * ((if rE ρd R xp.2 = 0 then 1 else 0) * G₁ xp.2))
              = (ρa xp.1 * ((if rE ρd R xp.1 = 0 then 1 else 0) * G₀ xp.1))
                * (ρb xp.2 * ((if rE ρd R xp.2 = 0 then 1 else 0)
                  * G₁ xp.2))
              from by rw [prodPMF_apply]; ring,
            tsum_prod_split
              (fun x => ρa x * ((if rE ρd R x = 0 then 1 else 0) * G₀ x))
              (fun x => ρb x * ((if rE ρd R x = 0 then 1 else 0) * G₁ x)),
            ← screenE_singleton, ← screenE_singleton]
        rw [e0, e1, e2, e3]

end CellRow

end GraphMarkovMatching
