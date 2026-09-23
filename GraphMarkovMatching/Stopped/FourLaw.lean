/-
The four-law contraction of `arbitrary_offspring_matching.tex`
(`thm:four-law-contraction`): for two source laws
`ρ₁, ρ₂` and two target laws `τ₁, τ₂` whose eight restricted directed potentials are
at most `M`, whose eight zero masses are at most `z`, and whose four weighted zero
integrals are at most `e`,

    P(ρ₁ × ρ₂, τ₁ × τ₂; R^□) ≤ a M + b M² + (γ + 4αM) z + 4 (1 + αM) e

with `a = 2 (L + K)`, `b = C_α(u)` and `γ = 2 + 2β`.  The proof integrates over the
doubly-positive set with the cancellation of the mean bad degrees between the source-row
terms and the target-overlap terms (`eq:four-law-rows`, `eq:four-law-overlaps`), and
handles the source pairs with a zero child degree by the resolved normalisation.

The scalar parameters `L`, `K`, `L0` enter as hypotheses, so that the exact maxima
`Lfun`, `Kfun` and rational surrogates are both admissible.

Organisation of the proof:

* `row_real`, `row_pt_gen`: the pointwise row estimate with the `s ≤ u` / `s > u`
  split (`eq:four-law-denominators`, the chord `chord_gen`, `eq:four-law-weight`);
* `main_pt`: the pointwise bound on a doubly-positive source pair
  (`eq:four-law-numerator` divided by `(r^□)^α`);
* `resPsi_pt`, `tsum_resPsi_le`: the product bound `eq:four-law-product` integrated
  over the positive set, carrying the mean bad degrees;
* `tsum_qE_sq_le`, `overlap_two_le`: the overlap estimate with the reversed potentials,
  `eq:four-law-square` and the `(1-β) z` term;
* `failureD_symm`, `failureD_le_resQ`: the identity behind the cancellation of `Q`;
* `PhiDres_square_split`: the pairs with a zero child degree, by the resolved
  normalisation;
* `fourLaw_contraction`: the assembly.
-/
import GraphMarkovMatching.Stopped.Scalar
import GraphMarkovMatching.Potential.Restricted

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

/-- The weighted zero integral of one source law against a zero target and a normalising
target: `∫_{r_{τ} = 0} W_{τ'} dρ`. -/
noncomputable def wZeroD {X : Type} (α : ℝ) (ρ τ τ' : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, ρ x * (if rE τ R x = 0 then WresD α τ' R x else 0)

/-! ### Scalar preliminaries -/

/-- The bad degree is `ofReal` of its real form. -/
lemma qE_eq_ofReal_q {X : Type} (τ : PMF X) (R : X → X → Prop) (x : X) :
    qE τ R x = ENNReal.ofReal (q τ R x) := by
  rw [q, ENNReal.ofReal_toReal qE_ne_top]

/-- `β ≤ L` under the `L`-hypothesis (the summand at `q = 0`). -/
lemma beta_le_of_hL {α β L : ℝ}
    (hL : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α β q ≤ L) : β ≤ L := by
  have h := hL 0 le_rfl zero_le_one
  simpa [Lsummand] using h

/-- `0 ≤ K` under the `K`-hypothesis (the value at `q = β`). -/
lemma K_nonneg_of_hK {α β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hK : ∀ q, 0 ≤ q → q ≤ 1 → (q - β) * (1 - q) ^ α ≤ K) : 0 ≤ K := by
  have h := hK β hβ0 hβ1
  simpa using h

/-! ### The pointwise row estimate -/

/-- **The row estimate** (`thm:four-law-contraction`, the first row term): for bad
degrees `a = q₁¹`, `b = q₁²`, `d = q₂¹`, `e = q₂²` in `[0,1)` and a pair good degree
`rsq` dominating the straight pairing `(1-a)(1-e)` and the inclusion–exclusion value
`r₁¹r₂² + r₁²r₂¹ - r₁¹r₁²`,

    a b rsq^{-α} ≤ φ(ab) (1 + c (d + e)) + φ(a) (u⁻¹ + α) (φ(d) + φ(e)),

by the chord `chord_gen` when `d + e ≤ u` and by `eq:four-law-weight` otherwise. -/
lemma row_real {α u a b d e rsq : ℝ} (hα : 1 ≤ α) (hu0 : 0 < u) (hu1 : u < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hd0 : 0 ≤ d) (hd1 : d < 1) (he0 : 0 ≤ e) (he1 : e < 1)
    (h1 : (1 - a) * (1 - e) ≤ rsq)
    (h2 : (1 - a) * (1 - e) + (1 - b) * (1 - d) - (1 - a) * (1 - b) ≤ rsq) :
    a * b * rsq ^ (-α)
      ≤ phi α (a * b) * (1 + chordSlope α u * (d + e))
        + phi α a * ((1 / u + α) * (phi α d + phi α e)) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have h1e : (0 : ℝ) < 1 - e := by linarith
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hab1 : a * b < 1 := by nlinarith
  have h1ab : (0 : ℝ) < 1 - a * b := by linarith
  have hφab : 0 ≤ phi α (a * b) := phi_nonneg hab0 hab1
  have hφa : 0 ≤ phi α a := phi_nonneg ha0 ha1
  have hφd : 0 ≤ phi α d := phi_nonneg hd0 hd1
  have hφe : 0 ≤ phi α e := phi_nonneg he0 he1
  have hc : 0 ≤ chordSlope α u := chordSlope_nonneg hα0 hu0 hu1
  have hcu : (0 : ℝ) ≤ 1 / u + α := by positivity
  have hpos : 0 < (1 - a) * (1 - e) := mul_pos h1a h1e
  have hrsq : 0 < rsq := lt_of_lt_of_le hpos h1
  by_cases hs : d + e ≤ u
  · -- the chord case `s ≤ u`
    have h1s : (0 : ℝ) < 1 - (d + e) := by linarith
    have hlow : (1 - (d + e)) * (1 - a * b) ≤ rsq := by
      nlinarith [h2, mul_nonneg (mul_nonneg ha0 he0) (sub_nonneg.2 hb1.le),
        mul_nonneg (mul_nonneg hb0 hd0) (sub_nonneg.2 ha1.le)]
    have hmono : rsq ^ (-α) ≤ ((1 - (d + e)) * (1 - a * b)) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos h1s h1ab) hlow (by linarith)
    have hsplit : ((1 - (d + e)) * (1 - a * b)) ^ (-α)
        = (1 - (d + e)) ^ (-α) * (1 - a * b) ^ (-α) :=
      Real.mul_rpow h1s.le h1ab.le
    have hchord : (1 - (d + e)) ^ (-α) ≤ 1 + chordSlope α u * (d + e) :=
      chord_gen hα0 hu0 hu1 (by linarith) hs
    have hphi : phi α (a * b) = a * b * (1 - a * b) ^ (-α) := by
      rw [phi, Real.rpow_neg h1ab.le, div_eq_mul_inv]
    have hW0 : 0 ≤ (1 - a * b) ^ (-α) := Real.rpow_nonneg h1ab.le _
    calc a * b * rsq ^ (-α)
        ≤ a * b * ((1 - (d + e)) ^ (-α) * (1 - a * b) ^ (-α)) := by
          rw [← hsplit]; exact mul_le_mul_of_nonneg_left hmono hab0
      _ = phi α (a * b) * (1 - (d + e)) ^ (-α) := by rw [hphi]; ring
      _ ≤ phi α (a * b) * (1 + chordSlope α u * (d + e)) :=
          mul_le_mul_of_nonneg_left hchord hφab
      _ ≤ phi α (a * b) * (1 + chordSlope α u * (d + e))
            + phi α a * ((1 / u + α) * (phi α d + phi α e)) :=
          le_add_of_nonneg_right (by positivity)
  · -- the weight case `s > u`
    push Not at hs
    have hmono : rsq ^ (-α) ≤ ((1 - a) * (1 - e)) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos hpos h1 (by linarith)
    have hsplit : ((1 - a) * (1 - e)) ^ (-α) = (1 - a) ^ (-α) * (1 - e) ^ (-α) :=
      Real.mul_rpow h1a.le h1e.le
    have hphia : phi α a = a * (1 - a) ^ (-α) := by
      rw [phi, Real.rpow_neg h1a.le, div_eq_mul_inv]
    have hW : (1 - e) ^ (-α) ≤ 1 + α * phi α e := rpow_neg_alpha_le hα he1
    have hind : 1 ≤ (d + e) / u := by rw [le_div_iff₀ hu0]; linarith
    have hde : d ≤ phi α d := le_phi hα0 hd0 hd1
    have hee : e ≤ phi α e := le_phi hα0 he0 he1
    have hWa : 0 ≤ (1 - a) ^ (-α) := Real.rpow_nonneg h1a.le _
    have hWe : 0 ≤ (1 - e) ^ (-α) := Real.rpow_nonneg h1e.le _
    have hbound : (1 - e) ^ (-α) ≤ (1 / u + α) * (phi α d + phi α e) := by
      calc (1 - e) ^ (-α) ≤ 1 + α * phi α e := hW
        _ ≤ (d + e) / u + α * phi α e := by linarith
        _ ≤ (phi α d + phi α e) / u + α * (phi α d + phi α e) := by
            have h1 : (d + e) / u ≤ (phi α d + phi α e) / u :=
              div_le_div_of_nonneg_right (by linarith) hu0.le
            have h2 : α * phi α e ≤ α * (phi α d + phi α e) :=
              mul_le_mul_of_nonneg_left (by linarith) hα0
            linarith
        _ = (1 / u + α) * (phi α d + phi α e) := by ring
    calc a * b * rsq ^ (-α)
        ≤ a * 1 * ((1 - a) ^ (-α) * (1 - e) ^ (-α)) := by
          rw [← hsplit]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hb1.le ha0) hmono
            (Real.rpow_nonneg hrsq.le _) (by linarith)
      _ = phi α a * (1 - e) ^ (-α) := by rw [hphia]; ring
      _ ≤ phi α a * ((1 / u + α) * (phi α d + phi α e)) :=
          mul_le_mul_of_nonneg_left hbound hφa
      _ ≤ phi α (a * b) * (1 + chordSlope α u * (d + e))
            + phi α a * ((1 / u + α) * (phi α d + phi α e)) :=
          le_add_of_nonneg_left (by positivity)

/-- The row estimate in `ℝ≥0∞`, for an abstract pair good degree `rsq`. -/
lemma row_pt_gen {α u a b d e : ℝ} {rsq : ℝ≥0∞} (hα : 1 ≤ α) (hu0 : 0 < u) (hu1 : u < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hd0 : 0 ≤ d) (hd1 : d < 1) (he0 : 0 ≤ e) (he1 : e < 1) (hrsq : rsq ≠ ⊤)
    (h1 : (1 - a) * (1 - e) ≤ rsq.toReal)
    (h2 : (1 - a) * (1 - e) + (1 - b) * (1 - d) - (1 - a) * (1 - b) ≤ rsq.toReal) :
    ENNReal.ofReal a * ENNReal.ofReal b * rsq ^ (-α)
      ≤ ENNReal.ofReal (phi α (a * b))
          * (1 + ENNReal.ofReal (chordSlope α u) * (ENNReal.ofReal d + ENNReal.ofReal e))
        + ENNReal.ofReal (phi α a)
          * ((ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
            * (ENNReal.ofReal (phi α d) + ENNReal.ofReal (phi α e))) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hreal := row_real hα hu0 hu1 ha0 ha1 hb0 hb1 hd0 hd1 he0 he1 h1 h2
  have hpos : 0 < rsq.toReal :=
    lt_of_lt_of_le (mul_pos (by linarith) (by linarith)) h1
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hab1 : a * b < 1 := by nlinarith
  have hφab : 0 ≤ phi α (a * b) := phi_nonneg hab0 hab1
  have hφa : 0 ≤ phi α a := phi_nonneg ha0 ha1
  have hφd : 0 ≤ phi α d := phi_nonneg hd0 hd1
  have hφe : 0 ≤ phi α e := phi_nonneg he0 he1
  have hc : 0 ≤ chordSlope α u := chordSlope_nonneg hα0 hu0 hu1
  have hu' : (0 : ℝ) ≤ 1 / u := by positivity
  have hrsq_eq : rsq = ENNReal.ofReal rsq.toReal := (ENNReal.ofReal_toReal hrsq).symm
  rw [hrsq_eq, ENNReal.ofReal_rpow_of_pos hpos, ← ENNReal.ofReal_mul ha0,
    ← ENNReal.ofReal_mul hab0]
  refine le_trans (ENNReal.ofReal_le_ofReal hreal) (le_of_eq ?_)
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hφab,
    ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_mul hc, ENNReal.ofReal_add hd0 he0, ENNReal.ofReal_mul hφa,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add hu' hα0,
    ENNReal.ofReal_add hφd hφe]

/-- **The pointwise bound on a doubly-positive pair** (`thm:four-law-contraction`):
`eq:four-law-numerator` divided by `(r^□)^α`, the two row terms estimated by
`row_pt_gen` and the two overlap terms by `eq:four-law-denominators`. -/
lemma main_pt {X : Type} {α u : ℝ} (hα : 1 ≤ α) (hu0 : 0 < u) (hu1 : u < 1)
    (τ₁ τ₂ : PMF X) (R : X → X → Prop) (x₁ x₂ : X)
    (h11 : rE τ₁ R x₁ ≠ 0) (h12 : rE τ₂ R x₁ ≠ 0)
    (h21 : rE τ₁ R x₂ ≠ 0) (h22 : rE τ₂ R x₂ ≠ 0) :
    phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) (x₁, x₂))
      ≤ phiE α (q τ₁ R x₁ * q τ₂ R x₁)
          * (1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₂ + qE τ₂ R x₂))
        + phiE α (q τ₁ R x₁)
          * ((ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
            * (phiE α (q τ₁ R x₂) + phiE α (q τ₂ R x₂)))
        + (1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₁ + qE τ₂ R x₁))
          * phiE α (q τ₁ R x₂ * q τ₂ R x₂)
        + ((ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
            * (phiE α (q τ₁ R x₁) + phiE α (q τ₂ R x₁)))
          * phiE α (q τ₂ R x₂)
        + cOverlap τ₁ R x₁ x₂ * (WresD α τ₁ R x₁ * WresD α τ₂ R x₂)
        + cOverlap τ₂ R x₁ x₂ * (WresD α τ₂ R x₁ * WresD α τ₁ R x₂) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hαpos : (0 : ℝ) < α := by linarith
  have hq11 : q τ₁ R x₁ < 1 := q_lt_one_of_rE_ne_zero h11
  have hq12 : q τ₂ R x₁ < 1 := q_lt_one_of_rE_ne_zero h12
  have hq21 : q τ₁ R x₂ < 1 := q_lt_one_of_rE_ne_zero h21
  have hq22 : q τ₂ R x₂ < 1 := q_lt_one_of_rE_ne_zero h22
  have hn11 : 0 ≤ q τ₁ R x₁ := q_nonneg
  have hn12 : 0 ≤ q τ₂ R x₁ := q_nonneg
  have hn21 : 0 ≤ q τ₁ R x₂ := q_nonneg
  have hn22 : 0 ≤ q τ₂ R x₂ := q_nonneg
  have hp1 : q τ₁ R x₁ * q τ₂ R x₁ < 1 := by nlinarith
  have hp2 : q τ₁ R x₂ * q τ₂ R x₂ < 1 := by nlinarith
  -- the straight and crossed minorants, and inclusion–exclusion
  have hstrE := straight_le_rE_square τ₁ τ₂ R x₁ x₂
  have hcrE := crossed_le_rE_square τ₁ τ₂ R x₁ x₂
  have hie := rE_square_two_toReal τ₁ τ₂ R x₁ x₂
  have htop : rE (prodPMF τ₁ τ₂) (SquareRel R) (x₁, x₂) ≠ ⊤ := rE_ne_top
  have ha1l : (aOverlap τ₁ R x₁ x₂).toReal ≤ 1 - q τ₁ R x₁ := by
    have := ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_left τ₁ R x₁ x₂)
    rwa [toReal_rE_eq] at this
  have ha1r : (aOverlap τ₁ R x₁ x₂).toReal ≤ 1 - q τ₁ R x₂ := by
    have := ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_right τ₁ R x₁ x₂)
    rwa [toReal_rE_eq] at this
  have ha2l : (aOverlap τ₂ R x₁ x₂).toReal ≤ 1 - q τ₂ R x₁ := by
    have := ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_left τ₂ R x₁ x₂)
    rwa [toReal_rE_eq] at this
  have ha2r : (aOverlap τ₂ R x₁ x₂).toReal ≤ 1 - q τ₂ R x₂ := by
    have := ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_right τ₂ R x₁ x₂)
    rwa [toReal_rE_eq] at this
  have ha1n : 0 ≤ (aOverlap τ₁ R x₁ x₂).toReal := ENNReal.toReal_nonneg
  have ha2n : 0 ≤ (aOverlap τ₂ R x₁ x₂).toReal := ENNReal.toReal_nonneg
  rw [phiE_eq_qE_mul_rpow α (SquareRel R) (prodPMF τ₁ τ₂) hαpos (x₁, x₂)]
  rw [toReal_rE_eq τ₁ R x₁, toReal_rE_eq τ₂ R x₂, toReal_rE_eq τ₂ R x₁,
    toReal_rE_eq τ₁ R x₂] at hie
  generalize hrsq : rE (prodPMF τ₁ τ₂) (SquareRel R) (x₁, x₂) = rsq at hstrE hcrE hie htop ⊢
  have hstr : (1 - q τ₁ R x₁) * (1 - q τ₂ R x₂) ≤ rsq.toReal := by
    have h := ENNReal.toReal_mono htop hstrE
    rwa [ENNReal.toReal_mul, toReal_rE_eq, toReal_rE_eq] at h
  -- the first row term
  have hrow1 := row_pt_gen (a := q τ₁ R x₁) (b := q τ₂ R x₁) (d := q τ₁ R x₂)
    (e := q τ₂ R x₂) (rsq := rsq) hα hu0 hu1 hn11 hq11 hn12 hq12 hn21 hq21 hn22 hq22 htop
    hstr (by
      have hp : (aOverlap τ₁ R x₁ x₂).toReal * (aOverlap τ₂ R x₁ x₂).toReal
          ≤ (1 - q τ₁ R x₁) * (1 - q τ₂ R x₁) :=
        mul_le_mul ha1l ha2l ha2n (by linarith)
      nlinarith [hie, hp])
  have hrow1' : qE τ₁ R x₁ * qE τ₂ R x₁ * rsq ^ (-α)
      ≤ phiE α (q τ₁ R x₁ * q τ₂ R x₁)
          * (1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₂ + qE τ₂ R x₂))
        + phiE α (q τ₁ R x₁)
          * ((ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
            * (phiE α (q τ₁ R x₂) + phiE α (q τ₂ R x₂))) := by
    rw [qE_eq_ofReal_q, qE_eq_ofReal_q, qE_eq_ofReal_q, qE_eq_ofReal_q, phiE_of_lt hp1,
      phiE_of_lt hq11, phiE_of_lt hq21, phiE_of_lt hq22]
    exact hrow1
  -- the second row term, with the source rows exchanged
  have hrow2 := row_pt_gen (a := q τ₂ R x₂) (b := q τ₁ R x₂) (d := q τ₂ R x₁)
    (e := q τ₁ R x₁) (rsq := rsq) hα hu0 hu1 hn22 hq22 hn21 hq21 hn12 hq12 hn11 hq11 htop
    (by rw [mul_comm]; exact hstr) (by
      have hp : (aOverlap τ₁ R x₁ x₂).toReal * (aOverlap τ₂ R x₁ x₂).toReal
          ≤ (1 - q τ₁ R x₂) * (1 - q τ₂ R x₂) :=
        mul_le_mul ha1r ha2r ha2n (by linarith)
      nlinarith [hie, hp])
  have hrow2' : qE τ₁ R x₂ * qE τ₂ R x₂ * rsq ^ (-α)
      ≤ (1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₁ + qE τ₂ R x₁))
          * phiE α (q τ₁ R x₂ * q τ₂ R x₂)
        + ((ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
            * (phiE α (q τ₁ R x₁) + phiE α (q τ₂ R x₁)))
          * phiE α (q τ₂ R x₂) := by
    rw [qE_eq_ofReal_q, qE_eq_ofReal_q, qE_eq_ofReal_q, qE_eq_ofReal_q, phiE_of_lt hp2,
      phiE_of_lt hq11, phiE_of_lt hq12, phiE_of_lt hq22]
    rw [mul_comm (q τ₂ R x₂) (q τ₁ R x₂), add_comm (ENNReal.ofReal (q τ₂ R x₁)),
      add_comm (ENNReal.ofReal (phi α (q τ₂ R x₁)))] at hrow2
    calc ENNReal.ofReal (q τ₁ R x₂) * ENNReal.ofReal (q τ₂ R x₂) * rsq ^ (-α)
        = ENNReal.ofReal (q τ₂ R x₂) * ENNReal.ofReal (q τ₁ R x₂) * rsq ^ (-α) := by ring
      _ ≤ _ := hrow2
      _ = _ := by ring
  -- the overlap terms
  have hov1 : cOverlap τ₁ R x₁ x₂ * rsq ^ (-α)
      ≤ cOverlap τ₁ R x₁ x₂ * (WresD α τ₁ R x₁ * WresD α τ₂ R x₂) := by
    refine mul_le_mul_right ?_ _
    calc rsq ^ (-α) ≤ (rE τ₁ R x₁ * rE τ₂ R x₂) ^ (-α) := rpow_neg_antitone hα0 hstrE
      _ = (rE τ₁ R x₁) ^ (-α) * (rE τ₂ R x₂) ^ (-α) :=
          ENNReal.mul_rpow_of_ne_zero h11 h22 (-α)
      _ = WresD α τ₁ R x₁ * WresD α τ₂ R x₂ := by
          rw [rE_rpow_neg_eq_WresD τ₁ R x₁ h11, rE_rpow_neg_eq_WresD τ₂ R x₂ h22]
  have hov2 : cOverlap τ₂ R x₁ x₂ * rsq ^ (-α)
      ≤ cOverlap τ₂ R x₁ x₂ * (WresD α τ₂ R x₁ * WresD α τ₁ R x₂) := by
    refine mul_le_mul_right ?_ _
    calc rsq ^ (-α) ≤ (rE τ₁ R x₂ * rE τ₂ R x₁) ^ (-α) := rpow_neg_antitone hα0 hcrE
      _ = (rE τ₁ R x₂) ^ (-α) * (rE τ₂ R x₁) ^ (-α) :=
          ENNReal.mul_rpow_of_ne_zero h21 h12 (-α)
      _ = WresD α τ₂ R x₁ * WresD α τ₁ R x₂ := by
          rw [rE_rpow_neg_eq_WresD τ₁ R x₂ h21, rE_rpow_neg_eq_WresD τ₂ R x₁ h12, mul_comm]
  calc qE (prodPMF τ₁ τ₂) (SquareRel R) (x₁, x₂) * rsq ^ (-α)
      ≤ (qE τ₁ R x₁ * qE τ₂ R x₁ + qE τ₁ R x₂ * qE τ₂ R x₂
          + cOverlap τ₁ R x₁ x₂ + cOverlap τ₂ R x₁ x₂) * rsq ^ (-α) :=
        mul_le_mul_left (qE_square_two τ₁ τ₂ R x₁ x₂) _
    _ = qE τ₁ R x₁ * qE τ₂ R x₁ * rsq ^ (-α) + qE τ₁ R x₂ * qE τ₂ R x₂ * rsq ^ (-α)
          + cOverlap τ₁ R x₁ x₂ * rsq ^ (-α) + cOverlap τ₂ R x₁ x₂ * rsq ^ (-α) := by ring
    _ ≤ _ := by
        refine le_trans (add_le_add (add_le_add (add_le_add hrow1' hrow2') hov1) hov2)
          (le_of_eq ?_)
        ring

/-! ### The restricted summands -/

/-- The indicator of the doubly-positive set `F = {r_{τ₁} > 0, r_{τ₂} > 0}`. -/
private noncomputable def dpInd {X : Type} (τ₁ τ₂ : PMF X) (R : X → X → Prop) (x : X) :
    ℝ≥0∞ :=
  if rE τ₁ R x = 0 ∨ rE τ₂ R x = 0 then 0 else 1

/-- The restricted potential summand `𝟙[r_τ > 0] φ(q_τ)`. -/
private noncomputable def resPhi {X : Type} (α : ℝ) (τ : PMF X) (R : X → X → Prop) (x : X) :
    ℝ≥0∞ :=
  if rE τ R x = 0 then 0 else phiE α (q τ R x)

/-- The restricted product summand `𝟙_F φ(q_{τ₁} q_{τ₂})` of `I_i`. -/
private noncomputable def resPsi {X : Type} (α : ℝ) (τ₁ τ₂ : PMF X) (R : X → X → Prop)
    (x : X) : ℝ≥0∞ :=
  dpInd τ₁ τ₂ R x * phiE α (q τ₁ R x * q τ₂ R x)

/-- The restricted bad degree `𝟙_F q_τ`. -/
private noncomputable def resQ {X : Type} (τ₁ τ₂ τ : PMF X) (R : X → X → Prop) (x : X) :
    ℝ≥0∞ :=
  dpInd τ₁ τ₂ R x * qE τ R x

/-- The chord factor `1 + c (q_{τ₁} + q_{τ₂})` on `F`. -/
private noncomputable def chordFac {X : Type} (cb : ℝ≥0∞) (τ₁ τ₂ : PMF X) (R : X → X → Prop)
    (x : X) : ℝ≥0∞ :=
  1 + cb * (resQ τ₁ τ₂ τ₁ R x + resQ τ₁ τ₂ τ₂ R x)

/-- The weight factor `(u⁻¹ + α)(φ(q_{τ₁}) + φ(q_{τ₂}))` on the positive sets. -/
private noncomputable def weightFac {X : Type} (k : ℝ≥0∞) (α : ℝ) (τ₁ τ₂ : PMF X)
    (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  k * (resPhi α τ₁ R x + resPhi α τ₂ R x)

/-- The restricted potential is the integral of `resPhi` (`thm:four-law-contraction`). -/
private lemma PhiDres_eq_resPhi {X : Type} (α : ℝ) (ρ τ : PMF X) (R : X → X → Prop) :
    PhiDres α ρ τ R = ∑' x, ρ x * resPhi α τ R x := rfl

/-- The indicator of `F` is at most one. -/
private lemma dpInd_le_one {X : Type} (τ₁ τ₂ : PMF X) (R : X → X → Prop) (x : X) :
    dpInd τ₁ τ₂ R x ≤ 1 := by
  unfold dpInd; split_ifs <;> simp

/-- Off `{r_{τ₁} > 0}` the indicator of `F` vanishes. -/
private lemma dpInd_eq_zero_left {X : Type} {τ₁ τ₂ : PMF X} {R : X → X → Prop} {x : X}
    (h : rE τ₁ R x = 0) : dpInd τ₁ τ₂ R x = 0 := by
  unfold dpInd; rw [ite_eq_left (Or.inl h)]

/-- Off `{r_{τ₂} > 0}` the indicator of `F` vanishes. -/
private lemma dpInd_eq_zero_right {X : Type} {τ₁ τ₂ : PMF X} {R : X → X → Prop} {x : X}
    (h : rE τ₂ R x = 0) : dpInd τ₁ τ₂ R x = 0 := by
  unfold dpInd; rw [ite_eq_left (Or.inr h)]

/-- On `F` the indicator is one. -/
private lemma dpInd_eq_one {X : Type} {τ₁ τ₂ : PMF X} {R : X → X → Prop} {x : X}
    (h₁ : rE τ₁ R x ≠ 0) (h₂ : rE τ₂ R x ≠ 0) : dpInd τ₁ τ₂ R x = 1 := by
  unfold dpInd; rw [ite_eq_right (not_or.mpr ⟨h₁, h₂⟩)]

/-- `∫_F q_τ dρ ≤ P(ρ,τ)` when `F ⊆ {r_τ > 0}`. -/
private lemma tsum_resQ_le_PhiDres {X : Type} {α : ℝ} (hα : 0 ≤ α) (ρ τ₁ τ₂ τ : PMF X)
    (R : X → X → Prop) (hF : ∀ x, rE τ R x = 0 → dpInd τ₁ τ₂ R x = 0) :
    ∑' x, ρ x * resQ τ₁ τ₂ τ R x ≤ PhiDres α ρ τ R := by
  rw [PhiDres]
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  by_cases h : rE τ R x = 0
  · rw [resQ, hF x h, zero_mul, ite_eq_left h]
  · rw [ite_eq_right h, resQ]
    calc dpInd τ₁ τ₂ R x * qE τ R x ≤ 1 * qE τ R x :=
          mul_le_mul_left (dpInd_le_one τ₁ τ₂ R x) _
      _ = qE τ R x := one_mul _
      _ ≤ phiE α (q τ R x) := by
          rw [qE_eq_ofReal_q]; exact ofReal_le_phiE hα q_nonneg q_le_one

/-- `∫_F q_τ dρ ≤ 1`. -/
private lemma tsum_resQ_le_one {X : Type} (ρ τ₁ τ₂ τ : PMF X) (R : X → X → Prop) :
    ∑' x, ρ x * resQ τ₁ τ₂ τ R x ≤ 1 := by
  calc ∑' x, ρ x * resQ τ₁ τ₂ τ R x ≤ ∑' x, ρ x * 1 := by
        refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
        rw [resQ]
        calc dpInd τ₁ τ₂ R x * qE τ R x ≤ 1 * 1 :=
              mul_le_mul' (dpInd_le_one τ₁ τ₂ R x) qE_le_one
          _ = 1 := one_mul 1
    _ = 1 := by simp

/-- **The product bound on `F`** (`eq:four-law-product`, pointwise):
`2 𝟙_F φ(q₁q₂) + β 𝟙_F (q₁ + q₂) ≤ L (𝟙[r₁>0] φ(q₁) + 𝟙[r₂>0] φ(q₂))`. -/
private lemma resPsi_pt {X : Type} {α β L : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hL : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α β q ≤ L) (τ₁ τ₂ : PMF X) (R : X → X → Prop)
    (x : X) :
    2 * resPsi α τ₁ τ₂ R x + ENNReal.ofReal β * (resQ τ₁ τ₂ τ₁ R x + resQ τ₁ τ₂ τ₂ R x)
      ≤ ENNReal.ofReal L * (resPhi α τ₁ R x + resPhi α τ₂ R x) := by
  by_cases h : rE τ₁ R x = 0 ∨ rE τ₂ R x = 0
  · have h0 : dpInd τ₁ τ₂ R x = 0 := by unfold dpInd; rw [ite_eq_left h]
    simp only [resPsi, resQ, h0, zero_mul, mul_zero, add_zero]
    exact zero_le
  · push Not at h
    obtain ⟨h1, h2⟩ := h
    have e1 : dpInd τ₁ τ₂ R x = 1 := dpInd_eq_one h1 h2
    have hq1 : q τ₁ R x < 1 := q_lt_one_of_rE_ne_zero h1
    have hq2 : q τ₂ R x < 1 := q_lt_one_of_rE_ne_zero h2
    have hn1 : 0 ≤ q τ₁ R x := q_nonneg
    have hn2 : 0 ≤ q τ₂ R x := q_nonneg
    have hp : q τ₁ R x * q τ₂ R x < 1 := by nlinarith
    have hφ1 : 0 ≤ phi α (q τ₁ R x) := phi_nonneg hn1 hq1
    have hφ2 : 0 ≤ phi α (q τ₂ R x) := phi_nonneg hn2 hq2
    have hφp : 0 ≤ phi α (q τ₁ R x * q τ₂ R x) := phi_nonneg (mul_nonneg hn1 hn2) hp
    have hL0 : 0 ≤ L := le_trans hβ (beta_le_of_hL hL)
    have hreal := phi_mul_le_beta hα hβ hL hn1 hq1 hn2 hq2
    simp only [resPsi, resQ, resPhi, e1, one_mul, ite_eq_right h1, ite_eq_right h2]
    rw [phiE_of_lt hp, phiE_of_lt hq1, phiE_of_lt hq2, qE_eq_ofReal_q, qE_eq_ofReal_q]
    calc 2 * ENNReal.ofReal (phi α (q τ₁ R x * q τ₂ R x))
          + ENNReal.ofReal β * (ENNReal.ofReal (q τ₁ R x) + ENNReal.ofReal (q τ₂ R x))
        = ENNReal.ofReal (2 * phi α (q τ₁ R x * q τ₂ R x)
            + β * (q τ₁ R x + q τ₂ R x)) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hβ,
            ENNReal.ofReal_add hn1 hn2, ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal (L * (phi α (q τ₁ R x) + phi α (q τ₂ R x))) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal L
            * (ENNReal.ofReal (phi α (q τ₁ R x)) + ENNReal.ofReal (phi α (q τ₂ R x))) := by
          rw [ENNReal.ofReal_mul hL0, ENNReal.ofReal_add hφ1 hφ2]

/-- **The product bound on `F`, integrated**:
`2 I + β ∫_F (q_{τ₁} + q_{τ₂}) dρ ≤ L (P(ρ,τ₁) + P(ρ,τ₂))`. -/
private lemma tsum_resPsi_le {X : Type} {α β L : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hL : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α β q ≤ L) (ρ τ₁ τ₂ : PMF X) (R : X → X → Prop) :
    2 * (∑' x, ρ x * resPsi α τ₁ τ₂ R x)
        + ENNReal.ofReal β
          * ((∑' x, ρ x * resQ τ₁ τ₂ τ₁ R x) + ∑' x, ρ x * resQ τ₁ τ₂ τ₂ R x)
      ≤ ENNReal.ofReal L * (PhiDres α ρ τ₁ R + PhiDres α ρ τ₂ R) := by
  rw [PhiDres_eq_resPhi, PhiDres_eq_resPhi]
  have e : 2 * (∑' x, ρ x * resPsi α τ₁ τ₂ R x)
        + ENNReal.ofReal β
          * ((∑' x, ρ x * resQ τ₁ τ₂ τ₁ R x) + ∑' x, ρ x * resQ τ₁ τ₂ τ₂ R x)
      = ∑' x, (2 * (ρ x * resPsi α τ₁ τ₂ R x)
          + ENNReal.ofReal β * (ρ x * resQ τ₁ τ₂ τ₁ R x + ρ x * resQ τ₁ τ₂ τ₂ R x)) := by
    simp only [ENNReal.tsum_add, ENNReal.tsum_mul_left]
  have e' : ENNReal.ofReal L * ((∑' x, ρ x * resPhi α τ₁ R x) + ∑' x, ρ x * resPhi α τ₂ R x)
      = ∑' x, ENNReal.ofReal L * (ρ x * resPhi α τ₁ R x + ρ x * resPhi α τ₂ R x) := by
    simp only [ENNReal.tsum_add, ENNReal.tsum_mul_left]
  rw [e, e']
  refine ENNReal.tsum_le_tsum fun x => ?_
  have h := resPsi_pt hα hβ hL τ₁ τ₂ R x
  calc 2 * (ρ x * resPsi α τ₁ τ₂ R x)
        + ENNReal.ofReal β * (ρ x * resQ τ₁ τ₂ τ₁ R x + ρ x * resQ τ₁ τ₂ τ₂ R x)
      = ρ x * (2 * resPsi α τ₁ τ₂ R x
          + ENNReal.ofReal β * (resQ τ₁ τ₂ τ₁ R x + resQ τ₁ τ₂ τ₂ R x)) := by ring
    _ ≤ ρ x * (ENNReal.ofReal L * (resPhi α τ₁ R x + resPhi α τ₂ R x)) :=
        mul_le_mul_right h _
    _ = ENNReal.ofReal L * (ρ x * resPhi α τ₁ R x + ρ x * resPhi α τ₂ R x) := by ring

/-- The chord factor integrates to `1 + c (∫_F q_{τ₁} dρ + ∫_F q_{τ₂} dρ)`. -/
private lemma tsum_chordFac {X : Type} (cb : ℝ≥0∞) (ρ τ₁ τ₂ : PMF X) (R : X → X → Prop) :
    ∑' x, ρ x * chordFac cb τ₁ τ₂ R x
      = 1 + cb * ((∑' x, ρ x * resQ τ₁ τ₂ τ₁ R x) + ∑' x, ρ x * resQ τ₁ τ₂ τ₂ R x) := by
  rw [tsum_congr fun x => show ρ x * chordFac cb τ₁ τ₂ R x
      = ρ x + cb * (ρ x * resQ τ₁ τ₂ τ₁ R x + ρ x * resQ τ₁ τ₂ τ₂ R x) from by
        rw [chordFac]; ring,
    ENNReal.tsum_add, PMF.tsum_coe, ENNReal.tsum_mul_left, ENNReal.tsum_add]

/-- The weight factor integrates to `k (P(ρ,τ₁) + P(ρ,τ₂))`. -/
private lemma tsum_weightFac {X : Type} (k : ℝ≥0∞) (α : ℝ) (ρ τ₁ τ₂ : PMF X)
    (R : X → X → Prop) :
    ∑' x, ρ x * weightFac k α τ₁ τ₂ R x = k * (PhiDres α ρ τ₁ R + PhiDres α ρ τ₂ R) := by
  rw [PhiDres_eq_resPhi, PhiDres_eq_resPhi,
    tsum_congr fun x => show ρ x * weightFac k α τ₁ τ₂ R x
      = k * (ρ x * resPhi α τ₁ R x + ρ x * resPhi α τ₂ R x) from by
        rw [weightFac]; ring,
    ENNReal.tsum_mul_left, ENNReal.tsum_add]

/-! ### The mean bad degrees -/

/-- **Symmetry of the mean bad degree** (`thm:four-law-contraction`):
`∫ q_τ dρ = ∫ q_ρ dτ` by symmetry of `R` and Fubini's theorem. -/
lemma failureD_symm {X : Type} (ρ τ : PMF X) (R : X → X → Prop)
    (hsymm : ∀ a b, R a b → R b a) : failureD ρ τ R = failureD τ ρ R := by
  have hb : ∀ x y, badInd R x y = badInd R y x := by
    intro x y
    unfold badInd
    by_cases h : R x y
    · rw [ite_eq_left h, ite_eq_left (hsymm x y h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hsymm y x h'))]
  calc failureD ρ τ R = ∑' x, ∑' y, ρ x * (τ y * badInd R x y) := by
        rw [failureD]
        exact tsum_congr fun x => by rw [qE_eq_tsum_mul, ENNReal.tsum_mul_left]
    _ = ∑' y, ∑' x, ρ x * (τ y * badInd R x y) := ENNReal.tsum_comm
    _ = ∑' y, τ y * ∑' x, ρ x * badInd R y x := by
        refine tsum_congr fun y => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => by rw [hb x y]; ring
    _ = failureD τ ρ R := by
        rw [failureD]
        exact tsum_congr fun y => by rw [qE_eq_tsum_mul]

/-- The omitted portion of the mean bad degree is carried by the zero masses:
`∫ q_τ dρ ≤ ∫_F q_τ dρ + ρ{r_{τ₁} = 0} + ρ{r_{τ₂} = 0}`. -/
private lemma failureD_le_resQ {X : Type} (ρ τ₁ τ₂ τ : PMF X) (R : X → X → Prop) :
    failureD ρ τ R
      ≤ (∑' x, ρ x * resQ τ₁ τ₂ τ R x) + zMass ρ τ₁ R + zMass ρ τ₂ R := by
  rw [failureD, zMass, zMass, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases h : rE τ₁ R x = 0 ∨ rE τ₂ R x = 0
  · rcases h with h | h
    · rw [ite_eq_left h, mul_one]
      calc ρ x * qE τ R x ≤ ρ x * 1 := mul_le_mul_right qE_le_one _
        _ = ρ x := mul_one _
        _ ≤ _ := le_add_self.trans le_self_add
    · rw [ite_eq_left h, mul_one]
      calc ρ x * qE τ R x ≤ ρ x * 1 := mul_le_mul_right qE_le_one _
        _ = ρ x := mul_one _
        _ ≤ _ := le_add_self
  · push Not at h
    rw [resQ, dpInd_eq_one h.1 h.2, one_mul]
    exact le_self_add.trans le_self_add

/-- **The reversed square bound** (`eq:four-law-square` integrated):
`∫ q_ρ² dτ ≤ K P(τ,ρ) + β ∫ q_ρ dτ + (1-β) τ{r_ρ = 0}`; the last term accounts for
`q_ρ = 1`. -/
private lemma tsum_qE_sq_le {X : Type} {α β K : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hK : ∀ q, 0 ≤ q → q ≤ 1 → (q - β) * (1 - q) ^ α ≤ K) (τ ρ : PMF X)
    (R : X → X → Prop) :
    ∑' y, τ y * qE ρ R y ^ 2
      ≤ ENNReal.ofReal K * PhiDres α τ ρ R + ENNReal.ofReal β * failureD τ ρ R
        + ENNReal.ofReal (1 - β) * zMass τ ρ R := by
  have hK0 : 0 ≤ K := K_nonneg_of_hK hβ0 hβ1 hK
  rw [PhiDres, failureD, zMass, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun y => ?_
  by_cases h : rE ρ R y = 0
  · have hq1 : qE ρ R y = 1 := by
      have := rE_add_qE ρ R y
      rwa [h, zero_add] at this
    rw [ite_eq_left h, ite_eq_left h, hq1]
    simp only [mul_zero, mul_one, zero_add, one_pow]
    rw [← add_mul, ← ENNReal.ofReal_add hβ0 (by linarith),
      show β + (1 - β) = (1 : ℝ) from by ring, ENNReal.ofReal_one, one_mul]
  · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero, add_zero]
    have hq : q ρ R y < 1 := q_lt_one_of_rE_ne_zero h
    have hn : 0 ≤ q ρ R y := q_nonneg
    have hφ : 0 ≤ phi α (q ρ R y) := phi_nonneg hn hq
    have hreal := sq_le_K_phi_add hα hK hn hq
    rw [qE_eq_ofReal_q, phiE_of_lt hq, ← ENNReal.ofReal_pow hn]
    calc τ y * ENNReal.ofReal (q ρ R y ^ 2)
        ≤ τ y * ENNReal.ofReal (K * phi α (q ρ R y) + β * q ρ R y) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal hreal) _
      _ = ENNReal.ofReal K * (τ y * ENNReal.ofReal (phi α (q ρ R y)))
          + ENNReal.ofReal β * (τ y * ENNReal.ofReal (q ρ R y)) := by
          rw [ENNReal.ofReal_add (mul_nonneg hK0 hφ) (mul_nonneg hβ0 hn),
            ENNReal.ofReal_mul hK0, ENNReal.ofReal_mul hβ0]
          ring

/-- **One overlap integral** (`eq:four-law-overlaps`, one target law): with
`H_i ≤ q_{ρ_i} + αM`, the reversed potentials and `eq:four-law-square`,
`2 ∫ H₁ H₂ dτ ≤ 2KM + β (∫ q_{ρ₁} dτ + ∫ q_{ρ₂} dτ) + 2(1-β) z + 4αM² + 4αMz + 2α²M²`. -/
private lemma overlap_two_le {X : Type} {α β K : ℝ} (hα : 1 ≤ α) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hK : ∀ q, 0 ≤ q → q ≤ 1 → (q - β) * (1 - q) ^ α ≤ K) (τ ρ₁ ρ₂ τa τb : PMF X)
    (R : X → X → Prop) (hsymm : ∀ a b, R a b → R b a) (M z : ℝ≥0∞)
    (h1 : PhiDres α ρ₁ τa R ≤ M) (h2 : PhiDres α ρ₂ τb R ≤ M)
    (hr1 : PhiDres α τ ρ₁ R ≤ M) (hr2 : PhiDres α τ ρ₂ R ≤ M)
    (hz1 : zMass τ ρ₁ R ≤ z) (hz2 : zMass τ ρ₂ R ≤ z) :
    2 * ∑' y, τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y)
      ≤ 2 * ENNReal.ofReal K * M
        + ENNReal.ofReal β * (failureD τ ρ₁ R + failureD τ ρ₂ R)
        + 2 * ENNReal.ofReal (1 - β) * z
        + 4 * ENNReal.ofReal α * M ^ 2 + 4 * ENNReal.ofReal α * M * z
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hH1 : ∀ y, HresD α ρ₁ τa R y ≤ qE ρ₁ R y + ENNReal.ofReal α * M := fun y =>
    (HresD_le hα ρ₁ τa R hsymm y).trans
      (add_le_add le_rfl (mul_le_mul_right ((KresD_le_PhiDres α ρ₁ τa R y).trans h1) _))
  have hH2 : ∀ y, HresD α ρ₂ τb R y ≤ qE ρ₂ R y + ENNReal.ofReal α * M := fun y =>
    (HresD_le hα ρ₂ τb R hsymm y).trans
      (add_le_add le_rfl (mul_le_mul_right ((KresD_le_PhiDres α ρ₂ τb R y).trans h2) _))
  have hpt : ∀ y, 2 * (τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y))
      ≤ τ y * qE ρ₁ R y ^ 2 + τ y * qE ρ₂ R y ^ 2
        + 2 * ENNReal.ofReal α * M * (τ y * qE ρ₁ R y + τ y * qE ρ₂ R y)
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 * τ y := by
    intro y
    calc 2 * (τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y))
        = τ y * (2 * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y)) := by ring
      _ ≤ τ y * (HresD α ρ₁ τa R y ^ 2 + HresD α ρ₂ τb R y ^ 2) :=
          mul_le_mul_right (ennreal_two_mul_le_add_sq _ _) _
      _ ≤ τ y * ((qE ρ₁ R y + ENNReal.ofReal α * M) ^ 2
          + (qE ρ₂ R y + ENNReal.ofReal α * M) ^ 2) := by
          gcongr
          · exact hH1 y
          · exact hH2 y
      _ = _ := by ring
  have hsq1 := tsum_qE_sq_le hα0 hβ0 hβ1 hK τ ρ₁ R
  have hsq2 := tsum_qE_sq_le hα0 hβ0 hβ1 hK τ ρ₂ R
  have hF1 : failureD τ ρ₁ R ≤ M + z :=
    (failureD_le_PhiDres_add_zMass α hα0 τ ρ₁ R).trans (add_le_add hr1 hz1)
  have hF2 : failureD τ ρ₂ R ≤ M + z :=
    (failureD_le_PhiDres_add_zMass α hα0 τ ρ₂ R).trans (add_le_add hr2 hz2)
  calc 2 * ∑' y, τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y)
      = ∑' y, 2 * (τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y)) :=
        ENNReal.tsum_mul_left.symm
    _ ≤ ∑' y, (τ y * qE ρ₁ R y ^ 2 + τ y * qE ρ₂ R y ^ 2
        + 2 * ENNReal.ofReal α * M * (τ y * qE ρ₁ R y + τ y * qE ρ₂ R y)
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 * τ y) := ENNReal.tsum_le_tsum hpt
    _ = (∑' y, τ y * qE ρ₁ R y ^ 2) + (∑' y, τ y * qE ρ₂ R y ^ 2)
        + 2 * ENNReal.ofReal α * M * (failureD τ ρ₁ R + failureD τ ρ₂ R)
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left,
          ENNReal.tsum_mul_left, ENNReal.tsum_add, PMF.tsum_coe, mul_one, failureD, failureD]
    _ ≤ (ENNReal.ofReal K * M + ENNReal.ofReal β * failureD τ ρ₁ R
          + ENNReal.ofReal (1 - β) * z)
        + (ENNReal.ofReal K * M + ENNReal.ofReal β * failureD τ ρ₂ R
          + ENNReal.ofReal (1 - β) * z)
        + 2 * ENNReal.ofReal α * M * ((M + z) + (M + z))
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 := by
        gcongr
        · exact hsq1.trans (add_le_add (add_le_add (mul_le_mul_right hr1 _) le_rfl)
            (mul_le_mul_right hz1 _))
        · exact hsq2.trans (add_le_add (add_le_add (mul_le_mul_right hr2 _) le_rfl)
            (mul_le_mul_right hz2 _))
    _ = _ := by ring

/-! ### The pairs with a zero child degree -/

/-- **The resolved pairs** (`thm:four-law-contraction`, last paragraph): the restricted
square potential is at most the integral over the doubly-positive set plus the four
weighted zero integrals times the corresponding inverse moments. -/
private lemma PhiDres_square_split {X : Type} {α : ℝ} (hα : 0 < α) (ρ₁ ρ₂ τ₁ τ₂ : PMF X)
    (R : X → X → Prop) :
    PhiDres α (prodPMF ρ₁ ρ₂) (prodPMF τ₁ τ₂) (SquareRel R)
      ≤ (∑' p : X × X, prodPMF ρ₁ ρ₂ p * (dpInd τ₁ τ₂ R p.1 * dpInd τ₁ τ₂ R p.2
            * phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) p)))
        + wZeroD α ρ₁ τ₁ τ₂ R * (∑' x, ρ₂ x * WresD α τ₁ R x)
        + wZeroD α ρ₁ τ₂ τ₁ R * (∑' x, ρ₂ x * WresD α τ₂ R x)
        + (∑' x, ρ₁ x * WresD α τ₁ R x) * wZeroD α ρ₂ τ₁ τ₂ R
        + (∑' x, ρ₁ x * WresD α τ₂ R x) * wZeroD α ρ₂ τ₂ τ₁ R := by
  have hpt : ∀ p : X × X, prodPMF ρ₁ ρ₂ p
      * (if rE (prodPMF τ₁ τ₂) (SquareRel R) p = 0 then 0
          else phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) p))
      ≤ prodPMF ρ₁ ρ₂ p * (dpInd τ₁ τ₂ R p.1 * dpInd τ₁ τ₂ R p.2
            * phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) p))
        + prodPMF ρ₁ ρ₂ p
          * ((if rE τ₁ R p.1 = 0 then WresD α τ₂ R p.1 else 0) * WresD α τ₁ R p.2)
        + prodPMF ρ₁ ρ₂ p
          * ((if rE τ₂ R p.1 = 0 then WresD α τ₁ R p.1 else 0) * WresD α τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p
          * (WresD α τ₁ R p.1 * (if rE τ₁ R p.2 = 0 then WresD α τ₂ R p.2 else 0))
        + prodPMF ρ₁ ρ₂ p
          * (WresD α τ₂ R p.1 * (if rE τ₂ R p.2 = 0 then WresD α τ₁ R p.2 else 0)) := by
    rintro ⟨x₁, x₂⟩
    by_cases hsq : rE (prodPMF τ₁ τ₂) (SquareRel R) (x₁, x₂) = 0
    · rw [ite_eq_left hsq, mul_zero]
      exact zero_le
    · rw [ite_eq_right hsq]
      by_cases hd : rE τ₁ R x₁ = 0 ∨ rE τ₂ R x₁ = 0 ∨ rE τ₁ R x₂ = 0 ∨ rE τ₂ R x₂ = 0
      · rcases hd with h | h | h | h
        · -- `r_{τ₁}(x₁) = 0`: the straight pairing is blocked, the crossed survives
          have hcr : rE τ₁ R x₂ * rE τ₂ R x₁ ≠ 0 := fun hc =>
            hsq ((rE_square_eq_zero_iff τ₁ τ₂ R x₁ x₂).mpr ⟨by rw [h, zero_mul], hc⟩)
          obtain ⟨hc1, hd0⟩ := mul_ne_zero_iff.mp hcr
          have hb := phiE_square_resolved_le_crossed hα τ₁ τ₂ R x₁ x₂ hc1 hd0
          rw [rE_rpow_neg_eq_WresD τ₁ R x₂ hc1, rE_rpow_neg_eq_WresD τ₂ R x₁ hd0,
            mul_comm] at hb
          refine le_trans (le_trans (mul_le_mul_right hb _) ?_)
            (le_add_self.trans (le_self_add.trans (le_self_add.trans le_self_add)))
          rw [ite_eq_left h]
        · -- `r_{τ₂}(x₁) = 0`: the crossed pairing is blocked, the straight survives
          have hst : rE τ₁ R x₁ * rE τ₂ R x₂ ≠ 0 := fun hc =>
            hsq ((rE_square_eq_zero_iff τ₁ τ₂ R x₁ x₂).mpr ⟨hc, by rw [h, mul_zero]⟩)
          obtain ⟨hc0, hd1⟩ := mul_ne_zero_iff.mp hst
          have hb := phiE_square_resolved_le hα τ₁ τ₂ R x₁ x₂ hc0 hd1
          rw [rE_rpow_neg_eq_WresD τ₁ R x₁ hc0, rE_rpow_neg_eq_WresD τ₂ R x₂ hd1] at hb
          refine le_trans (le_trans (mul_le_mul_right hb _) ?_)
            (le_add_self.trans (le_self_add.trans le_self_add))
          rw [ite_eq_left h]
        · -- `r_{τ₁}(x₂) = 0`: the crossed pairing is blocked, the straight survives
          have hst : rE τ₁ R x₁ * rE τ₂ R x₂ ≠ 0 := fun hc =>
            hsq ((rE_square_eq_zero_iff τ₁ τ₂ R x₁ x₂).mpr ⟨hc, by rw [h, zero_mul]⟩)
          obtain ⟨hc0, hd1⟩ := mul_ne_zero_iff.mp hst
          have hb := phiE_square_resolved_le hα τ₁ τ₂ R x₁ x₂ hc0 hd1
          rw [rE_rpow_neg_eq_WresD τ₁ R x₁ hc0, rE_rpow_neg_eq_WresD τ₂ R x₂ hd1] at hb
          refine le_trans (le_trans (mul_le_mul_right hb _) ?_)
            (le_add_self.trans le_self_add)
          rw [ite_eq_left h]
        · -- `r_{τ₂}(x₂) = 0`: the straight pairing is blocked, the crossed survives
          have hcr : rE τ₁ R x₂ * rE τ₂ R x₁ ≠ 0 := fun hc =>
            hsq ((rE_square_eq_zero_iff τ₁ τ₂ R x₁ x₂).mpr ⟨by rw [h, mul_zero], hc⟩)
          obtain ⟨hc1, hd0⟩ := mul_ne_zero_iff.mp hcr
          have hb := phiE_square_resolved_le_crossed hα τ₁ τ₂ R x₁ x₂ hc1 hd0
          rw [rE_rpow_neg_eq_WresD τ₁ R x₂ hc1, rE_rpow_neg_eq_WresD τ₂ R x₁ hd0,
            mul_comm] at hb
          refine le_trans (le_trans (mul_le_mul_right hb _) ?_) le_add_self
          rw [ite_eq_left h]
      · push Not at hd
        obtain ⟨hn11, hn12, hn21, hn22⟩ := hd
        refine le_trans (le_of_eq ?_)
          (le_self_add.trans (le_self_add.trans (le_self_add.trans le_self_add)))
        rw [dpInd_eq_one hn11 hn12, dpInd_eq_one hn21 hn22, one_mul, one_mul]
  have hT2 : ∑' p : X × X, prodPMF ρ₁ ρ₂ p
        * ((if rE τ₁ R p.1 = 0 then WresD α τ₂ R p.1 else 0) * WresD α τ₁ R p.2)
      = wZeroD α ρ₁ τ₁ τ₂ R * ∑' x, ρ₂ x * WresD α τ₁ R x :=
    tsum_mass_prod ρ₁ ρ₂ (fun x => if rE τ₁ R x = 0 then WresD α τ₂ R x else 0)
      (WresD α τ₁ R)
  have hT3 : ∑' p : X × X, prodPMF ρ₁ ρ₂ p
        * ((if rE τ₂ R p.1 = 0 then WresD α τ₁ R p.1 else 0) * WresD α τ₂ R p.2)
      = wZeroD α ρ₁ τ₂ τ₁ R * ∑' x, ρ₂ x * WresD α τ₂ R x :=
    tsum_mass_prod ρ₁ ρ₂ (fun x => if rE τ₂ R x = 0 then WresD α τ₁ R x else 0)
      (WresD α τ₂ R)
  have hT4 : ∑' p : X × X, prodPMF ρ₁ ρ₂ p
        * (WresD α τ₁ R p.1 * (if rE τ₁ R p.2 = 0 then WresD α τ₂ R p.2 else 0))
      = (∑' x, ρ₁ x * WresD α τ₁ R x) * wZeroD α ρ₂ τ₁ τ₂ R :=
    tsum_mass_prod ρ₁ ρ₂ (WresD α τ₁ R)
      (fun x => if rE τ₁ R x = 0 then WresD α τ₂ R x else 0)
  have hT5 : ∑' p : X × X, prodPMF ρ₁ ρ₂ p
        * (WresD α τ₂ R p.1 * (if rE τ₂ R p.2 = 0 then WresD α τ₁ R p.2 else 0))
      = (∑' x, ρ₁ x * WresD α τ₂ R x) * wZeroD α ρ₂ τ₂ τ₁ R :=
    tsum_mass_prod ρ₁ ρ₂ (WresD α τ₂ R)
      (fun x => if rE τ₂ R x = 0 then WresD α τ₁ R x else 0)
  calc PhiDres α (prodPMF ρ₁ ρ₂) (prodPMF τ₁ τ₂) (SquareRel R)
      ≤ ∑' p : X × X, (prodPMF ρ₁ ρ₂ p * (dpInd τ₁ τ₂ R p.1 * dpInd τ₁ τ₂ R p.2
            * phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) p))
        + prodPMF ρ₁ ρ₂ p
          * ((if rE τ₁ R p.1 = 0 then WresD α τ₂ R p.1 else 0) * WresD α τ₁ R p.2)
        + prodPMF ρ₁ ρ₂ p
          * ((if rE τ₂ R p.1 = 0 then WresD α τ₁ R p.1 else 0) * WresD α τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p
          * (WresD α τ₁ R p.1 * (if rE τ₁ R p.2 = 0 then WresD α τ₂ R p.2 else 0))
        + prodPMF ρ₁ ρ₂ p
          * (WresD α τ₂ R p.1 * (if rE τ₂ R p.2 = 0 then WresD α τ₁ R p.2 else 0))) := by
        rw [PhiDres]
        exact ENNReal.tsum_le_tsum hpt
    _ = _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add,
          hT2, hT3, hT4, hT5]

/-! ### The integral over the doubly-positive set -/

/-- **Rows and overlaps** (`thm:four-law-contraction`): the integral of the square
potential over `F₁ × F₂` is at most the four row products of `eq:four-law-rows` and the
two overlap integrals `∫ H₁¹ H₂² dτ₁`, `∫ H₁² H₂¹ dτ₂` (`fubini_swap_two_res`). -/
private lemma main_sum_le {X : Type} {α u : ℝ} (hα : 1 ≤ α) (hu0 : 0 < u) (hu1 : u < 1)
    (ρ₁ ρ₂ τ₁ τ₂ : PMF X) (R : X → X → Prop) :
    ∑' p : X × X, prodPMF ρ₁ ρ₂ p * (dpInd τ₁ τ₂ R p.1 * dpInd τ₁ τ₂ R p.2
        * phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) p))
      ≤ (∑' x, ρ₁ x * resPsi α τ₁ τ₂ R x)
          * (∑' x, ρ₂ x * chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x)
        + PhiDres α ρ₁ τ₁ R
          * (∑' x, ρ₂ x
              * weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x)
        + (∑' x, ρ₁ x * chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x)
          * (∑' x, ρ₂ x * resPsi α τ₁ τ₂ R x)
        + (∑' x, ρ₁ x
              * weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x)
          * PhiDres α ρ₂ τ₂ R
        + (∑' y, τ₁ y * (HresD α ρ₁ τ₁ R y * HresD α ρ₂ τ₂ R y))
        + (∑' y, τ₂ y * (HresD α ρ₁ τ₂ R y * HresD α ρ₂ τ₁ R y)) := by
  have hpt : ∀ p : X × X, prodPMF ρ₁ ρ₂ p * (dpInd τ₁ τ₂ R p.1 * dpInd τ₁ τ₂ R p.2
        * phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) p))
      ≤ prodPMF ρ₁ ρ₂ p * (resPsi α τ₁ τ₂ R p.1
            * chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p * (resPhi α τ₁ R p.1
            * weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p * (chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R p.1
            * resPsi α τ₁ τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p
          * (weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R p.1
            * resPhi α τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p
          * (cOverlap τ₁ R p.1 p.2 * (WresD α τ₁ R p.1 * WresD α τ₂ R p.2))
        + prodPMF ρ₁ ρ₂ p
          * (cOverlap τ₂ R p.1 p.2 * (WresD α τ₂ R p.1 * WresD α τ₁ R p.2)) := by
    rintro ⟨x₁, x₂⟩
    by_cases h1 : rE τ₁ R x₁ = 0 ∨ rE τ₂ R x₁ = 0
    · have h0 : dpInd τ₁ τ₂ R x₁ = 0 := by unfold dpInd; rw [ite_eq_left h1]
      simp only [h0, zero_mul, mul_zero]
      exact zero_le
    by_cases h2 : rE τ₁ R x₂ = 0 ∨ rE τ₂ R x₂ = 0
    · have h0 : dpInd τ₁ τ₂ R x₂ = 0 := by unfold dpInd; rw [ite_eq_left h2]
      simp only [h0, zero_mul, mul_zero]
      exact zero_le
    push Not at h1 h2
    obtain ⟨h11, h12⟩ := h1
    obtain ⟨h21, h22⟩ := h2
    have e1 : dpInd τ₁ τ₂ R x₁ = 1 := dpInd_eq_one h11 h12
    have e2 : dpInd τ₁ τ₂ R x₂ = 1 := dpInd_eq_one h21 h22
    have hmain := main_pt hα hu0 hu1 τ₁ τ₂ R x₁ x₂ h11 h12 h21 h22
    have f1 : resPsi α τ₁ τ₂ R x₁ = phiE α (q τ₁ R x₁ * q τ₂ R x₁) := by
      rw [resPsi, e1, one_mul]
    have f2 : resPsi α τ₁ τ₂ R x₂ = phiE α (q τ₁ R x₂ * q τ₂ R x₂) := by
      rw [resPsi, e2, one_mul]
    have g1 : chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x₁
        = 1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₁ + qE τ₂ R x₁) := by
      rw [chordFac, resQ, resQ, e1, one_mul, one_mul]
    have g2 : chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x₂
        = 1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₂ + qE τ₂ R x₂) := by
      rw [chordFac, resQ, resQ, e2, one_mul, one_mul]
    have p11 : resPhi α τ₁ R x₁ = phiE α (q τ₁ R x₁) := by rw [resPhi, ite_eq_right h11]
    have p12 : resPhi α τ₂ R x₁ = phiE α (q τ₂ R x₁) := by rw [resPhi, ite_eq_right h12]
    have p21 : resPhi α τ₁ R x₂ = phiE α (q τ₁ R x₂) := by rw [resPhi, ite_eq_right h21]
    have p22 : resPhi α τ₂ R x₂ = phiE α (q τ₂ R x₂) := by rw [resPhi, ite_eq_right h22]
    have w1 : weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x₁
        = (ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
          * (phiE α (q τ₁ R x₁) + phiE α (q τ₂ R x₁)) := by
      rw [weightFac, p11, p12]
    have w2 : weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x₂
        = (ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
          * (phiE α (q τ₁ R x₂) + phiE α (q τ₂ R x₂)) := by
      rw [weightFac, p21, p22]
    simp only [e1, e2, one_mul, f1, f2, g1, g2, p11, p22, w1, w2]
    refine le_trans (mul_le_mul_right hmain _) (le_of_eq ?_)
    ring
  have hov1 : ∑' p : X × X, prodPMF ρ₁ ρ₂ p
        * (cOverlap τ₁ R p.1 p.2 * (WresD α τ₁ R p.1 * WresD α τ₂ R p.2))
      = ∑' y, τ₁ y * (HresD α ρ₁ τ₁ R y * HresD α ρ₂ τ₂ R y) := by
    rw [← fubini_swap_two_res]
    exact tsum_congr fun p => by rw [prodPMF_apply]
  have hov2 : ∑' p : X × X, prodPMF ρ₁ ρ₂ p
        * (cOverlap τ₂ R p.1 p.2 * (WresD α τ₂ R p.1 * WresD α τ₁ R p.2))
      = ∑' y, τ₂ y * (HresD α ρ₁ τ₂ R y * HresD α ρ₂ τ₁ R y) := by
    rw [← fubini_swap_two_res]
    exact tsum_congr fun p => by rw [prodPMF_apply]
  refine le_trans (ENNReal.tsum_le_tsum hpt) (le_of_eq ?_)
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add,
    ENNReal.tsum_add, hov1, hov2,
    tsum_mass_prod ρ₁ ρ₂ (resPsi α τ₁ τ₂ R)
      (chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R),
    tsum_mass_prod ρ₁ ρ₂ (resPhi α τ₁ R)
      (weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R),
    tsum_mass_prod ρ₁ ρ₂ (chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R)
      (resPsi α τ₁ τ₂ R),
    tsum_mass_prod ρ₁ ρ₂
      (weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R)
      (resPhi α τ₂ R),
    ← PhiDres_eq_resPhi, ← PhiDres_eq_resPhi]

/-! ### The assembly -/

/-- **The four-law contraction** (`thm:four-law-contraction`). -/
theorem fourLaw_contraction {X : Type} {α β u L K L0 : ℝ} (hα : 1 ≤ α) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hu0 : 0 < u) (hu1 : u < 1)
    (hL : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α β q ≤ L)
    (hK : ∀ q, 0 ≤ q → q ≤ 1 → (q - β) * (1 - q) ^ α ≤ K)
    (hL0 : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α 0 q ≤ L0)
    (ρ₁ ρ₂ τ₁ τ₂ : PMF X) (R : X → X → Prop) (hsymm : ∀ a b, R a b → R b a)
    (Mb z e : ℝ≥0∞)
    (h11 : PhiDres α ρ₁ τ₁ R ≤ Mb) (h12 : PhiDres α ρ₁ τ₂ R ≤ Mb)
    (h21 : PhiDres α ρ₂ τ₁ R ≤ Mb) (h22 : PhiDres α ρ₂ τ₂ R ≤ Mb)
    (hr11 : PhiDres α τ₁ ρ₁ R ≤ Mb) (hr12 : PhiDres α τ₂ ρ₁ R ≤ Mb)
    (hr21 : PhiDres α τ₁ ρ₂ R ≤ Mb) (hr22 : PhiDres α τ₂ ρ₂ R ≤ Mb)
    (hz11 : zMass ρ₁ τ₁ R ≤ z) (hz12 : zMass ρ₁ τ₂ R ≤ z)
    (hz21 : zMass ρ₂ τ₁ R ≤ z) (hz22 : zMass ρ₂ τ₂ R ≤ z)
    (hzr11 : zMass τ₁ ρ₁ R ≤ z) (hzr12 : zMass τ₂ ρ₁ R ≤ z)
    (hzr21 : zMass τ₁ ρ₂ R ≤ z) (hzr22 : zMass τ₂ ρ₂ R ≤ z)
    (he11 : wZeroD α ρ₁ τ₁ τ₂ R ≤ e) (he12 : wZeroD α ρ₁ τ₂ τ₁ R ≤ e)
    (he21 : wZeroD α ρ₂ τ₁ τ₂ R ≤ e) (he22 : wZeroD α ρ₂ τ₂ τ₁ R ≤ e) :
    PhiDres α (prodPMF ρ₁ ρ₂) (prodPMF τ₁ τ₂) (SquareRel R)
      ≤ ENNReal.ofReal (2 * (L + K)) * Mb + ENNReal.ofReal (Cfun α L0 u) * Mb ^ 2
        + (ENNReal.ofReal (2 + 2 * β) + 4 * ENNReal.ofReal α * Mb) * z
        + 4 * (1 + ENNReal.ofReal α * Mb) * e := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hαpos : (0 : ℝ) < α := by linarith
  have hLn : 0 ≤ L := le_trans hβ0 (beta_le_of_hL hL)
  have hKn : 0 ≤ K := K_nonneg_of_hK hβ0 hβ1 hK
  have hL0n : 0 ≤ L0 := beta_le_of_hL hL0
  have hcn : 0 ≤ chordSlope α u := chordSlope_nonneg hα0 hu0 hu1
  have hun : (0 : ℝ) ≤ 1 / u := by positivity
  -- the coefficient identities
  have ea : ENNReal.ofReal (2 * (L + K)) = 2 * (ENNReal.ofReal L + ENNReal.ofReal K) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add hLn hKn, ENNReal.ofReal_ofNat]
  have eb : ENNReal.ofReal (Cfun α L0 u)
      = 4 * ENNReal.ofReal L0 * ENNReal.ofReal (chordSlope α u)
        + 4 * ENNReal.ofReal (1 / u) + 8 * ENNReal.ofReal α + 2 * ENNReal.ofReal α ^ 2 := by
    have hC : Cfun α L0 u = 4 * L0 * chordSlope α u + 4 * (1 / u) + 8 * α + 2 * α ^ 2 := by
      unfold Cfun chordSlope; ring
    have t1 : ENNReal.ofReal (4 * L0 * chordSlope α u)
        = 4 * ENNReal.ofReal L0 * ENNReal.ofReal (chordSlope α u) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat]
    have t2 : ENNReal.ofReal (4 * (1 / u)) = 4 * ENNReal.ofReal (1 / u) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    have t3 : ENNReal.ofReal (8 * α) = 8 * ENNReal.ofReal α := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    have t4 : ENNReal.ofReal (2 * α ^ 2) = 2 * ENNReal.ofReal α ^ 2 := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hα0, ENNReal.ofReal_ofNat]
    rw [hC, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), t1, t2, t3, t4]
  have ec : ENNReal.ofReal (2 + 2 * β) = 2 + 2 * ENNReal.ofReal β := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat]
  have hBG : ENNReal.ofReal β + ENNReal.ofReal (1 - β) = 1 := by
    rw [← ENNReal.ofReal_add hβ0 (by linarith), show β + (1 - β) = (1 : ℝ) from by ring,
      ENNReal.ofReal_one]
  have h42 : 4 * ENNReal.ofReal β + 2 * ENNReal.ofReal (1 - β) = 2 + 2 * ENNReal.ofReal β := by
    calc 4 * ENNReal.ofReal β + 2 * ENNReal.ofReal (1 - β)
        = 2 * ENNReal.ofReal β + 2 * (ENNReal.ofReal β + ENNReal.ofReal (1 - β)) := by ring
      _ = 2 + 2 * ENNReal.ofReal β := by rw [hBG]; ring
  -- the pieces
  have hsplit := PhiDres_square_split hαpos ρ₁ ρ₂ τ₁ τ₂ R
  have hmainsum := main_sum_le hα hu0 hu1 ρ₁ ρ₂ τ₁ τ₂ R
  have hI1 := (tsum_resPsi_le hα0 hβ0 hL ρ₁ τ₁ τ₂ R).trans
    (mul_le_mul_right (add_le_add h11 h12) _)
  have hI2 := (tsum_resPsi_le hα0 hβ0 hL ρ₂ τ₁ τ₂ R).trans
    (mul_le_mul_right (add_le_add h21 h22) _)
  have hI1M : (∑' x, ρ₁ x * resPsi α τ₁ τ₂ R x) ≤ ENNReal.ofReal L0 * Mb := by
    have h := (tsum_resPsi_le hα0 le_rfl hL0 ρ₁ τ₁ τ₂ R).trans
      (mul_le_mul_right (add_le_add h11 h12) _)
    rw [ENNReal.ofReal_zero, zero_mul, add_zero] at h
    have h2 : 2 * (∑' x, ρ₁ x * resPsi α τ₁ τ₂ R x) ≤ 2 * (ENNReal.ofReal L0 * Mb) :=
      h.trans (le_of_eq (by ring))
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2
  have hI2M : (∑' x, ρ₂ x * resPsi α τ₁ τ₂ R x) ≤ ENNReal.ofReal L0 * Mb := by
    have h := (tsum_resPsi_le hα0 le_rfl hL0 ρ₂ τ₁ τ₂ R).trans
      (mul_le_mul_right (add_le_add h21 h22) _)
    rw [ENNReal.ofReal_zero, zero_mul, add_zero] at h
    have h2 : 2 * (∑' x, ρ₂ x * resPsi α τ₁ τ₂ R x) ≤ 2 * (ENNReal.ofReal L0 * Mb) :=
      h.trans (le_of_eq (by ring))
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2
  have hQ11 : ∑' x, ρ₁ x * resQ τ₁ τ₂ τ₁ R x ≤ Mb :=
    (tsum_resQ_le_PhiDres hα0 ρ₁ τ₁ τ₂ τ₁ R fun _ h => dpInd_eq_zero_left h).trans h11
  have hQ12 : ∑' x, ρ₁ x * resQ τ₁ τ₂ τ₂ R x ≤ Mb :=
    (tsum_resQ_le_PhiDres hα0 ρ₁ τ₁ τ₂ τ₂ R fun _ h => dpInd_eq_zero_right h).trans h12
  have hQ21 : ∑' x, ρ₂ x * resQ τ₁ τ₂ τ₁ R x ≤ Mb :=
    (tsum_resQ_le_PhiDres hα0 ρ₂ τ₁ τ₂ τ₁ R fun _ h => dpInd_eq_zero_left h).trans h21
  have hQ22 : ∑' x, ρ₂ x * resQ τ₁ τ₂ τ₂ R x ≤ Mb :=
    (tsum_resQ_le_PhiDres hα0 ρ₂ τ₁ τ₂ τ₂ R fun _ h => dpInd_eq_zero_right h).trans h22
  have hq11 := tsum_resQ_le_one ρ₁ τ₁ τ₂ τ₁ R
  have hq12 := tsum_resQ_le_one ρ₁ τ₁ τ₂ τ₂ R
  have hq21 := tsum_resQ_le_one ρ₂ τ₁ τ₂ τ₁ R
  have hq22 := tsum_resQ_le_one ρ₂ τ₁ τ₂ τ₂ R
  have hC1 : ∑' x, ρ₁ x * chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x
      ≤ 1 + ENNReal.ofReal (chordSlope α u) * (Mb + Mb) := by
    rw [tsum_chordFac]
    exact add_le_add le_rfl (mul_le_mul_right (add_le_add hQ11 hQ12) _)
  have hC2 : ∑' x, ρ₂ x * chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x
      ≤ 1 + ENNReal.ofReal (chordSlope α u) * (Mb + Mb) := by
    rw [tsum_chordFac]
    exact add_le_add le_rfl (mul_le_mul_right (add_le_add hQ21 hQ22) _)
  have hW1 : ∑' x, ρ₁ x * weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x
      ≤ (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) * (Mb + Mb) := by
    rw [tsum_weightFac]
    exact mul_le_mul_right (add_le_add h11 h12) _
  have hW2 : ∑' x, ρ₂ x * weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x
      ≤ (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) * (Mb + Mb) := by
    rw [tsum_weightFac]
    exact mul_le_mul_right (add_le_add h21 h22) _
  have hO1 := overlap_two_le hα hβ0 hβ1 hK τ₁ ρ₁ ρ₂ τ₁ τ₂ R hsymm Mb z h11 h22 hr11 hr21
    hzr11 hzr21
  have hO2 := overlap_two_le hα hβ0 hβ1 hK τ₂ ρ₁ ρ₂ τ₂ τ₁ R hsymm Mb z h12 h21 hr12 hr22
    hzr12 hzr22
  have hF11 : failureD τ₁ ρ₁ R ≤ (∑' x, ρ₁ x * resQ τ₁ τ₂ τ₁ R x) + (z + z) := by
    rw [failureD_symm τ₁ ρ₁ R hsymm]
    exact (failureD_le_resQ ρ₁ τ₁ τ₂ τ₁ R).trans
      (by rw [add_assoc]; exact add_le_add le_rfl (add_le_add hz11 hz12))
  have hF21 : failureD τ₁ ρ₂ R ≤ (∑' x, ρ₂ x * resQ τ₁ τ₂ τ₁ R x) + (z + z) := by
    rw [failureD_symm τ₁ ρ₂ R hsymm]
    exact (failureD_le_resQ ρ₂ τ₁ τ₂ τ₁ R).trans
      (by rw [add_assoc]; exact add_le_add le_rfl (add_le_add hz21 hz22))
  have hF12 : failureD τ₂ ρ₁ R ≤ (∑' x, ρ₁ x * resQ τ₁ τ₂ τ₂ R x) + (z + z) := by
    rw [failureD_symm τ₂ ρ₁ R hsymm]
    exact (failureD_le_resQ ρ₁ τ₁ τ₂ τ₂ R).trans
      (by rw [add_assoc]; exact add_le_add le_rfl (add_le_add hz11 hz12))
  have hF22 : failureD τ₂ ρ₂ R ≤ (∑' x, ρ₂ x * resQ τ₁ τ₂ τ₂ R x) + (z + z) := by
    rw [failureD_symm τ₂ ρ₂ R hsymm]
    exact (failureD_le_resQ ρ₂ τ₁ τ₂ τ₂ R).trans
      (by rw [add_assoc]; exact add_le_add le_rfl (add_le_add hz21 hz22))
  have hZ1 : wZeroD α ρ₁ τ₁ τ₂ R * (∑' x, ρ₂ x * WresD α τ₁ R x)
      ≤ e * (1 + ENNReal.ofReal α * Mb) :=
    mul_le_mul' he11 ((tsum_WresD_le hα ρ₂ τ₁ R).trans
      (add_le_add le_rfl (mul_le_mul_right h21 _)))
  have hZ2 : wZeroD α ρ₁ τ₂ τ₁ R * (∑' x, ρ₂ x * WresD α τ₂ R x)
      ≤ e * (1 + ENNReal.ofReal α * Mb) :=
    mul_le_mul' he12 ((tsum_WresD_le hα ρ₂ τ₂ R).trans
      (add_le_add le_rfl (mul_le_mul_right h22 _)))
  have hZ3 : (∑' x, ρ₁ x * WresD α τ₁ R x) * wZeroD α ρ₂ τ₁ τ₂ R
      ≤ (1 + ENNReal.ofReal α * Mb) * e :=
    mul_le_mul' ((tsum_WresD_le hα ρ₁ τ₁ R).trans
      (add_le_add le_rfl (mul_le_mul_right h11 _))) he21
  have hZ4 : (∑' x, ρ₁ x * WresD α τ₂ R x) * wZeroD α ρ₂ τ₂ τ₁ R
      ≤ (1 + ENNReal.ofReal α * Mb) * e :=
    mul_le_mul' ((tsum_WresD_le hα ρ₁ τ₂ R).trans
      (add_le_add le_rfl (mul_le_mul_right h12 _))) he22
  -- abbreviations
  set A := ENNReal.ofReal α with hA
  set Lb := ENNReal.ofReal L with hLb
  set Kb := ENNReal.ofReal K with hKb
  set L0b := ENNReal.ofReal L0 with hL0b
  set cb := ENNReal.ofReal (chordSlope α u) with hcb
  set ub := ENNReal.ofReal (1 / u) with hub
  set Bb := ENNReal.ofReal β with hBb
  set Gb := ENNReal.ofReal (1 - β) with hGb
  set P := PhiDres α (prodPMF ρ₁ ρ₂) (prodPMF τ₁ τ₂) (SquareRel R) with hP
  set T := ∑' p : X × X, prodPMF ρ₁ ρ₂ p * (dpInd τ₁ τ₂ R p.1 * dpInd τ₁ τ₂ R p.2
    * phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) p)) with hT
  set I₁ := ∑' x, ρ₁ x * resPsi α τ₁ τ₂ R x with hI₁
  set I₂ := ∑' x, ρ₂ x * resPsi α τ₁ τ₂ R x with hI₂
  set C₁ := ∑' x, ρ₁ x * chordFac cb τ₁ τ₂ R x with hC₁
  set C₂ := ∑' x, ρ₂ x * chordFac cb τ₁ τ₂ R x with hC₂
  set V₁ := ∑' x, ρ₁ x * weightFac (ub + A) α τ₁ τ₂ R x with hV₁
  set V₂ := ∑' x, ρ₂ x * weightFac (ub + A) α τ₁ τ₂ R x with hV₂
  set Q11 := ∑' x, ρ₁ x * resQ τ₁ τ₂ τ₁ R x with hQ₁₁
  set Q12 := ∑' x, ρ₁ x * resQ τ₁ τ₂ τ₂ R x with hQ₁₂
  set Q21 := ∑' x, ρ₂ x * resQ τ₁ τ₂ τ₁ R x with hQ₂₁
  set Q22 := ∑' x, ρ₂ x * resQ τ₁ τ₂ τ₂ R x with hQ₂₂
  set O₁ := ∑' y, τ₁ y * (HresD α ρ₁ τ₁ R y * HresD α ρ₂ τ₂ R y) with hO₁
  set O₂ := ∑' y, τ₂ y * (HresD α ρ₁ τ₂ R y * HresD α ρ₂ τ₁ R y) with hO₂
  set Z₁ := wZeroD α ρ₁ τ₁ τ₂ R * (∑' x, ρ₂ x * WresD α τ₁ R x) with hZ₁
  set Z₂ := wZeroD α ρ₁ τ₂ τ₁ R * (∑' x, ρ₂ x * WresD α τ₂ R x) with hZ₂
  set Z₃ := (∑' x, ρ₁ x * WresD α τ₁ R x) * wZeroD α ρ₂ τ₁ τ₂ R with hZ₃
  set Z₄ := (∑' x, ρ₁ x * WresD α τ₂ R x) * wZeroD α ρ₂ τ₂ τ₁ R with hZ₄
  set F11 := failureD τ₁ ρ₁ R with hF₁₁
  set F21 := failureD τ₁ ρ₂ R with hF₂₁
  set F12 := failureD τ₂ ρ₁ R with hF₁₂
  set F22 := failureD τ₂ ρ₂ R with hF₂₂
  set P11 := PhiDres α ρ₁ τ₁ R with hP₁₁
  set P22 := PhiDres α ρ₂ τ₂ R with hP₂₂
  -- the cancellation of `Q`
  have hQfin : Bb * (Q11 + Q12 + Q21 + Q22) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top (show (1 : ℝ≥0∞) + 1 + 1 + 1 ≠ ⊤ from by simp)
        (add_le_add (add_le_add (add_le_add hq11 hq12) hq21) hq22))
  have key : 2 * P + Bb * (Q11 + Q12 + Q21 + Q22)
      ≤ 2 * (2 * (Lb + Kb) * Mb + (4 * L0b * cb + 4 * ub + 8 * A + 2 * A ^ 2) * Mb ^ 2
          + (4 * Bb + 2 * Gb + 4 * A * Mb) * z + 4 * (1 + A * Mb) * e)
        + Bb * (Q11 + Q12 + Q21 + Q22) := by
    calc 2 * P + Bb * (Q11 + Q12 + Q21 + Q22)
        ≤ 2 * (T + Z₁ + Z₂ + Z₃ + Z₄) + Bb * (Q11 + Q12 + Q21 + Q22) := by gcongr
      _ ≤ 2 * ((I₁ * C₂ + P11 * V₂ + C₁ * I₂ + V₁ * P22 + O₁ + O₂) + Z₁ + Z₂ + Z₃ + Z₄)
            + Bb * (Q11 + Q12 + Q21 + Q22) := by gcongr
      _ ≤ 2 * ((I₁ * (1 + cb * (Mb + Mb)) + Mb * ((ub + A) * (Mb + Mb))
              + (1 + cb * (Mb + Mb)) * I₂ + ((ub + A) * (Mb + Mb)) * Mb + O₁ + O₂)
            + e * (1 + A * Mb) + e * (1 + A * Mb) + (1 + A * Mb) * e + (1 + A * Mb) * e)
            + Bb * (Q11 + Q12 + Q21 + Q22) := by
          gcongr
      _ = (2 * I₁ + Bb * (Q11 + Q12)) + (2 * I₂ + Bb * (Q21 + Q22))
            + 4 * cb * Mb * (I₁ + I₂) + 8 * (ub + A) * Mb ^ 2 + 2 * O₁ + 2 * O₂
            + 8 * e * (1 + A * Mb) := by ring
      _ ≤ Lb * (Mb + Mb) + Lb * (Mb + Mb)
            + 4 * cb * Mb * (L0b * Mb + L0b * Mb) + 8 * (ub + A) * Mb ^ 2
            + (2 * Kb * Mb + Bb * (F11 + F21) + 2 * Gb * z + 4 * A * Mb ^ 2
              + 4 * A * Mb * z + 2 * A ^ 2 * Mb ^ 2)
            + (2 * Kb * Mb + Bb * (F12 + F22) + 2 * Gb * z + 4 * A * Mb ^ 2
              + 4 * A * Mb * z + 2 * A ^ 2 * Mb ^ 2)
            + 8 * e * (1 + A * Mb) := by
          gcongr
      _ ≤ Lb * (Mb + Mb) + Lb * (Mb + Mb)
            + 4 * cb * Mb * (L0b * Mb + L0b * Mb) + 8 * (ub + A) * Mb ^ 2
            + (2 * Kb * Mb + Bb * ((Q11 + (z + z)) + (Q21 + (z + z))) + 2 * Gb * z
              + 4 * A * Mb ^ 2 + 4 * A * Mb * z + 2 * A ^ 2 * Mb ^ 2)
            + (2 * Kb * Mb + Bb * ((Q12 + (z + z)) + (Q22 + (z + z))) + 2 * Gb * z
              + 4 * A * Mb ^ 2 + 4 * A * Mb * z + 2 * A ^ 2 * Mb ^ 2)
            + 8 * e * (1 + A * Mb) := by
          gcongr
      _ = _ := by ring
  have hcancel : 2 * P ≤ 2 * (2 * (Lb + Kb) * Mb
      + (4 * L0b * cb + 4 * ub + 8 * A + 2 * A ^ 2) * Mb ^ 2
      + (4 * Bb + 2 * Gb + 4 * A * Mb) * z + 4 * (1 + A * Mb) * e) :=
    ENNReal.le_of_add_le_add_right hQfin key
  have hfinal := (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hcancel
  rw [ea, eb, ec]
  rw [h42] at hfinal
  exact hfinal

end GraphMarkovMatching.Stopped
