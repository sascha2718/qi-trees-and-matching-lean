/-
Degree identities for the symmetrised square with two distinct column laws
(the exact-degrees step of `arbitrary_offspring_matching.tex` `thm:four-law`).

With `Y₀ ∼ ν₀`, `Y₁ ∼ ν₁` independent and rows `x₀, x₁` frozen:

* good degree:  `R + a₀a₁ = r₀⁰r₁¹ + r₀¹r₁⁰`   (inclusion-exclusion),
* bad degree:   `Q ≤ q₀⁰q₀¹ + q₁⁰q₁¹ + c₀ + c₁` (transversal + union),

where `aⱼ, cⱼ` are the both-compatible and neither-compatible masses of the
column law `νⱼ` and `rᵢʲ, qᵢʲ` the directed degrees of row `i` against `νⱼ`.
The proofs are the two-measure transcriptions of the one-law identities of
`GraphMarkovMatching.Support.Square`. `toReal` forms and the `ℝ≥0∞` two-product
arithmetic-mean bound close the file.
-/
import GraphMarkovMatching.Potential.DirectedProduct
import GraphMarkovMatching.Support.Contraction

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

/-! ### The good-degree identity -/

/-- **Inclusion-exclusion for two column laws**:
`R + a₀a₁ = r₀⁰r₁¹ + r₀¹r₁⁰`. -/
lemma rE_square_two (ν₀ ν₁ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    rE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)
        + aOverlap ν₀ R x₀ x₁ * aOverlap ν₁ R x₀ x₁
      = rE ν₀ R x₀ * rE ν₁ R x₁ + rE ν₁ R x₀ * rE ν₀ R x₁ := by
  have hSq : (∑' p : X × X, if SquareRel R (x₀, x₁) p then ν₀ p.1 * ν₁ p.2 else 0)
      = rE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁) := by
    rw [rE]; simp_rw [prodPMF_apply]
  have hInt : (∑' p : X × X,
        if (R x₀ p.1 ∧ R x₁ p.1) ∧ (R x₀ p.2 ∧ R x₁ p.2) then ν₀ p.1 * ν₁ p.2 else 0)
      = aOverlap ν₀ R x₀ x₁ * aOverlap ν₁ R x₀ x₁ := by
    rw [show aOverlap ν₀ R x₀ x₁ = ∑' y, if R x₀ y ∧ R x₁ y then ν₀ y else 0 from rfl,
      show aOverlap ν₁ R x₀ x₁ = ∑' y, if R x₀ y ∧ R x₁ y then ν₁ y else 0 from rfl]
    rw [tsum_congr fun p : X × X => show
        (if (R x₀ p.1 ∧ R x₁ p.1) ∧ (R x₀ p.2 ∧ R x₁ p.2) then ν₀ p.1 * ν₁ p.2 else 0)
          = (if R x₀ p.1 ∧ R x₁ p.1 then ν₀ p.1 else 0)
            * (if R x₀ p.2 ∧ R x₁ p.2 then ν₁ p.2 else 0)
        by by_cases h00 : R x₀ p.1 <;> by_cases h01 : R x₀ p.2 <;>
             by_cases h10 : R x₁ p.1 <;> by_cases h11 : R x₁ p.2 <;>
             simp [h00, h01, h10, h11]]
    exact tsum_prod_split (fun y => if R x₀ y ∧ R x₁ y then ν₀ y else 0)
      (fun y => if R x₀ y ∧ R x₁ y then ν₁ y else 0)
  have hA : (∑' p : X × X, if R x₀ p.1 ∧ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
      = rE ν₀ R x₀ * rE ν₁ R x₁ := by
    rw [tsum_congr fun p : X × X => show
        (if R x₀ p.1 ∧ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          = (if R x₀ p.1 then ν₀ p.1 else 0) * (if R x₁ p.2 then ν₁ p.2 else 0)
        by by_cases ha : R x₀ p.1 <;> by_cases hb : R x₁ p.2 <;> simp [ha, hb]]
    exact tsum_prod_split (fun y => if R x₀ y then ν₀ y else 0)
      (fun y => if R x₁ y then ν₁ y else 0)
  have hB : (∑' p : X × X, if R x₁ p.1 ∧ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
      = rE ν₁ R x₀ * rE ν₀ R x₁ := by
    rw [tsum_congr fun p : X × X => show
        (if R x₁ p.1 ∧ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          = (if R x₁ p.1 then ν₀ p.1 else 0) * (if R x₀ p.2 then ν₁ p.2 else 0)
        by by_cases ha : R x₁ p.1 <;> by_cases hb : R x₀ p.2 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => if R x₁ y then ν₀ y else 0)
      (fun y => if R x₀ y then ν₁ y else 0)]
    rw [show (∑' y, if R x₁ y then ν₀ y else 0) = rE ν₀ R x₁ from rfl,
      show (∑' y, if R x₀ y then ν₁ y else 0) = rE ν₁ R x₀ from rfl]
    ring
  have hadd : (∑' p : X × X, if SquareRel R (x₀, x₁) p then ν₀ p.1 * ν₁ p.2 else 0)
        + (∑' p : X × X,
            if (R x₀ p.1 ∧ R x₁ p.1) ∧ (R x₀ p.2 ∧ R x₁ p.2) then ν₀ p.1 * ν₁ p.2 else 0)
      = (∑' p : X × X, if R x₀ p.1 ∧ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
        + (∑' p : X × X, if R x₁ p.1 ∧ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0) := by
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun p => ?_
    by_cases h00 : R x₀ p.1 <;> by_cases h01 : R x₀ p.2 <;>
      by_cases h10 : R x₁ p.1 <;> by_cases h11 : R x₁ p.2 <;>
      simp [SquareRel, h00, h01, h10, h11]
  rw [hSq, hInt, hA, hB] at hadd
  exact hadd

/-! ### The bad-degree union bound -/

/-- **Transversal union bound for two column laws**:
`Q ≤ q₀⁰q₀¹ + q₁⁰q₁¹ + c₀ + c₁`. -/
lemma qE_square_two (ν₀ ν₁ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    qE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)
      ≤ qE ν₀ R x₀ * qE ν₁ R x₀ + qE ν₀ R x₁ * qE ν₁ R x₁
        + cOverlap ν₀ R x₀ x₁ + cOverlap ν₁ R x₀ x₁ := by
  have hq : qE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)
      = ∑' p : X × X, if SquareRel R (x₀, x₁) p then 0 else ν₀ p.1 * ν₁ p.2 := by
    rw [qE]; simp_rw [prodPMF_apply]
  have hpoint : ∀ p : X × X,
      (if SquareRel R (x₀, x₁) p then 0 else ν₀ p.1 * ν₁ p.2)
        ≤ (if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          + (if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          + (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then ν₀ p.1 * ν₁ p.2 else 0)
          + (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0) := by
    intro p
    by_cases hsq : SquareRel R (x₀, x₁) p
    · rw [if_pos hsq]; exact zero_le
    · rw [if_neg hsq]
      have hcov : (¬ R x₀ p.1 ∧ ¬ R x₀ p.2) ∨ (¬ R x₁ p.1 ∧ ¬ R x₁ p.2)
                ∨ (¬ R x₀ p.1 ∧ ¬ R x₁ p.1) ∨ (¬ R x₀ p.2 ∧ ¬ R x₁ p.2) := by
        by_contra hc
        exact hsq (by show (R x₀ p.1 ∧ R x₁ p.2) ∨ (R x₀ p.2 ∧ R x₁ p.1); tauto)
      set w := ν₀ p.1 * ν₁ p.2
      set t0 := (if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then w else 0)
      set t1 := (if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then w else 0)
      set t2 := (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then w else 0)
      set t3 := (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then w else 0)
      rcases hcov with h | h | h | h
      · calc w = t0 := (if_pos h).symm
          _ ≤ t0 + t1 := le_self_add
          _ ≤ t0 + t1 + t2 := le_self_add
          _ ≤ t0 + t1 + t2 + t3 := le_self_add
      · calc w = t1 := (if_pos h).symm
          _ ≤ t0 + t1 := le_add_self
          _ ≤ t0 + t1 + t2 := le_self_add
          _ ≤ t0 + t1 + t2 + t3 := le_self_add
      · calc w = t2 := (if_pos h).symm
          _ ≤ t0 + t1 + t2 := le_add_self
          _ ≤ t0 + t1 + t2 + t3 := le_self_add
      · calc w = t3 := (if_pos h).symm
          _ ≤ t0 + t1 + t2 + t3 := le_add_self
  have h0 : (∑' p : X × X, if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
      = qE ν₀ R x₀ * qE ν₁ R x₀ := by
    rw [tsum_congr fun p : X × X => show
        (if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          = (if ¬ R x₀ p.1 then ν₀ p.1 else 0) * (if ¬ R x₀ p.2 then ν₁ p.2 else 0)
        by by_cases ha : R x₀ p.1 <;> by_cases hb : R x₀ p.2 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => if ¬ R x₀ y then ν₀ y else 0)
      (fun y => if ¬ R x₀ y then ν₁ y else 0)]
    congr 1 <;> · rw [qE]; exact tsum_congr fun y => by by_cases h : R x₀ y <;> simp [h]
  have h1 : (∑' p : X × X, if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
      = qE ν₀ R x₁ * qE ν₁ R x₁ := by
    rw [tsum_congr fun p : X × X => show
        (if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          = (if ¬ R x₁ p.1 then ν₀ p.1 else 0) * (if ¬ R x₁ p.2 then ν₁ p.2 else 0)
        by by_cases ha : R x₁ p.1 <;> by_cases hb : R x₁ p.2 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => if ¬ R x₁ y then ν₀ y else 0)
      (fun y => if ¬ R x₁ y then ν₁ y else 0)]
    congr 1 <;> · rw [qE]; exact tsum_congr fun y => by by_cases h : R x₁ y <;> simp [h]
  have h2 : (∑' p : X × X, if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then ν₀ p.1 * ν₁ p.2 else 0)
      = cOverlap ν₀ R x₀ x₁ := by
    rw [show cOverlap ν₀ R x₀ x₁ = ∑' y, if ¬ R x₀ y ∧ ¬ R x₁ y then ν₀ y else 0 from rfl]
    rw [tsum_congr fun p : X × X => show
        (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then ν₀ p.1 * ν₁ p.2 else 0)
          = (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then ν₀ p.1 else 0) * ν₁ p.2
        by by_cases ha : R x₀ p.1 <;> by_cases hb : R x₁ p.1 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => if ¬ R x₀ y ∧ ¬ R x₁ y then ν₀ y else 0) (fun y => ν₁ y),
      PMF.tsum_coe, mul_one]
  have h3 : (∑' p : X × X, if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
      = cOverlap ν₁ R x₀ x₁ := by
    rw [show cOverlap ν₁ R x₀ x₁ = ∑' y, if ¬ R x₀ y ∧ ¬ R x₁ y then ν₁ y else 0 from rfl]
    rw [tsum_congr fun p : X × X => show
        (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          = ν₀ p.1 * (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then ν₁ p.2 else 0)
        by by_cases ha : R x₀ p.2 <;> by_cases hb : R x₁ p.2 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => ν₀ y) (fun y => if ¬ R x₀ y ∧ ¬ R x₁ y then ν₁ y else 0),
      PMF.tsum_coe, one_mul]
  rw [hq]
  calc ∑' p : X × X, (if SquareRel R (x₀, x₁) p then 0 else ν₀ p.1 * ν₁ p.2)
      ≤ ∑' p : X × X,
          ((if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
            + (if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
            + (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then ν₀ p.1 * ν₁ p.2 else 0)
            + (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)) :=
        ENNReal.tsum_le_tsum hpoint
    _ = (∑' p : X × X, if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          + (∑' p : X × X, if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          + (∑' p : X × X, if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then ν₀ p.1 * ν₁ p.2 else 0)
          + (∑' p : X × X, if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    _ = qE ν₀ R x₀ * qE ν₁ R x₀ + qE ν₀ R x₁ * qE ν₁ R x₁
          + cOverlap ν₀ R x₀ x₁ + cOverlap ν₁ R x₀ x₁ := by
        rw [h0, h1, h2, h3]

/-! ### `toReal` forms -/

/-- Good-degree identity in `ℝ`. -/
lemma rE_square_two_toReal (ν₀ ν₁ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    (rE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)).toReal
        + (aOverlap ν₀ R x₀ x₁).toReal * (aOverlap ν₁ R x₀ x₁).toReal
      = (rE ν₀ R x₀).toReal * (rE ν₁ R x₁).toReal
        + (rE ν₁ R x₀).toReal * (rE ν₀ R x₁).toReal := by
  have h := rE_square_two ν₀ ν₁ R x₀ x₁
  apply_fun ENNReal.toReal at h
  rw [ENNReal.toReal_add rE_ne_top
      (ENNReal.mul_ne_top (aOverlap_ne_top ν₀ R x₀ x₁) (aOverlap_ne_top ν₁ R x₀ x₁)),
    ENNReal.toReal_add (ENNReal.mul_ne_top rE_ne_top rE_ne_top)
      (ENNReal.mul_ne_top rE_ne_top rE_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul] at h
  exact h

/-- Bad-degree union bound in `ℝ`. -/
lemma qE_square_two_toReal (ν₀ ν₁ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    (qE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)).toReal
      ≤ (qE ν₀ R x₀).toReal * (qE ν₁ R x₀).toReal
        + (qE ν₀ R x₁).toReal * (qE ν₁ R x₁).toReal
        + (cOverlap ν₀ R x₀ x₁).toReal + (cOverlap ν₁ R x₀ x₁).toReal := by
  have h := qE_square_two ν₀ ν₁ R x₀ x₁
  have hq2 : ∀ z : X, qE ν₀ R z * qE ν₁ R z ≠ ⊤ :=
    fun z => ENNReal.mul_ne_top qE_ne_top qE_ne_top
  have hRHS : qE ν₀ R x₀ * qE ν₁ R x₀ + qE ν₀ R x₁ * qE ν₁ R x₁
        + cOverlap ν₀ R x₀ x₁ + cOverlap ν₁ R x₀ x₁ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hq2 x₀, hq2 x₁⟩, cOverlap_ne_top ν₀ R x₀ x₁⟩,
      cOverlap_ne_top ν₁ R x₀ x₁⟩
  have hmono := ENNReal.toReal_mono hRHS h
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨hq2 x₀, hq2 x₁⟩, cOverlap_ne_top ν₀ R x₀ x₁⟩)
      (cOverlap_ne_top ν₁ R x₀ x₁),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hq2 x₀, hq2 x₁⟩)
      (cOverlap_ne_top ν₀ R x₀ x₁),
    ENNReal.toReal_add (hq2 x₀) (hq2 x₁),
    ENNReal.toReal_mul, ENNReal.toReal_mul] at hmono
  exact hmono

/-! ### Two-product arithmetic mean in `ℝ≥0∞` -/

/-- `2ab ≤ a² + b²` in `ℝ≥0∞`. -/
lemma ennreal_two_mul_le_add_sq (a b : ℝ≥0∞) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  by_cases ha : a = ⊤
  · by_cases hb : b = 0
    · simp [ha, hb]
    · have : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
      rw [ha]
      calc 2 * (⊤ * b) ≤ ⊤ := le_top
        _ ≤ ⊤ ^ 2 + b ^ 2 := by simp
  · by_cases hb : b = ⊤
    · by_cases ha0 : a = 0
      · simp [hb, ha0]
      · rw [hb]
        calc 2 * (a * ⊤) ≤ ⊤ := le_top
          _ ≤ a ^ 2 + ⊤ ^ 2 := by simp
    · have h := two_mul_le_add_sq a.toReal b.toReal
      have h2 : (2 : ℝ) * (a.toReal * b.toReal) ≤ a.toReal ^ 2 + b.toReal ^ 2 := by
        nlinarith [sq_nonneg (a.toReal - b.toReal)]
      calc 2 * (a * b)
          = ENNReal.ofReal (2 * (a.toReal * b.toReal)) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb, ENNReal.ofReal_ofNat]
        _ ≤ ENNReal.ofReal (a.toReal ^ 2 + b.toReal ^ 2) := ENNReal.ofReal_le_ofReal h2
        _ = a ^ 2 + b ^ 2 := by
            rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
              ENNReal.ofReal_pow ENNReal.toReal_nonneg,
              ENNReal.ofReal_pow ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb]

end GraphMarkovMatching
