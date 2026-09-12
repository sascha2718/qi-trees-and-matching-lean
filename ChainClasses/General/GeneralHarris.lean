import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import ChainClasses.Scalar.Harris

/-!
`sec:general-classes` of `matching_classes_general.tex`: the arithmetic of
`thm:harris-general`, the Harris-Sevastyanov transform at general bounded
support.

As for `thm:harris`, the structural half (the two-type embedding behind the
decomposition) is classical and cited; certified here is everything the rest of
the document consumes of the transform `eq:hs-transform`, over the offspring
law as a finite real sequence.

* `genFun`, `genDeriv`, `hasDerivAt_genFun`: the generating function
  `f(s) = ∑_j θ_j s^j` of a law supported on `{0,…,J}` and its derivative.
* `transform_expansion`: the binomial expansion
  `f(q+(1-q)s) = ∑_k θ̃⁰_k s^k` with
  `θ̃⁰_k = ∑_j θ_j C(j,k)(1-q)^k q^{j-k}` (`surviveCoeff`), the law of the
  number of surviving children before conditioning.
* `surviveCoeff_zero` (`= f(q) = q`, the extinction event that conditioning
  removes, so `f̃(0) = 0`), `tilde_one` (`θ̃₁ = f'(q)`), `tilde_sum` (the
  transform is a law).
* `reduced_sum`: the reduced law `eq:reduced-law` is a law on `{2,…,J}`;
  `geometric_law_tsum` is the geometric neck-length law of
  `it:harris-general-reduced`.
* `conjugate_sum_general`, `conjugate_mean_general`: the conjugate law `eq:conjugate-general`
  is a law (`∑_j θ_j q^{j-1} = f(q)/q = 1`) with mean `f'(q)`.
* `extinction_ge` (`q ≥ θ₀ > 0`) and `genDeriv_pos` (`f'(q) > 0`); the
  subcriticality `f'(q) < 1`
  is the structural input and enters the lemmas as a hypothesis.
* `tilde_hairy`, `reduced_hairy`: the specialisation to `J = 2` at
  `q = θ₀/θ₂`, recovering the two-value skeleton law `θ̃₁ = θ₁ + 2θ₀`,
  `θ̃₂ = θ₂ - θ₀` of `thm:harris` and the point mass of the reduced law at
  arity `2`.
-/

namespace ChainClasses

/-! ### The generating function and its derivative -/

/-- The generating function `f(s) = ∑_{j=0}^{J} θ_j s^j` of an offspring law
supported on `{0,…,J}`. -/
noncomputable def genFun (J : ℕ) (θ : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), θ j * s ^ j

/-- The derivative `f'(s) = ∑_{j=1}^{J} j θ_j s^{j-1}`; the `j = 0` term
vanishes through the cast. -/
noncomputable def genDeriv (J : ℕ) (θ : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), (j : ℝ) * θ j * s ^ (j - 1)

/-- `genDeriv` is the derivative of the generating function. -/
lemma hasDerivAt_genFun (J : ℕ) (θ : ℕ → ℝ) (s : ℝ) :
    HasDerivAt (genFun J θ) (genDeriv J θ s) s := by
  have h : ∀ j ∈ Finset.range (J + 1),
      HasDerivAt (fun x : ℝ => θ j * x ^ j) ((j : ℝ) * θ j * s ^ (j - 1)) s := by
    intro j _
    have hp := HasDerivAt.const_mul (θ j) (hasDerivAt_pow j s)
    have he : (j : ℝ) * θ j * s ^ (j - 1) = θ j * ((j : ℝ) * s ^ (j - 1)) := by ring
    rw [he]
    exact hp
  exact HasDerivAt.fun_sum (A := fun (j : ℕ) (x : ℝ) => θ j * x ^ j)
    (A' := fun j => (j : ℝ) * θ j * s ^ (j - 1)) h

/-! ### `eq:hs-transform`, the binomial expansion -/

/-- The coefficient of `s^k` in `f(q+(1-q)s)`: the law of the number of
surviving children before conditioning, each child surviving independently with
probability `1-q`. -/
noncomputable def surviveCoeff (J : ℕ) (θ : ℕ → ℝ) (q : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), θ j * (j.choose k : ℝ) * (1 - q) ^ k * q ^ (j - k)

/-- **`eq:hs-transform`, the expansion**: `f(q+(1-q)s) = ∑_k θ̃⁰_k s^k`, the
binomial theorem summed against the law. -/
theorem transform_expansion (J : ℕ) (θ : ℕ → ℝ) (q s : ℝ) :
    genFun J θ (q + (1 - q) * s)
      = ∑ k ∈ Finset.range (J + 1), surviveCoeff J θ q k * s ^ k := by
  have hterm : ∀ j ∈ Finset.range (J + 1),
      θ j * (q + (1 - q) * s) ^ j
        = ∑ k ∈ Finset.range (J + 1),
            θ j * (j.choose k : ℝ) * (1 - q) ^ k * q ^ (j - k) * s ^ k := by
    intro j hj
    have hjb : j + 1 ≤ J + 1 := by
      have := Finset.mem_range.mp hj; omega
    have hexp : (q + (1 - q) * s) ^ j
        = ∑ k ∈ Finset.range (j + 1),
            ((1 - q) * s) ^ k * q ^ (j - k) * (j.choose k : ℝ) := by
      rw [add_comm q ((1 - q) * s)]
      exact add_pow _ _ j
    have hext : ∑ k ∈ Finset.range (j + 1),
          ((1 - q) * s) ^ k * q ^ (j - k) * (j.choose k : ℝ)
        = ∑ k ∈ Finset.range (J + 1),
            ((1 - q) * s) ^ k * q ^ (j - k) * (j.choose k : ℝ) := by
      refine Finset.sum_subset (Finset.range_subset_range.mpr hjb) ?_
      intro k _ hknot
      have hk : ¬ k < j + 1 := fun hc => hknot (Finset.mem_range.mpr hc)
      have hjk : j < k := by omega
      rw [Nat.choose_eq_zero_of_lt hjk]
      simp
    rw [hexp, hext, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow]
    ring
  unfold genFun surviveCoeff
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]

/-- The constant coefficient is `f(q)`: the event that no child survives, which
the conditioning removes, so `f̃(0) = 0` once `f(q) = q`. -/
lemma surviveCoeff_zero (J : ℕ) (θ : ℕ → ℝ) (q : ℝ) :
    surviveCoeff J θ q 0 = genFun J θ q := by
  unfold surviveCoeff genFun
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.choose_zero_right]
  simp

/-- The linear coefficient is `(1-q)f'(q)`, by `C(j,1) = j`. -/
lemma surviveCoeff_one (J : ℕ) (θ : ℕ → ℝ) (q : ℝ) :
    surviveCoeff J θ q 1 = (1 - q) * genDeriv J θ q := by
  unfold surviveCoeff genDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.choose_one_right, pow_one]
  ring

/-- **Full support of the surviving-children count.** With `θ_J > 0` and
`0 < q < 1` every count `k ≤ J` has positive probability: the `j = J` term
`θ_J C(J,k)(1-q)^k q^{J-k}` of `surviveCoeff` is positive, and killing is what
supplies `q > 0`. -/
lemma surviveCoeff_pos (J : ℕ) (θ : ℕ → ℝ) {q : ℝ} (hnn : ∀ j, 0 ≤ θ j)
    (hJ : 0 < θ J) (hq0 : 0 < q) (hq1 : q < 1) {k : ℕ} (hk : k ≤ J) :
    0 < surviveCoeff J θ q k := by
  unfold surviveCoeff
  refine Finset.sum_pos' (fun j _ => ?_) ⟨J, Finset.mem_range.mpr (Nat.lt_succ_self J), ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg (hnn j) (Nat.cast_nonneg _))
      (pow_nonneg (by linarith) _)) (pow_nonneg hq0.le _)
  · have hc : (0 : ℝ) < (J.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
    exact mul_pos (mul_pos (mul_pos hJ hc) (pow_pos (by linarith) k)) (pow_pos hq0 _)

/-! ### The skeleton law `θ̃` -/

/-- **`eq:hs-transform`, the law**: `θ̃_k` is the `s^k` coefficient of `f̃`,
with the constant term removed by the conditioning. -/
noncomputable def tilde (J : ℕ) (θ : ℕ → ℝ) (q : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else surviveCoeff J θ q k / (1 - q)

/-- `f̃(0) = 0`: the skeleton never dies out. -/
lemma tilde_zero (J : ℕ) (θ : ℕ → ℝ) (q : ℝ) : tilde J θ q 0 = 0 := by
  simp [tilde]

/-- **`θ̃₁ = f'(q)`**: the neck probability is the mean of the conjugate
law. -/
lemma tilde_one (J : ℕ) (θ : ℕ → ℝ) {q : ℝ} (hq1 : q < 1) :
    tilde J θ q 1 = genDeriv J θ q := by
  have h : (1 : ℝ) - q ≠ 0 := by linarith
  rw [tilde, if_neg one_ne_zero, surviveCoeff_one]
  field_simp

/-- Every skeleton arity `1 ≤ k ≤ J` has positive probability in the hairy
regime. -/
lemma tilde_pos (J : ℕ) (θ : ℕ → ℝ) {q : ℝ} (hnn : ∀ j, 0 ≤ θ j) (hJ : 0 < θ J)
    (hq0 : 0 < q) (hq1 : q < 1) {k : ℕ} (hk1 : 1 ≤ k) (hkb : k ≤ J) :
    0 < tilde J θ q k := by
  rw [tilde, if_neg (by omega : k ≠ 0)]
  exact div_pos (surviveCoeff_pos J θ hnn hJ hq0 hq1 hkb) (by linarith)

/-- **The transform is a law**: `∑_{k=1}^{J} θ̃_k = 1`, from
`f(q+(1-q)) = f(1) = 1` and the removed constant term `f(q) = q`. -/
theorem tilde_sum (J : ℕ) (θ : ℕ → ℝ) {q : ℝ}
    (hsum : ∑ j ∈ Finset.range (J + 1), θ j = 1)
    (hq : genFun J θ q = q) (hq1 : q < 1) :
    ∑ k ∈ Finset.range (J + 1), tilde J θ q k = 1 := by
  have hne : (1 : ℝ) - q ≠ 0 := by linarith
  have h1 : ∑ k ∈ Finset.range (J + 1), surviveCoeff J θ q k = 1 := by
    have hx := transform_expansion J θ q 1
    simp only [mul_one, one_pow] at hx
    rw [show q + (1 - q) = 1 by ring] at hx
    rw [← hx]
    unfold genFun
    simpa using hsum
  have h2 := Finset.sum_range_succ' (surviveCoeff J θ q) J
  rw [h1, surviveCoeff_zero, hq] at h2
  have htail : ∑ i ∈ Finset.range J, surviveCoeff J θ q (i + 1) = 1 - q := by
    linarith
  rw [Finset.sum_range_succ' (tilde J θ q) J, tilde_zero, add_zero]
  have hnz : ∀ i ∈ Finset.range J,
      tilde J θ q (i + 1) = surviveCoeff J θ q (i + 1) / (1 - q) := by
    intro i _
    rw [tilde, if_neg (Nat.succ_ne_zero i)]
  rw [Finset.sum_congr rfl hnz, ← Finset.sum_div, htail, div_self hne]

/-! ### `eq:reduced-law`, the law of the reduced skeleton -/

/-- **`eq:reduced-law`**: the offspring law of the tree of splits,
`ν̃_k = θ̃_k/(1-θ̃₁)`. -/
noncomputable def reducedLaw (J : ℕ) (θ : ℕ → ℝ) (q : ℝ) (k : ℕ) : ℝ :=
  tilde J θ q k / (1 - tilde J θ q 1)

/-- **The reduced law has full support in the bushy regime**: `ν̃_k > 0` for
every `2 ≤ k ≤ J`, because killing is available at every vertex.  This is what
makes the branching semigroup trivial there
(`branching_semigroup_eq_top`), and with it the cross-law obstruction that the
chain regime carries. -/
theorem reducedLaw_pos (J : ℕ) (θ : ℕ → ℝ) {q : ℝ} (hnn : ∀ j, 0 ≤ θ j) (hJ : 0 < θ J)
    (hq0 : 0 < q) (hq1 : q < 1) (hsub : genDeriv J θ q < 1) {k : ℕ}
    (hk1 : 1 ≤ k) (hkb : k ≤ J) : 0 < reducedLaw J θ q k := by
  rw [reducedLaw]
  have h1 : tilde J θ q 1 = genDeriv J θ q := tilde_one J θ hq1
  exact div_pos (tilde_pos J θ hnn hJ hq0 hq1 hk1 hkb) (by rw [h1]; linarith)

/-- **`it:harris-general-reduced`, the law**: `ν̃` is a probability law on
`{2,…,J}`; the subcriticality `f'(q) < 1` is the structural input. -/
theorem reduced_sum (J : ℕ) (θ : ℕ → ℝ) {q : ℝ} (hJ : 2 ≤ J)
    (hsum : ∑ j ∈ Finset.range (J + 1), θ j = 1)
    (hq : genFun J θ q = q) (hq1 : q < 1)
    (hsub : genDeriv J θ q < 1) :
    ∑ k ∈ Finset.Icc 2 J, reducedLaw J θ q k = 1 := by
  have ht1 : tilde J θ q 1 = genDeriv J θ q := tilde_one J θ hq1
  have hne : (1 : ℝ) - tilde J θ q 1 ≠ 0 := by rw [ht1]; linarith
  have hsplit := Finset.sum_Ico_consecutive (tilde J θ q)
    (by omega : 0 ≤ 2) (by omega : 2 ≤ J + 1)
  have hfull : ∑ k ∈ Finset.Ico 0 (J + 1), tilde J θ q k = 1 := by
    rw [← Finset.range_eq_Ico]
    exact tilde_sum J θ hsum hq hq1
  have h01 : ∑ k ∈ Finset.Ico 0 2, tilde J θ q k = tilde J θ q 1 := by
    rw [← Finset.range_eq_Ico, Finset.sum_range_succ, Finset.sum_range_one,
      tilde_zero, zero_add]
  have htail : ∑ k ∈ Finset.Ico 2 (J + 1), tilde J θ q k = 1 - tilde J θ q 1 := by
    rw [hfull, h01] at hsplit
    linarith
  have hIccIco : Finset.Icc 2 J = Finset.Ico 2 (J + 1) := by
    ext x
    simp [Finset.mem_Icc, Finset.mem_Ico]
  unfold reducedLaw
  rw [hIccIco, ← Finset.sum_div, htail, div_self hne]

/-- The geometric neck-length law of `it:harris-general-reduced` is a
probability law: `∑_{r≥1} a^{r-1}(1-a) = 1` at ratio `a = θ̃₁`. -/
lemma geometric_law_tsum {a : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) :
    ∑' r : ℕ, a ^ r * (1 - a) = 1 := by
  rw [tsum_mul_right, tsum_geometric_of_lt_one h0 h1]
  exact inv_mul_cancel₀ (by linarith)

/-! ### `eq:conjugate-general`, the bush law -/

/-- **`eq:conjugate-general`**: the conjugate law `θ̂_j = θ_j q^{j-1}`, the
real quotient carrying the case `j = 0`. -/
noncomputable def conjugateLaw (θ : ℕ → ℝ) (q : ℝ) (j : ℕ) : ℝ := θ j * q ^ j / q

/-- **The conjugate law is a law**: `∑_j θ_j q^{j-1} = f(q)/q = 1`. -/
theorem conjugate_sum_general (J : ℕ) (θ : ℕ → ℝ) {q : ℝ}
    (hq : genFun J θ q = q) (hq0 : q ≠ 0) :
    ∑ j ∈ Finset.range (J + 1), conjugateLaw θ q j = 1 := by
  unfold conjugateLaw
  rw [← Finset.sum_div]
  have h : ∑ j ∈ Finset.range (J + 1), θ j * q ^ j = genFun J θ q := rfl
  rw [h, hq, div_self hq0]

/-- **The conjugate law has mean `f'(q)`**, so it is subcritical exactly when
the transform is in the chain regime. -/
theorem conjugate_mean_general (J : ℕ) (θ : ℕ → ℝ) {q : ℝ} (hq0 : q ≠ 0) :
    ∑ j ∈ Finset.range (J + 1), (j : ℝ) * conjugateLaw θ q j = genDeriv J θ q := by
  unfold conjugateLaw genDeriv
  refine Finset.sum_congr rfl fun j _ => ?_
  cases j with
  | zero => simp
  | succ n =>
      rw [show n + 1 - 1 = n by omega, pow_succ]
      field_simp

/-! ### Positivity: `q ≥ θ₀` and `f'(q) > 0` -/

/-- `θ₀ > 0` pushes the extinction probability up: `q = f(q) ≥ θ₀`. -/
lemma extinction_ge (J : ℕ) (θ : ℕ → ℝ) {q : ℝ} (hnn : ∀ j, 0 ≤ θ j)
    (hq : genFun J θ q = q) (hq0 : 0 ≤ q) : θ 0 ≤ q := by
  have h : θ 0 * q ^ 0 ≤ ∑ j ∈ Finset.range (J + 1), θ j * q ^ j :=
    Finset.single_le_sum (f := fun j => θ j * q ^ j)
      (fun j _ => mul_nonneg (hnn j) (pow_nonneg hq0 j))
      (Finset.mem_range.mpr (Nat.succ_pos J))
  simp only [pow_zero, mul_one] at h
  calc θ 0 ≤ genFun J θ q := h
    _ = q := hq

/-- `f'(q) > 0` for `q > 0`: with `θ₀ > 0` the extinction probability is
positive, so the skeleton law has `0 < θ̃₁`. -/
lemma genDeriv_pos (J : ℕ) (θ : ℕ → ℝ) {q : ℝ} (hnn : ∀ j, 0 ≤ θ j) (hq0 : 0 < q)
    (hex : ∃ j ∈ Finset.range (J + 1), 1 ≤ j ∧ 0 < θ j) :
    0 < genDeriv J θ q := by
  obtain ⟨j, hjmem, hj1, hjpos⟩ := hex
  unfold genDeriv
  refine Finset.sum_pos' (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg i) (hnn i)) (pow_nonneg hq0.le _))
    ⟨j, hjmem, ?_⟩
  have hj : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  exact mul_pos (mul_pos hj hjpos) (pow_pos hq0 _)

/-! ### The specialisation to `J = 2` -/

/-- The three-point law of `IsHairy` as a sequence. -/
def hairyLaw (θ₀ θ₁ θ₂ : ℝ) : ℕ → ℝ
  | 0 => θ₀
  | 1 => θ₁
  | 2 => θ₂
  | _ + 3 => 0

variable {θ₀ θ₁ θ₂ : ℝ}

lemma genDeriv_hairy (θ₀ θ₁ θ₂ s : ℝ) :
    genDeriv 2 (hairyLaw θ₀ θ₁ θ₂) s = θ₁ + 2 * θ₂ * s := by
  unfold genDeriv
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [hairyLaw]
  push_cast
  ring

/-- **The specialisation of `thm:harris-general` to `J = 2`**: at
`q = θ₀/θ₂` the transform is the two-value skeleton law of `thm:harris`,
`θ̃₁ = θ₁ + 2θ₀` and `θ̃₂ = θ₂ - θ₀`. -/
theorem tilde_hairy (h : IsHairy θ₀ θ₁ θ₂) :
    tilde 2 (hairyLaw θ₀ θ₁ θ₂) (θ₀ / θ₂) 1 = θ₁ + 2 * θ₀ ∧
    tilde 2 (hairyLaw θ₀ θ₁ θ₂) (θ₀ / θ₂) 2 = θ₂ - θ₀ := by
  obtain ⟨hq0, hq1⟩ := h.extinction_mem
  have h2 : θ₂ ≠ 0 := ne_of_gt h.pos₂
  constructor
  · rw [tilde_one _ _ hq1, genDeriv_hairy]
    exact h.neck_prob
  · have hs2 : surviveCoeff 2 (hairyLaw θ₀ θ₁ θ₂) (θ₀ / θ₂) 2
        = θ₂ * (1 - θ₀ / θ₂) ^ 2 := by
      unfold surviveCoeff
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [hairyLaw]
      norm_num
    rw [tilde, if_neg (by norm_num : (2 : ℕ) ≠ 0), hs2]
    have hne : (1 : ℝ) - θ₀ / θ₂ ≠ 0 := by linarith
    have hcalc : θ₂ * (1 - θ₀ / θ₂) ^ 2 / (1 - θ₀ / θ₂) = θ₂ * (1 - θ₀ / θ₂) := by
      rw [sq]
      field_simp
    rw [hcalc, h.survival_prob]
    field_simp

/-- The reduced law of the `J = 2` case is the point mass at arity `2`: the
tree of splits is the binary tree. -/
theorem reduced_hairy (h : IsHairy θ₀ θ₁ θ₂) :
    reducedLaw 2 (hairyLaw θ₀ θ₁ θ₂) (θ₀ / θ₂) 2 = 1 := by
  obtain ⟨ht1, ht2⟩ := tilde_hairy h
  rw [reducedLaw, ht2, ht1]
  have hone : (1 : ℝ) - (θ₁ + 2 * θ₀) = θ₂ - θ₀ := by
    have := h.sum; linarith
  rw [hone]
  exact div_self (by have := h.lt₂; linarith)

end ChainClasses
