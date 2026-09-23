/-
The one-site estimates used by the chain and bushy applications: the chain-law calculation
behind `thm:eta-bound`, the abstract shape-law calculation behind `thm:shape-eta`, and the
probability-one passage used in `thm:cross-law` and `thm:hairy`.

* **Chain classes** (`thm:eta-bound`): the chain law `p_j = a^{D^j-1} - a^{D^{j+1}-1}` on
  `ℕ` with the path relation (`chainLaw`, `pathRelNat`); the explicit estimates
  `p_{j-1} ≥ a^{D^{j-1}-1}/2` (`chainMass_ge_half`),
  `p_j / p_{j-1}^α ≤ 2^α a^{α-1} a^{(D-α)D^{j-1}}` (`chainLaw_ratio_le`), the summed
  bound by `2^α a^{α-1} a^{D-α}/(1-a^{D-α})` (`chainLaw_tail_sum_le`), the potential bound
  `eta_chainLaw_le`, and the limits `p_0 → 1`, `η_{P,α} → 0` as `D → ∞`
  (`chainLaw_zero_tendsto`, `eta_chainLaw_tendsto`).
* **Bushy trees**: the abstract form of the shape estimates, a law on a label set with a
  size function `N`, a distinguished label `v₀` carrying every label of size `≤ D²`, an
  exponential tail `μ{N > n} ≤ A₀ e^{-c₀ n}` and compatible mass
  `b(v) ≥ exp(-C₀(N D^{-1/2} + 1))` off `v₀`; the `v₀` contribution `(1-μ(v₀))/μ(v₀)^α`
  (`bushy_v0_term_le`), the other labels' contribution
  `e^{αC₀} 𝔼[𝟙{N > D²} e^{αC₀ N D^{-1/2}}]` (`bushy_other_terms_le`), the summed bound by a
  fixed multiple of `e^{-c₀ D²/2}` (`bushy_moment_le`, `bushy_eta_le`), the mass bound
  `1 - μ(v₀) ≤ A₀ e^{-c₀ D²}` (`bushy_v0_mass_le`), and the limits `μ_D(v₀) → 1`,
  `η_{G_D,α}(μ_D) → 0` (`bushy_v0_tendsto`, `bushy_eta_tendsto_ennreal`,
  `bushy_eta_tendsto`).
* **The probability-one conclusion** used in `thm:cross-law` and `thm:hairy`: an event
  containing events of
  probability at least `1 - ε_D` with `ε_D → 0` has probability one (`prob_eq_one_of_le`,
  `prob_eq_one_of_eventually_le`), with no independence, nesting or coupling between the
  scales.
-/
import GraphMarkovMatching.Stopped.Constants
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support Filter
open scoped ENNReal Classical

/-! ### Chain classes (`thm:eta-bound`) -/

/-- The masses `p_j = a^{D^j-1} - a^{D^{j+1}-1}` of the chain law (`thm:eta-bound`). -/
noncomputable def chainMass (a : ℝ) (D j : ℕ) : ℝ := a ^ (D ^ j - 1) - a ^ (D ^ (j + 1) - 1)

lemma chainMass_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {D : ℕ} (hD : 1 ≤ D) (j : ℕ) :
    0 ≤ chainMass a D j := by
  rw [chainMass, sub_nonneg]
  apply pow_le_pow_of_le_one ha0 ha1
  have : D ^ j ≤ D ^ (j + 1) := Nat.pow_le_pow_right hD (Nat.le_succ j)
  omega

lemma chainMass_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) (j : ℕ) :
    0 < chainMass a D j := by
  rw [chainMass, sub_pos]
  apply pow_lt_pow_right_of_lt_one₀ ha0 ha1
  have h1 : D ^ j < D ^ (j + 1) := Nat.pow_lt_pow_right (by omega : 1 < D) (Nat.lt_succ_self j)
  have h2 : 1 ≤ D ^ j := Nat.one_le_pow _ _ (by omega)
  omega

/-- `p_0 = 1 - a^{D-1}`. -/
lemma chainMass_zero (a : ℝ) (D : ℕ) : chainMass a D 0 = 1 - a ^ (D - 1) := by
  simp [chainMass]

/-- `D^{i+1} - 1 = (D^i - 1) + D^i (D-1)` in `ℕ`. -/
private lemma pow_succ_sub_one (D i : ℕ) (hD : 1 ≤ D) :
    D ^ (i + 1) - 1 = (D ^ i - 1) + D ^ i * (D - 1) := by
  have h1 : D ^ i * (D - 1) = D ^ i * D - D ^ i := Nat.mul_sub_one _ _
  have h2 : D ^ i ≤ D ^ i * D := Nat.le_mul_of_pos_right _ hD
  have h3 : 1 ≤ D ^ i := Nat.one_le_pow _ _ hD
  rw [pow_succ, h1]
  omega

/-- The masses telescope to `1` (`thm:eta-bound`): `∑_j p_j = a^{D^0-1} = 1`. -/
lemma hasSum_chainMass {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) :
    HasSum (chainMass a D) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => chainMass_nonneg ha0.le ha1.le (by omega) j)]
  have hg : Tendsto (fun n : ℕ => a ^ (D ^ n - 1)) atTop (nhds 0) := by
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).comp ?_
    refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    have := @Nat.lt_pow_self n D (by omega)
    show n ≤ D ^ n - 1
    omega
  have h := hg.const_sub 1
  rw [sub_zero] at h
  refine h.congr fun n => ?_
  show 1 - a ^ (D ^ n - 1) = ∑ i ∈ Finset.range n, (a ^ (D ^ i - 1) - a ^ (D ^ (i + 1) - 1))
  rw [Finset.sum_range_sub' (fun i => a ^ (D ^ i - 1)) n]
  simp

/-- The chain law `p_j = a^{D^j-1} - a^{D^{j+1}-1}` on `ℕ`, `0 < a < 1`, `D ≥ 2`
(`thm:eta-bound`, the common law `μ_* = p^{(D)}`). -/
noncomputable def chainLaw (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (D : ℕ) (hD : 2 ≤ D) : PMF ℕ :=
  ⟨fun j => ENNReal.ofReal (chainMass a D j), by
    have h := hasSum_chainMass ha0 ha1 hD
    have h1 : ∑' j, ENNReal.ofReal (chainMass a D j) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => chainMass_nonneg ha0.le ha1.le (by omega) j)
        h.summable, h.tsum_eq, ENNReal.ofReal_one]
    rw [← h1]
    exact ENNReal.summable.hasSum⟩

lemma chainLaw_apply (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (D : ℕ) (hD : 2 ≤ D) (j : ℕ) :
    chainLaw a ha0 ha1 D hD j = ENNReal.ofReal (chainMass a D j) := rfl

/-- The total-in-`D` chain law: `chainLaw` at `max D 2`. -/
noncomputable def chainLaw' (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (D : ℕ) : PMF ℕ :=
  chainLaw a ha0 ha1 (max D 2) (le_max_right D 2)

lemma chainLaw'_apply (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (D j : ℕ) :
    chainLaw' a ha0 ha1 D j = ENNReal.ofReal (chainMass a (max D 2) j) := rfl

/-- The path relation on `ℕ`: equality or adjacency (`thm:eta-bound`). -/
def pathRelNat (i j : ℕ) : Prop := i = j ∨ i = j + 1 ∨ j = i + 1

theorem pathRelNat_refl (i : ℕ) : pathRelNat i i := Or.inl rfl

theorem pathRelNat_symm {i j : ℕ} (h : pathRelNat i j) : pathRelNat j i := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

lemma pathRelNat_succ_left (j : ℕ) : pathRelNat (j + 1) j := Or.inr (Or.inl rfl)

lemma pathRelNat_zero_one : pathRelNat 0 1 := Or.inr (Or.inr rfl)

/-- `p_{j-1} ≥ a^{D^{j-1}-1}/2` once `a^{D-1} ≤ 1/2` (`thm:eta-bound`), written at the
index `i = j - 1`. -/
theorem chainMass_ge_half {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D)
    (hhalf : a ^ (D - 1) ≤ 1 / 2) (i : ℕ) :
    a ^ (D ^ i - 1) / 2 ≤ chainMass a D i := by
  rw [chainMass, pow_succ_sub_one D i (by omega), pow_add]
  have ht : a ^ (D ^ i * (D - 1)) ≤ 1 / 2 :=
    (pow_le_pow_of_le_one ha0.le ha1.le
      (Nat.le_mul_of_pos_left _ (pow_pos (by omega) i))).trans hhalf
  have hg : 0 < a ^ (D ^ i - 1) := pow_pos ha0 _
  nlinarith

/-- The exact form of the ratio `a^{D^{i+1}-1} / (a^{D^i-1}/2)^α`. -/
private lemma chain_ratio_eq {a : ℝ} (ha0 : 0 < a) {D : ℕ} (hD : 1 ≤ D) (i : ℕ) (α : ℝ) :
    a ^ (D ^ (i + 1) - 1) / (a ^ (D ^ i - 1) / 2) ^ α
      = 2 ^ α * a ^ (α - 1) * a ^ (((D : ℝ) - α) * (D : ℝ) ^ i) := by
  have h1 : (1 : ℕ) ≤ D ^ i := Nat.one_le_pow _ _ hD
  have h2 : (1 : ℕ) ≤ D ^ (i + 1) := Nat.one_le_pow _ _ hD
  have hg : 0 < a ^ (D ^ i - 1) := pow_pos ha0 _
  have key : a ^ (D ^ (i + 1) - 1) / (a ^ (D ^ i - 1)) ^ α
      = a ^ (α - 1) * a ^ (((D : ℝ) - α) * (D : ℝ) ^ i) := by
    rw [← Real.rpow_add ha0, ← Real.rpow_natCast_mul ha0.le,
      ← Real.rpow_natCast a (D ^ (i + 1) - 1), ← Real.rpow_sub ha0]
    congr 1
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    ring
  rw [Real.div_rpow hg.le (by norm_num), div_div_eq_mul_div, mul_comm, mul_div_assoc, key,
    mul_assoc]

/-- **The ratio estimate** of `thm:eta-bound`: once `a^{D-1} ≤ 1/2`,
`p_j / p_{j-1}^α ≤ 2^α a^{α-1} a^{(D-α)D^{j-1}}` for every `j ≥ 1`, written at `i = j-1`. -/
theorem chainLaw_ratio_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D)
    (hhalf : a ^ (D - 1) ≤ 1 / 2) {α : ℝ} (hα : 0 ≤ α) (i : ℕ) :
    chainMass a D (i + 1) / chainMass a D i ^ α
      ≤ 2 ^ α * a ^ (α - 1) * a ^ (((D : ℝ) - α) * (D : ℝ) ^ i) := by
  rw [← chain_ratio_eq ha0 (by omega) i α]
  have hg : 0 < a ^ (D ^ i - 1) / 2 := by positivity
  refine div_le_div₀ (pow_pos ha0 _).le ?_ (Real.rpow_pos_of_pos hg α)
    (Real.rpow_le_rpow hg.le (chainMass_ge_half ha0 ha1 hD hhalf i) hα)
  rw [chainMass]
  have := pow_pos ha0 (D ^ (i + 1 + 1) - 1)
  linarith

/-- `a^{(D-α)D^i} ≤ (a^{D-α})^{i+1}` for `D > α`, from `D^i ≥ i + 1` (`thm:eta-bound`). -/
private lemma rpow_exponent_pow_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D)
    {α : ℝ} (hαD : α < D) (i : ℕ) :
    a ^ (((D : ℝ) - α) * (D : ℝ) ^ i) ≤ (a ^ ((D : ℝ) - α)) ^ (i + 1) := by
  have hDi : ((i : ℝ) + 1) ≤ (D : ℝ) ^ i := by
    have := @Nat.lt_pow_self i D (by omega)
    exact_mod_cast this
  have hexp : ((D : ℝ) - α) * ((i : ℝ) + 1) ≤ ((D : ℝ) - α) * (D : ℝ) ^ i :=
    mul_le_mul_of_nonneg_left hDi (by linarith)
  calc a ^ (((D : ℝ) - α) * (D : ℝ) ^ i)
      ≤ a ^ (((D : ℝ) - α) * ((i : ℝ) + 1)) :=
        Real.rpow_le_rpow_of_exponent_ge ha0 ha1.le hexp
    _ = (a ^ ((D : ℝ) - α)) ^ (i + 1) := by
        rw [← Nat.cast_succ, Real.rpow_mul_natCast ha0.le]

/-- **The summed ratio bound** of `thm:eta-bound`: for `D > α` and `a^{D-1} ≤ 1/2`,
`∑_{j ≥ 1} p_j / p_{j-1}^α ≤ 2^α a^{α-1} a^{D-α}/(1 - a^{D-α})`. -/
theorem chainLaw_tail_sum_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D)
    (hhalf : a ^ (D - 1) ≤ 1 / 2) {α : ℝ} (hα : 0 ≤ α) (hαD : α < D) :
    ∑' i, chainMass a D (i + 1) / chainMass a D i ^ α
      ≤ 2 ^ α * a ^ (α - 1) * (a ^ ((D : ℝ) - α) / (1 - a ^ ((D : ℝ) - α))) := by
  set x := a ^ ((D : ℝ) - α) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos ha0 _
  have hx1 : x < 1 := Real.rpow_lt_one ha0.le ha1 (by linarith)
  set C := (2 : ℝ) ^ α * a ^ (α - 1) with hC
  have hC0 : 0 ≤ C := by positivity
  have hterm : ∀ i, chainMass a D (i + 1) / chainMass a D i ^ α ≤ C * x * x ^ i := by
    intro i
    calc chainMass a D (i + 1) / chainMass a D i ^ α
        ≤ C * a ^ (((D : ℝ) - α) * (D : ℝ) ^ i) := chainLaw_ratio_le ha0 ha1 hD hhalf hα i
      _ ≤ C * x ^ (i + 1) := by
          gcongr
          exact rpow_exponent_pow_le ha0 ha1 hD hαD i
      _ = C * x * x ^ i := by rw [pow_succ']; ring
  have hsum : Summable fun i : ℕ => C * x * x ^ i :=
    (summable_geometric_of_lt_one hx0.le hx1).mul_left _
  calc ∑' i, chainMass a D (i + 1) / chainMass a D i ^ α
      ≤ ∑' i, C * x * x ^ i :=
        Summable.tsum_le_tsum hterm
          (Summable.of_nonneg_of_le
            (fun i => div_nonneg (chainMass_nonneg ha0.le ha1.le (by omega) _)
              (Real.rpow_nonneg (chainMass_nonneg ha0.le ha1.le (by omega) _) _)) hterm hsum)
          hsum
    _ = C * (x / (1 - x)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hx0.le hx1, div_eq_mul_inv, mul_assoc]

/-- The bad degree at `0` is at most `a^{D^2-1}` (`thm:eta-bound`: the incompatible mass
at `0` is `a^{D^2-1}`), since `0` is compatible with `0` and `1`. -/
theorem chainLaw_q_zero_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D) :
    q (chainLaw a ha0 ha1 D hD) pathRelNat 0 ≤ a ^ (D ^ 2 - 1) := by
  set μ := chainLaw a ha0 ha1 D hD with hμ
  have hsum : μ 0 + μ 1 ≤ rE μ pathRelNat 0 := by
    have h := ENNReal.sum_le_tsum (f := fun y => if pathRelNat 0 y then μ y else 0) {0, 1}
    rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)] at h
    simp only [ite_eq_left (pathRelNat_refl 0), ite_eq_left pathRelNat_zero_one] at h
    exact h
  have hreal : (μ 0 + μ 1).toReal = 1 - a ^ (D ^ 2 - 1) := by
    rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _), hμ, chainLaw_apply,
      chainLaw_apply, ENNReal.toReal_ofReal (chainMass_nonneg ha0.le ha1.le (by omega) _),
      ENNReal.toReal_ofReal (chainMass_nonneg ha0.le ha1.le (by omega) _)]
    simp only [chainMass, pow_zero, Nat.sub_self, zero_add, pow_one]
    ring
  have := ENNReal.toReal_mono rE_ne_top hsum
  rw [toReal_rE_eq, hreal] at this
  linarith

/-- **The potential bound of the chain law** (`thm:eta-bound`): for `D > α` and
`a^{D-1} ≤ 1/2`,
`η_{P,α}(μ_*) ≤ φ_α(a^{D^2-1}) + 2^α a^{α-1} a^{D-α}/(1 - a^{D-α})`. -/
theorem eta_chainLaw_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : ℕ} (hD : 2 ≤ D)
    {α : ℝ} (hα : 1 ≤ α) (hhalf : a ^ (D - 1) ≤ 1 / 2) (hαD : α < D) :
    PhiD α (chainLaw a ha0 ha1 D hD) (chainLaw a ha0 ha1 D hD) pathRelNat
      ≤ ENNReal.ofReal (phi α (a ^ (D ^ 2 - 1))
          + 2 ^ α * a ^ (α - 1) * (a ^ ((D : ℝ) - α) / (1 - a ^ ((D : ℝ) - α)))) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  set μ := chainLaw a ha0 ha1 D hD with hμ
  set x := a ^ ((D : ℝ) - α) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos ha0 _
  have hx1 : x < 1 := Real.rpow_lt_one ha0.le ha1 (by linarith)
  set C := (2 : ℝ) ^ α * a ^ (α - 1) with hC
  have hC0 : 0 ≤ C := by positivity
  have hD2 : (2 : ℕ) ^ 2 ≤ D ^ 2 := Nat.pow_le_pow_left hD 2
  have hlt : a ^ (D ^ 2 - 1) < 1 := pow_lt_one₀ ha0.le ha1 (by omega)
  have hφ0 : 0 ≤ phi α (a ^ (D ^ 2 - 1)) := phi_nonneg (pow_pos ha0 _).le hlt
  -- the term at `0`
  have h0 : μ 0 * phiE α (q μ pathRelNat 0) ≤ ENNReal.ofReal (phi α (a ^ (D ^ 2 - 1))) := by
    calc μ 0 * phiE α (q μ pathRelNat 0) ≤ phiE α (q μ pathRelNat 0) :=
          mul_le_of_le_one_left zero_le (PMF.coe_le_one μ 0)
      _ ≤ phiE α (a ^ (D ^ 2 - 1)) :=
          phiE_mono hα0 q_nonneg (chainLaw_q_zero_le ha0 ha1 hD)
      _ = ENNReal.ofReal (phi α (a ^ (D ^ 2 - 1))) := phiE_of_lt hlt
  -- the terms at `j + 1`
  have h1 : ∀ j, μ (j + 1) * phiE α (q μ pathRelNat (j + 1))
      ≤ ENNReal.ofReal (C * x * x ^ j) := by
    intro j
    have hpos : 0 < chainMass a D j := chainMass_pos ha0 ha1 hD j
    have hr : μ j ≤ rE μ pathRelNat (j + 1) := by
      rw [rE]
      calc μ j = if pathRelNat (j + 1) j then μ j else 0 := by
            rw [ite_eq_left (pathRelNat_succ_left j)]
        _ ≤ ∑' y, if pathRelNat (j + 1) y then μ y else 0 :=
            ENNReal.le_tsum (f := fun y => if pathRelNat (j + 1) y then μ y else 0) j
    have hr' : chainMass a D j ≤ 1 - q μ pathRelNat (j + 1) := by
      rw [← toReal_rE_eq]
      calc chainMass a D j = (μ j).toReal := by
            rw [hμ, chainLaw_apply, ENNReal.toReal_ofReal hpos.le]
        _ ≤ _ := ENNReal.toReal_mono rE_ne_top hr
    have hq1 : q μ pathRelNat (j + 1) < 1 := by linarith
    rw [phiE_of_lt hq1, hμ, chainLaw_apply,
      ← ENNReal.ofReal_mul (chainMass_nonneg ha0.le ha1.le (by omega) _)]
    apply ENNReal.ofReal_le_ofReal
    calc chainMass a D (j + 1) * phi α (q μ pathRelNat (j + 1))
        ≤ chainMass a D (j + 1) / chainMass a D j ^ α := by
          rw [phi, ← mul_div_assoc]
          refine div_le_div₀ (chainMass_nonneg ha0.le ha1.le (by omega) _)
            (mul_le_of_le_one_right (chainMass_nonneg ha0.le ha1.le (by omega) _) q_le_one)
            (Real.rpow_pos_of_pos hpos α) (Real.rpow_le_rpow hpos.le hr' hα0)
      _ ≤ C * a ^ (((D : ℝ) - α) * (D : ℝ) ^ j) := chainLaw_ratio_le ha0 ha1 hD hhalf hα0 j
      _ ≤ C * x ^ (j + 1) := by
          gcongr
          exact rpow_exponent_pow_le ha0 ha1 hD hαD j
      _ = C * x * x ^ j := by rw [pow_succ']; ring
  have hsum : Summable fun j : ℕ => C * x * x ^ j :=
    (summable_geometric_of_lt_one hx0.le hx1).mul_left _
  calc PhiD α μ μ pathRelNat
      = μ 0 * phiE α (q μ pathRelNat 0)
          + ∑' j, μ (j + 1) * phiE α (q μ pathRelNat (j + 1)) := by
        rw [PhiD, tsum_eq_zero_add' ENNReal.summable]
    _ ≤ ENNReal.ofReal (phi α (a ^ (D ^ 2 - 1))) + ∑' j, ENNReal.ofReal (C * x * x ^ j) :=
        add_le_add h0 (ENNReal.tsum_le_tsum h1)
    _ = ENNReal.ofReal (phi α (a ^ (D ^ 2 - 1))) + ENNReal.ofReal (∑' j, C * x * x ^ j) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum]
    _ = ENNReal.ofReal (phi α (a ^ (D ^ 2 - 1)) + C * (x / (1 - x))) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hx0.le hx1, div_eq_mul_inv, mul_assoc,
          ENNReal.ofReal_add hφ0 (by positivity)]

/-- `φ_α` is continuous at `0` with value `0`. -/
private lemma tendsto_phi_zero (α : ℝ) : Tendsto (phi α) (nhds 0) (nhds 0) := by
  have h : ContinuousAt (fun t : ℝ => t / (1 - t) ^ α) 0 := by
    refine ContinuousAt.div continuousAt_id ?_ (by simp)
    exact (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by norm_num))
  have h2 := h.tendsto
  simp only [zero_div] at h2
  exact h2

/-- `max D 2 - 1 → ∞`. -/
private lemma tendsto_max_sub_one : Tendsto (fun D : ℕ => max D 2 - 1) atTop atTop :=
  tendsto_atTop_mono (fun D => by omega) (tendsto_sub_atTop_nat 1)

/-- **`thm:eta-bound`, the mass at `0`**: `p_0 → 1` as `D → ∞`. -/
theorem chainLaw_zero_tendsto (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun D : ℕ => chainLaw' a ha0 ha1 D 0) atTop (nhds 1) := by
  have hg : Tendsto (fun D : ℕ => a ^ (max D 2 - 1)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).comp tendsto_max_sub_one
  have h := ENNReal.tendsto_ofReal (hg.const_sub 1)
  simp only [sub_zero, ENNReal.ofReal_one] at h
  refine h.congr fun D => ?_
  rw [chainLaw'_apply, chainMass_zero]

/-- The real bound of `eta_chainLaw_le` tends to `0` as `D → ∞` (`thm:eta-bound`). -/
private lemma tendsto_chain_bound {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (α : ℝ) :
    Tendsto (fun D : ℕ => phi α (a ^ (D ^ 2 - 1))
      + 2 ^ α * a ^ (α - 1) * (a ^ ((D : ℝ) - α) / (1 - a ^ ((D : ℝ) - α))))
      atTop (nhds 0) := by
  have t1 : Tendsto (fun D : ℕ => a ^ (D ^ 2 - 1)) atTop (nhds 0) := by
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).comp ?_
    refine tendsto_atTop_mono (fun D => ?_) (tendsto_sub_atTop_nat 1)
    have := Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) D
    show D - 1 ≤ D ^ 2 - 1
    omega
  have t1' : Tendsto (fun D : ℕ => phi α (a ^ (D ^ 2 - 1))) atTop (nhds 0) :=
    (tendsto_phi_zero α).comp t1
  have t2 : Tendsto (fun D : ℕ => a ^ ((D : ℝ) - α)) atTop (nhds 0) := by
    have := (tendsto_rpow_atTop_of_base_lt_one a (by linarith) ha1).comp
      (tendsto_atTop_add_const_right atTop (-α) tendsto_natCast_atTop_atTop)
    refine this.congr fun D => ?_
    simp [sub_eq_add_neg]
  have t3 : Tendsto (fun D : ℕ => a ^ ((D : ℝ) - α) / (1 - a ^ ((D : ℝ) - α))) atTop
      (nhds 0) := by
    have := t2.div (tendsto_const_nhds.sub t2) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    rw [show (0 : ℝ) / (1 - 0) = 0 by norm_num] at this
    exact this
  have := t1'.add (t3.const_mul (2 ^ α * a ^ (α - 1)))
  simpa using this

/-- **`thm:eta-bound`, the potential** in `ℝ≥0∞`: `η_{P,α}(μ_*) → 0` as `D → ∞`, for every
`α ≥ 1`. -/
theorem eta_chainLaw_tendsto_ennreal (α : ℝ) (hα : 1 ≤ α) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun D : ℕ => PhiD α (chainLaw' a ha0 ha1 D) (chainLaw' a ha0 ha1 D) pathRelNat)
      atTop (nhds 0) := by
  have hmax : Tendsto (fun D : ℕ => max D 2) atTop atTop :=
    tendsto_atTop_mono (fun D => le_max_left D 2) tendsto_id
  have hup : Tendsto (fun D : ℕ => ENNReal.ofReal (phi α (a ^ ((max D 2) ^ 2 - 1))
      + 2 ^ α * a ^ (α - 1) * (a ^ (((max D 2 : ℕ) : ℝ) - α)
        / (1 - a ^ (((max D 2 : ℕ) : ℝ) - α))))) atTop (nhds 0) := by
    have := ENNReal.tendsto_ofReal ((tendsto_chain_bound ha0 ha1 α).comp hmax)
    simpa [Function.comp_def] using this
  have e1 : ∀ᶠ D : ℕ in atTop, a ^ (max D 2 - 1) ≤ 1 / 2 :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).comp
      tendsto_max_sub_one).eventually_le_const (by norm_num)
  have e2 : ∀ᶠ D : ℕ in atTop, α < ((max D 2 : ℕ) : ℝ) := by
    filter_upwards [eventually_gt_atTop ⌈α⌉₊] with D hD
    calc α ≤ ⌈α⌉₊ := Nat.le_ceil α
      _ < (D : ℝ) := by exact_mod_cast hD
      _ ≤ ((max D 2 : ℕ) : ℝ) := by exact_mod_cast le_max_left D 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [e1, e2] with D h1 h2
  exact eta_chainLaw_le ha0 ha1 (le_max_right D 2) hα h1 h2

/-- **`thm:eta-bound`, the potential**: `η_{P,α}(μ_*) → 0` as `D → ∞`, for every
`α ≥ 1`. -/
theorem eta_chainLaw_tendsto (α : ℝ) (hα : 1 ≤ α) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun D : ℕ =>
      (PhiD α (chainLaw' a ha0 ha1 D) (chainLaw' a ha0 ha1 D) pathRelNat).toReal)
      atTop (nhds 0) := by
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (eta_chainLaw_tendsto_ennreal α hα a ha0 ha1)
  simpa [Function.comp_def] using this

/-! ### Bushy trees (`thm:shape-eta`) -/

/-- The `v₀` contribution to `η` is at most `(1 - μ(v₀))/μ(v₀)^α` (`thm:shape-eta`):
`v₀` is compatible with itself, so `b(v₀) ≥ μ(v₀)`. -/
theorem bushy_v0_term_le {V : Type} (μ : PMF V) (R : V → V → Prop) (v0 : V) {α : ℝ}
    (hα : 0 ≤ α) (hrefl : R v0 v0) :
    μ v0 * phiE α (q μ R v0)
      ≤ ENNReal.ofReal ((1 - (μ v0).toReal) / (μ v0).toReal ^ α) := by
  by_cases h0 : μ v0 = 0
  · rw [h0, zero_mul]; exact zero_le
  have hm : 0 < (μ v0).toReal := ENNReal.toReal_pos h0 (PMF.apply_ne_top _ _)
  have hmb : (μ v0).toReal ≤ (rE μ R v0).toReal :=
    ENNReal.toReal_mono rE_ne_top (le_rE_of_refl hrefl)
  have hq1 : q μ R v0 < 1 := q_lt_one hrefl h0
  have hb : (rE μ R v0).toReal = 1 - q μ R v0 := toReal_rE_eq μ R v0
  have hq0 : 0 ≤ q μ R v0 := q_nonneg
  calc μ v0 * phiE α (q μ R v0) ≤ phiE α (q μ R v0) :=
        mul_le_of_le_one_left zero_le (PMF.coe_le_one μ v0)
    _ = ENNReal.ofReal (phi α (q μ R v0)) := phiE_of_lt hq1
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [phi, ← hb]
        exact div_le_div₀ (by linarith) (by linarith) (Real.rpow_pos_of_pos hm α)
          (Real.rpow_le_rpow hm.le hmb hα)

/-- Every label other than `v₀` contributes at most `μ(v) e^{αC₀} e^{αC₀ N(v) D^{-1/2}}`
(`thm:shape-eta`): from `b(v) ≥ exp(-C₀(N D^{-1/2} + 1))`, `φ_α(1 - b(v)) ≤ b(v)^{-α}`,
and every positive-mass label other than `v₀` has `N > D²`. -/
theorem bushy_other_terms_le {V : Type} (μ : PMF V) (R : V → V → Prop) (N : V → ℕ) (v0 : V)
    (D : ℕ) {α C₀ : ℝ} (hα : 0 ≤ α)
    (hN : ∀ v, μ v ≠ 0 → v ≠ v0 → D ^ 2 < N v)
    (hb : ∀ v, μ v ≠ 0 → v ≠ v0 →
      ENNReal.ofReal (Real.exp (-(C₀ * ((N v : ℝ) / Real.sqrt D + 1)))) ≤ rE μ R v) :
    ∑' v, (if v = v0 then 0 else μ v * phiE α (q μ R v))
      ≤ ENNReal.ofReal (Real.exp (α * C₀))
        * ∑' v, (if D ^ 2 < N v then
            μ v * ENNReal.ofReal (Real.exp (α * C₀ / Real.sqrt D * N v)) else 0) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun v => ?_
  by_cases hv : v = v0
  · rw [ite_eq_left hv]; exact zero_le
  rw [ite_eq_right hv]
  by_cases h0 : μ v = 0
  · rw [h0, zero_mul]; exact zero_le
  rw [ite_eq_left (hN v h0 hv)]
  set e := Real.exp (-(C₀ * ((N v : ℝ) / Real.sqrt D + 1))) with he
  have he0 : 0 < e := Real.exp_pos _
  have hbe : e ≤ (rE μ R v).toReal := by
    have := ENNReal.toReal_mono rE_ne_top (hb v h0 hv)
    rwa [ENNReal.toReal_ofReal he0.le] at this
  have hrq : (rE μ R v).toReal = 1 - q μ R v := toReal_rE_eq μ R v
  have hq1 : q μ R v < 1 := by linarith
  calc μ v * phiE α (q μ R v) = μ v * ENNReal.ofReal (phi α (q μ R v)) := by
        rw [phiE_of_lt hq1]
    _ ≤ μ v * (ENNReal.ofReal (Real.exp (α * C₀))
          * ENNReal.ofReal (Real.exp (α * C₀ / Real.sqrt D * N v))) := by
        gcongr
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        rw [phi, ← hrq]
        calc q μ R v / (rE μ R v).toReal ^ α ≤ 1 / e ^ α :=
              div_le_div₀ zero_le_one q_le_one (Real.rpow_pos_of_pos he0 α)
                (Real.rpow_le_rpow he0.le hbe hα)
          _ = Real.exp (α * C₀) * Real.exp (α * C₀ / Real.sqrt D * N v) := by
              rw [he, ← Real.exp_mul, one_div, ← Real.exp_neg, ← Real.exp_add]
              congr 1
              by_cases hD : Real.sqrt D = 0
              · rw [hD]; ring
              · field_simp
                ring
    _ = _ := by ring

/-- The tail sum of `thm:shape-eta`: if `μ{N > n} ≤ A₀ e^{-c₀ n}` for every `n` and
`κ ≤ c₀/2`, then, summing over the integer values of `N > D²`,
`𝔼[𝟙{N > D²} e^{κ N}] ≤ A₀ e^{c₀} (1 - e^{-c₀/2})^{-1} e^{-c₀ D²/2}`. -/
theorem bushy_moment_le {V : Type} (μ : PMF V) (N : V → ℕ) (D : ℕ) {A₀ c₀ κ : ℝ}
    (hA : 0 ≤ A₀) (hc : 0 < c₀)
    (htail : ∀ n : ℕ, ∑' v, (if n < N v then μ v else 0)
      ≤ ENNReal.ofReal (A₀ * Real.exp (-(c₀ * n))))
    (hκ : κ ≤ c₀ / 2) :
    ∑' v, (if D ^ 2 < N v then μ v * ENNReal.ofReal (Real.exp (κ * N v)) else 0)
      ≤ ENNReal.ofReal (A₀ * Real.exp c₀ / (1 - Real.exp (-(c₀ / 2)))
          * Real.exp (-(c₀ * (D : ℝ) ^ 2 / 2))) := by
  set r := Real.exp (-(c₀ / 2)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  set K := A₀ * Real.exp c₀ with hK
  have hK0 : 0 ≤ K := by positivity
  -- the fibre `{N = n}` for each integer `n`
  set F : V → ℝ≥0∞ := fun v =>
    if D ^ 2 < N v then μ v * ENNReal.ofReal (Real.exp (c₀ / 2 * N v)) else 0 with hF
  have step1 : ∑' v, (if D ^ 2 < N v then μ v * ENNReal.ofReal (Real.exp (κ * N v)) else 0)
      ≤ ∑' v, F v := by
    refine ENNReal.tsum_le_tsum fun v => ?_
    simp only [hF]
    split_ifs
    · gcongr
    · exact le_rfl
  have step2 : ∑' v, F v = ∑' n : ℕ, ∑' v, (if n = N v then F v else 0) := by
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun v => (tsum_ite_eq (N v) (fun _ => F v)).symm
  have step3 : ∀ n : ℕ, ∑' v, (if n = N v then F v else 0)
      = (if D ^ 2 < n then ENNReal.ofReal (Real.exp (c₀ / 2 * n)) else 0)
        * ∑' v, (if n = N v then μ v else 0) := by
    intro n
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun v => ?_
    by_cases hn : n = N v
    · subst hn
      simp only [hF, ite_true]
      split_ifs <;> ring
    · simp [hn]
  have step4 : ∀ n : ℕ, D ^ 2 < n →
      ∑' v, (if n = N v then μ v else 0)
        ≤ ENNReal.ofReal (A₀ * Real.exp (-(c₀ * ((n : ℝ) - 1)))) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    calc ∑' v, (if m + 1 = N v then μ v else 0) ≤ ∑' v, (if m < N v then μ v else 0) := by
          refine ENNReal.tsum_le_tsum fun v => ?_
          split_ifs with h1 h2
          · exact le_rfl
          · omega
          · exact zero_le
          · exact le_rfl
      _ ≤ ENNReal.ofReal (A₀ * Real.exp (-(c₀ * m))) := htail m
      _ = _ := by push_cast; ring_nf
  have step5 : ∀ n : ℕ, ∑' v, (if n = N v then F v else 0)
      ≤ ENNReal.ofReal (if D ^ 2 < n then K * r ^ n else 0) := by
    intro n
    rw [step3 n]
    by_cases hn : D ^ 2 < n
    · rw [ite_eq_left hn, ite_eq_left hn]
      calc ENNReal.ofReal (Real.exp (c₀ / 2 * n)) * ∑' v, (if n = N v then μ v else 0)
          ≤ ENNReal.ofReal (Real.exp (c₀ / 2 * n))
            * ENNReal.ofReal (A₀ * Real.exp (-(c₀ * ((n : ℝ) - 1)))) := by
            gcongr
            exact step4 n hn
        _ = ENNReal.ofReal (K * r ^ n) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, hK, hr, ← Real.exp_nat_mul]
            congr 1
            have hex : Real.exp (c₀ / 2 * n) * Real.exp (-(c₀ * ((n : ℝ) - 1)))
                = Real.exp c₀ * Real.exp ((n : ℝ) * -(c₀ / 2)) := by
              rw [← Real.exp_add, ← Real.exp_add]
              congr 1
              ring
            linear_combination A₀ * hex
    · rw [ite_eq_right hn, ite_eq_right hn, zero_mul, ENNReal.ofReal_zero]
  -- the geometric tail
  have hsum : Summable fun n : ℕ => if D ^ 2 < n then K * r ^ n else 0 := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0.le hr1).mul_left K)
    · split_ifs <;> positivity
    · split_ifs
      · exact le_rfl
      · positivity
  have hshift : ∑' n : ℕ, (if D ^ 2 < n then K * r ^ n else 0) = K * r ^ (D ^ 2 + 1) / (1 - r) := by
    have hg : Function.Injective fun k : ℕ => k + (D ^ 2 + 1) := add_left_injective _
    have hsupp : Function.support (fun n : ℕ => if D ^ 2 < n then K * r ^ n else 0)
        ⊆ Set.range fun k : ℕ => k + (D ^ 2 + 1) := by
      intro n hn
      rw [Function.mem_support] at hn
      have : D ^ 2 < n := by
        by_contra h
        exact hn (ite_eq_right h)
      exact ⟨n - (D ^ 2 + 1), by simp only; omega⟩
    rw [← hg.tsum_eq hsupp]
    have h2 : ∀ k : ℕ, (if D ^ 2 < k + (D ^ 2 + 1) then K * r ^ (k + (D ^ 2 + 1)) else 0)
        = K * r ^ (D ^ 2 + 1) * r ^ k := by
      intro k
      rw [ite_eq_left (by omega), pow_add]
      ring
    simp_rw [h2]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1, div_eq_mul_inv]
  calc ∑' v, (if D ^ 2 < N v then μ v * ENNReal.ofReal (Real.exp (κ * N v)) else 0)
      ≤ ∑' v, F v := step1
    _ = ∑' n : ℕ, ∑' v, (if n = N v then F v else 0) := step2
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (if D ^ 2 < n then K * r ^ n else 0) :=
        ENNReal.tsum_le_tsum step5
    _ = ENNReal.ofReal (∑' n : ℕ, (if D ^ 2 < n then K * r ^ n else 0)) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by split_ifs <;> positivity) hsum]
    _ = ENNReal.ofReal (K * r ^ (D ^ 2 + 1) / (1 - r)) := by rw [hshift]
    _ ≤ ENNReal.ofReal (K / (1 - r) * Real.exp (-(c₀ * (D : ℝ) ^ 2 / 2))) := by
        apply ENNReal.ofReal_le_ofReal
        have hr1' : 0 < 1 - r := by linarith
        have hpow : r ^ (D ^ 2) = Real.exp (-(c₀ * (D : ℝ) ^ 2 / 2)) := by
          rw [hr, ← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
        have hKr : 0 ≤ K / (1 - r) := div_nonneg hK0 hr1'.le
        rw [← hpow, pow_succ]
        calc K * (r ^ (D ^ 2) * r) / (1 - r) = K / (1 - r) * (r ^ (D ^ 2) * r) := by ring
          _ ≤ K / (1 - r) * r ^ (D ^ 2) :=
              mul_le_mul_of_nonneg_left
                (mul_le_of_le_one_right (pow_nonneg hr0.le _) hr1.le) hKr


/-- The mass outside `v₀` is at most the tail `μ{N > D²} ≤ A₀ e^{-c₀ D²}` (`thm:shape-eta`):
every positive-mass label other than `v₀` comes from a shape of size `N > D²`. -/
theorem bushy_v0_mass_le {V : Type} (μ : PMF V) (N : V → ℕ) (v0 : V) (D : ℕ) {A₀ c₀ : ℝ}
    (hN : ∀ v, μ v ≠ 0 → v ≠ v0 → D ^ 2 < N v)
    (htail : ∀ n : ℕ, ∑' v, (if n < N v then μ v else 0)
      ≤ ENNReal.ofReal (A₀ * Real.exp (-(c₀ * n)))) :
    1 - μ v0 ≤ ENNReal.ofReal (A₀ * Real.exp (-(c₀ * (D : ℝ) ^ 2))) := by
  have h1 : (1 : ℝ≥0∞) = μ v0 + ∑' v, (if v = v0 then 0 else μ v) := by
    rw [← μ.tsum_coe]; exact ENNReal.tsum_eq_add_tsum_ite v0
  rw [h1, ENNReal.add_sub_cancel_left (PMF.apply_ne_top _ _)]
  calc ∑' v, (if v = v0 then 0 else μ v) ≤ ∑' v, (if D ^ 2 < N v then μ v else 0) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        by_cases hv : v = v0
        · rw [ite_eq_left hv]; exact zero_le
        by_cases h0 : μ v = 0
        · rw [ite_eq_right hv, h0]; exact zero_le
        rw [ite_eq_right hv, ite_eq_left (hN v h0 hv)]
    _ ≤ ENNReal.ofReal (A₀ * Real.exp (-(c₀ * ((D ^ 2 : ℕ) : ℝ)))) := htail (D ^ 2)
    _ = _ := by push_cast; rfl

/-- The real form of `bushy_v0_mass_le`: `1 - μ(v₀) ≤ A₀ e^{-c₀ D²}`. -/
theorem bushy_v0_mass_le_real {V : Type} (μ : PMF V) (N : V → ℕ) (v0 : V) (D : ℕ) {A₀ c₀ : ℝ}
    (hA : 0 ≤ A₀) (hN : ∀ v, μ v ≠ 0 → v ≠ v0 → D ^ 2 < N v)
    (htail : ∀ n : ℕ, ∑' v, (if n < N v then μ v else 0)
      ≤ ENNReal.ofReal (A₀ * Real.exp (-(c₀ * n)))) :
    1 - (μ v0).toReal ≤ A₀ * Real.exp (-(c₀ * (D : ℝ) ^ 2)) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (bushy_v0_mass_le μ N v0 D hN htail)
  rw [ENNReal.toReal_sub_of_le (PMF.coe_le_one μ v0) ENNReal.one_ne_top, ENNReal.toReal_one] at h
  rwa [ENNReal.toReal_ofReal (by positivity)] at h

/-- **The potential bound of the bushy laws** (`thm:shape-eta`): for
`α C₀ D^{-1/2} ≤ c₀/2`,
`η_{G_D,α}(μ_D) ≤ (1-μ_D(v₀))/μ_D(v₀)^α + e^{αC₀} A₀ e^{c₀} (1-e^{-c₀/2})^{-1} e^{-c₀D²/2}`. -/
theorem bushy_eta_le {V : Type} (μ : PMF V) (R : V → V → Prop) (N : V → ℕ) (v0 : V) (D : ℕ)
    {α A₀ c₀ C₀ : ℝ} (hα : 0 ≤ α) (hA : 0 ≤ A₀) (hc : 0 < c₀) (hrefl : R v0 v0)
    (hN : ∀ v, μ v ≠ 0 → v ≠ v0 → D ^ 2 < N v)
    (htail : ∀ n : ℕ, ∑' v, (if n < N v then μ v else 0)
      ≤ ENNReal.ofReal (A₀ * Real.exp (-(c₀ * n))))
    (hb : ∀ v, μ v ≠ 0 → v ≠ v0 →
      ENNReal.ofReal (Real.exp (-(C₀ * ((N v : ℝ) / Real.sqrt D + 1)))) ≤ rE μ R v)
    (hκ : α * C₀ / Real.sqrt D ≤ c₀ / 2) :
    PhiD α μ μ R ≤ ENNReal.ofReal ((1 - (μ v0).toReal) / (μ v0).toReal ^ α
        + Real.exp (α * C₀) * (A₀ * Real.exp c₀ / (1 - Real.exp (-(c₀ / 2)))
          * Real.exp (-(c₀ * (D : ℝ) ^ 2 / 2)))) := by
  have hm1 : (μ v0).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ v0)
  have hr1 : 0 < 1 - Real.exp (-(c₀ / 2)) := by
    have : Real.exp (-(c₀ / 2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  rw [PhiD, ENNReal.tsum_eq_add_tsum_ite v0,
    ENNReal.ofReal_add (div_nonneg (by linarith) (Real.rpow_nonneg ENNReal.toReal_nonneg α))
      (by positivity)]
  refine add_le_add (bushy_v0_term_le μ R v0 hα hrefl) ?_
  calc ∑' v, (if v = v0 then 0 else μ v * phiE α (q μ R v))
      ≤ ENNReal.ofReal (Real.exp (α * C₀))
        * ∑' v, (if D ^ 2 < N v then
            μ v * ENNReal.ofReal (Real.exp (α * C₀ / Real.sqrt D * N v)) else 0) :=
        bushy_other_terms_le μ R N v0 D hα hN hb
    _ ≤ ENNReal.ofReal (Real.exp (α * C₀))
        * ENNReal.ofReal (A₀ * Real.exp c₀ / (1 - Real.exp (-(c₀ / 2)))
          * Real.exp (-(c₀ * (D : ℝ) ^ 2 / 2))) := by
        gcongr
        exact bushy_moment_le μ N D hA hc htail hκ
    _ = _ := by rw [ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- `c₀ D² → ∞` and `c₀ D²/2 → ∞`. -/
private lemma tendsto_const_mul_sq (c₀ : ℝ) (hc : 0 < c₀) :
    Tendsto (fun D : ℕ => c₀ * (D : ℝ) ^ 2) atTop atTop :=
  (tendsto_pow_atTop two_ne_zero |>.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc

/-- The tail bound `A₀ e^{-c₀ D²} → 0`. -/
private lemma tendsto_tail_bound (A₀ c₀ : ℝ) (hc : 0 < c₀) :
    Tendsto (fun D : ℕ => A₀ * Real.exp (-(c₀ * (D : ℝ) ^ 2))) atTop (nhds 0) := by
  have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_const_mul_sq c₀ hc)).const_mul A₀
  rw [mul_zero] at this
  exact this

/-- `e^{-c₀ D²/2} → 0`. -/
private lemma tendsto_half_tail (c₀ : ℝ) (hc : 0 < c₀) :
    Tendsto (fun D : ℕ => Real.exp (-(c₀ * (D : ℝ) ^ 2 / 2))) atTop (nhds 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_const_mul_sq c₀ hc).atTop_div_const two_pos)

/-- The large-`D` condition `α C₀ D^{-1/2} ≤ c₀/2` holds eventually (`thm:shape-eta`). -/
private lemma eventually_kappa_le {α C₀ c₀ : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C₀) (hc : 0 < c₀) :
    ∀ᶠ D : ℕ in atTop, α * C₀ / Real.sqrt D ≤ c₀ / 2 := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈(2 * α * C₀ / c₀) ^ 2⌉₊]
    with D hD1 hD2
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hs : 2 * α * C₀ / c₀ ≤ Real.sqrt D := by
    rw [Real.le_sqrt (by positivity) hD0.le]
    calc (2 * α * C₀ / c₀) ^ 2 ≤ ⌈(2 * α * C₀ / c₀) ^ 2⌉₊ := Nat.le_ceil _
      _ ≤ D := by exact_mod_cast hD2
  rw [div_le_iff₀ hsD]
  calc α * C₀ = c₀ / 2 * (2 * α * C₀ / c₀) := by field_simp
    _ ≤ c₀ / 2 * Real.sqrt D := by gcongr

/-- **`μ_D(v₀) → 1`** (`thm:shape-eta`): the distinguished mass of the bushy laws tends
to one, from the tail bound alone. -/
theorem bushy_v0_tendsto {V : ℕ → Type} (μ : ∀ D, PMF (V D)) (N : ∀ D, V D → ℕ)
    (v0 : ∀ D, V D) {A₀ c₀ : ℝ} (hc : 0 < c₀)
    (hN : ∀ᶠ D : ℕ in atTop, ∀ v, μ D v ≠ 0 → v ≠ v0 D → D ^ 2 < N D v)
    (htail : ∀ᶠ D : ℕ in atTop, ∀ n : ℕ, ∑' v, (if n < N D v then μ D v else 0)
      ≤ ENNReal.ofReal (A₀ * Real.exp (-(c₀ * n)))) :
    Tendsto (fun D => μ D (v0 D)) atTop (nhds 1) := by
  have hlow : Tendsto (fun D : ℕ => 1 - ENNReal.ofReal (A₀ * Real.exp (-(c₀ * (D : ℝ) ^ 2))))
      atTop (nhds 1) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds
      (ENNReal.tendsto_ofReal (tendsto_tail_bound A₀ c₀ hc)) (Or.inl ENNReal.one_ne_top)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun D => PMF.coe_le_one _ _)
  filter_upwards [hN, htail] with D hN' htail'
  have h := bushy_v0_mass_le (μ D) (N D) (v0 D) D hN' htail'
  rw [tsub_le_iff_right] at h ⊢
  rw [add_comm]; exact h

/-- The real bound of `bushy_eta_le` tends to `0` (`thm:shape-eta`). -/
private lemma tendsto_bushy_bound {V : ℕ → Type} (μ : ∀ D, PMF (V D)) (N : ∀ D, V D → ℕ)
    (v0 : ∀ D, V D) {α A₀ c₀ C₀ : ℝ} (hc : 0 < c₀)
    (hN : ∀ᶠ D : ℕ in atTop, ∀ v, μ D v ≠ 0 → v ≠ v0 D → D ^ 2 < N D v)
    (htail : ∀ᶠ D : ℕ in atTop, ∀ n : ℕ, ∑' v, (if n < N D v then μ D v else 0)
      ≤ ENNReal.ofReal (A₀ * Real.exp (-(c₀ * n)))) :
    Tendsto (fun D : ℕ => (1 - (μ D (v0 D)).toReal) / (μ D (v0 D)).toReal ^ α
        + Real.exp (α * C₀) * (A₀ * Real.exp c₀ / (1 - Real.exp (-(c₀ / 2)))
          * Real.exp (-(c₀ * (D : ℝ) ^ 2 / 2)))) atTop (nhds 0) := by
  have hm : Tendsto (fun D => (μ D (v0 D)).toReal) atTop (nhds 1) := by
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp (bushy_v0_tendsto μ N v0 hc hN htail)
    simpa [Function.comp_def] using this
  have h1 : Tendsto (fun D => (1 - (μ D (v0 D)).toReal) / (μ D (v0 D)).toReal ^ α) atTop
      (nhds 0) := by
    have hsub : Tendsto (fun D => 1 - (μ D (v0 D)).toReal) atTop (nhds (1 - 1)) :=
      tendsto_const_nhds.sub hm
    have hpow : Tendsto (fun D => (μ D (v0 D)).toReal ^ α) atTop (nhds ((1 : ℝ) ^ α)) :=
      hm.rpow_const (Or.inl one_ne_zero)
    have := hsub.div hpow (by simp)
    rw [show ((1 : ℝ) - 1) / (1 : ℝ) ^ α = 0 by simp] at this
    exact this
  have h2 := ((tendsto_half_tail c₀ hc).const_mul
    (A₀ * Real.exp c₀ / (1 - Real.exp (-(c₀ / 2))))).const_mul (Real.exp (α * C₀))
  simp only [mul_zero] at h2
  simpa using h1.add h2

/-- **`η_{G_D,α}(μ_D) → 0`** (`thm:shape-eta`), in `ℝ≥0∞`: under the tail bound
`μ_D{N > n} ≤ A₀ e^{-c₀ n}`, the shrinking bound `b_D(v) ≥ exp(-C₀(N D^{-1/2} + 1))` on the
positive-mass labels other than `v₀`, and `N > D²` off `v₀`, the potential of the bushy laws tends
to zero. -/
theorem bushy_eta_tendsto_ennreal {V : ℕ → Type} (μ : ∀ D, PMF (V D))
    (R : ∀ D, V D → V D → Prop) (N : ∀ D, V D → ℕ) (v0 : ∀ D, V D)
    {α A₀ c₀ C₀ : ℝ} (hα : 0 ≤ α) (hA : 0 ≤ A₀) (hc : 0 < c₀) (hC : 0 ≤ C₀)
    (hrefl : ∀ᶠ D : ℕ in atTop, R D (v0 D) (v0 D))
    (hN : ∀ᶠ D : ℕ in atTop, ∀ v, μ D v ≠ 0 → v ≠ v0 D → D ^ 2 < N D v)
    (htail : ∀ᶠ D : ℕ in atTop, ∀ n : ℕ, ∑' v, (if n < N D v then μ D v else 0)
      ≤ ENNReal.ofReal (A₀ * Real.exp (-(c₀ * n))))
    (hb : ∀ᶠ D : ℕ in atTop, ∀ v, μ D v ≠ 0 → v ≠ v0 D →
      ENNReal.ofReal (Real.exp (-(C₀ * ((N D v : ℝ) / Real.sqrt D + 1)))) ≤ rE (μ D) (R D) v) :
    Tendsto (fun D => PhiD α (μ D) (μ D) (R D)) atTop (nhds 0) := by
  have hup := ENNReal.tendsto_ofReal (tendsto_bushy_bound μ N v0 (α := α) (C₀ := C₀) hc hN htail)
  rw [ENNReal.ofReal_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hrefl, hN, htail, hb, eventually_kappa_le hα hC hc]
    with D hrefl' hN' htail' hb' hκ
  exact bushy_eta_le (μ D) (R D) (N D) (v0 D) D hα hA hc hrefl' hN' htail' hb' hκ

/-- **`η_{G_D,α}(μ_D) → 0`** (`thm:shape-eta`), the real form of
`bushy_eta_tendsto_ennreal`. -/
theorem bushy_eta_tendsto {V : ℕ → Type} (μ : ∀ D, PMF (V D))
    (R : ∀ D, V D → V D → Prop) (N : ∀ D, V D → ℕ) (v0 : ∀ D, V D)
    {α A₀ c₀ C₀ : ℝ} (hα : 0 ≤ α) (hA : 0 ≤ A₀) (hc : 0 < c₀) (hC : 0 ≤ C₀)
    (hrefl : ∀ᶠ D : ℕ in atTop, R D (v0 D) (v0 D))
    (hN : ∀ᶠ D : ℕ in atTop, ∀ v, μ D v ≠ 0 → v ≠ v0 D → D ^ 2 < N D v)
    (htail : ∀ᶠ D : ℕ in atTop, ∀ n : ℕ, ∑' v, (if n < N D v then μ D v else 0)
      ≤ ENNReal.ofReal (A₀ * Real.exp (-(c₀ * n))))
    (hb : ∀ᶠ D : ℕ in atTop, ∀ v, μ D v ≠ 0 → v ≠ v0 D →
      ENNReal.ofReal (Real.exp (-(C₀ * ((N D v : ℝ) / Real.sqrt D + 1)))) ≤ rE (μ D) (R D) v) :
    Tendsto (fun D => (PhiD α (μ D) (μ D) (R D)).toReal) atTop (nhds 0) := by
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (bushy_eta_tendsto_ennreal μ R N v0 hα hA hc hC hrefl hN htail hb)
  simpa [Function.comp_def] using this

/-! ### The probability-one conclusion (`thm:cross-law` and `thm:hairy`) -/

/-- **The probability-one conclusion** (`thm:cross-law` and `thm:hairy`): if an event `A` contains events
`B_D` with `P(B_D) ≥ 1 - ε_D` and `ε_D → 0`, then `P(A) = 1`. The events `B_D` need not be
independent, nested or consistently coupled. -/
theorem prob_eq_one_of_le {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : Set Ω) (B : ℕ → Set Ω) (hB : ∀ D, B D ⊆ A)
    (ε : ℕ → ℝ≥0∞) (hε : Tendsto ε atTop (nhds 0)) (h : ∀ D, 1 - ε D ≤ P (B D)) : P A = 1 := by
  refine le_antisymm MeasureTheory.prob_le_one ?_
  have hlim : Tendsto (fun D => 1 - ε D) atTop (nhds 1) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds hε (Or.inl ENNReal.one_ne_top)
    simpa using this
  exact le_of_tendsto' hlim fun D => (h D).trans (MeasureTheory.measure_mono (hB D))

/-- `prob_eq_one_of_le` with the inclusions and the bounds required only for every
sufficiently large `D` (`thm:cross-law` and `thm:hairy`). -/
theorem prob_eq_one_of_eventually_le {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : Set Ω) (B : ℕ → Set Ω)
    (hB : ∀ᶠ D : ℕ in atTop, B D ⊆ A) (ε : ℕ → ℝ≥0∞) (hε : Tendsto ε atTop (nhds 0))
    (h : ∀ᶠ D : ℕ in atTop, 1 - ε D ≤ P (B D)) : P A = 1 := by
  refine le_antisymm MeasureTheory.prob_le_one ?_
  have hlim : Tendsto (fun D => 1 - ε D) atTop (nhds 1) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds hε (Or.inl ENNReal.one_ne_top)
    simpa using this
  refine le_of_tendsto hlim ?_
  filter_upwards [hB, h] with D hB' h'
  exact h'.trans (MeasureTheory.measure_mono hB')

end GraphMarkovMatching.Stopped
