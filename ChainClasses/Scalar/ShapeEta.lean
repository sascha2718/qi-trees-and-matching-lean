import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
`sec:shape-eta` of `gw_classes_simple.tex`: the potential bound
`thm:shape-eta`, `η_{G_D,α}(μ_D) ≤ e^{-cD²}`.

The proof splits the sum `eq:potential` at the class `v₀` of the one-vertex
shape and is scalar throughout, so it is certified here over the data the
geometry supplies: the mass `b₀` of the ball at `v₀`, the mass `g n` carried by
the members of size `n` of the remaining classes, and the ball masses `bb n` of
those classes.  The three inputs are exactly the three facts proved
geometrically in the tex, namely `μ_D(v₀) ≥ 1 - e^{-cD²}` (every shape of
diameter at most `D²` collapses to the one-vertex shape), `g n = 0` for
`n ≤ D²` (the same statement read on the complement), and the domination
`eq:shape-domination` `b ≥ e^{-C₁(n/√D + 1)}` (the shrinking cascade).

* `wgt` is the one-site weight `φ(b) = (1-b)/b^{5/2}` at `α = 5/2`;
  `wgt_le_of_half` is the `v₀`-term (`b ≥ ½` gives `φ ≤ 6(1-b)`),
  `wgt_le_of_exp` the tail terms, and `wgt_le_of_half_exp` the variant used by
  the coupling in `sec:shape-coupling`, where the ball mass carries a factor
  `½`.
* `eta_tail_sum` is the geometric sum of the display: the mass tail `e^{-cn}`
  beats the dilated weight `e^{γn}` as soon as `γ ≤ c/2`, which is the paper's
  condition `\tfrac52 C₁ D^{-1/2} ≤ c/2`.
* `shape_eta_le` assembles the two groups, and `shape_eta_final` is the
  largeness step `6e^{-cD²} + C₂e^{-cD²/2} ≤ e^{-cD²/4}` that renames `c/4` to
  `c` in `eq:shape-eta`.
-/

namespace ChainClasses

open Real

/-! ### The one-site weight -/

/-- The one-site weight of `eq:potential` at `α = 5/2`:
`φ(b) = (1-b)/b^{5/2}`. -/
noncomputable def wgt (b : ℝ) : ℝ := (1 - b) / b ^ ((5 : ℝ) / 2)

/-- `(1/2)^{5/2} ≥ 1/6`, the constant `6` of the `v₀`-term. -/
lemma one_div_six_le_rpow : (1 : ℝ) / 6 ≤ (1 / 2 : ℝ) ^ ((5 : ℝ) / 2) := by
  set y : ℝ := (1 / 2 : ℝ) ^ ((5 : ℝ) / 2) with hy
  have hpos : 0 < y := Real.rpow_pos_of_pos (by norm_num) _
  have hsq : y ^ (2 : ℕ) = 1 / 32 := by
    rw [hy, ← Real.rpow_natCast ((1 / 2 : ℝ) ^ ((5 : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num)]
    rw [show (5 : ℝ) / 2 * (2 : ℕ) = ((5 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    norm_num
  nlinarith [hsq, hpos]

/-- `e^x` as an rpow base: `(e^x)^y = e^{xy}`. -/
lemma exp_rpow_eq (x y : ℝ) : Real.exp x ^ y = Real.exp (x * y) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]

lemma wgt_nonneg {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) : 0 ≤ wgt b := by
  have hpos : (0 : ℝ) < b ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hb0 _
  exact div_nonneg (by linarith) hpos.le

/-- The `v₀`-term of `thm:shape-eta`: a ball mass at least `1/2` gives weight
at most `6(1-b)`. -/
lemma wgt_le_of_half {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1) : wgt b ≤ 6 * (1 - b) := by
  have hbpos : (0 : ℝ) < b := by linarith
  have hden : (1 : ℝ) / 6 ≤ b ^ ((5 : ℝ) / 2) :=
    one_div_six_le_rpow.trans (Real.rpow_le_rpow (by norm_num) hb (by norm_num))
  have hden0 : (0 : ℝ) < b ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hbpos _
  rw [wgt, div_le_iff₀ hden0]
  nlinarith [hden, hb1]

/-- The tail terms of `thm:shape-eta`: a ball mass at least `e^{-X}` gives
weight at most `e^{5X/2}`. -/
lemma wgt_le_of_exp {b X : ℝ} (hb : Real.exp (-X) ≤ b) : wgt b ≤ Real.exp (5 / 2 * X) := by
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (Real.exp_pos _) hb
  have hden : Real.exp (-(5 / 2 * X)) ≤ b ^ ((5 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow (Real.exp_pos (-X)).le hb (by norm_num : (0:ℝ) ≤ (5:ℝ)/2)
    rwa [exp_rpow_eq, show -X * ((5:ℝ)/2) = -(5 / 2 * X) by ring] at h
  have hden0 : (0 : ℝ) < b ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hbpos _
  have hmul : Real.exp (-(5 / 2 * X)) * Real.exp (5 / 2 * X) = 1 := by
    rw [← Real.exp_add]; simp
  rw [wgt, div_le_iff₀ hden0]
  nlinarith [Real.exp_pos (5 / 2 * X), hbpos]

/-- The variant used in `sec:shape-coupling`, where the ball mass carries a
factor `1/2`: from `b ≥ e^{-X}/2` the weight is at most `6e^{5X/2}`. -/
lemma wgt_le_of_half_exp {b X : ℝ} (hb : Real.exp (-X) / 2 ≤ b) :
    wgt b ≤ 6 * Real.exp (5 / 2 * X) := by
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by positivity) hb
  have hhalf : (Real.exp (-X) / 2) ^ ((5 : ℝ) / 2)
      = Real.exp (-(5 / 2 * X)) * (1 / 2 : ℝ) ^ ((5 : ℝ) / 2) := by
    rw [show Real.exp (-X) / 2 = Real.exp (-X) * (1 / 2 : ℝ) by ring,
      Real.mul_rpow (Real.exp_pos _).le (by norm_num), exp_rpow_eq,
      show -X * ((5:ℝ)/2) = -(5 / 2 * X) by ring]
  have hden : Real.exp (-(5 / 2 * X)) / 6 ≤ b ^ ((5 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow (by positivity) hb (by norm_num : (0:ℝ) ≤ (5:ℝ)/2)
    rw [hhalf] at h
    refine le_trans ?_ h
    have hsix := one_div_six_le_rpow
    have hexp : (0 : ℝ) < Real.exp (-(5 / 2 * X)) := Real.exp_pos _
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 6)]
    nlinarith
  have hden0 : (0 : ℝ) < b ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hbpos _
  have hmul : Real.exp (-(5 / 2 * X)) * Real.exp (5 / 2 * X) = 1 := by
    rw [← Real.exp_add]; simp
  rw [wgt, div_le_iff₀ hden0]
  nlinarith [Real.exp_pos (5 / 2 * X), hbpos]

/-! ### The geometric tail of the sum -/

lemma exp_mul_nat (x : ℝ) (n : ℕ) : Real.exp (x * (n : ℝ)) = Real.exp x ^ n := by
  rw [mul_comm, Real.exp_nat_mul]

variable {c γ : ℝ} {g : ℕ → ℝ}

lemma exp_neg_half_lt_one (hc : 0 < c) : Real.exp (-(c / 2)) < 1 := by
  have h0 : Real.exp (-(c / 2)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
  simpa using h0

/-- The termwise bound: the mass tail `e^{-cn}` beats the dilation `e^{γn}`
when `γ ≤ c/2`. -/
lemma eta_term_le (hgle : ∀ n, g n ≤ Real.exp (-(c * (n : ℝ)))) (hcomp : γ ≤ c / 2) (n : ℕ) :
    g n * Real.exp (γ * (n : ℝ)) ≤ Real.exp (-(c / 2) * (n : ℝ)) := by
  have hexp : (0 : ℝ) < Real.exp (γ * (n : ℝ)) := Real.exp_pos _
  have h1 : g n * Real.exp (γ * (n : ℝ))
      ≤ Real.exp (-(c * (n : ℝ))) * Real.exp (γ * (n : ℝ)) := by
    nlinarith [hgle n]
  refine h1.trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hprod : (0 : ℝ) ≤ (c / 2 - γ) * (n : ℝ) :=
    mul_nonneg (by linarith) (Nat.cast_nonneg n)
  nlinarith

/-- The dilated tail is summable as soon as the dilation `γ` is at most half
the mass rate `c`. -/
lemma summable_eta_tail (hc : 0 < c) (hg0 : ∀ n, 0 ≤ g n)
    (hgle : ∀ n, g n ≤ Real.exp (-(c * (n : ℝ)))) (hcomp : γ ≤ c / 2) :
    Summable fun n : ℕ => g n * Real.exp (γ * (n : ℝ)) := by
  have hmaj : Summable fun n : ℕ => Real.exp (-(c / 2) * (n : ℝ)) := by
    simp only [exp_mul_nat]
    exact summable_geometric_of_lt_one (Real.exp_pos _).le (exp_neg_half_lt_one hc)
  exact Summable.of_nonneg_of_le (fun n => mul_nonneg (hg0 n) (Real.exp_pos _).le)
    (eta_term_le hgle hcomp) hmaj

/-- The geometric sum of `thm:shape-eta`: a tail supported above `N`, with mass
rate `c` and dilation `γ ≤ c/2`, sums to at most
`(1-e^{-c/2})^{-1} e^{-cN/2}`. -/
theorem eta_tail_sum {N : ℕ} (hc : 0 < c) (hg0 : ∀ n, 0 ≤ g n)
    (hgle : ∀ n, g n ≤ Real.exp (-(c * (n : ℝ)))) (hgvan : ∀ n ≤ N, g n = 0)
    (hcomp : γ ≤ c / 2) :
    ∑' n : ℕ, g n * Real.exp (γ * (n : ℝ))
      ≤ (1 - Real.exp (-(c / 2)))⁻¹ * Real.exp (-(c / 2) * (N : ℝ)) := by
  have hsum := summable_eta_tail hc hg0 hgle hcomp
  have hlt1 := exp_neg_half_lt_one hc
  have hposr : (0 : ℝ) < 1 - Real.exp (-(c / 2)) := by linarith
  -- the first `N+1` terms vanish, so the sum is its own tail
  have hzero : ∑ i ∈ Finset.range (N + 1), g i * Real.exp (γ * (i : ℝ)) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [hgvan i (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi), zero_mul]
  have heq : ∑' n : ℕ, g n * Real.exp (γ * (n : ℝ))
      = ∑' k : ℕ, g (k + (N + 1)) * Real.exp (γ * ((k + (N + 1) : ℕ) : ℝ)) := by
    have hsplit := hsum.sum_add_tsum_nat_add (N + 1)
    linarith [hsplit, hzero]
  have hshift : Summable fun k : ℕ => g (k + (N + 1)) * Real.exp (γ * ((k + (N + 1) : ℕ) : ℝ)) :=
    (summable_nat_add_iff (N + 1)).mpr hsum
  have hgeo : Summable fun k : ℕ =>
      Real.exp (-(c / 2) * ((N : ℝ) + 1)) * Real.exp (-(c / 2)) ^ k :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hlt1).mul_left _
  have hterm : ∀ k : ℕ, g (k + (N + 1)) * Real.exp (γ * ((k + (N + 1) : ℕ) : ℝ))
      ≤ Real.exp (-(c / 2) * ((N : ℝ) + 1)) * Real.exp (-(c / 2)) ^ k := by
    intro k
    refine (eta_term_le hgle hcomp (k + (N + 1))).trans ?_
    rw [← exp_mul_nat, ← Real.exp_add]
    refine Real.exp_le_exp.mpr (le_of_eq ?_)
    push_cast
    ring
  rw [heq]
  refine (Summable.tsum_le_tsum hterm hshift hgeo).trans ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hlt1]
  have hmono : Real.exp (-(c / 2) * ((N : ℝ) + 1)) ≤ Real.exp (-(c / 2) * (N : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hinv : (0 : ℝ) ≤ (1 - Real.exp (-(c / 2)))⁻¹ := by positivity
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left hmono hinv

/-! ### The assembled bound -/

/-- **`thm:shape-eta`, the summation.** The `v₀`-term contributes `6e^{-cD²}`
and the remaining classes, grouped by the size of their members, contribute
`e^{3C₁}(1-e^{-c/2})^{-1}e^{-cD²/2}`. -/
theorem shape_eta_le {C₁ b₀ : ℝ} {D : ℕ} {bb : ℕ → ℝ}
    (hc : 0 < c) (hC₁ : 0 ≤ C₁)
    (hhalf : Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ 1 / 2)
    (hb₀ : 1 - Real.exp (-(c * ((D : ℝ) ^ 2))) ≤ b₀) (hb₀1 : b₀ ≤ 1)
    (hg0 : ∀ n, 0 ≤ g n) (hgle : ∀ n, g n ≤ Real.exp (-(c * (n : ℝ))))
    (hgvan : ∀ n ≤ D ^ 2, g n = 0)
    (hbb : ∀ n : ℕ, Real.exp (-(C₁ * ((n : ℝ) / Real.sqrt D + 1))) ≤ bb n)
    (hbb1 : ∀ n, bb n ≤ 1)
    (hcomp : 5 / 2 * C₁ / Real.sqrt D ≤ c / 2) :
    wgt b₀ + ∑' n : ℕ, g n * wgt (bb n)
      ≤ 6 * Real.exp (-(c * ((D : ℝ) ^ 2)))
        + Real.exp (3 * C₁) * ((1 - Real.exp (-(c / 2)))⁻¹
            * Real.exp (-(c / 2) * ((D : ℝ) ^ 2))) := by
  set γ : ℝ := 5 / 2 * C₁ / Real.sqrt D with hγ
  have hsqrt : (0 : ℝ) ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hbbpos : ∀ n, 0 < bb n := fun n => lt_of_lt_of_le (Real.exp_pos _) (hbb n)
  -- the `v₀`-term
  have hv₀ : wgt b₀ ≤ 6 * Real.exp (-(c * ((D : ℝ) ^ 2))) := by
    have hhalf' : (1 : ℝ) / 2 ≤ b₀ := by linarith
    exact (wgt_le_of_half hhalf' hb₀1).trans (by linarith)
  -- the remaining classes, termwise
  have hterm : ∀ n : ℕ,
      g n * wgt (bb n) ≤ Real.exp (3 * C₁) * (g n * Real.exp (γ * (n : ℝ))) := by
    intro n
    have hw := wgt_le_of_exp (hbb n)
    have hsplit : Real.exp (5 / 2 * (C₁ * ((n : ℝ) / Real.sqrt D + 1)))
        ≤ Real.exp (3 * C₁) * Real.exp (γ * (n : ℝ)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hidem : 5 / 2 * (C₁ * ((n : ℝ) / Real.sqrt D + 1))
          = 5 / 2 * C₁ / Real.sqrt D * (n : ℝ) + 5 / 2 * C₁ := by ring
      rw [hidem, hγ]
      linarith
    have hwle : wgt (bb n) ≤ Real.exp (3 * C₁) * Real.exp (γ * (n : ℝ)) := hw.trans hsplit
    nlinarith [hg0 n, wgt_nonneg (hbbpos n) (hbb1 n)]
  have hsum2 : Summable fun n : ℕ => Real.exp (3 * C₁) * (g n * Real.exp (γ * (n : ℝ))) :=
    (summable_eta_tail hc hg0 hgle hcomp).mul_left _
  have hsum1 : Summable fun n : ℕ => g n * wgt (bb n) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hg0 n) (wgt_nonneg (hbbpos n) (hbb1 n))) hterm hsum2
  have htail : ∑' n : ℕ, g n * wgt (bb n)
      ≤ Real.exp (3 * C₁) * ((1 - Real.exp (-(c / 2)))⁻¹
          * Real.exp (-(c / 2) * ((D : ℝ) ^ 2))) := by
    refine (Summable.tsum_le_tsum hterm hsum1 hsum2).trans ?_
    rw [tsum_mul_left]
    have hgeo := eta_tail_sum (N := D ^ 2) hc hg0 hgle hgvan hcomp
    have hcast : ((D ^ 2 : ℕ) : ℝ) = (D : ℝ) ^ 2 := by push_cast; ring
    rw [hcast] at hgeo
    have hpos : (0 : ℝ) < Real.exp (3 * C₁) := Real.exp_pos _
    exact mul_le_mul_of_nonneg_left hgeo hpos.le
  linarith

/-- **`thm:shape-eta`, the largeness step**: past a threshold `D₀` the two
contributions are absorbed into `e^{-cD²/4}`, which is `eq:shape-eta` after
renaming `c/4` to `c`. -/
theorem shape_eta_final {C₂ : ℝ} (hc : 0 < c) (hC₂ : 0 ≤ C₂) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      6 * Real.exp (-(c * ((D : ℝ) ^ 2))) + C₂ * Real.exp (-(c / 2) * ((D : ℝ) ^ 2))
        ≤ Real.exp (-(c / 4) * ((D : ℝ) ^ 2)) := by
  refine ⟨⌈(8 + 4 * C₂) / c⌉₊ + 1, fun D hD => ?_⟩
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by
    have h1 : 1 ≤ D := le_trans (Nat.le_add_left 1 _) hD
    exact_mod_cast h1
  have hDge : (8 + 4 * C₂) / c ≤ (D : ℝ) := by
    have h1 : ((⌈(8 + 4 * C₂) / c⌉₊ : ℕ) : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast le_trans (Nat.le_add_right _ 1) hD
    exact (Nat.le_ceil _).trans h1
  set Y : ℝ := c * (D : ℝ) ^ 2 with hY
  have hYge : 8 + 4 * C₂ ≤ Y := by
    have hlin : (8 + 4 * C₂) ≤ c * (D : ℝ) := by
      rw [div_le_iff₀ hc] at hDge; linarith
    have hDsq : (D : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
    rw [hY]
    nlinarith
  have hYpos : 0 < Y := by linarith
  -- `y e^{-y} ≤ 1` at the two rates
  have hkey : ∀ y : ℝ, 0 < y → y * Real.exp (-y) ≤ 1 := by
    intro y hy
    have h1 : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-y), mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-y)).le]
  set u : ℝ := Real.exp (-(3 * c / 4 * (D : ℝ) ^ 2)) with hu
  set v : ℝ := Real.exp (-(c / 4 * (D : ℝ) ^ 2)) with hv
  have hu0 : 0 < u := Real.exp_pos _
  have hv0 : 0 < v := Real.exp_pos _
  have hu1 : 3 * Y / 4 * u ≤ 1 := by
    have hk := hkey (3 * Y / 4) (by linarith)
    rwa [show -(3 * Y / 4) = -(3 * c / 4 * (D : ℝ) ^ 2) by rw [hY]; ring] at hk
  have hv1 : Y / 4 * v ≤ 1 := by
    have hk := hkey (Y / 4) (by linarith)
    rwa [show -(Y / 4) = -(c / 4 * (D : ℝ) ^ 2) by rw [hY]; ring] at hk
  have hbracket : 6 * u + C₂ * v ≤ 1 := by
    have h1 : 6 * u * Y ≤ 8 := by nlinarith
    have h2 : C₂ * v * Y ≤ 4 * C₂ := by nlinarith
    have h3 : (6 * u + C₂ * v) * Y ≤ 1 * Y := by nlinarith
    exact le_of_mul_le_mul_right h3 hYpos
  -- factor out `e^{-cD²/4}`
  have e1 : Real.exp (-(c * (D : ℝ) ^ 2)) = Real.exp (-(c / 4) * (D : ℝ) ^ 2) * u := by
    rw [hu, ← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-(c / 2) * (D : ℝ) ^ 2) = Real.exp (-(c / 4) * (D : ℝ) ^ 2) * v := by
    rw [hv, ← Real.exp_add]; congr 1; ring
  rw [e1, e2]
  have hexp : (0 : ℝ) < Real.exp (-(c / 4) * (D : ℝ) ^ 2) := Real.exp_pos _
  nlinarith

end ChainClasses
