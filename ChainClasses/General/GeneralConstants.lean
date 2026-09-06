import ChainClasses.Scalar.MarkedQI

/-!
The scalar constants of the general document: the comparability composition of the
transport relabelling and the constants of `it:general-hairy`.

* `markedQI_relabel` and `relabel_scale`: the comparability composition of the
  transport relabelling (`thm:relabel` of the general document), `27K₁³K₂` in
  general and `3¹⁵D¹⁶` at the net scales.
* `general_rate_to_one`, `relabel_glued_scale`, `cascade_depth` and
  `cascade_depth_le`: the constants of `it:general-hairy`.  The failure rates
  `K_ν̃ e^{-c₃D²}` fall below `ε_ν̃` past an explicit threshold, the gluing at
  `K = 3¹⁵D¹⁶` is an `8·3³⁰D³²`-quasi-isometry, and the forced cascade
  encoding a `k`-split has depth `⌈log₂ k⌉ ≤ ⌈log₂ b⌉`, so the padding of the
  assembly over `𝔹` is bounded in terms of `b` alone.
-/

namespace ChainClasses

/-! ### The relabelling composition of the general document -/

/-- **`thm:relabel`(ii)** of the general document: if `X` and `X'` reach
reference spaces `T`, `T'` by `K₁`-marked quasi-isometries and the references
are `K₂`-comparable, then `X` and `X'` are `27K₁³K₂`-comparable. -/
theorem markedQI_relabel {K₁ K₂ : ℝ} {X T T' X' : MarkedSpace} (h1 : 1 ≤ K₁) (h2 : 1 ≤ K₂)
    (hXT : MarkedQI K₁ X T) (hTT' : MarkedQI K₂ T T') (hX'T' : MarkedQI K₁ X' T') :
    MarkedQI (27 * K₁ ^ 3 * K₂) X X' := by
  have hc1 : (1 : ℝ) ≤ 3 * K₁ * K₂ := by nlinarith
  have hc2 : (1 : ℝ) ≤ 3 * K₁ ^ 2 := by nlinarith
  have h12 := markedQI_comp h1 h2 hXT hTT'
  have hsym := markedQI_symm h1 hX'T'
  have hfin := markedQI_comp hc1 hc2 h12 hsym
  have e : 3 * (3 * K₁ * K₂) * (3 * K₁ ^ 2) = 27 * K₁ ^ 3 * K₂ := by ring
  rwa [e] at hfin

/-- The constant of `thm:relabel`(ii) at the net scales: `K₁ = 9D³` from the
coupling support and `K₂ = 729D⁷` from equal-or-adjacent classes give
`3¹⁵D¹⁶`. -/
lemma relabel_scale (D : ℝ) :
    27 * (9 * D ^ 3) ^ 3 * (729 * D ^ 7) = 14348907 * D ^ 16 := by ring

/-! ### The constants of `it:general-hairy` -/

/-- **The last display of `thm:hairy` at general support**: the failure rates
`K_ν̃ e^{-c₃D²}` of `it:general-hairy` fall below any threshold, with the
explicit bound `D ≥ K_ν̃/(c₃ε) + 1`. -/
theorem general_rate_to_one {A c ε : ℝ} (hA : 0 < A) (hc : 0 < c) (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → A * Real.exp (-(c * (D : ℝ) ^ 2)) < ε := by
  refine ⟨⌈A / (c * ε)⌉₊ + 1, fun D hD => ?_⟩
  have hcast : ((⌈A / (c * ε)⌉₊ + 1 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  push_cast at hcast
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) ⌈A / (c * ε)⌉₊
    linarith
  have hlt : A / (c * ε) < (D : ℝ) := by
    have := Nat.le_ceil (A / (c * ε))
    linarith
  have hsq : (D : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
  have hDsq : (0 : ℝ) < (D : ℝ) ^ 2 := by nlinarith
  set y : ℝ := c * (D : ℝ) ^ 2 with hy
  have hypos : 0 < y := mul_pos hc hDsq
  have hkey : y * Real.exp (-y) ≤ 1 := by
    have h1 : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-y), mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-y)).le]
  have hylarge : A < y * ε := by
    have hce : 0 < c * ε := mul_pos hc hε
    rw [div_lt_iff₀ hce] at hlt
    rw [hy]
    nlinarith
  have hmul : y * (A * Real.exp (-y)) < y * ε := by nlinarith [Real.exp_pos (-y)]
  exact lt_of_mul_lt_mul_left hmul hypos.le

/-- The gluing scale of `it:general-hairy`: `thm:glued-transfer` applied at
the relabelling constant `K = 3¹⁵D¹⁶` gives an `8·3³⁰D³²`-quasi-isometry. -/
lemma relabel_glued_scale (D : ℝ) :
    8 * (14348907 * D ^ 16) ^ 2 = 8 * 14348907 ^ 2 * D ^ 32 := by ring

/-- **`it:general-hairy`, the cascade depth**: the forced cascade encoding a
`k`-split reaches `k` slots at depth `⌈log₂ k⌉`. -/
lemma cascade_depth (k : ℕ) : k ≤ 2 ^ Nat.clog 2 k :=
  Nat.le_pow_clog (by norm_num) k

/-- The depth is monotone in the arity, so over offspring bounded by `b` the
padding of the assembly is bounded by `⌈log₂ b⌉`, a constant of the law. -/
lemma cascade_depth_le {k b : ℕ} (h : k ≤ b) : Nat.clog 2 k ≤ Nat.clog 2 b :=
  Nat.clog_mono_right 2 h

end ChainClasses
