/-
The two maxima of `graph_matching_selfcontained.tex`, `eq:lambda-max` and `eq:kappa`.

`LA` and `KA` define the two maxima at an arbitrary exponent, as `eq:maxima` does,
and `le_LA`/`le_KA` give the only property the development asks of them: they
dominate their families on `[0,1]`.

The paper evaluates them at `α = 5/2`,

    L_α = max_{[0,1]} t/(1+t)^(5/2) = (2/3)/(5/3)^(5/2) = 6*sqrt 15/125,
    K_α = max_{[0,1]} t*(1-t)^(5/2) = (2/7)*(5/7)^(5/2),

but never uses either value: every downstream step goes through a rational
bound. So we prove only

    L_bound : t/(1+t)^alpha <= 14/75      (L_α = 0.185903...)
    K_bound : t*(1-t)^alpha <= 1/8        (K_α = 0.123200...)

with `LA_alpha_le` and `KA_alpha_le` transferring them to the maxima themselves.
This avoids `deriv`, any argmax, and `sqrt 15` / `sqrt (5/7)` entirely.

Choice of the two rationals. They are free parameters subject to the two
downstream uses:

  * `A = 2*L_α + 4*K_α < 7/8`  (`eq:one-step`):  2L + 4K < 7/8
  * the coefficient check after `eq:row-bound`, `2*L_α*C + 1/2 < 4` with
    `C = 28/3` from `Phi.lean`:                  L < 3.5*3/56 = 0.1875

`L = 14/75 = 0.18667` and `K = 1/8` satisfy both with room, giving
`A <= 28/75 + 1/2 = 0.87333 < 0.875` and `2L*C + 1/2 = 3.98444 < 4`, and they
leave the largest margin over the true maxima that those constraints allow.

Method. **Squaring** removes the `rpow`: `t*(1-t)^alpha <= K` becomes
`t^2*(1-t)^5 <= K^2`, and `t/(1+t)^alpha <= L` becomes `t^2 <= L^2*(1+t)^5`. Both
are then polynomial with rational coefficients, and neither is tangent (the minima
of the slacks are `0.00045` and `0.0037`), so `nlinarith` closes them given hints
at the critical points `t = 2/7` and `t = 2/3`. This works only because `2*alpha`
is the integer `5`; it is the reason the two rational bounds, and not the exact
maxima, are what the development carries.
-/
import GraphMatching.Phi

namespace GraphMatching

open Real Set

/-! ### The two maxima, `eq:maxima`

`eq:maxima` defines `L_α` and `K_α` as the maxima over `[0,1]` of `t/(1+t)^α` and
`t(1-t)^α`. Both families are bounded above by `1` there, so the suprema exist at
every `α ≥ 0` and dominate the family pointwise, which is all `eq:row-bound` and
`eq:kappa` ask of them. The exact values at `α = 5/2` are never used: every
downstream step goes through the rational bounds below. -/

/-- **`eq:maxima`**: `L_α = max_{0 ≤ t ≤ 1} t/(1+t)^α`. -/
noncomputable def LA (α : ℝ) : ℝ := sSup ((fun t : ℝ => t / (1 + t) ^ α) '' Icc 0 1)

/-- **`eq:maxima`**: `K_α = max_{0 ≤ t ≤ 1} t(1-t)^α`. -/
noncomputable def KA (α : ℝ) : ℝ := sSup ((fun t : ℝ => t * (1 - t) ^ α) '' Icc 0 1)

lemma nonempty_image_LA (α : ℝ) :
    ((fun t : ℝ => t / (1 + t) ^ α) '' Icc 0 1).Nonempty :=
  ⟨_, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩

lemma nonempty_image_KA (α : ℝ) :
    ((fun t : ℝ => t * (1 - t) ^ α) '' Icc 0 1).Nonempty :=
  ⟨_, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩

lemma bddAbove_image_LA {α : ℝ} (hα : 0 ≤ α) :
    BddAbove ((fun t : ℝ => t / (1 + t) ^ α) '' Icc 0 1) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  show t / (1 + t) ^ α ≤ 1
  have hone : (1 : ℝ) ≤ (1 + t) ^ α := by
    calc (1 : ℝ) = (1 : ℝ) ^ α := (Real.one_rpow α).symm
      _ ≤ (1 + t) ^ α := Real.rpow_le_rpow zero_le_one (by linarith [ht.1]) hα
  rw [div_le_one (by linarith)]
  linarith [ht.2]

lemma bddAbove_image_KA {α : ℝ} (hα : 0 ≤ α) :
    BddAbove ((fun t : ℝ => t * (1 - t) ^ α) '' Icc 0 1) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  show t * (1 - t) ^ α ≤ 1
  have hle : (1 - t) ^ α ≤ 1 := Real.rpow_le_one (by linarith [ht.2]) (by linarith [ht.1]) hα
  have hnn : (0 : ℝ) ≤ (1 - t) ^ α := Real.rpow_nonneg (by linarith [ht.2]) α
  nlinarith [ht.1, ht.2]

/-- `L_α` dominates its family: this is the only property of the maximum that
`eq:row-bound` uses. -/
lemma le_LA {α : ℝ} (hα : 0 ≤ α) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t / (1 + t) ^ α ≤ LA α :=
  le_csSup (bddAbove_image_LA hα) ⟨t, ⟨h0, h1⟩, rfl⟩

/-- `K_α` dominates its family, the property `eq:kappa` uses. -/
lemma le_KA {α : ℝ} (hα : 0 ≤ α) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t * (1 - t) ^ α ≤ KA α :=
  le_csSup (bddAbove_image_KA hα) ⟨t, ⟨h0, h1⟩, rfl⟩

/-- A uniform bound on the family bounds the maximum. -/
lemma LA_le {α c : ℝ} (h : ∀ t, 0 ≤ t → t ≤ 1 → t / (1 + t) ^ α ≤ c) : LA α ≤ c :=
  csSup_le (nonempty_image_LA α) (by rintro _ ⟨t, ht, rfl⟩; exact h t ht.1 ht.2)

lemma KA_le {α c : ℝ} (h : ∀ t, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ c) : KA α ≤ c :=
  csSup_le (nonempty_image_KA α) (by rintro _ ⟨t, ht, rfl⟩; exact h t ht.1 ht.2)

/-- **`eq:kappa`**, in the rational form the development needs:
`max_{t ∈ [0,1]} t·(1-t)^α ≤ 1/8`.

The exact maximum is `K_α = (2/7)(5/7)^{5/2} ≈ 0.12320`, attained at `t = 2/7`;
`1/8 = 0.125` bounds it with margin `0.0018`. -/
lemma K_bound {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t * (1 - t) ^ alpha ≤ 1 / 8 := by
  have hu : (0 : ℝ) ≤ 1 - t := by linarith
  have hX : 0 ≤ t * (1 - t) ^ alpha := mul_nonneg h0 (Real.rpow_nonneg hu alpha)
  have hsq : (t * (1 - t) ^ alpha) ^ (2 : ℕ) = t ^ 2 * (1 - t) ^ 5 := by
    rw [mul_pow, sq_rpow_alpha hu]
  -- the squared form: polynomial, minimum of the slack `0.00045` at `t = 2/7`
  have hpoly : t ^ 2 * (1 - t) ^ 5 ≤ 1 / 64 := by
    nlinarith [mul_nonneg (sq_nonneg (7 * t - 2)) (pow_nonneg hu 3),
      mul_nonneg (sq_nonneg (7 * t - 2)) (pow_nonneg hu 4),
      mul_nonneg (sq_nonneg (7 * t - 2)) (pow_nonneg hu 5),
      mul_nonneg (mul_nonneg h0 (sq_nonneg (7 * t - 2))) (pow_nonneg hu 3),
      sq_nonneg (7 * t - 2), h0, hu, pow_nonneg hu 5, mul_nonneg h0 hu]
  nlinarith [hX, hsq, hpoly]

/-- **`eq:lambda-max`**, in the rational form the development needs:
`t/(1+t)^α ≤ 14/75`.

The exact maximum is `L_α = (2/3)/(5/3)^{5/2} = 6√15/125 ≈ 0.18590`, attained at
`t = 2/3`; `14/75 ≈ 0.18667` bounds it with margin `0.00076`. The ceiling
`14/75 < 3/16` is forced by the coefficient check after `eq:row-bound`.

Note this needs only `0 ≤ t`, not `t ≤ 1`: the paper maximises over `[0,1]`,
but the bound holds on all of `[0,∞)`, since past `t = 2/3` the function
decreases. The `t ≤ 1` hypothesis is simply not used. -/
lemma L_bound {t : ℝ} (h0 : 0 ≤ t) : t / (1 + t) ^ alpha ≤ 14 / 75 := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hp : (0 : ℝ) < (1 + t) ^ alpha := Real.rpow_pos_of_pos h1t alpha
  have hX : 0 ≤ t / (1 + t) ^ alpha := div_nonneg h0 hp.le
  have hsq : (t / (1 + t) ^ alpha) ^ (2 : ℕ) = t ^ 2 / (1 + t) ^ 5 := by
    rw [div_pow, sq_rpow_alpha h1t.le]
  -- the squared form: polynomial, minimum of the slack `0.0037` at `t = 2/3`
  have hpoly : t ^ 2 / (1 + t) ^ 5 ≤ (14 / 75) ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + t) ^ 5)]
    nlinarith [sq_nonneg (3 * t - 2), h0, pow_nonneg h0 3,
      mul_nonneg h0 (sq_nonneg (3 * t - 2))]
  nlinarith [hX, hsq, hpoly]

/-- **`eq:lambda-max`** as a bound on the maximum itself: `L_{5/2} ≤ 14/75`. -/
lemma LA_alpha_le : LA alpha ≤ 14 / 75 := LA_le fun _ h0 _ => L_bound h0

/-- **`eq:kappa`** as a bound on the maximum itself: `K_{5/2} ≤ 1/8`. -/
lemma KA_alpha_le : KA alpha ≤ 1 / 8 := KA_le fun _ h0 h1 => K_bound h0 h1

/-! ### The contraction constants, `eq:contraction-constants` -/

/-- **`eq:contraction-constants`**: `M_α`, the product coefficient of `eq:row-bound`. It is
defined as the maximum of the two case coefficients, so `eq:row-bound` holds at every `α` with
no numeric input. -/
noncomputable def MA (α : ℝ) : ℝ := max (2 * LA α * chordConstA α + 1 / 2) (5 / 2)

/-- **`eq:contraction-constants`**: `A_α`, the linear coefficient of the contraction. -/
noncomputable def AA (α : ℝ) : ℝ := 2 * LA α + 4 * KA α

/-- **`eq:contraction-constants`**: `B_α`, the quadratic coefficient of the contraction. -/
noncomputable def BA (α : ℝ) : ℝ := MA α + 4 * α ^ 2

lemma LA_nonneg {α : ℝ} (hα : 0 ≤ α) : 0 ≤ LA α := by
  have := le_LA hα (le_refl (0:ℝ)) zero_le_one
  simpa using this

lemma KA_nonneg {α : ℝ} (hα : 0 ≤ α) : 0 ≤ KA α := by
  have := le_KA hα (le_refl (0:ℝ)) zero_le_one
  simpa using this

lemma case_one_le_MA (α : ℝ) : 2 * LA α * chordConstA α + 1 / 2 ≤ MA α := le_max_left _ _

lemma case_two_le_MA (α : ℝ) : (5 : ℝ) / 2 ≤ MA α := le_max_right _ _

lemma MA_nonneg (α : ℝ) : 0 ≤ MA α := le_trans (by norm_num) (case_two_le_MA α)

/-- The chord slope is nonnegative at every `α ≥ 0`. -/
lemma chordConstA_nonneg {α : ℝ} (hα : 0 ≤ α) : 0 ≤ chordConstA α := by
  rw [chordConstA]
  have h : (1 : ℝ) ≤ 2 ^ α := by
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
      _ ≤ (2 : ℝ) ^ α := (Real.rpow_le_rpow_left_iff (by norm_num)).mpr hα
  linarith

/-! ### The three constants at `α = 5/2`, `eq:constants-at-five-halves` -/

/-- `A_{5/2} ≤ 28/75 + 1/2 < 7/8`. -/
lemma AA_alpha_le : AA alpha ≤ 7 / 8 := by
  have hL := LA_alpha_le
  have hK := KA_alpha_le
  rw [AA]; linarith

/-- `M_{5/2} < 4`, from `2 L C + 1/2 ≤ 28/75 · 28/3 + 1/2` and `5/2 < 4`. -/
lemma MA_alpha_le : MA alpha ≤ 4 := by
  refine max_le ?_ (by norm_num)
  have hL := LA_alpha_le
  have hL0 := LA_nonneg alpha_nonneg
  have hC := chordConstA_alpha_le
  have hC0 := chordConstA_nonneg alpha_nonneg
  rw [chordConst] at hC
  nlinarith [hL, hL0, hC, hC0]

/-- `B_{5/2} = M_{5/2} + 25 ≤ 29`. -/
lemma BA_alpha_le : BA alpha ≤ 29 := by
  have hM := MA_alpha_le
  have : (4 : ℝ) * alpha ^ 2 = 25 := by norm_num [alpha]
  rw [BA, this]; linarith

end GraphMatching
