/-
The scalar threshold analysis of `arbitrary_offspring_matching.tex` (`sec:completion`,
"Completion of the proof"): the real forms of the explicit constants `S_H`, `G_H`,
`E(M)` and `Q(M)`, with their bridges to the `ℝ≥0∞` versions of `Paths.lean`, the
scalar upper bounds `Z̄(t)`, `Ē(t, M)`, `Q̄(t, M)` at the root bounds `δ ≤ ζ`,
`f ≤ (α+1) ζ`, `R_μ ≤ 1 + α ζ`, the monotone continuous threshold function `J_K` of
`eq:constructive-threshold` with its maximal admissible point `ε_K > 0`, the
zero-compatible quadratic `M_η` of `eq:zero-compatible-quadratic`, and the zero-compatible
threshold `ε⁰_K`.

* `SH`, `GH`, `Ereal`, `Qreal`: the real constants, with `SHe_eq_ofReal`, `GHe_ofReal`,
  `Efun_ofReal`, `Qfun_ofReal` and the monotonicity `Efun_mono`, `Qfun_mono`;
* `Zbar`, `Zbar_fixed`: the smaller root of `Z = S_H t + S_H T² Z²`, with `Z̄(t) ≤ 2 S_H t`;
* `Ebar`, `Qbar`, `JK`: the scalar bounds and the threshold function, with `JK_eq_div`,
  `JK_zero`, `JK_monotoneOn`, `JK_continuousOn`;
* `epsK`, `epsK_spec`, `barrier_of_le_epsK`: `eq:constructive-threshold` and the real
  barrier `t + (1 + (2α-1) t) Q̄(t, Kt) ≤ K t` on `[0, ε_K]`;
* `Meta`, `Meta_fixed`: `eq:zero-compatible-quadratic`;
* `JK0`, `epsK0`, `epsK0_spec`, `barrier0_of_le_epsK0`: the zero-compatible threshold.

Everything is pure real analysis; no model enters.
-/
import GraphMarkovMatching.Stopped.Paths
import GraphMarkovMatching.Stopped.Scalar

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support Model
open scoped ENNReal Classical

/-! ### The real constants `S_H` and `G_H` (`eq:explicit-zero-bound`,
`eq:explicit-weighted-error`) -/

/-- `S_H = 2^{H+1} - 1` (`eq:explicit-zero-bound`). -/
noncomputable def SH (H : ℕ) : ℝ := 2 ^ (H + 1) - 1

/-- `S_H = ∑_{d ≤ H} 2^d` (`eq:explicit-zero-bound`). -/
lemma SH_eq_sum (H : ℕ) : SH H = ∑ d ∈ Finset.range (H + 1), (2 : ℝ) ^ d := by
  induction H with
  | zero => norm_num [SH]
  | succ H ih =>
    rw [Finset.sum_range_succ, ← ih, SH, SH]
    ring

/-- `1 ≤ S_H` (`eq:explicit-zero-bound`). -/
lemma one_le_SH (H : ℕ) : 1 ≤ SH H := by
  unfold SH
  have h : (2 : ℝ) ≤ 2 ^ (H + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (H + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

/-- `0 < S_H`. -/
lemma SH_pos (H : ℕ) : 0 < SH H := lt_of_lt_of_le one_pos (one_le_SH H)

/-- The `ℝ≥0∞` constant `S_H` of `Paths.lean` is the real one (`eq:explicit-zero-bound`). -/
lemma SHe_eq_ofReal (H : ℕ) : SHe H = ENNReal.ofReal (SH H) := by
  rw [SH_eq_sum, SHe, ENNReal.ofReal_sum_of_nonneg (fun d _ => by positivity)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- `G_H(x) = ∑_{d ≤ H} x^d` (`eq:explicit-weighted-error`). -/
noncomputable def GH (H : ℕ) (x : ℝ) : ℝ := ∑ d ∈ Finset.range (H + 1), x ^ d

/-- The `ℝ≥0∞` function `G_H` of `Paths.lean` at a nonnegative real argument
(`eq:explicit-weighted-error`). -/
lemma GHe_ofReal (H : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    GHe H (ENNReal.ofReal x) = ENNReal.ofReal (GH H x) := by
  rw [GH, GHe, ENNReal.ofReal_sum_of_nonneg (fun d _ => pow_nonneg hx d)]
  exact Finset.sum_congr rfl fun d _ => (ENNReal.ofReal_pow hx d).symm

/-- `G_H` is nondecreasing on `[0, ∞)` (`sec:completion`). -/
lemma GH_mono (H : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : GH H x ≤ GH H y :=
  Finset.sum_le_sum fun d _ => pow_le_pow_left₀ hx hxy d

/-- `1 ≤ G_H(x)` for `x ≥ 0` (`eq:explicit-weighted-error`). -/
lemma one_le_GH (H : ℕ) {x : ℝ} (hx : 0 ≤ x) : 1 ≤ GH H x := by
  rw [GH, Finset.sum_range_succ', pow_zero]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun d _ => pow_nonneg hx _)

/-- `0 ≤ G_H(x)` for `x ≥ 0`. -/
lemma GH_nonneg (H : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ GH H x :=
  zero_le_one.trans (one_le_GH H hx)

/-- `G_H` is continuous (`sec:completion`). -/
lemma GH_continuous (H : ℕ) : Continuous (GH H) :=
  continuous_finsetSum _ fun d _ => continuous_pow d

/-! ### The real forms of `E(M)` and `Q(M)` (`eq:explicit-weighted-error`,
`sec:averaging`) -/

/-- The real form of `E(M)` of `eq:explicit-weighted-error`, with the root quantities
`f`, `R_μ` and the zero bound `Z` as parameters. -/
noncomputable def Ereal (α : ℝ) (H T : ℕ) (B f Rμ Z Mv : ℝ) : ℝ :=
  GH H (4 * B * Rμ * (1 + α * Mv))
    * (2 * B * (1 + α * Mv) ^ 2 * f + 2 * B * Rμ * (T * Z + α * Mv) ^ 2)

/-- `U(M) = 1 + α M` at a nonnegative real `M`. -/
lemma Ufun_ofReal {α : ℝ} (hα : 0 ≤ α) {Mv : ℝ} (hM : 0 ≤ Mv) :
    Ufun α (ENNReal.ofReal Mv) = ENNReal.ofReal (1 + α * Mv) := by
  rw [Ufun, ENNReal.ofReal_add zero_le_one (mul_nonneg hα hM), ENNReal.ofReal_one,
    ENNReal.ofReal_mul hα]

/-- The `ℝ≥0∞` bound `E(M)` of `Paths.lean` at nonnegative real arguments is the real one
(`eq:explicit-weighted-error`). -/
lemma Efun_ofReal (α : ℝ) (hα : 0 ≤ α) (H T : ℕ) {B f Rμ Z Mv : ℝ} (hB : 0 ≤ B)
    (hf : 0 ≤ f) (hR : 0 ≤ Rμ) (hZ : 0 ≤ Z) (hM : 0 ≤ Mv) :
    Efun α H T (ENNReal.ofReal B) (ENNReal.ofReal f) (ENNReal.ofReal Rμ) (ENNReal.ofReal Z)
        (ENNReal.ofReal Mv)
      = ENNReal.ofReal (Ereal α H T B f Rμ Z Mv) := by
  have hU : 0 ≤ 1 + α * Mv := by positivity
  have hαM : 0 ≤ α * Mv := mul_nonneg hα hM
  have hTZ : 0 ≤ (T : ℝ) * Z := mul_nonneg (Nat.cast_nonneg T) hZ
  rw [Efun, Ereal, Ufun_ofReal hα hM]
  have hG : 4 * ENNReal.ofReal B * ENNReal.ofReal Rμ * ENNReal.ofReal (1 + α * Mv)
      = ENNReal.ofReal (4 * B * Rμ * (1 + α * Mv)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have h1 : 2 * ENNReal.ofReal B * ENNReal.ofReal (1 + α * Mv) ^ 2 * ENNReal.ofReal f
      = ENNReal.ofReal (2 * B * (1 + α * Mv) ^ 2 * f) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_pow hU]
  have h2 : 2 * ENNReal.ofReal B * ENNReal.ofReal Rμ
        * ((T : ℝ≥0∞) * ENNReal.ofReal Z + ENNReal.ofReal α * ENNReal.ofReal Mv) ^ 2
      = ENNReal.ofReal (2 * B * Rμ * (T * Z + α * Mv) ^ 2) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add hTZ hαM, ENNReal.ofReal_mul hα,
      ENNReal.ofReal_mul (Nat.cast_nonneg T), ENNReal.ofReal_natCast]
  rw [hG, h1, h2, GHe_ofReal H (by positivity), ← ENNReal.ofReal_add (by positivity)
    (by positivity), ← ENNReal.ofReal_mul (GH_nonneg H (by positivity))]

/-- `E(M)` is nondecreasing in `B`, `f`, `R_μ`, `Z` and `M` (`sec:completion`: every
coefficient of `eq:explicit-weighted-error` is nonnegative). -/
lemma Efun_mono (α : ℝ) (H : ℕ) (T : ℝ≥0∞) {B B' f f' Rμ Rμ' Z Z' Mb Mb' : ℝ≥0∞}
    (hB : B ≤ B') (hf : f ≤ f') (hR : Rμ ≤ Rμ') (hZ : Z ≤ Z') (hM : Mb ≤ Mb') :
    Efun α H T B f Rμ Z Mb ≤ Efun α H T B' f' Rμ' Z' Mb' := by
  have hU : Ufun α Mb ≤ Ufun α Mb' := by
    unfold Ufun
    gcongr
  unfold Efun
  gcongr
  exact GHe_mono_left H (by gcongr)

/-- The real form of `Q(M) = a M + b M² + (γ + 4αM) Z + C (1 + αM) E` (`sec:averaging`). -/
noncomputable def Qreal (α a b γ C Z E Mv : ℝ) : ℝ :=
  a * Mv + b * Mv ^ 2 + (γ + 4 * α * Mv) * Z + C * (1 + α * Mv) * E

/-- The `ℝ≥0∞` bound `Q(M)` of `Paths.lean` at nonnegative real arguments is the real one
(`sec:averaging`). -/
lemma Qfun_ofReal (α : ℝ) (hα : 0 ≤ α) {a b γ C Z E Mv : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hγ : 0 ≤ γ) (hC : 0 ≤ C) (hZ : 0 ≤ Z) (hE : 0 ≤ E) (hM : 0 ≤ Mv) :
    Qfun α (ENNReal.ofReal a) (ENNReal.ofReal b) (ENNReal.ofReal γ) (ENNReal.ofReal C)
        (ENNReal.ofReal Z) (ENNReal.ofReal E) (ENNReal.ofReal Mv)
      = ENNReal.ofReal (Qreal α a b γ C Z E Mv) := by
  have hαM : 0 ≤ α * Mv := mul_nonneg hα hM
  rw [Qfun, Qreal]
  have h1 : ENNReal.ofReal a * ENNReal.ofReal Mv = ENNReal.ofReal (a * Mv) :=
    (ENNReal.ofReal_mul ha).symm
  have h2 : ENNReal.ofReal b * ENNReal.ofReal Mv ^ 2 = ENNReal.ofReal (b * Mv ^ 2) := by
    rw [ENNReal.ofReal_mul hb, ENNReal.ofReal_pow hM]
  have h3 : (ENNReal.ofReal γ + 4 * ENNReal.ofReal α * ENNReal.ofReal Mv) * ENNReal.ofReal Z
      = ENNReal.ofReal ((γ + 4 * α * Mv) * Z) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add hγ (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat]
  have h4 : ENNReal.ofReal C * (1 + ENNReal.ofReal α * ENNReal.ofReal Mv) * ENNReal.ofReal E
      = ENNReal.ofReal (C * (1 + α * Mv) * E) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hC,
      ENNReal.ofReal_add zero_le_one hαM, ENNReal.ofReal_one, ENNReal.ofReal_mul hα]
  rw [h1, h2, h3, h4, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- `Q(M)` is nondecreasing in `Z`, `E` and `M` (`sec:completion`). -/
lemma Qfun_mono (α : ℝ) (a b γ C : ℝ≥0∞) {Z Z' E E' Mb Mb' : ℝ≥0∞} (hZ : Z ≤ Z')
    (hE : E ≤ E') (hM : Mb ≤ Mb') :
    Qfun α a b γ C Z E Mb ≤ Qfun α a b γ C Z' E' Mb' := by
  unfold Qfun
  gcongr

/-! ### The scalar zero bound `Z̄(t)` (`sec:completion`) -/

/-- `Z̄(t) = 2 S_H t/(1 + √(1 - 4 S_H² T² t))` (`sec:completion`). -/
noncomputable def Zbar (H T : ℕ) (t : ℝ) : ℝ :=
  2 * SH H * t / (1 + Real.sqrt (1 - 4 * SH H ^ 2 * T ^ 2 * t))

/-- `Z̄(t)/t = 2 S_H/(1 + √(1 - 4 S_H² T² t))` (`sec:completion`). -/
noncomputable def ZbarQ (H T : ℕ) (t : ℝ) : ℝ :=
  2 * SH H / (1 + Real.sqrt (1 - 4 * SH H ^ 2 * T ^ 2 * t))

/-- `Z̄(t) = t · Z̄(t)/t`. -/
lemma Zbar_eq_mul (H T : ℕ) (t : ℝ) : Zbar H T t = t * ZbarQ H T t := by
  unfold Zbar ZbarQ
  ring

/-- The denominator of `Z̄` is at least one. -/
lemma one_le_Zden (H T : ℕ) (t : ℝ) : 1 ≤ 1 + Real.sqrt (1 - 4 * SH H ^ 2 * T ^ 2 * t) :=
  le_add_of_nonneg_right (Real.sqrt_nonneg _)

/-- The denominator of `Z̄` is positive. -/
lemma Zden_pos (H T : ℕ) (t : ℝ) : 0 < 1 + Real.sqrt (1 - 4 * SH H ^ 2 * T ^ 2 * t) :=
  lt_of_lt_of_le one_pos (one_le_Zden H T t)

/-- `0 ≤ Z̄(t)/t`. -/
lemma ZbarQ_nonneg (H T : ℕ) (t : ℝ) : 0 ≤ ZbarQ H T t :=
  div_nonneg (by linarith [SH_pos H]) (Zden_pos H T t).le

/-- `0 ≤ Z̄(t)` for `t ≥ 0` (`sec:completion`). -/
lemma Zbar_nonneg (H T : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Zbar H T t := by
  rw [Zbar_eq_mul]
  exact mul_nonneg ht (ZbarQ_nonneg H T t)

/-- `Z̄(t)` is the smaller root of `Z = S_H t + S_H T² Z²` when `4 S_H² T² t ≤ 1`
(`sec:completion`). -/
theorem Zbar_fixed (H T : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : 4 * SH H ^ 2 * T ^ 2 * t ≤ 1) :
    SH H * (t + (T : ℝ) ^ 2 * Zbar H T t ^ 2) = Zbar H T t := by
  -- `ht0` belongs to the interface; the identity needs only the discriminant condition
  have _ := ht0
  set s := Real.sqrt (1 - 4 * SH H ^ 2 * T ^ 2 * t) with hs_def
  have hs : s ^ 2 = 1 - 4 * SH H ^ 2 * T ^ 2 * t := Real.sq_sqrt (by linarith)
  have hden : 0 < 1 + s := Zden_pos H T t
  have key : Zbar H T t * (1 + s) = 2 * SH H * t := by
    rw [Zbar, ← hs_def]
    exact div_mul_cancel₀ _ hden.ne'
  have h : (1 + s) ^ 2 * (SH H * (t + (T : ℝ) ^ 2 * Zbar H T t ^ 2) - Zbar H T t) = 0 := by
    linear_combination
      (SH H * (T : ℝ) ^ 2 * (Zbar H T t * (1 + s) + 2 * SH H * t) - (1 + s)) * key
        + SH H * t * hs
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1) hden.ne'
  · linarith

/-- `Z̄(t) ≤ 2 S_H t` (`sec:completion`). -/
theorem Zbar_le_two (H T : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : 4 * SH H ^ 2 * T ^ 2 * t ≤ 1) :
    Zbar H T t ≤ 2 * SH H * t := by
  -- `ht` belongs to the interface; the bound holds for every `t ≥ 0`
  have _ := ht
  unfold Zbar
  exact div_le_self (by linarith [mul_nonneg (SH_pos H).le ht0]) (one_le_Zden H T t)

/-- `t ≤ Z̄(t)` (`sec:completion`: `Z̄(t) ≥ S_H t ≥ t`). -/
theorem le_Zbar (H T : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : 4 * SH H ^ 2 * T ^ 2 * t ≤ 1) :
    t ≤ Zbar H T t := by
  -- `ht` belongs to the interface; the bound holds for every `t ≥ 0`
  have _ := ht
  have hs1 : Real.sqrt (1 - 4 * SH H ^ 2 * T ^ 2 * t) ≤ 1 := by
    rw [Real.sqrt_le_one]
    have : 0 ≤ 4 * SH H ^ 2 * T ^ 2 * t := by positivity
    linarith
  have hden : 0 < 1 + Real.sqrt (1 - 4 * SH H ^ 2 * T ^ 2 * t) := Zden_pos H T t
  unfold Zbar
  rw [le_div_iff₀ hden]
  nlinarith [one_le_SH H, mul_nonneg ht0 (sub_nonneg.mpr hs1)]

/-- `Z̄(t)/t` is nondecreasing (`sec:completion`): the denominator decreases. -/
lemma ZbarQ_mono' (H T : ℕ) {t t' : ℝ} (htt : t ≤ t') : ZbarQ H T t ≤ ZbarQ H T t' := by
  unfold ZbarQ
  refine div_le_div_of_nonneg_left (by linarith [SH_pos H]) (Zden_pos H T t') ?_
  have : 4 * SH H ^ 2 * T ^ 2 * t ≤ 4 * SH H ^ 2 * T ^ 2 * t' :=
    mul_le_mul_of_nonneg_left htt (by positivity)
  have := Real.sqrt_le_sqrt (show 1 - 4 * SH H ^ 2 * T ^ 2 * t' ≤ 1 - 4 * SH H ^ 2 * T ^ 2 * t
    by linarith)
  linarith

/-- `Z̄(t)/t` is nondecreasing on `[0, t_*]` (`sec:completion`). -/
theorem ZbarQ_mono (H T : ℕ) {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t')
    (ht' : 4 * SH H ^ 2 * T ^ 2 * t' ≤ 1) : ZbarQ H T t ≤ ZbarQ H T t' := by
  -- `ht` and `ht'` belong to the interface; monotonicity holds on the whole line
  have _ := ht
  have _ := ht'
  exact ZbarQ_mono' H T htt

/-- `Z̄(t)/t` is continuous (`sec:completion`). -/
lemma ZbarQ_continuous (H T : ℕ) : Continuous (ZbarQ H T) := by
  unfold ZbarQ
  refine Continuous.div continuous_const ?_ fun t => (Zden_pos H T t).ne'
  exact continuous_const.add (Real.continuous_sqrt.comp (by fun_prop))

/-- `Z̄(t)/t` is continuous on `[0, 1/(4 S_H² T²)]` (`sec:completion`). -/
theorem ZbarQ_continuousOn (H T : ℕ) :
    ContinuousOn (ZbarQ H T) (Set.Icc 0 (1 / (4 * SH H ^ 2 * T ^ 2))) :=
  (ZbarQ_continuous H T).continuousOn

/-- `Z̄(t)/t = S_H` at `t = 0` (`sec:completion`: `Z̄(t) = S_H t + O(t²)`). -/
lemma ZbarQ_zero (H T : ℕ) : ZbarQ H T 0 = SH H := by
  unfold ZbarQ
  rw [mul_zero, sub_zero, Real.sqrt_one]
  ring

/-! ### The scalar bounds `Ē(t, M)`, `Q̄(t, M)` and the threshold function `J_K`
(`sec:completion`) -/

/-- `Ē(t, M) = E(M)` at the root bounds `f = (α+1) t`, `R_μ = 1 + α t`, `Z = Z̄(t)`
(`sec:completion`). -/
noncomputable def Ebar (α : ℝ) (H T : ℕ) (B t Mv : ℝ) : ℝ :=
  Ereal α H T B ((α + 1) * t) (1 + α * t) (Zbar H T t) Mv

/-- `Ē(t, Kt)/t`, written without division (`sec:completion`). -/
noncomputable def EbarQ (α : ℝ) (H T : ℕ) (B t Kc : ℝ) : ℝ :=
  GH H (4 * B * (1 + α * t) * (1 + α * (Kc * t)))
    * (2 * B * (1 + α * (Kc * t)) ^ 2 * (α + 1)
      + 2 * B * (1 + α * t) * t * (T * ZbarQ H T t + α * Kc) ^ 2)

/-- `Ē(t, Kt) = t · Ē(t, Kt)/t`, for every `t` (`sec:completion`). -/
lemma Ebar_eq_mul (α : ℝ) (H T : ℕ) (B t Kc : ℝ) :
    Ebar α H T B t (Kc * t) = t * EbarQ α H T B t Kc := by
  unfold Ebar Ereal EbarQ
  rw [Zbar_eq_mul]
  ring

/-- `Q̄(t, M) = Q(M)` at `Z = Z̄(t)`, `E = Ē(t, M)` (`sec:completion`). -/
noncomputable def Qbar (α a b γ C : ℝ) (H T : ℕ) (B t Mv : ℝ) : ℝ :=
  Qreal α a b γ C (Zbar H T t) (Ebar α H T B t Mv) Mv

/-- `A_0 = γ S_H + 2 C B (α+1) G_H(4B)` (`sec:completion`). -/
noncomputable def A0 (α γ C : ℝ) (H : ℕ) (B : ℝ) : ℝ :=
  γ * SH H + 2 * C * B * (α + 1) * GH H (4 * B)

/-- `K_0 = (1 + A_0)/(1 - a)` (`sec:completion`). -/
noncomputable def K0 (a A : ℝ) : ℝ := (1 + A) / (1 - a)

/-- `K_match = K + 2 S_H` (`sec:completion`). -/
noncomputable def Kmatch (H : ℕ) (Kc : ℝ) : ℝ := Kc + 2 * SH H

/-- `t_* = min{1/(4 S_H² T²), 1/(2 K_match)}` (`sec:completion`). -/
noncomputable def tstar (H T : ℕ) (Kc : ℝ) : ℝ :=
  min (1 / (4 * SH H ^ 2 * T ^ 2)) (1 / (2 * Kmatch H Kc))

/-- `J_K(t)` of `eq:constructive-threshold`, in the division-free form
`1 + (1 + (2α-1)t)[aK + bK²t + (γ + 4αKt) Z̄(t)/t + C(1 + αKt) Ē(t,Kt)/t]`. -/
noncomputable def JK (α a b γ C : ℝ) (H T : ℕ) (B Kc t : ℝ) : ℝ :=
  1 + (1 + (2 * α - 1) * t)
    * (a * Kc + b * Kc ^ 2 * t + (γ + 4 * α * Kc * t) * ZbarQ H T t
      + C * (1 + α * Kc * t) * EbarQ α H T B t Kc)

/-- The barrier expression is `t · J_K(t)`, for every `t` (`sec:completion`). -/
lemma barrier_eq_mul_JK (α a b γ C : ℝ) (H T : ℕ) (B Kc t : ℝ) :
    t + (1 + (2 * α - 1) * t) * Qbar α a b γ C H T B t (Kc * t)
      = t * JK α a b γ C H T B Kc t := by
  unfold Qbar Qreal JK
  rw [Zbar_eq_mul, Ebar_eq_mul]
  ring

/-- `J_K(t) = (t + [1 + (2α-1)t] Q̄(t, Kt))/t` for `t > 0` (`eq:constructive-threshold`). -/
theorem JK_eq_div (α a b γ C : ℝ) (H T : ℕ) (B Kc : ℝ) {t : ℝ} (ht : 0 < t) :
    JK α a b γ C H T B Kc t
      = (t + (1 + (2 * α - 1) * t) * Qbar α a b γ C H T B t (Kc * t)) / t := by
  rw [barrier_eq_mul_JK, mul_div_cancel_left₀ _ ht.ne']

/-- `J_K(0) = 1 + aK + A_0` (`sec:completion`). -/
theorem JK_zero (α a b γ C : ℝ) (H T : ℕ) (B Kc : ℝ) :
    JK α a b γ C H T B Kc 0 = 1 + a * Kc + A0 α γ C H B := by
  unfold JK EbarQ A0
  rw [ZbarQ_zero]
  simp only [mul_zero, add_zero, mul_one, zero_mul]
  ring

/-! ### Monotonicity and continuity of `J_K` (`sec:completion`) -/

/-- `0 ≤ Ē(t, Kt)/t` for `t ≥ 0`. -/
lemma EbarQ_nonneg {α : ℝ} (hα : 0 ≤ α) (H T : ℕ) {B Kc t : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ Kc)
    (ht : 0 ≤ t) : 0 ≤ EbarQ α H T B t Kc := by
  have hZ := ZbarQ_nonneg H T t
  unfold EbarQ
  exact mul_nonneg (GH_nonneg H (by positivity)) (by positivity)

/-- `Ē(t, Kt)/t` is nondecreasing on `[0, ∞)` (`sec:completion`: after substituting
`M = Kt`, every factor is nonnegative and nondecreasing). -/
lemma EbarQ_mono {α : ℝ} (hα : 0 ≤ α) (H T : ℕ) {B Kc t t' : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ Kc)
    (ht : 0 ≤ t) (htt : t ≤ t') : EbarQ α H T B t Kc ≤ EbarQ α H T B t' Kc := by
  have ht' : 0 ≤ t' := ht.trans htt
  have hZ := ZbarQ_mono' H T htt
  have hZ0 := ZbarQ_nonneg H T t
  have hZ0' := ZbarQ_nonneg H T t'
  have hX : 4 * B * (1 + α * t) * (1 + α * (Kc * t))
      ≤ 4 * B * (1 + α * t') * (1 + α * (Kc * t')) := by gcongr
  have hY : 2 * B * (1 + α * (Kc * t)) ^ 2 * (α + 1)
        + 2 * B * (1 + α * t) * t * (T * ZbarQ H T t + α * Kc) ^ 2
      ≤ 2 * B * (1 + α * (Kc * t')) ^ 2 * (α + 1)
        + 2 * B * (1 + α * t') * t' * (T * ZbarQ H T t' + α * Kc) ^ 2 := by gcongr
  unfold EbarQ
  exact mul_le_mul (GH_mono H (by positivity) hX) hY (by positivity)
    (GH_nonneg H (by positivity))

/-- `Ē(t, Kt)/t` is continuous in `t` (`sec:completion`). -/
lemma EbarQ_continuous (α : ℝ) (H T : ℕ) (B Kc : ℝ) :
    Continuous (fun t => EbarQ α H T B t Kc) := by
  have hG : Continuous (fun t : ℝ => GH H (4 * B * (1 + α * t) * (1 + α * (Kc * t)))) :=
    (GH_continuous H).comp (by fun_prop)
  have hZ := ZbarQ_continuous H T
  unfold EbarQ
  fun_prop

/-- `J_K` is nondecreasing on `[0, ∞)` (`sec:completion`: every factor in the explicit
expression is nonnegative and nondecreasing). -/
lemma JK_mono_of_le {α a b γ C : ℝ} (hα : 1 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (hC : 0 ≤ C) (H T : ℕ) {B Kc t t' : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ Kc) (ht : 0 ≤ t)
    (htt : t ≤ t') : JK α a b γ C H T B Kc t ≤ JK α a b γ C H T B Kc t' := by
  have hα0 : 0 ≤ α := by linarith
  have h2α : 0 ≤ 2 * α - 1 := by linarith
  have ht' : 0 ≤ t' := ht.trans htt
  have hZ := ZbarQ_mono' H T htt
  have hZ0 := ZbarQ_nonneg H T t
  have hZ0' := ZbarQ_nonneg H T t'
  have hE := EbarQ_mono hα0 H T hB hK ht htt
  have hE0 := EbarQ_nonneg hα0 H T hB hK ht
  have hE0' := EbarQ_nonneg hα0 H T hB hK ht'
  have hA : 1 + (2 * α - 1) * t ≤ 1 + (2 * α - 1) * t' := by gcongr
  have hA0 : 0 ≤ 1 + (2 * α - 1) * t := by positivity
  have hA0' : 0 ≤ 1 + (2 * α - 1) * t' := by positivity
  have hS : a * Kc + b * Kc ^ 2 * t + (γ + 4 * α * Kc * t) * ZbarQ H T t
        + C * (1 + α * Kc * t) * EbarQ α H T B t Kc
      ≤ a * Kc + b * Kc ^ 2 * t' + (γ + 4 * α * Kc * t') * ZbarQ H T t'
        + C * (1 + α * Kc * t') * EbarQ α H T B t' Kc := by gcongr
  have hS0 : 0 ≤ a * Kc + b * Kc ^ 2 * t + (γ + 4 * α * Kc * t) * ZbarQ H T t
      + C * (1 + α * Kc * t) * EbarQ α H T B t Kc := by positivity
  unfold JK
  exact add_le_add le_rfl (mul_le_mul hA hS hS0 hA0')

/-- `J_K` is nondecreasing on `[0, 1/(4 S_H² T²)]` (`sec:completion`). -/
theorem JK_monotoneOn {α a b γ C : ℝ} (hα : 1 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (hC : 0 ≤ C) {H T : ℕ} {B Kc : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ Kc) (hT : 1 ≤ T) :
    MonotoneOn (JK α a b γ C H T B Kc) (Set.Icc 0 (1 / (4 * SH H ^ 2 * T ^ 2))) := by
  -- `hT` belongs to the interface; monotonicity holds on all of `[0, ∞)`
  have _ := hT
  intro t ht t' _ htt
  exact JK_mono_of_le hα ha hb hγ hC H T hB hK ht.1 htt

/-- `J_K` is continuous (`sec:completion`). -/
lemma JK_continuous (α a b γ C : ℝ) (H T : ℕ) (B Kc : ℝ) :
    Continuous (JK α a b γ C H T B Kc) := by
  have hZ := ZbarQ_continuous H T
  have hE := EbarQ_continuous α H T B Kc
  unfold JK
  fun_prop

/-- `J_K` is continuous on `[0, 1/(4 S_H² T²)]` (`sec:completion`). -/
theorem JK_continuousOn {α a b γ C : ℝ} (hα : 1 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (hC : 0 ≤ C) {H T : ℕ} {B Kc : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ Kc) (hT : 1 ≤ T) :
    ContinuousOn (JK α a b γ C H T B Kc) (Set.Icc 0 (1 / (4 * SH H ^ 2 * T ^ 2))) := by
  -- the hypotheses belong to the interface; `J_K` is continuous on the whole line
  have _ := hα
  have _ := ha
  have _ := hb
  have _ := hγ
  have _ := hC
  have _ := hB
  have _ := hK
  have _ := hT
  exact (JK_continuous α a b γ C H T B Kc).continuousOn

/-! ### The maximal admissible point (`eq:constructive-threshold`) -/

/-- The maximal point of `[0, t_*]` at which a continuous function, nondecreasing on
`[0, ∞)` and below the level `K` at `0`, stays at most `K`: it is positive, at most `t_*`,
and the function is at most `K` on the whole interval up to it
(`eq:constructive-threshold`). -/
lemma sSup_admissible_spec {J : ℝ → ℝ} {Kc tst : ℝ} (hcont : Continuous J)
    (hmono : ∀ t t', 0 ≤ t → t ≤ t' → J t ≤ J t') (htst : 0 < tst) (h0 : J 0 < Kc) :
    0 < sSup {t | t ∈ Set.Icc 0 tst ∧ J t ≤ Kc}
      ∧ sSup {t | t ∈ Set.Icc 0 tst ∧ J t ≤ Kc} ≤ tst
      ∧ ∀ t ∈ Set.Icc 0 (sSup {t | t ∈ Set.Icc 0 tst ∧ J t ≤ Kc}), J t ≤ Kc := by
  set S := {t | t ∈ Set.Icc 0 tst ∧ J t ≤ Kc} with hS_def
  have hbdd : BddAbove S := ⟨tst, fun t ht => ht.1.2⟩
  have hne : S.Nonempty := ⟨0, ⟨le_rfl, htst.le⟩, h0.le⟩
  have hclosed : IsClosed S :=
    IsClosed.inter isClosed_Icc (isClosed_le hcont continuous_const)
  have hmem : sSup S ∈ S := hclosed.csSup_mem hne hbdd
  have hpos : 0 < sSup S := by
    have hev : ∀ᶠ t in nhds (0 : ℝ), J t < Kc :=
      hcont.continuousAt.eventually_lt continuousAt_const h0
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hev
    have hmin : 0 < min (δ / 2) tst := lt_min (by positivity) htst
    have ht0 : min (δ / 2) tst ∈ S := by
      refine ⟨⟨hmin.le, min_le_right _ _⟩, (hδ' ?_).le⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hmin.le]
      calc min (δ / 2) tst ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith
    exact lt_of_lt_of_le hmin (le_csSup hbdd ht0)
  exact ⟨hpos, hmem.1.2, fun t ht => (hmono t (sSup S) ht.1 ht.2).trans hmem.2⟩

/-- `ε_K = max{t ∈ [0, t_*] : J_K(t) ≤ K}` (`eq:constructive-threshold`). -/
noncomputable def epsK (α a b γ C : ℝ) (H T : ℕ) (B Kc : ℝ) : ℝ :=
  sSup {t | t ∈ Set.Icc 0 (tstar H T Kc) ∧ JK α a b γ C H T B Kc t ≤ Kc}

/-- `0 ≤ A_0` (`sec:completion`). -/
lemma A0_nonneg {α γ C : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hC : 0 ≤ C) (H : ℕ) {B : ℝ}
    (hB : 0 ≤ B) : 0 ≤ A0 α γ C H B := by
  have := SH_pos H
  have := GH_nonneg H (x := 4 * B) (by positivity)
  unfold A0
  positivity

/-- `0 < K_0` (`sec:completion`). -/
theorem K0_pos {a A : ℝ} (ha1 : a < 1) (hA : 0 ≤ A) : 0 < K0 a A :=
  div_pos (by linarith) (by linarith)

/-- `0 < K_match` (`sec:completion`). -/
theorem Kmatch_pos {H : ℕ} {Kc : ℝ} (hK : 0 < Kc) : 0 < Kmatch H Kc := by
  unfold Kmatch
  linarith [SH_pos H]

/-- `0 < t_*` (`sec:completion`). -/
theorem tstar_pos {H T : ℕ} {Kc : ℝ} (hK : 0 < Kc) (hT : 1 ≤ T) : 0 < tstar H T Kc := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have := SH_pos H
  have := Kmatch_pos (H := H) hK
  unfold tstar
  exact lt_min (by positivity) (by positivity)

/-- `t ≤ t_*` gives the two conditions `4 S_H² T² t ≤ 1` and `2 K_match t ≤ 1`
(`sec:completion`). -/
theorem le_tstar_imp {H T : ℕ} {Kc t : ℝ} (hK : 0 < Kc) (hT : 1 ≤ T)
    (ht : t ≤ tstar H T Kc) :
    4 * SH H ^ 2 * T ^ 2 * t ≤ 1 ∧ 2 * Kmatch H Kc * t ≤ 1 := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hS := SH_pos H
  have hKm := Kmatch_pos (H := H) hK
  have h1 : t ≤ 1 / (4 * SH H ^ 2 * T ^ 2) := ht.trans (min_le_left _ _)
  have h2 : t ≤ 1 / (2 * Kmatch H Kc) := ht.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at h1 h2
  constructor
  · linarith
  · linarith

/-- `J_K(0) < K` for `K > K_0` (`sec:completion`). -/
lemma JK_zero_lt {α a b γ C : ℝ} (ha1 : a < 1) (H T : ℕ) {B Kc : ℝ}
    (hK : K0 a (A0 α γ C H B) < Kc) : JK α a b γ C H T B Kc 0 < Kc := by
  rw [JK_zero]
  unfold K0 at hK
  rw [div_lt_iff₀ (by linarith)] at hK
  linarith

/-- **`eq:constructive-threshold`**: `ε_K > 0`, `ε_K ≤ t_*`, and `J_K ≤ K` on `[0, ε_K]`. -/
theorem epsK_spec {α a b γ C : ℝ} (hα : 1 ≤ α) (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hγ : 0 ≤ γ) (hC : 0 ≤ C) {H T : ℕ} {B Kc : ℝ} (hB : 1 ≤ B) (hT : 1 ≤ T)
    (hK : K0 a (A0 α γ C H B) < Kc) :
    0 < epsK α a b γ C H T B Kc ∧ epsK α a b γ C H T B Kc ≤ tstar H T Kc
      ∧ ∀ t ∈ Set.Icc 0 (epsK α a b γ C H T B Kc), JK α a b γ C H T B Kc t ≤ Kc := by
  have hB0 : 0 ≤ B := by linarith
  have hKpos : 0 < Kc := (K0_pos ha1 (A0_nonneg (by linarith) hγ hC H hB0)).trans hK
  exact sSup_admissible_spec (JK_continuous α a b γ C H T B Kc)
    (fun t t' ht htt => JK_mono_of_le hα ha0 hb hγ hC H T hB0 hKpos.le ht htt)
    (tstar_pos hKpos hT) (JK_zero_lt ha1 H T hK)

/-- The barrier in real form (`sec:completion`): for `0 ≤ t ≤ ε_K`,
`t + (1 + (2α-1) t) Q̄(t, Kt) ≤ K t`. -/
theorem barrier_of_le_epsK {α a b γ C : ℝ} (hα : 1 ≤ α) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb : 0 ≤ b) (hγ : 0 ≤ γ) (hC : 0 ≤ C) {H T : ℕ} {B Kc : ℝ} (hB : 1 ≤ B) (hT : 1 ≤ T)
    (hK : K0 a (A0 α γ C H B) < Kc) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ epsK α a b γ C H T B Kc) :
    t + (1 + (2 * α - 1) * t) * Qbar α a b γ C H T B t (Kc * t) ≤ Kc * t := by
  have hJ := (epsK_spec hα ha0 ha1 hb hγ hC hB hT hK).2.2 t ⟨ht0, ht⟩
  rw [barrier_eq_mul_JK, mul_comm Kc t]
  exact mul_le_mul_of_nonneg_left hJ ht0

/-! ### The zero-compatible quadratic (`eq:zero-compatible-quadratic`) -/

/-- The zero-compatible quadratic `M_η = 2η/(1 - da + √((1-da)² - 4dbη))` of
`eq:zero-compatible-quadratic`. -/
noncomputable def Meta (a b d η : ℝ) : ℝ :=
  2 * η / (1 - d * a + Real.sqrt ((1 - d * a) ^ 2 - 4 * d * b * η))

/-- The denominator of `M_η` is positive when `da < 1`. -/
lemma Meta_den_pos {a b d η : ℝ} (h1 : d * a < 1) :
    0 < 1 - d * a + Real.sqrt ((1 - d * a) ^ 2 - 4 * d * b * η) := by
  have := Real.sqrt_nonneg ((1 - d * a) ^ 2 - 4 * d * b * η)
  linarith

/-- `M_η` is the smallest nonnegative solution of `M = η + d(aM + bM²)`
(`eq:zero-compatible-quadratic`). -/
theorem Meta_fixed {a b d η : ℝ} (hη : 0 ≤ η) (hd : 0 ≤ d) (hb : 0 ≤ b) (h1 : d * a < 1)
    (h2 : 4 * d * b * η ≤ (1 - d * a) ^ 2) :
    η + d * (a * Meta a b d η + b * Meta a b d η ^ 2) = Meta a b d η := by
  -- `hη`, `hd`, `hb` belong to the interface; the identity needs only the discriminant
  have _ := hη
  have _ := hd
  have _ := hb
  set s := Real.sqrt ((1 - d * a) ^ 2 - 4 * d * b * η) with hs_def
  have hs : s ^ 2 = (1 - d * a) ^ 2 - 4 * d * b * η := Real.sq_sqrt (by linarith)
  have hden : 0 < 1 - d * a + s := Meta_den_pos (b := b) (η := η) h1
  have key : Meta a b d η * (1 - d * a + s) = 2 * η := by
    rw [Meta, ← hs_def]
    exact div_mul_cancel₀ _ hden.ne'
  have h : (1 - d * a + s) ^ 2
      * (η + d * (a * Meta a b d η + b * Meta a b d η ^ 2) - Meta a b d η) = 0 := by
    linear_combination
      (d * b * (Meta a b d η * (1 - d * a + s) + 2 * η) - (1 - d * a) * (1 - d * a + s)) * key
        + η * hs
  rcases mul_eq_zero.mp h with h1' | h1'
  · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1') hden.ne'
  · linarith

/-- `0 ≤ M_η` (`eq:zero-compatible-quadratic`). -/
theorem Meta_nonneg {a b d η : ℝ} (hη : 0 ≤ η) (h1 : d * a < 1) : 0 ≤ Meta a b d η :=
  div_nonneg (by linarith) (Meta_den_pos (b := b) (η := η) h1).le

/-- `M_η ≤ 2η/(1 - da)` (`eq:zero-compatible-quadratic`). -/
theorem Meta_le {a b d η : ℝ} (hη : 0 ≤ η) (h1 : d * a < 1) :
    Meta a b d η ≤ 2 * η / (1 - d * a) :=
  div_le_div_of_nonneg_left (by linarith) (by linarith)
    (le_add_of_nonneg_right (Real.sqrt_nonneg _))

/-! ### The zero-compatible threshold (`sec:completion`, `δ = 0`) -/

/-- The zero-compatible threshold function `J⁰_K(t) = 1 + (1 + (2α-1)t)(aK + bK²t)`
(`sec:completion`: `Z̄ = Ē = 0` and `A_0 = 0` when `δ = 0`). -/
noncomputable def JK0 (α a b Kc t : ℝ) : ℝ :=
  1 + (1 + (2 * α - 1) * t) * (a * Kc + b * Kc ^ 2 * t)

/-- `ε⁰_K = max{t ∈ [0, 1/(2K)] : J⁰_K(t) ≤ K}` (`sec:completion`). -/
noncomputable def epsK0 (α a b Kc : ℝ) : ℝ :=
  sSup {t | t ∈ Set.Icc 0 (1 / (2 * Kc)) ∧ JK0 α a b Kc t ≤ Kc}

/-- `J⁰_K` is nondecreasing on `[0, ∞)`. -/
lemma JK0_mono_of_le {α a b Kc t t' : ℝ} (hα : 1 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hK : 0 ≤ Kc) (ht : 0 ≤ t) (htt : t ≤ t') : JK0 α a b Kc t ≤ JK0 α a b Kc t' := by
  have h2α : 0 ≤ 2 * α - 1 := by linarith
  have ht' : 0 ≤ t' := ht.trans htt
  unfold JK0
  gcongr

/-- `J⁰_K` is continuous. -/
lemma JK0_continuous (α a b Kc : ℝ) : Continuous (JK0 α a b Kc) := by
  unfold JK0
  fun_prop

/-- The zero-compatible threshold: `ε⁰_K > 0`, `ε⁰_K ≤ 1/(2K)`, and `J⁰_K ≤ K` on
`[0, ε⁰_K]` for `K > 1/(1-a)` (`sec:completion`). -/
theorem epsK0_spec {α a b Kc : ℝ} (hα : 1 ≤ α) (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hK : 1 / (1 - a) < Kc) :
    0 < epsK0 α a b Kc ∧ epsK0 α a b Kc ≤ 1 / (2 * Kc)
      ∧ ∀ t ∈ Set.Icc 0 (epsK0 α a b Kc), JK0 α a b Kc t ≤ Kc := by
  have hKpos : 0 < Kc := (one_div_pos.mpr (by linarith)).trans hK
  have h0 : JK0 α a b Kc 0 < Kc := by
    unfold JK0
    rw [div_lt_iff₀ (by linarith)] at hK
    nlinarith
  exact sSup_admissible_spec (JK0_continuous α a b Kc)
    (fun t t' ht htt => JK0_mono_of_le hα ha0 hb hKpos.le ht htt)
    (one_div_pos.mpr (by positivity)) h0

/-- The zero-compatible barrier in real form (`sec:completion`): for `0 ≤ t ≤ ε⁰_K`,
`t + (1 + (2α-1) t)(a Kt + b (Kt)²) ≤ K t`. -/
theorem barrier0_of_le_epsK0 {α a b Kc : ℝ} (hα : 1 ≤ α) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb : 0 ≤ b) (hK : 1 / (1 - a) < Kc) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ epsK0 α a b Kc) :
    t + (1 + (2 * α - 1) * t) * (a * (Kc * t) + b * (Kc * t) ^ 2) ≤ Kc * t := by
  have hJ := (epsK0_spec hα ha0 ha1 hb hK).2.2 t ⟨ht0, ht⟩
  have e : t + (1 + (2 * α - 1) * t) * (a * (Kc * t) + b * (Kc * t) ^ 2)
      = t * JK0 α a b Kc t := by
    unfold JK0
    ring
  rw [e, mul_comm Kc t]
  exact mul_le_mul_of_nonneg_left hJ ht0

end GraphMarkovMatching.Stopped
