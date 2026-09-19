/-
The headline theorem of `arbitrary_offspring_matching.tex`: `thm:markov-matching` assembled
from the height induction (`Induction.lean`), the König step (`Infinite.lean`) and the
scalar threshold analysis (`Threshold.lean`), following "Completion of the proof" in
`sec:completion`.

* `Params`: the scalar parameters `α, β, u, L, K, L0` of the four-law contraction with
  the linear coefficient `a = 2(L+K) < 1`; `Params.ofLambda` chooses them from the
  exponent condition `λ_α < 1` at a minimising `β` and `u = 1/2`;
* `finiteA0`, `finiteK0`, `finiteEps`, `finiteKmatch`: the explicit constants of the
  finite alternative;
* `markov_matching_finite`, `markov_matching_finite_infinite`,
  `markov_matching_finite_exists`, `markov_matching_finite_exists_infinite`,
  `markov_matching_finite_eta`: the finite alternative, with the explicit constants, at
  infinite height, in existential form, and in the `η` form at `μ(0) ≥ p₀ > 0`;
* `markov_matching_zero`, `markov_matching_zero_infinite`, `markov_matching_zero_exists`:
  the zero-compatible alternative, with constants depending only on `α`;
* `markov_matching_zero_quadratic`: the explicit quadratic bound
  `eq:zero-compatible-quadratic`;
* `markov_matching_of_lambda`, `markov_matching_zero_of_lambda`: `thm:markov-matching` as
  stated, in terms of the exponent condition alone.
-/
import GraphMarkovMatching.Stopped.Induction
import GraphMarkovMatching.Stopped.Infinite
import GraphMarkovMatching.Stopped.Threshold

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support Model
open scoped ENNReal Classical

/-! ### The scalar parameters (`sec:completion`) -/

/-- The scalar parameters of the contraction: exponent, `β`, `u`, and admissible bounds
`L ≥ L_α(β)`, `K ≥ K_α(β)`, `L0 ≥ L_α` with linear coefficient `2(L+K) < 1`
(`sec:completion`). -/
structure Params where
  /-- The exponent `α ≥ 1`. -/
  α : ℝ
  /-- The parameter `β ∈ [0,1]` of `eq:mean-constants`. -/
  β : ℝ
  /-- The chord parameter `u ∈ (0,1)` of `eq:four-law-constants`. -/
  u : ℝ
  /-- An upper bound for `L_α(β)`. -/
  L : ℝ
  /-- An upper bound for `K_α(β)`. -/
  K : ℝ
  /-- An upper bound for `L_α = L_α(0)`. -/
  L0 : ℝ
  hα : 1 ≤ α
  hβ0 : 0 ≤ β
  hβ1 : β ≤ 1
  hu0 : 0 < u
  hu1 : u < 1
  hL : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α β q ≤ L
  hK : ∀ q, 0 ≤ q → q ≤ 1 → (q - β) * (1 - q) ^ α ≤ K
  hL0 : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α 0 q ≤ L0
  ha : 2 * (L + K) < 1

namespace Params

/-- The linear coefficient `a = 2(L+K)` (`sec:completion`). -/
noncomputable def a (p : Params) : ℝ := 2 * (p.L + p.K)

/-- The quadratic coefficient `b = C_α(u)` (`sec:completion`). -/
noncomputable def b (p : Params) : ℝ := Cfun p.α p.L0 p.u

/-- The zero coefficient `γ = 2 + 2β` (`sec:completion`). -/
noncomputable def γ (p : Params) : ℝ := 2 + 2 * p.β

/-- The mixture constant `C = 4 + 8(α+1)B` of the finite alternative (`sec:averaging`),
real. -/
noncomputable def Cm (p : Params) (B : ℝ) : ℝ := 4 + 8 * (p.α + 1) * B

/-- `0 ≤ α`. -/
lemma α_nonneg (p : Params) : 0 ≤ p.α := by linarith [p.hα]

/-- `0 ≤ L` (the summand at `q = 0` is `β ≥ 0`). -/
lemma L_nonneg (p : Params) : 0 ≤ p.L := p.hβ0.trans (beta_le_of_hL p.hL)

/-- `0 ≤ K` (the value at `q = β`). -/
lemma K_nonneg (p : Params) : 0 ≤ p.K := K_nonneg_of_hK p.hβ0 p.hβ1 p.hK

/-- `0 ≤ L0` (the summand at `q = 0`, `β = 0`). -/
lemma L0_nonneg (p : Params) : 0 ≤ p.L0 :=
  (Lsummand_nonneg (α := p.α) (β := 0) le_rfl le_rfl zero_le_one).trans
    (p.hL0 0 le_rfl zero_le_one)

/-- `0 ≤ a`. -/
lemma a_nonneg (p : Params) : 0 ≤ p.a := by
  unfold a
  linarith [p.L_nonneg, p.K_nonneg]

/-- `a < 1`. -/
lemma a_lt_one (p : Params) : p.a < 1 := p.ha

/-- `0 ≤ b`. -/
lemma b_nonneg (p : Params) : 0 ≤ p.b :=
  Cfun_nonneg p.α_nonneg p.L0_nonneg p.hu0 p.hu1

/-- `0 ≤ γ`. -/
lemma γ_nonneg (p : Params) : 0 ≤ p.γ := by
  unfold γ
  linarith [p.hβ0]

/-- `0 ≤ C` for `B ≥ 0`. -/
lemma Cm_nonneg (p : Params) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ p.Cm B := by
  unfold Cm
  have := p.α_nonneg
  positivity

/-- The `ℝ≥0∞` mixture constant of `Paths.lean` is the real one (`sec:averaging`). -/
lemma Cmix_eq (p : Params) {B : ℝ} (hB : 0 ≤ B) :
    Cmix p.α (ENNReal.ofReal B) = ENNReal.ofReal (p.Cm B) := by
  have hα1 : (0 : ℝ) ≤ p.α + 1 := by linarith [p.hα]
  have h8 : (0 : ℝ) ≤ 8 * (p.α + 1) := by positivity
  rw [Cm, ENNReal.ofReal_add (by norm_num) (mul_nonneg h8 hB), ENNReal.ofReal_mul h8,
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat, Cmix]

/-- A minimising `β` of `eq:mean-constants`. -/
private noncomputable def betaMin {α : ℝ} (hα : 1 ≤ α) : ℝ :=
  Classical.choose (exists_beta_min hα)

/-- The minimising `β` is admissible, attains `λ_α`, and minimises `L_α + K_α` on `[0,1]`
(`eq:mean-constants`). -/
private lemma betaMin_spec {α : ℝ} (hα : 1 ≤ α) :
    0 ≤ betaMin hα ∧ betaMin hα ≤ 1
      ∧ lambda α = 2 * (Lfun α (betaMin hα) + Kfun α (betaMin hα))
      ∧ ∀ β', 0 ≤ β' → β' ≤ 1 →
        Lfun α (betaMin hα) + Kfun α (betaMin hα) ≤ Lfun α β' + Kfun α β' :=
  Classical.choose_spec (exists_beta_min hα)

/-- The parameters at the exact maxima, from the exponent condition (`sec:completion`: a
minimising `β`, `u = 1/2`, `L = L_α(β)`, `K = K_α(β)`, `L0 = L_α`). -/
noncomputable def ofLambda {α : ℝ} (hα : 1 ≤ α) (h : lambda α < 1) : Params where
  α := α
  β := betaMin hα
  u := 1 / 2
  L := Lfun α (betaMin hα)
  K := Kfun α (betaMin hα)
  L0 := Lfun α 0
  hα := hα
  hβ0 := (betaMin_spec hα).1
  hβ1 := (betaMin_spec hα).2.1
  hu0 := by norm_num
  hu1 := by norm_num
  hL := fun q hq0 hq1 => le_Lfun (by linarith) (betaMin_spec hα).1 hq0 hq1
  hK := fun q hq0 hq1 => Kfun_bound hα (betaMin_spec hα).1 (betaMin_spec hα).2.1 hq0 hq1
  hL0 := fun q hq0 hq1 => le_Lfun (by linarith) le_rfl hq0 hq1
  ha := by
    have := (betaMin_spec hα).2.2.1
    linarith

/-- The exponent of the parameters chosen from the exponent condition. -/
lemma ofLambda_α {α : ℝ} (hα : 1 ≤ α) (h : lambda α < 1) : (ofLambda hα h).α = α := rfl

/-- With a minimising `β`, `a = λ_α` (`sec:completion`). -/
lemma ofLambda_a {α : ℝ} (hα : 1 ≤ α) (h : lambda α < 1) : (ofLambda hα h).a = lambda α := by
  show 2 * (Lfun α (betaMin hα) + Kfun α (betaMin hα)) = lambda α
  exact (betaMin_spec hα).2.2.1.symm

end Params

/-! ### The constants of the finite alternative (`sec:completion`) -/

/-- `A_0 = γ S_H + 2 C B (α+1) G_H(4B)` (`sec:completion`). -/
noncomputable def finiteA0 (p : Params) (H : ℕ) (B : ℝ) : ℝ := A0 p.α p.γ (p.Cm B) H B

/-- `K_0 = (1 + A_0)/(1 - a)` (`sec:completion`). -/
noncomputable def finiteK0 (p : Params) (H : ℕ) (B : ℝ) : ℝ := K0 p.a (finiteA0 p H B)

/-- `ε_K` of `eq:constructive-threshold` at the parameters `p`. -/
noncomputable def finiteEps (p : Params) (H T : ℕ) (B Kc : ℝ) : ℝ :=
  epsK p.α p.a p.b p.γ (p.Cm B) H T B Kc

/-- `K_match = K + 2 S_H` (`sec:completion`). -/
noncomputable def finiteKmatch (H : ℕ) (Kc : ℝ) : ℝ := Kmatch H Kc

/-- `0 < K_0`. -/
lemma finiteK0_pos (p : Params) (H : ℕ) {B : ℝ} (hB : 0 ≤ B) : 0 < finiteK0 p H B :=
  K0_pos p.a_lt_one (A0_nonneg p.α_nonneg p.γ_nonneg (p.Cm_nonneg hB) H hB)

/-- `ε_K > 0` (`eq:constructive-threshold`). -/
theorem finiteEps_pos (p : Params) (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B) (Kc : ℝ)
    (hK : finiteK0 p H B < Kc) : 0 < finiteEps p H T B Kc :=
  (epsK_spec p.hα p.a_nonneg p.a_lt_one p.b_nonneg p.γ_nonneg (p.Cm_nonneg (by linarith))
    hB hT hK).1

/-! ### The bridge from the scalar barrier to the `ℝ≥0∞` barrier (`sec:completion`) -/

namespace Model

variable {V I : Type} (M : Model V I)

/-- `ζ = ofReal ζ` when finite. -/
private lemma zeta_eq_ofReal {α : ℝ} (hζ : M.zeta α ≠ ⊤) :
    M.zeta α = ENNReal.ofReal (M.zeta α).toReal := (ENNReal.ofReal_toReal hζ).symm

/-- `f ≤ ofReal ((α+1) ζ)` (`eq:root-parameter-bounds`). -/
private lemma fRoot_le_ofReal (hc : M.IsCompat) {α : ℝ} (hα : 1 ≤ α) (hζ : M.zeta α ≠ ⊤) :
    M.fRoot α ≤ ENNReal.ofReal ((α + 1) * (M.zeta α).toReal) := by
  have e := M.zeta_eq_ofReal hζ
  calc M.fRoot α ≤ ENNReal.ofReal (1 + α) * M.zeta α := M.fRoot_le_zeta hc hα
    _ = ENNReal.ofReal (1 + α) * ENNReal.ofReal (M.zeta α).toReal := by rw [← e]
    _ = ENNReal.ofReal ((α + 1) * (M.zeta α).toReal) := by
        rw [← ENNReal.ofReal_mul (by linarith), add_comm]

/-- `R_μ ≤ ofReal (1 + α ζ)` (`eq:root-parameter-bounds`). -/
private lemma RmuC_le_ofReal (hc : M.IsCompat) {α : ℝ} (hα : 1 ≤ α) (hζ : M.zeta α ≠ ⊤) :
    M.RmuC α ≤ ENNReal.ofReal (1 + α * (M.zeta α).toReal) := by
  have e := M.zeta_eq_ofReal hζ
  have h0 : 0 ≤ α * (M.zeta α).toReal := mul_nonneg (by linarith) ENNReal.toReal_nonneg
  calc M.RmuC α ≤ 1 + ENNReal.ofReal α * M.zeta α := M.RmuC_le hc hα
    _ = 1 + ENNReal.ofReal α * ENNReal.ofReal (M.zeta α).toReal := by rw [← e]
    _ = ENNReal.ofReal (1 + α * (M.zeta α).toReal) := by
        rw [← ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_add zero_le_one h0,
          ENNReal.ofReal_one]

/-- `D_μ ≤ ofReal (1 + (2α-1) ζ)` (`sec:independent-root`). -/
private lemma DmuC_le_ofReal (hc : M.IsCompat) {α : ℝ} (hα : 1 ≤ α) (hζ : M.zeta α ≠ ⊤) :
    M.DmuC α ≤ ENNReal.ofReal (1 + (2 * α - 1) * (M.zeta α).toReal) := by
  have h2 : (0 : ℝ) ≤ 2 * α - 1 := by linarith
  have e := M.zeta_eq_ofReal hζ
  have h0 : 0 ≤ (2 * α - 1) * (M.zeta α).toReal := mul_nonneg h2 ENNReal.toReal_nonneg
  calc M.DmuC α ≤ 1 + ENNReal.ofReal (2 * α - 1) * M.zeta α := M.DmuC_le hc hα
    _ = 1 + ENNReal.ofReal (2 * α - 1) * ENNReal.ofReal (M.zeta α).toReal := by rw [← e]
    _ = ENNReal.ofReal (1 + (2 * α - 1) * (M.zeta α).toReal) := by
        rw [← ENNReal.ofReal_mul h2, ENNReal.ofReal_add zero_le_one h0, ENNReal.ofReal_one]

/-- The fixed-point condition of the uniform zero bound at `Z = ofReal Z̄(ζ)`
(`sec:completion`, `eq:explicit-zero-bound`). -/
private lemma zbar_fixed_ennreal {α : ℝ} (hα : 0 ≤ α) (hζ : M.zeta α ≠ ⊤) (H T : ℕ)
    (h4 : 4 * SH H ^ 2 * T ^ 2 * (M.zeta α).toReal ≤ 1) :
    SHe H * (M.delta + (T : ℝ≥0∞) ^ 2 * (ENNReal.ofReal (Zbar H T (M.zeta α).toReal)) ^ 2)
      ≤ ENNReal.ofReal (Zbar H T (M.zeta α).toReal) := by
  set t := (M.zeta α).toReal with ht_def
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hZ0 : 0 ≤ Zbar H T t := Zbar_nonneg H T ht0
  have hδ : M.delta ≤ ENNReal.ofReal t := by
    rw [ht_def, ← M.zeta_eq_ofReal hζ]
    exact M.delta_le_zeta hα
  calc SHe H * (M.delta + (T : ℝ≥0∞) ^ 2 * (ENNReal.ofReal (Zbar H T t)) ^ 2)
      ≤ SHe H * (ENNReal.ofReal t + (T : ℝ≥0∞) ^ 2 * (ENNReal.ofReal (Zbar H T t)) ^ 2) := by
        gcongr
    _ = ENNReal.ofReal (SH H * (t + (T : ℝ) ^ 2 * Zbar H T t ^ 2)) := by
        rw [SHe_eq_ofReal, ENNReal.ofReal_mul (SH_pos H).le, ENNReal.ofReal_add ht0 (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hZ0,
          ENNReal.ofReal_pow (Nat.cast_nonneg T), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (Zbar H T t) := by rw [Zbar_fixed H T ht0 h4]

/-- The `ℝ≥0∞` barrier `ζ + D_μ Q(Kζ) ≤ Kζ` of `eq:scalar-barrier-condition` from the real
barrier `barrier_of_le_epsK` (`sec:completion`). -/
private lemma barrier_ennreal (hc : M.IsCompat) (p : Params) (H T : ℕ) (hT : 1 ≤ T) (B : ℝ)
    (hB : 1 ≤ B) (Kc : ℝ) (hK : finiteK0 p H B < Kc) (hζ : M.zeta p.α ≠ ⊤)
    (hε : (M.zeta p.α).toReal ≤ finiteEps p H T B Kc) :
    M.zeta p.α + M.DmuC p.α * Qfun p.α (ENNReal.ofReal p.a) (ENNReal.ofReal p.b)
        (ENNReal.ofReal p.γ) (Cmix p.α (ENNReal.ofReal B))
        (ENNReal.ofReal (Zbar H T (M.zeta p.α).toReal))
        (Efun p.α H T (ENNReal.ofReal B) (M.fRoot p.α) (M.RmuC p.α)
          (ENNReal.ofReal (Zbar H T (M.zeta p.α).toReal))
          (ENNReal.ofReal (Kc * (M.zeta p.α).toReal)))
        (ENNReal.ofReal (Kc * (M.zeta p.α).toReal))
      ≤ ENNReal.ofReal (Kc * (M.zeta p.α).toReal) := by
  set t := (M.zeta p.α).toReal with ht_def
  have hα := p.hα
  have hα0 := p.α_nonneg
  have hB0 : 0 ≤ B := by linarith
  have hC0 := p.Cm_nonneg hB0
  have hKpos : 0 < Kc := (finiteK0_pos p H hB0).trans hK
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hM0 : 0 ≤ Kc * t := mul_nonneg hKpos.le ht0
  have hZ0 : 0 ≤ Zbar H T t := Zbar_nonneg H T ht0
  have hf0 : 0 ≤ (p.α + 1) * t := by positivity
  have hR0 : 0 ≤ 1 + p.α * t := by positivity
  have hE0 : 0 ≤ Ebar p.α H T B t (Kc * t) := by
    rw [Ebar_eq_mul]
    exact mul_nonneg ht0 (EbarQ_nonneg hα0 H T hB0 hKpos.le ht0)
  have hbarR := barrier_of_le_epsK hα p.a_nonneg p.a_lt_one p.b_nonneg p.γ_nonneg hC0 hB hT hK
    ht0 hε
  have hE : Efun p.α H T (ENNReal.ofReal B) (M.fRoot p.α) (M.RmuC p.α)
      (ENNReal.ofReal (Zbar H T t)) (ENNReal.ofReal (Kc * t))
      ≤ ENNReal.ofReal (Ebar p.α H T B t (Kc * t)) := by
    calc Efun p.α H T (ENNReal.ofReal B) (M.fRoot p.α) (M.RmuC p.α)
          (ENNReal.ofReal (Zbar H T t)) (ENNReal.ofReal (Kc * t))
        ≤ Efun p.α H T (ENNReal.ofReal B) (ENNReal.ofReal ((p.α + 1) * t))
          (ENNReal.ofReal (1 + p.α * t)) (ENNReal.ofReal (Zbar H T t))
          (ENNReal.ofReal (Kc * t)) :=
          Efun_mono p.α H T le_rfl (M.fRoot_le_ofReal hc hα hζ) (M.RmuC_le_ofReal hc hα hζ)
            le_rfl le_rfl
      _ = ENNReal.ofReal (Ebar p.α H T B t (Kc * t)) :=
          Efun_ofReal p.α hα0 H T hB0 hf0 hR0 hZ0 hM0
  have hQ : Qfun p.α (ENNReal.ofReal p.a) (ENNReal.ofReal p.b) (ENNReal.ofReal p.γ)
      (Cmix p.α (ENNReal.ofReal B)) (ENNReal.ofReal (Zbar H T t))
      (Efun p.α H T (ENNReal.ofReal B) (M.fRoot p.α) (M.RmuC p.α)
        (ENNReal.ofReal (Zbar H T t)) (ENNReal.ofReal (Kc * t)))
      (ENNReal.ofReal (Kc * t))
      ≤ ENNReal.ofReal (Qbar p.α p.a p.b p.γ (p.Cm B) H T B t (Kc * t)) := by
    calc Qfun p.α (ENNReal.ofReal p.a) (ENNReal.ofReal p.b) (ENNReal.ofReal p.γ)
          (Cmix p.α (ENNReal.ofReal B)) (ENNReal.ofReal (Zbar H T t))
          (Efun p.α H T (ENNReal.ofReal B) (M.fRoot p.α) (M.RmuC p.α)
            (ENNReal.ofReal (Zbar H T t)) (ENNReal.ofReal (Kc * t)))
          (ENNReal.ofReal (Kc * t))
        ≤ Qfun p.α (ENNReal.ofReal p.a) (ENNReal.ofReal p.b) (ENNReal.ofReal p.γ)
          (Cmix p.α (ENNReal.ofReal B)) (ENNReal.ofReal (Zbar H T t))
          (ENNReal.ofReal (Ebar p.α H T B t (Kc * t))) (ENNReal.ofReal (Kc * t)) :=
          Qfun_mono p.α _ _ _ _ le_rfl hE le_rfl
      _ = ENNReal.ofReal (Qbar p.α p.a p.b p.γ (p.Cm B) H T B t (Kc * t)) := by
          rw [p.Cmix_eq hB0]
          exact Qfun_ofReal p.α hα0 p.a_nonneg p.b_nonneg p.γ_nonneg hC0 hZ0 hE0 hM0
  have hD := M.DmuC_le_ofReal hc hα hζ
  rw [← ht_def] at hD
  have hQ0 : 0 ≤ Qbar p.α p.a p.b p.γ (p.Cm B) H T B t (Kc * t) := by
    unfold Qbar Qreal
    have := p.a_nonneg
    have := p.b_nonneg
    have := p.γ_nonneg
    positivity
  have hA0 : 0 ≤ 1 + (2 * p.α - 1) * t := by
    have : (0 : ℝ) ≤ 2 * p.α - 1 := by linarith
    positivity
  have hAQ : 0 ≤ (1 + (2 * p.α - 1) * t) * Qbar p.α p.a p.b p.γ (p.Cm B) H T B t (Kc * t) :=
    mul_nonneg hA0 hQ0
  calc M.zeta p.α + M.DmuC p.α * Qfun p.α (ENNReal.ofReal p.a) (ENNReal.ofReal p.b)
        (ENNReal.ofReal p.γ) (Cmix p.α (ENNReal.ofReal B)) (ENNReal.ofReal (Zbar H T t))
        (Efun p.α H T (ENNReal.ofReal B) (M.fRoot p.α) (M.RmuC p.α)
          (ENNReal.ofReal (Zbar H T t)) (ENNReal.ofReal (Kc * t)))
        (ENNReal.ofReal (Kc * t))
      ≤ ENNReal.ofReal t + ENNReal.ofReal (1 + (2 * p.α - 1) * t)
          * ENNReal.ofReal (Qbar p.α p.a p.b p.γ (p.Cm B) H T B t (Kc * t)) := by
        refine add_le_add ?_ (mul_le_mul' hD hQ)
        rw [ht_def, ← M.zeta_eq_ofReal hζ]
    _ = ENNReal.ofReal (t + (1 + (2 * p.α - 1) * t)
          * Qbar p.α p.a p.b p.γ (p.Cm B) H T B t (Kc * t)) := by
        rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_add ht0 hAQ]
    _ ≤ ENNReal.ofReal (Kc * t) := ENNReal.ofReal_le_ofReal hbarR

/-- `Z + M ≤ ofReal K_match · ζ` at `Z = ofReal Z̄(ζ)`, `M = ofReal (Kζ)`
(`sec:completion`: `Z̄ ≤ 2 S_H ζ`). -/
private lemma zbar_add_le {α : ℝ} (hζ : M.zeta α ≠ ⊤) (H T : ℕ) {Kc : ℝ} (hK : 0 ≤ Kc)
    (h4 : 4 * SH H ^ 2 * T ^ 2 * (M.zeta α).toReal ≤ 1) :
    ENNReal.ofReal (Zbar H T (M.zeta α).toReal) + ENNReal.ofReal (Kc * (M.zeta α).toReal)
      ≤ ENNReal.ofReal (finiteKmatch H Kc) * M.zeta α := by
  set t := (M.zeta α).toReal with ht_def
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hS := SH_pos H
  calc ENNReal.ofReal (Zbar H T t) + ENNReal.ofReal (Kc * t)
      ≤ ENNReal.ofReal (2 * SH H * t) + ENNReal.ofReal (Kc * t) := by
        gcongr
        exact Zbar_le_two H T ht0 h4
    _ = ENNReal.ofReal (finiteKmatch H Kc * t) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), finiteKmatch, Kmatch]
        congr 1
        ring
    _ = ENNReal.ofReal (finiteKmatch H Kc) * M.zeta α := by
        rw [ENNReal.ofReal_mul (by unfold finiteKmatch Kmatch; positivity), ht_def,
          ← M.zeta_eq_ofReal hζ]

/-- `ofReal (Kζ) = ofReal K · ζ`. -/
private lemma ofReal_mul_zeta {α : ℝ} (hζ : M.zeta α ≠ ⊤) {Kc : ℝ} (hK : 0 ≤ Kc) :
    ENNReal.ofReal (Kc * (M.zeta α).toReal) = ENNReal.ofReal Kc * M.zeta α := by
  rw [ENNReal.ofReal_mul hK, ← M.zeta_eq_ofReal hζ]

end Model

/-! ### The finite alternative (`thm:markov-matching`, `sec:completion`) -/

/-- **`thm:markov-matching`, finite alternative, with the explicit constants**
(`sec:completion`): for every finite model with a phase map of class size at most `T`, a
transition selection with inverse-probability sums at most `B`, fresh positivity and common returns within `H`,
if `ζ_α ≤ ε_K` then every equal-phase pair fails at every height with probability at most
`K_match ζ_α`, fresh pairs with probability at most `K ζ_α`, and every equal-phase
restricted potential is at most `K ζ_α`. -/
theorem markov_matching_finite (p : Params) (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B)
    (Kc : ℝ) (hK : finiteK0 p H B < Kc) {V I : Type} [Fintype I] (M : Model V I)
    (hc : M.IsCompat) {g : ℕ} (Θ : Model.Phase M g) (hTc : ∀ i, Θ.count i ≤ T)
    (Sel : Model.Selection M) (hBs : ∀ t, Sel.inverseSum p.α t ≤ ENNReal.ofReal B)
    (hFP : M.FreshPositive) (hCR : M.CommonReturns Θ H)
    (hζ : M.zeta p.α ≤ ENNReal.ofReal (finiteEps p H T B Kc)) :
    (∀ s t, Θ.θ s = Θ.θ t → ∀ h,
        M.failProb s t h ≤ ENNReal.ofReal (finiteKmatch H Kc) * M.zeta p.α)
    ∧ (∀ s t, M.fresh s → M.fresh t → ∀ h,
        M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta p.α)
    ∧ (∀ s t, Θ.θ s = Θ.θ t → ∀ h, M.P p.α s t h ≤ ENNReal.ofReal Kc * M.zeta p.α) := by
  have hα := p.hα
  have hB0 : 0 ≤ B := by linarith
  have hKpos : 0 < Kc := (finiteK0_pos p H hB0).trans hK
  have hζtop : M.zeta p.α ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hζ
  have hb0 : rE M.μ M.R M.zero ≠ 0 := M.rE_zero_ne_zero_of_zeta_ne_top hζtop
  set t := (M.zeta p.α).toReal with ht_def
  have hε : t ≤ finiteEps p H T B Kc :=
    ENNReal.toReal_le_of_le_ofReal (finiteEps_pos p H T hT B hB Kc hK).le hζ
  have hspec := epsK_spec p.hα p.a_nonneg p.a_lt_one p.b_nonneg p.γ_nonneg (p.Cm_nonneg hB0)
    hB hT hK
  have htstar : t ≤ tstar H T Kc := hε.trans hspec.2.1
  have h4 : 4 * SH H ^ 2 * T ^ 2 * t ≤ 1 := (le_tstar_imp hKpos hT htstar).1
  have hZ := M.zbar_fixed_ennreal p.α_nonneg hζtop H T h4
  have hbar := M.barrier_ennreal hc p H T hT B hB Kc hK hζtop hε
  have hfour : ∀ h Mb Zm E, M.FourLawAt Θ p.α h (ENNReal.ofReal p.a) (ENNReal.ofReal p.b)
      (ENNReal.ofReal p.γ) Mb Zm E :=
    fun h Mb Zm E => M.fourLawAt_of_params hc p.hα p.hβ0 p.hβ1 p.hu0 p.hu1 p.hL p.hK p.hL0
      Θ h Mb Zm E
  have hP := M.P_le_finite hc hb0 hFP hα Θ hTc hCR Sel hBs (ENNReal.ofReal p.a)
    (ENNReal.ofReal p.b) (ENNReal.ofReal p.γ) hfour hZ hbar
  have hF := M.failProb_le_finite hc hb0 hFP hα Θ hTc hCR Sel hBs (ENNReal.ofReal p.a)
    (ENNReal.ofReal p.b) (ENNReal.ofReal p.γ) hfour hZ hbar
  have hFf := M.failProb_le_finite_fresh hc hb0 hFP hα Θ hTc hCR Sel hBs (ENNReal.ofReal p.a)
    (ENNReal.ofReal p.b) (ENNReal.ofReal p.γ) hfour hZ hbar
  have hMb := M.ofReal_mul_zeta hζtop hKpos.le
  rw [← ht_def] at hMb
  have hZM := M.zbar_add_le hζtop H T hKpos.le h4
  rw [← ht_def] at hZM
  refine ⟨fun s u hsu h => (hF h s u hsu).trans hZM, fun s u hs hu h => ?_,
    fun s u hsu h => ?_⟩
  · rw [← hMb]
    exact hFf h s u hs hu
  · rw [← hMb]
    exact hP h s u hsu

/-- The infinite-tree conclusion of the finite alternative (`thm:markov-matching`,
`sec:completion`: König's lemma and continuity of probability). -/
theorem markov_matching_finite_infinite (p : Params) (H T : ℕ) (hT : 1 ≤ T) (B : ℝ)
    (hB : 1 ≤ B) (Kc : ℝ) (hK : finiteK0 p H B < Kc) {V I : Type} [Fintype I]
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V] [MeasurableSpace I]
    [MeasurableSingletonClass I] (M : Model V I) (hc : M.IsCompat) {g : ℕ}
    (Θ : Model.Phase M g) (hTc : ∀ i, Θ.count i ≤ T) (Sel : Model.Selection M)
    (hBs : ∀ t, Sel.inverseSum p.α t ≤ ENNReal.ofReal B) (hFP : M.FreshPositive)
    (hCR : M.CommonReturns Θ H) (hζ : M.zeta p.α ≤ ENNReal.ofReal (finiteEps p H T B Kc)) :
    (∀ s t, Θ.θ s = Θ.θ t →
        M.trajPair s t (M.InfMatchEv s t)ᶜ ≤ ENNReal.ofReal (finiteKmatch H Kc) * M.zeta p.α)
    ∧ (∀ s t, M.fresh s → M.fresh t →
        M.trajPair s t (M.InfMatchEv s t)ᶜ ≤ ENNReal.ofReal Kc * M.zeta p.α) := by
  obtain ⟨h1, h2, _⟩ := markov_matching_finite p H T hT B hB Kc hK M hc Θ hTc Sel hBs hFP hCR hζ
  exact ⟨fun s t hst => M.trajPair_infFail_le s t (h1 s t hst),
    fun s t hs ht => M.trajPair_infFail_le s t (h2 s t hs ht)⟩

set_option linter.unusedVariables false in
/-- **`thm:markov-matching`, finite alternative, existential form**: constants depending
only on `α` (through the parameters), `H`, `T`, `B`, uniform over all models with these
bounds. -/
theorem markov_matching_finite_exists (p : Params) (H T : ℕ) (hT : 1 ≤ T) (B : ℝ)
    (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] (M : Model V I) (hc : M.IsCompat) {g : ℕ}
      (Θ : Model.Phase M g) (hTc : ∀ i, Θ.count i ≤ T) (Sel : Model.Selection M)
      (hBs : ∀ t, Sel.inverseSum p.α t ≤ ENNReal.ofReal B) (hFP : M.FreshPositive)
      (hCR : M.CommonReturns Θ H),
      M.zeta p.α ≤ ENNReal.ofReal ε → ∀ s t, Θ.θ s = Θ.θ t →
        ∀ h, M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta p.α := by
  have hK : finiteK0 p H B < finiteK0 p H B + 1 := by linarith
  refine ⟨finiteKmatch H (finiteK0 p H B + 1), finiteEps p H T B (finiteK0 p H B + 1),
    finiteEps_pos p H T hT B hB _ hK, ?_⟩
  intro V I _ M hc g Θ hTc Sel hBs hFP hCR hζ
  exact (markov_matching_finite p H T hT B hB _ hK M hc Θ hTc Sel hBs hFP hCR hζ).1

set_option linter.unusedVariables false in
/-- **`thm:markov-matching`, finite alternative, existential form at infinite height**. -/
theorem markov_matching_finite_exists_infinite (p : Params) (H T : ℕ) (hT : 1 ≤ T) (B : ℝ)
    (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] [Countable V] [MeasurableSpace V]
      [MeasurableSingletonClass V] [MeasurableSpace I] [MeasurableSingletonClass I]
      (M : Model V I) (hc : M.IsCompat) {g : ℕ} (Θ : Model.Phase M g)
      (hTc : ∀ i, Θ.count i ≤ T) (Sel : Model.Selection M)
      (hBs : ∀ t, Sel.inverseSum p.α t ≤ ENNReal.ofReal B) (hFP : M.FreshPositive)
      (hCR : M.CommonReturns Θ H),
      M.zeta p.α ≤ ENNReal.ofReal ε → ∀ s t, Θ.θ s = Θ.θ t →
        M.trajPair s t (M.InfMatchEv s t)ᶜ ≤ ENNReal.ofReal Kc * M.zeta p.α := by
  obtain ⟨Kc, ε, hε, hbound⟩ := markov_matching_finite_exists p H T hT B hB
  refine ⟨Kc, ε, hε, ?_⟩
  intro V I _ _ _ _ _ _ M hc g Θ hTc Sel hBs hFP hCR hζ s t hst
  exact M.trajPair_infFail_le s t (hbound M hc Θ hTc Sel hBs hFP hCR hζ s t hst)

/-- **The `η` form** (`thm:markov-matching`, last sentence): with `μ(0) ≥ p₀ > 0`, replace
`ζ` by `η`, the constant by `K_match/p₀` and the threshold by `p₀ ε`. -/
theorem markov_matching_finite_eta (p : Params) (H T : ℕ) (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B)
    (Kc : ℝ) (hK : finiteK0 p H B < Kc) {V I : Type} [Fintype I] (M : Model V I)
    (hc : M.IsCompat) {g : ℕ} (Θ : Model.Phase M g) (hTc : ∀ i, Θ.count i ≤ T)
    (Sel : Model.Selection M) (hBs : ∀ t, Sel.inverseSum p.α t ≤ ENNReal.ofReal B)
    (hFP : M.FreshPositive) (hCR : M.CommonReturns Θ H) {p0 : ℝ} (hp0 : 0 < p0)
    (hp1 : p0 ≤ 1) (hμ : ENNReal.ofReal p0 ≤ M.μ M.zero)
    (hη : M.eta p.α ≤ ENNReal.ofReal (p0 * finiteEps p H T B Kc)) :
    ∀ s t, Θ.θ s = Θ.θ t → ∀ h,
      M.failProb s t h ≤ ENNReal.ofReal (finiteKmatch H Kc / p0) * M.eta p.α := by
  have hp : ENNReal.ofReal p0 ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hp1' : ENNReal.ofReal p0 ≤ 1 := ENNReal.ofReal_le_one.mpr hp1
  have hζη : M.zeta p.α ≤ M.eta p.α / ENNReal.ofReal p0 :=
    M.zeta_le_eta_div hc p.α_nonneg hp hp1' hμ
  have hζ : M.zeta p.α ≤ ENNReal.ofReal (finiteEps p H T B Kc) := by
    refine hζη.trans ?_
    rw [ENNReal.div_le_iff hp ENNReal.ofReal_ne_top, ← ENNReal.ofReal_mul
      (finiteEps_pos p H T hT B hB Kc hK).le, mul_comm]
    exact hη
  intro s t hst h
  calc M.failProb s t h ≤ ENNReal.ofReal (finiteKmatch H Kc) * M.zeta p.α :=
        (markov_matching_finite p H T hT B hB Kc hK M hc Θ hTc Sel hBs hFP hCR hζ).1 s t hst h
    _ ≤ ENNReal.ofReal (finiteKmatch H Kc) * (M.eta p.α / ENNReal.ofReal p0) := by gcongr
    _ = ENNReal.ofReal (finiteKmatch H Kc / p0) * M.eta p.α := by
        rw [ENNReal.ofReal_div_of_pos hp0, div_eq_mul_inv, div_eq_mul_inv]
        ring

/-! ### The zero-compatible alternative (`thm:markov-matching`, `sec:completion`) -/

/-- **`thm:markov-matching`, zero-compatible alternative**: countably many types, no return
or transition-bound assumption; constants depending only on `α`. -/
theorem markov_matching_zero (p : Params) (Kc : ℝ) (hK : 1 / (1 - p.a) < Kc) {V I : Type}
    (M : Model V I) (hc : M.IsCompat) (hδ : M.delta = 0)
    (hζ : M.zeta p.α ≤ ENNReal.ofReal (epsK0 p.α p.a p.b Kc)) :
    (∀ s t h, M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta p.α)
    ∧ (∀ s t h, M.P p.α s t h ≤ ENNReal.ofReal Kc * M.zeta p.α) := by
  have hα := p.hα
  have hspec := epsK0_spec p.hα p.a_nonneg p.a_lt_one p.b_nonneg hK
  have hKpos : 0 < Kc := (one_div_pos.mpr (by linarith [p.a_lt_one])).trans hK
  have hζtop : M.zeta p.α ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hζ
  set t := (M.zeta p.α).toReal with ht_def
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hε : t ≤ epsK0 p.α p.a p.b Kc := ENNReal.toReal_le_of_le_ofReal hspec.1.le hζ
  have hbarR := barrier0_of_le_epsK0 p.hα p.a_nonneg p.a_lt_one p.b_nonneg hK ht0 hε
  have hM0 : 0 ≤ Kc * t := mul_nonneg hKpos.le ht0
  have hD := M.DmuC_le_ofReal hc hα hζtop
  rw [← ht_def] at hD
  have hA0 : 0 ≤ 1 + (2 * p.α - 1) * t := by
    have : (0 : ℝ) ≤ 2 * p.α - 1 := by linarith
    positivity
  have hq0 : 0 ≤ p.a * (Kc * t) + p.b * (Kc * t) ^ 2 :=
    add_nonneg (mul_nonneg p.a_nonneg hM0) (mul_nonneg p.b_nonneg (sq_nonneg _))
  have hbar : M.zeta p.α + M.DmuC p.α * (ENNReal.ofReal p.a * ENNReal.ofReal (Kc * t)
      + ENNReal.ofReal p.b * ENNReal.ofReal (Kc * t) ^ 2) ≤ ENNReal.ofReal (Kc * t) := by
    calc M.zeta p.α + M.DmuC p.α * (ENNReal.ofReal p.a * ENNReal.ofReal (Kc * t)
          + ENNReal.ofReal p.b * ENNReal.ofReal (Kc * t) ^ 2)
        ≤ ENNReal.ofReal t + ENNReal.ofReal (1 + (2 * p.α - 1) * t)
            * ENNReal.ofReal (p.a * (Kc * t) + p.b * (Kc * t) ^ 2) := by
          refine add_le_add ?_ (mul_le_mul' hD (le_of_eq ?_))
          · rw [ht_def, ← M.zeta_eq_ofReal hζtop]
          · rw [ENNReal.ofReal_add (mul_nonneg p.a_nonneg hM0)
              (mul_nonneg p.b_nonneg (sq_nonneg _)), ENNReal.ofReal_mul p.a_nonneg,
              ENNReal.ofReal_mul p.b_nonneg, ENNReal.ofReal_pow hM0]
      _ = ENNReal.ofReal (t + (1 + (2 * p.α - 1) * t)
            * (p.a * (Kc * t) + p.b * (Kc * t) ^ 2)) := by
          rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_add ht0 (mul_nonneg hA0 hq0)]
      _ ≤ ENNReal.ofReal (Kc * t) := ENNReal.ofReal_le_ofReal hbarR
  have hfour : ∀ h Mb, M.FourLawAtZero p.α h (ENNReal.ofReal p.a) (ENNReal.ofReal p.b) Mb :=
    fun h Mb => M.fourLawAtZero_of_params hc hδ p.hα p.hβ0 p.hβ1 p.hu0 p.hu1 p.hL p.hK p.hL0
      h Mb
  have hMb := M.ofReal_mul_zeta hζtop hKpos.le
  rw [← ht_def] at hMb
  rw [← hMb]
  exact ⟨fun s u h => M.failProb_le_zero hc hδ hα _ _ hfour hbar h s u,
    fun s u h => M.P_le_zero hc hδ hα _ _ hfour hbar h s u⟩

/-- The infinite-tree conclusion of the zero-compatible alternative
(`thm:markov-matching`, `sec:completion`). -/
theorem markov_matching_zero_infinite (p : Params) (Kc : ℝ) (hK : 1 / (1 - p.a) < Kc)
    {V I : Type} [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I] (M : Model V I) (hc : M.IsCompat)
    (hδ : M.delta = 0) (hζ : M.zeta p.α ≤ ENNReal.ofReal (epsK0 p.α p.a p.b Kc)) :
    ∀ s t, M.trajPair s t (M.InfMatchEv s t)ᶜ ≤ ENNReal.ofReal Kc * M.zeta p.α :=
  fun s t => M.trajPair_infFail_le s t
    ((markov_matching_zero p Kc hK M hc hδ hζ).1 s t)

set_option linter.unusedVariables false in
/-- **`thm:markov-matching`, zero-compatible alternative, existential form**: constants
depending only on `α` (through the parameters). -/
theorem markov_matching_zero_exists (p : Params) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} (M : Model V I) (hc : M.IsCompat), M.delta = 0 →
      M.zeta p.α ≤ ENNReal.ofReal ε → ∀ s t h,
        M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta p.α := by
  have hK : 1 / (1 - p.a) < 1 / (1 - p.a) + 1 := by linarith
  refine ⟨1 / (1 - p.a) + 1, epsK0 p.α p.a p.b (1 / (1 - p.a) + 1),
    (epsK0_spec p.hα p.a_nonneg p.a_lt_one p.b_nonneg hK).1, ?_⟩
  intro V I M hc hδ hζ
  exact (markov_matching_zero p _ hK M hc hδ hζ).1

/-- **`eq:zero-compatible-quadratic`**: with `d = 1 + (2α-1)η`, `d a < 1` and
`(1-da)² ≥ 4 d b η`, the failure probabilities are at most `M_η`, without any type-count
or transition-bound assumption. -/
theorem markov_matching_zero_quadratic (p : Params) {V I : Type} (M : Model V I)
    (hc : M.IsCompat) (hδ : M.delta = 0) (hfin : M.eta p.α ≠ ⊤)
    (h1 : (1 + (2 * p.α - 1) * (M.eta p.α).toReal) * p.a < 1)
    (h2 : 4 * (1 + (2 * p.α - 1) * (M.eta p.α).toReal) * p.b * (M.eta p.α).toReal
      ≤ (1 - (1 + (2 * p.α - 1) * (M.eta p.α).toReal) * p.a) ^ 2) :
    ∀ s t h, M.failProb s t h ≤ ENNReal.ofReal
      (Meta p.a p.b (1 + (2 * p.α - 1) * (M.eta p.α).toReal) (M.eta p.α).toReal) := by
  have hα := p.hα
  have hζη : M.zeta p.α = M.eta p.α := M.zeta_eq_eta_of_delta_zero hδ
  have hζtop : M.zeta p.α ≠ ⊤ := by rw [hζη]; exact hfin
  set η := (M.eta p.α).toReal with hη_def
  set d := 1 + (2 * p.α - 1) * η with hd_def
  have hη0 : 0 ≤ η := ENNReal.toReal_nonneg
  have hd0 : 0 ≤ d := by
    have : (0 : ℝ) ≤ 2 * p.α - 1 := by linarith
    positivity
  have hMeta := Meta_fixed hη0 hd0 p.b_nonneg h1 h2
  have hM0 : 0 ≤ Meta p.a p.b d η := Meta_nonneg hη0 h1
  have hq0 : 0 ≤ p.a * Meta p.a p.b d η + p.b * Meta p.a p.b d η ^ 2 :=
    add_nonneg (mul_nonneg p.a_nonneg hM0) (mul_nonneg p.b_nonneg (sq_nonneg _))
  have hD : M.DmuC p.α ≤ ENNReal.ofReal d := by
    have := M.DmuC_le_ofReal hc hα hζtop
    rwa [hζη] at this
  have hbar : M.zeta p.α + M.DmuC p.α * (ENNReal.ofReal p.a * ENNReal.ofReal (Meta p.a p.b d η)
      + ENNReal.ofReal p.b * ENNReal.ofReal (Meta p.a p.b d η) ^ 2)
      ≤ ENNReal.ofReal (Meta p.a p.b d η) := by
    calc M.zeta p.α + M.DmuC p.α * (ENNReal.ofReal p.a * ENNReal.ofReal (Meta p.a p.b d η)
          + ENNReal.ofReal p.b * ENNReal.ofReal (Meta p.a p.b d η) ^ 2)
        ≤ ENNReal.ofReal η + ENNReal.ofReal d
            * ENNReal.ofReal (p.a * Meta p.a p.b d η + p.b * Meta p.a p.b d η ^ 2) := by
          refine add_le_add ?_ (mul_le_mul' hD (le_of_eq ?_))
          · rw [hζη, hη_def, ENNReal.ofReal_toReal hfin]
          · rw [ENNReal.ofReal_add (mul_nonneg p.a_nonneg hM0)
              (mul_nonneg p.b_nonneg (sq_nonneg _)), ENNReal.ofReal_mul p.a_nonneg,
              ENNReal.ofReal_mul p.b_nonneg, ENNReal.ofReal_pow hM0]
      _ = ENNReal.ofReal (η + d * (p.a * Meta p.a p.b d η + p.b * Meta p.a p.b d η ^ 2)) := by
          rw [← ENNReal.ofReal_mul hd0, ← ENNReal.ofReal_add hη0 (mul_nonneg hd0 hq0)]
      _ = ENNReal.ofReal (Meta p.a p.b d η) := by rw [hMeta]
  have hfour : ∀ h Mb, M.FourLawAtZero p.α h (ENNReal.ofReal p.a) (ENNReal.ofReal p.b) Mb :=
    fun h Mb => M.fourLawAtZero_of_params hc hδ p.hα p.hβ0 p.hβ1 p.hu0 p.hu1 p.hL p.hK p.hL0
      h Mb
  exact fun s t h => M.failProb_le_zero hc hδ hα _ _ hfour hbar h s t

/-! ### The headline in terms of the exponent condition (`thm:markov-matching`) -/

set_option linter.unusedVariables false in
/-- **`thm:markov-matching`, finite alternative, as stated**: under the exponent condition
`λ_α < 1`, constants depending only on `α, H, T, B`. -/
theorem markov_matching_of_lambda {α : ℝ} (hα : 1 ≤ α) (hlam : lambda α < 1) (H T : ℕ)
    (hT : 1 ≤ T) (B : ℝ) (hB : 1 ≤ B) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} [Fintype I] (M : Model V I) (hc : M.IsCompat) {g : ℕ}
      (Θ : Model.Phase M g), (∀ i, Θ.count i ≤ T) → ∀ (Sel : Model.Selection M),
      (∀ t, Sel.inverseSum α t ≤ ENNReal.ofReal B) → M.FreshPositive → M.CommonReturns Θ H →
      M.zeta α ≤ ENNReal.ofReal ε → ∀ s t, Θ.θ s = Θ.θ t →
        ∀ h, M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta α :=
  markov_matching_finite_exists (Params.ofLambda hα hlam) H T hT B hB

set_option linter.unusedVariables false in
/-- **`thm:markov-matching`, zero-compatible alternative, as stated**: under the exponent
condition `λ_α < 1`, constants depending only on `α`. -/
theorem markov_matching_zero_of_lambda {α : ℝ} (hα : 1 ≤ α) (hlam : lambda α < 1) :
    ∃ Kc ε : ℝ, 0 < ε ∧ ∀ {V I : Type} (M : Model V I) (hc : M.IsCompat), M.delta = 0 →
      M.zeta α ≤ ENNReal.ofReal ε → ∀ s t h,
        M.failProb s t h ≤ ENNReal.ofReal Kc * M.zeta α :=
  markov_matching_zero_exists (Params.ofLambda hα hlam)

end GraphMarkovMatching.Stopped
