/-
The concrete block profile discharging the abstract invariance of
`Reduction.lean`, with explicit constants.

The profile is the recursion

    B 0 = 40 e,    B (m+1) = e + (2+ρ) B m,

whose closed-form bound is `B m ≤ (2+ρ)^m · 41 e` (proved via the shifted
invariant `B m + e ≤ (2+ρ)^m · 41 e`). The two closure inequalities are proved
in `ℝ` by `nlinarith` and transported to `ℝ≥0∞` through `ofReal` bridges.

Standing numeric hypotheses (with `M = (2+ρ)^(k-1)·41` the profile ceiling):

  * `hsmall : 2α · M e ≤ ρ/2`     — the quadratic corrections are dominated
  * `hAm    : Ar · M ≤ 35`        — the swap contraction beats the profile
                                     growth; via the parameter menu this is
                                     `Ar·2^(k-1) ≤ 5/6`-type up to the
                                     `(1+ρ/2)^(k-1)·41/40` inflation
  * `hCm    : Cr · M e · M ≤ 1`   — the quadratic term is one `e`

The output is the uniform failure bound `≤ ofReal ((2+ρ)^(k-1) · 41 e)` at the
root phase `m = k-1`, for every height.
-/
import GraphMarkovMatching.Support.Reduction

namespace GraphMarkovMatching.Support

open scoped ENNReal Classical

/-! ### The real profile -/

/-- The block profile: `B 0 = 40e`, `B (m+1) = e + (2+ρ) B m`. -/
noncomputable def Bprof (e ρ : ℝ) : ℕ → ℝ
  | 0 => 40 * e
  | m + 1 => e + (2 + ρ) * Bprof e ρ m

lemma Bprof_nonneg {e ρ : ℝ} (he : 0 ≤ e) (hρ : 0 ≤ ρ) : ∀ m, 0 ≤ Bprof e ρ m := by
  intro m
  induction m with
  | zero => simp only [Bprof]; linarith
  | succ m ih => simp only [Bprof]; nlinarith

lemma le_Bprof {e ρ : ℝ} (he : 0 ≤ e) (hρ : 0 ≤ ρ) : ∀ m, e ≤ Bprof e ρ m := by
  intro m
  induction m with
  | zero => simp only [Bprof]; linarith
  | succ m ih =>
      have h := Bprof_nonneg he hρ m
      simp only [Bprof]; nlinarith

/-- The closed-form ceiling, via the shifted invariant `B m + e ≤ (2+ρ)^m·41e`. -/
lemma Bprof_add_le {e ρ : ℝ} (he : 0 ≤ e) (hρ : 0 ≤ ρ) :
    ∀ m, Bprof e ρ m + e ≤ (2 + ρ) ^ m * (41 * e) := by
  intro m
  induction m with
  | zero => simp only [Bprof, pow_zero]; linarith
  | succ m ih =>
      have hB0 := Bprof_nonneg he hρ m
      have h2 := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 2 + ρ)
      simp only [Bprof, pow_succ]
      nlinarith [h2, he, hρ, hB0]

lemma Bprof_le {e ρ : ℝ} (he : 0 ≤ e) (hρ : 0 ≤ ρ) (m : ℕ) :
    Bprof e ρ m ≤ (2 + ρ) ^ m * (41 * e) :=
  le_trans (le_add_of_nonneg_right he) (Bprof_add_le he hρ m)

/-! ### The two real closure inequalities -/

/-- Product-step closure: if `2αb ≤ ρ/2` and `2αe ≤ ρ/6`, the product step
map lands below `e + (2+ρ)b`. -/
lemma prodStep_le {α ρ e b : ℝ} (hα0 : 0 ≤ α) (_he : 0 ≤ e) (hb : 0 ≤ b)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hab : 2 * α * b ≤ ρ / 2) (hae : 2 * α * e ≤ ρ / 6) :
    e + (1 + 2 * α * e) * (2 * b + 2 * α * b ^ 2) ≤ e + (2 + ρ) * b := by
  have h2 : (0 : ℝ) ≤ 2 * α * b := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hab hb,
    mul_le_mul_of_nonneg_right hae hb,
    mul_le_mul_of_nonneg_right
      (mul_le_mul hae hab h2 (by linarith : (0 : ℝ) ≤ ρ / 6)) hb,
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hρ1 hρ0) hb,
    mul_nonneg hρ0 hb, _he, hb]

/-- Swap-step closure: if `Ar·b ≤ 35e`, `Cr·b² ≤ e` and `2αe ≤ 1/36`, the swap
step map lands below `40e = B 0`. -/
lemma swapStep_le {α e b Ar Cr : ℝ} (hα0 : 0 ≤ α) (he : 0 ≤ e) (hb : 0 ≤ b)
    (hAr0 : 0 ≤ Ar) (hCr0 : 0 ≤ Cr)
    (hAr : Ar * b ≤ 35 * e) (hCr : Cr * b ^ 2 ≤ e)
    (hae : 2 * α * e ≤ 1 / 36) :
    e + (1 + 2 * α * e) * (Ar * b + Cr * b ^ 2) ≤ 40 * e := by
  have hX : Ar * b + Cr * b ^ 2 ≤ 36 * e := by linarith
  have hX0 : (0 : ℝ) ≤ Ar * b + Cr * b ^ 2 := by positivity
  have hu0 : (0 : ℝ) ≤ 2 * α * e := by positivity
  have h1 : (2 * α * e) * (Ar * b + Cr * b ^ 2) ≤ (2 * α * e) * (36 * e) :=
    mul_le_mul_of_nonneg_left hX hu0
  have h2 : (2 * α * e) * (36 * e) ≤ (1 / 36) * (36 * e) :=
    mul_le_mul_of_nonneg_right hae (by linarith)
  nlinarith [hX, h1, h2, he]

/-! ### The `ofReal` bridges -/

/-- Bridge for the product step: the `ℝ≥0∞` step expression is below the
`ofReal` of the real step expression. -/
lemma ofReal_prodStep {α e b : ℝ} (hα0 : 0 ≤ α) (he : 0 ≤ e) (hb : 0 ≤ b)
    {η P : ℝ≥0∞} (hη : η ≤ ENNReal.ofReal e) (hP : P ≤ ENNReal.ofReal b) :
    η + (1 + ENNReal.ofReal (2 * α) * η) * (2 * P + ENNReal.ofReal (2 * α) * P ^ 2)
      ≤ ENNReal.ofReal (e + (1 + 2 * α * e) * (2 * b + 2 * α * b ^ 2)) := by
  have h2α : (0 : ℝ) ≤ 2 * α := by linarith
  have h2ae : (0 : ℝ) ≤ 2 * α * e := mul_nonneg h2α he
  have h2ab2 : (0 : ℝ) ≤ 2 * α * b ^ 2 := mul_nonneg h2α (sq_nonneg b)
  have hfac2 : (0 : ℝ) ≤ 2 * b + 2 * α * b ^ 2 := by linarith
  have step1 : η + (1 + ENNReal.ofReal (2 * α) * η)
        * (2 * P + ENNReal.ofReal (2 * α) * P ^ 2)
      ≤ ENNReal.ofReal e
        + (1 + ENNReal.ofReal (2 * α) * ENNReal.ofReal e)
          * (2 * ENNReal.ofReal b + ENNReal.ofReal (2 * α) * ENNReal.ofReal b ^ 2) := by
    gcongr
  refine le_trans step1 (le_of_eq ?_)
  have hb2 : (2 : ℝ≥0∞) * ENNReal.ofReal b = ENNReal.ofReal (2 * b) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hae' : ENNReal.ofReal (2 * α) * ENNReal.ofReal e = ENNReal.ofReal (2 * α * e) :=
    (ENNReal.ofReal_mul h2α).symm
  have hab2 : ENNReal.ofReal (2 * α) * ENNReal.ofReal b ^ 2
      = ENNReal.ofReal (2 * α * b ^ 2) := by
    rw [← ENNReal.ofReal_pow hb, ← ENNReal.ofReal_mul h2α]
  have h1e : (1 : ℝ≥0∞) + ENNReal.ofReal (2 * α * e) = ENNReal.ofReal (1 + 2 * α * e) := by
    rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) h2ae, ENNReal.ofReal_one]
  have hsum : ENNReal.ofReal (2 * b) + ENNReal.ofReal (2 * α * b ^ 2)
      = ENNReal.ofReal (2 * b + 2 * α * b ^ 2) :=
    (ENNReal.ofReal_add (by linarith) h2ab2).symm
  have hmul : ENNReal.ofReal (1 + 2 * α * e) * ENNReal.ofReal (2 * b + 2 * α * b ^ 2)
      = ENNReal.ofReal ((1 + 2 * α * e) * (2 * b + 2 * α * b ^ 2)) :=
    (ENNReal.ofReal_mul (by linarith)).symm
  rw [hae', hab2, hb2, h1e, hsum, hmul,
    ← ENNReal.ofReal_add he (mul_nonneg (by linarith) hfac2)]

/-- Bridge for the swap step, with abstract nonnegative constants `A', C'`. -/
lemma ofReal_swapStep {α e b A' C' : ℝ} (hα0 : 0 ≤ α) (he : 0 ≤ e) (hb : 0 ≤ b)
    (hA0 : 0 ≤ A') (hC0 : 0 ≤ C')
    {η P : ℝ≥0∞} (hη : η ≤ ENNReal.ofReal e) (hP : P ≤ ENNReal.ofReal b) :
    η + (1 + ENNReal.ofReal (2 * α) * η)
        * (ENNReal.ofReal A' * P + ENNReal.ofReal C' * P ^ 2)
      ≤ ENNReal.ofReal (e + (1 + 2 * α * e) * (A' * b + C' * b ^ 2)) := by
  have h2α : (0 : ℝ) ≤ 2 * α := by linarith
  have h2ae : (0 : ℝ) ≤ 2 * α * e := mul_nonneg h2α he
  have hAb : (0 : ℝ) ≤ A' * b := mul_nonneg hA0 hb
  have hCb : (0 : ℝ) ≤ C' * b ^ 2 := mul_nonneg hC0 (sq_nonneg b)
  have hfac2 : (0 : ℝ) ≤ A' * b + C' * b ^ 2 := by linarith
  have step1 : η + (1 + ENNReal.ofReal (2 * α) * η)
        * (ENNReal.ofReal A' * P + ENNReal.ofReal C' * P ^ 2)
      ≤ ENNReal.ofReal e
        + (1 + ENNReal.ofReal (2 * α) * ENNReal.ofReal e)
          * (ENNReal.ofReal A' * ENNReal.ofReal b
            + ENNReal.ofReal C' * ENNReal.ofReal b ^ 2) := by
    gcongr
  refine le_trans step1 (le_of_eq ?_)
  have hae' : ENNReal.ofReal (2 * α) * ENNReal.ofReal e = ENNReal.ofReal (2 * α * e) :=
    (ENNReal.ofReal_mul h2α).symm
  have hA' : ENNReal.ofReal A' * ENNReal.ofReal b = ENNReal.ofReal (A' * b) :=
    (ENNReal.ofReal_mul hA0).symm
  have hC' : ENNReal.ofReal C' * ENNReal.ofReal b ^ 2 = ENNReal.ofReal (C' * b ^ 2) := by
    rw [← ENNReal.ofReal_pow hb, ← ENNReal.ofReal_mul hC0]
  have h1e : (1 : ℝ≥0∞) + ENNReal.ofReal (2 * α * e) = ENNReal.ofReal (1 + 2 * α * e) := by
    rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) h2ae, ENNReal.ofReal_one]
  have hsum : ENNReal.ofReal (A' * b) + ENNReal.ofReal (C' * b ^ 2)
      = ENNReal.ofReal (A' * b + C' * b ^ 2) :=
    (ENNReal.ofReal_add hAb hCb).symm
  have hmul : ENNReal.ofReal (1 + 2 * α * e) * ENNReal.ofReal (A' * b + C' * b ^ 2)
      = ENNReal.ofReal ((1 + 2 * α * e) * (A' * b + C' * b ^ 2)) :=
    (ENNReal.ofReal_mul (by linarith)).symm
  rw [hae', hA', hC', h1e, hsum, hmul,
    ← ENNReal.ofReal_add he (mul_nonneg (by linarith) hfac2)]

/-! ### The concrete uniform bound -/

universe u
variable {V : Type u}

/-- **The concrete block theorem.** Under the parameter hypotheses of the
contraction lemma and the three numeric hypotheses (`hsmall`, `hAm`, `hCm`,
with `M = (2+ρ)^(k-1)·41` the profile ceiling), the phase potentials obey the
profile uniformly in the height:

    Ψ(m,n) ≤ ofReal (Bprof e ρ m)        (m ≤ k-1, all n). -/
theorem PsiK_le_concrete {α δ L K ρ e : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hK0 : 0 ≤ K)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (he : 0 ≤ e)
    (ν : ℕ → PMF V) (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a) (k : ℕ)
    (hη : ∀ m, m ≤ k - 1 → Phi α (ν m) R₀ ≤ ENNReal.ofReal e)
    (hsmall : 2 * α * ((2 + ρ) ^ (k - 1) * (41 * e)) ≤ ρ / 2)
    (hAm : (2 * L + 2 * (1 + δ) * K) * ((2 + ρ) ^ (k - 1) * 41) ≤ 35)
    (hCm : (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
        * ((2 + ρ) ^ (k - 1) * (41 * e)) * ((2 + ρ) ^ (k - 1) * 41) ≤ 1) :
    ∀ n m, m ≤ k - 1 → PsiK α ν R₀ k m n ≤ ENNReal.ofReal (Bprof e ρ m) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hρ0' : (0 : ℝ) ≤ ρ := hρ0.le
  have h2α : (0 : ℝ) ≤ 2 * α := by linarith
  set Me : ℝ := (2 + ρ) ^ (k - 1) * (41 * e) with hMe
  have hMe0 : 0 ≤ Me := by
    rw [hMe]; positivity
  -- profile ceiling on the relevant range
  have hBle : ∀ m, m ≤ k - 1 → Bprof e ρ m ≤ Me := by
    intro m hm
    calc Bprof e ρ m ≤ (2 + ρ) ^ m * (41 * e) := Bprof_le he hρ0' m
      _ ≤ (2 + ρ) ^ (k - 1) * (41 * e) := by
          have h1a : (1 : ℝ) ≤ 2 + ρ := by linarith
          have hpow : (2 + ρ) ^ m ≤ (2 + ρ) ^ (k - 1) := by
            calc (2 + ρ) ^ m = (2 + ρ) ^ m * 1 := (mul_one _).symm
              _ ≤ (2 + ρ) ^ m * (2 + ρ) ^ (k - 1 - m) :=
                  mul_le_mul_of_nonneg_left (one_le_pow₀ h1a)
                    (pow_nonneg (by linarith) m)
              _ = (2 + ρ) ^ (m + (k - 1 - m)) := (pow_add _ _ _).symm
              _ = (2 + ρ) ^ (k - 1) := by rw [Nat.add_sub_cancel' hm]
          have h41 : (0 : ℝ) ≤ 41 * e := by linarith
          exact mul_le_mul_of_nonneg_right hpow h41
  -- smallness of `2αe`, from the ceiling hypothesis (the pow is ≥ 1)
  have hone : (1 : ℝ) ≤ (2 + ρ) ^ (k - 1) := one_le_pow₀ (by linarith)
  have h41e : 41 * e ≤ Me := by
    rw [hMe]
    nlinarith [hone, he]
  have h82 : 2 * α * (41 * e) ≤ ρ / 2 :=
    le_trans (mul_le_mul_of_nonneg_left h41e h2α) hsmall
  have hae : 2 * α * e ≤ ρ / 82 := by nlinarith [h82]
  have hae_pr : 2 * α * e ≤ ρ / 6 := by linarith
  have hae_sw : 2 * α * e ≤ 1 / 36 := by nlinarith [hae, hρ1, hρ0']
  -- the swap constants
  set Ar : ℝ := 2 * L + 2 * (1 + δ) * K with hAr
  set Cr : ℝ := 2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2 with hCr
  have hδ' : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδ
  have hAr0 : 0 ≤ Ar := by rw [hAr]; nlinarith
  have hCr0 : 0 ≤ Cr := by
    rw [hCr]
    have hc := chordConst_nonneg hα0
    nlinarith [sq_nonneg α, mul_nonneg hL0 hc]
  -- swap-step ingredients at `b = Bprof e ρ (k-1)`
  have hBk := hBle (k - 1) le_rfl
  have hBk0 := Bprof_nonneg he hρ0' (k - 1)
  have hArb : Ar * Bprof e ρ (k - 1) ≤ 35 * e := by
    have h1 : Ar * Bprof e ρ (k - 1) ≤ Ar * Me :=
      mul_le_mul_of_nonneg_left hBk hAr0
    have h2 : Ar * Me ≤ 35 * e := by
      rw [hMe, show (2 + ρ) ^ (k - 1) * (41 * e) = ((2 + ρ) ^ (k - 1) * 41) * e from by ring,
          ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hAm he
    linarith
  have hCrb : Cr * Bprof e ρ (k - 1) ^ 2 ≤ e := by
    have hsq : Bprof e ρ (k - 1) ^ 2 ≤ Me ^ 2 := by nlinarith [hBk, hBk0]
    have h1 : Cr * Bprof e ρ (k - 1) ^ 2 ≤ Cr * Me ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hCr0
    have h2 : Cr * Me ^ 2 ≤ e := by
      have e1 : Cr * Me ^ 2 = (Cr * Me * ((2 + ρ) ^ (k - 1) * 41)) * e := by
        rw [hMe]; ring
      rw [e1]
      calc (Cr * Me * ((2 + ρ) ^ (k - 1) * 41)) * e ≤ 1 * e := by
            apply mul_le_mul_of_nonneg_right _ he
            rw [hMe]
            exact hCm
        _ = e := one_mul e
    linarith
  -- feed the abstract invariance
  refine PsiK_le_of_invariant hα hδ hL0 hK0 hL hK ν R₀ hrefl hsymm k
    (fun m => ENNReal.ofReal (Bprof e ρ m)) ?_ ?_ ?_
  · -- base: `η_m ≤ e ≤ Bprof m`
    intro m hm
    exact le_trans (hη m hm) (ENNReal.ofReal_le_ofReal (le_Bprof he hρ0' m))
  · -- product closure
    intro m hm1
    have hm : m ≤ k - 1 := le_trans (Nat.le_succ m) hm1
    have hb0 := Bprof_nonneg he hρ0' m
    have hab : 2 * α * Bprof e ρ m ≤ ρ / 2 :=
      le_trans (mul_le_mul_of_nonneg_left (hBle m hm) h2α) hsmall
    calc Phi α (ν (m + 1)) R₀
          + (1 + ENNReal.ofReal (2 * α) * Phi α (ν (m + 1)) R₀)
            * (2 * ENNReal.ofReal (Bprof e ρ m)
              + ENNReal.ofReal (2 * α) * ENNReal.ofReal (Bprof e ρ m) ^ 2)
        ≤ ENNReal.ofReal (e + (1 + 2 * α * e)
            * (2 * Bprof e ρ m + 2 * α * Bprof e ρ m ^ 2)) :=
          ofReal_prodStep hα0 he hb0 (hη (m + 1) hm1) le_rfl
      _ ≤ ENNReal.ofReal (e + (2 + ρ) * Bprof e ρ m) :=
          ENNReal.ofReal_le_ofReal
            (prodStep_le hα0 he hb0 hρ0' hρ1 hab hae_pr)
      _ = ENNReal.ofReal (Bprof e ρ (m + 1)) := by
          simp only [Bprof]
  · -- swap closure
    calc Phi α (ν 0) R₀
          + (1 + ENNReal.ofReal (2 * α) * Phi α (ν 0) R₀)
            * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K)
                * ENNReal.ofReal (Bprof e ρ (k - 1))
              + ENNReal.ofReal (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
                * ENNReal.ofReal (Bprof e ρ (k - 1)) ^ 2)
        ≤ ENNReal.ofReal (e + (1 + 2 * α * e)
            * (Ar * Bprof e ρ (k - 1) + Cr * Bprof e ρ (k - 1) ^ 2)) := by
          rw [hAr, hCr]
          exact ofReal_swapStep hα0 he hBk0
            (by rw [← hAr]; exact hAr0) (by rw [← hCr]; exact hCr0)
            (hη 0 (Nat.zero_le _)) le_rfl
      _ ≤ ENNReal.ofReal (40 * e) :=
          ENNReal.ofReal_le_ofReal
            (swapStep_le hα0 he hBk0 hAr0 hCr0 hArb hCrb hae_sw)
      _ = ENNReal.ofReal (Bprof e ρ 0) := by simp only [Bprof]

/-- **The concrete failure bound at the root phase**: for every height `n`,
two independent phase-labelled trees fail to admit a matching in
`AutK k (k-1) n` with probability at most `(2+ρ)^(k-1) · 41 e`. -/
theorem karyMatching_failure_le {α δ L K ρ e : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hK0 : 0 ≤ K)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (he : 0 ≤ e)
    (ν : ℕ → PMF V) (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a) (k : ℕ)
    (hη : ∀ m, m ≤ k - 1 → Phi α (ν m) R₀ ≤ ENNReal.ofReal e)
    (hsmall : 2 * α * ((2 + ρ) ^ (k - 1) * (41 * e)) ≤ ρ / 2)
    (hAm : (2 * L + 2 * (1 + δ) * K) * ((2 + ρ) ^ (k - 1) * 41) ≤ 35)
    (hCm : (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
        * ((2 + ρ) ^ (k - 1) * (41 * e)) * ((2 + ρ) ^ (k - 1) * 41) ≤ 1)
    (n : ℕ) :
    ∑' x, fullMuK ν k (k - 1) n x
        * qE (fullMuK ν k (k - 1) n) (fullSimK R₀ k (k - 1) n) x
      ≤ ENNReal.ofReal ((2 + ρ) ^ (k - 1) * (41 * e)) := by
  have h1 : ∑' x, fullMuK ν k (k - 1) n x
        * qE (fullMuK ν k (k - 1) n) (fullSimK R₀ k (k - 1) n) x
      ≤ PsiK α ν R₀ k (k - 1) n :=
    meanBad_le_Phi (by linarith) (fullSimK_refl R₀ hrefl k n (k - 1))
  have h2 := PsiK_le_concrete hα hδ hL0 hK0 hL hK hρ0 hρ1 he ν R₀ hrefl hsymm k
    hη hsmall hAm hCm n (k - 1) le_rfl
  have h3 : Bprof e ρ (k - 1) ≤ (2 + ρ) ^ (k - 1) * (41 * e) :=
    Bprof_le he hρ0.le (k - 1)
  exact le_trans h1 (le_trans h2 (ENNReal.ofReal_le_ofReal h3))

end GraphMarkovMatching.Support
