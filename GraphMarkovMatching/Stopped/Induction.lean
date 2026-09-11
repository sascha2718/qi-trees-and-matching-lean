/-
The height induction of `markov_matching_new_proof.tex` (`sec:completion`): the scalar
barrier `ζ + D_μ Q(M) ≤ M` of `eq:scalar-barrier-condition` propagates the bound `M` on
every equal-phase restricted potential from the heights below `h+1` to the height `h+1`,
through the uniform zero bound `Z` (`z_le_fixed`), the weighted zero bound `E(M)`
(`wZero_le_Efun`), the child-pair bound `Q(M)` (`childPair_le_Qfun`) and the independent
root (`P_succ_le`).

* `wZeroD_eq_wZero`, `sim_symm`: the bridge from the process laws to the abstract
  four-law contraction;
* `fourLawAt_of_params`, `fourLawAtZero_of_params`: `thm:four-law-contraction` supplies
  the four-law input at every height, in both alternatives;
* `P_le_finite`, `failProb_le_finite`, `failProb_le_finite_fresh`: the finite
  alternative, with the failure bounds `Z + M` for equal-phase pairs and `M` for fresh
  pairs;
* `P_le_zero`, `failProb_le_zero`: the zero-compatible alternative, with the failure bound
  `M` for every pair.
-/
import GraphMarkovMatching.Stopped.WeightedExpansion
import GraphMarkovMatching.Stopped.Mixture
import GraphMarkovMatching.Stopped.Root

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

namespace Model

variable {V I : Type} (M : Model V I)

/-! ### The bridge to the four-law contraction (`sec:contraction-extension`) -/

/-- The abstract weighted zero integral of the process laws is the weighted zero integral
against the singleton target (`sec:one-weight`). -/
lemma wZeroD_eq_wZero (α : ℝ) (s t t' : I) (h : ℕ) :
    wZeroD α (M.rho s h) (M.rho t h) (M.rho t' h) (M.sim h) = M.wZero α s {t} t' h := by
  rw [wZeroD, wZero]
  refine tsum_congr fun x => ?_
  simp [ZeroEv, deg, W]

/-- Matching at height `h` is symmetric for a compatible model (`sec:statement`). -/
lemma sim_symm (hc : M.IsCompat) (h : ℕ) : ∀ a b, M.sim h a b → M.sim h b a :=
  fullSim_symm M.srel (M.srel_symm hc) h

/-- The four-law input at every height from the scalar parameters
(`thm:four-law-contraction` applied to the process laws of equal phase). -/
theorem fourLawAt_of_params (hc : M.IsCompat) {α β u L K L0 : ℝ} (hα : 1 ≤ α) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hu0 : 0 < u) (hu1 : u < 1)
    (hL : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α β q ≤ L)
    (hK : ∀ q, 0 ≤ q → q ≤ 1 → (q - β) * (1 - q) ^ α ≤ K)
    (hL0 : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α 0 q ≤ L0)
    {g : ℕ} (Θ : Phase M g) (h : ℕ) (Mb Zm E : ℝ≥0∞) :
    M.FourLawAt Θ α h (ENNReal.ofReal (2 * (L + K))) (ENNReal.ofReal (Cfun α L0 u))
      (ENNReal.ofReal (2 + 2 * β)) Mb Zm E := by
  intro s₁ s₂ t₁ t₂ h1 h2 h3 hM hz hE
  have e1 : Θ.θ s₁ = Θ.θ t₂ := h1.trans h3.symm
  have e2 : Θ.θ s₂ = Θ.θ t₂ := h2.trans h3.symm
  have hE' : ∀ s t t', Θ.θ s = Θ.θ t → Θ.θ s = Θ.θ t' →
      wZeroD α (M.rho s h) (M.rho t h) (M.rho t' h) (M.sim h) ≤ E := by
    intro s t t' hst hst'
    rw [M.wZeroD_eq_wZero]
    refine hE s {t} t' (Set.singleton_nonempty t) ?_ hst'.symm
    intro t'' ht''
    rw [Set.mem_singleton_iff.1 ht'']
    exact hst.symm
  exact fourLaw_contraction hα hβ0 hβ1 hu0 hu1 hL hK hL0 (M.rho s₁ h) (M.rho s₂ h)
    (M.rho t₁ h) (M.rho t₂ h) (M.sim h) (M.sim_symm hc h) Mb Zm E
    (hM s₁ t₁ h1) (hM s₁ t₂ e1) (hM s₂ t₁ h2) (hM s₂ t₂ e2)
    (hM t₁ s₁ h1.symm) (hM t₂ s₁ e1.symm) (hM t₁ s₂ h2.symm) (hM t₂ s₂ e2.symm)
    (hz s₁ t₁ h1) (hz s₁ t₂ e1) (hz s₂ t₁ h2) (hz s₂ t₂ e2)
    (hz t₁ s₁ h1.symm) (hz t₂ s₁ e1.symm) (hz t₁ s₂ h2.symm) (hz t₂ s₂ e2.symm)
    (hE' s₁ t₁ t₂ h1 e1) (hE' s₁ t₂ t₁ e1 h1) (hE' s₂ t₁ t₂ h2 e2) (hE' s₂ t₂ t₁ e2 h2)

/-- The four-law input when `δ = 0`: the zero masses and weighted zero integrals vanish
(`sec:positive-degrees`), and `thm:four-law-contraction` reduces to `a M + b M²`. -/
theorem fourLawAtZero_of_params (hc : M.IsCompat) (hδ : M.delta = 0) {α β u L K L0 : ℝ}
    (hα : 1 ≤ α) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hu0 : 0 < u) (hu1 : u < 1)
    (hL : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α β q ≤ L)
    (hK : ∀ q, 0 ≤ q → q ≤ 1 → (q - β) * (1 - q) ^ α ≤ K)
    (hL0 : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α 0 q ≤ L0) (h : ℕ) (Mb : ℝ≥0∞) :
    M.FourLawAtZero α h (ENNReal.ofReal (2 * (L + K))) (ENNReal.ofReal (Cfun α L0 u)) Mb := by
  intro s₁ s₂ t₁ t₂ hM
  have hz : ∀ s t, zMass (M.rho s h) (M.rho t h) (M.sim h) ≤ 0 :=
    fun s t => (M.z_eq_zero_of_delta_zero hc hδ s t h).le
  have hE : ∀ s t t', wZeroD α (M.rho s h) (M.rho t h) (M.rho t' h) (M.sim h) ≤ 0 := by
    intro s t t'
    rw [M.wZeroD_eq_wZero]
    exact (M.wZero_eq_zero_of_delta_zero hc hδ s (Set.singleton_nonempty t) t' h).le
  have key := fourLaw_contraction hα hβ0 hβ1 hu0 hu1 hL hK hL0 (M.rho s₁ h) (M.rho s₂ h)
    (M.rho t₁ h) (M.rho t₂ h) (M.sim h) (M.sim_symm hc h) Mb 0 0
    (hM s₁ t₁) (hM s₁ t₂) (hM s₂ t₁) (hM s₂ t₂) (hM t₁ s₁) (hM t₂ s₁) (hM t₁ s₂) (hM t₂ s₂)
    (hz s₁ t₁) (hz s₁ t₂) (hz s₂ t₁) (hz s₂ t₂) (hz t₁ s₁) (hz t₂ s₁) (hz t₁ s₂) (hz t₂ s₂)
    (hE s₁ t₁ t₂) (hE s₁ t₂ t₁) (hE s₂ t₁ t₂) (hE s₂ t₂ t₁)
  simpa only [mul_zero, add_zero] using key

/-! ### The finite alternative (`sec:completion`) -/

/-- **The height induction, finite alternative** (`sec:completion`): under the scalar
barrier `ζ + D_μ Q(M) ≤ M` with `Q` evaluated at the uniform zero bound `Z` and the weighted
bound `E(M)`, every equal-phase restricted potential at every height is at most `M`. -/
theorem P_le_finite [Fintype I] (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0)
    (hFP : M.FreshPositive) {α : ℝ} (hα : 1 ≤ α) {g : ℕ} (Θ : Phase M g) {T : ℕ}
    (hT : ∀ i, Θ.count i ≤ T) {H : ℕ} (hCR : M.CommonReturns Θ H) (Sel : Selection M)
    {B : ℝ≥0∞} (hB : ∀ t, Sel.budget α t ≤ B) (a b γ : ℝ≥0∞)
    (hfour : ∀ h Mb Zm E, M.FourLawAt Θ α h a b γ Mb Zm E) {Z : ℝ≥0∞}
    (hZ : SHe H * (M.delta + (T : ℝ≥0∞) ^ 2 * Z ^ 2) ≤ Z) {Mb : ℝ≥0∞}
    (hbar : M.zeta α + M.DmuC α * Qfun α a b γ (Cmix α B) Z
        (Efun α H T B (M.fRoot α) (M.RmuC α) Z Mb) Mb ≤ Mb) :
    ∀ h s t, Θ.θ s = Θ.θ t → M.P α s t h ≤ Mb := by
  have hζ : M.zeta α ≤ Mb := le_self_add.trans hbar
  have hzZ : ∀ h s t, Θ.θ s = Θ.θ t → M.z s t h ≤ Z :=
    M.z_le_fixed hc hb0 hFP Θ hT hCR hZ
  intro h
  refine Nat.strong_induction_on h ?_
  intro h ih
  cases h with
  | zero =>
    intro s t _
    exact (M.P_zero_le hc hα s t).trans hζ
  | succ h' =>
    intro s t hst
    have hM' : ∀ s u, Θ.θ s = Θ.θ u → M.P α s u h' ≤ Mb := ih h' (Nat.lt_succ_self h')
    have hE := M.wZero_le_Efun hc hb0 hFP hα Θ hT hCR Sel hB (h := h') (Mb := Mb) (Zm := Z)
      (fun j hj => ih j (Nat.lt_succ_of_lt hj)) (fun j _ => hzZ j)
    have hQ := M.childPair_le_Qfun hc hb0 hα Θ Sel hB (hfour h' Mb Z _) hM' (hzZ h') hE s t hst
    exact (M.P_succ_le hc hα s t h' hQ).trans hbar

/-- The failure probability of every equal-phase pair is at most `Z + M`
(`sec:completion`). -/
theorem failProb_le_finite [Fintype I] (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0)
    (hFP : M.FreshPositive) {α : ℝ} (hα : 1 ≤ α) {g : ℕ} (Θ : Phase M g) {T : ℕ}
    (hT : ∀ i, Θ.count i ≤ T) {H : ℕ} (hCR : M.CommonReturns Θ H) (Sel : Selection M)
    {B : ℝ≥0∞} (hB : ∀ t, Sel.budget α t ≤ B) (a b γ : ℝ≥0∞)
    (hfour : ∀ h Mb Zm E, M.FourLawAt Θ α h a b γ Mb Zm E) {Z : ℝ≥0∞}
    (hZ : SHe H * (M.delta + (T : ℝ≥0∞) ^ 2 * Z ^ 2) ≤ Z) {Mb : ℝ≥0∞}
    (hbar : M.zeta α + M.DmuC α * Qfun α a b γ (Cmix α B) Z
        (Efun α H T B (M.fRoot α) (M.RmuC α) Z Mb) Mb ≤ Mb) :
    ∀ h s t, Θ.θ s = Θ.θ t → M.failProb s t h ≤ Z + Mb := by
  intro h s t hst
  calc M.failProb s t h ≤ M.P α s t h + M.z s t h := M.failProb_le α (by linarith) s t h
    _ ≤ Mb + Z :=
      add_le_add (M.P_le_finite hc hb0 hFP hα Θ hT hCR Sel hB a b γ hfour hZ hbar h s t hst)
        (M.z_le_fixed hc hb0 hFP Θ hT hCR hZ h s t hst)
    _ = Z + Mb := add_comm _ _

/-- For fresh initial types the zero term vanishes by fresh positivity: the failure
probability is at most `M` (`sec:completion`). -/
theorem failProb_le_finite_fresh [Fintype I] (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0)
    (hFP : M.FreshPositive) {α : ℝ} (hα : 1 ≤ α) {g : ℕ} (Θ : Phase M g) {T : ℕ}
    (hT : ∀ i, Θ.count i ≤ T) {H : ℕ} (hCR : M.CommonReturns Θ H) (Sel : Selection M)
    {B : ℝ≥0∞} (hB : ∀ t, Sel.budget α t ≤ B) (a b γ : ℝ≥0∞)
    (hfour : ∀ h Mb Zm E, M.FourLawAt Θ α h a b γ Mb Zm E) {Z : ℝ≥0∞}
    (hZ : SHe H * (M.delta + (T : ℝ≥0∞) ^ 2 * Z ^ 2) ≤ Z) {Mb : ℝ≥0∞}
    (hbar : M.zeta α + M.DmuC α * Qfun α a b γ (Cmix α B) Z
        (Efun α H T B (M.fRoot α) (M.RmuC α) Z Mb) Mb ≤ Mb) :
    ∀ h s t, M.fresh s → M.fresh t → M.failProb s t h ≤ Mb := by
  intro h s t hs ht
  have hst : Θ.θ s = Θ.θ t := by rw [Θ.fresh_zero s hs, Θ.fresh_zero t ht]
  have hz : M.z s t h = 0 := by
    rw [← M.zeroMass_singleton]
    exact M.zeroMass_eq_zero_of_fresh hFP hs ht (Set.mem_singleton t) h
  calc M.failProb s t h ≤ M.P α s t h + M.z s t h := M.failProb_le α (by linarith) s t h
    _ = M.P α s t h := by rw [hz, add_zero]
    _ ≤ Mb := M.P_le_finite hc hb0 hFP hα Θ hT hCR Sel hB a b γ hfour hZ hbar h s t hst

/-! ### The zero-compatible alternative (`sec:completion`) -/

/-- **The height induction, zero-compatible alternative** (`sec:completion`): with
`δ = 0`, under `ζ + D_μ (a M + b M²) ≤ M`, every restricted potential at every height is
at most `M`. -/
theorem P_le_zero (hc : M.IsCompat) (hδ : M.delta = 0) {α : ℝ} (hα : 1 ≤ α) (a b : ℝ≥0∞)
    (hfour : ∀ h Mb, M.FourLawAtZero α h a b Mb) {Mb : ℝ≥0∞}
    (hbar : M.zeta α + M.DmuC α * (a * Mb + b * Mb ^ 2) ≤ Mb) :
    ∀ h s t, M.P α s t h ≤ Mb := by
  have hζ : M.zeta α ≤ Mb := le_self_add.trans hbar
  intro h
  refine Nat.strong_induction_on h ?_
  intro h ih
  cases h with
  | zero =>
    intro s t
    exact (M.P_zero_le hc hα s t).trans hζ
  | succ h' =>
    intro s t
    have hM' : ∀ s u, M.P α s u h' ≤ Mb := ih h' (Nat.lt_succ_self h')
    have hQ := M.childPair_le_of_delta_zero hc hδ hα (hfour h' Mb) hM' s t
    exact (M.P_succ_le hc hα s t h' hQ).trans hbar

/-- With `δ = 0` the zero masses vanish, so the failure probability of every pair is at
most `M` (`sec:completion`). -/
theorem failProb_le_zero (hc : M.IsCompat) (hδ : M.delta = 0) {α : ℝ} (hα : 1 ≤ α)
    (a b : ℝ≥0∞) (hfour : ∀ h Mb, M.FourLawAtZero α h a b Mb) {Mb : ℝ≥0∞}
    (hbar : M.zeta α + M.DmuC α * (a * Mb + b * Mb ^ 2) ≤ Mb) :
    ∀ h s t, M.failProb s t h ≤ Mb := by
  intro h s t
  calc M.failProb s t h ≤ M.P α s t h + M.z s t h := M.failProb_le α (by linarith) s t h
    _ = M.P α s t h := by rw [M.z_eq_zero_of_delta_zero hc hδ s t h, add_zero]
    _ ≤ Mb := M.P_le_zero hc hδ hα a b hfour hbar h s t

end Model

end GraphMarkovMatching.Stopped
