/-
Averaging the transitions in `arbitrary_offspring_matching.tex` (`sec:averaging`):
the zero-mixture convexity lemma `thm:zero-mixture-convexity`, and the bound `Q(M)` on the
restricted potential of the source child-pair mixture against the target child-pair
mixture, in the finite alternative (selected components, mixture error
`8(α+1) B (1 + αM) E(M)`) and in the zero-compatible alternative (countable Jensen, no
error).

The four-law contraction enters as a hypothesis `hfour`, quantified over the process laws
at height `h`, so that this module does not depend on `FourLaw.lean`.
-/
import GraphMarkovMatching.Stopped.Moments
import GraphMarkovMatching.Stopped.FourLaw
import GraphMarkovMatching.Potential.Jensen

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

/-- The real inequality behind `thm:zero-mixture-convexity`: with `w`, `r` in place of the
note's masses and `N = 1 - w`, the convex minorant `(1-w)^α (1-w-r) r^{-α}` differs from
`(1-r) r^{-α}` by at most `(α+1) w r^{-α}`, by Bernoulli's inequality for the exponent
`α + 1`. -/
private lemma zero_mixture_real {α W Rb : ℝ} (hα : 1 ≤ α) (hW : 0 ≤ W) (hRb : 0 < Rb)
    (hsum : Rb + W ≤ 1) :
    phi α (1 - Rb)
      ≤ (1 - W) * phi α ((1 - W - Rb) / (1 - W)) + (α + 1) * W * Rb ^ (-α) := by
  have hN : 0 < 1 - W := by linarith
  have hRα : 0 < Rb ^ α := Real.rpow_pos_of_pos hRb α
  have hNα1 : (1 - W) ^ α ≤ 1 := Real.rpow_le_one hN.le (by linarith) (by linarith)
  have hB : 1 - (1 - W) ^ (α + 1) ≤ (α + 1) * (1 - (1 - W)) :=
    one_sub_rpow_le (by linarith) hN.le
  have hN1 : (1 - W) ^ (α + 1) = (1 - W) ^ α * (1 - W) := Real.rpow_add_one hN.ne' α
  have hprod : Rb * (1 - W) ^ α ≤ Rb := mul_le_of_le_one_right hRb.le hNα1
  have e1 : phi α (1 - Rb) = (1 - Rb) / Rb ^ α := by
    rw [phi]; congr 2; ring
  have e2 : (1 - W) * phi α ((1 - W - Rb) / (1 - W))
      = (1 - W - Rb) * (1 - W) ^ α / Rb ^ α := by
    rw [phi]
    have h1m : 1 - (1 - W - Rb) / (1 - W) = Rb / (1 - W) := by
      rw [eq_div_iff hN.ne', sub_mul, div_mul_cancel₀ _ hN.ne']
      ring
    rw [h1m, Real.div_rpow hRb.le hN.le]
    field_simp
  have e3 : (α + 1) * W * Rb ^ (-α) = (α + 1) * W / Rb ^ α := by
    rw [Real.rpow_neg hRb.le, div_eq_mul_inv]
  rw [e1, e2, e3, ← add_div, div_le_div_iff_of_pos_right hRα]
  nlinarith [hB, hN1, hprod]

/-- **Zero-mixture convexity** (`thm:zero-mixture-convexity`): for probability weights
`p` and degrees `r i ∈ [0,1]`, with `r = ∑ p i r i` and `w = ∑_{r i = 0} p i`,

    𝟙{r>0} (1-r)/r^α ≤ ∑ p i 𝟙{r i > 0} (1-r i)/(r i)^α + (α+1) w 𝟙{r>0} r^{-α}.

Stated in the safe `phiE` convention with restricted weights. -/
theorem zero_mixture_convexity {ι : Type} {α : ℝ} (hα : 1 ≤ α) (p : ι → ℝ≥0∞)
    (hp : ∑' i, p i = 1) (r : ι → ℝ≥0∞) (hr : ∀ i, r i ≤ 1) :
    (if (∑' i, p i * r i) = 0 then 0 else phiE α (1 - (∑' i, p i * r i).toReal))
      ≤ (∑' i, p i * (if r i = 0 then 0 else phiE α (1 - (r i).toReal)))
        + ENNReal.ofReal (α + 1) * (∑' i, p i * (if r i = 0 then 1 else 0))
          * (if (∑' i, p i * r i) = 0 then 0 else (∑' i, p i * r i) ^ (-α)) := by
  set rbar := ∑' i, p i * r i with hrbar_def
  by_cases h0 : rbar = 0
  · rw [if_pos h0]
    exact zero_le
  rw [if_neg h0, if_neg h0]
  set w := ∑' i, p i * (if r i = 0 then 1 else 0) with hw_def
  set N := ∑' i, p i * (if r i = 0 then 0 else 1) with hN_def
  set A := ∑' i, p i * (if r i = 0 then 0 else 1 - r i) with hA_def
  set S := ∑' i, p i * (if r i = 0 then 0 else phiE α (1 - (r i).toReal)) with hS_def
  have hr_top : ∀ i, r i ≠ ⊤ := fun i => ne_top_of_le_ne_top ENNReal.one_ne_top (hr i)
  -- the mass identities `w + N = 1` and `A + r = N`
  have hwN : w + N = 1 := by
    rw [hw_def, hN_def, ← ENNReal.tsum_add]
    refine Eq.trans (tsum_congr fun i => ?_) hp
    rw [← mul_add]
    by_cases hi : r i = 0 <;> simp [hi]
  have hAr : A + rbar = N := by
    rw [hA_def, hrbar_def, hN_def, ← ENNReal.tsum_add]
    refine tsum_congr fun i => ?_
    rw [← mul_add]
    by_cases hi : r i = 0
    · simp [hi]
    · rw [if_neg hi, if_neg hi, tsub_add_cancel_of_le (hr i)]
  have hN1 : N ≤ 1 := by rw [← hwN]; exact le_add_self
  have hw1 : w ≤ 1 := by rw [← hwN]; exact le_self_add
  have hN_top : N ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hN1
  have hw_top : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  have hrN : rbar ≤ N := by rw [← hAr]; exact le_add_self
  have hAN : A ≤ N := by rw [← hAr]; exact le_self_add
  have hr_top' : rbar ≠ ⊤ := ne_top_of_le_ne_top hN_top hrN
  have hA_top : A ≠ ⊤ := ne_top_of_le_ne_top hN_top hAN
  have hN0 : N ≠ 0 := fun h => h0 (le_antisymm (h ▸ hrN) zero_le)
  -- Jensen for the weights normalised on the positive components
  set c := N⁻¹ with hc_def
  have hcN : c * N = 1 := ENNReal.inv_mul_cancel hN0 hN_top
  have hJ := phiE_tsum_jensen hα (fun i => c * (p i * (if r i = 0 then 0 else 1)))
    (fun i => 1 - (r i).toReal)
    (by rw [ENNReal.tsum_mul_left, ← hN_def, hcN])
    (fun i => by
      have := ENNReal.toReal_mono ENNReal.one_ne_top (hr i)
      rw [ENNReal.toReal_one] at this
      linarith)
    (fun i => by simp)
  have hmean : (∑' i, c * (p i * (if r i = 0 then 0 else 1))
      * ENNReal.ofReal (1 - (r i).toReal)) = c * A := by
    rw [hA_def, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun i => ?_
    by_cases hi : r i = 0
    · simp [hi]
    · rw [if_neg hi, if_neg hi, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (hr_top i), ENNReal.ofReal_one, mul_one, mul_assoc]
  have hright : (∑' i, c * (p i * (if r i = 0 then 0 else 1)) * phiE α (1 - (r i).toReal))
      = c * S := by
    rw [hS_def, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun i => ?_
    by_cases hi : r i = 0
    · simp [hi]
    · rw [if_neg hi, if_neg hi, mul_one, mul_assoc]
  rw [hmean, hright] at hJ
  have hNJ : N * phiE α (c * A).toReal ≤ S := by
    calc N * phiE α (c * A).toReal ≤ N * (c * S) := mul_le_mul_right hJ _
      _ = (c * N) * S := by ring
      _ = S := by rw [hcN, one_mul]
  -- the real quantities
  set W := w.toReal with hW_def
  set Rb := rbar.toReal with hRb_def
  have hNr : N.toReal = 1 - W := by
    have := congrArg ENNReal.toReal hwN
    rw [ENNReal.toReal_add hw_top hN_top, ENNReal.toReal_one] at this
    linarith
  have hAr' : A.toReal = 1 - W - Rb := by
    have := congrArg ENNReal.toReal hAr
    rw [ENNReal.toReal_add hA_top hr_top', hNr] at this
    linarith
  have hcA : (c * A).toReal = (1 - W - Rb) / (1 - W) := by
    rw [ENNReal.toReal_mul, hc_def, ENNReal.toReal_inv, hNr, hAr', inv_mul_eq_div]
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hRb0 : 0 < Rb := ENNReal.toReal_pos h0 hr_top'
  have hsum : Rb + W ≤ 1 := by
    have := ENNReal.toReal_mono hN_top hrN
    rw [hNr] at this
    linarith
  have hlt1 : 1 - Rb < 1 := by linarith
  have hlt2 : (1 - W - Rb) / (1 - W) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hreal := zero_mixture_real hα hW0 hRb0 hsum
  have hphi0 : 0 ≤ phi α ((1 - W - Rb) / (1 - W)) :=
    phi_nonneg (div_nonneg (by linarith) (by linarith)) hlt2
  have hrpow0 : 0 ≤ Rb ^ (-α) := Real.rpow_nonneg hRb0.le _
  -- assemble in `ℝ≥0∞`
  have hrbar_eq : rbar = ENNReal.ofReal Rb := (ENNReal.ofReal_toReal hr_top').symm
  have hw_eq : w = ENNReal.ofReal W := (ENNReal.ofReal_toReal hw_top).symm
  have hN_eq : N = ENNReal.ofReal (1 - W) := by rw [← hNr, ENNReal.ofReal_toReal hN_top]
  calc phiE α (1 - Rb) = ENNReal.ofReal (phi α (1 - Rb)) := phiE_of_lt hlt1
    _ ≤ ENNReal.ofReal ((1 - W) * phi α ((1 - W - Rb) / (1 - W))
          + (α + 1) * W * Rb ^ (-α)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (1 - W) * ENNReal.ofReal (phi α ((1 - W - Rb) / (1 - W)))
          + ENNReal.ofReal (α + 1) * ENNReal.ofReal W * ENNReal.ofReal (Rb ^ (-α)) := by
        rw [ENNReal.ofReal_add (mul_nonneg (by linarith) hphi0)
            (mul_nonneg (mul_nonneg (by linarith) hW0) hrpow0),
          ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_mul (mul_nonneg (by linarith) hW0),
          ENNReal.ofReal_mul (by linarith)]
    _ = N * phiE α (c * A).toReal + ENNReal.ofReal (α + 1) * w * rbar ^ (-α) := by
        rw [hcA, phiE_of_lt hlt2, hN_eq, hw_eq, hrbar_eq, ENNReal.ofReal_rpow_of_pos hRb0]
    _ ≤ S + ENNReal.ofReal (α + 1) * w * rbar ^ (-α) := add_le_add_left hNJ _

/-! ### Fubini swaps and product integrals -/

/-- A Fubini swap: integrating a countable mixture of integrands is the mixture of the
integrals. -/
lemma tsum_mul_tsum_comm {X J : Type} (f : X → ℝ≥0∞) (g : J → ℝ≥0∞) (F : J → X → ℝ≥0∞) :
    ∑' x, f x * ∑' j, g j * F j x = ∑' j, g j * ∑' x, f x * F j x := by
  calc ∑' x, f x * ∑' j, g j * F j x = ∑' x, ∑' j, f x * (g j * F j x) := by
        refine tsum_congr fun x => ?_
        rw [← ENNReal.tsum_mul_left]
    _ = ∑' j, ∑' x, f x * (g j * F j x) := ENNReal.tsum_comm
    _ = ∑' j, g j * ∑' x, f x * F j x := by
        refine tsum_congr fun j => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => by ring

/-- A Fubini swap with a finite mixture. -/
lemma tsum_mul_finsetSum_comm {X J : Type} (f : X → ℝ≥0∞) (s : Finset J) (g : J → ℝ≥0∞)
    (F : J → X → ℝ≥0∞) :
    ∑' x, f x * ∑ j ∈ s, g j * F j x = ∑ j ∈ s, g j * ∑' x, f x * F j x := by
  calc ∑' x, f x * ∑ j ∈ s, g j * F j x = ∑' x, ∑ j ∈ s, f x * (g j * F j x) := by
        refine tsum_congr fun x => ?_
        rw [Finset.mul_sum]
    _ = ∑ j ∈ s, ∑' x, f x * (g j * F j x) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ = ∑ j ∈ s, g j * ∑' x, f x * F j x := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => by ring

/-- A separated integrand against a product law integrates to the product of the two
one-coordinate integrals (`sec:averaging`: the zero condition on one child and the inverse
weight on its independent sibling). -/
lemma tsum_prod_mul_le {X : Type} (ρ₁ ρ₂ : PMF X) (G : X × X → ℝ≥0∞) (f₁ f₂ : X → ℝ≥0∞)
    (hG : ∀ x, G x = f₁ x.1 * f₂ x.2) {A B : ℝ≥0∞}
    (h₁ : ∑' x, ρ₁ x * f₁ x ≤ A) (h₂ : ∑' x, ρ₂ x * f₂ x ≤ B) :
    ∑' x : X × X, prodPMF ρ₁ ρ₂ x * G x ≤ A * B := by
  calc ∑' x : X × X, prodPMF ρ₁ ρ₂ x * G x
      = ∑' x : X × X, (ρ₁ x.1 * f₁ x.1) * (ρ₂ x.2 * f₂ x.2) := by
        refine tsum_congr fun x => ?_
        rw [hG, prodPMF_apply]
        ring
    _ = (∑' x, ρ₁ x * f₁ x) * (∑' x, ρ₂ x * f₂ x) :=
        tsum_prod_split (fun y => ρ₁ y * f₁ y) (fun y => ρ₂ y * f₂ y)
    _ ≤ A * B := mul_le_mul' h₁ h₂

/-- The restricted inverse power in `if` form is the restricted weight
(`sec:restricted-potential`). -/
lemma ite_rpow_eq_WresD {X : Type} (α : ℝ) (ρ : PMF X) (R : X → X → Prop) (x : X) :
    (if rE ρ R x = 0 then 0 else (rE ρ R x) ^ (-α)) = WresD α ρ R x := by
  by_cases h0 : rE ρ R x = 0
  · rw [if_pos h0, WresD, if_pos h0]
  · rw [if_neg h0, rE_rpow_neg_eq_WresD _ _ _ h0]

/-- The constant bookkeeping of `sec:averaging`: the fixed-pair bound plus the mixture
error `(α+1) B · 4(1+αM) E` is at most `Q(M)` with `C = 4 + 8(α+1)B`. -/
lemma bound_le_Qfun (α : ℝ) (a b γ B Zm E Mb : ℝ≥0∞) :
    (a * Mb + b * Mb ^ 2 + (γ + 4 * ENNReal.ofReal α * Mb) * Zm
        + 4 * (1 + ENNReal.ofReal α * Mb) * E)
      + ENNReal.ofReal (α + 1) * B * (4 * (1 + ENNReal.ofReal α * Mb) * E)
      ≤ Model.Qfun α a b γ (Model.Cmix α B) Zm E Mb := by
  rw [Model.Qfun, Model.Cmix]
  have h8 : (4 + 8 * ENNReal.ofReal (α + 1) * B) * (1 + ENNReal.ofReal α * Mb) * E
      = 4 * (1 + ENNReal.ofReal α * Mb) * E
        + 8 * (ENNReal.ofReal (α + 1) * B * ((1 + ENNReal.ofReal α * Mb) * E)) := by ring
  have h4 : ENNReal.ofReal (α + 1) * B * (4 * (1 + ENNReal.ofReal α * Mb) * E)
      = 4 * (ENNReal.ofReal (α + 1) * B * ((1 + ENNReal.ofReal α * Mb) * E)) := by ring
  rw [h8, h4, ← add_assoc]
  exact add_le_add le_rfl (mul_le_mul' (by norm_num) le_rfl)

namespace Model

variable {V I : Type} (M : Model V I)

/-- The abstract four-law input at height `h`: every four-law comparison of process laws
of equal phase at height `h` with the potentials at most `Mb`, the zero masses at most
`Zm`, and the weighted zero integrals at most `E` obeys the contraction with constants
`a, b, γ`. -/
def FourLawAt {g : ℕ} (Θ : Phase M g) (α : ℝ) (h : ℕ) (a b γ Mb Zm E : ℝ≥0∞) : Prop :=
  ∀ s₁ s₂ t₁ t₂ : I, Θ.θ s₁ = Θ.θ t₁ → Θ.θ s₂ = Θ.θ t₁ → Θ.θ t₂ = Θ.θ t₁ →
    (∀ s u, Θ.θ s = Θ.θ u → M.P α s u h ≤ Mb) →
    (∀ s t, Θ.θ s = Θ.θ t → M.z s t h ≤ Zm) →
    (∀ s (D : Set I) u, D.Nonempty → (∀ t ∈ D, Θ.θ t = Θ.θ s) → Θ.θ u = Θ.θ s →
      M.wZero α s D u h ≤ E) →
    PhiDres α (prodPMF (M.rho s₁ h) (M.rho s₂ h)) (prodPMF (M.rho t₁ h) (M.rho t₂ h))
        (SquareRel (M.sim h))
      ≤ a * Mb + b * Mb ^ 2 + (γ + 4 * ENNReal.ofReal α * Mb) * Zm
        + 4 * (1 + ENNReal.ofReal α * Mb) * E

/-! ### The averaged transition -/

/-- The weighted zero integral against a singleton target, in indicator form. -/
lemma wZero_singleton_eq (α : ℝ) (s a u : I) (h : ℕ) :
    M.wZero α s {a} u h
      = ∑' x, M.rho s h x * ((if M.deg a h x = 0 then 1 else 0) * M.W α u h x) := by
  rw [wZero]
  refine tsum_congr fun x => ?_
  congr 1
  by_cases hx : M.deg a h x = 0
  · have hz : M.ZeroEv {a} h x := fun t ht => by
      rw [Set.mem_singleton_iff.mp ht]
      exact hx
    rw [if_pos hz, if_pos hx, one_mul]
  · have hz : ¬ M.ZeroEv {a} h x := fun hz => hx (hz a (Set.mem_singleton a))
    rw [if_neg hz, if_neg hx, zero_mul]

/-- **The pointwise mixture bound** (`thm:zero-mixture-convexity` at the target child-pair
mixture): the restricted summand against the mixture is at most the mixture of the
component summands plus `(α+1)` times the zero-component mass times the restricted inverse
mixture degree. -/
lemma pointwise_childMix_le {α : ℝ} (hα : 1 ≤ α) (t : I) (h : ℕ)
    (x : FullLab (I × V) h × FullLab (I × V) h) :
    (if rE (M.childMix t h) (SquareRel (M.sim h)) x = 0 then 0
        else phiE α (q (M.childMix t h) (SquareRel (M.sim h)) x))
      ≤ (∑' j, M.π t j
            * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0 then 0
              else phiE α (q (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x)))
        + ENNReal.ofReal (α + 1)
          * (∑' j, M.π t j
              * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0
                then 1 else 0))
          * WresD α (M.childMix t h) (SquareRel (M.sim h)) x := by
  have key := zero_mixture_convexity hα (M.π t) (M.π t).tsum_coe
    (fun j => rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x)
    (fun _ => rE_le_one)
  have hq : ∀ ν : PMF (FullLab (I × V) h × FullLab (I × V) h),
      (1 : ℝ) - (rE ν (SquareRel (M.sim h)) x).toReal = q ν (SquareRel (M.sim h)) x :=
    fun ν => by rw [toReal_rE_eq, sub_sub_cancel]
  simp only [hq, ← M.rE_childMix t h x, ite_rpow_eq_WresD] at key
  exact key

/-- **The main term** of the averaged transition: the mixture over the charged target
transitions of the fixed-pair restricted potentials, each at most `bound`. -/
lemma mixture_main_le {α : ℝ} (t : I) (h : ℕ)
    (σ : PMF (FullLab (I × V) h × FullLab (I × V) h)) {bound : ℝ≥0∞}
    (hb : ∀ j, M.π t j ≠ 0 →
      PhiDres α σ (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) ≤ bound) :
    ∑' x, σ x * ∑' j, M.π t j
        * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0 then 0
          else phiE α (q (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x))
      ≤ bound := by
  rw [tsum_mul_tsum_comm]
  calc ∑' j, M.π t j * ∑' x, σ x
        * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0 then 0
          else phiE α (q (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x))
      ≤ ∑' j, M.π t j * bound := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        by_cases hj : M.π t j = 0
        · rw [hj, zero_mul, zero_mul]
        · exact mul_le_mul' le_rfl (hb j hj)
    _ = bound := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **The split integrals** (`sec:averaging`): for one target component `j` with a zero
child degree and one selected component `j'` supplying the normalising pairing, each of
the four products of a zero condition on one source child with the inverse weights is at
most `E (1 + αM)`, the zero child contributing the weighted zero integral and its
independent sibling the inverse moment. -/
lemma split_integral_le {α : ℝ} (hα : 1 ≤ α) {g : ℕ} (Θ : Phase M g) {h : ℕ} {Mb E : ℝ≥0∞}
    (hM : ∀ s u, Θ.θ s = Θ.θ u → M.P α s u h ≤ Mb)
    (hE : ∀ s (D : Set I) u, D.Nonempty → (∀ t ∈ D, Θ.θ t = Θ.θ s) → Θ.θ u = Θ.θ s →
      M.wZero α s D u h ≤ E)
    {s₁ s₂ : I} {j j' : I × I} (hs₂ : Θ.θ s₂ = Θ.θ s₁) (hj1 : Θ.θ j.1 = Θ.θ s₁)
    (hj2 : Θ.θ j.2 = Θ.θ s₁) (hj'1 : Θ.θ j'.1 = Θ.θ s₁) (hj'2 : Θ.θ j'.2 = Θ.θ s₁) :
    ∑' x : FullLab (I × V) h × FullLab (I × V) h,
      prodPMF (M.rho s₁ h) (M.rho s₂ h) x
        * (((if M.deg j.1 h x.1 = 0 then 1 else 0) + (if M.deg j.2 h x.2 = 0 then 1 else 0))
          * (M.W α j'.1 h x.1 * M.W α j'.2 h x.2 + M.W α j'.2 h x.1 * M.W α j'.1 h x.2))
      ≤ 4 * (1 + ENNReal.ofReal α * Mb) * E := by
  have hE1 : ∀ u, Θ.θ u = Θ.θ s₁ →
      ∑' y, M.rho s₁ h y * ((if M.deg j.1 h y = 0 then 1 else 0) * M.W α u h y) ≤ E :=
    fun u hu => by
      rw [← wZero_singleton_eq]
      exact hE s₁ {j.1} u (Set.singleton_nonempty _)
        (fun t ht => by rw [Set.mem_singleton_iff.mp ht]; exact hj1) hu
  have hE2 : ∀ u, Θ.θ u = Θ.θ s₁ →
      ∑' y, M.rho s₂ h y * ((if M.deg j.2 h y = 0 then 1 else 0) * M.W α u h y) ≤ E :=
    fun u hu => by
      rw [← wZero_singleton_eq]
      exact hE s₂ {j.2} u (Set.singleton_nonempty _)
        (fun t ht => by rw [Set.mem_singleton_iff.mp ht, hj2, hs₂]) (by rw [hu, hs₂])
  have hU1 : ∀ u, Θ.θ u = Θ.θ s₁ →
      ∑' y, M.rho s₁ h y * M.W α u h y ≤ 1 + ENNReal.ofReal α * Mb := fun u hu =>
    (M.moment_le hα s₁ u h).trans (add_le_add le_rfl (mul_le_mul' le_rfl (hM s₁ u hu.symm)))
  have hU2 : ∀ u, Θ.θ u = Θ.θ s₁ →
      ∑' y, M.rho s₂ h y * M.W α u h y ≤ 1 + ENNReal.ofReal α * Mb := fun u hu =>
    (M.moment_le hα s₂ u h).trans
      (add_le_add le_rfl (mul_le_mul' le_rfl (hM s₂ u (hs₂.trans hu.symm))))
  have hexp : ∀ x : FullLab (I × V) h × FullLab (I × V) h,
      prodPMF (M.rho s₁ h) (M.rho s₂ h) x
        * (((if M.deg j.1 h x.1 = 0 then 1 else 0) + (if M.deg j.2 h x.2 = 0 then 1 else 0))
          * (M.W α j'.1 h x.1 * M.W α j'.2 h x.2 + M.W α j'.2 h x.1 * M.W α j'.1 h x.2))
      = prodPMF (M.rho s₁ h) (M.rho s₂ h) x
          * ((if M.deg j.1 h x.1 = 0 then 1 else 0) * (M.W α j'.1 h x.1 * M.W α j'.2 h x.2))
        + prodPMF (M.rho s₁ h) (M.rho s₂ h) x
          * ((if M.deg j.1 h x.1 = 0 then 1 else 0) * (M.W α j'.2 h x.1 * M.W α j'.1 h x.2))
        + prodPMF (M.rho s₁ h) (M.rho s₂ h) x
          * ((if M.deg j.2 h x.2 = 0 then 1 else 0) * (M.W α j'.1 h x.1 * M.W α j'.2 h x.2))
        + prodPMF (M.rho s₁ h) (M.rho s₂ h) x
          * ((if M.deg j.2 h x.2 = 0 then 1 else 0) * (M.W α j'.2 h x.1 * M.W α j'.1 h x.2)) :=
    fun x => by ring
  rw [tsum_congr hexp, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
  calc _ ≤ E * (1 + ENNReal.ofReal α * Mb) + E * (1 + ENNReal.ofReal α * Mb)
        + (1 + ENNReal.ofReal α * Mb) * E + (1 + ENNReal.ofReal α * Mb) * E := by
        refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
        · exact tsum_prod_mul_le _ _ _
            (fun y => (if M.deg j.1 h y = 0 then 1 else 0) * M.W α j'.1 h y)
            (fun y => M.W α j'.2 h y) (fun x => by ring) (hE1 j'.1 hj'1) (hU2 j'.2 hj'2)
        · exact tsum_prod_mul_le _ _ _
            (fun y => (if M.deg j.1 h y = 0 then 1 else 0) * M.W α j'.2 h y)
            (fun y => M.W α j'.1 h y) (fun x => by ring) (hE1 j'.2 hj'2) (hU2 j'.1 hj'1)
        · exact tsum_prod_mul_le _ _ _ (fun y => M.W α j'.1 h y)
            (fun y => (if M.deg j.2 h y = 0 then 1 else 0) * M.W α j'.2 h y)
            (fun x => by ring) (hU1 j'.1 hj'1) (hE2 j'.2 hj'2)
        · exact tsum_prod_mul_le _ _ _ (fun y => M.W α j'.2 h y)
            (fun y => (if M.deg j.2 h y = 0 then 1 else 0) * M.W α j'.1 h y)
            (fun x => by ring) (hU1 j'.2 hj'2) (hE2 j'.1 hj'1)
    _ = 4 * (1 + ENNReal.ofReal α * Mb) * E := by ring

/-- The zero indicator of a target component pair degree is at most the sum of the two
straight zero indicators (`sec:averaging`, product form). -/
lemma ite_pair_zero_le (j : I × I) (h : ℕ) (x : FullLab (I × V) h × FullLab (I × V) h) :
    (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0 then (1 : ℝ≥0∞)
        else 0)
      ≤ (if M.deg j.1 h x.1 = 0 then 1 else 0) + (if M.deg j.2 h x.2 = 0 then 1 else 0) := by
  by_cases hr : rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0
  · rw [if_pos hr]
    have h' := ((rE_square_eq_zero_iff (M.rho j.1 h) (M.rho j.2 h) (M.sim h) x.1 x.2).mp hr).1
    rcases mul_eq_zero.mp h' with h1 | h2
    · rw [if_pos (show M.deg j.1 h x.1 = 0 from h1)]
      exact le_add_right le_rfl
    · rw [if_pos (show M.deg j.2 h x.2 = 0 from h2)]
      exact le_add_left le_rfl
  · rw [if_neg hr]
    exact zero_le

/-- **The averaged transition at a fixed source pair** (`sec:averaging`): the restricted
potential of a charged source child pair against the target child-pair mixture is at most
the fixed-pair four-law bound plus the mixture error `(α+1) B · 4 (1 + αM) E`. -/
lemma pair_childMix_le {α : ℝ} (hα : 1 ≤ α) {g : ℕ} (Θ : Phase M g)
    (Sel : Selection M) {B : ℝ≥0∞} (hB : ∀ t, Sel.inverseSum α t ≤ B) {h : ℕ}
    {a b γ Mb Zm E : ℝ≥0∞} (hfour : M.FourLawAt Θ α h a b γ Mb Zm E)
    (hM : ∀ s u, Θ.θ s = Θ.θ u → M.P α s u h ≤ Mb)
    (hz : ∀ s t, Θ.θ s = Θ.θ t → M.z s t h ≤ Zm)
    (hE : ∀ s (D : Set I) u, D.Nonempty → (∀ t ∈ D, Θ.θ t = Θ.θ s) → Θ.θ u = Θ.θ s →
      M.wZero α s D u h ≤ E)
    {s t : I} (hst : Θ.θ s = Θ.θ t) {j₀ : I × I} (hj₀ : M.π s j₀ ≠ 0) :
    PhiDres α (prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h)) (M.childMix t h) (SquareRel (M.sim h))
      ≤ (a * Mb + b * Mb ^ 2 + (γ + 4 * ENNReal.ofReal α * Mb) * Zm
          + 4 * (1 + ENNReal.ofReal α * Mb) * E)
        + ENNReal.ofReal (α + 1) * B * (4 * (1 + ENNReal.ofReal α * Mb) * E) := by
  have hα0 : 0 ≤ α := le_trans zero_le_one hα
  have hs1 : Θ.θ j₀.1 = Θ.θ t + 1 := by rw [(Θ.child s j₀ hj₀).1, hst]
  have hs2 : Θ.θ j₀.2 = Θ.θ t + 1 := by rw [(Θ.child s j₀ hj₀).2, hst]
  -- the four-law input for every charged target transition
  have hfour' : ∀ j, M.π t j ≠ 0 →
      PhiDres α (prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h)) (prodPMF (M.rho j.1 h) (M.rho j.2 h))
          (SquareRel (M.sim h))
        ≤ a * Mb + b * Mb ^ 2 + (γ + 4 * ENNReal.ofReal α * Mb) * Zm
          + 4 * (1 + ENNReal.ofReal α * Mb) * E := fun j hj =>
    hfour j₀.1 j₀.2 j.1 j.2 (by rw [hs1, (Θ.child t j hj).1]) (by rw [hs2, (Θ.child t j hj).1])
      (by rw [(Θ.child t j hj).2, (Θ.child t j hj).1]) hM hz hE
  -- the split integrals for every charged target transition and selected component
  have hsplit : ∀ j, M.π t j ≠ 0 → ∀ j' ∈ Sel.J t,
      ∑' x : FullLab (I × V) h × FullLab (I × V) h,
        prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x
          * (((if M.deg j.1 h x.1 = 0 then 1 else 0) + (if M.deg j.2 h x.2 = 0 then 1 else 0))
            * (M.W α j'.1 h x.1 * M.W α j'.2 h x.2 + M.W α j'.2 h x.1 * M.W α j'.1 h x.2))
        ≤ 4 * (1 + ENNReal.ofReal α * Mb) * E := fun j hj j' hj' =>
    M.split_integral_le hα Θ hM hE (by rw [hs2, hs1]) (by rw [(Θ.child t j hj).1, hs1])
      (by rw [(Θ.child t j hj).2, hs1])
      (by rw [(Θ.child t j' (Sel.charged t j' hj')).1, hs1])
      (by rw [(Θ.child t j' (Sel.charged t j' hj')).2, hs1])
  -- the pointwise error bound on the charged source pairs
  have hpt : ∀ x : FullLab (I × V) h × FullLab (I × V) h,
      prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x
        * (ENNReal.ofReal (α + 1)
          * (∑' j, M.π t j
              * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0
                then 1 else 0))
          * WresD α (M.childMix t h) (SquareRel (M.sim h)) x)
      ≤ prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x
        * (ENNReal.ofReal (α + 1) * ∑' j, M.π t j * ∑ j' ∈ Sel.J t, (M.π t j') ^ (-α)
          * (((if M.deg j.1 h x.1 = 0 then 1 else 0) + (if M.deg j.2 h x.2 = 0 then 1 else 0))
            * (M.W α j'.1 h x.1 * M.W α j'.2 h x.2 + M.W α j'.2 h x.1 * M.W α j'.1 h x.2))) := by
    intro x
    by_cases hx : prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x = 0
    · rw [hx, zero_mul, zero_mul]
    have hx1 : M.rho j₀.1 h x.1 ≠ 0 := fun h0 => hx (by rw [prodPMF_apply, h0, zero_mul])
    have hx2 : M.rho j₀.2 h x.2 ≠ 0 := fun h0 => hx (by rw [prodPMF_apply, h0, mul_zero])
    refine mul_le_mul' le_rfl ?_
    rw [mul_assoc]
    refine mul_le_mul' le_rfl ?_
    have hW : WresD α (M.childMix t h) (SquareRel (M.sim h)) x
        ≤ ∑ j' ∈ Sel.J t, (M.π t j') ^ (-α)
          * (M.W α j'.1 h x.1 * M.W α j'.2 h x.2 + M.W α j'.2 h x.1 * M.W α j'.1 h x.2) :=
      (M.WresD_childMix_le hα0 Sel t h x (M.statesIn_of_rho_ne_zero _ _ _ hx1)
        (M.statesIn_of_rho_ne_zero _ _ _ hx2)).trans
        (Finset.sum_le_sum fun j' _ => mul_le_mul' le_rfl (M.WresD_pair_le hα0 j'.1 j'.2 h x))
    calc (∑' j, M.π t j
            * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0
              then 1 else 0))
          * WresD α (M.childMix t h) (SquareRel (M.sim h)) x
        ≤ (∑' j, M.π t j
            * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0
              then 1 else 0))
          * ∑ j' ∈ Sel.J t, (M.π t j') ^ (-α)
            * (M.W α j'.1 h x.1 * M.W α j'.2 h x.2 + M.W α j'.2 h x.1 * M.W α j'.1 h x.2) :=
          mul_le_mul' le_rfl hW
      _ = ∑' j, M.π t j * ∑ j' ∈ Sel.J t, (M.π t j') ^ (-α)
            * ((if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0
                then 1 else 0)
              * (M.W α j'.1 h x.1 * M.W α j'.2 h x.2 + M.W α j'.2 h x.1 * M.W α j'.1 h x.2)) := by
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr fun j => ?_
          rw [mul_assoc, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun j' _ => ?_
          ring
      _ ≤ ∑' j, M.π t j * ∑ j' ∈ Sel.J t, (M.π t j') ^ (-α)
            * (((if M.deg j.1 h x.1 = 0 then 1 else 0) + (if M.deg j.2 h x.2 = 0 then 1 else 0))
              * (M.W α j'.1 h x.1 * M.W α j'.2 h x.2 + M.W α j'.2 h x.1 * M.W α j'.1 h x.2)) :=
          ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl (Finset.sum_le_sum fun j' _ =>
            mul_le_mul' le_rfl (mul_le_mul' (M.ite_pair_zero_le j h x) le_rfl))
  -- integrate the pointwise mixture bound
  rw [PhiDres]
  calc ∑' x, prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x
        * (if rE (M.childMix t h) (SquareRel (M.sim h)) x = 0 then 0
          else phiE α (q (M.childMix t h) (SquareRel (M.sim h)) x))
      ≤ ∑' x, prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x
        * ((∑' j, M.π t j
            * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0 then 0
              else phiE α (q (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x)))
          + ENNReal.ofReal (α + 1)
            * (∑' j, M.π t j
                * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0
                  then 1 else 0))
            * WresD α (M.childMix t h) (SquareRel (M.sim h)) x) :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (M.pointwise_childMix_le hα t h x)
    _ = (∑' x, prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x * ∑' j, M.π t j
            * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0 then 0
              else phiE α (q (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x)))
        + ∑' x, prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x
          * (ENNReal.ofReal (α + 1)
            * (∑' j, M.π t j
                * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0
                  then 1 else 0))
            * WresD α (M.childMix t h) (SquareRel (M.sim h)) x) := by
        rw [← ENNReal.tsum_add]
        exact tsum_congr fun x => mul_add _ _ _
    _ ≤ (a * Mb + b * Mb ^ 2 + (γ + 4 * ENNReal.ofReal α * Mb) * Zm
          + 4 * (1 + ENNReal.ofReal α * Mb) * E)
        + ENNReal.ofReal (α + 1) * B * (4 * (1 + ENNReal.ofReal α * Mb) * E) := by
        refine add_le_add (M.mixture_main_le t h _ hfour') ?_
        calc ∑' x, prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x
              * (ENNReal.ofReal (α + 1)
                * (∑' j, M.π t j
                    * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0
                      then 1 else 0))
                * WresD α (M.childMix t h) (SquareRel (M.sim h)) x)
            ≤ ∑' x, prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x
              * (ENNReal.ofReal (α + 1) * ∑' j, M.π t j * ∑ j' ∈ Sel.J t, (M.π t j') ^ (-α)
                * (((if M.deg j.1 h x.1 = 0 then 1 else 0)
                    + (if M.deg j.2 h x.2 = 0 then 1 else 0))
                  * (M.W α j'.1 h x.1 * M.W α j'.2 h x.2
                    + M.W α j'.2 h x.1 * M.W α j'.1 h x.2))) := ENNReal.tsum_le_tsum hpt
          _ = ENNReal.ofReal (α + 1) * ∑' x, prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x
              * ∑' j, M.π t j * ∑ j' ∈ Sel.J t, (M.π t j') ^ (-α)
                * (((if M.deg j.1 h x.1 = 0 then 1 else 0)
                    + (if M.deg j.2 h x.2 = 0 then 1 else 0))
                  * (M.W α j'.1 h x.1 * M.W α j'.2 h x.2
                    + M.W α j'.2 h x.1 * M.W α j'.1 h x.2)) := by
              rw [← ENNReal.tsum_mul_left]
              exact tsum_congr fun x => by ring
          _ = ENNReal.ofReal (α + 1) * ∑' j, M.π t j * ∑ j' ∈ Sel.J t, (M.π t j') ^ (-α)
              * ∑' x, prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x
                * (((if M.deg j.1 h x.1 = 0 then 1 else 0)
                    + (if M.deg j.2 h x.2 = 0 then 1 else 0))
                  * (M.W α j'.1 h x.1 * M.W α j'.2 h x.2
                    + M.W α j'.2 h x.1 * M.W α j'.1 h x.2)) := by
              rw [tsum_mul_tsum_comm]
              congr 1
              refine tsum_congr fun j => ?_
              rw [tsum_mul_finsetSum_comm]
          _ ≤ ENNReal.ofReal (α + 1) * ∑' j, M.π t j * ∑ j' ∈ Sel.J t, (M.π t j') ^ (-α)
              * (4 * (1 + ENNReal.ofReal α * Mb) * E) := by
              refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun j => ?_)
              by_cases hj : M.π t j = 0
              · rw [hj, zero_mul, zero_mul]
              · exact mul_le_mul' le_rfl (Finset.sum_le_sum fun j' hj' =>
                  mul_le_mul' le_rfl (hsplit j hj j' hj'))
          _ = ENNReal.ofReal (α + 1) * (∑' j, M.π t j) * Sel.inverseSum α t
              * (4 * (1 + ENNReal.ofReal α * Mb) * E) := by
              rw [← Finset.sum_mul, ENNReal.tsum_mul_right, Selection.inverseSum]
              ring
          _ ≤ ENNReal.ofReal (α + 1) * 1 * B * (4 * (1 + ENNReal.ofReal α * Mb) * E) :=
              mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl (M.π t).tsum_coe.le) (hB t)) le_rfl
          _ = ENNReal.ofReal (α + 1) * B * (4 * (1 + ENNReal.ofReal α * Mb) * E) := by
              rw [mul_one]

/-- **The child-pair bound, finite alternative** (`sec:averaging`): the restricted potential
of the source child-pair mixture of `s` against the target child-pair mixture of `t` is
at most `Q(M) = a M + b M² + (γ + 4αM) Z + C (1 + αM) E` with `C = 4 + 8(α+1)B`. -/
theorem childPair_le_Qfun [Fintype I] (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0)
    {α : ℝ} (hα : 1 ≤ α) {g : ℕ} (Θ : Phase M g) (Sel : Selection M) {B : ℝ≥0∞}
    (hB : ∀ t, Sel.inverseSum α t ≤ B) {h : ℕ} {a b γ Mb Zm E : ℝ≥0∞}
    (hfour : M.FourLawAt Θ α h a b γ Mb Zm E)
    (hM : ∀ s u, Θ.θ s = Θ.θ u → M.P α s u h ≤ Mb)
    (hz : ∀ s t, Θ.θ s = Θ.θ t → M.z s t h ≤ Zm)
    (hE : ∀ s (D : Set I) u, D.Nonempty → (∀ t ∈ D, Θ.θ t = Θ.θ s) → Θ.θ u = Θ.θ s →
      M.wZero α s D u h ≤ E)
    (s t : I) (hst : Θ.θ s = Θ.θ t) :
    PhiDres α (M.childMix s h) (M.childMix t h) (SquareRel (M.sim h))
      ≤ Qfun α a b γ (Cmix α B) Zm E Mb := by
  -- the compatibility and root-mass hypotheses belong to the finite-alternative interface
  -- and enter only through the inputs `hfour`, `hM`, `hz`, `hE`; the averaging step itself
  -- does not use them
  have _ := hc
  have _ := hb0
  rw [show M.childMix s h = (M.π s).bind (fun j => prodPMF (M.rho j.1 h) (M.rho j.2 h))
    from rfl, PhiDres_bind_left]
  calc ∑' j, M.π s j * PhiDres α (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (M.childMix t h)
          (SquareRel (M.sim h))
      ≤ ∑' j, M.π s j * Qfun α a b γ (Cmix α B) Zm E Mb := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        by_cases hj : M.π s j = 0
        · rw [hj, zero_mul, zero_mul]
        · exact mul_le_mul' le_rfl
            ((M.pair_childMix_le hα Θ Sel hB hfour hM hz hE hst hj).trans
              (bound_le_Qfun α a b γ B Zm E Mb))
    _ = Qfun α a b γ (Cmix α B) Zm E Mb := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The abstract four-law input when `δ = 0`: every four-law comparison of process laws at
height `h` with the potentials at most `Mb` obeys the contraction with constants `a, b`. -/
def FourLawAtZero (α : ℝ) (h : ℕ) (a b Mb : ℝ≥0∞) : Prop :=
  ∀ s₁ s₂ t₁ t₂ : I, (∀ s u, M.P α s u h ≤ Mb) →
    PhiDres α (prodPMF (M.rho s₁ h) (M.rho s₂ h)) (prodPMF (M.rho t₁ h) (M.rho t₂ h))
        (SquareRel (M.sim h))
      ≤ a * Mb + b * Mb ^ 2

/-- **The child-pair bound, zero-compatible alternative** (`sec:averaging`): when `δ = 0`,
the restricted potential of the source child-pair mixture against the target child-pair
mixture is at most `a M + b M²`, by countable Jensen without mixture error. -/
theorem childPair_le_of_delta_zero (hc : M.IsCompat) (hδ : M.delta = 0) {α : ℝ} (hα : 1 ≤ α)
    {h : ℕ} {a b Mb : ℝ≥0∞} (hfour : M.FourLawAtZero α h a b Mb)
    (hM : ∀ s u, M.P α s u h ≤ Mb) (s t : I) :
    PhiDres α (M.childMix s h) (M.childMix t h) (SquareRel (M.sim h)) ≤ a * Mb + b * Mb ^ 2 := by
  rw [show M.childMix s h = (M.π s).bind (fun j => prodPMF (M.rho j.1 h) (M.rho j.2 h))
    from rfl, PhiDres_bind_left]
  calc ∑' j, M.π s j * PhiDres α (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (M.childMix t h)
          (SquareRel (M.sim h))
      ≤ ∑' j, M.π s j * (a * Mb + b * Mb ^ 2) := by
        refine ENNReal.tsum_le_tsum fun j₀ => ?_
        by_cases hj : M.π s j₀ = 0
        · rw [hj, zero_mul, zero_mul]
        refine mul_le_mul' le_rfl ?_
        have hfour' : ∀ j, M.π t j ≠ 0 →
            PhiDres α (prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h))
                (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h))
              ≤ a * Mb + b * Mb ^ 2 :=
          fun j _ => hfour j₀.1 j₀.2 j.1 j.2 hM
        -- every target component has positive degree on a charged source pair
        have hpt : ∀ x : FullLab (I × V) h × FullLab (I × V) h,
            prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x
              * (if rE (M.childMix t h) (SquareRel (M.sim h)) x = 0 then 0
                else phiE α (q (M.childMix t h) (SquareRel (M.sim h)) x))
            ≤ prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x * ∑' j, M.π t j
              * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0
                then 0
                else phiE α (q (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x)) := by
          intro x
          by_cases hx : prodPMF (M.rho j₀.1 h) (M.rho j₀.2 h) x = 0
          · rw [hx, zero_mul, zero_mul]
          have hx1 : M.rho j₀.1 h x.1 ≠ 0 := fun h0 => hx (by rw [prodPMF_apply, h0, zero_mul])
          have hx2 : M.rho j₀.2 h x.2 ≠ 0 := fun h0 => hx (by rw [prodPMF_apply, h0, mul_zero])
          have hzero : (∑' j, M.π t j
              * (if rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x = 0
                then 1 else 0)) = 0 := by
            refine ENNReal.tsum_eq_zero.mpr fun j => ?_
            have hr : rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) x ≠ 0 := by
              intro hr
              have h' := ((rE_square_eq_zero_iff (M.rho j.1 h) (M.rho j.2 h) (M.sim h)
                x.1 x.2).mp hr).1
              rcases mul_eq_zero.mp h' with h1 | h2
              · exact M.deg_ne_zero_of_delta_zero hc hδ h j₀.1 j.1 x.1 hx1 h1
              · exact M.deg_ne_zero_of_delta_zero hc hδ h j₀.2 j.2 x.2 hx2 h2
            rw [if_neg hr, mul_zero]
          refine mul_le_mul' le_rfl ?_
          have key := M.pointwise_childMix_le hα t h x
          rw [hzero, mul_zero, zero_mul, add_zero] at key
          exact key
        exact (ENNReal.tsum_le_tsum hpt).trans (M.mixture_main_le t h _ hfour')
    _ = a * Mb + b * Mb ^ 2 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Model

end GraphMarkovMatching.Stopped
