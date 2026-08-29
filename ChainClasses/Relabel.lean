/-
`sec:general-relabel` of `matching_classes_general.tex`: the transport
relabelling, over the mass-sequence and coupling interfaces of the shape half.

The comparability composition of `thm:relabel` is `markedQI_relabel` in
`Hairy.lean` and the cascade producing the couplings is `ShapeCoupling.lean`;
certified here are the remaining scalar steps.

* `thm:mass-uniform`: `mixture_moment_le`, a finite mixture of laws with a
  common exponential-moment bound keeps the bound, feeding `chernoff_tail`;
  `mixture_point_lower`, the mixture dominates each conditional law, which is
  how the point-mass bound of the mixture serves for every `μ_k`; and
  `conv_moment`, the moment of an independent sum is the product of the
  moments, which is how the exit bouquet multiplies the moment of
  `thm:shape-mass` by a constant.
* `thm:relabel`\ `it:relabel-law` as `relabel_law`: the label reads off the
  second component of a coupling whose second marginal is the mixture `μ`, so
  the label law is the pushforward `μ_D`, whatever the first marginal.  The
  hypotheses mention the coupling only through that marginal, which is the
  `k`-independence of the label law.
* `thm:product-form` as `product_of_constant_conditional`: a conditional law
  that does not depend on the condition makes the joint law the product of
  its marginals.
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import ChainClasses.ShapeMass

namespace ChainClasses

open Real

/-! ### `thm:mass-uniform`: the mixture and the bouquet -/

/-- **`thm:mass-uniform`, the mixture tail**: a finite mixture of laws, each
with exponential moment at most `M`, has exponential moment at most `M`, so
`chernoff_tail` applies to the mixture with the same constants. -/
theorem mixture_moment_le {ι : Type*} {K : Finset ι} {w : ι → ℝ} {f : ι → ℕ → ℝ}
    {t M : ℝ} (hw : ∀ i ∈ K, 0 ≤ w i) (hw1 : ∑ i ∈ K, w i ≤ 1) (hM0 : 0 ≤ M)
    (hs : ∀ i ∈ K, Summable fun n : ℕ => Real.exp (t * (n : ℝ)) * f i n)
    (hM : ∀ i ∈ K, ∑' n : ℕ, Real.exp (t * (n : ℝ)) * f i n ≤ M) :
    Summable (fun n : ℕ => Real.exp (t * (n : ℝ)) * ∑ i ∈ K, w i * f i n) ∧
      ∑' n : ℕ, Real.exp (t * (n : ℝ)) * ∑ i ∈ K, w i * f i n ≤ M := by
  have hre : ∀ n : ℕ, Real.exp (t * (n : ℝ)) * ∑ i ∈ K, w i * f i n
      = ∑ i ∈ K, w i * (Real.exp (t * (n : ℝ)) * f i n) := by
    intro n
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsummand : ∀ i ∈ K, Summable fun n : ℕ => w i * (Real.exp (t * (n : ℝ)) * f i n) :=
    fun i hi => (hs i hi).mul_left (w i)
  have hsum : Summable fun n : ℕ => ∑ i ∈ K, w i * (Real.exp (t * (n : ℝ)) * f i n) :=
    summable_sum hsummand
  constructor
  · rw [show (fun n : ℕ => Real.exp (t * (n : ℝ)) * ∑ i ∈ K, w i * f i n)
        = fun n : ℕ => ∑ i ∈ K, w i * (Real.exp (t * (n : ℝ)) * f i n) from funext hre]
    exact hsum
  · calc ∑' n : ℕ, Real.exp (t * (n : ℝ)) * ∑ i ∈ K, w i * f i n
        = ∑' n : ℕ, ∑ i ∈ K, w i * (Real.exp (t * (n : ℝ)) * f i n) := tsum_congr hre
      _ = ∑ i ∈ K, ∑' n : ℕ, w i * (Real.exp (t * (n : ℝ)) * f i n) :=
          Summable.tsum_finsetSum hsummand
      _ = ∑ i ∈ K, w i * ∑' n : ℕ, Real.exp (t * (n : ℝ)) * f i n :=
          Finset.sum_congr rfl fun i _ => tsum_mul_left
      _ ≤ ∑ i ∈ K, w i * M :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hM i hi) (hw i hi)
      _ = (∑ i ∈ K, w i) * M := (Finset.sum_mul ..).symm
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right hw1 hM0
      _ = M := one_mul M

/-- **`thm:mass-uniform`, the point masses**: the mixture dominates each
conditional law, `μ(σ) ≥ ν̃_k μ_k(σ)`, so the point-mass bound of any one
component serves for the mixture. -/
lemma mixture_point_lower {ι : Type*} {K : Finset ι} {w a : ι → ℝ}
    (hnn : ∀ i ∈ K, 0 ≤ w i * a i) {k : ι} (hk : k ∈ K) :
    w k * a k ≤ ∑ i ∈ K, w i * a i :=
  Finset.single_le_sum hnn hk

/-- A power of `p` as an exponential at a general rate:
`p^{mn} = e^{-(m log p⁻¹)n}`. -/
lemma pow_mul_eq_exp {p : ℝ} (hp0 : 0 < p) (m n : ℕ) :
    p ^ (m * n) = Real.exp (-((m : ℝ) * Real.log p⁻¹) * (n : ℝ)) := by
  have h : -((m : ℝ) * Real.log p⁻¹) * (n : ℝ) = ((m * n : ℕ) : ℝ) * Real.log p := by
    rw [Real.log_inv]; push_cast; ring
  rw [h, mul_comm, Real.exp_nat_mul, Real.exp_log hp0]

/-- **`thm:mass-uniform`, the point-mass form**: a mass that is a product of
at most `mn` factors, each at least `p`, is at least `e^{-Cn}` with
`C = m log p⁻¹`; the count of the proof is `m = 2 + b`. -/
theorem mass_point_general {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {m n : ℕ} {L : List ℝ}
    (hlen : L.length ≤ m * n) (hfac : ∀ x ∈ L, p ≤ x) :
    Real.exp (-((m : ℝ) * Real.log p⁻¹) * (n : ℝ)) ≤ L.prod := by
  rw [← pow_mul_eq_exp hp0]
  exact prod_ge_pow hp0 hp1 hlen hfac

/-- **`thm:mass-uniform`, the bouquet**: the exponential moment of an
independent sum is the product of the moments, so each further total progeny
in the exit bouquet multiplies the moment of `thm:shape-mass` by a
constant. -/
theorem conv_moment {f g : ℕ → ℝ} {t : ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (hsf : Summable fun n : ℕ => Real.exp (t * (n : ℝ)) * f n)
    (hsg : Summable fun n : ℕ => Real.exp (t * (n : ℝ)) * g n) :
    HasSum (fun n : ℕ => Real.exp (t * (n : ℝ)) *
        ∑ k ∈ Finset.range (n + 1), f k * g (n - k))
      ((∑' n : ℕ, Real.exp (t * (n : ℝ)) * f n)
        * ∑' n : ℕ, Real.exp (t * (n : ℝ)) * g n) := by
  set F : ℕ → ℝ := fun n => Real.exp (t * (n : ℝ)) * f n with hF
  set G : ℕ → ℝ := fun n => Real.exp (t * (n : ℝ)) * g n with hG
  have key : ∀ n : ℕ, Real.exp (t * (n : ℝ)) * ∑ k ∈ Finset.range (n + 1), f k * g (n - k)
      = ∑ k ∈ Finset.range (n + 1), F k * G (n - k) := by
    intro n
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
      push_cast [hkn]
      ring
    rw [hF, hG]
    simp only
    rw [show t * (n : ℝ) = t * (k : ℝ) + t * ((n - k : ℕ) : ℝ) by rw [hsub]; ring,
      Real.exp_add]
    ring
  have hFn : (fun n : ℕ => ‖F n‖) = F :=
    funext fun n => Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hf n))
  have hGn : (fun n : ℕ => ‖G n‖) = G :=
    funext fun n => Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg n))
  have hFnorm : Summable fun n : ℕ => ‖F n‖ := by rw [hFn]; exact hsf
  have hGnorm : Summable fun n : ℕ => ‖G n‖ := by rw [hGn]; exact hsg
  have h := hasSum_sum_range_mul_of_summable_norm hFnorm hGnorm
  rw [show (fun n : ℕ => Real.exp (t * (n : ℝ)) *
      ∑ k ∈ Finset.range (n + 1), f k * g (n - k))
      = fun n : ℕ => ∑ k ∈ Finset.range (n + 1), F k * G (n - k) from funext key]
  exact h

/-! ### `thm:relabel`\ `it:relabel-law`: the label law -/

/-- **`it:relabel-law`**: the label is `rep_D` of the second component of a
coupling whose second marginal is `μ`, so its law is the pushforward `μ_D`.
The coupling enters only through that marginal: the conclusion does not see
the first marginal `μ_k`, which is the `k`-independence of the label law. -/
theorem relabel_law {S R : Type*} {cpl : S → S → ℝ} {μ : S → ℝ} (rep : S → R)
    (hnn : ∀ σ τ, 0 ≤ cpl σ τ)
    (hmarg : ∀ τ, HasSum (fun σ => cpl σ τ) (μ τ))
    (hμ : Summable μ) (x : R) :
    HasSum (fun p : {p : S × S // rep p.2 = x} => cpl p.1.1 p.1.2)
      (∑' τ : {τ : S // rep τ = x}, μ τ.1) := by
  classical
  have hrowSummable : ∀ τ : {τ : S // rep τ = x}, Summable fun σ : S => cpl σ τ.1 :=
    fun τ => (hmarg τ.1).summable
  have hμT : Summable fun τ : {τ : S // rep τ = x} => μ τ.1 :=
    hμ.comp_injective Subtype.val_injective
  have hrowsum : Summable fun τ : {τ : S // rep τ = x} => ∑' σ : S, cpl σ τ.1 :=
    hμT.congr fun τ => ((hmarg τ.1).tsum_eq).symm
  have hsig : Summable fun q : (Σ _ : {τ : S // rep τ = x}, S) => cpl q.2 q.1.1 :=
    (summable_sigma_of_nonneg
      (f := fun q : (Σ _ : {τ : S // rep τ = x}, S) => cpl q.2 q.1.1)
      (fun q => hnn q.2 q.1.1)).mpr ⟨hrowSummable, hrowsum⟩
  have hhs : HasSum (fun q : (Σ _ : {τ : S // rep τ = x}, S) => cpl q.2 q.1.1)
      (∑' τ : {τ : S // rep τ = x}, μ τ.1) :=
    HasSum.sigma_of_hasSum hμT.hasSum (fun τ => hmarg τ.1) hsig
  let e : (Σ _ : {τ : S // rep τ = x}, S) ≃ {p : S × S // rep p.2 = x} :=
    { toFun := fun q => ⟨(q.2, q.1.1), q.1.2⟩
      invFun := fun p => ⟨⟨p.1.2, p.2⟩, p.1.1⟩
      left_inv := fun q => rfl
      right_inv := fun p => rfl }
  exact (Equiv.hasSum_iff
    (f := fun p : {p : S × S // rep p.2 = x} => cpl p.1.1 p.1.2)
    (a := ∑' τ : {τ : S // rep τ = x}, μ τ.1) e).mp hhs

/-! ### `thm:product-form`: the independence step -/

/-- **`thm:product-form`**: a conditional law that does not depend on the
condition makes the joint law the product of its marginals: the labels are
independent of the arity field, with the one law `μ_D`, and the pair law is
`Q = μ_D ⊗ ν̃`. -/
theorem product_of_constant_conditional {K L : Type*} {w : K → ℝ} {ρ : L → ℝ}
    (hw : HasSum w 1) (hρ : HasSum ρ 1) (hwn : ∀ k, 0 ≤ w k) (hρn : ∀ x, 0 ≤ ρ x) :
    HasSum (fun p : K × L => w p.1 * ρ p.2) 1 ∧
      (∀ x, HasSum (fun k => w k * ρ x) (ρ x)) ∧
      ∀ k, HasSum (fun x => w k * ρ x) (w k) := by
  refine ⟨?_, fun x => by simpa using hw.mul_right (ρ x),
    fun k => by simpa using hρ.mul_left (w k)⟩
  have hsummable : Summable fun p : K × L => w p.1 * ρ p.2 := by
    refine (summable_prod_of_nonneg fun p => mul_nonneg (hwn p.1) (hρn p.2)).mpr
      ⟨fun k => hρ.summable.mul_left (w k), ?_⟩
    rw [show (fun k => ∑' x : L, w k * ρ x) = fun k => w k from
      funext fun k => by rw [tsum_mul_left, hρ.tsum_eq, mul_one]]
    exact hw.summable
  have h := HasSum.mul hw hρ hsummable
  simpa using h

end ChainClasses