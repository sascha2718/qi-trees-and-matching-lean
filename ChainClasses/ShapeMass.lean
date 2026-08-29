/-
`sec:shape-harris` of `matching_classes_simple.tex`: the two mass bounds of
`thm:shape-mass`, which carry the potential computation of `sec:shape-eta` and
the capacity bound of `sec:shape-coupling`.

Both clauses are scalar statements about the shape law, and both are certified
here over the data the proof actually uses, the Galton-Watson construction of
`thm:shape-iid` entering only through that data.

* Clause (ii), no positive-probability shape is much lighter than
  exponentially in its size: `μ(σ)` is a product of at most `2|σ|` factors,
  each one of the seven constants of the proof, so `prod_ge_pow` gives
  `μ(σ) ≥ p^{2|σ|}` and `shape_mass_point` rewrites this as `e^{-C|σ|}` with
  `C = 2 log p⁻¹`, `p` the least of the seven.
* Clause (i), the exponential tail: `chernoff_tail` is Markov's inequality for
  the exponential moment, and `shape_mass_tail` absorbs the moment into `n₀`,
  the paper's `c = t/2`.  The moment itself is finite by `geom_mgf_summable`:
  the neck length is geometric, so the compound sum `m + Z_1 + … + Z_{m-1}` has
  an exponential moment as soon as `e^t 𝔼e^{tZ} < 1/θ̃₁`.
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

namespace ChainClasses

open Real

/-! ### Clause (ii): the point-mass bound -/

/-- A product of factors bounded below by `p > 0` is at least `p` to the
length. -/
lemma pow_length_le_prod {p : ℝ} (hp0 : 0 < p) {L : List ℝ} (hfac : ∀ x ∈ L, p ≤ x) :
    p ^ L.length ≤ L.prod := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have hat : p ≤ a := hfac a (List.mem_cons_self ..)
      have hrest : p ^ t.length ≤ t.prod := ih fun x hx => hfac x (List.mem_cons_of_mem a hx)
      have hmul : p * p ^ t.length ≤ a * t.prod :=
        mul_le_mul hat hrest (pow_nonneg hp0.le _) (hp0.le.trans hat)
      simpa [pow_succ, mul_comm] using hmul

/-- A product of at most `N` factors, each at least `p ∈ (0,1]`, is at least
`p^N`. -/
lemma prod_ge_pow {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {N : ℕ} {L : List ℝ}
    (hlen : L.length ≤ N) (hfac : ∀ x ∈ L, p ≤ x) : p ^ N ≤ L.prod :=
  (pow_le_pow_of_le_one hp0.le hp1 hlen).trans (pow_length_le_prod hp0 hfac)

/-- A power of `p` as an exponential: `p^{2n} = e^{-(2 log p⁻¹)n}`. -/
lemma pow_two_mul_eq_exp {p : ℝ} (hp0 : 0 < p) (n : ℕ) :
    p ^ (2 * n) = Real.exp (-(2 * Real.log p⁻¹) * (n : ℝ)) := by
  have h : -(2 * Real.log p⁻¹) * (n : ℝ) = ((2 * n : ℕ) : ℝ) * Real.log p := by
    rw [Real.log_inv]; push_cast; ring
  rw [h, mul_comm, Real.exp_nat_mul, Real.exp_log hp0]

/-- **`thm:shape-mass`(ii)**: a mass that is a product of at most `2n` factors,
each at least `p`, is at least `e^{-Cn}` with `C = 2 log p⁻¹`. -/
theorem shape_mass_point {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {n : ℕ} {L : List ℝ}
    (hlen : L.length ≤ 2 * n) (hfac : ∀ x ∈ L, p ≤ x) :
    Real.exp (-(2 * Real.log p⁻¹) * (n : ℝ)) ≤ L.prod := by
  rw [← pow_two_mul_eq_exp hp0]
  exact prod_ge_pow hp0 hp1 hlen hfac

/-! ### Clause (i): the exponential tail -/

variable {t M : ℝ} {f : ℕ → ℝ}

/-- The tail of a law with a finite exponential moment is summable. -/
lemma summable_tail (ht : 0 < t) (hf : ∀ n, 0 ≤ f n)
    (hsum : Summable fun n : ℕ => Real.exp (t * (n : ℝ)) * f n) : Summable f := by
  refine Summable.of_nonneg_of_le hf (fun n => ?_) hsum
  have h1 : (1 : ℝ) ≤ Real.exp (t * (n : ℝ)) :=
    Real.one_le_exp (by positivity)
  nlinarith [hf n]

/-- **Markov's inequality for the exponential moment**: a moment bound
`∑ e^{tn} f(n) ≤ M` bounds the tail above `N` by `M e^{-tN}`. -/
theorem chernoff_tail (ht : 0 < t) (hf : ∀ n, 0 ≤ f n)
    (hsum : Summable fun n : ℕ => Real.exp (t * (n : ℝ)) * f n)
    (hM : ∑' n : ℕ, Real.exp (t * (n : ℝ)) * f n ≤ M) (N : ℕ) :
    ∑' k : ℕ, f (k + N) ≤ M * Real.exp (-(t * (N : ℝ))) := by
  have hfs : Summable f := summable_tail ht hf hsum
  have hshift : Summable fun k : ℕ => Real.exp (t * ((k + N : ℕ) : ℝ)) * f (k + N) :=
    (summable_nat_add_iff N).mpr hsum
  have htail : ∑' k : ℕ, Real.exp (t * ((k + N : ℕ) : ℝ)) * f (k + N)
      ≤ ∑' n : ℕ, Real.exp (t * (n : ℝ)) * f n := by
    have hsplit := hsum.sum_add_tsum_nat_add N
    have hpos : 0 ≤ ∑ i ∈ Finset.range N, Real.exp (t * (i : ℝ)) * f i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Real.exp_pos _).le (hf i)
    linarith [hsplit]
  have hterm : ∀ k : ℕ,
      f (k + N) ≤ Real.exp (-(t * (N : ℝ))) * (Real.exp (t * ((k + N : ℕ) : ℝ)) * f (k + N)) := by
    intro k
    have hcast : Real.exp (-(t * (N : ℝ))) * Real.exp (t * ((k + N : ℕ) : ℝ))
        = Real.exp (t * (k : ℝ)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    have h1 : (1 : ℝ) ≤ Real.exp (t * (k : ℝ)) := Real.one_le_exp (by positivity)
    calc f (k + N) = 1 * f (k + N) := (one_mul _).symm
      _ ≤ Real.exp (t * (k : ℝ)) * f (k + N) := by nlinarith [hf (k + N)]
      _ = Real.exp (-(t * (N : ℝ))) * (Real.exp (t * ((k + N : ℕ) : ℝ)) * f (k + N)) := by
          rw [← hcast]; ring
  calc ∑' k : ℕ, f (k + N)
      ≤ ∑' k : ℕ, Real.exp (-(t * (N : ℝ))) * (Real.exp (t * ((k + N : ℕ) : ℝ)) * f (k + N)) :=
        Summable.tsum_le_tsum hterm ((summable_nat_add_iff N).mpr hfs) (hshift.mul_left _)
    _ = Real.exp (-(t * (N : ℝ))) * ∑' k : ℕ, Real.exp (t * ((k + N : ℕ) : ℝ)) * f (k + N) :=
        tsum_mul_left
    _ ≤ Real.exp (-(t * (N : ℝ))) * M := by
        have hpos := Real.exp_pos (-(t * (N : ℝ)))
        nlinarith [htail, hM]
    _ = M * Real.exp (-(t * (N : ℝ))) := mul_comm _ _

/-- **`thm:shape-mass`(i)**: past `n₀ := 2 log M / t` the moment constant is
absorbed and the tail is `e^{-cn}` with `c = t/2`. -/
theorem shape_mass_tail (ht : 0 < t) (hM1 : 1 ≤ M) (hf : ∀ n, 0 ≤ f n)
    (hsum : Summable fun n : ℕ => Real.exp (t * (n : ℝ)) * f n)
    (hM : ∑' n : ℕ, Real.exp (t * (n : ℝ)) * f n ≤ M) {N : ℕ}
    (hN : 2 * Real.log M ≤ t * (N : ℝ)) :
    ∑' k : ℕ, f (k + N) ≤ Real.exp (-(t / 2) * (N : ℝ)) := by
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  have hMle : M ≤ Real.exp (t * (N : ℝ) / 2) := by
    calc M = Real.exp (Real.log M) := (Real.exp_log hMpos).symm
      _ ≤ Real.exp (t * (N : ℝ) / 2) := Real.exp_le_exp.mpr (by linarith)
  refine (chernoff_tail ht hf hsum hM N).trans ?_
  have hkey : Real.exp (t * (N : ℝ) / 2) * Real.exp (-(t * (N : ℝ)))
      = Real.exp (-(t / 2) * (N : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc M * Real.exp (-(t * (N : ℝ)))
      ≤ Real.exp (t * (N : ℝ) / 2) * Real.exp (-(t * (N : ℝ))) := by
        have := Real.exp_pos (-(t * (N : ℝ))); nlinarith
    _ = Real.exp (-(t / 2) * (N : ℝ)) := hkey

/-- The exponential moment of the shape size is finite: the neck length is
geometric with ratio `θ₁`, so the compound sum has moment
`∑_m θ₁^{m-1} θ₂ r^m < ∞` for every `r` with `θ₁ r < 1`. -/
lemma geom_mgf_summable {θ₁ θ₂ r : ℝ} (h1 : 0 ≤ θ₁) (hr : 0 ≤ r) (h : θ₁ * r < 1) :
    Summable fun m : ℕ => θ₁ ^ m * θ₂ * r ^ (m + 1) := by
  have hcongr : ∀ m : ℕ, θ₁ ^ m * θ₂ * r ^ (m + 1) = (θ₂ * r) * (θ₁ * r) ^ m := by
    intro m; rw [mul_pow]; ring
  simp only [hcongr]
  exact (summable_geometric_of_lt_one (by positivity) h).mul_left _

end ChainClasses
