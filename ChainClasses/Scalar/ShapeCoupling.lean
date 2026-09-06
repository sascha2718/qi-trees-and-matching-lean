import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
`sec:shape-coupling` of `gw_classes_simple.tex`: the capacity bound
`eq:capacity` and the cascade that turns it into the coupling of
`thm:shape-coupling`.

The shrinking map `shrink` carries the tail of each shape law into the support
of the other one, halving sizes.  Writing `M σ k` for the mass, under the law
of the appropriate side, of the `k`-fold iterated fibre `shrink^{-k}(σ)`, the
capacity bound is `M σ 1 ≤ M σ 0 / 2`, and the fibre decomposition
`M σ (k+1) = ∑_{ρ ∈ shrink^{-1}(σ)} M ρ k` propagates it to all levels
(`IsCascade.halving`).  The coupling gives the pair `(σ, shrink σ)` the mass

    out(σ) = ∑_{k ≥ 0} (-1)^k M σ k,

and `in(σ) = ∑_{ρ ∈ shrink^{-1}(σ)} out(ρ)` is what the construction spends at
`σ` as a target.  Certified here:

* `capacity_small` and `capacity_large`, the two regimes of `eq:capacity`,
  `|τ| ≤ 64` and `|τ| > 64`, each turning the size confinement of the fibre
  into `μ(shrink^{-1}(τ)) ≤ ½ μ'(τ)` through the mass bounds of
  `thm:shape-mass`;
* `cascadeOut_le` and `half_le_cascadeOut`, the alternating-series sandwich
  `½M₀ ≤ out ≤ M₀`;
* `cascadeIn_eq`, the identity `in = M₀ - out`, by summing the alternating
  series over the fibre;
* the two consequences the construction uses, `cascadeOut_add_cascadeIn` (a
  source atom spends its full mass) and `cascadeIn_le_half` (a target atom
  spends at most half of its mass, leaving the small remainders to be closed
  off by an arbitrary coupling).

The two shape laws enter as one type `T`, the disjoint union of the two
supports, which is how `shrink` alternates between them.
-/

namespace ChainClasses

open Real

/-! ### `eq:capacity`, the two regimes -/

/-- **`eq:capacity`, small targets.** For `|τ| ≤ 64` the fibre sits above size
`D²`, so its mass is at most `e^{-c₄D²}`, which the largeness condition
`log 2 + 64C⋆ ≤ c₄D²` turns into half of the point mass `e^{-C⋆|τ|}` of `τ`. -/
lemma capacity_small {cs x mfib mtau y : ℝ} (hcs : 0 ≤ cs) (hx : x ≤ 64)
    (htau : Real.exp (-(cs * x)) ≤ mtau) (hfib : mfib ≤ Real.exp (-y))
    (hy : Real.log 2 + 64 * cs ≤ y) : mfib ≤ mtau / 2 := by
  have h1 : Real.exp (-y) ≤ Real.exp (-(Real.log 2 + 64 * cs)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(Real.log 2 + 64 * cs)) = Real.exp (-(64 * cs)) / 2 := by
    rw [show -(Real.log 2 + 64 * cs) = -(64 * cs) + -Real.log 2 by ring, Real.exp_add,
      show -Real.log 2 = Real.log (2 : ℝ)⁻¹ by rw [Real.log_inv],
      Real.exp_log (by norm_num)]
    ring
  have h3 : Real.exp (-(64 * cs)) ≤ Real.exp (-(cs * x)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [h2] at h1
  linarith

/-- **`eq:capacity`, large targets.** For `|τ| > 64` the fibre sits above size
`3s|τ|/64`, so its mass is at most `e^{-3c₄s|τ|/64}`, which the largeness
condition `log 2/64 + C⋆ ≤ 3c₄s/64` turns into half of `e^{-C⋆|τ|}`. -/
lemma capacity_large {cs r x mfib mtau : ℝ} (hx : 64 < x)
    (htau : Real.exp (-(cs * x)) ≤ mtau) (hfib : mfib ≤ Real.exp (-(r * x)))
    (hr : Real.log 2 / 64 + cs ≤ r) : mfib ≤ mtau / 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hgap : Real.log 2 ≤ (r - cs) * x := by nlinarith
  have h1 : Real.exp (-(r * x)) ≤ Real.exp (-(cs * x)) / 2 := by
    have h2 : Real.exp (-(r * x)) * 2 ≤ Real.exp (-(cs * x)) := by
      have hstep : Real.exp (-(r * x)) * Real.exp (Real.log 2) ≤ Real.exp (-(cs * x)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at hstep
    linarith
  linarith

/-! ### The cascade -/

variable {T : Type*} {shrink : T → T} {M : T → ℕ → ℝ}

/-- The iterated-fibre masses of a shrinking map: `M σ k` is the mass of
`shrink^{-k}(σ)`, with the fibre decomposition and the capacity bound
`eq:capacity` at the first level. -/
structure IsCascade (shrink : T → T) (M : T → ℕ → ℝ) : Prop where
  nonneg : ∀ σ k, 0 ≤ M σ k
  fibre : ∀ σ k, HasSum (fun ρ : {ρ : T // shrink ρ = σ} => M ρ.1 k) (M σ (k + 1))
  capacity : ∀ σ, M σ 1 ≤ M σ 0 / 2

/-- The capacity bound propagates to every level: `M σ (k+1) ≤ M σ k / 2`. -/
lemma IsCascade.halving (h : IsCascade shrink M) : ∀ (k : ℕ) (σ : T), M σ (k + 1) ≤ M σ k / 2 := by
  intro k
  induction k with
  | zero => exact h.capacity
  | succ n ih =>
      intro σ
      have h1 : HasSum (fun ρ : {ρ : T // shrink ρ = σ} => M ρ.1 (n + 1)) (M σ (n + 1 + 1)) :=
        h.fibre σ (n + 1)
      have h2 : HasSum (fun ρ : {ρ : T // shrink ρ = σ} => M ρ.1 n / 2) (M σ (n + 1) / 2) :=
        HasSum.div_const (h.fibre σ n) 2
      refine hasSum_le ?_ h1 h2
      intro ρ
      exact ih ρ.1

/-- Geometric decay along the levels: `M σ (k+m) ≤ M σ m (1/2)^k`. -/
lemma IsCascade.le_shift (h : IsCascade shrink M) (σ : T) (m : ℕ) :
    ∀ k, M σ (k + m) ≤ M σ m * (1 / 2 : ℝ) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
      have hrw : n + 1 + m = n + m + 1 := by omega
      rw [hrw]
      have h1 : M σ (n + m + 1) ≤ M σ (n + m) / 2 := h.halving (n + m) σ
      have h2 : M σ m * (1 / 2 : ℝ) ^ (n + 1) = M σ m * (1 / 2 : ℝ) ^ n / 2 := by
        rw [pow_succ]; ring
      rw [h2]
      linarith

lemma IsCascade.summable_shift (h : IsCascade shrink M) (σ : T) (m : ℕ) :
    Summable fun k => M σ (k + m) := by
  refine Summable.of_nonneg_of_le (fun k => h.nonneg _ _) (h.le_shift σ m) ?_
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

lemma IsCascade.summable_row (h : IsCascade shrink M) (σ : T) : Summable fun k => M σ k := by
  simpa using h.summable_shift σ 0

lemma IsCascade.tsum_shift_le (h : IsCascade shrink M) (σ : T) (m : ℕ) :
    ∑' k, M σ (k + m) ≤ 2 * M σ m := by
  refine (Summable.tsum_le_tsum (h.le_shift σ m) (h.summable_shift σ m)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)).trans ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num
  linarith

/-- The alternating cascade sum from level `m` on. -/
noncomputable def outFrom (M : T → ℕ → ℝ) (σ : T) (m : ℕ) : ℝ :=
  ∑' k, (-1 : ℝ) ^ k * M σ (k + m)

/-- The cascade mass `out(σ)` given to the pair `(σ, shrink σ)`. -/
noncomputable def cascadeOut (M : T → ℕ → ℝ) (σ : T) : ℝ := outFrom M σ 0

/-- The cascade mass `in(σ)` spent at `σ` as a target. -/
noncomputable def cascadeIn (shrink : T → T) (M : T → ℕ → ℝ) (σ : T) : ℝ :=
  ∑' ρ : {ρ : T // shrink ρ = σ}, cascadeOut M ρ.1

lemma IsCascade.summable_outFrom (h : IsCascade shrink M) (σ : T) (m : ℕ) :
    Summable fun k => (-1 : ℝ) ^ k * M σ (k + m) := by
  have habs : (fun k => ‖(-1 : ℝ) ^ k * M σ (k + m)‖) = fun k => M σ (k + m) := by
    funext k
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_of_nonneg (h.nonneg _ _)]
  refine Summable.of_norm ?_
  rw [habs]
  exact h.summable_shift σ m

/-- Peeling the first term: `outFrom m = M σ m - outFrom (m+1)`. -/
lemma IsCascade.outFrom_rec (h : IsCascade shrink M) (σ : T) (m : ℕ) :
    outFrom M σ m = M σ m - outFrom M σ (m + 1) := by
  rw [outFrom, (h.summable_outFrom σ m).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, Nat.zero_add]
  have htail : ∑' k, (-1 : ℝ) ^ (k + 1) * M σ (k + 1 + m) = -outFrom M σ (m + 1) := by
    rw [outFrom, ← tsum_neg]
    refine tsum_congr fun k => ?_
    have hidx : k + 1 + m = k + (m + 1) := by omega
    rw [hidx, pow_succ]
    ring
  rw [htail]
  ring

lemma IsCascade.abs_outFrom_le (h : IsCascade shrink M) (σ : T) (m : ℕ) :
    |outFrom M σ m| ≤ 2 * M σ m := by
  have habs : (fun k => ‖(-1 : ℝ) ^ k * M σ (k + m)‖) = fun k => M σ (k + m) := by
    funext k
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_of_nonneg (h.nonneg _ _)]
  have hsum : Summable fun k => ‖(-1 : ℝ) ^ k * M σ (k + m)‖ := by
    rw [habs]; exact h.summable_shift σ m
  have h1 := norm_tsum_le_tsum_norm hsum
  rw [habs] at h1
  have h2 := h.tsum_shift_le σ m
  rw [Real.norm_eq_abs] at h1
  exact (h1.trans h2)

/-- The cascade mass is nonnegative. -/
lemma IsCascade.outFrom_nonneg (h : IsCascade shrink M) (σ : T) (m : ℕ) : 0 ≤ outFrom M σ m := by
  have h1 := h.outFrom_rec σ m
  have h2 := h.abs_outFrom_le σ (m + 1)
  have h3 : outFrom M σ (m + 1) ≤ 2 * M σ (m + 1) := (le_abs_self _).trans h2
  have h4 : M σ (m + 1) ≤ M σ m / 2 := h.halving m σ
  linarith

/-- **`½M₀ ≤ out`**: the alternating series loses at most the first correction,
which the capacity bound caps at half. -/
lemma IsCascade.half_le_outFrom (h : IsCascade shrink M) (σ : T) (m : ℕ) :
    M σ m / 2 ≤ outFrom M σ m := by
  have h1 := h.outFrom_rec σ m
  have h2 : outFrom M σ (m + 1) ≤ M σ (m + 1) := by
    have h3 := h.outFrom_rec σ (m + 1)
    have h4 := h.outFrom_nonneg σ (m + 2)
    linarith
  have h5 : M σ (m + 1) ≤ M σ m / 2 := h.halving m σ
  linarith

/-- **`out ≤ M₀`**: the cascade never spends more than the atom carries. -/
lemma IsCascade.outFrom_le (h : IsCascade shrink M) (σ : T) (m : ℕ) :
    outFrom M σ m ≤ M σ m := by
  have h1 := h.outFrom_rec σ m
  have h2 := h.outFrom_nonneg σ (m + 1)
  linarith

lemma IsCascade.cascadeOut_nonneg (h : IsCascade shrink M) (σ : T) : 0 ≤ cascadeOut M σ :=
  h.outFrom_nonneg σ 0

lemma IsCascade.half_le_cascadeOut (h : IsCascade shrink M) (σ : T) :
    M σ 0 / 2 ≤ cascadeOut M σ :=
  h.half_le_outFrom σ 0

lemma IsCascade.cascadeOut_le (h : IsCascade shrink M) (σ : T) : cascadeOut M σ ≤ M σ 0 :=
  h.outFrom_le σ 0

/-- **`in = M₀ - out`**: summing the alternating series over the fibre shifts
it by one level. -/
theorem IsCascade.cascadeIn_eq (h : IsCascade shrink M) (σ : T) :
    cascadeIn shrink M σ = M σ 0 - cascadeOut M σ := by
  set F : {ρ : T // shrink ρ = σ} → ℕ → ℝ := fun ρ k => (-1 : ℝ) ^ k * M ρ.1 k with hF
  have habs : ∀ (ρ : {ρ : T // shrink ρ = σ}) (k : ℕ), |F ρ k| = M ρ.1 k := by
    intro ρ k
    rw [hF]
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_of_nonneg (h.nonneg _ _)
  -- absolute summability of the double family
  have hrow : ∀ ρ : {ρ : T // shrink ρ = σ}, Summable fun k => |F ρ k| := by
    intro ρ
    simp only [habs]
    exact h.summable_row ρ.1
  have hcol : Summable fun ρ : {ρ : T // shrink ρ = σ} => ∑' k, |F ρ k| := by
    refine Summable.of_nonneg_of_le (fun ρ => tsum_nonneg fun k => abs_nonneg _)
      (fun ρ => ?_) (((h.fibre σ 0).summable).mul_left 2)
    simp only [habs]
    simpa using h.tsum_shift_le ρ.1 0
  have hsummable : Summable (Function.uncurry F) := by
    refine Summable.of_abs ?_
    refine (summable_prod_of_nonneg (fun p => abs_nonneg _)).mpr ⟨?_, ?_⟩
    · intro ρ; exact hrow ρ
    · exact hcol
  -- the two iterated sums
  have hswap : ∑' (k : ℕ) (ρ : {ρ : T // shrink ρ = σ}), F ρ k
      = ∑' (ρ : {ρ : T // shrink ρ = σ}) (k : ℕ), F ρ k := hsummable.tsum_comm
  have hinner : ∀ k : ℕ, ∑' ρ : {ρ : T // shrink ρ = σ}, F ρ k = (-1 : ℝ) ^ k * M σ (k + 1) := by
    intro k
    rw [hF]
    simp only
    rw [tsum_mul_left, (h.fibre σ k).tsum_eq]
  have hleft : ∑' (k : ℕ) (ρ : {ρ : T // shrink ρ = σ}), F ρ k = outFrom M σ 1 := by
    rw [outFrom]
    exact tsum_congr hinner
  have hright : ∑' (ρ : {ρ : T // shrink ρ = σ}) (k : ℕ), F ρ k = cascadeIn shrink M σ := by
    rw [cascadeIn]
    refine tsum_congr fun ρ => ?_
    rw [cascadeOut, outFrom]
    exact tsum_congr fun k => by simp only [hF, Nat.add_zero]
  rw [← hright, ← hswap, hleft]
  have := h.outFrom_rec σ 0
  rw [cascadeOut]
  linarith

/-- A source atom spends its full mass: `out(σ) + in(σ) = M₀(σ)`. -/
theorem IsCascade.cascadeOut_add_cascadeIn (h : IsCascade shrink M) (σ : T) :
    cascadeOut M σ + cascadeIn shrink M σ = M σ 0 := by
  rw [h.cascadeIn_eq σ]; ring

/-- A target atom spends at most half its mass, leaving the small remainders
of equal total mass to be closed off by an arbitrary coupling. -/
theorem IsCascade.cascadeIn_le_half (h : IsCascade shrink M) (σ : T) :
    cascadeIn shrink M σ ≤ M σ 0 / 2 := by
  have h1 := h.cascadeIn_eq σ
  have h2 := h.half_le_cascadeOut σ
  linarith

end ChainClasses
