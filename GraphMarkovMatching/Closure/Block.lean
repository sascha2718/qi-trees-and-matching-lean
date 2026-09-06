/-
The abstract linear-block layer of the arbitrary-support screened recursion
(`arbitrary_offspring_matching.tex` `sec:recursion`: `thm:engine` and its
closure form `thm:closure-form`).

The screen block acts by a nonnegative matrix `N` on the finitely many
live screen coordinates and is nilpotent; the two facts of the section are
certified in invariant form:

* `nilSum_fixed`, `nilpotent_invariant` (`thm:invariant`): the vector
  `Ê = ∑_{j<r} N^j(u·𝟙)` satisfies `u + (N Ê)_i = Ê_i` when
  `N^r(u·𝟙) = 0`, and any screen sequence with `E_0 ≤ u·𝟙` and
  `E_{h+1} ≤ u·𝟙 + N E_h` stays below `Ê` at every height;
* `screened_uniform_bound_mono` (`thm:engine`): the abstract closure with
  arbitrary monotone step functions `f, g`; under the closure inequalities
  `f(Kc·η, Ξ) ≤ Kc·η` and `g(Kc·η, Ξ) ≤ u`, the scalar satisfies
  `Ψ_h ≤ Kc·η` uniformly in the height.

The matrix `N` need not be substochastic in any norm; only nilpotence and
the invariant vector enter (tex: no operator norm and no substochasticity
enter `thm:engine`).  The current block matrix is `accN` with the constant
`CW` on full-successor edges.  The instantiation with the concrete ledger
is `Closure/Gen.lean` and `Closure/EStep.lean`.
-/
import GraphMarkovMatching.Process.Basic

namespace GraphMarkovMatching

open scoped ENNReal

variable {ι : Type} [Fintype ι]

/-! ### Matrix–vector calculus over `ℝ≥0∞` -/

/-- Matrix–vector action of a nonnegative screen-transfer matrix. -/
noncomputable def mulVec (N : ι → ι → ℝ≥0∞) (x : ι → ℝ≥0∞) : ι → ℝ≥0∞ :=
  fun i => ∑ j, N i j * x j

/-- `mulVec` is monotone in the vector. -/
lemma mulVec_mono {N : ι → ι → ℝ≥0∞} {x y : ι → ℝ≥0∞}
    (h : ∀ j, x j ≤ y j) (i : ι) :
    mulVec N x i ≤ mulVec N y i :=
  Finset.sum_le_sum fun j _ => mul_le_mul_right (h j) _

/-- `mulVec` commutes with finite sums of vectors. -/
lemma mulVec_sum {β : Type} (s : Finset β) (N : ι → ι → ℝ≥0∞)
    (f : β → ι → ℝ≥0∞) (i : ι) :
    mulVec N (fun k => ∑ b ∈ s, f b k) i = ∑ b ∈ s, mulVec N (f b) i := by
  unfold mulVec
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-! ### The nilpotent invariant -/

/-- The invariant vector `Ê = ∑_{j<r} N^j(u·𝟙)` of the nilpotent screen
block (`thm:invariant`). -/
noncomputable def nilSum (N : ι → ι → ℝ≥0∞) (r : ℕ) (u : ℝ≥0∞) : ι → ℝ≥0∞ :=
  fun i => ∑ j ∈ Finset.range r, (mulVec N)^[j] (fun _ => u) i

/-- The fixed-point identity `u + (N Ê)_i = Ê_i` under `N^r(u·𝟙) = 0`
(`thm:invariant`). -/
lemma nilSum_fixed {N : ι → ι → ℝ≥0∞} {r : ℕ} {u : ℝ≥0∞}
    (hnil : (mulVec N)^[r] (fun _ => u) = fun _ => 0) (i : ι) :
    u + mulVec N (nilSum N r u) i = nilSum N r u i := by
  have h1 : mulVec N (nilSum N r u) i
      = ∑ j ∈ Finset.range r, (mulVec N)^[j + 1] (fun _ => u) i := by
    rw [show nilSum N r u = fun k => ∑ j ∈ Finset.range r,
          (mulVec N)^[j] (fun _ => u) k from rfl, mulVec_sum]
    exact Finset.sum_congr rfl fun j _ =>
      (congrFun (Function.iterate_succ_apply' (mulVec N) j _) i).symm
  have hgr : (mulVec N)^[r] (fun _ => u) i = 0 := by rw [hnil]
  have h2 : ∑ j ∈ Finset.range (r + 1), (mulVec N)^[j] (fun _ => u) i
      = (∑ j ∈ Finset.range r, (mulVec N)^[j + 1] (fun _ => u) i) + u :=
    Finset.sum_range_succ' (fun j => (mulVec N)^[j] (fun _ => u) i) r
  have h3 : ∑ j ∈ Finset.range (r + 1), (mulVec N)^[j] (fun _ => u) i
      = nilSum N r u i + (mulVec N)^[r] (fun _ => u) i :=
    Finset.sum_range_succ (fun j => (mulVec N)^[j] (fun _ => u) i) r
  calc u + mulVec N (nilSum N r u) i
      = (∑ j ∈ Finset.range r, (mulVec N)^[j + 1] (fun _ => u) i) + u := by
        rw [h1]; exact add_comm _ _
    _ = ∑ j ∈ Finset.range (r + 1), (mulVec N)^[j] (fun _ => u) i := h2.symm
    _ = nilSum N r u i + (mulVec N)^[r] (fun _ => u) i := h3
    _ = nilSum N r u i := by rw [hgr, add_zero]

/-- **The nilpotent invariant** (`thm:invariant`, the screen half of the
block recursion): a sequence with `E_0 ≤ u·𝟙` and
`E_{h+1} ≤ u·𝟙 + N E_h` stays below `Ê = ∑_{j<r} N^j(u·𝟙)` at every
height. -/
theorem nilpotent_invariant {N : ι → ι → ℝ≥0∞} {r : ℕ} {u : ℝ≥0∞}
    (hr : 0 < r)
    (hnil : (mulVec N)^[r] (fun _ => u) = fun _ => 0)
    (E : ℕ → ι → ℝ≥0∞)
    (hE0 : ∀ i, E 0 i ≤ u)
    (hstep : ∀ h i, E (h + 1) i ≤ u + mulVec N (E h) i) :
    ∀ h i, E h i ≤ nilSum N r u i := by
  intro h
  induction h with
  | zero =>
      intro i
      exact le_trans (hE0 i)
        (Finset.single_le_sum
          (f := fun j => (mulVec N)^[j] (fun _ => u) i)
          (fun j _ => zero_le) (Finset.mem_range.mpr hr))
  | succ h ih =>
      intro i
      refine le_trans (hstep h i) ?_
      rw [← nilSum_fixed hnil i]
      exact add_le_add le_rfl (mulVec_mono ih i)

/-! ### The coupled recursion -/

/-- **The screened block recursion, monotone form** (`thm:engine`): the
step inhomogeneities may be arbitrary functions of the ordinary scalar and
the screen supremum, monotone in both arguments; the closure inequalities
are evaluated at the bounds.  This subsumes the quadratic form
and absorbs the higher-degree cross terms of the assembled ledger rows. -/
theorem screened_uniform_bound_mono
    {N : ι → ι → ℝ≥0∞} {r : ℕ} (hr : 0 < r)
    (Ψ : ℕ → ℝ≥0∞) (E : ℕ → ι → ℝ≥0∞)
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (hf : ∀ a a' b b', a ≤ a' → b ≤ b' → f a b ≤ f a' b')
    (hg : ∀ a a' b b', a ≤ a' → b ≤ b' → g a b ≤ g a' b')
    (Kc η u Ξ : ℝ≥0∞)
    (hnil : (mulVec N)^[r] (fun _ => u) = fun _ => 0)
    (hΞ : ∀ i, nilSum N r u i ≤ Ξ)
    (hΨ0 : Ψ 0 ≤ Kc * η)
    (hE0 : ∀ i, E 0 i ≤ u)
    (hΨstep : ∀ h, Ψ (h + 1) ≤ f (Ψ h) (⨆ i, E h i))
    (hEstep : ∀ h i, E (h + 1) i ≤ g (Ψ h) (⨆ i, E h i) + mulVec N (E h) i)
    (hu : g (Kc * η) Ξ ≤ u)
    (hclose : f (Kc * η) Ξ ≤ Kc * η) :
    ∀ h, Ψ h ≤ Kc * η := by
  have main : ∀ h, Ψ h ≤ Kc * η ∧ ∀ i, E h i ≤ nilSum N r u i := by
    intro h
    induction h with
    | zero =>
        refine ⟨hΨ0, fun i => ?_⟩
        exact le_trans (hE0 i)
          (Finset.single_le_sum
            (f := fun j => (mulVec N)^[j] (fun _ => u) i)
            (fun j _ => zero_le) (Finset.mem_range.mpr hr))
    | succ h ih =>
        obtain ⟨ihΨ, ihE⟩ := ih
        have hsup : (⨆ i, E h i) ≤ Ξ :=
          iSup_le fun i => le_trans (ihE i) (hΞ i)
        constructor
        · exact le_trans (hΨstep h)
            (le_trans (hf _ _ _ _ ihΨ hsup) hclose)
        · intro i
          refine le_trans (hEstep h i) ?_
          rw [← nilSum_fixed hnil i]
          exact add_le_add (le_trans (hg _ _ _ _ ihΨ hsup) hu)
            (mulVec_mono ihE i)
  exact fun h => (main h).1

end GraphMarkovMatching
