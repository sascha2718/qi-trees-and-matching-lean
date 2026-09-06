/-
Rare two-law perturbations of a finite screen grammar.

This file supplies the analytic mechanism for the near-common-support
extension in `matching_classes_general.tex`.  If the common-core screen
operator is nilpotent and every exceptional transition retains its small
mass `eps`, then the full operator is a small perturbation of a nilpotent
one.  Its block powers contract for sufficiently small `eps`, hence its
Green vector is finite and the abstract screened closure applies.
-/
import GraphMarkovMatching.Composite.Resolvent
import GraphMarkovMatching.Closure.Geometric

namespace GraphMarkovMatching

open scoped ENNReal Classical

variable {ι : Type} [Fintype ι]

/-- The screen operator obtained from a common core `N` and an exceptional
row `M` which retains the exceptional mass `eps`. -/
noncomputable def rareMatrix (N M : ι → ι → ℝ≥0∞) (eps : ℝ≥0∞) :
    ι → ι → ℝ≥0∞ :=
  fun i j => N i j + eps * M i j

lemma mulVec_rareMatrix (N M : ι → ι → ℝ≥0∞) (eps : ℝ≥0∞)
    (x : ι → ℝ≥0∞) (i : ι) :
    mulVec (rareMatrix N M eps) x i = mulVec N x i + eps * mulVec M x i := by
  unfold rareMatrix mulVec
  simp_rw [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The row sum of the rare perturbation is at most `2*C` when both
constituent row sums are at most `C` and `eps ≤ 1`. -/
lemma rareMatrix_row_sum_le {N M : ι → ι → ℝ≥0∞} {eps C : ℝ≥0∞}
    (heps : eps ≤ 1)
    (hNrow : ∀ i, ∑ j, N i j ≤ C)
    (hMrow : ∀ i, ∑ j, M i j ≤ C) (i : ι) :
    ∑ j, rareMatrix N M eps i j ≤ 2 * C := by
  rw [show (∑ j, rareMatrix N M eps i j) =
      (∑ j, N i j) + eps * ∑ j, M i j by
    unfold rareMatrix
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]]
  calc
    (∑ j, N i j) + eps * ∑ j, M i j ≤ C + 1 * C := by
      gcongr
      · exact hNrow i
      · exact hMrow i
    _ = 2 * C := by ring

/-- All powers of the perturbed operator have the crude row bound
`(2*C)^n`. -/
lemma rareMatrix_iterate_le {N M : ι → ι → ℝ≥0∞} {eps C : ℝ≥0∞}
    (heps : eps ≤ 1)
    (hNrow : ∀ i, ∑ j, N i j ≤ C)
    (hMrow : ∀ i, ∑ j, M i j ≤ C) :
    ∀ n i, (mulVec (rareMatrix N M eps))^[n] (fun _ => 1) i ≤ (2 * C) ^ n := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ih =>
      intro i
      rw [Function.iterate_succ_apply']
      calc
        mulVec (rareMatrix N M eps)
            ((mulVec (rareMatrix N M eps))^[n] (fun _ => 1)) i
            ≤ (2 * C) * (2 * C) ^ n :=
          mulVec_le_of_row_sum (rareMatrix_row_sum_le heps hNrow hMrow) ih i
        _ = (2 * C) ^ (n + 1) := by rw [pow_succ']

/-- A nilpotent common core plus an `eps`-weighted exceptional operator has
an `r`-step row bound `eps * (2*C)^r`.  This is the precise perturbative
replacement for the invalid use of the unweighted renewal kernel. -/
theorem rareMatrix_iterate_le_core_add {N M : ι → ι → ℝ≥0∞}
    {eps C : ℝ≥0∞}
    (heps : eps ≤ 1)
    (hNrow : ∀ i, ∑ j, N i j ≤ C)
    (hMrow : ∀ i, ∑ j, M i j ≤ C) :
    ∀ n i, (mulVec (rareMatrix N M eps))^[n] (fun _ => 1) i ≤
      (mulVec N)^[n] (fun _ => 1) i + eps * (2 * C) ^ n := by
  intro n
  induction n with
  | zero =>
      intro i
      simp
  | succ n ih =>
      intro i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        mulVec_rareMatrix]
      have hW := rareMatrix_iterate_le heps hNrow hMrow n
      have hN : mulVec N ((mulVec (rareMatrix N M eps))^[n] (fun _ => 1)) i ≤
          mulVec N ((mulVec N)^[n] (fun _ => 1)) i + C * (eps * (2 * C) ^ n) := by
        calc
          mulVec N ((mulVec (rareMatrix N M eps))^[n] (fun _ => 1)) i
              ≤ mulVec N (fun j => (mulVec N)^[n] (fun _ => 1) j +
                  eps * (2 * C) ^ n) i := mulVec_mono ih i
          _ = mulVec N ((mulVec N)^[n] (fun _ => 1)) i +
                mulVec N (fun _ => eps * (2 * C) ^ n) i := by
              unfold mulVec
              simp_rw [mul_add, Finset.sum_add_distrib]
          _ ≤ mulVec N ((mulVec N)^[n] (fun _ => 1)) i +
                C * (eps * (2 * C) ^ n) := by
              gcongr
              exact mulVec_le_of_row_sum hNrow (fun _ => le_rfl) i
      have hM : mulVec M ((mulVec (rareMatrix N M eps))^[n] (fun _ => 1)) i ≤
          C * (2 * C) ^ n :=
        mulVec_le_of_row_sum hMrow hW i
      calc
        mulVec N ((mulVec (rareMatrix N M eps))^[n] (fun _ => 1)) i +
            eps * mulVec M ((mulVec (rareMatrix N M eps))^[n] (fun _ => 1)) i
            ≤ (mulVec N ((mulVec N)^[n] (fun _ => 1)) i +
                C * (eps * (2 * C) ^ n)) + eps * (C * (2 * C) ^ n) := by
              gcongr
        _ = mulVec N ((mulVec N)^[n] (fun _ => 1)) i +
              eps * (2 * C) ^ (n + 1) := by
            rw [pow_succ']
            ring

/-- At the nilpotence exponent the common term disappears, so every live
block of length `r` pays the exceptional mass. -/
theorem rareMatrix_block_contraction {N M : ι → ι → ℝ≥0∞}
    {eps C : ℝ≥0∞} {r : ℕ}
    (heps : eps ≤ 1)
    (hNrow : ∀ i, ∑ j, N i j ≤ C)
    (hMrow : ∀ i, ∑ j, M i j ≤ C)
    (hnil : (mulVec N)^[r] (fun _ => 1) = fun _ => 0) (i : ι) :
    (mulVec (rareMatrix N M eps))^[r] (fun _ => 1) i ≤
      eps * (2 * C) ^ r := by
  refine le_trans (rareMatrix_iterate_le_core_add heps hNrow hMrow r i) ?_
  rw [hnil]
  simp

/-! ### From a rare block contraction to a finite Green bound -/

/-- On a finite index type the countable-kernel action is the ordinary
finite matrix action. -/
lemma mulVecInf_eq_mulVec (N : ι → ι → ℝ≥0∞) (x : ι → ℝ≥0∞) :
    mulVecInf N x = mulVec N x := by
  funext i
  rw [mulVecInf, mulVec, tsum_fintype]

/-- Consequently the two notions of a kernel power agree on finite state
spaces. -/
lemma infPow_eq_iterate (N : ι → ι → ℝ≥0∞) :
    ∀ n x, infPow N n x = (mulVec N)^[n] x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      rw [infPow, ih, Function.iterate_succ_apply']
      exact mulVecInf_eq_mulVec N _

/-- Iterated finite matrix actions preserve pointwise inequalities. -/
lemma mulVec_iterate_mono {W : ι → ι → ℝ≥0∞} {x y : ι → ℝ≥0∞}
    (hxy : ∀ i, x i ≤ y i) :
    ∀ n i, (mulVec W)^[n] x i ≤ (mulVec W)^[n] y i := by
  intro n
  induction n with
  | zero => exact hxy
  | succ n ih =>
      intro i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact mulVec_mono ih i

/-- A row-sum bound propagates through any number of steps, starting from
an arbitrary constant majorant. -/
lemma mulVec_iterate_le_of_row_sum {W : ι → ι → ℝ≥0∞} {D b : ℝ≥0∞}
    (hrow : ∀ i, ∑ j, W i j ≤ D) {x : ι → ℝ≥0∞}
    (hx : ∀ i, x i ≤ b) :
    ∀ n i, (mulVec W)^[n] x i ≤ D ^ n * b := by
  intro n
  induction n with
  | zero =>
      intro i
      simpa using hx i
  | succ n ih =>
      intro i
      rw [Function.iterate_succ_apply']
      calc
        mulVec W ((mulVec W)^[n] x) i ≤ D * (D ^ n * b) :=
          mulVec_le_of_row_sum hrow ih i
        _ = D ^ (n + 1) * b := by rw [pow_succ']; ring

/-- A scalar can be pulled through every finite matrix power. -/
lemma mulVec_iterate_mul (W : ι → ι → ℝ≥0∞) (a : ℝ≥0∞)
    (x : ι → ℝ≥0∞) (n : ℕ) (i : ι) :
    (mulVec W)^[n] (fun j => a * x j) i =
      a * (mulVec W)^[n] x i := by
  rw [← infPow_eq_iterate W, ← infPow_eq_iterate W]
  exact infPow_mul W a x n i

/-- Repeating an `r`-step contraction gives a geometric bound at all
block endpoints. -/
lemma mulVec_iterate_blocks_le {W : ι → ι → ℝ≥0∞} {ρ : ℝ≥0∞} {r : ℕ}
    (hblock : ∀ i, (mulVec W)^[r] (fun _ => 1) i ≤ ρ) :
    ∀ q i, (mulVec W)^[q * r] (fun _ => 1) i ≤ ρ ^ q := by
  intro q
  induction q with
  | zero => intro i; simp
  | succ q ih =>
      intro i
      rw [Nat.succ_mul, Function.iterate_add_apply]
      calc
        (mulVec W)^[q * r] ((mulVec W)^[r] (fun _ => 1)) i
            ≤ (mulVec W)^[q * r] (fun _ => ρ * 1) i :=
          mulVec_iterate_mono (fun j => by simpa using hblock j) (q * r) i
        _ = ρ * (mulVec W)^[q * r] (fun _ => 1) i :=
          mulVec_iterate_mul W ρ (fun _ => 1) (q * r) i
        _ ≤ ρ * ρ ^ q := mul_le_mul_right (ih i) ρ
        _ = ρ ^ (q + 1) := by rw [pow_succ']

/-- Fill the remainder after each contracting block using only a crude
one-step row bound. -/
lemma mulVec_iterate_le_of_block {W : ι → ι → ℝ≥0∞} {D ρ : ℝ≥0∞}
    {r : ℕ}
    (hrow : ∀ i, ∑ j, W i j ≤ D)
    (hblock : ∀ i, (mulVec W)^[r] (fun _ => 1) i ≤ ρ) :
    ∀ m i, (mulVec W)^[m] (fun _ => 1) i ≤
      ρ ^ (m / r) * D ^ (m % r) := by
  intro m i
  have hm : m = m % r + (m / r) * r := by
    simpa [Nat.mul_comm, Nat.add_comm] using (Nat.div_add_mod m r).symm
  calc
    (mulVec W)^[m] (fun _ => 1) i =
        (mulVec W)^[m % r + (m / r) * r] (fun _ => 1) i :=
      congrFun (congrArg (fun n => (mulVec W)^[n] (fun _ => 1)) hm) i
    _ = (mulVec W)^[m % r]
        ((mulVec W)^[(m / r) * r] (fun _ => 1)) i :=
      congrFun (Function.iterate_add_apply (mulVec W) (m % r)
        ((m / r) * r) (fun _ => 1)) i
    _ ≤ D ^ (m % r) * ρ ^ (m / r) :=
      mulVec_iterate_le_of_row_sum hrow
        (mulVec_iterate_blocks_le hblock (m / r)) (m % r) i
    _ = ρ ^ (m / r) * D ^ (m % r) := mul_comm _ _

/-- Quotient and remainder turn the scalar path series into a geometric
series of blocks times the finite contribution of a remainder. -/
lemma tsum_block_geometric (r : ℕ) [NeZero r] (ρ D : ℝ≥0∞) :
    (∑' m : ℕ, ρ ^ (m / r) * D ^ (m % r)) =
      (1 - ρ)⁻¹ * (∑ j : Fin r, D ^ (j : ℕ)) := by
  calc
    (∑' m : ℕ, ρ ^ (m / r) * D ^ (m % r)) =
        (∑' q : ℕ, ρ ^ q) * (∑ j : Fin r, D ^ (j : ℕ)) := by
      calc
        (∑' m : ℕ, ρ ^ (m / r) * D ^ (m % r)) =
            ∑' m : ℕ, ρ ^ ((Nat.divModEquiv r m).1) *
              D ^ ((Nat.divModEquiv r m).2 : ℕ) := by simp
        _ = ∑' p : ℕ × Fin r, ρ ^ p.1 * D ^ (p.2 : ℕ) :=
          (Nat.divModEquiv r).tsum_eq
            (fun p : ℕ × Fin r => ρ ^ p.1 * D ^ (p.2 : ℕ))
        _ = (∑' q : ℕ, ρ ^ q) * (∑ j : Fin r, D ^ (j : ℕ)) := by
          calc
            (∑' p : ℕ × Fin r, ρ ^ p.1 * D ^ (p.2 : ℕ)) =
                ∑' q : ℕ, ∑' j : Fin r, ρ ^ q * D ^ (j : ℕ) :=
              ENNReal.tsum_prod'
            _ = _ := by
              simp_rw [tsum_fintype, ← Finset.mul_sum]
              rw [ENNReal.tsum_mul_right]
    _ = (1 - ρ)⁻¹ * (∑ j : Fin r, D ^ (j : ℕ)) := by
      rw [ENNReal.tsum_geometric]

/-- The weighted rare-matrix closure with both conclusions exposed: the
ordinary coordinate stays below `Kc * η` and every exceptional debt stays
below `Ξ`. -/
theorem screened_uniform_bound_rareMatrix_with_debt
    (N M : ι → ι → ℝ≥0∞) (eps C : ℝ≥0∞) (r : ℕ) (hr : 0 < r)
    (heps : eps ≤ 1)
    (hNrow : ∀ i, ∑ j, N i j ≤ C)
    (hMrow : ∀ i, ∑ j, M i j ≤ C)
    (hnil : (mulVec N)^[r] (fun _ => 1) = fun _ => 0)
    (Kc η u Ξ : ℝ≥0∞)
    (hΞ : (1 - eps * (2 * C) ^ r)⁻¹ *
        (∑ j : Fin r, (2 * C) ^ (j : ℕ)) * u ≤ Ξ)
    (Ψ : ℕ → ℝ≥0∞) (E : ℕ → ι → ℝ≥0∞)
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (hf : ∀ a a' b b', a ≤ a' → b ≤ b' → f a b ≤ f a' b')
    (hg : ∀ a a' b b', a ≤ a' → b ≤ b' → g a b ≤ g a' b')
    (hΨ0 : Ψ 0 ≤ Kc * η)
    (hE0 : ∀ i, E 0 i ≤ u)
    (hΨstep : ∀ h, Ψ (h + 1) ≤ f (Ψ h) (⨆ i, E h i))
    (hEstep : ∀ h i,
      E (h + 1) i ≤ g (Ψ h) (⨆ j, E h j) +
        mulVecInf (rareMatrix N M eps) (E h) i)
    (hu : g (Kc * η) Ξ ≤ u)
    (hclose : f (Kc * η) Ξ ≤ Kc * η) :
    ∀ h, Ψ h ≤ Kc * η ∧ ∀ i, E h i ≤ Ξ := by
  letI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  have hrow : ∀ i, ∑ j, rareMatrix N M eps i j ≤ 2 * C :=
    rareMatrix_row_sum_le heps hNrow hMrow
  have hblock : ∀ i,
      (mulVec (rareMatrix N M eps))^[r] (fun _ => 1) i ≤
        eps * (2 * C) ^ r :=
    rareMatrix_block_contraction heps hNrow hMrow hnil
  have hpath : ∀ m i,
      infPow (rareMatrix N M eps) m (fun _ => 1) i ≤
        (eps * (2 * C) ^ r) ^ (m / r) * (2 * C) ^ (m % r) := by
    intro m i
    rw [infPow_eq_iterate]
    exact mulVec_iterate_le_of_block hrow hblock m i
  have hsum :
      (∑' m : ℕ, (eps * (2 * C) ^ r) ^ (m / r) *
        (2 * C) ^ (m % r)) * u ≤ Ξ := by
    rw [tsum_block_geometric]
    exact hΞ
  exact screened_uniform_bound_resolvent_with_debt
    (rareMatrix N M eps)
    (fun m => (eps * (2 * C) ^ r) ^ (m / r) * (2 * C) ^ (m % r))
    Kc η u Ξ hpath hsum Ψ E f g hf hg hΨ0 hE0 hΨstep hEstep hu hclose

end GraphMarkovMatching
