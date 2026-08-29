/-
Rare two-law perturbations of a finite screen grammar.

This file supplies the analytic mechanism for the near-common-support
extension in `matching_classes_general.tex`.  If the common-core screen
operator is nilpotent and every exceptional transition retains its small
mass `eps`, then the full operator is a small perturbation of a nilpotent
one.  Its block powers contract for sufficiently small `eps`, hence its
Green vector is finite and the abstract screened closure applies.
-/
import GraphMarkovMatching.Tail.Block
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

/-- **Rare-perturbation Green bound.**  If `N` is nilpotent and both
`N` and `M` have row sums at most `C`, then the resolvent of
`N + eps M` is controlled by a geometric block series.  The only smallness
condition needed later is `eps * (2*C)^r < 1`. -/
theorem rareMatrix_resolvent_le {N M : ι → ι → ℝ≥0∞}
    {eps C : ℝ≥0∞} {r : ℕ} (hr : 0 < r)
    (heps : eps ≤ 1)
    (hNrow : ∀ i, ∑ j, N i j ≤ C)
    (hMrow : ∀ i, ∑ j, M i j ≤ C)
    (hnil : (mulVec N)^[r] (fun _ => 1) = fun _ => 0) (i : ι) :
    infResolvent (rareMatrix N M eps) (fun _ => 1) i ≤
      (1 - eps * (2 * C) ^ r)⁻¹ *
        (∑ j : Fin r, (2 * C) ^ (j : ℕ)) := by
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
  calc
    infResolvent (rareMatrix N M eps) (fun _ => 1) i ≤
        (∑' m : ℕ, (eps * (2 * C) ^ r) ^ (m / r) *
          (2 * C) ^ (m % r)) * 1 := infResolvent_le hpath i
    _ = (1 - eps * (2 * C) ^ r)⁻¹ *
        (∑ j : Fin r, (2 * C) ^ (j : ℕ)) := by
      rw [mul_one, tsum_block_geometric]

/-- **Rare-perturbation screened closure.**  This is the analytic endpoint
used by the near-common-law matching proof.  Once the concrete grammar has
been split as `N + eps M`, with a nilpotent common part `N`, the original
height induction closes under the displayed finite Green-vector budget. -/
theorem screened_uniform_bound_rareMatrix
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
    ∀ h, Ψ h ≤ Kc * η := by
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
  exact screened_uniform_bound_resolvent
    (rareMatrix N M eps)
    (fun m => (eps * (2 * C) ^ r) ^ (m / r) * (2 * C) ^ (m % r))
    Kc η u Ξ hpath hsum Ψ E f g hf hg hΨ0 hE0 hΨstep hEstep hu hclose

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

/-! ### The explicit polynomial small-parameter specialization -/

/-- Linear coefficient used in the polynomial specialization of the
weighted Hall ledger. -/
noncomputable def weightedLedgerA (a c d Γ : ℝ≥0∞) : ℝ≥0∞ :=
  a + 2 * c * d * Γ

noncomputable def weightedLedgerK (a c d Γ : ℝ≥0∞) : ℝ≥0∞ :=
  2 * weightedLedgerA a c d Γ

noncomputable def weightedLedgerU (d η : ℝ≥0∞) : ℝ≥0∞ := 2 * d * η

noncomputable def weightedLedgerXi (d Γ η : ℝ≥0∞) : ℝ≥0∞ :=
  2 * d * Γ * η

/-- **Polynomial weighted-ledger closure.**  This is the denominator-free
formal version of the manuscript's two explicit smallness inequalities.  It
proves all three scalar closure conditions, including the positive ordinary
budget; there is no premise of the form `2 * K * η ≤ K * η`. -/
theorem weightedLedger_polynomial_closure
    (a b c d e Γ η : ℝ≥0∞)
    (hb : b * (weightedLedgerK a c d Γ) ^ 2 * η ≤
      weightedLedgerA a c d Γ)
    (he : e * (weightedLedgerK a c d Γ + 2 * d * Γ) ^ 2 * η ≤ d) :
    Γ * weightedLedgerU d η ≤ weightedLedgerXi d Γ η ∧
      d * η + e * (weightedLedgerK a c d Γ * η +
          weightedLedgerXi d Γ η) ^ 2 ≤ weightedLedgerU d η ∧
      a * η + b * (weightedLedgerK a c d Γ * η) ^ 2 +
          c * weightedLedgerXi d Γ η ≤
        weightedLedgerK a c d Γ * η := by
  let A := weightedLedgerA a c d Γ
  let K := weightedLedgerK a c d Γ
  have hb' : b * K ^ 2 * η ≤ A := by simpa [K, A] using hb
  have he' : e * (K + 2 * d * Γ) ^ 2 * η ≤ d := by
    simpa [K] using he
  have hquadF : b * (K * η) ^ 2 ≤ A * η := by
    calc
      b * (K * η) ^ 2 = (b * K ^ 2 * η) * η := by ring
      _ ≤ A * η := by
        simpa [mul_comm] using mul_le_mul_right hb' η
  have hquadG : e * (K * η + weightedLedgerXi d Γ η) ^ 2 ≤ d * η := by
    calc
      e * (K * η + weightedLedgerXi d Γ η) ^ 2 =
          (e * (K + 2 * d * Γ) ^ 2 * η) * η := by
            simp only [weightedLedgerXi]
            ring
      _ ≤ d * η := by
        simpa [mul_comm] using mul_le_mul_right he' η
  refine ⟨?_, ?_, ?_⟩
  · simp only [weightedLedgerU, weightedLedgerXi]
    rw [show Γ * (2 * d * η) = 2 * d * Γ * η by ring]
  · change d * η + e * (K * η + weightedLedgerXi d Γ η) ^ 2 ≤
      weightedLedgerU d η
    calc
      d * η + e * (K * η + weightedLedgerXi d Γ η) ^ 2 ≤
          d * η + d * η := add_le_add le_rfl hquadG
      _ = weightedLedgerU d η := by simp [weightedLedgerU]; ring
  · change a * η + b * (K * η) ^ 2 + c * weightedLedgerXi d Γ η ≤ K * η
    calc
      a * η + b * (K * η) ^ 2 + c * weightedLedgerXi d Γ η ≤
          a * η + A * η + c * weightedLedgerXi d Γ η := by gcongr
      _ = K * η := by
        simp only [A, K, weightedLedgerA, weightedLedgerK, weightedLedgerXi]
        ring

/-- Function-level form of the polynomial specialization.  Bounds on `f`
and `g` at the invariant corner imply the exact closure hypotheses consumed
by the weighted ledger. -/
theorem weightedLedger_polynomial_function_closure
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (a b c d e Γ η : ℝ≥0∞)
    (hb : b * (weightedLedgerK a c d Γ) ^ 2 * η ≤
      weightedLedgerA a c d Γ)
    (he : e * (weightedLedgerK a c d Γ + 2 * d * Γ) ^ 2 * η ≤ d)
    (hf : f (weightedLedgerK a c d Γ * η)
        (weightedLedgerXi d Γ η) ≤
      a * η + b * (weightedLedgerK a c d Γ * η) ^ 2 +
        c * weightedLedgerXi d Γ η)
    (hg : g (weightedLedgerK a c d Γ * η)
        (weightedLedgerXi d Γ η) ≤
      d * η + e * (weightedLedgerK a c d Γ * η +
        weightedLedgerXi d Γ η) ^ 2) :
    Γ * weightedLedgerU d η ≤ weightedLedgerXi d Γ η ∧
      g (weightedLedgerK a c d Γ * η) (weightedLedgerXi d Γ η) ≤
        weightedLedgerU d η ∧
      f (weightedLedgerK a c d Γ * η) (weightedLedgerXi d Γ η) ≤
        weightedLedgerK a c d Γ * η := by
  obtain ⟨hXi, hgPoly, hfPoly⟩ :=
    weightedLedger_polynomial_closure a b c d e Γ η hb he
  exact ⟨hXi, hg.trans hgPoly, hf.trans hfPoly⟩

/-- The two denominator-free smallness conditions above have a strictly
positive solution for every finite nonnegative polynomial coefficient with
`a,d > 0`.  This is the formal content of "a genuine small positive
regime" in the manuscript. -/
theorem exists_pos_weightedLedger_polynomial_smallness
    {a b c d e Γ : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d)
    (he : 0 ≤ e) (hΓ : 0 ≤ Γ) :
    let A := a + 2 * c * d * Γ
    let K := 2 * A
    ∃ η : ℝ, 0 < η ∧ b * K ^ 2 * η ≤ A ∧
      e * (K + 2 * d * Γ) ^ 2 * η ≤ d := by
  dsimp only
  let A := a + 2 * c * d * Γ
  let K := 2 * A
  let B := b * K ^ 2
  let E := e * (K + 2 * d * Γ) ^ 2
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  let η := min (A / (1 + B)) (d / (1 + E))
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (div_pos hA (by positivity)) (div_pos hd (by positivity))
  refine ⟨η, hη, ?_, ?_⟩
  · change B * η ≤ A
    have hsmall : η ≤ A / (1 + B) := min_le_left _ _
    have hmul : η * (1 + B) ≤ A :=
      (le_div_iff₀ (by positivity : 0 < 1 + B)).mp hsmall
    nlinarith
  · change E * η ≤ d
    have hsmall : η ≤ d / (1 + E) := min_le_right _ _
    have hmul : η * (1 + E) ≤ d :=
      (le_div_iff₀ (by positivity : 0 < 1 + E)).mp hsmall
    nlinarith

/-! ### An explicit fixed-law threshold -/

/-- Real-valued version of the linear budget in the polynomial ledger.  It
is used only to state an explicit positive threshold after all law-dependent
coefficients have been fixed. -/
noncomputable def weightedLedgerAReal (a c d Gamma : ℝ) : ℝ :=
  a + 2 * c * d * Gamma

/-- Real-valued ordinary-potential coefficient for the fixed-law barrier. -/
noncomputable def weightedLedgerKReal (a c d Gamma : ℝ) : ℝ :=
  2 * weightedLedgerAReal a c d Gamma

/-- A concrete upper bound for the total graph potential once the offspring
laws, and hence all five ledger coefficients and the Green multiplier, have
been fixed.  The added `1`s make the formula positive without case splits
when one of the quadratic coefficients vanishes. -/
noncomputable def weightedLedgerEtaThreshold
    (a b c d e Gamma : ℝ) : ℝ :=
  min
    (weightedLedgerAReal a c d Gamma /
      (1 + b * weightedLedgerKReal a c d Gamma ^ 2))
    (d / (1 + e *
      (weightedLedgerKReal a c d Gamma + 2 * d * Gamma) ^ 2))

/-- The fixed-law total-potential threshold is genuinely positive for finite
nonnegative ledger coefficients with positive inhomogeneous budgets. -/
theorem weightedLedgerEtaThreshold_pos
    {a b c d e Gamma : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d)
    (he : 0 ≤ e) (hGamma : 0 ≤ Gamma) :
    0 < weightedLedgerEtaThreshold a b c d e Gamma := by
  have hA : 0 < weightedLedgerAReal a c d Gamma := by
    dsimp [weightedLedgerAReal]
    positivity
  have hB : 0 ≤ b * weightedLedgerKReal a c d Gamma ^ 2 := by
    positivity
  have hE : 0 ≤ e *
      (weightedLedgerKReal a c d Gamma + 2 * d * Gamma) ^ 2 := by
    positivity
  rw [weightedLedgerEtaThreshold]
  exact lt_min
    (div_pos hA (by positivity))
    (div_pos hd (by positivity))

/-- Every nonnegative total potential below the explicit fixed-law threshold
satisfies the two polynomial absorption inequalities used by
`weightedLedger_polynomial_closure`. -/
theorem weightedLedger_smallness_of_eta_le_threshold
    {a b c d e Gamma eta : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d)
    (he : 0 ≤ e) (hGamma : 0 ≤ Gamma)
    (heta0 : 0 ≤ eta)
    (heta : eta ≤ weightedLedgerEtaThreshold a b c d e Gamma) :
    b * weightedLedgerKReal a c d Gamma ^ 2 * eta ≤
        weightedLedgerAReal a c d Gamma ∧
      e * (weightedLedgerKReal a c d Gamma + 2 * d * Gamma) ^ 2 * eta ≤
        d := by
  let A := weightedLedgerAReal a c d Gamma
  let K := weightedLedgerKReal a c d Gamma
  let B := b * K ^ 2
  let E := e * (K + 2 * d * Gamma) ^ 2
  have hA : 0 < A := by
    dsimp [A, weightedLedgerAReal]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hleft : eta ≤ A / (1 + B) := by
    exact heta.trans (by
      rw [weightedLedgerEtaThreshold]
      exact min_le_left _ _)
  have hright : eta ≤ d / (1 + E) := by
    exact heta.trans (by
      rw [weightedLedgerEtaThreshold]
      exact min_le_right _ _)
  have hmulB : eta * (1 + B) ≤ A :=
    (le_div_iff₀ (by positivity : 0 < 1 + B)).mp hleft
  have hmulE : eta * (1 + E) ≤ d :=
    (le_div_iff₀ (by positivity : 0 < 1 + E)).mp hright
  change B * eta ≤ A ∧ E * eta ≤ d
  constructor <;> nlinarith

/-! ### Weighted domination by a killed renewal kernel -/

/-- Entrywise domination of a screen matrix by a scalar multiple of a
renewal matrix passes to their actions on every nonnegative vector. -/
lemma mulVec_le_scaled_mulVec {W R : ι → ι → ℝ≥0∞} {A : ℝ≥0∞}
    (hWR : ∀ i j, W i j ≤ A * R i j) (x : ι → ℝ≥0∞) (i : ι) :
    mulVec W x i ≤ A * mulVec R x i := by
  unfold mulVec
  calc
    (∑ j, W i j * x j) ≤ ∑ j, (A * R i j) * x j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_left (hWR i j) (x j)
    _ = A * ∑ j, R i j * x j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring

/-- The entrywise comparison `W ≤ A R` propagates to every path layer. -/
lemma mulVec_iterate_le_dominated {W R : ι → ι → ℝ≥0∞} {A : ℝ≥0∞}
    (hWR : ∀ i j, W i j ≤ A * R i j) :
    ∀ n i, (mulVec W)^[n] (fun _ => 1) i ≤
      A ^ n * (mulVec R)^[n] (fun _ => 1) i := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ih =>
      intro i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      calc
        mulVec W ((mulVec W)^[n] (fun _ => 1)) i ≤
            mulVec W (fun j => A ^ n *
              (mulVec R)^[n] (fun _ => 1) j) i := mulVec_mono ih i
        _ = A ^ n * mulVec W ((mulVec R)^[n] (fun _ => 1)) i := by
          exact mulVec_iterate_mul W (A ^ n)
            ((mulVec R)^[n] (fun _ => 1)) 1 i
        _ ≤ A ^ n * (A * mulVec R
            ((mulVec R)^[n] (fun _ => 1)) i) :=
          mul_le_mul_right
            (mulVec_le_scaled_mulVec hWR ((mulVec R)^[n] (fun _ => 1)) i)
            (A ^ n)
        _ = A ^ (n + 1) *
            mulVec R ((mulVec R)^[n] (fun _ => 1)) i := by
          rw [pow_succ']
          ring

/-- If `R` is substochastic then `W ≤ A R` gives the one-step row bound
`A` needed between renewal blocks. -/
lemma dominated_row_sum_le {W R : ι → ι → ℝ≥0∞} {A : ℝ≥0∞}
    (hWR : ∀ i j, W i j ≤ A * R i j)
    (hRrow : ∀ i, ∑ j, R i j ≤ 1) (i : ι) :
    ∑ j, W i j ≤ A := by
  calc
    (∑ j, W i j) ≤ ∑ j, A * R i j :=
      Finset.sum_le_sum fun j _ => hWR i j
    _ = A * ∑ j, R i j := by rw [Finset.mul_sum]
    _ ≤ A * 1 := mul_le_mul_right (hRrow i) A
    _ = A := mul_one A

/-- A killed renewal estimate for `R` becomes a block contraction for its
weighted screen kernel `W`.  This is the missing implication in the earlier
asynchronous proof; it explicitly requires domination of the *actual*
weighted matrix, not merely absorption of `R`. -/
lemma dominated_block_contraction {W R : ι → ι → ℝ≥0∞}
    {A q : ℝ≥0∞} {H : ℕ}
    (hWR : ∀ i j, W i j ≤ A * R i j)
    (hkill : ∀ i, (mulVec R)^[H] (fun _ => 1) i ≤ 1 - q) (i : ι) :
    (mulVec W)^[H] (fun _ => 1) i ≤ A ^ H * (1 - q) := by
  exact le_trans (mulVec_iterate_le_dominated hWR H i)
    (mul_le_mul_right (hkill i) (A ^ H))

/-- **Weighted-renewal Green bound.**  Suppose `R` is a substochastic
killed phase kernel, it loses mass at least `q` every `H` steps, and the
actual screen matrix is entrywise at most `A R`.  Then its path resolvent is
bounded by the geometric series with block ratio `A^H(1-q)`. -/
theorem dominated_resolvent_le {W R : ι → ι → ℝ≥0∞}
    {A q : ℝ≥0∞} {H : ℕ} (hH : 0 < H)
    (hWR : ∀ i j, W i j ≤ A * R i j)
    (hRrow : ∀ i, ∑ j, R i j ≤ 1)
    (hkill : ∀ i, (mulVec R)^[H] (fun _ => 1) i ≤ 1 - q) (i : ι) :
    infResolvent W (fun _ => 1) i ≤
      (1 - A ^ H * (1 - q))⁻¹ *
        (∑ j : Fin H, A ^ (j : ℕ)) := by
  letI : NeZero H := ⟨Nat.ne_of_gt hH⟩
  have hrow : ∀ i, ∑ j, W i j ≤ A :=
    dominated_row_sum_le hWR hRrow
  have hblock : ∀ i,
      (mulVec W)^[H] (fun _ => 1) i ≤ A ^ H * (1 - q) :=
    dominated_block_contraction hWR hkill
  have hpath : ∀ m i, infPow W m (fun _ => 1) i ≤
      (A ^ H * (1 - q)) ^ (m / H) * A ^ (m % H) := by
    intro m i
    rw [infPow_eq_iterate]
    exact mulVec_iterate_le_of_block hrow hblock m i
  calc
    infResolvent W (fun _ => 1) i ≤
        (∑' m : ℕ, (A ^ H * (1 - q)) ^ (m / H) *
          A ^ (m % H)) * 1 := infResolvent_le hpath i
    _ = (1 - A ^ H * (1 - q))⁻¹ *
        (∑ j : Fin H, A ^ (j : ℕ)) := by
      rw [mul_one, tsum_block_geometric]

/-- The screened matching recursion closes under the same weighted-renewal
comparison.  In applications `A = 1 + O(η)`; hence any fixed killing chance
`q > 0` wins once the label potential `η` is sufficiently small. -/
theorem screened_uniform_bound_dominated
    (W R : ι → ι → ℝ≥0∞) (A q : ℝ≥0∞) (H : ℕ) (hH : 0 < H)
    (hWR : ∀ i j, W i j ≤ A * R i j)
    (hRrow : ∀ i, ∑ j, R i j ≤ 1)
    (hkill : ∀ i, (mulVec R)^[H] (fun _ => 1) i ≤ 1 - q)
    (Kc η u Ξ : ℝ≥0∞)
    (hΞ : (1 - A ^ H * (1 - q))⁻¹ *
        (∑ j : Fin H, A ^ (j : ℕ)) * u ≤ Ξ)
    (Ψ : ℕ → ℝ≥0∞) (E : ℕ → ι → ℝ≥0∞)
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (hf : ∀ a a' b b', a ≤ a' → b ≤ b' → f a b ≤ f a' b')
    (hg : ∀ a a' b b', a ≤ a' → b ≤ b' → g a b ≤ g a' b')
    (hΨ0 : Ψ 0 ≤ Kc * η)
    (hE0 : ∀ i, E 0 i ≤ u)
    (hΨstep : ∀ h, Ψ (h + 1) ≤ f (Ψ h) (⨆ i, E h i))
    (hEstep : ∀ h i,
      E (h + 1) i ≤ g (Ψ h) (⨆ j, E h j) + mulVecInf W (E h) i)
    (hu : g (Kc * η) Ξ ≤ u)
    (hclose : f (Kc * η) Ξ ≤ Kc * η) :
    ∀ h, Ψ h ≤ Kc * η := by
  letI : NeZero H := ⟨Nat.ne_of_gt hH⟩
  have hrow : ∀ i, ∑ j, W i j ≤ A :=
    dominated_row_sum_le hWR hRrow
  have hblock : ∀ i,
      (mulVec W)^[H] (fun _ => 1) i ≤ A ^ H * (1 - q) :=
    dominated_block_contraction hWR hkill
  have hpath : ∀ m i, infPow W m (fun _ => 1) i ≤
      (A ^ H * (1 - q)) ^ (m / H) * A ^ (m % H) := by
    intro m i
    rw [infPow_eq_iterate]
    exact mulVec_iterate_le_of_block hrow hblock m i
  have hsum :
      (∑' m : ℕ, (A ^ H * (1 - q)) ^ (m / H) * A ^ (m % H)) * u ≤ Ξ := by
    rw [tsum_block_geometric]
    exact hΞ
  exact screened_uniform_bound_resolvent W
    (fun m => (A ^ H * (1 - q)) ^ (m / H) * A ^ (m % H))
    Kc η u Ξ hpath hsum Ψ E f g hf hg hΨ0 hE0 hΨstep hEstep hu hclose

end GraphMarkovMatching
