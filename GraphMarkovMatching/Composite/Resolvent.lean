/-
Countable nonnegative kernels and the screened closure through a finite
invariant.

`Closure/Block.lean` draws the screen invariant of a finite grammar from
a finite nilpotent matrix.  The closure theorems here need neither
finiteness of the index nor a matrix presentation: a countable kernel
acts through `mulVecInf`, its iterates `infPow` and its resolvent
`infResolvent` are `tsum`s, and any finite invariant profile closes the
recursion.  `Composite/RareMatrix.lean` consumes the resolvent form for the
rare two-law perturbations.

* `mulVecInf`, `infPow`, `infResolvent`: the countable kernel calculus,
  with monotonicity, the `tsum` exchange, scalar homogeneity and the
  fixed-point identity `u + N F = F` of the resolvent;
* `screened_uniform_bound_functional`: closure through a positive
  functional finite on the invariant, the seed profile keeping its
  offspring weights;
* `screened_uniform_bound_invariant_state`, `screened_uniform_bound_invariant`:
  closure through a finite invariant of a monotone screen operator;
* `screened_uniform_bound_resolvent`, `screened_uniform_bound_resolvent_with_debt`:
  the invariant taken as the resolvent `∑_m N^m (u·1)`, the second form
  exposing the exceptional-debt conclusion of the weighted Hall ledger.
-/
import GraphMarkovMatching.Closure.Block

namespace GraphMarkovMatching

open scoped ENNReal

variable {ι : Type}

/-! ### Countable nonnegative kernels -/

/-- Matrix-vector multiplication for a kernel on an arbitrary countable
index.  Unlike `mulVec`, the row is a `tsum`, not a finite sum. -/
noncomputable def mulVecInf (N : ι → ι → ℝ≥0∞) (x : ι → ℝ≥0∞) (i : ι) : ℝ≥0∞ :=
  ∑' j, N i j * x j

/-- Iteration of a countable kernel. -/
noncomputable def infPow (N : ι → ι → ℝ≥0∞) : ℕ → (ι → ℝ≥0∞) → ι → ℝ≥0∞
  | 0, x => x
  | m + 1, x => mulVecInf N (infPow N m x)

/-- The coordinatewise path resolvent. -/
noncomputable def infResolvent (N : ι → ι → ℝ≥0∞) (u : ι → ℝ≥0∞) (i : ι) :
    ℝ≥0∞ :=
  ∑' m, infPow N m u i

lemma mulVecInf_mono {N : ι → ι → ℝ≥0∞} {x y : ι → ℝ≥0∞}
    (hxy : ∀ i, x i ≤ y i) (i : ι) :
    mulVecInf N x i ≤ mulVecInf N y i :=
  ENNReal.tsum_le_tsum fun j => mul_le_mul_right (hxy j) _

/-- A nonnegative countable kernel commutes with a countable sum of
vectors. -/
lemma mulVecInf_tsum (N : ι → ι → ℝ≥0∞) (x : ℕ → ι → ℝ≥0∞) (i : ι) :
    mulVecInf N (fun j => ∑' m, x m j) i = ∑' m, mulVecInf N (x m) i := by
  rw [mulVecInf]
  calc
    (∑' j, N i j * ∑' m, x m j)
        = ∑' j, ∑' m, N i j * x m j := by
            refine tsum_congr fun j => ?_
            exact (ENNReal.tsum_mul_left).symm
    _ = ∑' m, ∑' j, N i j * x m j := ENNReal.tsum_comm
    _ = ∑' m, mulVecInf N (x m) i := by rfl

/-- Scalar multiplication passes through a countable kernel. -/
lemma mulVecInf_mul (N : ι → ι → ℝ≥0∞) (a : ℝ≥0∞) (x : ι → ℝ≥0∞) (i : ι) :
    mulVecInf N (fun j => a * x j) i = a * mulVecInf N x i := by
  rw [mulVecInf, mulVecInf]
  calc
    (∑' j, N i j * (a * x j)) = ∑' j, a * (N i j * x j) := by
      refine tsum_congr fun j => ?_
      ring
    _ = a * ∑' j, N i j * x j := ENNReal.tsum_mul_left

lemma infPow_mul (N : ι → ι → ℝ≥0∞) (a : ℝ≥0∞) (x : ι → ℝ≥0∞) :
    ∀ m i, infPow N m (fun j => a * x j) i = a * infPow N m x i := by
  intro m
  induction m with
  | zero => exact fun _ => rfl
  | succ m ih =>
      intro i
      simp only [infPow]
      rw [show infPow N m (fun j => a * x j) =
          fun j => a * infPow N m x j from funext ih]
      exact mulVecInf_mul N a _ i

/-- The path resolvent absorbs one more application of the kernel. -/
lemma infResolvent_fixed (N : ι → ι → ℝ≥0∞) (u : ι → ℝ≥0∞) (i : ι) :
    u i + mulVecInf N (infResolvent N u) i = infResolvent N u i := by
  rw [infResolvent, tsum_eq_zero_add' ENNReal.summable]
  congr 1
  change mulVecInf N (fun j => ∑' m, infPow N m u j) i = _
  rw [mulVecInf_tsum]
  exact tsum_congr fun m => rfl

/-- A scalar majorant for all path layers bounds the resolvent. -/
lemma infResolvent_le {N : ι → ι → ℝ≥0∞} {a : ℕ → ℝ≥0∞} {u : ℝ≥0∞}
    (hpath : ∀ m i, infPow N m (fun _ => 1) i ≤ a m) (i : ι) :
    infResolvent N (fun _ => u) i ≤ (∑' m, a m) * u := by
  rw [infResolvent, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun m => ?_
  rw [show (fun _ : ι => u) = fun j => u * (fun _ : ι => 1) j by
    funext j; rw [mul_one], infPow_mul]
  rw [mul_comm u]
  exact mul_le_mul_left (hpath m i) u

/-! ### Closure in a positive functional -/

/-- **Countable screened closure in a positive functional.**

This is the closure interface required by an unbounded offspring
support.  Individual screen coordinates need not be uniformly bounded:
a coordinate exposing a very large counter may have a large resolvent.
Only the positive functional `Λ` that occurs in the ordinary rows is
required to be finite on the invariant `F`.  The seed profile `b`
retains the offspring weights before any bound is taken.

The earlier supremum-form theorem below remains useful for finite
support, but is intentionally not used for the exponential-tail
extension. -/
theorem screened_uniform_bound_functional
    (op : (ι → ℝ≥0∞) → ι → ℝ≥0∞)
    (hop : ∀ {x y : ι → ℝ≥0∞}, (∀ i, x i ≤ y i) → ∀ i, op x i ≤ op y i)
    (Λ : (ι → ℝ≥0∞) → ℝ≥0∞)
    (hΛ : ∀ {x y : ι → ℝ≥0∞}, (∀ i, x i ≤ y i) → Λ x ≤ Λ y)
    (Ψ : ℕ → ℝ≥0∞) (E : ℕ → ι → ℝ≥0∞)
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (hf : ∀ a a' b b', a ≤ a' → b ≤ b' → f a b ≤ f a' b')
    (hg : ∀ a a' b b', a ≤ a' → b ≤ b' → g a b ≤ g a' b')
    (Kc η Ξ : ℝ≥0∞) (seed F : ι → ℝ≥0∞)
    (hF : ∀ i, g (Kc * η) Ξ * seed i + op F i ≤ F i)
    (hFΞ : Λ F ≤ Ξ)
    (hΨ0 : Ψ 0 ≤ Kc * η)
    (hE0 : ∀ i, E 0 i ≤ F i)
    (hΨstep : ∀ h, Ψ (h + 1) ≤ f (Ψ h) (Λ (E h)))
    (hEstep : ∀ h i,
      E (h + 1) i ≤ g (Ψ h) (Λ (E h)) * seed i + op (E h) i)
    (hclose : f (Kc * η) Ξ ≤ Kc * η) :
    ∀ h, Ψ h ≤ Kc * η := by
  have main : ∀ h, Ψ h ≤ Kc * η ∧ ∀ i, E h i ≤ F i := by
    intro h
    induction h with
    | zero => exact ⟨hΨ0, hE0⟩
    | succ h ih =>
        obtain ⟨ihΨ, ihE⟩ := ih
        have hfun : Λ (E h) ≤ Ξ := le_trans (hΛ ihE) hFΞ
        constructor
        · exact le_trans (hΨstep h)
            (le_trans (hf _ _ _ _ ihΨ hfun) hclose)
        · intro i
          refine le_trans (hEstep h i) ?_
          exact le_trans
            (add_le_add
              (mul_le_mul_left (hg _ _ _ _ ihΨ hfun) (seed i))
              (hop ihE i))
            (hF i)
  exact fun h => (main h).1

/-- **Screened closure from a supplied invariant, with an arbitrary index.**

`op` is the positive linear screen operator at the level of the argument; the
proof only needs its monotonicity.  If `F` absorbs the constant screen input
`u`, bounds every initial screen, and has supremum at most `Ξ`, then the usual
two closure inequalities keep the ordinary coordinate below `Kc * η` and all
screen coordinates below `F` at every height.

Unlike `screened_uniform_bound_mono`, the index need not be finite and no
nilpotence exponent is mentioned.  In the finite application one may take
`F = nilSum N r u`.  For an unbounded support this supremum interface is
generally too strong; the functional version above is the relevant abstract
replacement. -/
theorem screened_uniform_bound_invariant_state
    (op : (ι → ℝ≥0∞) → ι → ℝ≥0∞)
    (hop : ∀ {x y : ι → ℝ≥0∞}, (∀ i, x i ≤ y i) → ∀ i, op x i ≤ op y i)
    (Ψ : ℕ → ℝ≥0∞) (E : ℕ → ι → ℝ≥0∞)
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (hf : ∀ a a' b b', a ≤ a' → b ≤ b' → f a b ≤ f a' b')
    (hg : ∀ a a' b b', a ≤ a' → b ≤ b' → g a b ≤ g a' b')
    (Kc η u Ξ : ℝ≥0∞) (F : ι → ℝ≥0∞)
    (hF : ∀ i, u + op F i ≤ F i)
    (hFΞ : ∀ i, F i ≤ Ξ)
    (hΨ0 : Ψ 0 ≤ Kc * η)
    (hE0 : ∀ i, E 0 i ≤ F i)
    (hΨstep : ∀ h, Ψ (h + 1) ≤ f (Ψ h) (⨆ i, E h i))
    (hEstep : ∀ h i,
      E (h + 1) i ≤ g (Ψ h) (⨆ j, E h j) + op (E h) i)
    (hu : g (Kc * η) Ξ ≤ u)
    (hclose : f (Kc * η) Ξ ≤ Kc * η) :
    ∀ h, Ψ h ≤ Kc * η ∧ ∀ i, E h i ≤ F i := by
  intro h
  induction h with
  | zero => exact ⟨hΨ0, hE0⟩
  | succ h ih =>
      obtain ⟨ihΨ, ihE⟩ := ih
      have hsup : (⨆ i, E h i) ≤ Ξ :=
        iSup_le fun i => le_trans (ihE i) (hFΞ i)
      constructor
      · exact le_trans (hΨstep h)
          (le_trans (hf _ _ _ _ ihΨ hsup) hclose)
      · intro i
        refine le_trans (hEstep h i) ?_
        exact le_trans
          (add_le_add (le_trans (hg _ _ _ _ ihΨ hsup) hu)
            (hop ihE i))
          (hF i)

theorem screened_uniform_bound_invariant
    (op : (ι → ℝ≥0∞) → ι → ℝ≥0∞)
    (hop : ∀ {x y : ι → ℝ≥0∞}, (∀ i, x i ≤ y i) → ∀ i, op x i ≤ op y i)
    (Ψ : ℕ → ℝ≥0∞) (E : ℕ → ι → ℝ≥0∞)
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (hf : ∀ a a' b b', a ≤ a' → b ≤ b' → f a b ≤ f a' b')
    (hg : ∀ a a' b b', a ≤ a' → b ≤ b' → g a b ≤ g a' b')
    (Kc η u Ξ : ℝ≥0∞) (F : ι → ℝ≥0∞)
    (hF : ∀ i, u + op F i ≤ F i)
    (hFΞ : ∀ i, F i ≤ Ξ)
    (hΨ0 : Ψ 0 ≤ Kc * η)
    (hE0 : ∀ i, E 0 i ≤ F i)
    (hΨstep : ∀ h, Ψ (h + 1) ≤ f (Ψ h) (⨆ i, E h i))
    (hEstep : ∀ h i,
      E (h + 1) i ≤ g (Ψ h) (⨆ j, E h j) + op (E h) i)
    (hu : g (Kc * η) Ξ ≤ u)
    (hclose : f (Kc * η) Ξ ≤ Kc * η) :
    ∀ h, Ψ h ≤ Kc * η := by
  exact fun h => (screened_uniform_bound_invariant_state op hop Ψ E f g hf hg
    Kc η u Ξ F hF hFΞ hΨ0 hE0 hΨstep hEstep hu hclose h).1

/-- **Resolvent form of the screened closure.**

This packages the legitimate use of a Green vector in the matching
recursion.  The kernel occurring in `hEstep` must be the same kernel `N`
whose path powers are bounded by `a`; a tail estimate for a different
unweighted Markov kernel is not enough.

The invariant is the resolvent

`F = sum_m N^m (u * 1)`.

The hypothesis `hpath` and the scalar summability bound `hsum` give
`F <= Xi`, while `infResolvent_fixed` gives `u + N F = F`. -/
theorem screened_uniform_bound_resolvent
    (N : ι → ι → ℝ≥0∞)
    (a : ℕ → ℝ≥0∞)
    (Kc η u Ξ : ℝ≥0∞)
    (hpath : ∀ m i, infPow N m (fun _ => 1) i ≤ a m)
    (hsum : (∑' m, a m) * u ≤ Ξ)
    (Ψ : ℕ → ℝ≥0∞) (E : ℕ → ι → ℝ≥0∞)
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (hf : ∀ a a' b b', a ≤ a' → b ≤ b' → f a b ≤ f a' b')
    (hg : ∀ a a' b b', a ≤ a' → b ≤ b' → g a b ≤ g a' b')
    (hΨ0 : Ψ 0 ≤ Kc * η)
    (hE0 : ∀ i, E 0 i ≤ u)
    (hΨstep : ∀ h, Ψ (h + 1) ≤ f (Ψ h) (⨆ i, E h i))
    (hEstep : ∀ h i,
      E (h + 1) i ≤ g (Ψ h) (⨆ j, E h j) + mulVecInf N (E h) i)
    (hu : g (Kc * η) Ξ ≤ u)
    (hclose : f (Kc * η) Ξ ≤ Kc * η) :
    ∀ h, Ψ h ≤ Kc * η := by
  let F : ι → ℝ≥0∞ := infResolvent N (fun _ => u)
  have hF : ∀ i, u + mulVecInf N F i ≤ F i := by
    intro i
    exact le_of_eq (infResolvent_fixed N (fun _ => u) i)
  have hFΞ : ∀ i, F i ≤ Ξ := by
    intro i
    exact le_trans (infResolvent_le hpath i) hsum
  have hE0F : ∀ i, E 0 i ≤ F i := by
    intro i
    refine le_trans (hE0 i) ?_
    exact le_trans (show u ≤ infPow N 0 (fun _ => u) i from le_rfl)
      (ENNReal.le_tsum 0)
  exact screened_uniform_bound_invariant
    (mulVecInf N) (fun {_ _} hxy i => mulVecInf_mono hxy i)
    Ψ E f g hf hg Kc η u Ξ F hF hFΞ hΨ0 hE0F hΨstep hEstep hu hclose

/-- Resolvent closure with the exceptional-debt conclusion exposed.  This
is the exact joint conclusion used in the prose weighted Hall-ledger
theorem. -/
theorem screened_uniform_bound_resolvent_with_debt
    (N : ι → ι → ℝ≥0∞)
    (a : ℕ → ℝ≥0∞)
    (Kc η u Ξ : ℝ≥0∞)
    (hpath : ∀ m i, infPow N m (fun _ => 1) i ≤ a m)
    (hsum : (∑' m, a m) * u ≤ Ξ)
    (Ψ : ℕ → ℝ≥0∞) (E : ℕ → ι → ℝ≥0∞)
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (hf : ∀ a a' b b', a ≤ a' → b ≤ b' → f a b ≤ f a' b')
    (hg : ∀ a a' b b', a ≤ a' → b ≤ b' → g a b ≤ g a' b')
    (hΨ0 : Ψ 0 ≤ Kc * η)
    (hE0 : ∀ i, E 0 i ≤ u)
    (hΨstep : ∀ h, Ψ (h + 1) ≤ f (Ψ h) (⨆ i, E h i))
    (hEstep : ∀ h i,
      E (h + 1) i ≤ g (Ψ h) (⨆ j, E h j) + mulVecInf N (E h) i)
    (hu : g (Kc * η) Ξ ≤ u)
    (hclose : f (Kc * η) Ξ ≤ Kc * η) :
    ∀ h, Ψ h ≤ Kc * η ∧ ∀ i, E h i ≤ Ξ := by
  let F : ι → ℝ≥0∞ := infResolvent N (fun _ => u)
  have hF : ∀ i, u + mulVecInf N F i ≤ F i := by
    intro i
    exact le_of_eq (infResolvent_fixed N (fun _ => u) i)
  have hFΞ : ∀ i, F i ≤ Ξ := by
    intro i
    exact le_trans (infResolvent_le hpath i) hsum
  have hE0F : ∀ i, E 0 i ≤ F i := by
    intro i
    refine le_trans (hE0 i) ?_
    exact le_trans (show u ≤ infPow N 0 (fun _ => u) i from le_rfl)
      (ENNReal.le_tsum 0)
  intro h
  obtain ⟨hΨ, hE⟩ := screened_uniform_bound_invariant_state
    (mulVecInf N) (fun {_ _} hxy i => mulVecInf_mono hxy i)
    Ψ E f g hf hg Kc η u Ξ F hF hFΞ hΨ0 hE0F hΨstep hEstep hu hclose h
  exact ⟨hΨ, fun i => le_trans (hE i) (hFΞ i)⟩

end GraphMarkovMatching
