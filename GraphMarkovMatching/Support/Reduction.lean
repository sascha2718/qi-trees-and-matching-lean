/-
The reduction for `G_k`: the phase potentials

    Ψ(m,n) := Φ_α(fullMuK ν k m n, fullSimK R₀ k m n),

their one-step bounds (product phases via the product lemma twice, the swap
phase via the contraction lemma plus the product lemma for the root factor),
and the **abstract block invariance**: any profile `B : ℕ → ℝ≥0∞` that
dominates the one-site potentials and is closed under the two step maps
dominates `Ψ(m,n)` for every height.

The abstract form runs the downward induction with explicit
`(1+γ)`-prefactors: the block lemma is the instantiation of
`PsiK_le_of_invariant` at a chosen profile; the concrete instantiation with
clean constants is `ConcreteBlock.lean`.

Finally `meanBad_le_Phi` converts the potential bound into the failure
probability bound.
-/
import GraphMarkovMatching.Support.Tree
import GraphMarkovMatching.Support.Contraction

namespace GraphMarkovMatching.Support

open scoped ENNReal Classical

/-! ### The mean bad degree is below the potential -/

variable {X : Type*}

/-- `𝔼[q] ≤ Φ_α`: the failure probability (mean bad degree) is at most the
potential, since `q ≤ φ_α(q)` on the support. Needs `α ≥ 0`. -/
lemma meanBad_le_Phi {α : ℝ} (hα : 0 ≤ α) {μ : PMF X} {R : X → X → Prop}
    (hrefl : ∀ x, R x x) :
    ∑' x, μ x * qE μ R x ≤ Phi α μ R := by
  rw [Phi]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : μ x = 0
  · simp [hx]
  · have hq : μ x * qE μ R x = μ x * ENNReal.ofReal (q μ R x) := by
      rw [q, ENNReal.ofReal_toReal qE_ne_top]
    rw [hq]
    exact mul_q_le_summand hα (hrefl x) hx

/-! ### The phase potentials -/

universe u
variable {V : Type u}

/-- `Ψ(m,n)`: the potential of the phase-`m`, height-`n` relation. -/
noncomputable def PsiK (α : ℝ) (ν : ℕ → PMF V) (R₀ : V → V → Prop) (k m n : ℕ) : ℝ≥0∞ :=
  Phi α (fullMuK ν k m n) (fullSimK R₀ k m n)

@[simp] lemma PsiK_zero (α : ℝ) (ν : ℕ → PMF V) (R₀ : V → V → Prop) (k m : ℕ) :
    PsiK α ν R₀ k m 0 = Phi α (ν m) R₀ := by
  rw [PsiK, fullSimK_zero, fullMuK_zero]
  rfl

/-! ### One-step bounds -/

/-- **Product phase**: for `m+1`,

    Ψ(m+1, n+1) ≤ η_{m+1} + (1 + 2α η_{m+1}) (2 Ψ(m,n) + 2α Ψ(m,n)²),

by the product lemma applied to the two subtrees and then to the root factor. -/
lemma PsiK_succ_prod {α : ℝ} (hα : 1 ≤ α) (ν : ℕ → PMF V) (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (k m n : ℕ) :
    PsiK α ν R₀ k (m + 1) (n + 1)
      ≤ Phi α (ν (m + 1)) R₀
        + (1 + ENNReal.ofReal (2 * α) * Phi α (ν (m + 1)) R₀)
          * (2 * PsiK α ν R₀ k m n + ENNReal.ofReal (2 * α) * PsiK α ν R₀ k m n ^ 2) := by
  have hr : ∀ x, fullSimK R₀ k m n x x := fullSimK_refl R₀ hrefl k n m
  set S := fullSimK R₀ k m n with hS
  set M := fullMuK ν k m n with hM
  set P := PsiK α ν R₀ k m n with hP
  have hpair : Phi α (prodPMF M M) (ProdRel S S)
      ≤ 2 * P + ENNReal.ofReal (2 * α) * P ^ 2 := by
    calc Phi α (prodPMF M M) (ProdRel S S)
        ≤ Phi α M S + Phi α M S + ENNReal.ofReal (2 * α) * (Phi α M S * Phi α M S) :=
          Phi_prodPMF_le hα M M S S hr hr
      _ = 2 * P + ENNReal.ofReal (2 * α) * P ^ 2 := by rw [hP, PsiK, ← hS, ← hM]; ring
  rw [PsiK, fullSimK_succ_prod, fullMuK_succ_prod, ← hM, ← hS]
  calc Phi α (prodPMF (ν (m + 1)) (prodPMF M M)) (ProdRel R₀ (ProdRel S S))
      ≤ Phi α (ν (m + 1)) R₀ + Phi α (prodPMF M M) (ProdRel S S)
          + ENNReal.ofReal (2 * α)
            * (Phi α (ν (m + 1)) R₀ * Phi α (prodPMF M M) (ProdRel S S)) :=
        Phi_prodPMF_le hα (ν (m + 1)) (prodPMF M M) R₀ (ProdRel S S)
          hrefl (ProdRel_refl hr hr)
    _ ≤ Phi α (ν (m + 1)) R₀ + (2 * P + ENNReal.ofReal (2 * α) * P ^ 2)
          + ENNReal.ofReal (2 * α)
            * (Phi α (ν (m + 1)) R₀ * (2 * P + ENNReal.ofReal (2 * α) * P ^ 2)) := by
        gcongr
    _ = Phi α (ν (m + 1)) R₀
          + (1 + ENNReal.ofReal (2 * α) * Phi α (ν (m + 1)) R₀)
            * (2 * P + ENNReal.ofReal (2 * α) * P ^ 2) := by ring

/-- **Swap phase**: with the contraction constants
`Ar = 2L + 2(1+δ)K` and `Cr = 2L c_α + 5/2 + 2(1+δ⁻¹)α²`,

    Ψ(0, n+1) ≤ η₀ + (1 + 2α η₀) (Ar·Ψ(k-1,n) + Cr·Ψ(k-1,n)²). -/
lemma PsiK_succ_swap {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hK0 : 0 ≤ K)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (ν : ℕ → PMF V) (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a) (k n : ℕ) :
    PsiK α ν R₀ k 0 (n + 1)
      ≤ Phi α (ν 0) R₀
        + (1 + ENNReal.ofReal (2 * α) * Phi α (ν 0) R₀)
          * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * PsiK α ν R₀ k (k - 1) n
            + ENNReal.ofReal (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
              * PsiK α ν R₀ k (k - 1) n ^ 2) := by
  have hr : ∀ x, fullSimK R₀ k (k - 1) n x x := fullSimK_refl R₀ hrefl k n (k - 1)
  have hs : ∀ a b, fullSimK R₀ k (k - 1) n a b → fullSimK R₀ k (k - 1) n b a :=
    fullSimK_symm R₀ hsymm k n (k - 1)
  set S := fullSimK R₀ k (k - 1) n with hS
  set M := fullMuK ν k (k - 1) n with hM
  set P := PsiK α ν R₀ k (k - 1) n with hP
  have hpair : Phi α (prodPMF M M) (SquareRel S)
      ≤ ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * P
        + ENNReal.ofReal (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2) * P ^ 2 := by
    have h := Phi_square_le hα hδ hL0 hK0 hL hK M S hr hs
    rw [hP, PsiK, ← hS, ← hM]
    exact h
  rw [PsiK, fullSimK_succ_swap, fullMuK_succ_swap, ← hM, ← hS]
  calc Phi α (prodPMF (ν 0) (prodPMF M M)) (ProdRel R₀ (SquareRel S))
      ≤ Phi α (ν 0) R₀ + Phi α (prodPMF M M) (SquareRel S)
          + ENNReal.ofReal (2 * α)
            * (Phi α (ν 0) R₀ * Phi α (prodPMF M M) (SquareRel S)) :=
        Phi_prodPMF_le hα (ν 0) (prodPMF M M) R₀ (SquareRel S)
          hrefl (SquareRel_refl hr)
    _ ≤ Phi α (ν 0) R₀
          + (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * P
            + ENNReal.ofReal (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2) * P ^ 2)
          + ENNReal.ofReal (2 * α)
            * (Phi α (ν 0) R₀
              * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * P
                + ENNReal.ofReal (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
                  * P ^ 2)) := by gcongr
    _ = Phi α (ν 0) R₀
          + (1 + ENNReal.ofReal (2 * α) * Phi α (ν 0) R₀)
            * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * P
              + ENNReal.ofReal (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
                * P ^ 2) := by ring

/-! ### The abstract block invariance -/

/-- **Abstract block invariance.** Let `B : ℕ → ℝ≥0∞` be a profile such that
the one-site potentials sit below `B`, the product step map sends `B m` below
`B (m+1)` (for the phases `m+1 ≤ k-1` that occur), and the swap step map sends
`B (k-1)` below `B 0`. Then `Ψ(m,n) ≤ B m` for every height `n` and every
phase `m ≤ k-1`.

This is the block lemma with the constants abstracted away: the two
closure hypotheses are the product-step and swap-step estimates for the
chosen profile. -/
theorem PsiK_le_of_invariant {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hK0 : 0 ≤ K)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (ν : ℕ → PMF V) (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a) (k : ℕ)
    (B : ℕ → ℝ≥0∞)
    (hbase : ∀ m, m ≤ k - 1 → Phi α (ν m) R₀ ≤ B m)
    (hprod : ∀ m, m + 1 ≤ k - 1 → Phi α (ν (m + 1)) R₀
      + (1 + ENNReal.ofReal (2 * α) * Phi α (ν (m + 1)) R₀)
        * (2 * B m + ENNReal.ofReal (2 * α) * B m ^ 2) ≤ B (m + 1))
    (hswap : Phi α (ν 0) R₀
      + (1 + ENNReal.ofReal (2 * α) * Phi α (ν 0) R₀)
        * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B (k - 1)
          + ENNReal.ofReal (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
            * B (k - 1) ^ 2) ≤ B 0) :
    ∀ n m, m ≤ k - 1 → PsiK α ν R₀ k m n ≤ B m := by
  intro n
  induction n with
  | zero => intro m hm; rw [PsiK_zero]; exact hbase m hm
  | succ n ih =>
      intro m hm
      match m with
      | 0 =>
          calc PsiK α ν R₀ k 0 (n + 1)
              ≤ Phi α (ν 0) R₀
                  + (1 + ENNReal.ofReal (2 * α) * Phi α (ν 0) R₀)
                    * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * PsiK α ν R₀ k (k - 1) n
                      + ENNReal.ofReal (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
                        * PsiK α ν R₀ k (k - 1) n ^ 2) :=
                PsiK_succ_swap hα hδ hL0 hK0 hL hK ν R₀ hrefl hsymm k n
            _ ≤ Phi α (ν 0) R₀
                  + (1 + ENNReal.ofReal (2 * α) * Phi α (ν 0) R₀)
                    * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B (k - 1)
                      + ENNReal.ofReal (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
                        * B (k - 1) ^ 2) := by
                gcongr <;> exact ih (k - 1) le_rfl
            _ ≤ B 0 := hswap
      | m + 1 =>
          calc PsiK α ν R₀ k (m + 1) (n + 1)
              ≤ Phi α (ν (m + 1)) R₀
                  + (1 + ENNReal.ofReal (2 * α) * Phi α (ν (m + 1)) R₀)
                    * (2 * PsiK α ν R₀ k m n
                      + ENNReal.ofReal (2 * α) * PsiK α ν R₀ k m n ^ 2) :=
                PsiK_succ_prod hα ν R₀ hrefl k m n
            _ ≤ Phi α (ν (m + 1)) R₀
                  + (1 + ENNReal.ofReal (2 * α) * Phi α (ν (m + 1)) R₀)
                    * (2 * B m + ENNReal.ofReal (2 * α) * B m ^ 2) := by
                gcongr <;> exact ih m (le_trans (Nat.le_succ m) hm)
            _ ≤ B (m + 1) := hprod m hm

/-- The failure-probability form: under the invariance hypotheses, two
independent phase-labelled trees of any height `n`, rooted at phase `m ≤ k-1`,
fail to admit a matching in `AutK k m n` with probability at most `B m`. -/
theorem matching_failure_le {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hK0 : 0 ≤ K)
    (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (ν : ℕ → PMF V) (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a) (k : ℕ)
    (B : ℕ → ℝ≥0∞)
    (hbase : ∀ m, m ≤ k - 1 → Phi α (ν m) R₀ ≤ B m)
    (hprod : ∀ m, m + 1 ≤ k - 1 → Phi α (ν (m + 1)) R₀
      + (1 + ENNReal.ofReal (2 * α) * Phi α (ν (m + 1)) R₀)
        * (2 * B m + ENNReal.ofReal (2 * α) * B m ^ 2) ≤ B (m + 1))
    (hswap : Phi α (ν 0) R₀
      + (1 + ENNReal.ofReal (2 * α) * Phi α (ν 0) R₀)
        * (ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * B (k - 1)
          + ENNReal.ofReal (2 * L * chordConst α + 5 / 2 + 2 * (1 + δ⁻¹) * α ^ 2)
            * B (k - 1) ^ 2) ≤ B 0)
    (n m : ℕ) (hm : m ≤ k - 1) :
    ∑' x, fullMuK ν k m n x * qE (fullMuK ν k m n) (fullSimK R₀ k m n) x ≤ B m :=
  le_trans (meanBad_le_Phi (by linarith) (fullSimK_refl R₀ hrefl k n m))
    (PsiK_le_of_invariant hα hδ hL0 hK0 hL hK ν R₀ hrefl hsymm k B hbase hprod hswap n m hm)

end GraphMarkovMatching.Support
