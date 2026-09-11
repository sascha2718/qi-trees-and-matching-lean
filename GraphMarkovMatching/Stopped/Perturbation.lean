/-
Finite-height continuity of arbitrary binary Markov tree laws under changes of their
root and child-pair laws. These estimates also apply at a parameter boundary where a
common-core presentation ceases to satisfy its positive-mass assumptions.
-/
import GraphMarkovMatching.Stopped.Unbounded

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

private lemma internal_count_succ (n : ℕ) :
    2 ^ (n + 1) - 1 = 1 + 2 * (2 ^ n - 1) := by
  have h : 0 < 2 ^ n := pow_pos (by omega) n
  rw [pow_succ]
  omega

/-- With a fixed root, at most `2^n - 1` child-pair draws affect height `n`. -/
theorem tvDist_muM_le {S : Type} (P Q : S → PMF (S × S)) (d : ℝ≥0∞)
    (hPQ : ∀ s, tvDist (P s) (Q s) ≤ d) :
    ∀ n s, tvDist (muM P s n) (muM Q s n) ≤ ((2 ^ n - 1 : ℕ) : ℝ≥0∞) * d := by
  intro n
  induction n with
  | zero => intro s; simp [muM, tvDist_self]
  | succ n ih =>
    intro s
    rw [muM_succ, muM_succ]
    calc tvDist ((pairMix P s n).map (branch s)) ((pairMix Q s n).map (branch s))
        ≤ tvDist (pairMix P s n) (pairMix Q s n) := tvDist_map_le _ _ _
      _ ≤ tvDist (P s) (Q s) + ∑' j, P s j *
          tvDist (prodPMF (muM P j.1 n) (muM P j.2 n))
            (prodPMF (muM Q j.1 n) (muM Q j.2 n)) := tvDist_bind_le _ _ _ _
      _ ≤ d + ∑' j, P s j * (2 * (((2 ^ n - 1 : ℕ) : ℝ≥0∞) * d)) := by
        refine add_le_add (hPQ s) (ENNReal.tsum_le_tsum fun j => ?_)
        refine mul_le_mul_right ?_ _
        exact (tvDist_prodPMF_le _ _ _ _).trans ((add_le_add (ih j.1) (ih j.2)).trans_eq
          (two_mul _).symm)
      _ = ((2 ^ (n + 1) - 1 : ℕ) : ℝ≥0∞) * d := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, internal_count_succ]
        push_cast
        ring

/-- An arbitrary root mixture adds its own total-variation error. -/
theorem tvDist_mix_muM_le {S : Type} (P Q : S → PMF (S × S)) (p q : PMF S)
    (d : ℝ≥0∞) (hPQ : ∀ s, tvDist (P s) (Q s) ≤ d) (n : ℕ) :
    tvDist (p.bind fun s => muM P s n) (q.bind fun s => muM Q s n)
      ≤ tvDist p q + ((2 ^ n - 1 : ℕ) : ℝ≥0∞) * d := by
  refine (tvDist_bind_le _ _ _ _).trans ?_
  calc tvDist p q + ∑' s, p s * tvDist (muM P s n) (muM Q s n)
      ≤ tvDist p q + ∑' s, p s * (((2 ^ n - 1 : ℕ) : ℝ≥0∞) * d) :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum fun s =>
          mul_le_mul_right (tvDist_muM_le P Q d hPQ n s) _)
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- If each sampled vertex law changes by at most `d`, a root draw and two possible
child draws per internal vertex give the address bound `2^(n+1) - 1`. -/
theorem tvDist_mix_muM_le_addresses {S : Type} (P Q : S → PMF (S × S)) (p q : PMF S)
    (d : ℝ≥0∞) (hpq : tvDist p q ≤ d) (hPQ : ∀ s, tvDist (P s) (Q s) ≤ 2 * d)
    (n : ℕ) :
    tvDist (p.bind fun s => muM P s n) (q.bind fun s => muM Q s n)
      ≤ ((2 ^ (n + 1) - 1 : ℕ) : ℝ≥0∞) * d := by
  refine (tvDist_mix_muM_le P Q p q (2 * d) hPQ n).trans ?_
  calc tvDist p q + ((2 ^ n - 1 : ℕ) : ℝ≥0∞) * (2 * d)
      ≤ d + ((2 ^ n - 1 : ℕ) : ℝ≥0∞) * (2 * d) := add_le_add hpq le_rfl
    _ = _ := by rw [internal_count_succ]; push_cast; ring

/-- Changing only the target law changes the matching failure by at most its total
variation; the source law and compatibility relation are arbitrary. -/
theorem failureD_le_add_tvDist_right {S : Type} (ρ p q : PMF S) (R : S → S → Prop) :
    failureD ρ p R ≤ failureD ρ q R + tvDist p q := by
  unfold failureD
  calc ∑' x, ρ x * qE p R x
      ≤ ∑' x, ρ x * (qE q R x + tvDist p q) := by
        refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
        rw [qE_eq_tsum_mul, qE_eq_tsum_mul]
        exact tsum_mul_le_add_tvDist p q _ fun y => badInd_le_one R x y
    _ = _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end GraphMarkovMatching.Stopped
