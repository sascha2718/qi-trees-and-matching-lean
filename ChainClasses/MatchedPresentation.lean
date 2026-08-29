/-
`thm:matched-presentation` of `matching_classes_general.tex`, the law level: the
matched blob presentations of two chain-regime reduced skeletons, as explicit
mass functions, with the support, floor, bulk and window clauses.

The presentation rule of the prose reads a bounded number of random inputs: the
real shifts revealed by descents, the simulated shifts of the other law, a
free-exploration branch of mass `δ`, per-descent failures of probability
`θ₁^{D²}`, and stopping coins.  Its stopped total is the value of a finite
probabilistic automaton, and the presented arity law is one plus the
automaton's stop law.  This file certifies the clauses of
`thm:matched-presentation` on that automaton, laws entering as real mass
functions on finite supports in the convention of `ChainRegime`.  The product
clause over the presented skeleton is the probabilistic clause of
`thm:blob-law` and stays with the almost sure framework.

* `ideal`, `ideal_sum_le_one`, `ideal_sum_eq_one`: the idealised coupled
  exploration, the lagging-side walk of `thm:common-renewal` stopped at
  agreement at or below `L` or at first passage past `L`.
* `ideal_bulk_symm`: **the idealised bulk laws agree**: the stop law at a bulk
  value is symmetric under exchanging the two laws, which is the equality
  behind `thm:matched-presentation`\labelcref{it:matched-bulk}.
* `alive`, `alive_word_le`, `alive_le_pow`, `ideal_window_le_alive`: **the
  window mass**.  A stop past `L` needs many increments, each block of `H`
  increments closes the lag with probability at least `q = p^H` through the
  correction words of `thm:common-renewal` read by `renewalWordRun`, and the
  survival probability decays geometrically.
-/
import ChainClasses.RenewalAlignment

namespace ChainClasses

namespace Matched

open Finset

/-! ### The idealised coupled exploration

The state is the pair of accumulated totals.  The lagging side moves, the walk
stops at agreement at or below `L` and at first passage past `L`, and nowhere
else.  Fuel makes the recursion structural, and every quantitative lemma holds
at every fuel or at large fuel. -/

section Ideal

variable (A B : Finset ℕ) (P P' : ℕ → ℝ) (L : ℕ)

/-- The stop law of the idealised coupled exploration from the totals `(r, t)`:
the mass with which the walk stops at the total `s` within `F` steps. -/
noncomputable def ideal : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, _, _, _ => 0
  | F + 1, r, t, s =>
      if L < r ∨ r = t then (if s = r then 1 else 0)
      else if r < t then ∑ x ∈ A, P x * ideal F (r + x) t s
      else ∑ y ∈ B, P' y * ideal F r (t + y) s

/-- The survival probability of the idealised walk: the mass of not having
stopped within `m` steps. -/
noncomputable def alive : ℕ → ℕ → ℕ → ℝ
  | 0, r, t => if L < r ∨ r = t then 0 else 1
  | m + 1, r, t =>
      if L < r ∨ r = t then 0
      else if r < t then ∑ x ∈ A, P x * alive m (r + x) t
      else ∑ y ∈ B, P' y * alive m r (t + y)

variable {A B P P' L}

lemma ideal_stop {F r t s : ℕ} (h : L < r ∨ r = t) :
    ideal A B P P' L (F + 1) r t s = if s = r then 1 else 0 := by
  rw [ideal, if_pos h]

lemma ideal_left {F r t s : ℕ} (h : ¬ (L < r ∨ r = t)) (hrt : r < t) :
    ideal A B P P' L (F + 1) r t s = ∑ x ∈ A, P x * ideal A B P P' L F (r + x) t s := by
  rw [ideal, if_neg h, if_pos hrt]

lemma ideal_right {F r t s : ℕ} (h : ¬ (L < r ∨ r = t)) (hrt : ¬ r < t) :
    ideal A B P P' L (F + 1) r t s = ∑ y ∈ B, P' y * ideal A B P P' L F r (t + y) s := by
  rw [ideal, if_neg h, if_neg hrt]

lemma ideal_nonneg (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b) :
    ∀ F r t s, 0 ≤ ideal A B P P' L F r t s := by
  intro F
  induction F with
  | zero => intro r t s; simp [ideal]
  | succ F ih =>
      intro r t s
      rw [ideal]
      split
      · positivity
      · split
        · exact Finset.sum_nonneg fun x hx ↦ mul_nonneg (hP x hx) (ih _ _ _)
        · exact Finset.sum_nonneg fun y hy ↦ mul_nonneg (hP' y hy) (ih _ _ _)

/-- The mass of any set of stop values is at most one. -/
lemma ideal_sum_le_one (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1) :
    ∀ (F r t : ℕ) (S : Finset ℕ), ∑ s ∈ S, ideal A B P P' L F r t s ≤ 1 := by
  intro F
  induction F with
  | zero => intro r t S; simp [ideal]
  | succ F ih =>
      intro r t S
      by_cases h : L < r ∨ r = t
      · calc ∑ s ∈ S, ideal A B P P' L (F + 1) r t s
            = ∑ s ∈ S, if s = r then (1 : ℝ) else 0 :=
              Finset.sum_congr rfl fun s _ ↦ ideal_stop h
          _ ≤ 1 := by
              rw [Finset.sum_ite_eq' S r fun _ ↦ (1 : ℝ)]
              split <;> norm_num
      · by_cases hrt : r < t
        · calc ∑ s ∈ S, ideal A B P P' L (F + 1) r t s
              = ∑ x ∈ A, P x * ∑ s ∈ S, ideal A B P P' L F (r + x) t s := by
                simp only [ideal_left h hrt]
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum ..).symm
            _ ≤ ∑ x ∈ A, P x * 1 :=
                Finset.sum_le_sum fun x hx ↦
                  mul_le_mul_of_nonneg_left (ih _ _ _) (hP x hx)
            _ = 1 := by rw [← Finset.sum_mul, hP1, one_mul]
        · calc ∑ s ∈ S, ideal A B P P' L (F + 1) r t s
              = ∑ y ∈ B, P' y * ∑ s ∈ S, ideal A B P P' L F r (t + y) s := by
                simp only [ideal_right h hrt]
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun y _ ↦ (Finset.mul_sum ..).symm
            _ ≤ ∑ y ∈ B, P' y * 1 :=
                Finset.sum_le_sum fun y hy ↦
                  mul_le_mul_of_nonneg_left (ih _ _ _) (hP' y hy)
            _ = 1 := by rw [← Finset.sum_mul, hP'1, one_mul]

/-- With enough fuel the walk has stopped: the stop law is a law.  The stop
values lie among `0, …, max r (L + MA)`, and each nonterminal step increases
`r + t`, which is bounded along the run. -/
lemma ideal_sum_eq_one {MA MB : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) (hMB : ∀ b ∈ B, b ≤ MB)
    (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1) :
    ∀ F r t, r ≤ L + MA → t ≤ L + MB → 2 * L + MA + MB + 1 ≤ F + r + t →
      ∑ s ∈ Finset.range (L + MA + 1), ideal A B P P' L F r t s = 1 := by
  intro F
  induction F with
  | zero =>
      intro r t hr ht hF
      omega
  | succ F ih =>
      intro r t hr ht hF
      by_cases h : L < r ∨ r = t
      · calc ∑ s ∈ Finset.range (L + MA + 1), ideal A B P P' L (F + 1) r t s
            = ∑ s ∈ Finset.range (L + MA + 1), if s = r then (1 : ℝ) else 0 :=
              Finset.sum_congr rfl fun s _ ↦ ideal_stop h
          _ = 1 := by
              rw [Finset.sum_ite_eq' (Finset.range (L + MA + 1)) r fun _ ↦ (1 : ℝ),
                if_pos (Finset.mem_range.mpr (by omega))]
      · have hrL : ¬ L < r := fun hc ↦ h (Or.inl hc)
        by_cases hrt : r < t
        · calc ∑ s ∈ Finset.range (L + MA + 1), ideal A B P P' L (F + 1) r t s
              = ∑ x ∈ A, P x * ∑ s ∈ Finset.range (L + MA + 1),
                  ideal A B P P' L F (r + x) t s := by
                simp only [ideal_left h hrt]
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum ..).symm
            _ = ∑ x ∈ A, P x * 1 := by
                refine Finset.sum_congr rfl fun x hx ↦ ?_
                rw [ih (r + x) t (by have := hMA x hx; omega) ht
                  (by have := hA0 x hx; omega)]
            _ = 1 := by rw [← Finset.sum_mul, hP1, one_mul]
        · have htr : t < r := by omega
          calc ∑ s ∈ Finset.range (L + MA + 1), ideal A B P P' L (F + 1) r t s
              = ∑ y ∈ B, P' y * ∑ s ∈ Finset.range (L + MA + 1),
                  ideal A B P P' L F r (t + y) s := by
                simp only [ideal_right h hrt]
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun y _ ↦ (Finset.mul_sum ..).symm
            _ = ∑ y ∈ B, P' y * 1 := by
                refine Finset.sum_congr rfl fun y hy ↦ ?_
                rw [ih r (t + y) hr (by have := hMB y hy; omega)
                  (by have := hB0 y hy; omega)]
            _ = 1 := by rw [← Finset.sum_mul, hP'1, one_mul]

/-- The stop law charges only totals in the closure of the support: the real
total starts there and every real increment stays there. -/
lemma ideal_eq_zero_of_notMem {s : ℕ} (F : ℕ) :
    ∀ r t, r ∈ AddSubmonoid.closure (A : Set ℕ) →
      s ∉ AddSubmonoid.closure (A : Set ℕ) → ideal A B P P' L F r t s = 0 := by
  induction F with
  | zero => intro r t _ _; simp [ideal]
  | succ F ih =>
      intro r t hr hs
      by_cases h : L < r ∨ r = t
      · rw [ideal_stop h, if_neg (fun hsr ↦ hs (by rw [hsr]; exact hr))]
      · by_cases hrt : r < t
        · rw [ideal_left h hrt]
          refine Finset.sum_eq_zero fun x hx ↦ ?_
          rw [ih (r + x) t (AddSubmonoid.add_mem _ hr
            (AddSubmonoid.subset_closure hx)) hs, mul_zero]
        · rw [ideal_right h hrt]
          refine Finset.sum_eq_zero fun y _ ↦ ?_
          rw [ih r (t + y) hr hs, mul_zero]

/-- The stop law charges only totals at most `max r (L + MA)`. -/
lemma ideal_eq_zero_of_gt {MA : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) {s : ℕ} (F : ℕ) :
    ∀ r t, r ≤ L + MA → L + MA < s → ideal A B P P' L F r t s = 0 := by
  induction F with
  | zero => intro r t _ _; simp [ideal]
  | succ F ih =>
      intro r t hr hs
      by_cases h : L < r ∨ r = t
      · rw [ideal_stop h, if_neg (by omega)]
      · have hrL : ¬ L < r := fun hc ↦ h (Or.inl hc)
        by_cases hrt : r < t
        · rw [ideal_left h hrt]
          refine Finset.sum_eq_zero fun x hx ↦ ?_
          rw [ih (r + x) t (by have := hMA x hx; omega) hs, mul_zero]
        · rw [ideal_right h hrt]
          refine Finset.sum_eq_zero fun y _ ↦ ?_
          rw [ih r (t + y) hr hs, mul_zero]

/-! ### The bulk stop law is symmetric

A stop at or below `L` is a stop at agreement, and agreement is symmetric in
the two walks.  The one asymmetry of the rule, stopping when the real total
passes `L`, contributes nothing to the bulk: once either total is past `L` the
walk cannot stop at or below `L`. -/

/-- Past `L` on the simulated side, no bulk stop: the real total must climb to
the simulated one and passes `L` on the way. -/
lemma ideal_bulk_zero_of_snd {s : ℕ} (hs : s ≤ L) (F : ℕ) :
    ∀ r t, L < t → ideal A B P P' L F r t s = 0 := by
  induction F with
  | zero => intro r t _; simp [ideal]
  | succ F ih =>
      intro r t ht
      by_cases h : L < r ∨ r = t
      · rw [ideal_stop h, if_neg (by omega)]
      · have hrt : r < t := by omega
        rw [ideal_left h hrt]
        refine Finset.sum_eq_zero fun x _ ↦ ?_
        rw [ih (r + x) t ht, mul_zero]

/-- **The bulk symmetry**: at stop values at most `L` the idealised stop law is
invariant under exchanging the two laws together with the two totals. -/
theorem ideal_bulk_symm {s : ℕ} (hs : s ≤ L) (F : ℕ) :
    ∀ r t, ideal A B P P' L F r t s = ideal B A P' P L F t r s := by
  induction F with
  | zero => intro r t; simp [ideal]
  | succ F ih =>
      intro r t
      rcases eq_or_ne r t with rfl | hne
      · rw [ideal_stop (Or.inr rfl), ideal_stop (Or.inr rfl)]
      · by_cases hr : L < r
        · by_cases ht : L < t
          · rw [ideal_stop (Or.inl hr), ideal_stop (Or.inl ht),
              if_neg (by omega), if_neg (by omega)]
          · rw [ideal_stop (Or.inl hr), if_neg (by omega),
              ideal_bulk_zero_of_snd hs _ t r hr]
        · by_cases ht : L < t
          · rw [ideal_stop (Or.inl ht), if_neg (by omega),
              ideal_bulk_zero_of_snd hs _ r t ht]
          · by_cases hrt : r < t
            · rw [ideal_left (by omega) hrt, ideal_right (by omega) (by omega)]
              exact Finset.sum_congr rfl fun x _ ↦ by rw [ih]
            · rw [ideal_right (by omega) hrt,
                ideal_left (by omega) (by omega)]
              exact Finset.sum_congr rfl fun y _ ↦ by rw [ih]

/-! ### The window tail

A stop past `L` needs the real total to climb past `L`, hence at least
`L / MA` real increments; the survival probability of the lag walk decays
geometrically, one factor per block of `H` increments, through the correction
words of `thm:common-renewal`. -/

lemma alive_stop {m r t : ℕ} (h : L < r ∨ r = t) : alive A B P P' L m r t = 0 := by
  cases m <;> · rw [alive, if_pos h]

lemma alive_nonneg (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b) :
    ∀ m r t, 0 ≤ alive A B P P' L m r t := by
  intro m
  induction m with
  | zero => intro r t; rw [alive]; split <;> norm_num
  | succ m ih =>
      intro r t
      rw [alive]
      split
      · exact le_rfl
      · split
        · exact Finset.sum_nonneg fun x hx ↦ mul_nonneg (hP x hx) (ih _ _)
        · exact Finset.sum_nonneg fun y hy ↦ mul_nonneg (hP' y hy) (ih _ _)

lemma alive_le_one (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1) :
    ∀ m r t, alive A B P P' L m r t ≤ 1 := by
  intro m
  induction m with
  | zero => intro r t; rw [alive]; split <;> norm_num
  | succ m ih =>
      intro r t
      rw [alive]
      split
      · norm_num
      · split
        · calc ∑ x ∈ A, P x * alive A B P P' L m (r + x) t
              ≤ ∑ x ∈ A, P x * 1 :=
                Finset.sum_le_sum fun x hx ↦
                  mul_le_mul_of_nonneg_left (ih _ _) (hP x hx)
            _ = 1 := by rw [← Finset.sum_mul, hP1, one_mul]
        · calc ∑ y ∈ B, P' y * alive A B P P' L m r (t + y)
              ≤ ∑ y ∈ B, P' y * 1 :=
                Finset.sum_le_sum fun y hy ↦
                  mul_le_mul_of_nonneg_left (ih _ _) (hP' y hy)
            _ = 1 := by rw [← Finset.sum_mul, hP'1, one_mul]

/-- **The window mass is bounded by the survival probability**: while
`r + j·MA ≤ L` no stop past `L` can occur within `j` steps, so all window mass
flows through states alive at time `j`. -/
lemma ideal_window_le_alive {MA : ℕ} (hMA : ∀ a ∈ A, a ≤ MA)
    (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    {W : Finset ℕ} (hW : ∀ s ∈ W, L < s) :
    ∀ j F r t, r + j * MA ≤ L →
      ∑ s ∈ W, ideal A B P P' L F r t s ≤ alive A B P P' L j r t := by
  intro j
  induction j with
  | zero =>
      intro F r t hj
      by_cases h : L < r ∨ r = t
      · rcases h with h | h
        · omega
        · rw [alive_stop (Or.inr h)]
          refine le_of_eq ?_
          cases F with
          | zero => simp [ideal]
          | succ F =>
              calc ∑ s ∈ W, ideal A B P P' L (F + 1) r t s
                  = ∑ s ∈ W, if s = r then (1 : ℝ) else 0 :=
                    Finset.sum_congr rfl fun s _ ↦ ideal_stop (Or.inr h)
                _ = 0 := by
                    rw [Finset.sum_ite_eq' W r fun _ ↦ (1 : ℝ)]
                    split
                    · rename_i hmem
                      exact absurd (hW r hmem) (by omega)
                    · rfl
      · have : alive A B P P' L 0 r t = 1 := by rw [alive, if_neg h]
        rw [this]
        exact ideal_sum_le_one hP hP' hP1 hP'1 F r t W
  | succ j ih =>
      intro F r t hj
      have hrL : ¬ L < r := by omega
      by_cases h : L < r ∨ r = t
      · have hrt : r = t := by tauto
        rw [alive_stop (Or.inr hrt)]
        refine le_of_eq ?_
        cases F with
        | zero => simp [ideal]
        | succ F =>
            calc ∑ s ∈ W, ideal A B P P' L (F + 1) r t s
                = ∑ s ∈ W, if s = r then (1 : ℝ) else 0 :=
                  Finset.sum_congr rfl fun s _ ↦ ideal_stop (Or.inr hrt)
              _ = 0 := by
                  rw [Finset.sum_ite_eq' W r fun _ ↦ (1 : ℝ)]
                  split
                  · rename_i hmem
                    exact absurd (hW r hmem) (by omega)
                  · rfl
      · cases F with
        | zero =>
            simp only [ideal, Finset.sum_const_zero]
            exact alive_nonneg hP hP' _ _ _
        | succ F =>
            by_cases hrt : r < t
            · rw [show alive A B P P' L (j + 1) r t
                  = ∑ x ∈ A, P x * alive A B P P' L j (r + x) t by
                    rw [alive, if_neg h, if_pos hrt]]
              calc ∑ s ∈ W, ideal A B P P' L (F + 1) r t s
                  = ∑ x ∈ A, P x * ∑ s ∈ W, ideal A B P P' L F (r + x) t s := by
                    simp only [ideal_left h hrt]
                    rw [Finset.sum_comm]
                    exact Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum ..).symm
                _ ≤ ∑ x ∈ A, P x * alive A B P P' L j (r + x) t :=
                    Finset.sum_le_sum fun x hx ↦
                      mul_le_mul_of_nonneg_left
                        (ih F (r + x) t (by
                          have h1 := hMA x hx
                          have h2 : (j + 1) * MA = j * MA + MA := Nat.succ_mul j MA
                          omega)) (hP x hx)
            · rw [show alive A B P P' L (j + 1) r t
                  = ∑ y ∈ B, P' y * alive A B P P' L j r (t + y) by
                    rw [alive, if_neg h, if_neg hrt]]
              calc ∑ s ∈ W, ideal A B P P' L (F + 1) r t s
                  = ∑ y ∈ B, P' y * ∑ s ∈ W, ideal A B P P' L F r (t + y) s := by
                    simp only [ideal_right h hrt]
                    rw [Finset.sum_comm]
                    exact Finset.sum_congr rfl fun y _ ↦ (Finset.mul_sum ..).symm
                _ ≤ ∑ y ∈ B, P' y * alive A B P P' L j r (t + y) :=
                    Finset.sum_le_sum fun y hy ↦
                      mul_le_mul_of_nonneg_left
                        (ih F r (t + y) (by
                          have h2 : (j + 1) * MA = j * MA + MA := Nat.succ_mul j MA
                          omega)) (hP' y hy)

end Ideal

/-! ### The correction-word descent

The lag of the idealised walk moves by the lagging-side rule, so a pair of
prescribed correction words closing the lag under `renewalWordRun` is read in
exactly the automaton's interlacing.  Spelling the words costs a factor of the
least mass per letter, which kills a fixed fraction of the surviving mass in
every block. -/

section Words

lemma renewalWordRunAux_neg_nil {d : ℤ} (hd : d < 0) (ys : List ℕ) :
    ∀ n, renewalWordRunAux n d [] ys = d := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [renewalWordRunAux, if_neg hd.ne, if_pos hd]

lemma renewalWordRunAux_pos_nil {d : ℤ} (hd : 0 < d) (xs : List ℕ) :
    ∀ n, renewalWordRunAux n d xs [] = d := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [renewalWordRunAux, if_neg hd.ne',
        if_neg (show ¬ d < 0 by omega)]

lemma renewalWordRun_neg_cons {d : ℤ} (hd : d < 0) (a : ℕ) (xs ys : List ℕ) :
    renewalWordRun d (a :: xs) ys = renewalWordRun (d + a) xs ys := by
  rw [renewalWordRun, renewalWordRun,
    show (a :: xs).length + ys.length = (xs.length + ys.length) + 1 by
      simp only [List.length_cons]; omega]
  simp only [renewalWordRunAux, if_neg hd.ne, if_pos hd]

lemma renewalWordRun_pos_cons {d : ℤ} (hd : 0 < d) (b : ℕ) (xs ys : List ℕ) :
    renewalWordRun d xs (b :: ys) = renewalWordRun (d - b) xs ys := by
  rw [renewalWordRun, renewalWordRun,
    show xs.length + (b :: ys).length = (xs.length + ys.length) + 1 by
      simp only [List.length_cons]; omega]
  simp only [renewalWordRunAux, if_neg hd.ne',
    if_neg (show ¬ d < 0 by omega)]

/-- A list of factors bounded below by `p ≥ 0` has product at least
`p ^ length`. -/
lemma pow_length_le_prod {p : ℝ} (hp : 0 ≤ p) :
    ∀ l : List ℝ, (∀ x ∈ l, p ≤ x) → p ^ l.length ≤ l.prod := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
      intro h
      have ha := h a List.mem_cons_self
      calc p ^ (a :: l).length = p * p ^ l.length := by rw [List.length_cons, pow_succ']
        _ ≤ a * l.prod := by
            refine mul_le_mul ha (ih fun x hx ↦ h x (List.mem_cons_of_mem a hx))
              (pow_nonneg hp _) (le_trans hp ha)
        _ = (a :: l).prod := (List.prod_cons).symm

variable {A B : Finset ℕ} {P P' : ℕ → ℝ} {L : ℕ}

lemma prob_le_one (hP : ∀ a ∈ A, 0 ≤ P a) (hP1 : ∑ a ∈ A, P a = 1) {a : ℕ}
    (ha : a ∈ A) : P a ≤ 1 := by
  rw [← hP1]
  exact Finset.single_le_sum hP ha

/-- A product of masses over a support is in the unit interval. -/
lemma prod_map_mem_unit {S : Finset ℕ} {f : ℕ → ℝ} (hf0 : ∀ a ∈ S, 0 ≤ f a)
    (hf1 : ∀ a ∈ S, f a ≤ 1) :
    ∀ l : List ℕ, (∀ x ∈ l, x ∈ S) → 0 ≤ (l.map f).prod ∧ (l.map f).prod ≤ 1 := by
  intro l
  induction l with
  | nil => intro _; norm_num
  | cons a l ih =>
      intro h
      have ha := h a List.mem_cons_self
      obtain ⟨ih0, ih1⟩ := ih fun x hx ↦ h x (List.mem_cons_of_mem a hx)
      rw [List.map_cons, List.prod_cons]
      constructor
      · exact mul_nonneg (hf0 a ha) ih0
      · exact mul_le_one₀ (hf1 a ha) ih0 ih1

/-- **The word descent**: prescribed correction words that close the lag are
read in the automaton's interlacing, so the surviving mass after `H` steps
loses at least the mass of spelling them. -/
lemma alive_word_le (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1) :
    ∀ (H : ℕ) (r t : ℕ) (xs ys : List ℕ), (∀ x ∈ xs, x ∈ A) → (∀ y ∈ ys, y ∈ B) →
      xs.length + ys.length ≤ H →
      renewalWordRun ((r : ℤ) - t) xs ys = 0 →
      alive A B P P' L H r t ≤ 1 - (xs.map P).prod * (ys.map P').prod := by
  intro H
  induction H with
  | zero =>
      intro r t xs ys hxs hys hlen hrun
      have hxs0 : xs = [] := List.length_eq_zero_iff.mp (by omega)
      have hys0 : ys = [] := List.length_eq_zero_iff.mp (by omega)
      subst hxs0; subst hys0
      have hd : (r : ℤ) - t = 0 := by
        rw [renewalWordRun] at hrun
        simpa [renewalWordRunAux] using hrun
      have hrt : r = t := by omega
      rw [alive_stop (Or.inr hrt)]
      simp
  | succ H ih =>
      intro r t xs ys hxs hys hlen hrun
      have hprodx := prod_map_mem_unit hP (fun a ha ↦ prob_le_one hP hP1 ha) xs hxs
      have hprody := prod_map_mem_unit hP' (fun b hb ↦ prob_le_one hP' hP'1 hb) ys hys
      by_cases hterm : L < r ∨ r = t
      · rw [alive_stop hterm]
        have := mul_le_one₀ hprodx.2 hprody.1 hprody.2
        linarith [mul_nonneg hprodx.1 hprody.1]
      · have hne : r ≠ t := fun hc ↦ hterm (Or.inr hc)
        by_cases hrt : r < t
        · -- the real side lags, the words prescribe the next real increment
          have hd : (r : ℤ) - t < 0 := by omega
          obtain ⟨a, xs', rfl⟩ : ∃ a xs', xs = a :: xs' := by
            cases xs with
            | nil =>
                exfalso
                rw [renewalWordRun, renewalWordRunAux_neg_nil hd] at hrun
                omega
            | cons a xs' => exact ⟨a, xs', rfl⟩
          have ha : a ∈ A := hxs a List.mem_cons_self
          have hrun' : renewalWordRun (((r + a : ℕ) : ℤ) - t) xs' ys = 0 := by
            have h1 := renewalWordRun_neg_cons hd a xs' ys
            rw [h1] at hrun
            rw [show (((r + a : ℕ) : ℤ) - t) = (r : ℤ) - t + a by push_cast; ring]
            exact hrun
          have hstep : alive A B P P' L (H + 1) r t
              = ∑ x ∈ A, P x * alive A B P P' L H (r + x) t := by
            rw [alive, if_neg hterm, if_pos hrt]
          have hihx := ih (r + a) t xs' ys
            (fun x hx ↦ hxs x (List.mem_cons_of_mem a hx)) hys
            (by simp only [List.length_cons] at hlen; omega) hrun'
          have hsplit : ∑ x ∈ A, P x * alive A B P P' L H (r + x) t
              = P a * alive A B P P' L H (r + a) t
                + ∑ x ∈ A.erase a, P x * alive A B P P' L H (r + x) t :=
            (Finset.add_sum_erase A
              (fun x ↦ P x * alive A B P P' L H (r + x) t) ha).symm
          have herase : ∑ x ∈ A.erase a, P x * alive A B P P' L H (r + x) t
              ≤ 1 - P a := by
            calc ∑ x ∈ A.erase a, P x * alive A B P P' L H (r + x) t
                ≤ ∑ x ∈ A.erase a, P x * 1 :=
                  Finset.sum_le_sum fun x hx ↦ mul_le_mul_of_nonneg_left
                    (alive_le_one hP hP' hP1 hP'1 _ _ _)
                    (hP x (Finset.mem_of_mem_erase hx))
              _ = 1 - P a := by
                  simp only [mul_one]
                  have h := Finset.add_sum_erase A P ha
                  linarith [h.trans hP1]
          have hmain : P a * alive A B P P' L H (r + a) t
              ≤ P a * (1 - (xs'.map P).prod * (ys.map P').prod) :=
            mul_le_mul_of_nonneg_left hihx (hP a ha)
          rw [hstep, hsplit]
          have hgoal : ((a :: xs').map P).prod * (ys.map P').prod
              = P a * ((xs'.map P).prod * (ys.map P').prod) := by
            rw [List.map_cons, List.prod_cons]
            ring
          rw [hgoal]
          nlinarith [hP a ha]
        · -- the simulated side lags
          have htr : t < r := by omega
          have hd : 0 < (r : ℤ) - t := by omega
          obtain ⟨b, ys', rfl⟩ : ∃ b ys', ys = b :: ys' := by
            cases ys with
            | nil =>
                exfalso
                rw [renewalWordRun, renewalWordRunAux_pos_nil hd] at hrun
                omega
            | cons b ys' => exact ⟨b, ys', rfl⟩
          have hb : b ∈ B := hys b List.mem_cons_self
          have hrun' : renewalWordRun ((r : ℤ) - ((t + b : ℕ) : ℤ)) xs ys' = 0 := by
            have h1 := renewalWordRun_pos_cons hd b xs ys'
            rw [h1] at hrun
            rw [show ((r : ℤ) - ((t + b : ℕ) : ℤ)) = (r : ℤ) - t - b by push_cast; ring]
            exact hrun
          have hstep : alive A B P P' L (H + 1) r t
              = ∑ y ∈ B, P' y * alive A B P P' L H r (t + y) := by
            rw [alive, if_neg hterm, if_neg hrt]
          have hihy := ih r (t + b) xs ys'
            hxs (fun y hy ↦ hys y (List.mem_cons_of_mem b hy))
            (by simp only [List.length_cons] at hlen; omega) hrun'
          have hsplit : ∑ y ∈ B, P' y * alive A B P P' L H r (t + y)
              = P' b * alive A B P P' L H r (t + b)
                + ∑ y ∈ B.erase b, P' y * alive A B P P' L H r (t + y) :=
            (Finset.add_sum_erase B
              (fun y ↦ P' y * alive A B P P' L H r (t + y)) hb).symm
          have herase : ∑ y ∈ B.erase b, P' y * alive A B P P' L H r (t + y)
              ≤ 1 - P' b := by
            calc ∑ y ∈ B.erase b, P' y * alive A B P P' L H r (t + y)
                ≤ ∑ y ∈ B.erase b, P' y * 1 :=
                  Finset.sum_le_sum fun y hy ↦ mul_le_mul_of_nonneg_left
                    (alive_le_one hP hP' hP1 hP'1 _ _ _)
                    (hP' y (Finset.mem_of_mem_erase hy))
              _ = 1 - P' b := by
                  simp only [mul_one]
                  have h := Finset.add_sum_erase B P' hb
                  linarith [h.trans hP'1]
          have hmain : P' b * alive A B P P' L H r (t + b)
              ≤ P' b * (1 - (xs.map P).prod * (ys'.map P').prod) :=
            mul_le_mul_of_nonneg_left hihy (hP' b hb)
          rw [hstep, hsplit]
          have hgoal : (xs.map P).prod * ((b :: ys').map P').prod
              = P' b * ((xs.map P).prod * (ys'.map P').prod) := by
            rw [List.map_cons, List.prod_cons]
            ring
          rw [hgoal]
          nlinarith [hP' b hb]

end Words

/-! ### Uniform correction words and geometric decay

The lag of the walk stays in the finite window `(-MB, MA)`, the correction
words of `thm:common-renewal` may be chosen uniformly over it, and iterating
the word descent block by block gives geometric decay of the survival
probability. -/

section Blocks

variable {A B : Finset ℕ} {P P' : ℕ → ℝ} {L : ℕ}

/-- The states the coupled exploration visits: totals in the two semigroup
closures, with the lag in the finite window of `thm:common-renewal`. -/
def ValidState (A B : Finset ℕ) (MA MB : ℕ) (r t : ℕ) : Prop :=
  r ∈ AddSubmonoid.closure (A : Set ℕ) ∧ t ∈ AddSubmonoid.closure (B : Set ℕ) ∧
    -(MB : ℤ) < (r : ℤ) - t ∧ (r : ℤ) - t < MA

lemma validState_stepA {MA MB : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) {r t x : ℕ}
    (h : ValidState A B MA MB r t) (hx : x ∈ A) (hx0 : 0 < x) (hrt : r < t) :
    ValidState A B MA MB (r + x) t := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨AddSubmonoid.add_mem _ h1 (AddSubmonoid.subset_closure hx), h2, ?_, ?_⟩
  · push_cast
    omega
  · have := hMA x hx
    push_cast
    omega

lemma validState_stepB {MA MB : ℕ} (hMB : ∀ b ∈ B, b ≤ MB) {r t y : ℕ}
    (h : ValidState A B MA MB r t) (hy : y ∈ B) (hy0 : 0 < y) (htr : t < r) :
    ValidState A B MA MB r (t + y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, AddSubmonoid.add_mem _ h2 (AddSubmonoid.subset_closure hy), ?_, ?_⟩
  · have := hMB y hy
    push_cast
    omega
  · push_cast
    omega

/-- **Uniform correction words over the lag window**: one bound `H` on the
length of a closing pair of words, over every valid state. -/
lemma exists_uniform_words
    (hsem : AddSubmonoid.closure (A : Set ℕ) = AddSubmonoid.closure (B : Set ℕ))
    (MA MB : ℕ) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ r t : ℕ, ValidState A B MA MB r t →
      ∃ xs ys : List ℕ, (∀ x ∈ xs, x ∈ A) ∧ (∀ y ∈ ys, y ∈ B) ∧
        renewalWordRun ((r : ℤ) - t) xs ys = 0 ∧ xs.length + ys.length ≤ H := by
  classical
  have key : ∀ z ∈ Finset.Ioo (-(MB : ℤ)) (MA : ℤ), ∃ n : ℕ,
      ∀ r t : ℕ, r ∈ AddSubmonoid.closure (A : Set ℕ) →
        t ∈ AddSubmonoid.closure (B : Set ℕ) → (r : ℤ) - t = z →
        ∃ xs ys : List ℕ, (∀ x ∈ xs, x ∈ A) ∧ (∀ y ∈ ys, y ∈ B) ∧
          renewalWordRun z xs ys = 0 ∧ xs.length + ys.length ≤ n := by
    intro z _
    by_cases hex : ∃ r t : ℕ, r ∈ AddSubmonoid.closure (A : Set ℕ) ∧
        t ∈ AddSubmonoid.closure (B : Set ℕ) ∧ (r : ℤ) - t = z
    · obtain ⟨r0, t0, h1, h2, h3⟩ := hex
      obtain ⟨xs, ys, hxs, hys, hrun⟩ := common_renewal_run hsem h1 h2
      exact ⟨xs.length + ys.length, fun r t _ _ _ ↦
        ⟨xs, ys, hxs, hys, h3 ▸ hrun, le_rfl⟩⟩
    · exact ⟨0, fun r t hr ht hz ↦ absurd ⟨r, t, hr, ht, hz⟩ hex⟩
  choose n hn using key
  refine ⟨1 + (Finset.Ioo (-(MB : ℤ)) (MA : ℤ)).attach.sup (fun z ↦ n z.1 z.2),
    by omega, fun r t hv ↦ ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hv
  have hz : (r : ℤ) - t ∈ Finset.Ioo (-(MB : ℤ)) (MA : ℤ) := Finset.mem_Ioo.mpr ⟨h3, h4⟩
  obtain ⟨xs, ys, hxs, hys, hrun, hlen⟩ := hn _ hz r t h1 h2 rfl
  refine ⟨xs, ys, hxs, hys, hrun, ?_⟩
  have hle : n ((r : ℤ) - t) hz
      ≤ (Finset.Ioo (-(MB : ℤ)) (MA : ℤ)).attach.sup (fun z ↦ n z.1 z.2) :=
    Finset.le_sup
      (f := fun z : {z // z ∈ Finset.Ioo (-(MB : ℤ)) (MA : ℤ)} ↦ n z.1 z.2)
      (Finset.mem_attach _ ⟨_, hz⟩)
  omega

/-- **The Chapman decomposition**: a uniform bound on the survival probability
after `m` further steps multiplies the survival probability after `a` steps. -/
lemma alive_add_le {MA MB : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) (hMB : ∀ b ∈ B, b ≤ MB)
    (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b)
    (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    {m : ℕ} {c : ℝ}
    (hc : ∀ r t, ValidState A B MA MB r t → alive A B P P' L m r t ≤ c) :
    ∀ a r t, ValidState A B MA MB r t →
      alive A B P P' L (a + m) r t ≤ c * alive A B P P' L a r t := by
  intro a
  induction a with
  | zero =>
      intro r t hv
      rw [Nat.zero_add]
      by_cases h : L < r ∨ r = t
      · rw [alive_stop h, alive_stop h, mul_zero]
      · rw [show alive A B P P' L 0 r t = 1 by rw [alive, if_neg h], mul_one]
        exact hc r t hv
  | succ a ih =>
      intro r t hv
      rw [Nat.succ_add]
      by_cases h : L < r ∨ r = t
      · rw [alive_stop h, alive_stop h, mul_zero]
      · by_cases hrt : r < t
        · rw [show alive A B P P' L (a + m + 1) r t
              = ∑ x ∈ A, P x * alive A B P P' L (a + m) (r + x) t by
                rw [alive, if_neg h, if_pos hrt],
            show alive A B P P' L (a + 1) r t
              = ∑ x ∈ A, P x * alive A B P P' L a (r + x) t by
                rw [alive, if_neg h, if_pos hrt], Finset.mul_sum]
          refine Finset.sum_le_sum fun x hx ↦ ?_
          calc P x * alive A B P P' L (a + m) (r + x) t
              ≤ P x * (c * alive A B P P' L a (r + x) t) :=
                mul_le_mul_of_nonneg_left
                  (ih (r + x) t (validState_stepA hMA hv hx (hA0 x hx) hrt))
                  (hP x hx)
            _ = c * (P x * alive A B P P' L a (r + x) t) := by ring
        · rw [show alive A B P P' L (a + m + 1) r t
              = ∑ y ∈ B, P' y * alive A B P P' L (a + m) r (t + y) by
                rw [alive, if_neg h, if_neg hrt],
            show alive A B P P' L (a + 1) r t
              = ∑ y ∈ B, P' y * alive A B P P' L a r (t + y) by
                rw [alive, if_neg h, if_neg hrt], Finset.mul_sum]
          refine Finset.sum_le_sum fun y hy ↦ ?_
          calc P' y * alive A B P P' L (a + m) r (t + y)
              ≤ P' y * (c * alive A B P P' L a r (t + y)) :=
                mul_le_mul_of_nonneg_left
                  (ih r (t + y) (validState_stepB hMB hv hy (hB0 y hy) (by omega)))
                  (hP' y hy)
            _ = c * (P' y * alive A B P P' L a r (t + y)) := by ring

/-- **The block bound**: every block of `H` steps closes the lag with
probability at least `p ^ H`. -/
lemma alive_block_le
    (hsem : AddSubmonoid.closure (A : Set ℕ) = AddSubmonoid.closure (B : Set ℕ))
    (MA MB : ℕ) {p : ℝ} (hp0 : 0 < p) (hAne : A.Nonempty)
    (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    (hPp : ∀ a ∈ A, p ≤ P a) (hP'p : ∀ b ∈ B, p ≤ P' b) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ r t, ValidState A B MA MB r t →
      alive A B P P' L (H) r t ≤ 1 - p ^ H := by
  obtain ⟨H, hH1, hH⟩ := exists_uniform_words hsem MA MB
  have hp1 : p ≤ 1 := by
    obtain ⟨a, ha⟩ := hAne
    exact (hPp a ha).trans (prob_le_one hP hP1 ha)
  refine ⟨H, hH1, fun r t hv ↦ ?_⟩
  obtain ⟨xs, ys, hxs, hys, hrun, hlen⟩ := hH r t hv
  calc alive A B P P' L H r t
      ≤ 1 - (xs.map P).prod * (ys.map P').prod :=
        alive_word_le hP hP' hP1 hP'1 H r t xs ys hxs hys hlen hrun
    _ ≤ 1 - p ^ H := by
        have h1 : p ^ xs.length ≤ (xs.map P).prod := by
          have h := pow_length_le_prod hp0.le (xs.map P) (fun x hx ↦ ?_)
          · simpa using h
          · obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
            exact hPp x' (hxs x' hx')
        have h2 : p ^ ys.length ≤ (ys.map P').prod := by
          have h := pow_length_le_prod hp0.le (ys.map P') (fun y hy ↦ ?_)
          · simpa using h
          · obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
            exact hP'p y' (hys y' hy')
        have h3 : p ^ H ≤ p ^ (xs.length + ys.length) :=
          pow_le_pow_of_le_one hp0.le hp1 hlen
        have h4 : p ^ (xs.length + ys.length) = p ^ xs.length * p ^ ys.length :=
          pow_add p _ _
        have h5 : p ^ xs.length * p ^ ys.length ≤ (xs.map P).prod * (ys.map P').prod :=
          mul_le_mul h1 h2 (pow_nonneg hp0.le _)
            (le_trans (pow_nonneg hp0.le _) h1)
        linarith

/-- **Geometric decay of the survival probability.** -/
lemma alive_le_pow {MA MB : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) (hMB : ∀ b ∈ B, b ≤ MB)
    (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b)
    (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    {H : ℕ} {q : ℝ} (hq0 : 0 ≤ 1 - q)
    (hblock : ∀ r t, ValidState A B MA MB r t → alive A B P P' L H r t ≤ 1 - q) :
    ∀ k r t, ValidState A B MA MB r t →
      alive A B P P' L (k * H) r t ≤ (1 - q) ^ k := by
  intro k
  induction k with
  | zero =>
      intro r t _
      rw [Nat.zero_mul, pow_zero]
      exact alive_le_one hP hP' hP1 hP'1 0 r t
  | succ k ih =>
      intro r t hv
      rw [show (k + 1) * H = H + k * H by ring, pow_succ]
      calc alive A B P P' L (H + k * H) r t
          ≤ (1 - q) ^ k * alive A B P P' L H r t :=
            alive_add_le hMA hMB hA0 hB0 hP hP'
              (fun r' t' hv' ↦ ih r' t' hv') H r t hv
        _ ≤ (1 - q) ^ k * (1 - q) :=
            mul_le_mul_of_nonneg_left (hblock r t hv) (pow_nonneg hq0 k)

/-- The survival probability is non-increasing in the number of steps. -/
lemma alive_anti (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1) :
    ∀ m r t, alive A B P P' L (m + 1) r t ≤ alive A B P P' L m r t := by
  intro m
  induction m with
  | zero =>
      intro r t
      by_cases h : L < r ∨ r = t
      · rw [alive_stop h, alive_stop h]
      · rw [show alive A B P P' L 0 r t = 1 by rw [alive, if_neg h]]
        exact alive_le_one hP hP' hP1 hP'1 1 r t
  | succ m ih =>
      intro r t
      by_cases h : L < r ∨ r = t
      · rw [alive_stop h, alive_stop h]
      · by_cases hrt : r < t
        · rw [show alive A B P P' L (m + 1 + 1) r t
              = ∑ x ∈ A, P x * alive A B P P' L (m + 1) (r + x) t by
                rw [alive, if_neg h, if_pos hrt],
            show alive A B P P' L (m + 1) r t
              = ∑ x ∈ A, P x * alive A B P P' L m (r + x) t by
                rw [alive, if_neg h, if_pos hrt]]
          exact Finset.sum_le_sum fun x hx ↦
            mul_le_mul_of_nonneg_left (ih (r + x) t) (hP x hx)
        · rw [show alive A B P P' L (m + 1 + 1) r t
              = ∑ y ∈ B, P' y * alive A B P P' L (m + 1) r (t + y) by
                rw [alive, if_neg h, if_neg hrt],
            show alive A B P P' L (m + 1) r t
              = ∑ y ∈ B, P' y * alive A B P P' L m r (t + y) by
                rw [alive, if_neg h, if_neg hrt]]
          exact Finset.sum_le_sum fun y hy ↦
            mul_le_mul_of_nonneg_left (ih r (t + y)) (hP' y hy)

lemma alive_anti_of_le (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    {m m' : ℕ} (h : m ≤ m') (r t : ℕ) :
    alive A B P P' L m' r t ≤ alive A B P P' L m r t := by
  induction m' with
  | zero =>
      rw [Nat.le_zero.mp h]
  | succ m' ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
      · exact le_trans (alive_anti hP hP' hP1 hP'1 m' r t) (ih (by omega))
      · exact le_rfl

end Blocks

/-! ### The realised coupled exploration

Failures spend exits without moving the totals, and exhaustion stops the blob
at its current total.  The realised rule departs from the idealised one only
through exhaustion, whose mass needs two failures. -/

section Couple

variable (A B : Finset ℕ) (P P' : ℕ → ℝ) (L : ℕ) (φ : ℝ)

/-- The stop law of the realised coupled exploration from totals `(r, t)` with
`e` unspent exits: a real move descends, failing with probability `φ`. -/
noncomputable def couple : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, _, _, _, _ => 0
  | F + 1, r, t, e, s =>
      if L < r ∨ r = t then (if s = r then 1 else 0)
      else if e = 0 then (if s = r then 1 else 0)
      else if r < t then
        φ * couple F r t (e - 1) s
          + (1 - φ) * ∑ x ∈ A, P x * couple F (r + x) t (e + x) s
      else ∑ y ∈ B, P' y * couple F r (t + y) e s

/-- The mass of the exhaustion event: every exit spent before the walk
stops. -/
noncomputable def exhaust : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, _, _, _ => 0
  | F + 1, r, t, e =>
      if L < r ∨ r = t then 0
      else if e = 0 then 1
      else if r < t then
        φ * exhaust F r t (e - 1)
          + (1 - φ) * ∑ x ∈ A, P x * exhaust F (r + x) t (e + x)
      else ∑ y ∈ B, P' y * exhaust F r (t + y) e

variable {A B P P' L φ}

lemma couple_nonneg (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ F r t e s, 0 ≤ couple A B P P' L φ F r t e s := by
  intro F
  induction F with
  | zero => intro r t e s; simp [couple]
  | succ F ih =>
      intro r t e s
      rw [couple]
      split
      · positivity
      · split
        · positivity
        · split
          · have h1 := Finset.sum_nonneg fun x hx ↦ mul_nonneg (hP x hx) (ih (r + x) t (e + x) s)
            have h2 := ih r t (e - 1) s
            nlinarith
          · exact Finset.sum_nonneg fun y hy ↦ mul_nonneg (hP' y hy) (ih r (t + y) e s)

lemma exhaust_nonneg (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ F r t e, 0 ≤ exhaust A B P P' L φ F r t e := by
  intro F
  induction F with
  | zero => intro r t e; simp [exhaust]
  | succ F ih =>
      intro r t e
      rw [exhaust]
      split
      · exact le_rfl
      · split
        · norm_num
        · split
          · have h1 := Finset.sum_nonneg fun x hx ↦ mul_nonneg (hP x hx) (ih (r + x) t (e + x))
            have h2 := ih r t (e - 1)
            nlinarith
          · exact Finset.sum_nonneg fun y hy ↦ mul_nonneg (hP' y hy) (ih r (t + y) e)

lemma exhaust_le_one (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ F r t e, exhaust A B P P' L φ F r t e ≤ 1 := by
  intro F
  induction F with
  | zero => intro r t e; simp [exhaust]
  | succ F ih =>
      intro r t e
      rw [exhaust]
      split
      · norm_num
      · split
        · exact le_rfl
        · split
          · have h1 : ∑ x ∈ A, P x * exhaust A B P P' L φ F (r + x) t (e + x) ≤ 1 := by
              calc ∑ x ∈ A, P x * exhaust A B P P' L φ F (r + x) t (e + x)
                  ≤ ∑ x ∈ A, P x * 1 :=
                    Finset.sum_le_sum fun x hx ↦
                      mul_le_mul_of_nonneg_left (ih (r + x) t (e + x)) (hP x hx)
                _ = 1 := by rw [← Finset.sum_mul, hP1, one_mul]
            have h2 := ih r t (e - 1)
            nlinarith
          · calc ∑ y ∈ B, P' y * exhaust A B P P' L φ F r (t + y) e
                ≤ ∑ y ∈ B, P' y * 1 :=
                  Finset.sum_le_sum fun y hy ↦
                    mul_le_mul_of_nonneg_left (ih r (t + y) e) (hP' y hy)
              _ = 1 := by rw [← Finset.sum_mul, hP'1, one_mul]

/-- **One failure is unlikely**: the exhaustion mass from at least one exit is
at most one failure among at most `F` descents. -/
lemma exhaust_le_mul (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ F r t e, 1 ≤ e → exhaust A B P P' L φ F r t e ≤ F * φ := by
  intro F
  induction F with
  | zero => intro r t e _; simp [exhaust]
  | succ F ih =>
      intro r t e he
      rw [exhaust]
      split
      · positivity
      · split
        · omega
        · split
          · have h1 : exhaust A B P P' L φ F r t (e - 1) ≤ 1 :=
              exhaust_le_one hP hP' hP1 hP'1 hφ0 hφ1 F r t (e - 1)
            have h2 : ∑ x ∈ A, P x * exhaust A B P P' L φ F (r + x) t (e + x)
                ≤ F * φ := by
              calc ∑ x ∈ A, P x * exhaust A B P P' L φ F (r + x) t (e + x)
                  ≤ ∑ x ∈ A, P x * (F * φ) :=
                    Finset.sum_le_sum fun x hx ↦
                      mul_le_mul_of_nonneg_left (ih (r + x) t (e + x) (by omega))
                        (hP x hx)
                _ = F * φ := by rw [← Finset.sum_mul, hP1, one_mul]
            have h3 : 0 ≤ ∑ x ∈ A, P x * exhaust A B P P' L φ F (r + x) t (e + x) :=
              Finset.sum_nonneg fun x hx ↦
                mul_nonneg (hP x hx) (exhaust_nonneg hP hP' hφ0 hφ1 F _ _ _)
            have hexp : ((F + 1 : ℕ) : ℝ) * φ = F * φ + φ := by push_cast; ring
            nlinarith
          · calc ∑ y ∈ B, P' y * exhaust A B P P' L φ F r (t + y) e
                ≤ ∑ y ∈ B, P' y * (F * φ) :=
                  Finset.sum_le_sum fun y hy ↦
                    mul_le_mul_of_nonneg_left (ih r (t + y) e he) (hP' y hy)
              _ = F * φ := by rw [← Finset.sum_mul, hP'1, one_mul]
              _ ≤ (F + 1 : ℕ) * φ := by push_cast; nlinarith

/-- **Exhaustion needs two failures**: from two unspent exits its mass is at
most the square of one failure among at most `F` descents. -/
lemma exhaust_le_sq (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ F r t e, 2 ≤ e → exhaust A B P P' L φ F r t e ≤ (F * φ) ^ 2 := by
  intro F
  induction F with
  | zero => intro r t e _; simp [exhaust]
  | succ F ih =>
      intro r t e he
      rw [exhaust]
      split
      · positivity
      · split
        · omega
        · split
          · have h1 : exhaust A B P P' L φ F r t (e - 1) ≤ F * φ :=
              exhaust_le_mul hP hP' hP1 hP'1 hφ0 hφ1 F r t (e - 1) (by omega)
            have h2 : ∑ x ∈ A, P x * exhaust A B P P' L φ F (r + x) t (e + x)
                ≤ (F * φ) ^ 2 := by
              calc ∑ x ∈ A, P x * exhaust A B P P' L φ F (r + x) t (e + x)
                  ≤ ∑ x ∈ A, P x * ((F * φ) ^ 2) :=
                    Finset.sum_le_sum fun x hx ↦
                      mul_le_mul_of_nonneg_left (ih (r + x) t (e + x) (by omega))
                        (hP x hx)
                _ = (F * φ) ^ 2 := by rw [← Finset.sum_mul, hP1, one_mul]
            have h3 : 0 ≤ ∑ x ∈ A, P x * exhaust A B P P' L φ F (r + x) t (e + x) :=
              Finset.sum_nonneg fun x hx ↦
                mul_nonneg (hP x hx) (exhaust_nonneg hP hP' hφ0 hφ1 F _ _ _)
            have hexp : (((F + 1 : ℕ) : ℝ) * φ) ^ 2
                = (F * φ) ^ 2 + 2 * F * φ ^ 2 + φ ^ 2 := by push_cast; ring
            nlinarith
          · calc ∑ y ∈ B, P' y * exhaust A B P P' L φ F r (t + y) e
                ≤ ∑ y ∈ B, P' y * ((F * φ) ^ 2) :=
                  Finset.sum_le_sum fun y hy ↦
                    mul_le_mul_of_nonneg_left (ih r (t + y) e he) (hP' y hy)
              _ = (F * φ) ^ 2 := by rw [← Finset.sum_mul, hP'1, one_mul]
              _ ≤ ((F + 1 : ℕ) * φ) ^ 2 := by
                  have h4 : (0 : ℝ) ≤ F * φ := by positivity
                  have h5 : (F : ℝ) * φ ≤ (F + 1 : ℕ) * φ := by push_cast; nlinarith
                  nlinarith

/-! #### Unfolding the realised rule -/

lemma couple_stop {F r t e s : ℕ} (h : L < r ∨ r = t) :
    couple A B P P' L φ (F + 1) r t e s = if s = r then 1 else 0 := by
  rw [couple, if_pos h]

lemma couple_exh {F r t e s : ℕ} (h : ¬ (L < r ∨ r = t)) (he : e = 0) :
    couple A B P P' L φ (F + 1) r t e s = if s = r then 1 else 0 := by
  rw [couple, if_neg h, if_pos he]

lemma couple_left {F r t e s : ℕ} (h : ¬ (L < r ∨ r = t)) (he : ¬ e = 0)
    (hrt : r < t) :
    couple A B P P' L φ (F + 1) r t e s
      = φ * couple A B P P' L φ F r t (e - 1) s
        + (1 - φ) * ∑ x ∈ A, P x * couple A B P P' L φ F (r + x) t (e + x) s := by
  rw [couple, if_neg h, if_neg he, if_pos hrt]

lemma couple_right {F r t e s : ℕ} (h : ¬ (L < r ∨ r = t)) (he : ¬ e = 0)
    (hrt : ¬ r < t) :
    couple A B P P' L φ (F + 1) r t e s
      = ∑ y ∈ B, P' y * couple A B P P' L φ F r (t + y) e s := by
  rw [couple, if_neg h, if_neg he, if_neg hrt]

lemma exhaust_stop {F r t e : ℕ} (h : L < r ∨ r = t) :
    exhaust A B P P' L φ (F + 1) r t e = 0 := by
  rw [exhaust, if_pos h]

lemma exhaust_exh {F r t e : ℕ} (h : ¬ (L < r ∨ r = t)) (he : e = 0) :
    exhaust A B P P' L φ (F + 1) r t e = 1 := by
  rw [exhaust, if_neg h, if_pos he]

lemma exhaust_left {F r t e : ℕ} (h : ¬ (L < r ∨ r = t)) (he : ¬ e = 0)
    (hrt : r < t) :
    exhaust A B P P' L φ (F + 1) r t e
      = φ * exhaust A B P P' L φ F r t (e - 1)
        + (1 - φ) * ∑ x ∈ A, P x * exhaust A B P P' L φ F (r + x) t (e + x) := by
  rw [exhaust, if_neg h, if_neg he, if_pos hrt]

lemma exhaust_right {F r t e : ℕ} (h : ¬ (L < r ∨ r = t)) (he : ¬ e = 0)
    (hrt : ¬ r < t) :
    exhaust A B P P' L φ (F + 1) r t e
      = ∑ y ∈ B, P' y * exhaust A B P P' L φ F r (t + y) e := by
  rw [exhaust, if_neg h, if_neg he, if_neg hrt]

/-! #### The idealised rule at stable fuel -/

/-- Past the step bound the fuel is irrelevant. -/
lemma ideal_succ_eq {MA MB : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) (hMB : ∀ b ∈ B, b ≤ MB)
    (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b) :
    ∀ F r t s, r ≤ L + MA → t ≤ L + MB → 2 * L + MA + MB + 1 ≤ F + r + t →
      ideal A B P P' L (F + 1) r t s = ideal A B P P' L F r t s := by
  intro F
  induction F with
  | zero =>
      intro r t s hr ht hF
      omega
  | succ F ih =>
      intro r t s hr ht hF
      by_cases h : L < r ∨ r = t
      · rw [ideal_stop h, ideal_stop h]
      · have hrL : ¬ L < r := fun hc ↦ h (Or.inl hc)
        by_cases hrt : r < t
        · rw [ideal_left h hrt, ideal_left h hrt]
          refine Finset.sum_congr rfl fun x hx ↦ ?_
          rw [ih (r + x) t s (by have := hMA x hx; omega) ht
            (by have := hA0 x hx; omega)]
        · rw [ideal_right h hrt, ideal_right h hrt]
          refine Finset.sum_congr rfl fun y hy ↦ ?_
          rw [ih r (t + y) s hr (by have := hMB y hy; omega)
            (by have := hB0 y hy; omega)]

/-- The stable-fuel idealised rule satisfies its own one-step recursion on the
real side. -/
lemma idealFix_left {MA MB : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) (hMB : ∀ b ∈ B, b ≤ MB)
    (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b) {r t s : ℕ}
    (h : ¬ (L < r ∨ r = t)) (hrt : r < t) (ht : t ≤ L + MB) :
    ideal A B P P' L (2 * L + MA + MB + 1) r t s
      = ∑ x ∈ A, P x * ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s := by
  rw [show 2 * L + MA + MB + 1 = (2 * L + MA + MB) + 1 from rfl, ideal_left h hrt]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [ideal_succ_eq hMA hMB hA0 hB0 (2 * L + MA + MB) (r + x) t s
    (by have := hMA x hx; omega) ht (by have := hA0 x hx; omega)]

/-- The stable-fuel idealised rule satisfies its own one-step recursion on the
simulated side. -/
lemma idealFix_right {MA MB : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) (hMB : ∀ b ∈ B, b ≤ MB)
    (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b) {r t s : ℕ}
    (h : ¬ (L < r ∨ r = t)) (hrt : ¬ r < t) (hr : r ≤ L + MA) :
    ideal A B P P' L (2 * L + MA + MB + 1) r t s
      = ∑ y ∈ B, P' y * ideal A B P P' L (2 * L + MA + MB + 1) r (t + y) s := by
  rw [show 2 * L + MA + MB + 1 = (2 * L + MA + MB) + 1 from rfl, ideal_right h hrt]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  rw [ideal_succ_eq hMA hMB hA0 hB0 (2 * L + MA + MB) r (t + y) s hr
    (by have h1 := hMB y hy; omega) (by have := hB0 y hy; omega)]

/-! #### The realised rule departs from the idealised one only on exhaustion -/

/-- **The exhaustion coupling**: on any set of stop values the realised and the
idealised laws differ by at most twice the exhaustion mass. -/
lemma couple_ideal_close {MA MB : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) (hMB : ∀ b ∈ B, b ≤ MB)
    (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b)
    (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ (F : ℕ) (r t e : ℕ) (S : Finset ℕ), r ≤ L + MA → t ≤ L + MB →
      3 * L + 2 * MA + MB + 1 + e ≤ F + 2 * r + t →
      ∑ s ∈ S, |couple A B P P' L φ F r t e s
          - ideal A B P P' L (2 * L + MA + MB + 1) r t s|
        ≤ 2 * exhaust A B P P' L φ F r t e := by
  intro F
  induction F with
  | zero =>
      intro r t e S hr ht hF
      omega
  | succ F ih =>
      intro r t e S hr ht hF
      by_cases h : L < r ∨ r = t
      · rw [exhaust_stop h, mul_zero]
        refine le_of_eq (Finset.sum_eq_zero fun s _ ↦ ?_)
        rw [couple_stop h, ideal_stop h, sub_self, abs_zero]
      · by_cases he : e = 0
        · rw [exhaust_exh h he, mul_one]
          calc ∑ s ∈ S, |couple A B P P' L φ (F + 1) r t e s
                - ideal A B P P' L (2 * L + MA + MB + 1) r t s|
              ≤ ∑ s ∈ S, ((if s = r then 1 else 0)
                  + ideal A B P P' L (2 * L + MA + MB + 1) r t s) := by
                refine Finset.sum_le_sum fun s _ ↦ ?_
                rw [couple_exh h he]
                have h1 : (0 : ℝ) ≤ if s = r then 1 else 0 := by split <;> norm_num
                have h2 := ideal_nonneg (L := L) hP hP' (2 * L + MA + MB + 1) r t s
                rw [abs_sub_le_iff]
                constructor <;> linarith
            _ = (∑ s ∈ S, if s = r then (1 : ℝ) else 0)
                + ∑ s ∈ S, ideal A B P P' L (2 * L + MA + MB + 1) r t s :=
                Finset.sum_add_distrib
            _ ≤ 1 + 1 := by
                gcongr
                · rw [Finset.sum_ite_eq' S r fun _ ↦ (1 : ℝ)]
                  split <;> norm_num
                · exact ideal_sum_le_one hP hP' hP1 hP'1 _ r t S
            _ = 2 := by norm_num
        · by_cases hrt : r < t
          · -- one real descent: failure keeps the state, success advances it
            have hkey : ∀ s ∈ S, |couple A B P P' L φ (F + 1) r t e s
                - ideal A B P P' L (2 * L + MA + MB + 1) r t s|
                ≤ φ * |couple A B P P' L φ F r t (e - 1) s
                    - ideal A B P P' L (2 * L + MA + MB + 1) r t s|
                  + (1 - φ) * ∑ x ∈ A, P x * |couple A B P P' L φ F (r + x) t (e + x) s
                    - ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s| := by
              intro s _
              rw [couple_left h he hrt]
              have hD := idealFix_left (P := P) (P' := P') hMA hMB hA0 hB0 h hrt ht (s := s)
              have hsplit : ∑ x ∈ A, P x * (couple A B P P' L φ F (r + x) t (e + x) s
                    - ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s)
                  = (∑ x ∈ A, P x * couple A B P P' L φ F (r + x) t (e + x) s)
                    - ∑ x ∈ A, P x * ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s := by
                rw [← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun x _ ↦ by ring
              have harg : φ * couple A B P P' L φ F r t (e - 1) s
                  + (1 - φ) * ∑ x ∈ A, P x * couple A B P P' L φ F (r + x) t (e + x) s
                  - ideal A B P P' L (2 * L + MA + MB + 1) r t s
                  = φ * (couple A B P P' L φ F r t (e - 1) s
                      - ideal A B P P' L (2 * L + MA + MB + 1) r t s)
                    + (1 - φ) * ∑ x ∈ A, P x * (couple A B P P' L φ F (r + x) t (e + x) s
                      - ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s) := by
                rw [hsplit, ← hD]
                ring
              rw [harg]
              calc |φ * (couple A B P P' L φ F r t (e - 1) s
                    - ideal A B P P' L (2 * L + MA + MB + 1) r t s)
                  + (1 - φ) * ∑ x ∈ A, P x * (couple A B P P' L φ F (r + x) t (e + x) s
                    - ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s)|
                  ≤ |φ * (couple A B P P' L φ F r t (e - 1) s
                      - ideal A B P P' L (2 * L + MA + MB + 1) r t s)|
                    + |(1 - φ) * ∑ x ∈ A, P x * (couple A B P P' L φ F (r + x) t (e + x) s
                      - ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s)| :=
                    abs_add_le _ _
                _ ≤ φ * |couple A B P P' L φ F r t (e - 1) s
                      - ideal A B P P' L (2 * L + MA + MB + 1) r t s|
                    + (1 - φ) * ∑ x ∈ A, P x * |couple A B P P' L φ F (r + x) t (e + x) s
                      - ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s| := by
                    rw [abs_mul, abs_mul, abs_of_nonneg hφ0,
                      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - φ)]
                    gcongr
                    calc |∑ x ∈ A, P x * (couple A B P P' L φ F (r + x) t (e + x) s
                          - ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s)|
                        ≤ ∑ x ∈ A, |P x * (couple A B P P' L φ F (r + x) t (e + x) s
                          - ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s)| :=
                          Finset.abs_sum_le_sum_abs _ _
                      _ = ∑ x ∈ A, P x * |couple A B P P' L φ F (r + x) t (e + x) s
                          - ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s| :=
                          Finset.sum_congr rfl fun x hx ↦ by
                            rw [abs_mul, abs_of_nonneg (hP x hx)]
            calc ∑ s ∈ S, |couple A B P P' L φ (F + 1) r t e s
                - ideal A B P P' L (2 * L + MA + MB + 1) r t s|
                ≤ ∑ s ∈ S, (φ * |couple A B P P' L φ F r t (e - 1) s
                    - ideal A B P P' L (2 * L + MA + MB + 1) r t s|
                  + (1 - φ) * ∑ x ∈ A, P x * |couple A B P P' L φ F (r + x) t (e + x) s
                    - ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s|) :=
                  Finset.sum_le_sum hkey
              _ = φ * ∑ s ∈ S, |couple A B P P' L φ F r t (e - 1) s
                    - ideal A B P P' L (2 * L + MA + MB + 1) r t s|
                  + (1 - φ) * ∑ x ∈ A, P x * ∑ s ∈ S,
                      |couple A B P P' L φ F (r + x) t (e + x) s
                        - ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s| := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
                  congr 1
                  rw [Finset.sum_comm]
                  exact congrArg _ (Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum ..).symm)
              _ ≤ φ * (2 * exhaust A B P P' L φ F r t (e - 1))
                  + (1 - φ) * ∑ x ∈ A, P x *
                      (2 * exhaust A B P P' L φ F (r + x) t (e + x)) := by
                  have h1 := ih r t (e - 1) S hr ht (by omega)
                  have h2 : ∀ x ∈ A, ∑ s ∈ S, |couple A B P P' L φ F (r + x) t (e + x) s
                      - ideal A B P P' L (2 * L + MA + MB + 1) (r + x) t s|
                      ≤ 2 * exhaust A B P P' L φ F (r + x) t (e + x) := fun x hx ↦
                    ih (r + x) t (e + x) S (by have := hMA x hx; omega) ht
                      (by have := hA0 x hx; omega)
                  have hle1 := mul_le_mul_of_nonneg_left h1 hφ0
                  have hle2 := mul_le_mul_of_nonneg_left
                    (Finset.sum_le_sum fun x hx ↦
                      mul_le_mul_of_nonneg_left (h2 x hx) (hP x hx))
                    (by linarith : (0 : ℝ) ≤ 1 - φ)
                  linarith
              _ = 2 * exhaust A B P P' L φ (F + 1) r t e := by
                  have hsum2 : ∑ x ∈ A, P x *
                      (2 * exhaust A B P P' L φ F (r + x) t (e + x))
                      = 2 * ∑ x ∈ A, P x * exhaust A B P P' L φ F (r + x) t (e + x) := by
                    rw [Finset.mul_sum]
                    exact Finset.sum_congr rfl fun x _ ↦ by ring
                  rw [hsum2, exhaust_left h he hrt]
                  ring
          · -- the simulated side moves, no descent
            have hkey : ∀ s ∈ S, |couple A B P P' L φ (F + 1) r t e s
                - ideal A B P P' L (2 * L + MA + MB + 1) r t s|
                ≤ ∑ y ∈ B, P' y * |couple A B P P' L φ F r (t + y) e s
                    - ideal A B P P' L (2 * L + MA + MB + 1) r (t + y) s| := by
              intro s _
              rw [couple_right h he hrt]
              have hD := idealFix_right (P := P) (P' := P') hMA hMB hA0 hB0 h hrt hr (s := s)
              have harg : ∑ y ∈ B, P' y * couple A B P P' L φ F r (t + y) e s
                  - ideal A B P P' L (2 * L + MA + MB + 1) r t s
                  = ∑ y ∈ B, P' y * (couple A B P P' L φ F r (t + y) e s
                      - ideal A B P P' L (2 * L + MA + MB + 1) r (t + y) s) := by
                rw [show ∑ y ∈ B, P' y * (couple A B P P' L φ F r (t + y) e s
                      - ideal A B P P' L (2 * L + MA + MB + 1) r (t + y) s)
                    = (∑ y ∈ B, P' y * couple A B P P' L φ F r (t + y) e s)
                      - ∑ y ∈ B, P' y * ideal A B P P' L (2 * L + MA + MB + 1) r (t + y) s by
                    rw [← Finset.sum_sub_distrib]
                    exact Finset.sum_congr rfl fun y _ ↦ by ring, ← hD]
              rw [harg]
              calc |∑ y ∈ B, P' y * (couple A B P P' L φ F r (t + y) e s
                    - ideal A B P P' L (2 * L + MA + MB + 1) r (t + y) s)|
                  ≤ ∑ y ∈ B, |P' y * (couple A B P P' L φ F r (t + y) e s
                    - ideal A B P P' L (2 * L + MA + MB + 1) r (t + y) s)| :=
                    Finset.abs_sum_le_sum_abs _ _
                _ = ∑ y ∈ B, P' y * |couple A B P P' L φ F r (t + y) e s
                    - ideal A B P P' L (2 * L + MA + MB + 1) r (t + y) s| :=
                    Finset.sum_congr rfl fun y hy ↦ by
                      rw [abs_mul, abs_of_nonneg (hP' y hy)]
            calc ∑ s ∈ S, |couple A B P P' L φ (F + 1) r t e s
                - ideal A B P P' L (2 * L + MA + MB + 1) r t s|
                ≤ ∑ s ∈ S, ∑ y ∈ B, P' y * |couple A B P P' L φ F r (t + y) e s
                    - ideal A B P P' L (2 * L + MA + MB + 1) r (t + y) s| :=
                  Finset.sum_le_sum hkey
              _ = ∑ y ∈ B, P' y * ∑ s ∈ S, |couple A B P P' L φ F r (t + y) e s
                    - ideal A B P P' L (2 * L + MA + MB + 1) r (t + y) s| := by
                  rw [Finset.sum_comm]
                  exact Finset.sum_congr rfl fun y _ ↦ (Finset.mul_sum ..).symm
              _ ≤ ∑ y ∈ B, P' y * (2 * exhaust A B P P' L φ F r (t + y) e) := by
                  have h2 : ∀ y ∈ B, ∑ s ∈ S, |couple A B P P' L φ F r (t + y) e s
                      - ideal A B P P' L (2 * L + MA + MB + 1) r (t + y) s|
                      ≤ 2 * exhaust A B P P' L φ F r (t + y) e := fun y hy ↦
                    ih r (t + y) e S hr (by have h1 := hMB y hy; omega)
                      (by have := hB0 y hy; omega)
                  exact Finset.sum_le_sum fun y hy ↦
                    mul_le_mul_of_nonneg_left (h2 y hy) (hP' y hy)
              _ = 2 * exhaust A B P P' L φ (F + 1) r t e := by
                  have hsum2 : ∑ y ∈ B, P' y * (2 * exhaust A B P P' L φ F r (t + y) e)
                      = 2 * ∑ y ∈ B, P' y * exhaust A B P P' L φ F r (t + y) e := by
                    rw [Finset.mul_sum]
                    exact Finset.sum_congr rfl fun y _ ↦ by ring
                  rw [hsum2, exhaust_right h he hrt]

/-! #### Support and totality of the realised rule -/

lemma couple_sum_le_one (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ (F r t e : ℕ) (S : Finset ℕ), ∑ s ∈ S, couple A B P P' L φ F r t e s ≤ 1 := by
  intro F
  induction F with
  | zero => intro r t e S; simp [couple]
  | succ F ih =>
      intro r t e S
      have hind : ∀ r' : ℕ, ∑ s ∈ S, (if s = r' then (1 : ℝ) else 0) ≤ 1 := by
        intro r'
        rw [Finset.sum_ite_eq' S r' fun _ ↦ (1 : ℝ)]
        split <;> norm_num
      by_cases h : L < r ∨ r = t
      · calc ∑ s ∈ S, couple A B P P' L φ (F + 1) r t e s
            = ∑ s ∈ S, if s = r then (1 : ℝ) else 0 :=
              Finset.sum_congr rfl fun s _ ↦ couple_stop h
          _ ≤ 1 := hind r
      · by_cases he : e = 0
        · calc ∑ s ∈ S, couple A B P P' L φ (F + 1) r t e s
              = ∑ s ∈ S, if s = r then (1 : ℝ) else 0 :=
                Finset.sum_congr rfl fun s _ ↦ couple_exh h he
            _ ≤ 1 := hind r
        · by_cases hrt : r < t
          · calc ∑ s ∈ S, couple A B P P' L φ (F + 1) r t e s
                = φ * ∑ s ∈ S, couple A B P P' L φ F r t (e - 1) s
                  + (1 - φ) * ∑ x ∈ A, P x *
                      ∑ s ∈ S, couple A B P P' L φ F (r + x) t (e + x) s := by
                  simp only [couple_left h he hrt]
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
                  congr 1
                  rw [Finset.sum_comm]
                  exact congrArg _ (Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum ..).symm)
              _ ≤ φ * 1 + (1 - φ) * ∑ x ∈ A, P x * 1 := by
                  have h1 := ih r t (e - 1) S
                  have h2 := Finset.sum_le_sum fun x (hx : x ∈ A) ↦
                    mul_le_mul_of_nonneg_left (ih (r + x) t (e + x) S) (hP x hx)
                  have h3 := mul_le_mul_of_nonneg_left h1 hφ0
                  have h4 := mul_le_mul_of_nonneg_left h2
                    (by linarith : (0 : ℝ) ≤ 1 - φ)
                  linarith
              _ = 1 := by rw [← Finset.sum_mul, hP1]; ring
          · calc ∑ s ∈ S, couple A B P P' L φ (F + 1) r t e s
                = ∑ y ∈ B, P' y * ∑ s ∈ S, couple A B P P' L φ F r (t + y) e s := by
                  simp only [couple_right h he hrt]
                  rw [Finset.sum_comm]
                  exact Finset.sum_congr rfl fun y _ ↦ (Finset.mul_sum ..).symm
              _ ≤ ∑ y ∈ B, P' y * 1 :=
                  Finset.sum_le_sum fun y hy ↦
                    mul_le_mul_of_nonneg_left (ih r (t + y) e S) (hP' y hy)
              _ = 1 := by rw [← Finset.sum_mul, hP'1, one_mul]

/-- With enough fuel the realised rule has stopped. -/
lemma couple_sum_eq_one {MA MB : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) (hMB : ∀ b ∈ B, b ≤ MB)
    (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1) :
    ∀ F r t e, r ≤ L + MA → t ≤ L + MB →
      3 * L + 2 * MA + MB + 1 + e ≤ F + 2 * r + t →
      ∑ s ∈ Finset.range (L + MA + 1), couple A B P P' L φ F r t e s = 1 := by
  intro F
  induction F with
  | zero =>
      intro r t e hr ht hF
      omega
  | succ F ih =>
      intro r t e hr ht hF
      have hind : ∀ r' : ℕ, r' ≤ L + MA →
          ∑ s ∈ Finset.range (L + MA + 1), (if s = r' then (1 : ℝ) else 0) = 1 := by
        intro r' hr'
        rw [Finset.sum_ite_eq' (Finset.range (L + MA + 1)) r' fun _ ↦ (1 : ℝ),
          if_pos (Finset.mem_range.mpr (by omega))]
      by_cases h : L < r ∨ r = t
      · calc ∑ s ∈ Finset.range (L + MA + 1), couple A B P P' L φ (F + 1) r t e s
            = ∑ s ∈ Finset.range (L + MA + 1), if s = r then (1 : ℝ) else 0 :=
              Finset.sum_congr rfl fun s _ ↦ couple_stop h
          _ = 1 := hind r hr
      · by_cases he : e = 0
        · calc ∑ s ∈ Finset.range (L + MA + 1), couple A B P P' L φ (F + 1) r t e s
              = ∑ s ∈ Finset.range (L + MA + 1), if s = r then (1 : ℝ) else 0 :=
                Finset.sum_congr rfl fun s _ ↦ couple_exh h he
            _ = 1 := hind r hr
        · by_cases hrt : r < t
          · calc ∑ s ∈ Finset.range (L + MA + 1), couple A B P P' L φ (F + 1) r t e s
                = φ * ∑ s ∈ Finset.range (L + MA + 1), couple A B P P' L φ F r t (e - 1) s
                  + (1 - φ) * ∑ x ∈ A, P x * ∑ s ∈ Finset.range (L + MA + 1),
                      couple A B P P' L φ F (r + x) t (e + x) s := by
                  simp only [couple_left h he hrt]
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
                  congr 1
                  rw [Finset.sum_comm]
                  exact congrArg _ (Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum ..).symm)
              _ = φ * 1 + (1 - φ) * ∑ x ∈ A, P x * 1 := by
                  rw [ih r t (e - 1) hr ht (by omega)]
                  congr 2
                  refine Finset.sum_congr rfl fun x hx ↦ ?_
                  rw [ih (r + x) t (e + x) (by have := hMA x hx; omega) ht
                    (by have := hA0 x hx; omega)]
              _ = 1 := by rw [← Finset.sum_mul, hP1]; ring
          · calc ∑ s ∈ Finset.range (L + MA + 1), couple A B P P' L φ (F + 1) r t e s
                = ∑ y ∈ B, P' y * ∑ s ∈ Finset.range (L + MA + 1),
                    couple A B P P' L φ F r (t + y) e s := by
                  simp only [couple_right h he hrt]
                  rw [Finset.sum_comm]
                  exact Finset.sum_congr rfl fun y _ ↦ (Finset.mul_sum ..).symm
              _ = ∑ y ∈ B, P' y * 1 := by
                  refine Finset.sum_congr rfl fun y hy ↦ ?_
                  rw [ih r (t + y) e hr (by have := hMB y hy; omega)
                    (by have := hB0 y hy; omega)]
              _ = 1 := by rw [← Finset.sum_mul, hP'1, one_mul]

/-- Stops of the realised rule lie in the semigroup. -/
lemma couple_eq_zero_of_notMem {s : ℕ} :
    ∀ F r t e, r ∈ AddSubmonoid.closure (A : Set ℕ) →
      s ∉ AddSubmonoid.closure (A : Set ℕ) → couple A B P P' L φ F r t e s = 0 := by
  intro F
  induction F with
  | zero => intro r t e _ _; simp [couple]
  | succ F ih =>
      intro r t e hr hs
      have hind : (if s = r then (1 : ℝ) else 0) = 0 :=
        if_neg fun hsr ↦ hs (by rw [hsr]; exact hr)
      by_cases h : L < r ∨ r = t
      · rw [couple_stop h, hind]
      · by_cases he : e = 0
        · rw [couple_exh h he, hind]
        · by_cases hrt : r < t
          · rw [couple_left h he hrt, ih r t (e - 1) hr hs]
            rw [Finset.sum_eq_zero fun x hx ↦ by
              rw [ih (r + x) t (e + x) (AddSubmonoid.add_mem _ hr
                (AddSubmonoid.subset_closure hx)) hs, mul_zero]]
            ring
          · rw [couple_right h he hrt]
            exact Finset.sum_eq_zero fun y _ ↦ by
              rw [ih r (t + y) e hr hs, mul_zero]

/-- Stops of the realised rule lie at or below `L + MA`. -/
lemma couple_eq_zero_of_gt {MA : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) {s : ℕ} :
    ∀ F r t e, r ≤ L + MA → L + MA < s → couple A B P P' L φ F r t e s = 0 := by
  intro F
  induction F with
  | zero => intro r t e _ _; simp [couple]
  | succ F ih =>
      intro r t e hr hs
      have hind : (if s = r then (1 : ℝ) else 0) = 0 := if_neg (by omega)
      by_cases h : L < r ∨ r = t
      · rw [couple_stop h, hind]
      · have hrL : ¬ L < r := fun hc ↦ h (Or.inl hc)
        by_cases he : e = 0
        · rw [couple_exh h he, hind]
        · by_cases hrt : r < t
          · rw [couple_left h he hrt, ih r t (e - 1) hr hs]
            rw [Finset.sum_eq_zero fun x hx ↦ by
              rw [ih (r + x) t (e + x) (by have := hMA x hx; omega) hs, mul_zero]]
            ring
          · rw [couple_right h he hrt]
            exact Finset.sum_eq_zero fun y _ ↦ by
              rw [ih r (t + y) e hr hs, mul_zero]

/-- Stops of the realised rule lie at or above the current total. -/
lemma couple_eq_zero_of_lt {s : ℕ} :
    ∀ F r t e, s < r → couple A B P P' L φ F r t e s = 0 := by
  intro F
  induction F with
  | zero => intro r t e _; simp [couple]
  | succ F ih =>
      intro r t e hsr
      have hind : (if s = r then (1 : ℝ) else 0) = 0 := if_neg (by omega)
      by_cases h : L < r ∨ r = t
      · rw [couple_stop h, hind]
      · by_cases he : e = 0
        · rw [couple_exh h he, hind]
        · by_cases hrt : r < t
          · rw [couple_left h he hrt, ih r t (e - 1) hsr]
            rw [Finset.sum_eq_zero fun x hx ↦ by
              rw [ih (r + x) t (e + x) (by omega), mul_zero]]
            ring
          · rw [couple_right h he hrt]
            exact Finset.sum_eq_zero fun y _ ↦ by
              rw [ih r (t + y) e hsr, mul_zero]

end Couple

/-! ### The free exploration

The rule ignores the other law: it stops with probability one half after each
absorption, stops outright past `L`, and otherwise descends, failing with
probability `φ`.  Its stops realise every total of the truncated semigroup with
mass bounded below. -/

section Free

variable (A : Finset ℕ) (P : ℕ → ℝ) (L : ℕ) (φ : ℝ)

/-- The stop law of the free exploration from total `r` with `e` unspent
exits. -/
noncomputable def free : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, _, _, _ => 0
  | F + 1, r, e, s =>
      if L < r then (if s = r then 1 else 0)
      else if e = 0 then (if s = r then 1 else 0)
      else (1 / 2) * (if s = r then 1 else 0)
        + (1 / 2) * (φ * free F r (e - 1) s
          + (1 - φ) * ∑ x ∈ A, P x * free F (r + x) (e + x) s)

variable {A P L φ}

lemma free_stop {F r e s : ℕ} (h : L < r) :
    free A P L φ (F + 1) r e s = if s = r then 1 else 0 := by
  rw [free, if_pos h]

lemma free_exh {F r e s : ℕ} (h : ¬ L < r) (he : e = 0) :
    free A P L φ (F + 1) r e s = if s = r then 1 else 0 := by
  rw [free, if_neg h, if_pos he]

lemma free_step {F r e s : ℕ} (h : ¬ L < r) (he : ¬ e = 0) :
    free A P L φ (F + 1) r e s
      = (1 / 2) * (if s = r then 1 else 0)
        + (1 / 2) * (φ * free A P L φ F r (e - 1) s
          + (1 - φ) * ∑ x ∈ A, P x * free A P L φ F (r + x) (e + x) s) := by
  rw [free, if_neg h, if_neg he]

lemma free_nonneg (hP : ∀ a ∈ A, 0 ≤ P a) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ F r e s, 0 ≤ free A P L φ F r e s := by
  intro F
  induction F with
  | zero => intro r e s; simp [free]
  | succ F ih =>
      intro r e s
      rw [free]
      split
      · positivity
      · split
        · positivity
        · have h1 := Finset.sum_nonneg fun x hx ↦
            mul_nonneg (hP x hx) (ih (r + x) (e + x) s)
          have h2 := ih r (e - 1) s
          have h3 : (0 : ℝ) ≤ if s = r then 1 else 0 := by split <;> norm_num
          nlinarith

lemma free_sum_le_one (hP : ∀ a ∈ A, 0 ≤ P a) (hP1 : ∑ a ∈ A, P a = 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ (F r e : ℕ) (S : Finset ℕ), ∑ s ∈ S, free A P L φ F r e s ≤ 1 := by
  intro F
  induction F with
  | zero => intro r e S; simp [free]
  | succ F ih =>
      intro r e S
      have hind : ∀ r' : ℕ, ∑ s ∈ S, (if s = r' then (1 : ℝ) else 0) ≤ 1 := by
        intro r'
        rw [Finset.sum_ite_eq' S r' fun _ ↦ (1 : ℝ)]
        split <;> norm_num
      by_cases h : L < r
      · calc ∑ s ∈ S, free A P L φ (F + 1) r e s
            = ∑ s ∈ S, if s = r then (1 : ℝ) else 0 :=
              Finset.sum_congr rfl fun s _ ↦ free_stop h
          _ ≤ 1 := hind r
      · by_cases he : e = 0
        · calc ∑ s ∈ S, free A P L φ (F + 1) r e s
              = ∑ s ∈ S, if s = r then (1 : ℝ) else 0 :=
                Finset.sum_congr rfl fun s _ ↦ free_exh h he
            _ ≤ 1 := hind r
        · calc ∑ s ∈ S, free A P L φ (F + 1) r e s
              = (1 / 2) * ∑ s ∈ S, (if s = r then (1 : ℝ) else 0)
                + (1 / 2) * (φ * ∑ s ∈ S, free A P L φ F r (e - 1) s
                  + (1 - φ) * ∑ x ∈ A, P x * ∑ s ∈ S, free A P L φ F (r + x) (e + x) s) := by
                simp only [free_step h he]
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
                have hswap : ∑ s ∈ S, (φ * free A P L φ F r (e - 1) s
                      + (1 - φ) * ∑ x ∈ A, P x * free A P L φ F (r + x) (e + x) s)
                    = φ * ∑ s ∈ S, free A P L φ F r (e - 1) s
                      + (1 - φ) * ∑ x ∈ A, P x *
                          ∑ s ∈ S, free A P L φ F (r + x) (e + x) s := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
                  congr 1
                  rw [Finset.sum_comm]
                  exact congrArg _ (Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum ..).symm)
                rw [hswap]
            _ ≤ (1 / 2) * 1 + (1 / 2) * (φ * 1 + (1 - φ) * ∑ x ∈ A, P x * 1) := by
                have h1 := hind r
                have h2 := ih r (e - 1) S
                have h3 := Finset.sum_le_sum fun x (hx : x ∈ A) ↦
                  mul_le_mul_of_nonneg_left (ih (r + x) (e + x) S) (hP x hx)
                have h4 := mul_le_mul_of_nonneg_left h2 hφ0
                have h5 := mul_le_mul_of_nonneg_left h3
                  (by linarith : (0 : ℝ) ≤ 1 - φ)
                nlinarith
            _ = 1 := by rw [← Finset.sum_mul, hP1]; ring

/-- With enough fuel the free rule has stopped. -/
lemma free_sum_eq_one {MA : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) (hA0 : ∀ a ∈ A, 0 < a)
    (hP1 : ∑ a ∈ A, P a = 1) :
    ∀ F r e, r ≤ L + MA → 2 * L + 2 * MA + 1 + e ≤ F + 2 * r →
      ∑ s ∈ Finset.range (L + MA + 1), free A P L φ F r e s = 1 := by
  intro F
  induction F with
  | zero =>
      intro r e hr hF
      omega
  | succ F ih =>
      intro r e hr hF
      have hind : ∀ r' : ℕ, r' ≤ L + MA →
          ∑ s ∈ Finset.range (L + MA + 1), (if s = r' then (1 : ℝ) else 0) = 1 := by
        intro r' hr'
        rw [Finset.sum_ite_eq' (Finset.range (L + MA + 1)) r' fun _ ↦ (1 : ℝ),
          if_pos (Finset.mem_range.mpr (by omega))]
      by_cases h : L < r
      · calc ∑ s ∈ Finset.range (L + MA + 1), free A P L φ (F + 1) r e s
            = ∑ s ∈ Finset.range (L + MA + 1), if s = r then (1 : ℝ) else 0 :=
              Finset.sum_congr rfl fun s _ ↦ free_stop h
          _ = 1 := hind r hr
      · by_cases he : e = 0
        · calc ∑ s ∈ Finset.range (L + MA + 1), free A P L φ (F + 1) r e s
              = ∑ s ∈ Finset.range (L + MA + 1), if s = r then (1 : ℝ) else 0 :=
                Finset.sum_congr rfl fun s _ ↦ free_exh h he
            _ = 1 := hind r hr
        · calc ∑ s ∈ Finset.range (L + MA + 1), free A P L φ (F + 1) r e s
              = (1 / 2) * ∑ s ∈ Finset.range (L + MA + 1), (if s = r then (1 : ℝ) else 0)
                + (1 / 2) * (φ * ∑ s ∈ Finset.range (L + MA + 1), free A P L φ F r (e - 1) s
                  + (1 - φ) * ∑ x ∈ A, P x * ∑ s ∈ Finset.range (L + MA + 1),
                      free A P L φ F (r + x) (e + x) s) := by
                simp only [free_step h he]
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
                have hswap : ∑ s ∈ Finset.range (L + MA + 1),
                      (φ * free A P L φ F r (e - 1) s
                        + (1 - φ) * ∑ x ∈ A, P x * free A P L φ F (r + x) (e + x) s)
                    = φ * ∑ s ∈ Finset.range (L + MA + 1), free A P L φ F r (e - 1) s
                      + (1 - φ) * ∑ x ∈ A, P x * ∑ s ∈ Finset.range (L + MA + 1),
                          free A P L φ F (r + x) (e + x) s := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
                  congr 1
                  rw [Finset.sum_comm]
                  exact congrArg _ (Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum ..).symm)
                rw [hswap]
            _ = (1 / 2) * 1 + (1 / 2) * (φ * 1 + (1 - φ) * ∑ x ∈ A, P x * 1) := by
                have hxall : ∑ x ∈ A, P x * ∑ s ∈ Finset.range (L + MA + 1),
                    free A P L φ F (r + x) (e + x) s = ∑ x ∈ A, P x * 1 :=
                  Finset.sum_congr rfl fun x hx ↦ by
                    rw [ih (r + x) (e + x) (by have := hMA x hx; omega)
                      (by have := hA0 x hx; omega)]
                rw [hind r (by omega), ih r (e - 1) hr (by omega), hxall]
            _ = 1 := by rw [← Finset.sum_mul, hP1]; ring

lemma free_eq_zero_of_notMem {s : ℕ} :
    ∀ F r e, r ∈ AddSubmonoid.closure (A : Set ℕ) →
      s ∉ AddSubmonoid.closure (A : Set ℕ) → free A P L φ F r e s = 0 := by
  intro F
  induction F with
  | zero => intro r e _ _; simp [free]
  | succ F ih =>
      intro r e hr hs
      have hind : (if s = r then (1 : ℝ) else 0) = 0 :=
        if_neg fun hsr ↦ hs (by rw [hsr]; exact hr)
      by_cases h : L < r
      · rw [free_stop h, hind]
      · by_cases he : e = 0
        · rw [free_exh h he, hind]
        · rw [free_step h he, hind, ih r (e - 1) hr hs]
          rw [Finset.sum_eq_zero fun x hx ↦ by
            rw [ih (r + x) (e + x) (AddSubmonoid.add_mem _ hr
              (AddSubmonoid.subset_closure hx)) hs, mul_zero]]
          ring

lemma free_eq_zero_of_gt {MA : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) {s : ℕ} :
    ∀ F r e, r ≤ L + MA → L + MA < s → free A P L φ F r e s = 0 := by
  intro F
  induction F with
  | zero => intro r e _ _; simp [free]
  | succ F ih =>
      intro r e hr hs
      have hind : (if s = r then (1 : ℝ) else 0) = 0 := if_neg (by omega)
      by_cases h : L < r
      · rw [free_stop h, hind]
      · by_cases he : e = 0
        · rw [free_exh h he, hind]
        · rw [free_step h he, hind, ih r (e - 1) hr hs]
          rw [Finset.sum_eq_zero fun x hx ↦ by
            rw [ih (r + x) (e + x) (by have := hMA x hx; omega) hs, mul_zero]]
          ring

lemma free_eq_zero_of_lt {s : ℕ} :
    ∀ F r e, s < r → free A P L φ F r e s = 0 := by
  intro F
  induction F with
  | zero => intro r e _; simp [free]
  | succ F ih =>
      intro r e hsr
      have hind : (if s = r then (1 : ℝ) else 0) = 0 := if_neg (by omega)
      by_cases h : L < r
      · rw [free_stop h, hind]
      · by_cases he : e = 0
        · rw [free_exh h he, hind]
        · rw [free_step h he, hind, ih r (e - 1) hsr]
          rw [Finset.sum_eq_zero fun x hx ↦ by
            rw [ih (r + x) (e + x) (by omega), mul_zero]]
          ring

/-- The free rule stops at its current total with probability at least one
half. -/
lemma free_self_ge (hP : ∀ a ∈ A, 0 ≤ P a) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    {F r e : ℕ} (h : ¬ L < r) :
    (1 / 2 : ℝ) ≤ free A P L φ (F + 1) r e r := by
  by_cases he : e = 0
  · rw [free_exh h he, if_pos rfl]
    norm_num
  · rw [free_step h he, if_pos rfl]
    have h1 := free_nonneg (L := L) hP hφ0 hφ1 F r (e - 1) r
    have h2 := Finset.sum_nonneg fun x (hx : x ∈ A) ↦
      mul_nonneg (hP x hx) (free_nonneg (L := L) hP hφ0 hφ1 F (r + x) (e + x) r)
    nlinarith

/-- One prescribed successful descent keeps a mass floor. -/
lemma free_step_ge (hP : ∀ a ∈ A, 0 ≤ P a) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    {F r e s x : ℕ} (h : ¬ L < r) (he : ¬ e = 0) (hx : x ∈ A) {c : ℝ}
    (hc : c ≤ free A P L φ F (r + x) (e + x) s) :
    (1 - φ) / 2 * (P x * c) ≤ free A P L φ (F + 1) r e s := by
  rw [free_step h he]
  have h1 : (0 : ℝ) ≤ if s = r then 1 else 0 := by split <;> norm_num
  have h2 := free_nonneg (L := L) hP hφ0 hφ1 F r (e - 1) s
  have h3 : P x * c ≤ ∑ x' ∈ A, P x' * free A P L φ F (r + x') (e + x') s := by
    calc P x * c ≤ P x * free A P L φ F (r + x) (e + x) s :=
          mul_le_mul_of_nonneg_left hc (hP x hx)
      _ ≤ ∑ x' ∈ A, P x' * free A P L φ F (r + x') (e + x') s := by
          refine Finset.single_le_sum (f := fun x' ↦ P x' * free A P L φ F (r + x') (e + x') s)
            (fun x' hx' ↦ mul_nonneg (hP x' hx')
              (free_nonneg (L := L) hP hφ0 hφ1 F _ _ _)) hx
  nlinarith

/-- **The bulk floor**: a word of shifts whose total stays at or below `L` is
spelled and stopped at with probability at least
`(1/2) ((1-φ)/2)^{|w|} ∏ P`. -/
lemma free_ge_word_bulk (hP : ∀ a ∈ A, 0 ≤ P a) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ (w : List ℕ) (F r e : ℕ), (∀ x ∈ w, x ∈ A) → w.length < F → e ≠ 0 →
      r + w.sum ≤ L →
      (1 / 2) * ((1 - φ) / 2) ^ w.length * (w.map P).prod
        ≤ free A P L φ F r e (r + w.sum) := by
  intro w
  induction w with
  | nil =>
      intro F r e _ hF he hr
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [List.sum_nil, Nat.add_zero, List.length_nil, pow_zero, List.map_nil,
        List.prod_nil, mul_one]
      refine free_self_ge hP hφ0 hφ1 ?_
      simp only [List.sum_nil, Nat.add_zero] at hr
      omega
  | cons x w ih =>
      intro F r e hw hF he hr
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hx : x ∈ A := hw x List.mem_cons_self
      have hsum : r + (x :: w).sum = (r + x) + w.sum := by
        simp only [List.sum_cons]
        omega
      rw [hsum]
      have hc := ih F' (r + x) (e + x) (fun x' hx' ↦ hw x' (List.mem_cons_of_mem x hx'))
        (by simp only [List.length_cons] at hF; omega) (by omega)
        (by rw [← hsum]; exact hr)
      have heq : (1 / 2) * ((1 - φ) / 2) ^ (x :: w).length * ((x :: w).map P).prod
          = (1 - φ) / 2 * (P x * ((1 / 2) * ((1 - φ) / 2) ^ w.length * (w.map P).prod)) := by
        rw [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
        ring
      rw [heq]
      have hrL : ¬ L < r := by
        have h7 : r ≤ r + (x :: w).sum := Nat.le_add_right _ _
        omega
      exact free_step_ge hP hφ0 hφ1 hrL he hx hc

/-- **The window floor**: a word whose total stays at or below `L` followed by
one more shift past `L` is spelled and stopped at with probability at least
`((1-φ)/2)^{|w|+1} ∏ P`. -/
lemma free_ge_word_window (hP : ∀ a ∈ A, 0 ≤ P a) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    ∀ (w : List ℕ) (z F r e : ℕ), (∀ x ∈ w, x ∈ A) → z ∈ A →
      w.length + 1 < F → e ≠ 0 → r + w.sum ≤ L → L < r + w.sum + z →
      ((1 - φ) / 2) ^ (w.length + 1) * ((w.map P).prod * P z)
        ≤ free A P L φ F r e (r + w.sum + z) := by
  intro w
  induction w with
  | nil =>
      intro z F r e _ hz hF he hr hLz
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
      simp only [List.sum_nil, Nat.add_zero, List.length_nil, List.map_nil,
        List.prod_nil, one_mul, zero_add, pow_one] at hr hLz ⊢
      have hstop : free A P L φ (F'' + 1) (r + z) (e + z) (r + z) = 1 := by
        rw [free_stop (by omega), if_pos rfl]
      have hc := free_step_ge hP hφ0 hφ1 (by omega) he hz
        (c := 1) (le_of_eq hstop.symm)
      calc (1 - φ) / 2 * P z = (1 - φ) / 2 * (P z * 1) := by ring
        _ ≤ free A P L φ (F'' + 1 + 1) r e (r + z) := hc
  | cons x w ih =>
      intro z F r e hw hz hF he hr hLz
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hx : x ∈ A := hw x List.mem_cons_self
      have hsum : r + (x :: w).sum + z = ((r + x) + w.sum) + z := by
        simp only [List.sum_cons]
        omega
      rw [hsum]
      have hc := ih z F' (r + x) (e + x) (fun x' hx' ↦ hw x' (List.mem_cons_of_mem x hx'))
        hz (by simp only [List.length_cons] at hF; omega) (by omega)
        (by simp only [List.sum_cons] at hr ⊢; omega)
        (by simp only [List.sum_cons] at hLz ⊢; omega)
      have heq : ((1 - φ) / 2) ^ ((x :: w).length + 1) * (((x :: w).map P).prod * P z)
          = (1 - φ) / 2 * (P x * (((1 - φ) / 2) ^ (w.length + 1)
              * ((w.map P).prod * P z))) := by
        rw [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
        ring
      rw [heq]
      have hrL : ¬ L < r := by
        have h7 : r ≤ r + (x :: w).sum := Nat.le_add_right _ _
        omega
      exact free_step_ge hP hφ0 hφ1 hrL he hx hc

end Free

/-! ### The matched presentation

The presented shift law of one side: the free branch with probability `δ`,
the coupled branch otherwise, integrated over the root shift and the first
simulated increment.  The presented arity is one plus the shift. -/

section Assembly

variable (A B : Finset ℕ) (P P' : ℕ → ℝ) (L : ℕ) (φ δ : ℝ)

/-- The stop law of the free branch, integrated over the root shift. -/
noncomputable def freeLaw (F s : ℕ) : ℝ :=
  ∑ x ∈ A, P x * free A P L φ F x (x + 1) s

/-- The stop law of the coupled branch, integrated over the root shift and the
first simulated increment. -/
noncomputable def coupleLaw (F s : ℕ) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ B, P x * (P' y * couple A B P P' L φ F x y (x + 1) s)

/-- The stop law of the idealised coupled branch, at stable fuel. -/
noncomputable def idealLaw (MA MB : ℕ) (s : ℕ) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ B, P x * (P' y * ideal A B P P' L (2 * L + MA + MB + 1) x y s)

/-- **The presented shift law of the matched presentation**: free exploration
with probability `δ`, coupled exploration otherwise. -/
noncomputable def matchedShift (F s : ℕ) : ℝ :=
  δ * freeLaw A P L φ F s + (1 - δ) * coupleLaw A B P P' L φ F s

variable {A B P P' L φ δ}

/-- A list of positive naturals is at most as long as its sum. -/
lemma length_le_sum : ∀ l : List ℕ, (∀ x ∈ l, 1 ≤ x) → l.length ≤ l.sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
      intro h
      have hx := h x List.mem_cons_self
      have := ih fun x' hx' ↦ h x' (List.mem_cons_of_mem x hx')
      simp only [List.length_cons, List.sum_cons]
      omega

lemma freeLaw_sum_eq_one {MA : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) (hA0 : ∀ a ∈ A, 0 < a)
    (hP1 : ∑ a ∈ A, P a = 1) {F : ℕ} (hF : 2 * L + 2 * MA + 2 ≤ F) :
    ∑ s ∈ Finset.range (L + MA + 1), freeLaw A P L φ F s = 1 := by
  have hswap : ∑ s ∈ Finset.range (L + MA + 1), freeLaw A P L φ F s
      = ∑ x ∈ A, P x * ∑ s ∈ Finset.range (L + MA + 1), free A P L φ F x (x + 1) s := by
    simp only [freeLaw]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum ..).symm
  rw [hswap,
    Finset.sum_congr rfl fun x hx ↦ by
      rw [free_sum_eq_one hMA hA0 hP1 F x (x + 1) (by have := hMA x hx; omega)
        (by have h1 := hMA x hx; have h2 := hA0 x hx; omega)],
    ← Finset.sum_mul, hP1, one_mul]

lemma coupleLaw_sum_eq_one {MA MB : ℕ} (hMA : ∀ a ∈ A, a ≤ MA)
    (hMB : ∀ b ∈ B, b ≤ MB) (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    {F : ℕ} (hF : 3 * L + 2 * MA + MB + 2 ≤ F) :
    ∑ s ∈ Finset.range (L + MA + 1), coupleLaw A B P P' L φ F s = 1 := by
  have hswap : ∑ s ∈ Finset.range (L + MA + 1), coupleLaw A B P P' L φ F s
      = ∑ x ∈ A, ∑ y ∈ B, P x * (P' y *
          ∑ s ∈ Finset.range (L + MA + 1), couple A B P P' L φ F x y (x + 1) s) := by
    simp only [coupleLaw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hswap,
    Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun y hy ↦ by
      rw [couple_sum_eq_one hMA hMB hA0 hB0 hP1 hP'1 F x y (x + 1)
        (by have := hMA x hx; omega) (by have := hMB y hy; omega)
        (by have h1 := hA0 x hx; have h2 := hB0 y hy; omega)]]
  rw [Finset.sum_congr rfl fun x _ ↦ by
    rw [show ∑ y ∈ B, P x * (P' y * 1) = P x * ∑ y ∈ B, P' y by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ ↦ by ring, hP'1, mul_one],
    hP1]

/-- **The presented law is a law** at adequate fuel. -/
theorem matchedShift_sum_eq_one {MA MB : ℕ} (hMA : ∀ a ∈ A, a ≤ MA)
    (hMB : ∀ b ∈ B, b ≤ MB) (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    {F : ℕ} (hF : 3 * L + 2 * MA + MB + 2 ≤ F) (hF' : 2 * L + 2 * MA + 2 ≤ F) :
    ∑ s ∈ Finset.range (L + MA + 1), matchedShift A B P P' L φ δ F s = 1 := by
  simp only [matchedShift]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    freeLaw_sum_eq_one hMA hA0 hP1 hF',
    coupleLaw_sum_eq_one hMA hMB hA0 hB0 hP1 hP'1 hF]
  ring

/-! #### The support and the floor -/

/-- **The floor of the free branch**: every total of `Λ ∩ (0, L + MA]` carries
free mass at least `(1/2) p (p(1-φ)/2)^{L+MA}`, provided the window totals
retract into the semigroup. -/
theorem freeLaw_ge_of_mem {MA : ℕ} (hMAmem : MA ∈ A)
    (hA0 : ∀ a ∈ A, 0 < a) (hMAL : MA ≤ L)
    (hP : ∀ a ∈ A, 0 ≤ P a) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hPp : ∀ a ∈ A, p ≤ P a) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hwin : ∀ s' : ℕ, s' ∈ AddSubmonoid.closure (A : Set ℕ) → L < s' → s' ≤ L + MA →
      s' - MA ∈ AddSubmonoid.closure (A : Set ℕ))
    {F : ℕ} (hF : L + MA + 2 ≤ F) {s : ℕ}
    (hs : s ∈ AddSubmonoid.closure (A : Set ℕ)) (hs0 : 0 < s) (hsL : s ≤ L + MA) :
    (1 / 2) * p * (p * (1 - φ) / 2) ^ (L + MA) ≤ freeLaw A P L φ F s := by
  have hbase0 : (0 : ℝ) ≤ p * (1 - φ) / 2 := by
    have : (0 : ℝ) ≤ 1 - φ := by linarith
    positivity
  have hbase1 : p * (1 - φ) / 2 ≤ 1 := by nlinarith
  -- the prescribed event through one word
  have hmain : ∀ x₁ ∈ A, ∀ w : List ℕ, (∀ a ∈ w, a ∈ A) → x₁ + w.sum = s →
      w.length + 1 < F → (x₁ + w.sum ≤ L ∨
        (∃ w', w = w' ++ [MA] ∧ x₁ + w'.sum ≤ L ∧ L < s)) →
      (1 / 2) * p * (p * (1 - φ) / 2) ^ (L + MA) ≤ freeLaw A P L φ F s := by
    intro x₁ hx₁ w hw hsum hlen hcase
    have hword : ∀ c : ℝ, c ≤ free A P L φ F x₁ (x₁ + 1) s → 0 ≤ c →
        c * p ≤ freeLaw A P L φ F s := by
      intro c hc hc0
      calc c * p ≤ free A P L φ F x₁ (x₁ + 1) s * P x₁ := by
            have := hPp x₁ hx₁
            have := free_nonneg (L := L) hP hφ0 hφ1 F x₁ (x₁ + 1) s
            nlinarith
        _ = P x₁ * free A P L φ F x₁ (x₁ + 1) s := by ring
        _ ≤ freeLaw A P L φ F s := by
            rw [freeLaw]
            exact Finset.single_le_sum
              (f := fun x ↦ P x * free A P L φ F x (x + 1) s)
              (fun x hx ↦ mul_nonneg (hP x hx)
                (free_nonneg (L := L) hP hφ0 hφ1 F _ _ _)) hx₁
    have hprodw : ∀ w' : List ℕ, (∀ a ∈ w', a ∈ A) → p ^ w'.length ≤ (w'.map P).prod := by
      intro w' hw'
      have h := pow_length_le_prod hp0.le (w'.map P) (fun a ha ↦ by
        obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
        exact hPp a' (hw' a' ha'))
      simpa using h
    rcases hcase with hbulk | ⟨w', rfl, hw'L, hLs⟩
    · -- the bulk word
      have hfree := free_ge_word_bulk hP hφ0 hφ1 w F x₁ (x₁ + 1) hw
        (by omega) (by omega) hbulk
      rw [hsum] at hfree
      refine le_trans ?_ (hword _ hfree ?_)
      · have h1 : p ^ w.length * ((1 - φ) / 2) ^ w.length
            ≤ (w.map P).prod * ((1 - φ) / 2) ^ w.length := by
          have h2 := hprodw w hw
          have h3 : (0 : ℝ) ≤ ((1 - φ) / 2) ^ w.length :=
            pow_nonneg (by linarith) _
          nlinarith [pow_nonneg hp0.le w.length]
        have h4 : (p * (1 - φ) / 2) ^ (L + MA)
            ≤ (p * (1 - φ) / 2) ^ w.length := by
          refine pow_le_pow_of_le_one hbase0 hbase1 ?_
          have h5 : ∀ a ∈ w, 1 ≤ a := fun a ha ↦ hA0 a (hw a ha)
          have h6 := length_le_sum w h5
          omega
        have h7 : (p * (1 - φ) / 2) ^ w.length
            = p ^ w.length * ((1 - φ) / 2) ^ w.length := by
          rw [← mul_pow]
          congr 1
          ring
        calc (1 / 2) * p * (p * (1 - φ) / 2) ^ (L + MA)
            ≤ (1 / 2) * p * (p * (1 - φ) / 2) ^ w.length := by
              have : (0 : ℝ) < (1 / 2) * p := by positivity
              nlinarith
          _ = (1 / 2) * (p ^ w.length * ((1 - φ) / 2) ^ w.length) * p := by
              rw [h7]; ring
          _ ≤ (1 / 2) * ((w.map P).prod * ((1 - φ) / 2) ^ w.length) * p := by
              nlinarith
          _ = (1 / 2) * ((1 - φ) / 2) ^ w.length * (w.map P).prod * p := by ring
      · have h8 : (0 : ℝ) ≤ (w.map P).prod :=
          List.prod_nonneg fun a ha ↦ by
            obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
            exact hP a' (hw a' ha')
        have h9 : (0 : ℝ) ≤ ((1 - φ) / 2) ^ w.length := pow_nonneg (by linarith) _
        positivity
    · -- the window word: the last letter is the maximal shift
      have hzA : MA ∈ A := hMAmem
      have hwA : ∀ a ∈ w', a ∈ A := fun a ha ↦ hw a (List.mem_append_left _ ha)
      have hLz : L < x₁ + w'.sum + MA := by
        have hsumMA : (w' ++ [MA]).sum = w'.sum + MA := by simp
        omega
      have hlen' : w'.length + 1 < F := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
      have hfree := free_ge_word_window hP hφ0 hφ1 w' MA F x₁ (x₁ + 1) hwA hzA
        hlen' (by omega) hw'L hLz
      have hsum' : x₁ + w'.sum + MA = s := by
        have hsumMA : (w' ++ [MA]).sum = w'.sum + MA := by simp
        omega
      rw [hsum'] at hfree
      have h11' : (0 : ℝ) ≤ (w'.map P).prod :=
        List.prod_nonneg fun a ha ↦ by
          obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
          exact hP a' (hwA a' ha')
      refine le_trans ?_ (hword _ hfree ?_)
      · have h4 : (p * (1 - φ) / 2) ^ (L + MA)
            ≤ (p * (1 - φ) / 2) ^ (w'.length + 1) := by
          refine pow_le_pow_of_le_one hbase0 hbase1 ?_
          have h5 : ∀ a ∈ w', 1 ≤ a := fun a ha ↦ hA0 a (hwA a ha)
          have h6 := length_le_sum w' h5
          omega
        have h7 : (p * (1 - φ) / 2) ^ (w'.length + 1)
            = p ^ (w'.length + 1) * ((1 - φ) / 2) ^ (w'.length + 1) := by
          rw [← mul_pow]
          congr 1
          ring
        have h2 := hprodw w' hwA
        have h9 : (0 : ℝ) ≤ ((1 - φ) / 2) ^ (w'.length + 1) :=
          pow_nonneg (by linarith) _
        have h10 : p ^ (w'.length + 1) = p ^ w'.length * p := pow_succ p _
        have h11 : (0 : ℝ) ≤ (w'.map P).prod :=
          List.prod_nonneg fun a ha ↦ by
            obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
            exact hP a' (hwA a' ha')
        have h12 : p ≤ P MA := hPp MA hzA
        calc (1 / 2) * p * (p * (1 - φ) / 2) ^ (L + MA)
            ≤ (1 / 2) * p * (p * (1 - φ) / 2) ^ (w'.length + 1) := by
              have : (0 : ℝ) < (1 / 2) * p := by positivity
              nlinarith
          _ ≤ (p * (1 - φ) / 2) ^ (w'.length + 1) * p := by
              have h13 : (0 : ℝ) ≤ (p * (1 - φ) / 2) ^ (w'.length + 1) := pow_nonneg hbase0 _
              nlinarith
          _ = ((1 - φ) / 2) ^ (w'.length + 1) * (p ^ w'.length * p) * p := by
              rw [h7, h10]; ring
          _ ≤ ((1 - φ) / 2) ^ (w'.length + 1) * ((w'.map P).prod * P MA) * p := by
              have h14 : p ^ w'.length * p ≤ (w'.map P).prod * P MA := by
                nlinarith [h2, h12, h11', pow_nonneg hp0.le w'.length, hp0.le]
              have h15 := mul_le_mul_of_nonneg_left h14 h9
              exact mul_le_mul_of_nonneg_right h15 hp0.le
      · have h11 : (0 : ℝ) ≤ (w'.map P).prod :=
          List.prod_nonneg fun a ha ↦ by
            obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
            exact hP a' (hwA a' ha')
        have h9 : (0 : ℝ) ≤ ((1 - φ) / 2) ^ (w'.length + 1) :=
          pow_nonneg (by linarith) _
        have := hP MA hMAmem
        positivity
  -- produce the word
  by_cases hsL' : s ≤ L
  · obtain ⟨l, hl, hlsum⟩ := AddSubmonoid.exists_list_of_mem_closure hs
    have hlne : l ≠ [] := by
      intro hc
      rw [hc] at hlsum
      simp at hlsum
      omega
    obtain ⟨x₁, w, rfl⟩ := List.exists_cons_of_ne_nil hlne
    have hx₁ : x₁ ∈ A := hl x₁ List.mem_cons_self
    have hwmem : ∀ a ∈ w, a ∈ A := fun a ha ↦ hl a (List.mem_cons_of_mem x₁ ha)
    have hsum : x₁ + w.sum = s := by
      simp only [List.sum_cons] at hlsum
      omega
    refine hmain x₁ hx₁ w hwmem hsum ?_ (Or.inl (by omega))
    have h5 : ∀ a ∈ w, 1 ≤ a := fun a ha ↦ hA0 a (hwmem a ha)
    have h6 := length_le_sum w h5
    omega
  · -- the window: retract by the maximal shift
    have hs' := hwin s hs (by omega) hsL
    obtain ⟨l, hl, hlsum⟩ := AddSubmonoid.exists_list_of_mem_closure hs'
    have hlne : l ≠ [] := by
      intro hc
      rw [hc] at hlsum
      simp at hlsum
      omega
    obtain ⟨x₁, w', rfl⟩ := List.exists_cons_of_ne_nil hlne
    have hx₁ : x₁ ∈ A := hl x₁ List.mem_cons_self
    have hwmem : ∀ a ∈ w', a ∈ A := fun a ha ↦ hl a (List.mem_cons_of_mem x₁ ha)
    have hsum' : x₁ + w'.sum = s - MA := by
      simp only [List.sum_cons] at hlsum
      omega
    have hsMA : MA ≤ s := by omega
    refine hmain x₁ hx₁ (w' ++ [MA])
      (fun a ha ↦ by
        rcases List.mem_append.mp ha with h | h
        · exact hwmem a h
        · rw [List.mem_singleton.mp h]; exact hMAmem)
      (by
        have : (w' ++ [MA]).sum = w'.sum + MA := by simp
        omega)
      ?_ (Or.inr ⟨w', rfl, by omega, by omega⟩)
    have h5 : ∀ a ∈ w', 1 ≤ a := fun a ha ↦ hA0 a (hwmem a ha)
    have h6 := length_le_sum w' h5
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-! #### Integrated bounds -/

lemma freeLaw_nonneg (hP : ∀ a ∈ A, 0 ≤ P a) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (F s : ℕ) : 0 ≤ freeLaw A P L φ F s :=
  Finset.sum_nonneg fun x hx ↦
    mul_nonneg (hP x hx) (free_nonneg (L := L) hP hφ0 hφ1 F _ _ _)

lemma coupleLaw_nonneg (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (F s : ℕ) : 0 ≤ coupleLaw A B P P' L φ F s :=
  Finset.sum_nonneg fun x hx ↦ Finset.sum_nonneg fun y hy ↦
    mul_nonneg (hP x hx) (mul_nonneg (hP' y hy)
      (couple_nonneg hP hP' hφ0 hφ1 F _ _ _ _))

lemma freeLaw_sum_le_one (hP : ∀ a ∈ A, 0 ≤ P a) (hP1 : ∑ a ∈ A, P a = 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (F : ℕ) (S : Finset ℕ) :
    ∑ s ∈ S, freeLaw A P L φ F s ≤ 1 := by
  have hswap : ∑ s ∈ S, freeLaw A P L φ F s
      = ∑ x ∈ A, P x * ∑ s ∈ S, free A P L φ F x (x + 1) s := by
    simp only [freeLaw]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum ..).symm
  rw [hswap]
  calc ∑ x ∈ A, P x * ∑ s ∈ S, free A P L φ F x (x + 1) s
      ≤ ∑ x ∈ A, P x * 1 :=
        Finset.sum_le_sum fun x hx ↦ mul_le_mul_of_nonneg_left
          (free_sum_le_one hP hP1 hφ0 hφ1 F x (x + 1) S) (hP x hx)
    _ = 1 := by rw [← Finset.sum_mul, hP1, one_mul]

lemma coupleLaw_swap (F s : ℕ) :
    coupleLaw A B P P' L φ F s
      = ∑ x ∈ A, ∑ y ∈ B, P x * (P' y * couple A B P P' L φ F x y (x + 1) s) := rfl

lemma coupleLaw_sum_le_one (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (F : ℕ) (S : Finset ℕ) :
    ∑ s ∈ S, coupleLaw A B P P' L φ F s ≤ 1 := by
  have hswap : ∑ s ∈ S, coupleLaw A B P P' L φ F s
      = ∑ x ∈ A, ∑ y ∈ B, P x * (P' y *
          ∑ s ∈ S, couple A B P P' L φ F x y (x + 1) s) := by
    simp only [coupleLaw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hswap]
  calc ∑ x ∈ A, ∑ y ∈ B, P x * (P' y * ∑ s ∈ S, couple A B P P' L φ F x y (x + 1) s)
      ≤ ∑ x ∈ A, ∑ y ∈ B, P x * (P' y * 1) := by
        refine Finset.sum_le_sum fun x hx ↦ Finset.sum_le_sum fun y hy ↦ ?_
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (couple_sum_le_one hP hP' hP1 hP'1 hφ0 hφ1 F x y (x + 1) S) (hP' y hy))
          (hP x hx)
    _ = 1 := by
        rw [Finset.sum_congr rfl fun x _ ↦ by
          rw [show ∑ y ∈ B, P x * (P' y * 1) = P x * ∑ y ∈ B, P' y by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun y _ ↦ by ring, hP'1, mul_one], hP1]

lemma freeLaw_eq_zero {MA : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) (hA0 : ∀ a ∈ A, 0 < a)
    {F s : ℕ}
    (h : ¬ (s ∈ AddSubmonoid.closure (A : Set ℕ) ∧ 0 < s ∧ s ≤ L + MA)) :
    freeLaw A P L φ F s = 0 := by
  rw [freeLaw]
  refine Finset.sum_eq_zero fun x hx ↦ ?_
  by_cases h1 : s ∈ AddSubmonoid.closure (A : Set ℕ)
  · by_cases h2 : 0 < s
    · have h3 : L + MA < s := by
        by_contra h4
        exact h ⟨h1, h2, by omega⟩
      rw [free_eq_zero_of_gt hMA F x (x + 1) (by have := hMA x hx; omega) h3, mul_zero]
    · have h4 : s = 0 := by omega
      rw [free_eq_zero_of_lt F x (x + 1) (by have := hA0 x hx; omega), mul_zero]
  · rw [free_eq_zero_of_notMem F x (x + 1)
      (AddSubmonoid.subset_closure (Finset.mem_coe.mpr hx)) h1, mul_zero]

lemma coupleLaw_eq_zero {MA : ℕ} (hMA : ∀ a ∈ A, a ≤ MA) (hA0 : ∀ a ∈ A, 0 < a)
    {F s : ℕ}
    (h : ¬ (s ∈ AddSubmonoid.closure (A : Set ℕ) ∧ 0 < s ∧ s ≤ L + MA)) :
    coupleLaw A B P P' L φ F s = 0 := by
  rw [coupleLaw]
  refine Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y hy ↦ ?_
  by_cases h1 : s ∈ AddSubmonoid.closure (A : Set ℕ)
  · by_cases h2 : 0 < s
    · have h3 : L + MA < s := by
        by_contra h4
        exact h ⟨h1, h2, by omega⟩
      rw [couple_eq_zero_of_gt hMA F x y (x + 1) (by have := hMA x hx; omega) h3,
        mul_zero, mul_zero]
    · have h4 : s = 0 := by omega
      rw [couple_eq_zero_of_lt F x y (x + 1) (by have := hA0 x hx; omega),
        mul_zero, mul_zero]
  · rw [couple_eq_zero_of_notMem F x y (x + 1)
      (AddSubmonoid.subset_closure (Finset.mem_coe.mpr hx)) h1, mul_zero, mul_zero]

/-- **The realised coupled law is close to the idealised one**, integrated over
the roots: the difference on any set of totals is at most twice the exhaustion
mass, itself at most `2 (Fφ)²`. -/
lemma coupleLaw_idealLaw_close {MA MB : ℕ} (hMA : ∀ a ∈ A, a ≤ MA)
    (hMB : ∀ b ∈ B, b ≤ MB) (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b)
    (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    {F : ℕ} (hF : 3 * L + 2 * MA + MB + 2 ≤ F) (S : Finset ℕ) :
    ∑ s ∈ S, |coupleLaw A B P P' L φ F s - idealLaw A B P P' L MA MB s|
      ≤ 2 * (F * φ) ^ 2 := by
  have hkey : ∀ s ∈ S, |coupleLaw A B P P' L φ F s - idealLaw A B P P' L MA MB s|
      ≤ ∑ x ∈ A, ∑ y ∈ B, P x * (P' y * |couple A B P P' L φ F x y (x + 1) s
          - ideal A B P P' L (2 * L + MA + MB + 1) x y s|) := by
    intro s _
    have harg : coupleLaw A B P P' L φ F s - idealLaw A B P P' L MA MB s
        = ∑ x ∈ A, ∑ y ∈ B, P x * (P' y * (couple A B P P' L φ F x y (x + 1) s
            - ideal A B P P' L (2 * L + MA + MB + 1) x y s)) := by
      rw [coupleLaw, idealLaw, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ ↦ by ring
    rw [harg]
    calc |∑ x ∈ A, ∑ y ∈ B, P x * (P' y * (couple A B P P' L φ F x y (x + 1) s
          - ideal A B P P' L (2 * L + MA + MB + 1) x y s))|
        ≤ ∑ x ∈ A, |∑ y ∈ B, P x * (P' y * (couple A B P P' L φ F x y (x + 1) s
          - ideal A B P P' L (2 * L + MA + MB + 1) x y s))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ A, ∑ y ∈ B, |P x * (P' y * (couple A B P P' L φ F x y (x + 1) s
          - ideal A B P P' L (2 * L + MA + MB + 1) x y s))| :=
          Finset.sum_le_sum fun x _ ↦ Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x ∈ A, ∑ y ∈ B, P x * (P' y * |couple A B P P' L φ F x y (x + 1) s
          - ideal A B P P' L (2 * L + MA + MB + 1) x y s|) := by
          refine Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun y hy ↦ ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (hP x hx), abs_of_nonneg (hP' y hy)]
  calc ∑ s ∈ S, |coupleLaw A B P P' L φ F s - idealLaw A B P P' L MA MB s|
      ≤ ∑ s ∈ S, ∑ x ∈ A, ∑ y ∈ B, P x * (P' y * |couple A B P P' L φ F x y (x + 1) s
          - ideal A B P P' L (2 * L + MA + MB + 1) x y s|) :=
        Finset.sum_le_sum hkey
    _ = ∑ x ∈ A, ∑ y ∈ B, P x * (P' y * ∑ s ∈ S, |couple A B P P' L φ F x y (x + 1) s
          - ideal A B P P' L (2 * L + MA + MB + 1) x y s|) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ ∑ x ∈ A, ∑ y ∈ B, P x * (P' y * (2 * (F * φ) ^ 2)) := by
        refine Finset.sum_le_sum fun x hx ↦ Finset.sum_le_sum fun y hy ↦ ?_
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (hP' y hy)) (hP x hx)
        calc ∑ s ∈ S, |couple A B P P' L φ F x y (x + 1) s
              - ideal A B P P' L (2 * L + MA + MB + 1) x y s|
            ≤ 2 * exhaust A B P P' L φ F x y (x + 1) :=
              couple_ideal_close hMA hMB hA0 hB0 hP hP' hP1 hP'1 hφ0 hφ1 F x y (x + 1) S
                (by have := hMA x hx; omega) (by have := hMB y hy; omega)
                (by have h1 := hA0 x hx; have h2 := hB0 y hy; omega)
          _ ≤ 2 * (F * φ) ^ 2 := by
              have := exhaust_le_sq (L := L) hP hP' hP1 hP'1 hφ0 hφ1 F x y (x + 1)
                (by have := hA0 x hx; omega)
              linarith
    _ = 2 * (F * φ) ^ 2 := by
        rw [Finset.sum_congr rfl fun x _ ↦ by
          rw [show ∑ y ∈ B, P x * (P' y * (2 * (F * φ) ^ 2))
              = P x * (2 * (F * φ) ^ 2) * ∑ y ∈ B, P' y by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun y _ ↦ by ring, hP'1, mul_one]]
        rw [← Finset.sum_mul, hP1, one_mul]

/-- **The idealised bulk laws of the two sides agree.** -/
lemma idealLaw_bulk_eq {MA MB : ℕ} {s : ℕ} (hs : s ≤ L) :
    idealLaw A B P P' L MA MB s = idealLaw B A P' P L MB MA s := by
  rw [idealLaw, idealLaw, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  rw [show 2 * L + MB + MA + 1 = 2 * L + MA + MB + 1 by ring,
    ideal_bulk_symm hs (2 * L + MA + MB + 1) y x]
  ring

/-! #### The clause theorems of `thm:matched-presentation` -/

/-- **`thm:matched-presentation`\labelcref{it:matched-support}**: the presented
shifts are exactly the elements of `Λ ∩ (0, L + MA]`. -/
theorem matchedShift_pos_iff {MA : ℕ} (hMAmem : MA ∈ A) (hMA : ∀ a ∈ A, a ≤ MA)
    (hA0 : ∀ a ∈ A, 0 < a) (hMAL : MA ≤ L)
    (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hPp : ∀ a ∈ A, p ≤ P a)
    (hφ0 : 0 ≤ φ) (hφh : φ ≤ 1 / 2) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hwin : ∀ s' : ℕ, s' ∈ AddSubmonoid.closure (A : Set ℕ) → L < s' → s' ≤ L + MA →
      s' - MA ∈ AddSubmonoid.closure (A : Set ℕ))
    {F : ℕ} (hF : L + MA + 2 ≤ F) {s : ℕ} :
    0 < matchedShift A B P P' L φ δ F s
      ↔ s ∈ AddSubmonoid.closure (A : Set ℕ) ∧ 0 < s ∧ s ≤ L + MA := by
  have hφ1 : φ ≤ 1 := by linarith
  constructor
  · intro hpos
    by_contra h
    rw [matchedShift, freeLaw_eq_zero hMA hA0 h, coupleLaw_eq_zero hMA hA0 h,
      mul_zero, mul_zero, add_zero] at hpos
    exact lt_irrefl 0 hpos
  · rintro ⟨h1, h2, h3⟩
    have hfloor := freeLaw_ge_of_mem hMAmem hA0 hMAL hP hp0 hp1 hPp hφ0 hφ1 hwin
      hF h1 h2 h3
    have hc0 := coupleLaw_nonneg (L := L) hP hP' hφ0 hφ1 F s
    have hcpos : (0 : ℝ) < (1 / 2) * p * (p * (1 - φ) / 2) ^ (L + MA) := by
      have hb : (0 : ℝ) < p * (1 - φ) / 2 := by nlinarith
      positivity
    have h4 : 0 < δ * freeLaw A P L φ F s := by nlinarith
    have h5 : 0 ≤ (1 - δ) * coupleLaw A B P P' L φ F s := by nlinarith
    rw [matchedShift]
    linarith

/-- **`thm:matched-presentation`\labelcref{it:matched-mass}**: every presented
shift carries mass at least `c δ`, with `c` independent of `δ` and of the
failure probability bound. -/
theorem matchedShift_floor {MA : ℕ} (hMAmem : MA ∈ A)
    (hA0 : ∀ a ∈ A, 0 < a) (hMAL : MA ≤ L)
    (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hPp : ∀ a ∈ A, p ≤ P a)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hwin : ∀ s' : ℕ, s' ∈ AddSubmonoid.closure (A : Set ℕ) → L < s' → s' ≤ L + MA →
      s' - MA ∈ AddSubmonoid.closure (A : Set ℕ))
    {F : ℕ} (hF : L + MA + 2 ≤ F) {s : ℕ}
    (h1 : s ∈ AddSubmonoid.closure (A : Set ℕ)) (h2 : 0 < s) (h3 : s ≤ L + MA) :
    δ * ((1 / 2) * p * (p * (1 - φ) / 2) ^ (L + MA))
      ≤ matchedShift A B P P' L φ δ F s := by
  have hfloor := freeLaw_ge_of_mem hMAmem hA0 hMAL hP hp0 hp1 hPp hφ0 hφ1 hwin
    hF h1 h2 h3
  have hc0 := coupleLaw_nonneg (L := L) hP hP' hφ0 hφ1 F s
  rw [matchedShift]
  nlinarith

/-- **`thm:matched-presentation`\labelcref{it:matched-bulk}, the bulk
agreement**: on totals at or below `L` the two presented laws differ by at most
`2δ` plus the two exhaustion masses. -/
theorem matchedShift_bulk_close {MA MB : ℕ} {φ' : ℝ} (hMA : ∀ a ∈ A, a ≤ MA)
    (hMB : ∀ b ∈ B, b ≤ MB) (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b)
    (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hφ'0 : 0 ≤ φ') (hφ'1 : φ' ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {F F' : ℕ} (hF : 3 * L + 2 * MA + MB + 2 ≤ F) (hF' : 3 * L + 2 * MB + MA + 2 ≤ F')
    {Sb : Finset ℕ} (hSb : ∀ s ∈ Sb, s ≤ L) :
    ∑ s ∈ Sb, |matchedShift A B P P' L φ δ F s - matchedShift B A P' P L φ' δ F' s|
      ≤ 2 * δ + 2 * (F * φ) ^ 2 + 2 * (F' * φ') ^ 2 := by
  have hkey : ∀ s ∈ Sb,
      |matchedShift A B P P' L φ δ F s - matchedShift B A P' P L φ' δ F' s|
      ≤ δ * (freeLaw A P L φ F s + freeLaw B P' L φ' F' s)
        + (1 - δ) * (|coupleLaw A B P P' L φ F s - idealLaw A B P P' L MA MB s|
          + |coupleLaw B A P' P L φ' F' s - idealLaw B A P' P L MB MA s|) := by
    intro s hsb
    rw [matchedShift, matchedShift]
    have hfe : freeLaw A P L φ F s ≥ 0 := freeLaw_nonneg (L := L) hP hφ0 hφ1 F s
    have hfe' : freeLaw B P' L φ' F' s ≥ 0 := freeLaw_nonneg (L := L) hP' hφ'0 hφ'1 F' s
    have hieq := idealLaw_bulk_eq (A := A) (B := B) (P := P) (P' := P')
      (L := L) (MA := MA) (MB := MB) (hSb s hsb)
    have habs1 : |freeLaw A P L φ F s - freeLaw B P' L φ' F' s|
        ≤ freeLaw A P L φ F s + freeLaw B P' L φ' F' s := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have habs2 : |coupleLaw A B P P' L φ F s - coupleLaw B A P' P L φ' F' s|
        ≤ |coupleLaw A B P P' L φ F s - idealLaw A B P P' L MA MB s|
          + |coupleLaw B A P' P L φ' F' s - idealLaw B A P' P L MB MA s| := by
      calc |coupleLaw A B P P' L φ F s - coupleLaw B A P' P L φ' F' s|
          = |(coupleLaw A B P P' L φ F s - idealLaw A B P P' L MA MB s)
            - (coupleLaw B A P' P L φ' F' s - idealLaw B A P' P L MB MA s)| := by
            rw [hieq]
            ring_nf
        _ ≤ _ := abs_sub _ _
    calc |δ * freeLaw A P L φ F s + (1 - δ) * coupleLaw A B P P' L φ F s
          - (δ * freeLaw B P' L φ' F' s + (1 - δ) * coupleLaw B A P' P L φ' F' s)|
        = |δ * (freeLaw A P L φ F s - freeLaw B P' L φ' F' s)
          + (1 - δ) * (coupleLaw A B P P' L φ F s - coupleLaw B A P' P L φ' F' s)| := by
          ring_nf
      _ ≤ |δ * (freeLaw A P L φ F s - freeLaw B P' L φ' F' s)|
          + |(1 - δ) * (coupleLaw A B P P' L φ F s - coupleLaw B A P' P L φ' F' s)| :=
          abs_add_le _ _
      _ ≤ δ * (freeLaw A P L φ F s + freeLaw B P' L φ' F' s)
          + (1 - δ) * (|coupleLaw A B P P' L φ F s - idealLaw A B P P' L MA MB s|
            + |coupleLaw B A P' P L φ' F' s - idealLaw B A P' P L MB MA s|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hδ0,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - δ)]
          have h6 := mul_le_mul_of_nonneg_left habs1 hδ0
          have h7 := mul_le_mul_of_nonneg_left habs2
            (by linarith : (0 : ℝ) ≤ 1 - δ)
          linarith
  calc ∑ s ∈ Sb, |matchedShift A B P P' L φ δ F s - matchedShift B A P' P L φ' δ F' s|
      ≤ ∑ s ∈ Sb, (δ * (freeLaw A P L φ F s + freeLaw B P' L φ' F' s)
        + (1 - δ) * (|coupleLaw A B P P' L φ F s - idealLaw A B P P' L MA MB s|
          + |coupleLaw B A P' P L φ' F' s - idealLaw B A P' P L MB MA s|)) :=
        Finset.sum_le_sum hkey
    _ = δ * (∑ s ∈ Sb, freeLaw A P L φ F s + ∑ s ∈ Sb, freeLaw B P' L φ' F' s)
        + (1 - δ) * (∑ s ∈ Sb, |coupleLaw A B P P' L φ F s - idealLaw A B P P' L MA MB s|
          + ∑ s ∈ Sb, |coupleLaw B A P' P L φ' F' s - idealLaw B A P' P L MB MA s|) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ δ * (1 + 1) + (1 - δ) * (2 * (F * φ) ^ 2 + 2 * (F' * φ') ^ 2) := by
        have h1 := freeLaw_sum_le_one (L := L) hP hP1 hφ0 hφ1 F Sb
        have h2 := freeLaw_sum_le_one (L := L) hP' hP'1 hφ'0 hφ'1 F' Sb
        have h3 := coupleLaw_idealLaw_close hMA hMB hA0 hB0 hP hP' hP1 hP'1 hφ0 hφ1
          hF Sb
        have h4 := coupleLaw_idealLaw_close hMB hMA hB0 hA0 hP' hP hP'1 hP1 hφ'0 hφ'1
          hF' Sb
        have h5 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hδ0
        have h6 := mul_le_mul_of_nonneg_left (add_le_add h3 h4)
          (by linarith : (0 : ℝ) ≤ 1 - δ)
        linarith
    _ ≤ 2 * δ + 2 * (F * φ) ^ 2 + 2 * (F' * φ') ^ 2 := by
        have h7 : (0 : ℝ) ≤ 2 * (F * φ) ^ 2 := by positivity
        have h8 : (0 : ℝ) ≤ 2 * (F' * φ') ^ 2 := by positivity
        nlinarith

/-- **`thm:matched-presentation`\labelcref{it:matched-bulk}, the window
mass**: the mass past `L` is at most the free branch, the geometric survival
bound of `thm:common-renewal`, and the exhaustion mass. -/
theorem matchedShift_window {MA MB : ℕ} (hMA : ∀ a ∈ A, a ≤ MA)
    (hMB : ∀ b ∈ B, b ≤ MB) (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b)
    (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    (hP1 : ∑ a ∈ A, P a = 1) (hP'1 : ∑ b ∈ B, P' b = 1)
    (hsem : AddSubmonoid.closure (A : Set ℕ) = AddSubmonoid.closure (B : Set ℕ))
    {p : ℝ} (hp0 : 0 < p) (hAne : A.Nonempty)
    (hPp : ∀ a ∈ A, p ≤ P a) (hP'p : ∀ b ∈ B, p ≤ P' b)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {F : ℕ} (hF : 3 * L + 2 * MA + MB + 2 ≤ F) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ (W : Finset ℕ), (∀ s ∈ W, L < s) →
      ∀ k : ℕ, (k * H + 1) * MA ≤ L →
      ∑ s ∈ W, matchedShift A B P P' L φ δ F s
        ≤ δ + (1 - p ^ H) ^ k + 2 * (F * φ) ^ 2 := by
  obtain ⟨H, hH1, hblock⟩ := alive_block_le (L := L) hsem MA MB hp0 hAne
    hP hP' hP1 hP'1 hPp hP'p
  have hp1 : p ≤ 1 := by
    obtain ⟨a, ha⟩ := hAne
    exact (hPp a ha).trans (prob_le_one hP hP1 ha)
  have hq0 : (0 : ℝ) ≤ 1 - p ^ H := by
    have := pow_le_one₀ hp0.le hp1 (n := H)
    linarith
  refine ⟨H, hH1, fun W hW k hk ↦ ?_⟩
  have hidealW : ∑ s ∈ W, idealLaw A B P P' L MA MB s ≤ (1 - p ^ H) ^ k := by
    have hswap : ∑ s ∈ W, idealLaw A B P P' L MA MB s
        = ∑ x ∈ A, ∑ y ∈ B, P x * (P' y *
            ∑ s ∈ W, ideal A B P P' L (2 * L + MA + MB + 1) x y s) := by
      simp only [idealLaw]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [hswap]
    calc ∑ x ∈ A, ∑ y ∈ B, P x * (P' y *
          ∑ s ∈ W, ideal A B P P' L (2 * L + MA + MB + 1) x y s)
        ≤ ∑ x ∈ A, ∑ y ∈ B, P x * (P' y * (1 - p ^ H) ^ k) := by
          refine Finset.sum_le_sum fun x hx ↦ Finset.sum_le_sum fun y hy ↦ ?_
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ?_ (hP' y hy)) (hP x hx)
          have hvalid : ValidState A B MA MB x y := by
            refine ⟨AddSubmonoid.subset_closure (Finset.mem_coe.mpr hx),
              AddSubmonoid.subset_closure (Finset.mem_coe.mpr hy), ?_, ?_⟩
            · have h1 := hB0 y hy
              have h2 := hMB y hy
              have h3 := hA0 x hx
              omega
            · have h1 := hA0 x hx
              have h2 := hMA x hx
              have h3 := hB0 y hy
              omega
          calc ∑ s ∈ W, ideal A B P P' L (2 * L + MA + MB + 1) x y s
              ≤ alive A B P P' L (k * H) x y := by
                refine ideal_window_le_alive hMA hP hP' hP1 hP'1 hW (k * H) _ x y ?_
                have h1 := hMA x hx
                have h2 : (k * H + 1) * MA = k * H * MA + MA := Nat.succ_mul _ _
                omega
            _ ≤ (1 - p ^ H) ^ k :=
                alive_le_pow hMA hMB hA0 hB0 hP hP' hP1 hP'1 hq0
                  (fun r' t' hv' ↦ hblock r' t' hv') k x y hvalid
      _ = (1 - p ^ H) ^ k := by
          rw [Finset.sum_congr rfl fun x _ ↦ by
            rw [show ∑ y ∈ B, P x * (P' y * (1 - p ^ H) ^ k)
                = P x * (1 - p ^ H) ^ k * ∑ y ∈ B, P' y by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun y _ ↦ by ring, hP'1, mul_one]]
          rw [← Finset.sum_mul, hP1, one_mul]
  have hcplW : ∑ s ∈ W, coupleLaw A B P P' L φ F s
      ≤ (1 - p ^ H) ^ k + 2 * (F * φ) ^ 2 := by
    have htv := coupleLaw_idealLaw_close hMA hMB hA0 hB0 hP hP' hP1 hP'1 hφ0 hφ1 hF W
    have h1 : ∑ s ∈ W, coupleLaw A B P P' L φ F s
        ≤ ∑ s ∈ W, idealLaw A B P P' L MA MB s
          + ∑ s ∈ W, |coupleLaw A B P P' L φ F s - idealLaw A B P P' L MA MB s| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun s _ ↦ ?_
      have := abs_nonneg (coupleLaw A B P P' L φ F s - idealLaw A B P P' L MA MB s)
      have := le_abs_self (coupleLaw A B P P' L φ F s - idealLaw A B P P' L MA MB s)
      linarith
    linarith
  have hfreeW := freeLaw_sum_le_one (L := L) hP hP1 hφ0 hφ1 F W
  simp only [matchedShift]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h2 := mul_le_mul_of_nonneg_left hfreeW hδ0
  have h3 := mul_le_mul_of_nonneg_left hcplW (by linarith : (0 : ℝ) ≤ 1 - δ)
  have h4 : (0 : ℝ) ≤ (1 - p ^ H) ^ k := pow_nonneg hq0 k
  have h5 : (0 : ℝ) ≤ 2 * (F * φ) ^ 2 := by positivity
  nlinarith

/-- **`thm:matched-presentation`\labelcref{it:matched-flat}, the constant.**  A
blob holds at most `n` splits and the neck segments of at most `1 + L + M`
failed descents, each within `R + 1` vertices of the exit it hangs from, so its
diameter is at most `2(n + 2 + L + M)(R + 1)`; collapsing it onto its root is
then a `γ₁ R`-marked quasi-isometry with `γ₁ = 4(n + 2 + L + M)` by
`markedQI_of_collapse`, exactly as in `thm:cluster-flat`. -/
lemma blob_flat_scale {n L M R : ℕ} (hR : 1 ≤ R) :
    2 * (n + 2 + L + M) * (R + 1) ≤ 4 * (n + 2 + L + M) * R := by
  nlinarith

end Assembly

end Matched

end ChainClasses
