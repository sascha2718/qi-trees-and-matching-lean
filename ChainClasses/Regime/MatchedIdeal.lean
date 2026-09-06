import ChainClasses.Regime.RenewalAlignment

/-!
`thm:matched-presentation` of `matching_classes_general.tex`, first part: the idealised
coupled exploration with its symmetric bulk stop law and window tail, the correction-word
descent, and uniform correction words with geometric decay.  The realised and the free
explorations follow in `MatchedCouple`, and `MatchedPresentation` assembles the clauses.
-/

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

end Blocks

end Matched

end ChainClasses
