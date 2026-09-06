import ChainClasses.Regime.MatchedIdeal

/-!
`thm:matched-presentation`, second part: the realised coupled exploration (unfolding the
realised rule, the idealised rule at stable fuel, departure from the idealised rule only on
exhaustion, support and totality) and the free exploration.  `MatchedPresentation`
assembles the clauses.
-/

namespace ChainClasses

namespace Matched

open Finset

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

end Matched

end ChainClasses
