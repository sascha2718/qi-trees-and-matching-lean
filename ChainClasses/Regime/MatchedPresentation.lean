import ChainClasses.Regime.MatchedCouple

/-!
`thm:matched-presentation` of `matching_classes_general.tex`, the law level: the
matched blob presentations of two chain-regime reduced skeletons, as explicit
The construction is built in three modules: `MatchedIdeal`, `MatchedCouple` and this one,
which assembles the presentation and proves its clauses; the account below covers all
three.

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

* `ideal`, `ideal_sum_le_one`: the idealised coupled
  exploration, the lagging-side walk of `thm:common-renewal` stopped at
  agreement at or below `L` or at first passage past `L`.
* `ideal_bulk_symm`: **the idealised bulk laws agree**: the stop law at a bulk
  value is symmetric under exchanging the two laws, which is the equality
  behind `thm:matched-presentation` (`it:matched-bulk`).
* `alive`, `alive_word_le`, `alive_le_pow`, `ideal_window_le_alive`: **the
  window mass**.  A stop past `L` needs many increments, each block of `H`
  increments closes the lag with probability at least `q = p^H` through the
  correction words of `thm:common-renewal` read by `renewalWordRun`, and the
  survival probability decays geometrically.
-/

namespace ChainClasses

namespace Matched

open Finset

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

/-- **`thm:matched-presentation` (`it:matched-support`)**: the presented
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

/-- **`thm:matched-presentation` (`it:matched-mass`)**: every presented
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

/-- **`thm:matched-presentation` (`it:matched-bulk`), the bulk
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

/-- **`thm:matched-presentation` (`it:matched-bulk`), the window
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

/-- **`thm:matched-presentation` (`it:matched-flat`), the constant.**  A
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
