import ChainClasses.Regime.ChainRegime

/-!
Asynchronous renewal alignment for two finite shifted-arity supports.

Exact equality of one-step or fixed-depth frontier laws is unnecessarily
strong for the quasi-isometry construction.  If two shifted supports generate
the same additive submonoid, any partial renewal totals on the two sides have
finite continuations to a common total.  For finite supports, every one-step
generator has a representation on the other side of uniformly bounded length.

These are the support-arithmetic inputs to the asynchronous block construction
in `matching_classes_general.tex`.  The probabilistic next step runs the
lagging accumulated total.  Its overshoot lies in a finite state space; positive
weights on the finite supports then turn the finite continuation proved here
into a uniform positive chance of alignment and hence an exponential tail.
-/

namespace ChainClasses

/-- One move of the lagging-side renewal rule.  A positive lag means that the
right walk moves by `b`; a negative lag means that the left walk moves by
`a`; zero is absorbing for one completed renewal block. -/
def renewalLagStep (d : ℤ) (a b : ℕ) : ℤ :=
  if 0 < d then d - b else if d < 0 then d + a else 0

/-- Fuelled implementation of the asynchronous correction-word reader. -/
def renewalWordRunAux : ℕ → ℤ → List ℕ → List ℕ → ℤ
  | 0, d, _, _ => d
  | n + 1, d, xs, ys =>
      if d = 0 then 0
      else if d < 0 then
        match xs with
        | [] => d
        | a :: xs' => renewalWordRunAux n (d + a) xs' ys
      else
        match ys with
        | [] => d
        | b :: ys' => renewalWordRunAux n (d - b) xs ys'

/-- Read two prescribed correction words asynchronously, consuming a left
increment only when the left total is lagging and a right increment only when
the right total is lagging.  Equality is absorbing. -/
def renewalWordRun (d : ℤ) (xs ys : List ℕ) : ℤ :=
  renewalWordRunAux (xs.length + ys.length) d xs ys

private theorem renewalWordRunAux_eq_zero {fuel : ℕ} {d : ℤ}
    {xs ys : List ℕ} (hlen : xs.length + ys.length ≤ fuel)
    (hbal : d + (xs.sum : ℤ) - (ys.sum : ℤ) = 0) :
    renewalWordRunAux fuel d xs ys = 0 := by
  induction fuel generalizing d xs ys with
  | zero =>
      have hxl : xs.length = 0 := by omega
      have hyl : ys.length = 0 := by omega
      have hx : xs = [] := List.length_eq_zero_iff.mp hxl
      have hy : ys = [] := List.length_eq_zero_iff.mp hyl
      subst xs
      subst ys
      simp only [List.sum_nil, Nat.cast_zero, add_zero, sub_zero] at hbal
      simp [renewalWordRunAux, hbal]
  | succ fuel ih =>
      simp only [renewalWordRunAux]
      split_ifs with hd0 hdneg
      · rfl
      · cases xs with
        | nil =>
            simp only [List.sum_nil, Nat.cast_zero, add_zero] at hbal
            have hys : (0 : ℤ) ≤ (ys.sum : ℤ) := by positivity
            omega
        | cons a xs' =>
            apply ih
            · simp only [List.length_cons] at hlen
              omega
            · push_cast [List.sum_cons] at hbal ⊢
              omega
      · have hdpos : 0 < d := by omega
        cases ys with
        | nil =>
            simp only [List.sum_nil, Nat.cast_zero, sub_zero] at hbal
            have hxs : (0 : ℤ) ≤ (xs.sum : ℤ) := by positivity
            omega
        | cons b ys' =>
            apply ih
            · simp only [List.length_cons] at hlen
              omega
            · push_cast [List.sum_cons] at hbal ⊢
              omega

@[simp] lemma renewalWordRun_zero (xs ys : List ℕ) :
    renewalWordRun 0 xs ys = 0 := by
  unfold renewalWordRun
  cases h : xs.length + ys.length with
  | zero => rfl
  | succ n => simp [renewalWordRunAux]

/-- Balanced correction words really close the lag under the asynchronous
reading rule.  This fills the deterministic gap between equality of the two
completed sums and killing of the renewal phase. -/
theorem renewalWordRun_eq_zero {d : ℤ} {xs ys : List ℕ}
    (hbal : d + (xs.sum : ℤ) - (ys.sum : ℤ) = 0) :
    renewalWordRun d xs ys = 0 := by
  exact renewalWordRunAux_eq_zero le_rfl hbal

/-- The finite phase alphabet for the asynchronous renewal zipper. -/
noncomputable def renewalLagStates (MA MB : ℕ) : Finset ℤ :=
  Finset.Ioo (-(MB : ℤ)) (MA : ℤ)

/-- Lag phases as an actual finite type, ready to be added to a finite target
grammar without introducing an unbounded block counter. -/
abbrev RenewalPhase (MA MB : ℕ) := ↥(renewalLagStates MA MB)

/-- The lag after the initial pair of positive bounded increments lies in the
open overshoot window. -/
theorem initial_renewal_lag_mem_window {a b MA MB : ℕ}
    (ha0 : 0 < a) (hb0 : 0 < b) (ha : a ≤ MA) (hb : b ≤ MB) :
    -(MB : ℤ) < (a : ℤ) - b ∧ (a : ℤ) - b < MA := by
  omega

/-- Advancing only the lagging walk preserves the finite overshoot window.
This is the deterministic finite-state assertion behind the renewal proof. -/
theorem renewalLagStep_mem_window {d : ℤ} {a b MA MB : ℕ}
    (hd : -(MB : ℤ) < d ∧ d < MA)
    (ha0 : 0 < a) (hb0 : 0 < b) (ha : a ≤ MA) (hb : b ≤ MB) :
    -(MB : ℤ) < renewalLagStep d a b ∧ renewalLagStep d a b < MA := by
  unfold renewalLagStep
  split_ifs with hdpos hdneg
  · constructor <;> omega
  · constructor <;> omega
  · constructor <;> norm_num <;> omega

/-- The lag transition is closed on the finite zipper phase alphabet. -/
theorem renewalLagStep_mem_states {d : ℤ} {a b MA MB : ℕ}
    (hd : d ∈ renewalLagStates MA MB)
    (ha0 : 0 < a) (hb0 : 0 < b) (ha : a ≤ MA) (hb : b ≤ MB) :
    renewalLagStep d a b ∈ renewalLagStates MA MB := by
  simp only [renewalLagStates, Finset.mem_Ioo] at hd ⊢
  exact renewalLagStep_mem_window hd ha0 hb0 ha hb

/-- The lagging-side transition as an endomorphism of the finite phase type. -/
noncomputable def renewalPhaseStep (MA MB : ℕ) (d : RenewalPhase MA MB)
    (a b : ℕ) (ha0 : 0 < a) (hb0 : 0 < b) (ha : a ≤ MA) (hb : b ≤ MB) :
    RenewalPhase MA MB :=
  ⟨renewalLagStep d.1 a b,
    renewalLagStep_mem_states d.2 ha0 hb0 ha hb⟩

@[simp] theorem renewalPhaseStep_val (MA MB : ℕ) (d : RenewalPhase MA MB)
    (a b : ℕ) (ha0 : 0 < a) (hb0 : 0 < b) (ha : a ≤ MA) (hb : b ≤ MB) :
    (renewalPhaseStep MA MB d a b ha0 hb0 ha hb).1 = renewalLagStep d.1 a b := rfl

/-- Any two partial renewal totals have finite continuations to one common
total when the shifted supports generate the same additive semigroup. -/
theorem common_renewal_completion {A B : Set ℕ}
    (hsem : AddSubmonoid.closure A = AddSubmonoid.closure B)
    {s t : ℕ} (hs : s ∈ AddSubmonoid.closure A)
    (ht : t ∈ AddSubmonoid.closure B) :
    ∃ xs ys : List ℕ,
      (∀ x ∈ xs, x ∈ A) ∧ (∀ y ∈ ys, y ∈ B) ∧
      s + xs.sum = t + ys.sum := by
  have htA : t ∈ AddSubmonoid.closure A := by simpa [hsem] using ht
  have hsB : s ∈ AddSubmonoid.closure B := by simpa [← hsem] using hs
  obtain ⟨xs, hxs, hxsum⟩ := AddSubmonoid.exists_list_of_mem_closure htA
  obtain ⟨ys, hys, hysum⟩ := AddSubmonoid.exists_list_of_mem_closure hsB
  refine ⟨xs, ys, hxs, hys, ?_⟩
  rw [hxsum, hysum, Nat.add_comm]

/-- The continuation supplied by semigroup equality is a genuine killing
word for the asynchronous lag runner, not merely an equality of final sums. -/
theorem common_renewal_run {A B : Set ℕ}
    (hsem : AddSubmonoid.closure A = AddSubmonoid.closure B)
    {s t : ℕ} (hs : s ∈ AddSubmonoid.closure A)
    (ht : t ∈ AddSubmonoid.closure B) :
    ∃ xs ys : List ℕ,
      (∀ x ∈ xs, x ∈ A) ∧ (∀ y ∈ ys, y ∈ B) ∧
      renewalWordRun ((s : ℤ) - t) xs ys = 0 := by
  obtain ⟨xs, ys, hxs, hys, hsum⟩ := common_renewal_completion hsem hs ht
  refine ⟨xs, ys, hxs, hys, renewalWordRun_eq_zero ?_⟩
  have hsumZ : (s : ℤ) + (xs.sum : ℤ) = (t : ℤ) + (ys.sum : ℤ) := by
    exact_mod_cast hsum
  omega

/-- A finite collection of pairs of partial renewal totals admits one uniform
bound on the total number of continuation steps needed to align each pair.

This is the deterministic compactness step used after the lag process has
been confined to its finite overshoot state space. -/
theorem finite_common_renewal_completions (A B : Set ℕ)
    (hsem : AddSubmonoid.closure A = AddSubmonoid.closure B)
    (D : Finset (ℕ × ℕ))
    (hD : ∀ p ∈ D,
      p.1 ∈ AddSubmonoid.closure A ∧ p.2 ∈ AddSubmonoid.closure B) :
    ∃ H : ℕ, ∀ p ∈ D, ∃ xs ys : List ℕ,
      (∀ x ∈ xs, x ∈ A) ∧ (∀ y ∈ ys, y ∈ B) ∧
      p.1 + xs.sum = p.2 + ys.sum ∧ xs.length + ys.length ≤ H := by
  classical
  let leftCompletion : {p // p ∈ D} → List ℕ := fun p =>
    Classical.choose (common_renewal_completion hsem (hD p p.property).1
      (hD p p.property).2)
  let rightCompletion : {p // p ∈ D} → List ℕ := fun p =>
    Classical.choose (Classical.choose_spec
      (common_renewal_completion hsem (hD p p.property).1
        (hD p p.property).2))
  have hcompletion : ∀ p : {p // p ∈ D},
      (∀ x ∈ leftCompletion p, x ∈ A) ∧
      (∀ y ∈ rightCompletion p, y ∈ B) ∧
      p.1.1 + (leftCompletion p).sum = p.1.2 + (rightCompletion p).sum := fun p =>
    Classical.choose_spec (Classical.choose_spec
      (common_renewal_completion hsem (hD p p.property).1
        (hD p p.property).2))
  let H := ∑ p : {p // p ∈ D},
    ((leftCompletion p).length + (rightCompletion p).length)
  refine ⟨H, ?_⟩
  intro p hp
  let ps : {q // q ∈ D} := ⟨p, hp⟩
  refine ⟨leftCompletion ps, rightCompletion ps,
    (hcompletion ps).1, (hcompletion ps).2.1, (hcompletion ps).2.2, ?_⟩
  exact Finset.single_le_sum
    (f := fun q : {q // q ∈ D} =>
      ((leftCompletion q).length + (rightCompletion q).length))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ ps)

/-- Iterating a uniform block-success estimate gives geometric decay.  The
probability theory supplies the one-step inequality; this lemma records the
exact deterministic induction used by the renewal argument. -/
theorem geometric_decay_of_block_contraction (q : ℝ) (_hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (failure : ℕ → ℝ) (hzero : failure 0 ≤ 1)
    (hstep : ∀ n, failure (n + 1) ≤ (1 - q) * failure n)
    (_hfailure : ∀ n, 0 ≤ failure n) :
    ∀ n, failure n ≤ (1 - q) ^ n := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      rw [pow_succ]
      calc
        failure (n + 1) ≤ (1 - q) * failure n := hstep n
        _ ≤ (1 - q) * (1 - q) ^ n := by
          exact mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hq1)
        _ = (1 - q) ^ n * (1 - q) := by ring

/-- A geometric return estimate for an unweighted killed chain does not by
itself produce an invariant for a screen operator carrying an additional
weight.  Already in one dimension, if the weighted gain is at least one then
no positive finite supersolution of `u + gain * F ≤ F` exists. -/
theorem no_screen_invariant_of_supercritical_gain {u gain F : ℝ}
    (hu : 0 < u) (hgain : 1 ≤ gain) (hF : 0 ≤ F) :
    ¬ u + gain * F ≤ F := by
  intro h
  have hFF : F ≤ gain * F := by nlinarith
  linarith

/-- Concrete scalar witness for the gap between renewal killing and the
weighted screen recursion: the killed chain survives one step with factor
`3/4`, hence has a geometric Green function, but an edge weight `2` changes
the screen gain to `3/2` and destroys every positive finite invariant. -/
theorem geometric_killing_does_not_control_weighted_screen {u F : ℝ}
    (hu : 0 < u) (hF : 0 ≤ F) :
    ¬ u + 2 * ((3 : ℝ) / 4) * F ≤ F := by
  have hgain : (1 : ℝ) ≤ 2 * ((3 : ℝ) / 4) := by norm_num
  exact no_screen_invariant_of_supercritical_gain hu hgain hF


/-- The shifted split supports of `{1,3,5}` and `{1,3,7}` generate the
same semigroup, even though neither one-step support contains the other. -/
theorem closure_two_four_eq_two_six :
    AddSubmonoid.closure ({2, 4} : Set ℕ) =
      AddSubmonoid.closure ({2, 6} : Set ℕ) := by
  have h24 : AddSubmonoid.closure ({2, 4} : Set ℕ) =
      AddSubmonoid.closure ({2} : Set ℕ) := by
    apply le_antisymm
    · apply AddSubmonoid.closure_le.mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact AddSubmonoid.subset_closure (by simp)
      · have h2 : 2 ∈ AddSubmonoid.closure ({2} : Set ℕ) :=
          AddSubmonoid.subset_closure (by simp)
        simpa using AddSubmonoid.add_mem _ h2 h2
    · exact AddSubmonoid.closure_mono (by simp)
  have h26 : AddSubmonoid.closure ({2, 6} : Set ℕ) =
      AddSubmonoid.closure ({2} : Set ℕ) := by
    apply le_antisymm
    · apply AddSubmonoid.closure_le.mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact AddSubmonoid.subset_closure (by simp)
      · have h2 : 2 ∈ AddSubmonoid.closure ({2} : Set ℕ) :=
          AddSubmonoid.subset_closure (by simp)
        simpa using AddSubmonoid.add_mem _ (AddSubmonoid.add_mem _ h2 h2) h2
    · exact AddSubmonoid.closure_mono (by simp)
  rw [h24, h26]

end ChainClasses
