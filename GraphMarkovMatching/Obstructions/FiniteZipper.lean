/-
Finite macro-step zippers for two-law matching.

The important normalization point is that a zipper row must retain *every*
offspring outcome which has a continuation in the finite phase grammar.
Then the counter part of the compatible degree is the full row mass `1`;
no inverse power of an exceptional atom is introduced.  The only linear
weight left in the screen row is the integrated label inverse moment, which
is `1 + O(eta)` in the matching ledger.

This file makes that statement exact for an arbitrary finite macro grammar.
An outcome either closes the present zipper (`none`) or moves to a new live
phase (`some j`).  The killed kernel is the mass of live outcomes.  The
screen kernel multiplies a whole row by its integrated inverse-label moment.
If every row has killed mass at least `q`, the actual screen operator is
dominated by `A` times a substochastic kernel with one-step loss `q`, and the
weighted-renewal closure from `Closure/RareMatrix.lean` applies.
-/
import GraphMarkovMatching.Closure.RareMatrix

namespace GraphMarkovMatching

open scoped ENNReal Classical

variable {ι Ω : Type} [Fintype ι] [Fintype Ω]

/-- A finite macro-step grammar.  `mass i o` is the probability of outcome
`o` in phase `i`; `next i o = none` means that the zipper closes, while
`some j` is a surviving transition to phase `j`. -/
structure FiniteZipper where
  mass : ι → Ω → ℝ≥0∞
  next : ι → Ω → Option ι
  mass_sum : ∀ i, ∑ o, mass i o = 1

namespace FiniteZipper

/-- Mass of transitions which remain in the live phase alphabet. -/
noncomputable def liveKernel (Z : FiniteZipper (ι := ι) (Ω := Ω)) :
    ι → ι → ℝ≥0∞ :=
  fun i j => ∑ o, if Z.next i o = some j then Z.mass i o else 0

/-- Mass of outcomes which close the present macro zipper. -/
noncomputable def killedMass (Z : FiniteZipper (ι := ι) (Ω := Ω))
    (i : ι) : ℝ≥0∞ :=
  ∑ o, if Z.next i o = none then Z.mass i o else 0

/-- Total counter mass retained by a proposed phase compatibility rule. -/
noncomputable def retainedMass (Z : FiniteZipper (ι := ι) (Ω := Ω))
    (admissible : ι → Ω → Prop) [DecidablePred fun p : ι × Ω => admissible p.1 p.2]
    (i : ι) : ℝ≥0∞ :=
  ∑ o, if admissible i o then Z.mass i o else 0

omit [Fintype ι] in
/-- If the phase grammar gives every outcome a continuation, its retained
counter mass is exactly one.  This is the formal reason that neither `zeta`
nor an individual atom mass is inverted in the screen row. -/
lemma retainedMass_eq_one_of_all
    (Z : FiniteZipper (ι := ι) (Ω := Ω))
    (admissible : ι → Ω → Prop)
    [DecidablePred fun p : ι × Ω => admissible p.1 p.2]
    (hall : ∀ i o, admissible i o) (i : ι) :
    Z.retainedMass admissible i = 1 := by
  rw [retainedMass]
  simp_rw [if_pos (hall i _)]
  exact Z.mass_sum i

omit [Fintype ι] in
/-- One explicitly selected closing outcome lower-bounds the killed mass. -/
lemma mass_le_killedMass_of_next_none
    (Z : FiniteZipper (ι := ι) (Ω := Ω)) {i : ι} {o : Ω}
    (ho : Z.next i o = none) :
    Z.mass i o ≤ Z.killedMass i := by
  rw [killedMass]
  calc
    Z.mass i o = (if Z.next i o = none then Z.mass i o else 0) := by simp [ho]
    _ ≤ ∑ x, if Z.next i x = none then Z.mass i x else 0 :=
      Finset.single_le_sum
        (f := fun x : Ω => if Z.next i x = none then Z.mass i x else 0)
        (fun _ _ => zero_le) (Finset.mem_univ o)

omit [Fintype ι] in
/-- A finite family of selected correction outcomes with uniformly positive
mass supplies the uniform killing bound required by the macro kernel. -/
lemma uniform_kill_of_selected
    (Z : FiniteZipper (ι := ι) (Ω := Ω)) {q : ℝ≥0∞}
    (selected : ι → Ω)
    (hclose : ∀ i, Z.next i (selected i) = none)
    (hmass : ∀ i, q ≤ Z.mass i (selected i)) :
    ∀ i, q ≤ Z.killedMass i := by
  intro i
  exact (hmass i).trans (Z.mass_le_killedMass_of_next_none (hclose i))

/-- On a finite phase alphabet, merely choosing one positive-probability
closing correction for every phase automatically produces a uniform
positive killing constant.  The product is deliberately crude but explicit. -/
theorem exists_uniform_positive_kill
    (Z : FiniteZipper (ι := ι) (Ω := Ω))
    (selected : ι → Ω)
    (hclose : ∀ i, Z.next i (selected i) = none)
    (hpos : ∀ i, Z.mass i (selected i) ≠ 0) :
    ∃ q : ℝ≥0∞, q ≠ 0 ∧ ∀ i, q ≤ Z.killedMass i := by
  let q : ℝ≥0∞ := ∏ i, Z.mass i (selected i)
  have hmass_le_one : ∀ i, Z.mass i (selected i) ≤ 1 := by
    intro i
    calc
      Z.mass i (selected i) ≤ ∑ o, Z.mass i o :=
        Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ (selected i))
      _ = 1 := Z.mass_sum i
  have hqpos : q ≠ 0 := by
    rw [show q = ∏ i, Z.mass i (selected i) from rfl]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hpos i
  refine ⟨q, hqpos, ?_⟩
  intro i
  have hrest : (∏ j ∈ (Finset.univ.erase i), Z.mass j (selected j)) ≤ 1 := by
    exact Finset.prod_le_one (fun _ _ => zero_le) (fun j _ => hmass_le_one j)
  have hqi : q ≤ Z.mass i (selected i) := by
    calc
      q = Z.mass i (selected i) *
          ∏ j ∈ (Finset.univ.erase i), Z.mass j (selected j) := by
            change (∏ k ∈ Finset.univ, Z.mass k (selected k)) =
              Z.mass i (selected i) *
                ∏ j ∈ (Finset.univ.erase i), Z.mass j (selected j)
            exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
      _ ≤ Z.mass i (selected i) * 1 := mul_le_mul_right hrest _
      _ = Z.mass i (selected i) := mul_one _
  exact hqi.trans (Z.mass_le_killedMass_of_next_none (hclose i))

/-- The live row and the killed outcome partition the full probability row. -/
lemma liveKernel_sum_add_killedMass
    (Z : FiniteZipper (ι := ι) (Ω := Ω)) (i : ι) :
    (∑ j, Z.liveKernel i j) + Z.killedMass i = 1 := by
  change (∑ j, ∑ o, if Z.next i o = some j then Z.mass i o else 0) +
      (∑ o, if Z.next i o = none then Z.mass i o else 0) = 1
  rw [Finset.sum_comm]
  calc
    (∑ o, ∑ j, if Z.next i o = some j then Z.mass i o else 0) +
          ∑ o, (if Z.next i o = none then Z.mass i o else 0)
        = ∑ o, ((∑ j, if Z.next i o = some j then Z.mass i o else 0) +
            if Z.next i o = none then Z.mass i o else 0) := by
              rw [Finset.sum_add_distrib]
    _ = ∑ o, Z.mass i o := by
      apply Finset.sum_congr rfl
      intro o _
      cases hnext : Z.next i o with
      | none => simp
      | some j => simp
    _ = 1 := Z.mass_sum i

/-- The live kernel is substochastic. -/
lemma liveKernel_row_sum_le_one
    (Z : FiniteZipper (ι := ι) (Ω := Ω)) (i : ι) :
    ∑ j, Z.liveKernel i j ≤ 1 := by
  calc
    (∑ j, Z.liveKernel i j) ≤
        (∑ j, Z.liveKernel i j) + Z.killedMass i := le_add_right le_rfl
    _ = 1 := Z.liveKernel_sum_add_killedMass i

/-! ### Exact finite-word interpretation of live-kernel powers -/

/-- Execute an outcome word.  Once the zipper has closed, it remains closed. -/
def run (Z : FiniteZipper (ι := ι) (Ω := Ω)) :
    Option ι → List Ω → Option ι
  | s, [] => s
  | none, _ :: os => Z.run none os
  | some i, o :: os => Z.run (Z.next i o) os

/-- Probability of the cylinder read until its first closing outcome.  The
tail of a word after closure is ignored because no further draw is made. -/
noncomputable def pathMass (Z : FiniteZipper (ι := ι) (Ω := Ω)) :
    Option ι → List Ω → ℝ≥0∞
  | _, [] => 1
  | none, _ :: _ => 1
  | some i, o :: os => Z.mass i o * Z.pathMass (Z.next i o) os

/-- Survival probability for `n` further micro steps. -/
noncomputable def survival (Z : FiniteZipper (ι := ι) (Ω := Ω)) :
    ℕ → ι → ℝ≥0∞
  | 0, _ => 1
  | n + 1, i => ∑ o, Z.mass i o *
      match Z.next i o with
      | none => 0
      | some j => Z.survival n j

/-- Matrix action by the live kernel is the outcome-wise continuation sum. -/
lemma mulVec_liveKernel (Z : FiniteZipper (ι := ι) (Ω := Ω))
    (x : ι → ℝ≥0∞) (i : ι) :
    mulVec Z.liveKernel x i =
      ∑ o, Z.mass i o *
        match Z.next i o with
        | none => 0
        | some j => x j := by
  unfold mulVec liveKernel
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  cases hnext : Z.next i o with
  | none => simp
  | some j => simp

/-- The recursive survival probability is exactly the corresponding power
of the live transition matrix. -/
theorem survival_eq_iterate (Z : FiniteZipper (ι := ι) (Ω := Ω)) :
    ∀ n i, Z.survival n i = (mulVec Z.liveKernel)^[n] (fun _ => 1) i := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih =>
      intro i
      rw [survival, Function.iterate_succ_apply', Z.mulVec_liveKernel]
      apply Finset.sum_congr rfl
      intro o _
      cases hnext : Z.next i o with
      | none => simp
      | some j => simp [ih]

omit [Fintype ι] in
/-- A substochastic zipper survives for at most unit mass at every time. -/
lemma survival_le_one (Z : FiniteZipper (ι := ι) (Ω := Ω)) :
    ∀ n i, Z.survival n i ≤ 1 := by
  intro n
  induction n with
  | zero => intro i; simp [survival]
  | succ n ih =>
      intro i
      rw [survival]
      calc
        (∑ o, Z.mass i o *
            match Z.next i o with
            | none => 0
            | some j => Z.survival n j)
            ≤ ∑ o, Z.mass i o := by
              apply Finset.sum_le_sum
              intro o _
              cases hnext : Z.next i o with
              | none => simp
              | some j => simpa [hnext] using mul_le_mul_right (ih j) (Z.mass i o)
        _ = 1 := Z.mass_sum i

omit [Fintype ι] in
/-- A concrete closing cylinder and the `n`-step surviving mass fit inside
the full probability row. -/
theorem survival_add_pathMass_le_one
    (Z : FiniteZipper (ι := ι) (Ω := Ω)) :
    ∀ {n i os}, os.length ≤ n → Z.run (some i) os = none →
      Z.survival n i + Z.pathMass (some i) os ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro i os hlen hclose
      cases os with
      | nil => simp [run] at hclose
      | cons o os => simp at hlen
  | succ n ih =>
      intro i os hlen hclose
      cases os with
      | nil => simp [run] at hclose
      | cons o os =>
          have hlen' : os.length ≤ n := by simpa using hlen
          rw [survival, pathMass]
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ o)]
          cases hnext : Z.next i o with
          | none =>
              have hother :
                  (∑ x ∈ Finset.univ.erase o, Z.mass i x *
                    match Z.next i x with
                    | none => 0
                    | some j => Z.survival n j) ≤
                    ∑ x ∈ Finset.univ.erase o, Z.mass i x := by
                apply Finset.sum_le_sum
                intro x _
                cases hx : Z.next i x with
                | none => simp
                | some j =>
                    simpa [hx] using mul_le_mul_right (Z.survival_le_one n j) (Z.mass i x)
              simp only [mul_zero, add_zero]
              have hnone : Z.pathMass none os = 1 := by
                cases os <;> rfl
              rw [hnone, mul_one]
              calc
                (∑ x ∈ Finset.univ.erase o, Z.mass i x *
                    match Z.next i x with
                    | none => 0
                    | some j => Z.survival n j) + Z.mass i o
                    ≤ (∑ x ∈ Finset.univ.erase o, Z.mass i x) + Z.mass i o :=
                  add_le_add hother le_rfl
                _ = ∑ x, Z.mass i x :=
                  Finset.sum_erase_add _ _ (Finset.mem_univ o)
                _ = 1 := Z.mass_sum i
          | some j =>
              have hclose' : Z.run (some j) os = none := by
                simpa [run, hnext] using hclose
              have hpath := ih hlen' hclose'
              have hother :
                  (∑ x ∈ Finset.univ.erase o, Z.mass i x *
                    match Z.next i x with
                    | none => 0
                    | some k => Z.survival n k) ≤
                    ∑ x ∈ Finset.univ.erase o, Z.mass i x := by
                apply Finset.sum_le_sum
                intro x _
                cases hx : Z.next i x with
                | none => simp
                | some k =>
                    simpa [hx] using mul_le_mul_right (Z.survival_le_one n k) (Z.mass i x)
              change
                ((∑ x ∈ Finset.univ.erase o, Z.mass i x *
                    match Z.next i x with
                    | none => 0
                    | some k => Z.survival n k) +
                    Z.mass i o * Z.survival n j) +
                    Z.mass i o * Z.pathMass (some j) os ≤ 1
              calc
                ((∑ x ∈ Finset.univ.erase o, Z.mass i x *
                    match Z.next i x with
                    | none => 0
                    | some k => Z.survival n k) +
                    Z.mass i o * Z.survival n j) +
                    Z.mass i o * Z.pathMass (some j) os
                    = (∑ x ∈ Finset.univ.erase o, Z.mass i x *
                        match Z.next i x with
                        | none => 0
                        | some k => Z.survival n k) +
                        Z.mass i o *
                          (Z.survival n j + Z.pathMass (some j) os) := by
                            simp [mul_add, add_assoc]
                _ ≤ (∑ x ∈ Finset.univ.erase o, Z.mass i x) +
                      Z.mass i o * 1 :=
                  add_le_add hother (mul_le_mul_right hpath (Z.mass i o))
                _ = ∑ x, Z.mass i x := by
                  rw [mul_one, Finset.sum_erase_add _ _ (Finset.mem_univ o)]
                _ = 1 := Z.mass_sum i

/-- A closing word of mass at least `q`, of length at most `n`, gives the
exact `n`-step killed-kernel estimate. -/
theorem iterate_liveKernel_le_one_sub_of_closingWord
    (Z : FiniteZipper (ι := ι) (Ω := Ω)) {n : ℕ} {q : ℝ≥0∞}
    (hq1 : q ≤ 1) (i : ι) (os : List Ω)
    (hlen : os.length ≤ n) (hclose : Z.run (some i) os = none)
    (hmass : q ≤ Z.pathMass (some i) os) :
    (mulVec Z.liveKernel)^[n] (fun _ => 1) i ≤ 1 - q := by
  rw [← Z.survival_eq_iterate]
  apply ENNReal.le_sub_of_add_le_right
    (ne_top_of_le_ne_top ENNReal.one_ne_top hq1)
  calc
    Z.survival n i + q ≤ Z.survival n i + Z.pathMass (some i) os :=
      add_le_add_right hmass _
    _ ≤ 1 := Z.survival_add_pathMass_le_one hlen hclose

/-- A uniform lower bound on the closing outcomes gives a one-step killed
kernel estimate.  Macro outcomes may themselves encode a bounded correction
word, so this is the block estimate needed by the renewal resolvent. -/
lemma liveKernel_row_sum_le_one_sub {Z : FiniteZipper (ι := ι) (Ω := Ω)}
    {q : ℝ≥0∞} (hkill : ∀ i, q ≤ Z.killedMass i) (i : ι) :
    ∑ j, Z.liveKernel i j ≤ 1 - q := by
  have hq1 : q ≤ 1 := by
    calc
      q ≤ Z.killedMass i := hkill i
      _ ≤ (∑ j, Z.liveKernel i j) + Z.killedMass i := le_add_left le_rfl
      _ = 1 := Z.liveKernel_sum_add_killedMass i
  apply ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top ENNReal.one_ne_top hq1)
  calc
    (∑ j, Z.liveKernel i j) + q
        ≤ (∑ j, Z.liveKernel i j) + Z.killedMass i :=
          add_le_add le_rfl (hkill i)
    _ = 1 := Z.liveKernel_sum_add_killedMass i

/-- The actual linear screen kernel after integrating the label inverse
moment.  Crucially the counter kernel is not divided by an atom mass: all
live outcomes remain in `liveKernel`. -/
noncomputable def screenKernel
    (Z : FiniteZipper (ι := ι) (Ω := Ω)) (tilt : ι → ℝ≥0∞) :
    ι → ι → ℝ≥0∞ :=
  fun i j => tilt i * Z.liveKernel i j

/-- The integrated inverse-label moment attached to a phase.  `source i` is
the law carried by the distinguished source cell and `normalization i` is the
target law whose compatible degree normalizes that row. -/
noncomputable def integratedLabelTilt {X : Type} (α : ℝ)
    (source normalization : ι → PMF X) (R : X → X → Prop) (i : ι) : ℝ≥0∞ :=
  ∑' x, source i x * WresD α (normalization i) R x

omit [Fintype ι] in
/-- The existing inverse-moment lemma gives the promised `1 + O(eta)` phase
tilt for arbitrary (in particular cross-law) source and normalization laws. -/
lemma integratedLabelTilt_le {X : Type} {α : ℝ} (hα : 1 ≤ α)
    (source normalization : ι → PMF X) (R : X → X → Prop) {M : ℝ≥0∞}
    (hM : ∀ i, PhiDres α (source i) (normalization i) R ≤ M) (i : ι) :
    integratedLabelTilt α source normalization R i ≤
      1 + ENNReal.ofReal α * M := by
  calc
    integratedLabelTilt α source normalization R i ≤
        1 + ENNReal.ofReal α * PhiDres α (source i) (normalization i) R :=
      by simpa [integratedLabelTilt] using
        (tsum_WresD_le hα (source i) (normalization i) R)
    _ ≤ 1 + ENNReal.ofReal α * M := by
      gcongr
      exact hM i

omit [Fintype ι] in
/-- Hence the actual phase screen kernel is dominated by the killed counter
kernel with scalar `A = 1 + α M`; no offspring atom occurs in `A`. -/
lemma integrated_screenKernel_le {X : Type} {α : ℝ} (hα : 1 ≤ α)
    (Z : FiniteZipper (ι := ι) (Ω := Ω))
    (source normalization : ι → PMF X) (R : X → X → Prop) {M : ℝ≥0∞}
    (hM : ∀ i, PhiDres α (source i) (normalization i) R ≤ M) (i j : ι) :
    Z.screenKernel (integratedLabelTilt α source normalization R) i j ≤
      (1 + ENNReal.ofReal α * M) * Z.liveKernel i j := by
  exact mul_le_mul_left
    (integratedLabelTilt_le hα source normalization R hM i) _

/-- The screen kernel before using the full-retention identity: the label
moment is multiplied by the inverse power of the retained counter mass. -/
noncomputable def normalizedScreenKernel
    (Z : FiniteZipper (ι := ι) (Ω := Ω))
    (admissible : ι → Ω → Prop)
    [DecidablePred fun p : ι × Ω => admissible p.1 p.2]
    (α : ℝ) (labelTilt : ι → ℝ≥0∞) : ι → ι → ℝ≥0∞ :=
  fun i j => labelTilt i * (Z.retainedMass admissible i) ^ (-α) *
    Z.liveKernel i j

omit [Fintype ι] in
/-- Retaining every counter outcome removes the counter inverse degree
exactly, leaving the rowwise integrated label tilt. -/
lemma normalizedScreenKernel_eq_screenKernel_of_all
    (Z : FiniteZipper (ι := ι) (Ω := Ω))
    (admissible : ι → Ω → Prop)
    [DecidablePred fun p : ι × Ω => admissible p.1 p.2]
    (hall : ∀ i o, admissible i o) (α : ℝ) (labelTilt : ι → ℝ≥0∞) :
    Z.normalizedScreenKernel admissible α labelTilt =
      Z.screenKernel labelTilt := by
  funext i j
  rw [normalizedScreenKernel, screenKernel, Z.retainedMass_eq_one_of_all admissible hall]
  simp

omit [Fintype ι] in
/-- A rowwise inverse-moment bound gives the exact weighted domination used
by the renewal closure. -/
lemma screenKernel_le {Z : FiniteZipper (ι := ι) (Ω := Ω)}
    {tilt : ι → ℝ≥0∞} {A : ℝ≥0∞} (htilt : ∀ i, tilt i ≤ A) (i j : ι) :
    Z.screenKernel tilt i j ≤ A * Z.liveKernel i j := by
  exact mul_le_mul_left (htilt i) _

/-- A finite macro grammar with closing mass `q` has precisely the killed
estimate required by `dominated_resolvent_le`, with block length one. -/
lemma liveKernel_killed_one {Z : FiniteZipper (ι := ι) (Ω := Ω)}
    {q : ℝ≥0∞} (hkill : ∀ i, q ≤ Z.killedMass i) (i : ι) :
    (mulVec Z.liveKernel)^[1] (fun _ => 1) i ≤ 1 - q := by
  rw [Function.iterate_one, mulVec]
  simpa using Z.liveKernel_row_sum_le_one_sub hkill i

/-- The concrete finite-zipper Green bound. -/
theorem screenKernel_resolvent_le
    (Z : FiniteZipper (ι := ι) (Ω := Ω)) (tilt : ι → ℝ≥0∞)
    (A q : ℝ≥0∞) (htilt : ∀ i, tilt i ≤ A)
    (hkill : ∀ i, q ≤ Z.killedMass i) (i : ι) :
    infResolvent (Z.screenKernel tilt) (fun _ => 1) i ≤
      (1 - A * (1 - q))⁻¹ := by
  have h := dominated_resolvent_le (ι := ι) (H := 1) (A := A) (q := q)
    (W := Z.screenKernel tilt) (R := Z.liveKernel) (by omega)
    (Z.screenKernel_le htilt) Z.liveKernel_row_sum_le_one
    (Z.liveKernel_killed_one hkill) i
  simpa using h

/-- A selected positive-probability correction in every finite phase
automatically supplies some nonzero killing constant and hence a concrete
weighted Green bound. -/
theorem exists_positive_kill_screenKernel_resolvent
    (Z : FiniteZipper (ι := ι) (Ω := Ω))
    (selected : ι → Ω)
    (hclose : ∀ i, Z.next i (selected i) = none)
    (hpos : ∀ i, Z.mass i (selected i) ≠ 0)
    (tilt : ι → ℝ≥0∞) (A : ℝ≥0∞)
    (htilt : ∀ i, tilt i ≤ A) :
    ∃ q : ℝ≥0∞, q ≠ 0 ∧ ∀ i,
      infResolvent (Z.screenKernel tilt) (fun _ => 1) i ≤
        (1 - A * (1 - q))⁻¹ := by
  obtain ⟨q, hq, hkill⟩ := Z.exists_uniform_positive_kill selected hclose hpos
  exact ⟨q, hq, Z.screenKernel_resolvent_le tilt A q htilt hkill⟩

/-- **Finite-zipper screened closure.**  This is the instantiated endpoint
for a concrete finite outcome grammar.  The counter normalization is already
inside the probability kernel, so the contraction ratio is exactly
`A * (1-q)`; in applications `A = 1 + O(eta)`. -/
theorem screened_uniform_bound_finiteZipper
    (Z : FiniteZipper (ι := ι) (Ω := Ω)) (tilt : ι → ℝ≥0∞)
    (A q : ℝ≥0∞) (htilt : ∀ i, tilt i ≤ A)
    (hkill : ∀ i, q ≤ Z.killedMass i)
    (Kc η u Ξ : ℝ≥0∞)
    (hΞ : (1 - A * (1 - q))⁻¹ * u ≤ Ξ)
    (Ψ : ℕ → ℝ≥0∞) (E : ℕ → ι → ℝ≥0∞)
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (hf : ∀ a a' b b', a ≤ a' → b ≤ b' → f a b ≤ f a' b')
    (hg : ∀ a a' b b', a ≤ a' → b ≤ b' → g a b ≤ g a' b')
    (hΨ0 : Ψ 0 ≤ Kc * η)
    (hE0 : ∀ i, E 0 i ≤ u)
    (hΨstep : ∀ h, Ψ (h + 1) ≤ f (Ψ h) (⨆ i, E h i))
    (hEstep : ∀ h i,
      E (h + 1) i ≤ g (Ψ h) (⨆ j, E h j) +
        mulVecInf (Z.screenKernel tilt) (E h) i)
    (hu : g (Kc * η) Ξ ≤ u)
    (hclose : f (Kc * η) Ξ ≤ Kc * η) :
    ∀ h, Ψ h ≤ Kc * η := by
  apply screened_uniform_bound_dominated
    (Z.screenKernel tilt) Z.liveKernel A q 1 (by omega)
    (Z.screenKernel_le htilt) Z.liveKernel_row_sum_le_one
    (Z.liveKernel_killed_one hkill)
    Kc η u Ξ
  · simpa using hΞ
  · exact hf
  · exact hg
  · exact hΨ0
  · exact hE0
  · exact hΨstep
  · exact hEstep
  · exact hu
  · exact hclose

end FiniteZipper

end GraphMarkovMatching
