/-
Uniform heavy-component reductions for the `{3,5,7,9}` / `11,13`
two-law problem.

The old finite-support row bounded the inverse degree of a mixture by an
unweighted sum of component inverse degrees.  Applied to the exceptional
atom, that creates the forbidden factor `ε⁻ᵅ`.  The lemmas below instead
choose one charged heavy component.  On the set where that component has
positive degree, its mass minorizes the aggregate degree.  The complementary
set is retained as a genuine screen with the heavy component added to the
zero list.  Thus no inverse of any other atom is introduced.
-/
import GraphMarkovMatching.Obstructions.HeavyCore
import GraphMarkovMatching.Tail.Hybrid
import GraphMarkovMatching.Archive.VaryingTwoLawLedger
import GraphMarkovMatching.Process.ZMass

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {A X : Type}

/-- **Pointwise heavy-component split for a mixture inverse tilt.**  A
selected charged component controls the aggregate inverse degree wherever
that component is live.  Where it is dead, the whole aggregate tilt is
retained explicitly as debt. -/
lemma WresD_bind_le_component_add_dead (α : ℝ) (hα : 0 ≤ α)
    (w : PMF A) (f : A → PMF X) (R : X → X → Prop) (a : A)
    (ha : (w a : ℝ≥0∞) ≠ 0) (x : X) :
    WresD α (w.bind f) R x
      ≤ (w a : ℝ≥0∞) ^ (-α) * WresD α (f a) R x
        + (if rE (f a) R x = 0 then WresD α (w.bind f) R x else 0) := by
  by_cases hcomp : rE (f a) R x = 0
  · rw [if_pos hcomp]
    exact le_add_left le_rfl
  · rw [if_neg hcomp, add_zero]
    have hmix : rE (w.bind f) R x ≠ 0 := by
      intro hzero
      have hmin := mul_rE_le_rE_bind w f R x a
      rw [hzero] at hmin
      exact (mul_ne_zero ha hcomp) (le_antisymm hmin zero_le)
    have hmin : (w a : ℝ≥0∞) * rE (f a) R x
        ≤ rE (w.bind f) R x :=
      mul_rE_le_rE_bind w f R x a
    rw [← rE_rpow_neg_eq_WresD (w.bind f) R x hmix,
      ← rE_rpow_neg_eq_WresD (f a) R x hcomp,
      ← ENNReal.mul_rpow_of_ne_zero ha hcomp (-α)]
    exact rpow_neg_antitone hα hmin

/-- The dead part in the pointwise heavy-component split is exactly the
screen obtained by adjoining the heavy component to the zero list. -/
lemma screenE_bind_WresD_le_component_add_screen (α : ℝ) (hα : 0 ≤ α)
    (ρs : PMF X) (w : PMF A) (f : A → PMF X) (R : X → X → Prop)
    (a : A) (ha : (w a : ℝ≥0∞) ≠ 0) (zs : List (PMF X)) :
    screenE ρs R zs (WresD α (w.bind f) R)
      ≤ (w a : ℝ≥0∞) ^ (-α)
          * screenE ρs R zs (WresD α (f a) R)
        + screenE ρs R (f a :: zs) (WresD α (w.bind f) R) := by
  rw [screenE, screenE, screenE, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hcomp : rE (f a) R x = 0
  · have hcons : screenInd R (f a :: zs) x = screenInd R zs x := by
      rw [screenInd, screenInd]
      by_cases hall : ∀ ρ ∈ zs, rE ρ R x = 0
      · rw [if_pos hall, if_pos]
        intro ρ hρ
        simp only [List.mem_cons] at hρ
        rcases hρ with hρ | hρ
        · simpa [hρ] using hcomp
        · exact hall ρ hρ
      · rw [if_neg hall, if_neg]
        intro h
        exact hall fun ρ hρ => h ρ (List.mem_cons_of_mem _ hρ)
    rw [hcons]
    exact le_add_left le_rfl
  · have hcons : screenInd R (f a :: zs) x = 0 := by
      rw [screenInd, if_neg]
      exact fun hall => hcomp (hall (f a) (List.mem_cons_self))
    rw [hcons, mul_zero, zero_mul, add_zero]
    calc
      ρs x * screenInd R zs x * WresD α (w.bind f) R x
          ≤ ρs x * screenInd R zs x
              * ((w a : ℝ≥0∞) ^ (-α) * WresD α (f a) R x) :=
        mul_le_mul_right
          (WresD_bind_le_component_add_dead α hα w f R a ha x |>
            (by simpa [hcomp] using ·)) _
      _ = (w a : ℝ≥0∞) ^ (-α)
          * (ρs x * screenInd R zs x * WresD α (f a) R x) := by ring

/-- Uniform form of the screen split when the chosen component has mass at
least `1/8`.  This is the coefficient needed by the four-point heavy-core
ledger; it is independent of `ε` and of the other three common weights. -/
lemma screenE_bind_WresD_le_eight_rpow_add_screen (α : ℝ) (hα : 0 ≤ α)
    (ρs : PMF X) (w : PMF A) (f : A → PMF X) (R : X → X → Prop)
    (a : A) (ha : 8⁻¹ ≤ (w a : ℝ≥0∞)) (zs : List (PMF X)) :
    screenE ρs R zs (WresD α (w.bind f) R)
      ≤ (8 : ℝ≥0∞) ^ α * screenE ρs R zs (WresD α (f a) R)
        + screenE ρs R (f a :: zs) (WresD α (w.bind f) R) := by
  have ha0 : (w a : ℝ≥0∞) ≠ 0 := by
    intro hzero
    rw [hzero] at ha
    norm_num at ha
  refine le_trans
    (screenE_bind_WresD_le_component_add_screen α hα ρs w f R a ha0 zs)
    (add_le_add ?_ le_rfl)
  refine mul_le_mul_left ?_ _
  calc
    (w a : ℝ≥0∞) ^ (-α) ≤ ((8 : ℝ≥0∞)⁻¹) ^ (-α) :=
      rpow_neg_antitone hα ha
    _ = (8 : ℝ≥0∞) ^ α := by
      rw [ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]

/-- **Heavy replacement for the inverse-atom one-sided bound.**  If some
charged component is dead, either the selected heavy component is itself
dead (the first screen), or it is live and controls the aggregate inverse
tilt.  In the latter case only an unweighted finite sum of screens remains;
no inverse mass of the dead component occurs. -/
lemma component_dead_exists_le_heavy (α : ℝ) (hα : 0 ≤ α)
    (ρs : PMF X) (w : PMF A) (f : A → PMF X) (R : X → X → Prop)
    (a : A) (ha : (w a : ℝ≥0∞) ≠ 0) :
    (∑' x, ρs x
        * ((if ∃ j, (w j : ℝ≥0∞) ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0)
          * WresD α (w.bind f) R x))
      ≤ screenE ρs R [f a] (WresD α (w.bind f) R)
        + (w a : ℝ≥0∞) ^ (-α) *
            ∑' j, if (w j : ℝ≥0∞) = 0 then 0
              else screenE ρs R [f j] (WresD α (f a) R) := by
  have hpoint : ∀ x,
      ρs x *
          ((if ∃ j, (w j : ℝ≥0∞) ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0)
            * WresD α (w.bind f) R x)
        ≤ ρs x *
            ((if rE (f a) R x = 0 then 1 else 0)
              * WresD α (w.bind f) R x)
          + (w a : ℝ≥0∞) ^ (-α) *
              ∑' j, if (w j : ℝ≥0∞) = 0 then 0
                else ρs x * ((if rE (f j) R x = 0 then 1 else 0)
                  * WresD α (f a) R x) := by
    intro x
    by_cases hex : ∃ j, (w j : ℝ≥0∞) ≠ 0 ∧ rE (f j) R x = 0
    · rw [if_pos hex]
      by_cases hcomp : rE (f a) R x = 0
      · rw [if_pos hcomp, one_mul]
        exact le_add_right le_rfl
      · rw [if_neg hcomp, zero_mul, mul_zero, zero_add]
        obtain ⟨j, hjw, hjdead⟩ := hex
        have htilt : WresD α (w.bind f) R x
            ≤ (w a : ℝ≥0∞) ^ (-α) * WresD α (f a) R x := by
          simpa [hcomp] using
            WresD_bind_le_component_add_dead α hα w f R a ha x
        calc
          ρs x * (1 * WresD α (w.bind f) R x)
              ≤ (w a : ℝ≥0∞) ^ (-α)
                  * (ρs x * WresD α (f a) R x) := by
                rw [one_mul]
                refine le_trans (mul_le_mul_right htilt _) ?_
                exact le_of_eq (by ring)
          _ = (w a : ℝ≥0∞) ^ (-α) *
                (if (w j : ℝ≥0∞) = 0 then 0
                  else ρs x * ((if rE (f j) R x = 0 then 1 else 0)
                    * WresD α (f a) R x)) := by
                rw [if_neg hjw, if_pos hjdead, one_mul]
          _ ≤ (w a : ℝ≥0∞) ^ (-α) *
                ∑' j, if (w j : ℝ≥0∞) = 0 then 0
                  else ρs x * ((if rE (f j) R x = 0 then 1 else 0)
                    * WresD α (f a) R x) := by
                exact mul_le_mul_right (ENNReal.le_tsum j) _
    · rw [if_neg hex, zero_mul, mul_zero]
      exact zero_le
  calc
    (∑' x, ρs x
        * ((if ∃ j, (w j : ℝ≥0∞) ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0)
          * WresD α (w.bind f) R x))
        ≤ ∑' x, (ρs x *
            ((if rE (f a) R x = 0 then 1 else 0)
              * WresD α (w.bind f) R x)
          + (w a : ℝ≥0∞) ^ (-α) *
              ∑' j, if (w j : ℝ≥0∞) = 0 then 0
                else ρs x * ((if rE (f j) R x = 0 then 1 else 0)
                  * WresD α (f a) R x)) :=
          ENNReal.tsum_le_tsum hpoint
    _ = (∑' x, ρs x *
            ((if rE (f a) R x = 0 then 1 else 0)
              * WresD α (w.bind f) R x))
          + (w a : ℝ≥0∞) ^ (-α) *
              ∑' x, ∑' j, if (w j : ℝ≥0∞) = 0 then 0
                else ρs x * ((if rE (f j) R x = 0 then 1 else 0)
                  * WresD α (f a) R x) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ = screenE ρs R [f a] (WresD α (w.bind f) R)
          + (w a : ℝ≥0∞) ^ (-α) *
              ∑' j, ∑' x, if (w j : ℝ≥0∞) = 0 then 0
                else ρs x * ((if rE (f j) R x = 0 then 1 else 0)
                  * WresD α (f a) R x) := by
            rw [screenE_singleton, ENNReal.tsum_comm]
    _ = screenE ρs R [f a] (WresD α (w.bind f) R)
          + (w a : ℝ≥0∞) ^ (-α) *
              ∑' j, if (w j : ℝ≥0∞) = 0 then 0
                else screenE ρs R [f j] (WresD α (f a) R) := by
            congr 1
            congr 1
            refine tsum_congr fun j => ?_
            by_cases hj : (w j : ℝ≥0∞) = 0
            · simp [hj]
            · simp_rw [if_neg hj]
              rw [screenE_singleton]

/-- Uniform `1/8` specialization of
`component_dead_exists_le_heavy`. -/
lemma component_dead_exists_le_eight (α : ℝ) (hα : 0 ≤ α)
    (ρs : PMF X) (w : PMF A) (f : A → PMF X) (R : X → X → Prop)
    (a : A) (ha : 8⁻¹ ≤ (w a : ℝ≥0∞)) :
    (∑' x, ρs x
        * ((if ∃ j, (w j : ℝ≥0∞) ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0)
          * WresD α (w.bind f) R x))
      ≤ screenE ρs R [f a] (WresD α (w.bind f) R)
        + (8 : ℝ≥0∞) ^ α *
            ∑' j, if (w j : ℝ≥0∞) = 0 then 0
              else screenE ρs R [f j] (WresD α (f a) R) := by
  have ha0 : (w a : ℝ≥0∞) ≠ 0 := by
    intro hzero
    rw [hzero] at ha
    norm_num at ha
  refine le_trans (component_dead_exists_le_heavy α hα ρs w f R a ha0)
    (add_le_add le_rfl ?_)
  refine mul_le_mul_left ?_ _
  calc
    (w a : ℝ≥0∞) ^ (-α) ≤ ((8 : ℝ≥0∞)⁻¹) ^ (-α) :=
      rpow_neg_antitone hα ha
    _ = (8 : ℝ≥0∞) ^ α := by
      rw [ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]

/-- A component-dead screen normalized by the aggregate mixture is already
paid by the aggregate ordinary potential after multiplication by the
component mass.  On the component-dead set the aggregate bad degree is at
least that mass. -/
lemma component_mass_mul_screen_bind_WresD_le_PhiDres
    (α : ℝ) (hα : 0 < α) (ρs : PMF X) (w : PMF A)
    (f : A → PMF X) (R : X → X → Prop) (a : A) :
    (w a : ℝ≥0∞) * screenE ρs R [f a] (WresD α (w.bind f) R)
      ≤ PhiDres α ρs (w.bind f) R := by
  rw [screenE_singleton, PhiDres, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hcomp : rE (f a) R x = 0
  · rw [if_pos hcomp]
    by_cases hmix : rE (w.bind f) R x = 0
    · simp [WresD, hmix]
    · rw [if_neg hmix]
      have hqcomp : qE (f a) R x = 1 := by
        have hsum := rE_add_qE (f a) R x
        rw [hcomp, zero_add] at hsum
        exact hsum
      have hq : (w a : ℝ≥0∞) ≤ qE (w.bind f) R x := by
        rw [qE_bind]
        calc
          (w a : ℝ≥0∞) = (w a : ℝ≥0∞) * qE (f a) R x := by rw [hqcomp, mul_one]
          _ ≤ ∑' b, (w b : ℝ≥0∞) * qE (f b) R x := ENNReal.le_tsum a
      rw [phiE_eq_qE_mul_rpow α R (w.bind f) hα x,
        rE_rpow_neg_eq_WresD (w.bind f) R x hmix]
      calc
        (w a : ℝ≥0∞) *
              (ρs x * (1 * WresD α (w.bind f) R x))
            = ρs x * ((w a : ℝ≥0∞) * WresD α (w.bind f) R x) := by ring
        _ ≤ ρs x *
              (qE (w.bind f) R x * WresD α (w.bind f) R x) :=
            mul_le_mul_right (mul_le_mul_left hq _) _
  · rw [if_neg hcomp, zero_mul, mul_zero, mul_zero]
    exact zero_le

/-- Uniform consequence of the preceding lemma for a component of mass at
least `1/8`. -/
lemma screen_bind_WresD_component_dead_le_eight_PhiDres
    (α : ℝ) (hα : 0 < α) (ρs : PMF X) (w : PMF A)
    (f : A → PMF X) (R : X → X → Prop) (a : A)
    (ha : 8⁻¹ ≤ (w a : ℝ≥0∞)) :
    screenE ρs R [f a] (WresD α (w.bind f) R)
      ≤ 8 * PhiDres α ρs (w.bind f) R := by
  let E := screenE ρs R [f a] (WresD α (w.bind f) R)
  let P := PhiDres α ρs (w.bind f) R
  have hEP : 8⁻¹ * E ≤ P := by
    exact le_trans (mul_le_mul_left ha E)
      (component_mass_mul_screen_bind_WresD_le_PhiDres α hα ρs w f R a)
  calc
    E = 8 * (8⁻¹ * E) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel]
      · rw [one_mul]
      · norm_num
      · norm_num
    _ ≤ 8 * P := mul_le_mul_right hEP 8

/-- Fully closed uniform one-sided estimate: the aggregate-normalized
heavy-dead term returns to the ordinary potential, while every other dead
component is charged by a screen normalized by the fixed heavy component.
Neither output contains an inverse exceptional mass. -/
lemma component_dead_exists_le_eight_closed
    (α : ℝ) (hα : 0 < α) (ρs : PMF X) (w : PMF A)
    (f : A → PMF X) (R : X → X → Prop) (a : A)
    (ha : 8⁻¹ ≤ (w a : ℝ≥0∞)) :
    (∑' x, ρs x
        * ((if ∃ j, (w j : ℝ≥0∞) ≠ 0 ∧ rE (f j) R x = 0 then 1 else 0)
          * WresD α (w.bind f) R x))
      ≤ 8 * PhiDres α ρs (w.bind f) R
        + (8 : ℝ≥0∞) ^ α *
            ∑' j, if (w j : ℝ≥0∞) = 0 then 0
              else screenE ρs R [f j] (WresD α (f a) R) := by
  exact le_trans (component_dead_exists_le_eight α hα.le ρs w f R a ha)
    (add_le_add
      (screen_bind_WresD_component_dead_le_eight_PhiDres
        α hα ρs w f R a ha)
      le_rfl)

/-! ### Probability-retaining unit-tilt mixture rows -/

/-- Unit zero-interface mass is exactly linear in its source law.  This is
the unit-tilt counterpart of `screenE_bind_left`. -/
lemma zMass_bind_left (w : PMF A) (f : A → PMF X) (ρt : PMF X)
    (R : X → X → Prop) :
    zMass (w.bind f) ρt R = ∑' a, w a * zMass (f a) ρt R := by
  rw [zMass, tsum_bind_mul]
  exact tsum_congr fun a => by rw [zMass]

/-- A charged component of a target mixture dominates the zero event of the
whole target mixture.  No inverse component mass is used: a zero aggregate
degree forces every charged component degree to vanish. -/
lemma zMass_bind_right_le_component (ρs : PMF X) (w : PMF A)
    (f : A → PMF X) (R : X → X → Prop) (a : A)
    (ha : (w a : ℝ≥0∞) ≠ 0) :
    zMass ρs (w.bind f) R ≤ zMass ρs (f a) R := by
  rw [zMass, zMass]
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  by_cases hmix : rE (w.bind f) R x = 0
  · rw [if_pos hmix]
    have hcomp : rE (f a) R x = 0 := by
      rcases (rE_bind_eq_zero_iff w f R x).mp hmix a with hwa | hfa
      · exact (ha hwa).elim
      · exact hfa
    rw [if_pos hcomp]
  · rw [if_neg hmix]
    exact zero_le

/-- Combining source linearity with heavy-target domination preserves every
source mixture coefficient.  This is the basic unit-tilt debt row needed by
the two-law example. -/
lemma zMass_bind_bind_le_component (wa : PMF A) (fa : A → PMF X)
    (wb : PMF A) (fb : A → PMF X) (R : X → X → Prop) (b : A)
    (hb : (wb b : ℝ≥0∞) ≠ 0) :
    zMass (wa.bind fa) (wb.bind fb) R
      ≤ ∑' a, wa a * zMass (fa a) (fb b) R := by
  rw [zMass_bind_left]
  exact ENNReal.tsum_le_tsum fun a =>
    mul_le_mul_right (zMass_bind_right_le_component (fa a) wb fb R b hb) _

/-! ### Specialization to the asymmetric fresh-target row -/

/-- **Uniform heavy-core one-sided row.**  This is the exact replacement
for `crossOneSided_le_ledger` in the four-point example.  The old bound used
the sum of all inverse offspring masses.  Here one target atom of mass at
least `1/8` is selected; the output contains only the aggregate ordinary
potential and fixed-heavy-normalized component screens. -/
theorem crossOneSided_le_heavy
    {V : Type} (α : ℝ) (hα : 0 < α) (Rv : V → V → Prop)
    (μ : PMF V) (νL νR : PMF ℕ) (v0 : V) (k i h : ℕ)
    (hi : 8⁻¹ ≤ (νR i : ℝ≥0∞)) (SR : Finset ℕ)
    (hRsupp : ∀ j : ℕ, (νR j : ℝ≥0∞) ≠ 0 ↔ j ∈ SR)
    (M E : ℝ≥0∞)
    (hPhi : PhiDres α (Xi μ νL v0 k h) (XiBar μ νR v0 h)
        (SquareRel (fullSim (labRel Rv) h)) ≤ M)
    (hScreen : ∀ j ∈ SR,
      screenE (Xi μ νL v0 k h) (SquareRel (fullSim (labRel Rv) h))
        [Xi μ νR v0 j h]
        (WresD α (Xi μ νR v0 i h)
          (SquareRel (fullSim (labRel Rv) h))) ≤ E) :
    (∑' xp, Xi μ νL v0 k h xp
      * ((if ∃ j, νR j ≠ 0 ∧ rE (Xi μ νR v0 j h)
          (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
        * WresD α (XiBar μ νR v0 h)
          (SquareRel (fullSim (labRel Rv) h)) xp))
      ≤ 8 * M + (8 : ℝ≥0∞) ^ α * (SR.card * E) := by
  let R2 := SquareRel (fullSim (labRel Rv) h)
  have hcore := component_dead_exists_le_eight_closed α hα
    (Xi μ νL v0 k h) νR (fun j => Xi μ νR v0 j h) R2 i hi
  refine le_trans hcore (add_le_add (mul_le_mul_right hPhi 8) ?_)
  refine mul_le_mul_right ?_ ((8 : ℝ≥0∞) ^ α)
  have hout : ∀ j ∉ SR,
      (if (νR j : ℝ≥0∞) = 0 then 0
        else screenE (Xi μ νL v0 k h) R2 [Xi μ νR v0 j h]
          (WresD α (Xi μ νR v0 i h) R2)) = 0 := by
    intro j hj
    have hz : (νR j : ℝ≥0∞) = 0 := by
      by_contra hn
      exact hj ((hRsupp j).mp hn)
    simp [hz]
  rw [tsum_eq_sum hout]
  calc
    (∑ j ∈ SR, if (νR j : ℝ≥0∞) = 0 then 0
      else screenE (Xi μ νL v0 k h) R2 [Xi μ νR v0 j h]
        (WresD α (Xi μ νR v0 i h) R2))
        ≤ ∑ _j ∈ SR, E := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [if_neg ((hRsupp j).mpr hj)]
          exact hScreen j hj
    _ = SR.card * E := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Probability-retaining unit fresh-mixture row.**  Selecting any charged
right offspring component turns the cross zero mass of the two fresh child
mixtures into the left-offspring-weighted sum of fixed-component zero masses.
In particular the left exceptional term keeps its factor `νL 11`; no inverse
of `νR i` or of an unused common atom occurs. -/
theorem zMass_XiBar_cross_le_heavy_component
    {V : Type} (Rv : V → V → Prop) (μ : PMF V)
    (νL νR : PMF ℕ) (v0 : V) (i h : ℕ)
    (hi : (νR i : ℝ≥0∞) ≠ 0) :
    zMass (XiBar μ νL v0 h) (XiBar μ νR v0 h)
        (SquareRel (fullSim (labRel Rv) h))
      ≤ ∑' k, νL k *
          zMass (Xi μ νL v0 k h) (Xi μ νR v0 i h)
            (SquareRel (fullSim (labRel Rv) h)) := by
  exact zMass_bind_bind_le_component νL (fun k => Xi μ νL v0 k h)
    νR (fun j => Xi μ νR v0 j h)
    (SquareRel (fullSim (labRel Rv) h)) i hi

/-- The exact level-synchronous child-screen output of a fixed pair of
offspring components.  Every term comes from the literal straight-or-crossed
`SquareRel` Hall factorization; no flat exit pairing is used. -/
noncomputable def unitXiChildDebt {V : Type} (Rv : V → V → Prop)
    (μ : PMF V) (νL νR : PMF ℕ) (v0 : V) (k i h : ℕ) : ℝ≥0∞ :=
  let R := fullSim (labRel Rv) h
  let L0 := interpT μ νL v0 h (gcomp0 k)
  let L1 := interpT μ νL v0 h (gcomp1 k)
  let R0 := interpT μ νR v0 h (gcomp0 i)
  let R1 := interpT μ νR v0 h (gcomp1 i)
  screenE L0 R [R0, R1] (fun _ => 1)
    + screenE L1 R [R0, R1] (fun _ => 1)
    + screenE L0 R [R0] (fun _ => 1)
        * screenE L1 R [R0] (fun _ => 1)
    + screenE L0 R [R1] (fun _ => 1)
        * screenE L1 R [R1] (fun _ => 1)

/-- A fixed-component cross zero mass is bounded by its four literal
level-synchronous Hall charges. -/
theorem zMass_Xi_cross_le_unitXiChildDebt
    {V : Type} (Rv : V → V → Prop) (μ : PMF V)
    (νL νR : PMF ℕ) (v0 : V) (k i h : ℕ) :
    zMass (Xi μ νL v0 k h) (Xi μ νR v0 i h)
        (SquareRel (fullSim (labRel Rv) h))
      ≤ unitXiChildDebt Rv μ νL νR v0 k i h := by
  rw [Xi_eq_prod μ νL v0 k h, Xi_eq_prod μ νR v0 i h, zMass]
  exact deadMass_factorize
    (interpT μ νL v0 h (gcomp0 k))
    (interpT μ νL v0 h (gcomp1 k))
    (interpT μ νR v0 h (gcomp0 i))
    (interpT μ νR v0 h (gcomp1 i))
    (fullSim (labRel Rv) h)

/-- Combined unit-debt entrance and one-step descendant factorization.  The
source weights remain outside the four child-screen charges. -/
theorem zMass_XiBar_cross_le_weighted_child_debt
    {V : Type} (Rv : V → V → Prop) (μ : PMF V)
    (νL νR : PMF ℕ) (v0 : V) (i h : ℕ)
    (hi : (νR i : ℝ≥0∞) ≠ 0) :
    zMass (XiBar μ νL v0 h) (XiBar μ νR v0 h)
        (SquareRel (fullSim (labRel Rv) h))
      ≤ ∑' k, νL k * unitXiChildDebt Rv μ νL νR v0 k i h := by
  refine le_trans
    (zMass_XiBar_cross_le_heavy_component Rv μ νL νR v0 i h hi) ?_
  exact ENNReal.tsum_le_tsum fun k => mul_le_mul_right
    (zMass_Xi_cross_le_unitXiChildDebt Rv μ νL νR v0 k i h) _

end GraphMarkovMatching
