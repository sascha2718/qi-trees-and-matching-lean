/-
Finite recursive product estimates for the grafted 11/13 replacement counters.

The crucial consequence is support positivity: once the one-coordinate
directed potential is finite, every charged finite frontier word has positive
degree into the opposite-law replacement component.  This discharges the
semantic support premise in the direct Hall minorization theorem.
-/
import GraphMarkovMatching.Archive.VaryingGraftedReplacement
import GraphMarkovMatching.Potential.DirectedProduct

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

def ProductPower (X : Type) : ℕ → Type
  | 0 => PUnit
  | n + 1 => X × ProductPower X n

noncomputable def iidProductPower {X : Type} (ρ : PMF X) :
    (n : ℕ) → PMF (ProductPower X n)
  | 0 => PMF.pure PUnit.unit
  | n + 1 => prodPMF ρ (iidProductPower ρ n)

def productPowerRel {X : Type} (R : X → X → Prop) :
    (n : ℕ) → ProductPower X n → ProductPower X n → Prop
  | 0 => fun _ _ => True
  | n + 1 => ProdRel R (productPowerRel R n)

noncomputable def iteratedProductBound (α : ℝ) (M : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 0
  | n + 1 => M + iteratedProductBound α M n +
      ENNReal.ofReal (2 * α) * (M * iteratedProductBound α M n)

lemma PhiD_pure_punit (α : ℝ) :
    PhiD α (PMF.pure PUnit.unit) (PMF.pure PUnit.unit)
      (fun _ _ : PUnit => True) = 0 := by
  rw [PhiD]
  simp [q, qE]

/-- A product of `n` directed coordinates, each of potential at most `M`,
has the explicit iterated product-lemma bound. -/
theorem PhiD_iidProductPower_le {X : Type} {α : ℝ} (hα : 1 ≤ α)
    (ρs ρt : PMF X) (R : X → X → Prop) (M : ℝ≥0∞)
    (hM : PhiD α ρs ρt R ≤ M) :
    ∀ n, PhiD α (iidProductPower ρs n) (iidProductPower ρt n)
      (productPowerRel R n) ≤ iteratedProductBound α M n := by
  intro n
  induction n with
  | zero =>
      change PhiD α (PMF.pure PUnit.unit) (PMF.pure PUnit.unit)
        (fun _ _ : PUnit => True) ≤ 0
      rw [PhiD_pure_punit]
  | succ n ih =>
      calc
        PhiD α (iidProductPower ρs (n + 1)) (iidProductPower ρt (n + 1))
            (productPowerRel R (n + 1))
          ≤ PhiD α ρs ρt R +
              PhiD α (iidProductPower ρs n) (iidProductPower ρt n)
                (productPowerRel R n) +
            ENNReal.ofReal (2 * α) *
              (PhiD α ρs ρt R *
                PhiD α (iidProductPower ρs n) (iidProductPower ρt n)
                  (productPowerRel R n)) := by
            change PhiD α (prodPMF ρs (iidProductPower ρs n))
              (prodPMF ρt (iidProductPower ρt n))
              (ProdRel R (productPowerRel R n)) ≤ _
            exact PhiD_prodPMF_le hα ρs ρt
              (iidProductPower ρs n) (iidProductPower ρt n)
              R (productPowerRel R n)
        _ ≤ M + iteratedProductBound α M n +
            ENNReal.ofReal (2 * α) *
              (M * iteratedProductBound α M n) := by gcongr
        _ = iteratedProductBound α M (n + 1) := rfl

lemma iteratedProductBound_ne_top {α : ℝ} {M : ℝ≥0∞} (hM : M ≠ ⊤) :
    ∀ n, iteratedProductBound α M n ≠ ⊤ := by
  intro n
  induction n with
  | zero => simp [iteratedProductBound]
  | succ n ih =>
      simp only [iteratedProductBound]
      exact ENNReal.add_ne_top.2
        ⟨ENNReal.add_ne_top.2 ⟨hM, ih⟩,
          ENNReal.mul_ne_top (ENNReal.ofReal_ne_top)
            (ENNReal.mul_ne_top hM ih)⟩

/-- Finiteness of a directed potential forces positive target degree on
every charged source atom. -/
lemma rE_ne_zero_of_PhiD_ne_top {X : Type} {α : ℝ}
    {ρs ρt : PMF X} {R : X → X → Prop}
    (hfin : PhiD α ρs ρt R ≠ ⊤) {x : X} (hx : ρs x ≠ 0) :
    rE ρt R x ≠ 0 := by
  have hq := q_lt_one_of_charged hfin hx
  intro hr
  have hsum := rE_add_qE ρt R x
  rw [hr, zero_add] at hsum
  have hqone : q ρt R x = 1 := by
    rw [q, hsum, ENNReal.toReal_one]
  rw [hqone] at hq
  exact (lt_irrefl 1) hq

/-- The iterated product component is support-positive whenever the one-site
directed potential has a finite ceiling. -/
theorem iidProductPower_support_positive {X : Type} {α : ℝ} (hα : 1 ≤ α)
    (ρs ρt : PMF X) (R : X → X → Prop) (M : ℝ≥0∞)
    (hMtop : M ≠ ⊤) (hM : PhiD α ρs ρt R ≤ M) (n : ℕ) :
    ∀ x, iidProductPower ρs n x ≠ 0 →
      rE (iidProductPower ρt n) (productPowerRel R n) x ≠ 0 := by
  have hprod := PhiD_iidProductPower_le hα ρs ρt R M hM n
  have hfin : PhiD α (iidProductPower ρs n) (iidProductPower ρt n)
      (productPowerRel R n) ≠ ⊤ :=
    ne_top_of_le_ne_top (iteratedProductBound_ne_top hMtop n) hprod
  exact fun _ hx => rE_ne_zero_of_PhiD_ne_top hfin hx

end GraphMarkovMatching
