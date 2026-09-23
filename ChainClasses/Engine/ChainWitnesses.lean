import ChainClasses.Engine.ReducedProfiles
import Mathlib.Algebra.Group.Submonoid.Membership

/-! Two explicit chain offspring laws with the same unary mass and distinct reduced
branching semigroups. -/

namespace ChainClasses.ChainWitnesses

open BranchingProcess (Offspring)
open scoped ENNReal Classical

noncomputable def theta2 : Offspring 2 where
  mass := fun k => if k = 1 ∨ k = 2 then 1 / 2 else 0
  nonneg := by intro k; split_ifs <;> norm_num
  vanishing := by intro k hk; rw [ite_eq_right (by omega)]
  total := by norm_num [Finset.sum_range_succ]

noncomputable def theta3 : Offspring 3 where
  mass := fun k => if k = 1 ∨ k = 3 then 1 / 2 else 0
  nonneg := by intro k; split_ifs <;> norm_num
  vanishing := by intro k hk; rw [ite_eq_right (by omega)]
  total := by norm_num [Finset.sum_range_succ]

@[simp] lemma theta2_apply (k : ℕ) : theta2 k = if k = 1 ∨ k = 2 then 1 / 2 else 0 := rfl
@[simp] lemma theta3_apply (k : ℕ) : theta3 k = if k = 1 ∨ k = 3 then 1 / 2 else 0 := rfl
@[simp] lemma theta2_zero : theta2 0 = 0 := by norm_num
@[simp] lemma theta3_zero : theta3 0 = 0 := by norm_num
@[simp] lemma theta2_one : theta2 1 = 1 / 2 := by norm_num
@[simp] lemma theta3_one : theta3 1 = 1 / 2 := by norm_num
@[simp] lemma theta2_top : theta2 2 = 1 / 2 := by norm_num
@[simp] lemma theta3_top : theta3 3 = 1 / 2 := by norm_num
lemma theta2_top_pos : 0 < theta2 2 := by norm_num
lemma theta3_top_pos : 0 < theta3 3 := by norm_num
lemma theta2_one_pos : 0 < theta2 1 := by norm_num
lemma theta3_one_pos : 0 < theta3 1 := by norm_num
lemma theta2_one_lt_one : theta2 1 < 1 := by norm_num
lemma theta3_one_lt_one : theta3 1 < 1 := by norm_num

@[simp] lemma shiftSupp_theta2 : shiftSupp theta2 = {1} := by
  ext x
  rw [mem_shiftSupp]
  simp only [theta2_apply, ne_eq, Finset.mem_singleton]
  by_cases hx : x = 1
  · subst x; norm_num
  · by_cases hz : x = 0
    · subst x; norm_num
    · rw [ite_eq_right (by omega)]
      simp [hx]

@[simp] lemma shiftSupp_theta3 : shiftSupp theta3 = {2} := by
  ext x
  rw [mem_shiftSupp]
  simp only [theta3_apply, ne_eq, Finset.mem_singleton]
  by_cases hx : x = 2
  · subst x; norm_num
  · by_cases hz : x = 0
    · subst x; norm_num
    · rw [ite_eq_right (by omega)]
      simp [hx]

/-- The reduced binary and ternary arities generate different additive semigroups. -/
theorem semigroups_ne :
    AddSubmonoid.closure (shiftSupp theta2 : Set ℕ) ≠
      AddSubmonoid.closure (shiftSupp theta3 : Set ℕ) := by
  rw [shiftSupp_theta2, shiftSupp_theta3, Finset.coe_singleton, Finset.coe_singleton]
  intro heq
  have h : 1 ∈ AddSubmonoid.closure ({2} : Set ℕ) :=
    heq ▸ AddSubmonoid.subset_closure (by simp : 1 ∈ ({1} : Set ℕ))
  obtain ⟨n, hn⟩ := AddSubmonoid.mem_closure_singleton.mp h
  simp only [nsmul_eq_mul] at hn
  omega

/-- Suppressing unary vertices leaves the deterministic binary arity law. -/
theorem reducedPMF_theta2 (hq : theta2.extinction < 1) (hs1 : theta2.skeletonWeight 1 < 1)
    (hJ : 2 ≤ 2) : reducedPMF theta2 hq hs1 hJ = PMF.pure 2 := by
  ext k
  rw [reducedPMF_apply, PMF.pure_apply]
  by_cases hk : k = 2
  · subst k
    rw [ite_eq_left (by omega), ite_eq_left rfl, reducedWeight_def,
      skeletonWeight_eq_of_chain theta2 theta2_zero,
      skeletonWeight_eq_of_chain theta2 theta2_zero]
    norm_num
  · rw [ite_eq_right hk]
    by_cases h2 : 2 ≤ k
    · rw [ite_eq_left h2, reducedWeight_def,
        skeletonWeight_eq_of_chain theta2 theta2_zero,
        skeletonWeight_eq_of_chain theta2 theta2_zero, theta2_apply,
        ite_eq_right (by omega)]
      simp
    · rw [ite_eq_right h2]

/-- Suppressing unary vertices leaves the deterministic ternary arity law. -/
theorem reducedPMF_theta3 (hq : theta3.extinction < 1) (hs1 : theta3.skeletonWeight 1 < 1)
    (hJ : 2 ≤ 3) : reducedPMF theta3 hq hs1 hJ = PMF.pure 3 := by
  ext k
  rw [reducedPMF_apply, PMF.pure_apply]
  by_cases hk : k = 3
  · subst k
    rw [ite_eq_left (by omega), ite_eq_left rfl, reducedWeight_def,
      skeletonWeight_eq_of_chain theta3 theta3_zero,
      skeletonWeight_eq_of_chain theta3 theta3_zero]
    norm_num
  · rw [ite_eq_right hk]
    by_cases h2 : 2 ≤ k
    · rw [ite_eq_left h2, reducedWeight_def,
        skeletonWeight_eq_of_chain theta3 theta3_zero,
        skeletonWeight_eq_of_chain theta3 theta3_zero, theta3_apply,
        ite_eq_right (by omega)]
      simp
    · rw [ite_eq_right h2]

end ChainClasses.ChainWitnesses
