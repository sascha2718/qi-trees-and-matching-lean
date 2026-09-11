/-
The elementary counter laws used in the preassigned-profile obstruction.
-/
import GraphMarkovMatching.Models.Counter
import Mathlib.Probability.Distributions.Uniform

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

noncomputable def nuFour : PMF ℕ := PMF.pure 4

noncomputable def nuFourSeven : PMF ℕ :=
  (PMF.uniformOfFintype Bool).map (fun b => if b then 7 else 4)

lemma nuFour_support : nuFour.support = ({4} : Set ℕ) := by
  simp [nuFour]

lemma nuFourSeven_support : nuFourSeven.support = ({4, 7} : Set ℕ) := by
  rw [nuFourSeven, PMF.support_map]
  have hu : (PMF.uniformOfFintype Bool).support = Set.univ := by
    simp
  rw [hu]
  ext n
  simp only [Set.mem_image, Set.mem_univ, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, _, rfl⟩
    cases b <;> simp
  · intro h
    rcases h with rfl | rfl
    · exact ⟨false, by simp⟩
    · exact ⟨true, by simp⟩

end GraphMarkovMatching
