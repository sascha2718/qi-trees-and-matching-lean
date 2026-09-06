/-
The source ray of an infinite screen path
(`arbitrary_offspring_matching.tex`, `thm:source-ray` and the source
side of `thm:nilpotence`):
along a `screenSucc`-path the zero list iterates `zsucc` and the source
cell follows an admissible descent, and from a fresh cell the path
returns to a fresh cell after exactly a return length of the support.

* `screenSucc_zlist` / `screenSucc_cell`: the components of a successor
  screen;
* `hits_F_of_gpair` (`thm:source-ray` (a)): a cell path that has
  entered the forced cascade of a counter `k` reaches the fresh cell
  after a length in `toFresh k`;
* `cellPath_F_return` (`thm:source-ray` (b)): from a fresh cell the
  path returns to a fresh cell after a length in `𝒟_ν`.
-/
import GraphMarkovMatching.Grammar.Descend

namespace GraphMarkovMatching

/-- The zero list of a successor screen is the successor zero list. -/
lemma screenSucc_zlist {S : Finset ℕ} {sc sc' : GScreen}
    (h : sc' ∈ screenSucc S sc) : sc'.zlist = zsucc S sc.zlist := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h
  rfl

/-- The cell of a successor screen is a successor of the cell. -/
lemma screenSucc_cell {S : Finset ℕ} {sc sc' : GScreen}
    (h : sc' ∈ screenSucc S sc) : sc'.cell ∈ tgtSucc S sc.cell := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
  exact (Finset.mem_product.mp hp).1

/-- A cell path that has entered the forced cascade of a counter `k`
reaches the fresh cell after a length in `toFresh k`
(`thm:source-ray` (a)). -/
lemma hits_F_of_gpair {S : Finset ℕ} {c : ℕ → Tgt}
    (hc : ∀ n, c (n + 1) ∈ tgtSucc S (c n)) :
    ∀ k n, c (n + 1) ∈ gpair k → ∃ m ∈ toFresh k, c (n + m) = Tgt.F := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hmem
    cases hval : c (n + 1) with
    | F =>
        rw [hval] at hmem
        have hk3 : k ≤ 3 := by
          by_contra hgt
          rw [gpair, if_pos (by omega)] at hmem
          simp at hmem
        refine ⟨1, ?_, hval⟩
        by_cases h2 : k ≤ 2
        · rw [toFresh_le_two h2]
          exact Finset.mem_singleton_self _
        · rw [show k = 3 from by omega, toFresh_three]
          simp
    | Z i =>
        rw [hval] at hmem
        rw [gpair] at hmem
        split_ifs at hmem with h4 h3
        · simp only [Finset.mem_insert, Finset.mem_singleton,
            Tgt.Z.injEq] at hmem
          have hnext : c (n + 1 + 1) ∈ gpair i := by
            have h := hc (n + 1)
            rw [hval] at h
            exact h
          rcases hmem with rfl | rfl
          · obtain ⟨m', hm', hF⟩ := ih (k / 2) (by omega) (n + 1) hnext
            refine ⟨m' + 1, ?_, ?_⟩
            · rw [toFresh_of_ge h4]
              exact Finset.mem_union_left _
                (Finset.mem_image_of_mem _ hm')
            · rw [show n + (m' + 1) = n + 1 + m' from by omega]
              exact hF
          · obtain ⟨m', hm', hF⟩ := ih (k - k / 2) (by omega) (n + 1)
              hnext
            refine ⟨m' + 1, ?_, ?_⟩
            · rw [toFresh_of_ge h4]
              exact Finset.mem_union_right _
                (Finset.mem_image_of_mem _ hm')
            · rw [show n + (m' + 1) = n + 1 + m' from by omega]
              exact hF
        · subst h3
          simp only [Finset.mem_insert, Finset.mem_singleton,
            Tgt.Z.injEq] at hmem
          rcases hmem with rfl | hmem
          · have hnext : c (n + 1 + 1) ∈ gpair 2 := by
              have h := hc (n + 1)
              rw [hval] at h
              exact h
            obtain ⟨m', hm', hF⟩ := ih 2 (by omega) (n + 1) hnext
            rw [toFresh_le_two (by omega)] at hm'
            rw [Finset.mem_singleton.mp hm'] at hF
            refine ⟨2, ?_, ?_⟩
            · rw [toFresh_three]
              simp
            · rw [show n + 2 = n + 1 + 1 from by omega]
              exact hF
          · exact absurd hmem (by simp)
        · rw [Finset.mem_singleton] at hmem
          exact absurd hmem (by simp)
    | Fk i =>
        rw [hval] at hmem
        rw [gpair] at hmem
        split_ifs at hmem <;> simp at hmem

/-- **The fresh return of the source ray** (`thm:source-ray` (b)):
from a fresh cell the path returns to a fresh cell after a return
length of the support. -/
lemma cellPath_F_return {S : Finset ℕ} {c : ℕ → Tgt}
    (hc : ∀ n, c (n + 1) ∈ tgtSucc S (c n)) {n : ℕ}
    (hF : c n = Tgt.F) :
    ∃ m ∈ depthSet S, c (n + m) = Tgt.F := by
  have h := hc n
  rw [hF] at h
  obtain ⟨k, hk, hmem⟩ := Finset.mem_biUnion.mp h
  obtain ⟨m, hm, hF'⟩ := hits_F_of_gpair hc k n hmem
  exact ⟨m, Finset.mem_biUnion.mpr ⟨k, hk, hm⟩, hF'⟩

/-- Return lengths are positive. -/
lemma one_le_of_mem_depthSet {S : Finset ℕ} {d : ℕ}
    (hd : d ∈ depthSet S) : 1 ≤ d := by
  obtain ⟨k, _, hdk⟩ := Finset.mem_biUnion.mp hd
  exact one_le_of_mem_toFresh k d hdk

end GraphMarkovMatching
