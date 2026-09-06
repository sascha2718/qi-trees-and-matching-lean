/-
Admissible descents in the screen grammar
(`arbitrary_offspring_matching.tex`: `def:descend`, `thm:coverage`,
and the realisation half of `thm:descend-realise`): descents of zero-list
members persist in the iterated zero list, return lengths are realized
as descents to the fresh state, and every semigroup element is an
admissible fresh-to-fresh descent length.

* `Descend S m t t'` (`def:descend`): an admissible `m`-step descent
  in the target alphabet (any successor at each step);
* `Descend.trans`: descents concatenate;
* `mem_zsucc_iter_of_descend` (`thm:coverage`): if a zero list
  contains `t`, then `m` successor steps later it contains every
  admissible `m`-descendant of `t`;
* `descend_of_mem_toFresh`, `descend_F` (`thm:descend-realise`,
  realisation): every return length
  `d ∈ toFresh k` is realized as a `d`-step descent from `Z k`, `Fk k`
  or (for `k ∈ S`) from `F`, to the fresh state;
* `descend_closure`: every element of the semigroup `Σ_ν` is an
  admissible fresh-to-fresh descent length.
-/
import GraphMarkovMatching.Grammar.Alphabet
import GraphMarkovMatching.Grammar.Depths

namespace GraphMarkovMatching

/-- An admissible `m`-step descent in the target alphabet. -/
inductive Descend (S : Finset ℕ) : ℕ → Tgt → Tgt → Prop
  | refl (t : Tgt) : Descend S 0 t t
  | step {m : ℕ} {t t' t'' : Tgt} (h : t' ∈ tgtSucc S t)
      (h' : Descend S m t' t'') : Descend S (m + 1) t t''

/-- Descents concatenate. -/
lemma Descend.trans {S : Finset ℕ} {m m' : ℕ} {t t' t'' : Tgt}
    (h1 : Descend S m t t') :
    Descend S m' t' t'' → Descend S (m + m') t t'' := by
  induction h1 with
  | refl _ =>
      intro h2
      rw [Nat.zero_add]
      exact h2
  | step h _ ih =>
      intro h2
      rw [Nat.add_right_comm]
      exact Descend.step h (ih h2)

/-- **List coverage** (`thm:coverage`): if a zero list contains `t`,
then `m` successor steps later it contains every admissible
`m`-descendant of `t`. -/
lemma mem_zsucc_iter_of_descend {S : Finset ℕ} {m : ℕ} {t t' : Tgt}
    {z : Finset Tgt} (ht : t ∈ z) (hd : Descend S m t t') :
    t' ∈ (zsucc S)^[m] z := by
  induction hd generalizing z with
  | refl _ =>
      rw [Function.iterate_zero_apply]
      exact ht
  | step h _ ih =>
      rw [Function.iterate_succ_apply]
      exact ih (Finset.mem_biUnion.mpr ⟨_, ht, h⟩)

/-- Return lengths are realized as descents to the fresh state, from
any target whose successors contain the cascade pair. -/
lemma descend_of_mem_toFresh {S : Finset ℕ} :
    ∀ k, ∀ d ∈ toFresh k, ∀ t : Tgt,
      gpair k ⊆ tgtSucc S t → Descend S d t Tgt.F := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d hd t hsub
    by_cases h2 : k ≤ 2
    · rw [toFresh_le_two h2] at hd
      rw [Finset.mem_singleton.mp hd]
      refine Descend.step (hsub ?_) (Descend.refl _)
      rw [gpair, if_neg (by omega), if_neg (by omega)]
      exact Finset.mem_singleton_self _
    · by_cases h3 : k = 3
      · subst h3
        have hg3 : gpair 3 = {Tgt.Z 2, Tgt.F} := by
          rw [gpair, if_neg (by omega), if_pos rfl]
        rw [toFresh_three] at hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · refine Descend.step (hsub ?_) (Descend.refl _)
          rw [hg3]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        · have h1mem : (1 : ℕ) ∈ toFresh 2 := by
            rw [toFresh_le_two (by omega)]
            exact Finset.mem_singleton_self _
          refine Descend.step (hsub ?_)
            (ih 2 (by omega) 1 h1mem (Tgt.Z 2) (fun x hx => hx))
          rw [hg3]
          exact Finset.mem_insert_self _ _
      · have h4 : 4 ≤ k := by omega
        have hgk : gpair k = {Tgt.Z (k / 2), Tgt.Z (k - k / 2)} := by
          rw [gpair, if_pos h4]
        rw [toFresh_of_ge h4] at hd
        rcases Finset.mem_union.mp hd with h | h
        · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
          refine Descend.step (hsub ?_)
            (ih (k / 2) (by omega) e he (Tgt.Z (k / 2))
              (fun x hx => hx))
          rw [hgk]
          exact Finset.mem_insert_self _ _
        · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
          refine Descend.step (hsub ?_)
            (ih (k - k / 2) (by omega) e he (Tgt.Z (k - k / 2))
              (fun x hx => hx))
          rw [hgk]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- Return lengths of support counters are fresh-to-fresh descent
lengths. -/
lemma descend_F {S : Finset ℕ} {k d : ℕ} (hk : k ∈ S)
    (hd : d ∈ toFresh k) : Descend S d Tgt.F Tgt.F :=
  descend_of_mem_toFresh k d hd Tgt.F
    (fun _ hx => Finset.mem_biUnion.mpr ⟨k, hk, hx⟩)

/-- Every element of the semigroup `Σ_ν` is an admissible
fresh-to-fresh descent length. -/
lemma descend_closure {S : Finset ℕ} {m : ℕ}
    (hm : m ∈ AddSubmonoid.closure ((depthSet S : Set ℕ))) :
    Descend S m Tgt.F Tgt.F := by
  induction hm using AddSubmonoid.closure_induction with
  | mem d hd =>
      obtain ⟨k, hk, hdk⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hd)
      exact descend_F hk hdk
  | zero => exact Descend.refl _
  | add a b _ _ iha ihb => exact Descend.trans iha ihb

end GraphMarkovMatching
