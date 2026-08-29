/-
The descent core of the general-ν screen rows
(`arbitrary_offspring_matching.tex`, `thm:descent` in
`sec:rows`): the zero list of a formal screen, descended through a branch
point at a compatible root, is exactly the square-dead event of its
member pairs, and the member pairs cover exactly the interpreted
successor list of the grammar.

* `memPairsOf` / `memPairs`: the member pairs of a zero list: each
  forced member contributes its cascade pair, the fresh member one pair
  per supported counter;
* `memPairs_mem` / `memPairs_cov`: the member components are exactly
  the interpreted successor list `zsucc`, the hypotheses of the Hall
  factorization;
* `memInd_branch_iff`: the one-step descent of the zero event at a
  compatible root (`eq:decomp-forced`, `eq:decomp-fresh`, and the zero
  direction of `thm:fresh-mixture` in one statement);
* `mem_screenSucc_mk` and the list calculus helpers used to collect
  the linear successor charges.
-/
import GraphMarkovMatching.Rows.Psi
import GraphMarkovMatching.Process.Factorize
import GraphMarkovMatching.Process.ScreenTilt

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (μ : PMF V) (ν : PMF ℕ) (v0 : V)

/-- The member pairs contributed by one zero-list member: forced
members their cascade pair, the fresh member one pair per supported
counter. -/
noncomputable def memPairsOf (S : Finset ℕ) (h : ℕ) :
    Tgt → List (PMF (FullLab (V × ℕ) h) × PMF (FullLab (V × ℕ) h))
  | Tgt.Z j => [(interpT μ ν v0 h (gcomp0 j), interpT μ ν v0 h (gcomp1 j))]
  | Tgt.F => S.toList.map fun k =>
      (interpT μ ν v0 h (gcomp0 k), interpT μ ν v0 h (gcomp1 k))
  | Tgt.Fk k => [(interpT μ ν v0 h (gcomp0 k), interpT μ ν v0 h (gcomp1 k))]

/-- The member pairs of a zero list. -/
noncomputable def memPairs (S : Finset ℕ) (h : ℕ) (z : Finset Tgt) :
    List (PMF (FullLab (V × ℕ) h) × PMF (FullLab (V × ℕ) h)) :=
  z.toList.flatMap (memPairsOf μ ν v0 S h)

/-- Every member-pair component lies in the interpreted successor
list. -/
lemma memPairs_mem (S : Finset ℕ) (h : ℕ) (z : Finset Tgt) :
    ∀ p ∈ memPairs μ ν v0 S h z,
      p.1 ∈ ((zsucc S z).toList).map (interpT μ ν v0 h)
        ∧ p.2 ∈ ((zsucc S z).toList).map (interpT μ ν v0 h) := by
  intro p hp
  obtain ⟨t, htz, hpt⟩ := List.mem_flatMap.mp hp
  have htz' : t ∈ z := Finset.mem_toList.mp htz
  have hmem : ∀ t' ∈ tgtSucc S t,
      interpT μ ν v0 h t' ∈ ((zsucc S z).toList).map (interpT μ ν v0 h) :=
    fun t' ht' => List.mem_map.mpr ⟨t', Finset.mem_toList.mpr
      (Finset.mem_biUnion.mpr ⟨t, htz', ht'⟩), rfl⟩
  match t with
  | Tgt.Z j =>
      rw [memPairsOf, List.mem_singleton] at hpt
      subst hpt
      exact ⟨hmem _ (gcomp_mem_gpair j).1, hmem _ (gcomp_mem_gpair j).2⟩
  | Tgt.F =>
      rw [memPairsOf] at hpt
      obtain ⟨k, hk, hpk⟩ := List.mem_map.mp hpt
      subst hpk
      have hkS : k ∈ S := Finset.mem_toList.mp hk
      refine ⟨hmem _ ?_, hmem _ ?_⟩
      · exact Finset.mem_biUnion.mpr ⟨k, hkS, (gcomp_mem_gpair k).1⟩
      · exact Finset.mem_biUnion.mpr ⟨k, hkS, (gcomp_mem_gpair k).2⟩
  | Tgt.Fk k =>
      rw [memPairsOf, List.mem_singleton] at hpt
      subst hpt
      exact ⟨hmem _ (gcomp_mem_gpair k).1, hmem _ (gcomp_mem_gpair k).2⟩

/-- Every element of the interpreted successor list is a member-pair
component. -/
lemma memPairs_cov (S : Finset ℕ) (h : ℕ) (z : Finset Tgt) :
    ∀ ρ ∈ ((zsucc S z).toList).map (interpT μ ν v0 h),
      ∃ p ∈ memPairs μ ν v0 S h z, ρ = p.1 ∨ ρ = p.2 := by
  intro ρ hρ
  obtain ⟨t', ht', hρt⟩ := List.mem_map.mp hρ
  obtain ⟨t, htz, htt'⟩ := Finset.mem_biUnion.mp (Finset.mem_toList.mp ht')
  have hflat : ∀ p ∈ memPairsOf μ ν v0 S h t,
      p ∈ memPairs μ ν v0 S h z :=
    fun p hp => List.mem_flatMap.mpr ⟨t, Finset.mem_toList.mpr htz, hp⟩
  match t with
  | Tgt.Z j =>
      rw [show tgtSucc S (Tgt.Z j) = gpair j from rfl, gpair_eq_pair] at htt'
      refine ⟨(interpT μ ν v0 h (gcomp0 j), interpT μ ν v0 h (gcomp1 j)),
        hflat _ (List.mem_singleton_self _), ?_⟩
      rcases Finset.mem_insert.mp htt' with rfl | h2
      · exact Or.inl hρt.symm
      · rw [Finset.mem_singleton.mp h2] at hρt
        exact Or.inr hρt.symm
  | Tgt.F =>
      obtain ⟨k, hkS, hk⟩ := Finset.mem_biUnion.mp htt'
      rw [gpair_eq_pair] at hk
      refine ⟨(interpT μ ν v0 h (gcomp0 k), interpT μ ν v0 h (gcomp1 k)),
        hflat _ (List.mem_map.mpr ⟨k, Finset.mem_toList.mpr hkS, rfl⟩), ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | h2
      · exact Or.inl hρt.symm
      · rw [Finset.mem_singleton.mp h2] at hρt
        exact Or.inr hρt.symm
  | Tgt.Fk k =>
      rw [show tgtSucc S (Tgt.Fk k) = gpair k from rfl, gpair_eq_pair] at htt'
      refine ⟨(interpT μ ν v0 h (gcomp0 k), interpT μ ν v0 h (gcomp1 k)),
        hflat _ (List.mem_singleton_self _), ?_⟩
      rcases Finset.mem_insert.mp htt' with rfl | h2
      · exact Or.inl hρt.symm
      · rw [Finset.mem_singleton.mp h2] at hρt
        exact Or.inr hρt.symm

variable (Rv : V → V → Prop)

/-- **The one-step descent of the zero event** (`sec:rows`,
`thm:descent`) at a compatible root: the interpreted zero list of a
formal screen is dead at the branch
point exactly when every member pair is square-dead at the child
pair. -/
lemma memInd_branch_iff (S : Finset ℕ)
    (hSsupp : ∀ j : ℕ, (ν j : ℝ≥0∞) ≠ 0 ↔ j ∈ S)
    {v : V} (hv0 : Rv v v0) (hvpos : rE μ Rv v ≠ 0) (k h : ℕ)
    (z : Finset Tgt) (hzf : ∀ t ∈ z, ∀ m, t ≠ Tgt.Fk m)
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    (∀ ρ ∈ (z.toList).map (interpT μ ν v0 (h + 1)),
        rE ρ (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp) = 0)
      ↔ ∀ p ∈ memPairs μ ν v0 S h z,
          rE (prodPMF p.1 p.2) (SquareRel (fullSim (labRel Rv) h)) xp = 0 := by
  have hmem : ∀ t ∈ z,
      ((rE (interpT μ ν v0 (h + 1) t) (fullSim (labRel Rv) (h + 1))
          (branch (v, k) xp) = 0)
        ↔ ∀ p ∈ memPairsOf μ ν v0 S h t,
            rE (prodPMF p.1 p.2) (SquareRel (fullSim (labRel Rv) h)) xp = 0) := by
    intro t htz
    match t with
    | Tgt.Z j =>
        have h1 := rE_Zlaw_succ_branch μ ν v0 Rv v k j h xp
        rw [if_pos hv0] at h1
        constructor
        · intro hdead p hp
          rw [List.mem_singleton.mp hp]
          rw [show rE (interpT μ ν v0 (h + 1) (Tgt.Z j))
              (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
              = rE (Xi μ ν v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp from h1] at hdead
          rw [← Xi_eq_prod μ ν v0 j h]
          exact hdead
        · intro hall
          have h2 := hall _ (List.mem_singleton_self _)
          rw [← Xi_eq_prod μ ν v0 j h] at h2
          rw [show rE (interpT μ ν v0 (h + 1) (Tgt.Z j))
              (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
              = rE (Xi μ ν v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp from h1]
          exact h2
    | Tgt.F =>
        have h1 := rE_Tlaw_succ_branch μ ν v0 Rv v k h xp
        have hbar : rE (interpT μ ν v0 (h + 1) Tgt.F)
            (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp) = 0
            ↔ rE (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 := by
          rw [show rE (interpT μ ν v0 (h + 1) Tgt.F)
              (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
              = rE μ Rv v * rE (XiBar μ ν v0 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp from h1]
          constructor
          · intro h0
            rcases mul_eq_zero.mp h0 with h0 | h0
            · exact absurd h0 hvpos
            · exact h0
          · intro h0
            rw [h0, mul_zero]
        rw [hbar,
          show rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp = 0
            ↔ ∀ a, (ν a : ℝ≥0∞) = 0 ∨ rE (Xi μ ν v0 a h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 from
            rE_bind_eq_zero_iff ν (fun a => Xi μ ν v0 a h) _ xp]
        constructor
        · intro hall p hp
          rw [memPairsOf] at hp
          obtain ⟨a, haS, hpa⟩ := List.mem_map.mp hp
          subst hpa
          rw [← Xi_eq_prod μ ν v0 a h]
          exact (hall a).resolve_left
            ((hSsupp a).mpr (Finset.mem_toList.mp haS))
        · intro hall a
          by_cases ha : (ν a : ℝ≥0∞) = 0
          · exact Or.inl ha
          · refine Or.inr ?_
            have haS : a ∈ S := (hSsupp a).mp ha
            have h2 := hall _ (List.mem_map.mpr
              ⟨a, Finset.mem_toList.mpr haS, rfl⟩)
            rw [← Xi_eq_prod μ ν v0 a h] at h2
            exact h2
    | Tgt.Fk m => exact absurd rfl (hzf _ htz m)
  constructor
  · intro hall p hp
    obtain ⟨t, htz, hpt⟩ := List.mem_flatMap.mp hp
    exact (hmem t (Finset.mem_toList.mp htz)).mp
      (hall _ (List.mem_map.mpr ⟨t, htz, rfl⟩)) p hpt
  · intro hall ρ hρ
    obtain ⟨t, htz, hρt⟩ := List.mem_map.mp hρ
    subst hρt
    exact (hmem t (Finset.mem_toList.mp htz)).mpr
      (fun p hp => hall p (List.mem_flatMap.mpr ⟨t, htz, hp⟩))

/-! ### Successor bookkeeping -/

/-- Explicit successor screens are grammar successors. -/
lemma mem_screenSucc_mk {S : Finset ℕ} {c t' : Tgt} {z : Finset Tgt}
    {u u' : Option Tgt} (ht : t' ∈ tgtSucc S c) (hu : u' ∈ normSucc S u) :
    (⟨t', zsucc S z, u'⟩ : GScreen) ∈ screenSucc S ⟨c, z, u⟩ :=
  Finset.mem_image.mpr ⟨(t', u'), Finset.mem_product.mpr ⟨ht, hu⟩, rfl⟩

lemma none_mem_normSucc (S : Finset ℕ) : none ∈ normSucc S none :=
  Finset.mem_singleton_self _

lemma some_mem_normSucc {S : Finset ℕ} {w t : Tgt} (h : t ∈ tgtSucc S w) :
    some t ∈ normSucc S (some w) :=
  Finset.mem_image_of_mem some h

/-- A single successor charge is below the full successor sum. -/
lemma interp_le_succ_sum (α : ℝ) (h : ℕ) {S : Finset ℕ} {sc sc' : GScreen}
    (hmem : sc' ∈ screenSucc S sc) :
    interpScreen α Rv μ ν v0 h sc'
      ≤ ∑ sc'' ∈ screenSucc S sc, interpScreen α Rv μ ν v0 h sc'' :=
  Finset.single_le_sum (fun _ _ => zero_le) hmem

/-- Finite list sums against a uniform bound. -/
lemma list_map_sum_le {A : Type} (l : List A) (f : A → ℝ≥0∞) (b : ℝ≥0∞)
    (hf : ∀ a ∈ l, f a ≤ b) :
    (l.map f).sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons]
      calc f a + (l.map f).sum
          ≤ b + l.length * b :=
            add_le_add (hf a (List.mem_cons_self ..))
              (ih fun a' ha' => hf a' (List.mem_cons_of_mem _ ha'))
        _ = (l.length + 1) * b := by ring
        _ = ((l.length + 1 : ℕ) : ℝ≥0∞) * b := by
            rw [Nat.cast_add, Nat.cast_one]

/-- The interpreted successor list has the successor cardinality. -/
lemma zsucc_map_length (S : Finset ℕ) (h : ℕ) (z : Finset Tgt) :
    (((zsucc S z).toList).map (interpT μ ν v0 h)).length
      = (zsucc S z).card := by
  rw [List.length_map, Finset.length_toList]

end GraphMarkovMatching
