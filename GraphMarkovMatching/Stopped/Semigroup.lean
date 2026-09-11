/-
The branching semigroup of a set of arities and its atoms (`markov_matching_new_proof.tex`,
`sec:common-presentations`, "The common generators", and `sec:unbounded-supports`, "The
common generators remain finite"): pure additive combinatorics of `AddSubmonoid ℕ`.

* `shiftSemigroup S`: the nonnegative sums of the shifted arities `k - 1`, `k ∈ S`;
* `IsAtom Λ a`, `atoms Λ`: a positive element which is not the sum of two positive elements;
* `isAtom_mem_generators`: every atom of a generated submonoid is a generator, and
  `atoms_subset_inter`: the atoms of a common branching semigroup lie in both shifted
  supports (`thm:common-atoms`);
* `mem_closure_atoms`: the atoms generate, and `length_le_of_sum_atoms`: an expression as a
  sum of atoms has at most `⌊n / s₀⌋` summands (`thm:common-atoms`);
* `atoms_finite`, `atoms_ncard_le`: at most one atom in each residue class modulo a positive
  element, hence at most `s₀` atoms (`sec:unbounded-supports`);
* `exists_atoms_finset`: the finite atomic core of a finitely generated submonoid;
* `example_atoms`: the example of `sec:common-presentations` with the nonnested supports
  `{4, 6, 7}` and `{4, 6, 9}`.
-/
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace GraphMarkovMatching.Stopped

open scoped Classical

/-! ### The branching semigroup and its atoms (`sec:common-presentations`) -/

/-- The branching semigroup of a set of arities: the nonnegative sums of the shifted arities
`k - 1` (`sec:common-presentations`). -/
def shiftSemigroup (S : Set ℕ) : AddSubmonoid ℕ := AddSubmonoid.closure ((fun k => k - 1) '' S)

/-- An atom of an additive submonoid: a positive element that is not the sum of two positive
elements (`sec:common-presentations`, "The common generators"). -/
def IsAtom (Λ : AddSubmonoid ℕ) (a : ℕ) : Prop :=
  a ∈ Λ ∧ 0 < a ∧ ¬ ∃ b c, b ∈ Λ ∧ c ∈ Λ ∧ 0 < b ∧ 0 < c ∧ a = b + c

/-- The set of atoms (`sec:common-presentations`, "The common generators"). -/
def atoms (Λ : AddSubmonoid ℕ) : Set ℕ := {a | IsAtom Λ a}

/-- Membership in `atoms` unfolds to `IsAtom`. -/
lemma mem_atoms {Λ : AddSubmonoid ℕ} {a : ℕ} : a ∈ atoms Λ ↔ IsAtom Λ a := Iff.rfl

/-- An atom lies in the submonoid. -/
lemma IsAtom.mem {Λ : AddSubmonoid ℕ} {a : ℕ} (h : IsAtom Λ a) : a ∈ Λ := h.1

/-- An atom is positive. -/
lemma IsAtom.pos {Λ : AddSubmonoid ℕ} {a : ℕ} (h : IsAtom Λ a) : 0 < a := h.2.1

/-- An atom is not the sum of two positive elements of the submonoid. -/
lemma IsAtom.not_add {Λ : AddSubmonoid ℕ} {a b c : ℕ} (h : IsAtom Λ a) (hb : b ∈ Λ)
    (hc : c ∈ Λ) (hb0 : 0 < b) (hc0 : 0 < c) : a ≠ b + c :=
  fun habc => h.2.2 ⟨b, c, hb, hc, hb0, hc0, habc⟩

/-- An atom which is the sum of a list of elements of the submonoid is one of the summands
(`thm:common-atoms`: two or more positive summands would decompose the atom). -/
lemma IsAtom.mem_list_of_sum {Λ : AddSubmonoid ℕ} {a : ℕ} (ha : IsAtom Λ a) :
    ∀ l : List ℕ, (∀ y ∈ l, y ∈ Λ) → l.sum = a → a ∈ l := by
  intro l
  induction l with
  | nil =>
    intro _ hsum
    simp only [List.sum_nil] at hsum
    exact absurd hsum.symm ha.pos.ne'
  | cons y rest ih =>
    intro hl hsum
    have hy : y ∈ Λ := hl y (List.mem_cons_self ..)
    have hrest : ∀ z ∈ rest, z ∈ Λ := fun z hz => hl z (List.mem_cons_of_mem _ hz)
    simp only [List.sum_cons] at hsum
    rcases Nat.eq_zero_or_pos y with hy0 | hy0
    · subst hy0
      exact List.mem_cons_of_mem _ (ih hrest (by simpa using hsum))
    rcases Nat.eq_zero_or_pos rest.sum with hr0 | hr0
    · rw [hr0, add_zero] at hsum
      exact hsum ▸ List.mem_cons_self ..
    exact absurd hsum.symm (ha.not_add hy (list_sum_mem hrest) hy0 hr0)

/-- **Every atom of a generated semigroup is a generator** (`thm:common-atoms`). -/
theorem isAtom_mem_generators {G : Set ℕ} {a : ℕ} (h : IsAtom (AddSubmonoid.closure G) a) :
    a ∈ G := by
  obtain ⟨l, hl, hsum⟩ := AddSubmonoid.exists_list_of_mem_closure h.mem
  exact hl a (h.mem_list_of_sum l (fun y hy => AddSubmonoid.subset_closure (hl y hy)) hsum)

/-- The atoms of a generated submonoid form a subset of the generators (`thm:common-atoms`). -/
lemma atoms_closure_subset (G : Set ℕ) : atoms (AddSubmonoid.closure G) ⊆ G :=
  fun _ ha => isAtom_mem_generators ha

/-- An atom of a branching semigroup is a shifted arity (`thm:common-atoms`); since atoms are
positive, the arity is `a + 1`. -/
lemma isAtom_shiftSemigroup_imp {S : Set ℕ} {a : ℕ} (h : IsAtom (shiftSemigroup S) a) :
    a + 1 ∈ S := by
  obtain ⟨k, hk, hka⟩ := isAtom_mem_generators h
  have hka' : k - 1 = a := hka
  have hpos := h.pos
  have : k = a + 1 := by omega
  exact this ▸ hk

/-- `thm:common-atoms`: the atoms of the common semigroup lie in both shifted supports. -/
theorem atoms_subset_inter {SL SR : Set ℕ} (h : shiftSemigroup SL = shiftSemigroup SR) :
    ∀ a ∈ atoms (shiftSemigroup SL), a + 1 ∈ SL ∧ a + 1 ∈ SR :=
  fun _ ha => ⟨isAtom_shiftSemigroup_imp ha, isAtom_shiftSemigroup_imp (h ▸ ha)⟩

/-- The atoms generate (`thm:common-atoms`): every element is a sum of atoms, by strong
induction. -/
theorem mem_closure_atoms (Λ : AddSubmonoid ℕ) {n : ℕ} (hn : n ∈ Λ) :
    n ∈ AddSubmonoid.closure (atoms Λ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · exact hn0 ▸ zero_mem _
    by_cases hatom : IsAtom Λ n
    · exact AddSubmonoid.subset_closure hatom
    have hdec : ∃ b c, b ∈ Λ ∧ c ∈ Λ ∧ 0 < b ∧ 0 < c ∧ n = b + c := by
      by_contra hcon
      exact hatom ⟨hn, hn0, hcon⟩
    obtain ⟨b, c, hb, hc, hb0, hc0, rfl⟩ := hdec
    exact add_mem (ih b (by omega) hb) (ih c (by omega) hc)

/-- Every expression of `n` as a sum of atoms has at most `n / s₀` summands, `s₀ = min atoms`
(`thm:common-atoms`). -/
theorem length_le_of_sum_atoms (Λ : AddSubmonoid ℕ) (s₀ : ℕ) (hs₀ : ∀ a ∈ atoms Λ, s₀ ≤ a)
    (hs₀pos : 0 < s₀) (l : List ℕ) (hl : ∀ a ∈ l, a ∈ atoms Λ) : l.length ≤ l.sum / s₀ := by
  rw [Nat.le_div_iff_mul_le hs₀pos]
  have := List.card_nsmul_le_sum l s₀ (fun a ha => hs₀ a (hl a ha))
  simpa [smul_eq_mul] using this

/-! ### Finiteness of the atoms (`sec:unbounded-supports`) -/

/-- Two atoms in the same residue class modulo a positive element of the submonoid coincide:
the larger one would differ from the smaller by a positive multiple of that element
(`sec:unbounded-supports`, "The common generators remain finite"). -/
private lemma eq_of_mod_eq_of_isAtom {Λ : AddSubmonoid ℕ} {s₀ : ℕ} (hs₀ : s₀ ∈ Λ) {a b : ℕ}
    (ha : IsAtom Λ a) (hb : IsAtom Λ b) (hab : a % s₀ = b % s₀) : a = b := by
  -- the ordered claim: no atom lies strictly above another one of the same residue class
  have key : ∀ a b : ℕ, IsAtom Λ a → IsAtom Λ b → a % s₀ = b % s₀ → a < b → False := by
    intro a b ha hb hab hlt
    have hdvd : s₀ ∣ b - a := (Nat.modEq_iff_dvd' hlt.le).mp hab
    obtain ⟨m, hm⟩ := hdvd
    have hmem : b - a ∈ Λ := by
      have := nsmul_mem hs₀ m
      rwa [smul_eq_mul, mul_comm, ← hm] at this
    exact hb.not_add ha.mem hmem ha.pos (by omega) (by omega)
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact (key a b ha hb hab hlt).elim
  · exact heq
  · exact (key b a hb ha hab.symm hgt).elim

/-- The residue map modulo an element of the submonoid is injective on the atoms
(`sec:unbounded-supports`). -/
lemma injOn_mod_atoms {Λ : AddSubmonoid ℕ} {s₀ : ℕ} (hs₀ : s₀ ∈ Λ) :
    Set.InjOn (fun a => a % s₀) (atoms Λ) :=
  fun _ ha _ hb hab => eq_of_mod_eq_of_isAtom hs₀ ha hb hab

/-- The residue map modulo a positive `s₀` sends the atoms into `{0, …, s₀ - 1}`. -/
private lemma mapsTo_mod_atoms (Λ : AddSubmonoid ℕ) {s₀ : ℕ} (hpos : 0 < s₀) :
    Set.MapsTo (fun a => a % s₀) (atoms Λ) (↑(Finset.range s₀) : Set ℕ) :=
  fun _ _ => by simpa using Nat.mod_lt _ hpos

/-- **Finiteness** (`sec:unbounded-supports`): a submonoid of `ℕ` with a positive element has
at most one atom in each residue class modulo that element, hence finitely many atoms. -/
theorem atoms_finite (Λ : AddSubmonoid ℕ) (h : ∃ n ∈ Λ, 0 < n) : (atoms Λ).Finite := by
  obtain ⟨n, hn, hnpos⟩ := h
  exact Set.Finite.of_injOn (mapsTo_mod_atoms Λ hnpos) (injOn_mod_atoms hn)
    (Finset.finite_toSet _)

/-- At most one atom in each residue class modulo the least positive element `s₀`, hence at
most `s₀` atoms (`sec:unbounded-supports`). -/
theorem atoms_ncard_le (Λ : AddSubmonoid ℕ) {s₀ : ℕ} (hs₀ : s₀ ∈ Λ) (hpos : 0 < s₀)
    (hmin : ∀ n ∈ Λ, 0 < n → s₀ ≤ n) : (atoms Λ).ncard ≤ s₀ := by
  -- minimality of `s₀` is not needed: any positive element of `Λ` gives the bound
  have _ := hmin
  calc (atoms Λ).ncard ≤ (↑(Finset.range s₀) : Set ℕ).ncard :=
        Set.ncard_le_ncard_of_injOn (fun a => a % s₀) (mapsTo_mod_atoms Λ hpos)
          (injOn_mod_atoms hs₀) (Finset.finite_toSet _)
    _ = s₀ := by rw [Set.ncard_coe_finset, Finset.card_range]

/-- For finite generating sets the atoms are finite and generate: the constructive form used
by the presentations (`thm:common-atoms`). -/
theorem exists_atoms_finset (G : Finset ℕ) :
    ∃ A : Finset ℕ, (↑A : Set ℕ) = atoms (AddSubmonoid.closure (↑G : Set ℕ)) ∧
      AddSubmonoid.closure (↑A : Set ℕ) = AddSubmonoid.closure (↑G : Set ℕ) := by
  refine ⟨G.filter (IsAtom (AddSubmonoid.closure (↑G : Set ℕ))), ?_, ?_⟩
  · ext a
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_atoms]
    exact ⟨fun h => h.2, fun h => ⟨isAtom_mem_generators h, h⟩⟩
  · apply le_antisymm
    · exact AddSubmonoid.closure_mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    · refine AddSubmonoid.closure_le.mpr fun g hg => ?_
      have hmem := mem_closure_atoms (AddSubmonoid.closure (↑G : Set ℕ))
        (AddSubmonoid.subset_closure hg)
      refine AddSubmonoid.closure_mono ?_ hmem
      intro a ha
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨isAtom_mem_generators ha, ha⟩

/-! ### The example with nonnested supports (`sec:common-presentations`) -/

/-- Every element of a submonoid generated by elements `≥ s` is zero or `≥ s`. -/
lemma zero_or_le_of_mem_closure {G : Set ℕ} {s : ℕ} (hG : ∀ g ∈ G, s ≤ g) {n : ℕ}
    (hn : n ∈ AddSubmonoid.closure G) : n = 0 ∨ s ≤ n := by
  induction hn using AddSubmonoid.closure_induction with
  | mem x hx => exact Or.inr (hG x hx)
  | zero => exact Or.inl rfl
  | add x y _ _ hx hy => omega

/-- A generator which is positive and smaller than twice the least generator is an atom. -/
lemma isAtom_of_lt_two_mul {G : Set ℕ} {s g : ℕ} (hG : ∀ g ∈ G, s ≤ g) (hg : g ∈ G)
    (hpos : 0 < g) (hlt : g < 2 * s) : IsAtom (AddSubmonoid.closure G) g := by
  refine ⟨AddSubmonoid.subset_closure hg, hpos, ?_⟩
  rintro ⟨b, c, hb, hc, hb0, hc0, hg⟩
  rcases zero_or_le_of_mem_closure hG hb with hb' | hb' <;>
    rcases zero_or_le_of_mem_closure hG hc with hc' | hc' <;> omega

/-- The shifted support of `{4, 6, 7}` is `{3, 5, 6}` (`sec:common-presentations`). -/
private lemma image_shift_467 : (fun k => k - 1) '' ({4, 6, 7} : Set ℕ) = {3, 5, 6} := by
  simp [Set.image_insert_eq]

/-- The shifted support of `{4, 6, 9}` is `{3, 5, 8}` (`sec:common-presentations`). -/
private lemma image_shift_469 : (fun k => k - 1) '' ({4, 6, 9} : Set ℕ) = {3, 5, 8} := by
  simp [Set.image_insert_eq]

/-- Adjoining an element of the closure to the generators does not change the closure. -/
private lemma closure_insert_eq {G : Set ℕ} {x : ℕ} (hx : x ∈ AddSubmonoid.closure G) :
    AddSubmonoid.closure (insert x G) = AddSubmonoid.closure G :=
  le_antisymm (AddSubmonoid.closure_le.mpr (Set.insert_subset hx AddSubmonoid.subset_closure))
    (AddSubmonoid.closure_mono (Set.subset_insert _ _))

/-- `⟨3, 5, 6⟩ = ⟨3, 5⟩` since `6 = 3 + 3` (`sec:common-presentations`). -/
private lemma closure_356 :
    AddSubmonoid.closure ({3, 5, 6} : Set ℕ) = AddSubmonoid.closure ({3, 5} : Set ℕ) := by
  have h : ({3, 5, 6} : Set ℕ) = insert 6 {3, 5} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have h6 : (3 : ℕ) + 3 ∈ AddSubmonoid.closure ({3, 5} : Set ℕ) :=
    add_mem (AddSubmonoid.subset_closure (by simp)) (AddSubmonoid.subset_closure (by simp))
  rw [h]
  exact closure_insert_eq h6

/-- `⟨3, 5, 8⟩ = ⟨3, 5⟩` since `8 = 3 + 5` (`sec:common-presentations`). -/
private lemma closure_358 :
    AddSubmonoid.closure ({3, 5, 8} : Set ℕ) = AddSubmonoid.closure ({3, 5} : Set ℕ) := by
  have h : ({3, 5, 8} : Set ℕ) = insert 8 {3, 5} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have h8 : (3 : ℕ) + 5 ∈ AddSubmonoid.closure ({3, 5} : Set ℕ) :=
    add_mem (AddSubmonoid.subset_closure (by simp)) (AddSubmonoid.subset_closure (by simp))
  rw [h]
  exact closure_insert_eq h8

/-- The atoms of `⟨3, 5⟩` are `3` and `5` (`sec:common-presentations`). -/
private lemma atoms_closure_35 : atoms (AddSubmonoid.closure ({3, 5} : Set ℕ)) = {3, 5} := by
  have hG : ∀ g ∈ ({3, 5} : Set ℕ), 3 ≤ g := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    omega
  apply Set.Subset.antisymm (atoms_closure_subset _)
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rw [mem_atoms]
  rcases ha with rfl | rfl
  · exact isAtom_of_lt_two_mul hG (by simp) (by norm_num) (by norm_num)
  · exact isAtom_of_lt_two_mul hG (by simp) (by norm_num) (by norm_num)

/-- The example of `sec:common-presentations`: `{4, 6, 7}` and `{4, 6, 9}` have the shifted
semigroup `⟨3, 5⟩`, atoms `{3, 5}`, common core `{4, 6}`. -/
theorem example_atoms :
    atoms (shiftSemigroup {4, 6, 7}) = {3, 5} ∧
      shiftSemigroup {4, 6, 7} = shiftSemigroup {4, 6, 9} := by
  have h1 : shiftSemigroup {4, 6, 7} = AddSubmonoid.closure ({3, 5} : Set ℕ) := by
    rw [shiftSemigroup, image_shift_467, closure_356]
  have h2 : shiftSemigroup {4, 6, 9} = AddSubmonoid.closure ({3, 5} : Set ℕ) := by
    rw [shiftSemigroup, image_shift_469, closure_358]
  exact ⟨by rw [h1, atoms_closure_35], by rw [h1, h2]⟩

end GraphMarkovMatching.Stopped
