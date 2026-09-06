import Mathlib.Tactic
import ChainClasses.General.GeneralShape

/-!
`sec:general-merge` of `matching_classes_general.tex`: the combinatorics of
`thm:merge` and the arithmetic of `def:branching-semigroup`.

The metric clause of `thm:merge` (the contraction moves every vertex by at
most the size of one shape) waits on the metric realisation; certified here
are the two counting clauses and the semigroup argument behind the sentence
that supports of laws with the same branching semigroup agree after enough
merging.

* `merge_arity`, `merge_size`: contracting the edge from a root of arity `k₁`
  to a child of arity `k₂` produces a root of arity `k₁ + k₂ - 1` and removes
  exactly one vertex.
* `merge_step`: on the shifted generators `k - 1` the merge is addition, so
  the reachable shifts form the branching semigroup
  (`def:branching-semigroup`); we take the additive submonoid closure, which
  adds only the empty merge `0`.
* `mem_of_coprime`: a numerical semigroup containing coprime `a ≥ 1` and `b`
  contains every `n ≥ (a-1)b`.
* `exists_consecutive_of_gcd_one`: Bézout over a finite generating set with
  gcd `1` produces a consecutive pair `v, v+1` in the closure.
* `semigroup_cofinite`: a numerical semigroup whose finite generating set has
  gcd `1` contains every sufficiently large natural number, with the explicit
  threshold `v²`; a general gcd reduces to this by scaling.
-/

namespace ChainClasses

/-! ### `thm:merge`, the counting clauses -/

namespace RTree

/-- The contraction of the edge between the root and a distinguished child:
the child's children are spliced into the root's list. -/
def mergeChild (l₁ ds l₂ : List RTree) : RTree := .node (l₁ ++ ds ++ l₂)

/-- **`thm:merge`, the arity**: a root of arity `k₁ = |l₁| + 1 + |l₂|` merged
with a child of arity `k₂ = |ds|` has arity `k₁ + k₂ - 1`. -/
lemma merge_arity (l₁ ds l₂ : List RTree) :
    (l₁ ++ ds ++ l₂).length + 1 = (l₁ ++ RTree.node ds :: l₂).length + ds.length := by
  simp only [List.length_append, List.length_cons]
  omega

/-- **`thm:merge`, the size**: the contraction removes exactly one vertex. -/
lemma merge_size (l₁ ds l₂ : List RTree) :
    (mergeChild l₁ ds l₂).size + 1 = (RTree.node (l₁ ++ RTree.node ds :: l₂)).size := by
  simp only [mergeChild, size, sizeF_append, sizeF]
  omega

end RTree

/-! ### `def:branching-semigroup` -/

/-- **`thm:merge` on the shifted generators**: merging splits of arities `k₁`
and `k₂` produces the shift `(k₁ + k₂ - 1) - 1 = (k₁ - 1) + (k₂ - 1)`, so the
reachable shifts form the additive semigroup of `def:branching-semigroup`. -/
lemma merge_step {Λ : AddSubmonoid ℕ} {k₁ k₂ : ℕ} (h₁ : 1 ≤ k₁) (h₂ : 1 ≤ k₂)
    (m₁ : k₁ - 1 ∈ Λ) (m₂ : k₂ - 1 ∈ Λ) : k₁ + k₂ - 1 - 1 ∈ Λ := by
  have h : k₁ + k₂ - 1 - 1 = (k₁ - 1) + (k₂ - 1) := by omega
  rw [h]
  exact add_mem m₁ m₂

/-- A semigroup containing the shift `1` is everything. -/
lemma closure_eq_top_of_one_mem {G : Set ℕ} (h : 1 ∈ G) :
    AddSubmonoid.closure G = ⊤ := by
  rw [AddSubmonoid.eq_top_iff']
  intro n
  have h1 : (1 : ℕ) ∈ AddSubmonoid.closure G := AddSubmonoid.subset_closure h
  simpa using AddSubmonoid.nsmul_mem (AddSubmonoid.closure G) h1 n

/-- **The branching semigroup of a hairy law is everything.** In the hairy
regime the reduced law charges arity `2` (`reducedLaw_pos`), whose shift is
`1`, so `Λ = ℕ₀` and the semigroup separates nothing.  In the chain regime
arity `2` may be absent, which is what leaves room for the obstruction. -/
theorem branching_semigroup_eq_top {S : Set ℕ} (h2 : 2 ∈ S) :
    AddSubmonoid.closure ((fun k => k - 1) '' S) = ⊤ :=
  closure_eq_top_of_one_mem ⟨2, h2, rfl⟩

/-- A numerical semigroup containing coprime elements `a ≥ 1` and `b`
contains every `n ≥ (a-1)b`: the multiples `jb`, `j < a`, cover all residues
modulo `a`, and from `(a-1)b` upwards the missing part is a multiple of
`a`. -/
theorem mem_of_coprime {Λ : AddSubmonoid ℕ} {a b : ℕ} (ha : a ∈ Λ) (hb : b ∈ Λ)
    (hco : Nat.Coprime a b) (ha1 : 1 ≤ a) {n : ℕ} (hn : (a - 1) * b ≤ n) : n ∈ Λ := by
  haveI : NeZero a := ⟨by omega⟩
  set w : (ZMod a)ˣ := ZMod.unitOfCoprime b hco.symm with hw
  set j : ℕ := ((n : ZMod a) * ↑w⁻¹).val with hj
  have hjlt : j < a := ZMod.val_lt _
  have hjb : (j : ZMod a) * (b : ZMod a) = (n : ZMod a) := by
    rw [hj, ZMod.natCast_val, ZMod.cast_id]
    have hwb : ((w : (ZMod a)ˣ) : ZMod a) = (b : ZMod a) := by
      rw [hw]; rfl
    rw [← hwb, mul_assoc]
    simp
  have hmod : j * b ≡ n [MOD a] := by
    have : ((j * b : ℕ) : ZMod a) = (n : ZMod a) := by push_cast; exact hjb
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  have hjble : j * b ≤ n := by
    calc j * b ≤ (a - 1) * b := Nat.mul_le_mul_right b (by omega)
      _ ≤ n := hn
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hjble).mp hmod
  have hrep : n = j * b + a * c := by omega
  rw [hrep]
  refine add_mem ?_ ?_
  · have := AddSubmonoid.nsmul_mem Λ hb j
    simpa [smul_eq_mul] using this
  · have := AddSubmonoid.nsmul_mem Λ ha c
    simpa [smul_eq_mul, Nat.mul_comm] using this

/-- **Bézout over a finite generating set**: the closure contains `u` and `v`
with `u - v` the gcd of the generators. -/
theorem exists_diff_gcd (G : Finset ℕ) :
    ∃ u ∈ AddSubmonoid.closure (G : Set ℕ), ∃ v ∈ AddSubmonoid.closure (G : Set ℕ),
      (u : ℤ) - v = G.gcd id := by
  classical
  induction G using Finset.induction_on with
  | empty => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | insert a s hnotmem ih =>
      obtain ⟨u, hu, v, hv, huv⟩ := ih
      have hmono : AddSubmonoid.closure (s : Set ℕ)
          ≤ AddSubmonoid.closure ((insert a s : Finset ℕ) : Set ℕ) := by
        apply AddSubmonoid.closure_mono
        rw [Finset.coe_insert]
        exact Set.subset_insert a s
      have hu' := hmono hu
      have hv' := hmono hv
      have hamem : a ∈ AddSubmonoid.closure ((insert a s : Finset ℕ) : Set ℕ) :=
        AddSubmonoid.subset_closure (by simp)
      set g : ℕ := s.gcd id with hg
      -- Bézout for the pair (a, g)
      have hbez := Nat.gcd_eq_gcd_ab a g
      set x : ℤ := Nat.gcdA a g with hx
      set y : ℤ := Nat.gcdB a g with hy
      -- the two nonnegative combinations
      set P : ℕ := a * x.toNat + u * y.toNat + v * (-y).toNat with hP
      set M : ℕ := a * (-x).toNat + u * (-y).toNat + v * y.toNat with hM
      have hmem : ∀ (p q r : ℕ), a * p + u * q + v * r
          ∈ AddSubmonoid.closure ((insert a s : Finset ℕ) : Set ℕ) := by
        intro p q r
        refine add_mem (add_mem ?_ ?_) ?_
        · simpa [smul_eq_mul, Nat.mul_comm] using
            AddSubmonoid.nsmul_mem _ hamem p
        · simpa [smul_eq_mul, Nat.mul_comm] using
            AddSubmonoid.nsmul_mem _ hu' q
        · simpa [smul_eq_mul, Nat.mul_comm] using
            AddSubmonoid.nsmul_mem _ hv' r
      refine ⟨P, by rw [hP]; exact hmem _ _ _, M, by rw [hM]; exact hmem _ _ _, ?_⟩
      have htx : (x.toNat : ℤ) - (-x).toNat = x := Int.toNat_sub_toNat_neg x
      have hty : (y.toNat : ℤ) - (-y).toNat = y := Int.toNat_sub_toNat_neg y
      have hgcd : (insert a s).gcd id = Nat.gcd a g := by
        rw [Finset.gcd_insert]
        rfl
      rw [hgcd, hbez]
      push_cast [hP, hM]
      linear_combination (a : ℤ) * htx + ((u : ℤ) - (v : ℤ)) * hty + y * huv

/-- Consecutive elements of the closure, from gcd `1`. -/
theorem exists_consecutive_of_gcd_one {G : Finset ℕ} (hgcd : G.gcd id = 1) :
    ∃ v, v ∈ AddSubmonoid.closure (G : Set ℕ) ∧
      v + 1 ∈ AddSubmonoid.closure (G : Set ℕ) := by
  obtain ⟨u, hu, v, hv, huv⟩ := exists_diff_gcd G
  rw [hgcd] at huv
  have h : u = v + 1 := by
    have : (u : ℤ) = v + 1 := by push_cast at huv ⊢; linarith
    exact_mod_cast this
  exact ⟨v, hv, h ▸ hu⟩

/-- **`def:branching-semigroup`, cofiniteness**: a numerical semigroup whose
finite generating set has gcd `1` contains every sufficiently large natural
number; the general gcd reduces to this by scaling.  This is the sentence
that makes supports with equal branching semigroups agree after enough
merging. -/
theorem semigroup_cofinite {G : Finset ℕ} (hgcd : G.gcd id = 1) :
    ∃ N, ∀ n, N ≤ n → n ∈ AddSubmonoid.closure (G : Set ℕ) := by
  obtain ⟨v, hv, hv1⟩ := exists_consecutive_of_gcd_one hgcd
  refine ⟨v * v, fun n hn => ?_⟩
  have hco : Nat.Coprime (v + 1) v := by
    rw [Nat.add_comm]
    exact Nat.coprime_add_self_left.mpr (Nat.gcd_one_left v)
  refine mem_of_coprime hv1 hv hco (by omega) ?_
  simpa using hn

/-- Every element of the closure is a multiple of the gcd of the generators. -/
theorem gcd_dvd_of_mem_closure {G : Finset ℕ} {n : ℕ}
    (hn : n ∈ AddSubmonoid.closure (G : Set ℕ)) : G.gcd id ∣ n := by
  induction hn using AddSubmonoid.closure_induction with
  | mem x hx => exact Finset.gcd_dvd (Finset.mem_coe.mp hx)
  | zero => exact dvd_zero _
  | add x y _ _ hx hy => exact dvd_add hx hy

/-- Equal closures force equal gcds of the generating sets. -/
theorem gcd_eq_of_closure_eq {G G' : Finset ℕ}
    (h : AddSubmonoid.closure (G : Set ℕ) = AddSubmonoid.closure (G' : Set ℕ)) :
    G.gcd id = G'.gcd id := by
  refine Nat.dvd_antisymm (Finset.dvd_gcd fun x hx => ?_)
    (Finset.dvd_gcd fun x hx => ?_)
  · exact gcd_dvd_of_mem_closure (h ▸ AddSubmonoid.subset_closure (Finset.mem_coe.mpr hx))
  · exact gcd_dvd_of_mem_closure (h ▸ AddSubmonoid.subset_closure (Finset.mem_coe.mpr hx))

/-- Scaling into the closure: a closure element of the divided generators scales to a
closure element of the generators. -/
theorem mul_mem_closure_of_mem_closure_div {G : Finset ℕ} {g n : ℕ}
    (hgdvd : ∀ x ∈ G, g ∣ x)
    (hn : n ∈ AddSubmonoid.closure ((G.image (· / g) : Finset ℕ) : Set ℕ)) :
    g * n ∈ AddSubmonoid.closure (G : Set ℕ) := by
  induction hn using AddSubmonoid.closure_induction with
  | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      rw [Nat.mul_div_cancel' (hgdvd y hy)]
      exact AddSubmonoid.subset_closure (Finset.mem_coe.mpr hy)
  | zero => simp
  | add x y _ _ hx hy =>
      rw [Nat.mul_add]
      exact add_mem hx hy

/-- **`def:branching-semigroup`, cofiniteness at a general gcd**: a numerical semigroup
with finite generating set contains every sufficiently large multiple of the gcd of its
generators, by scaling `semigroup_cofinite`. -/
theorem semigroup_cofinite_gcd (G : Finset ℕ) :
    ∃ N, ∀ n, N ≤ n → G.gcd id ∣ n → n ∈ AddSubmonoid.closure (G : Set ℕ) := by
  classical
  rcases Nat.eq_zero_or_pos (G.gcd id) with hg0 | hgpos
  · -- gcd zero: only `n = 0` is divisible, below any positive threshold
    refine ⟨1, fun n hn hdvd => ?_⟩
    rw [hg0] at hdvd
    omega
  · have hgdvd : ∀ x ∈ G, G.gcd id ∣ x := fun x hx => Finset.gcd_dvd hx
    -- the divided generators have gcd one
    have hgcd1 : (G.image (· / G.gcd id)).gcd id = 1 := by
      rcases Nat.eq_zero_or_pos ((G.image (· / G.gcd id)).gcd id) with h0 | hpos'
      · exfalso
        rw [Finset.gcd_eq_zero_iff] at h0
        have hex : ∃ x ∈ G, x ≠ 0 := by
          by_contra hcon
          push Not at hcon
          have : G.gcd id = 0 := Finset.gcd_eq_zero_iff.mpr fun x hx => hcon x hx
          omega
        obtain ⟨x, hx, hx0⟩ := hex
        have h5 : G.gcd id ≤ x := Nat.le_of_dvd (by omega) (hgdvd x hx)
        have h6 : 0 < x / G.gcd id := Nat.div_pos h5 hgpos
        have h7 := h0 (x / G.gcd id) (Finset.mem_image_of_mem _ hx)
        simp only [id] at h7
        omega
      · have hdvd : G.gcd id * (G.image (· / G.gcd id)).gcd id ∣ G.gcd id := by
          refine Finset.dvd_gcd fun x hx => ?_
          have h1 : (G.image (· / G.gcd id)).gcd id ∣ x / G.gcd id :=
            Finset.gcd_dvd (Finset.mem_image_of_mem _ hx)
          calc G.gcd id * (G.image (· / G.gcd id)).gcd id
              ∣ G.gcd id * (x / G.gcd id) := mul_dvd_mul_left _ h1
            _ = x := Nat.mul_div_cancel' (hgdvd x hx)
        have hle : G.gcd id * (G.image (· / G.gcd id)).gcd id ≤ G.gcd id :=
          Nat.le_of_dvd hgpos hdvd
        have hle1 : (G.image (· / G.gcd id)).gcd id ≤ 1 := by
          by_contra hcon
          have h2 : G.gcd id * 2 ≤ G.gcd id * (G.image (· / G.gcd id)).gcd id :=
            Nat.mul_le_mul_left _ (by omega)
          omega
        omega
    obtain ⟨N₁, hN₁⟩ := semigroup_cofinite hgcd1
    refine ⟨G.gcd id * N₁, fun n hn hdvd => ?_⟩
    obtain ⟨m, rfl⟩ := hdvd
    have hm : N₁ ≤ m := by
      by_contra hcon
      have h3 : G.gcd id * m < G.gcd id * N₁ :=
        (Nat.mul_lt_mul_left hgpos).mpr (by omega)
      omega
    exact mul_mem_closure_of_mem_closure_div hgdvd (hN₁ m hm)

/-- **`thm:semigroup-threshold` in full**: for a nonempty finite set of positive
generators with gcd `d`, some `v` has `vd` and `(v+1)d` in the closure, and every
multiple of `d` at least `v²d` lies in the closure. -/
theorem semigroup_threshold {G : Finset ℕ} (hne : G.Nonempty) (hpos : ∀ x ∈ G, 0 < x) :
    ∃ v : ℕ, G.gcd id * v ∈ AddSubmonoid.closure (G : Set ℕ)
      ∧ G.gcd id * (v + 1) ∈ AddSubmonoid.closure (G : Set ℕ)
      ∧ ∀ n, G.gcd id * v ^ 2 ≤ n → G.gcd id ∣ n → n ∈ AddSubmonoid.closure (G : Set ℕ) := by
  classical
  obtain ⟨x, hx⟩ := hne
  have hgpos : 0 < G.gcd id := by
    rcases Nat.eq_zero_or_pos (G.gcd id) with h0 | h0
    · exfalso
      rw [Finset.gcd_eq_zero_iff] at h0
      have h1 := h0 x hx
      simp only [id] at h1
      have := hpos x hx
      omega
    · exact h0
  have hgdvd : ∀ y ∈ G, G.gcd id ∣ y := fun y hy => Finset.gcd_dvd hy
  have hgcd1 : (G.image (· / G.gcd id)).gcd id = 1 := by
    -- as in `semigroup_cofinite_gcd`
    rcases Nat.eq_zero_or_pos ((G.image (· / G.gcd id)).gcd id) with h0 | hpos'
    · exfalso
      rw [Finset.gcd_eq_zero_iff] at h0
      have h5 : G.gcd id ≤ x := Nat.le_of_dvd (hpos x hx) (hgdvd x hx)
      have h6 : 0 < x / G.gcd id := Nat.div_pos h5 hgpos
      have h7 := h0 (x / G.gcd id) (Finset.mem_image_of_mem _ hx)
      simp only [id] at h7
      omega
    · have hdvd : G.gcd id * (G.image (· / G.gcd id)).gcd id ∣ G.gcd id := by
        refine Finset.dvd_gcd fun y hy => ?_
        have h1 : (G.image (· / G.gcd id)).gcd id ∣ y / G.gcd id :=
          Finset.gcd_dvd (Finset.mem_image_of_mem _ hy)
        calc G.gcd id * (G.image (· / G.gcd id)).gcd id
            ∣ G.gcd id * (y / G.gcd id) := mul_dvd_mul_left _ h1
          _ = y := Nat.mul_div_cancel' (hgdvd y hy)
      have hle := Nat.le_of_dvd hgpos hdvd
      have hle1 : (G.image (· / G.gcd id)).gcd id ≤ 1 := by
        by_contra hcon
        have h2 : G.gcd id * 2 ≤ G.gcd id * (G.image (· / G.gcd id)).gcd id :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      omega
  obtain ⟨v, hv, hv1⟩ := exists_consecutive_of_gcd_one hgcd1
  refine ⟨v, mul_mem_closure_of_mem_closure_div hgdvd hv,
    mul_mem_closure_of_mem_closure_div hgdvd hv1, fun n hn hdvd => ?_⟩
  obtain ⟨m, rfl⟩ := hdvd
  have hm : v ^ 2 ≤ m := by
    by_contra hcon
    have h3 : G.gcd id * m < G.gcd id * v ^ 2 :=
      (Nat.mul_lt_mul_left hgpos).mpr (by omega)
    omega
  refine mul_mem_closure_of_mem_closure_div hgdvd ?_
  have hco : Nat.Coprime (v + 1) v := by
    rw [Nat.add_comm]
    exact Nat.coprime_add_self_left.mpr (Nat.gcd_one_left v)
  refine mem_of_coprime hv1 hv hco (by omega) ?_
  have h8 : v + 1 - 1 = v := by omega
  rw [h8, ← sq]
  exact hm

end ChainClasses
