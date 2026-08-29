/-
The formal screen grammar of the arbitrary-support proof
(`arbitrary_offspring_matching.tex`, the grammar and the successor
step): the target alphabet, the cascade pairs, the successor step on
zero lists, screens as data, and the bounded alphabet and screen
family that close the grammar and bound `𝔠_ν`.

* `Tgt`: the target alphabet: forced states `Z j`, the fresh state
  `F`, and fresh components `Fk k`;
* `gpair j`: the children targets of a counter `j`, following the
  kernel: `j ≥ 4` forces the split `(j/2, j - j/2)`, `j = 3` emits
  the forced counter `2` and a fresh child, `j ≤ 2` emits fresh
  children;
* `tgtSucc S` / `zsucc S`: the successor step on targets and on zero
  lists: forced targets advance through their cascade pairs, the fresh
  target through all components of the support;
* `GScreen`: screens as data: a source cell, a zero list, and an
  optional normalization; `screenSucc S` produces the successor
  screens (one distinguished source child, the normalization
  descending to a child);
* `tgtUniv N` / `screenUniv N`: the bounded alphabet and screen
  family;
  `tgtSucc_subset`, `zsucc_subset` and `screenSucc_subset` show the
  grammar is closed inside them, so the screen family generated from
  any seed is finite (`|𝔠_ν| ≤ |screenUniv N|`).
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring

namespace GraphMarkovMatching

/-- The target alphabet: forced states, the fresh state, and fresh
components. -/
inductive Tgt : Type
  | Z (j : ℕ)
  | F
  | Fk (k : ℕ)
  deriving DecidableEq

/-- The children targets of a counter, following the kernel. -/
def gpair (j : ℕ) : Finset Tgt :=
  if 4 ≤ j then {Tgt.Z (j / 2), Tgt.Z (j - j / 2)}
  else if j = 3 then {Tgt.Z 2, Tgt.F}
  else {Tgt.F}

/-- The successor step on targets: forced targets advance through
their cascade pairs, the fresh target through all components of the
support. -/
def tgtSucc (S : Finset ℕ) : Tgt → Finset Tgt
  | Tgt.Z j => gpair j
  | Tgt.F => S.biUnion gpair
  | Tgt.Fk k => gpair k

/-- The successor step on zero lists. -/
def zsucc (S : Finset ℕ) (z : Finset Tgt) : Finset Tgt :=
  z.biUnion (tgtSucc S)

/-- A formal screen: a source cell, a zero list, and an optional
normalization. -/
structure GScreen : Type where
  cell : Tgt
  zlist : Finset Tgt
  norm : Option Tgt
  deriving DecidableEq

/-- The normalization descends to a child of the normalization. -/
def normSucc (S : Finset ℕ) : Option Tgt → Finset (Option Tgt)
  | none => {none}
  | some u => (tgtSucc S u).image some

/-- The successor screens: one distinguished source child carries the
successor zero list and a child of the normalization. -/
def screenSucc (S : Finset ℕ) (sc : GScreen) : Finset GScreen :=
  ((tgtSucc S sc.cell) ×ˢ normSucc S sc.norm).image
    fun p => ⟨p.1, zsucc S sc.zlist, p.2⟩

/-! ### The bounded alphabet and screen family -/

/-- The bounded target alphabet. -/
def tgtUniv (N : ℕ) : Finset Tgt :=
  insert Tgt.F (((Finset.range (N + 1)).image Tgt.Z)
    ∪ ((Finset.range (N + 1)).image Tgt.Fk))

lemma F_mem_tgtUniv {N : ℕ} : Tgt.F ∈ tgtUniv N :=
  Finset.mem_insert_self _ _

lemma Z_mem_tgtUniv {N j : ℕ} : Tgt.Z j ∈ tgtUniv N ↔ j ≤ N := by
  simp [tgtUniv, Nat.lt_succ_iff]

lemma Fk_mem_tgtUniv {N k : ℕ} : Tgt.Fk k ∈ tgtUniv N ↔ k ≤ N := by
  simp [tgtUniv, Nat.lt_succ_iff]

/-- Gadget pairs of bounded counters are bounded. -/
lemma gpair_subset {N j : ℕ} (hN : 2 ≤ N) (hj : j ≤ N) :
    gpair j ⊆ tgtUniv N := by
  intro t ht
  rw [gpair] at ht
  split_ifs at ht with h4 h3
  · rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Z_mem_tgtUniv.mpr (by omega)
    · rw [Finset.mem_singleton.mp ht]
      exact Z_mem_tgtUniv.mpr (by omega)
  · rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Z_mem_tgtUniv.mpr (by omega)
    · rw [Finset.mem_singleton.mp ht]
      exact F_mem_tgtUniv
  · rw [Finset.mem_singleton.mp ht]
    exact F_mem_tgtUniv

/-- The successor step preserves the bounded alphabet. -/
lemma tgtSucc_subset {N : ℕ} {S : Finset ℕ} {t : Tgt} (hN : 2 ≤ N)
    (hS : ∀ k ∈ S, k ≤ N) (ht : t ∈ tgtUniv N) :
    tgtSucc S t ⊆ tgtUniv N := by
  match t with
  | Tgt.Z j => exact gpair_subset hN (Z_mem_tgtUniv.mp ht)
  | Tgt.F =>
      intro x hx
      obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hx
      exact gpair_subset hN (hS k hk) hxk
  | Tgt.Fk k => exact gpair_subset hN (Fk_mem_tgtUniv.mp ht)

/-- The successor step preserves bounded zero lists. -/
lemma zsucc_subset {N : ℕ} {S : Finset ℕ} {z : Finset Tgt} (hN : 2 ≤ N)
    (hS : ∀ k ∈ S, k ≤ N) (hz : z ⊆ tgtUniv N) :
    zsucc S z ⊆ tgtUniv N := by
  intro x hx
  obtain ⟨t, htz, hxt⟩ := Finset.mem_biUnion.mp hx
  exact tgtSucc_subset hN hS (hz htz) hxt

/-- The bounded screen family. -/
def screenUniv (N : ℕ) : Finset GScreen :=
  ((tgtUniv N) ×ˢ ((tgtUniv N).powerset
      ×ˢ insert none ((tgtUniv N).image some))).image
    fun x => ⟨x.1, x.2.1, x.2.2⟩

/-- Membership in the bounded screen family componentwise. -/
lemma mem_screenUniv {N : ℕ} {sc : GScreen} :
    sc ∈ screenUniv N
      ↔ sc.cell ∈ tgtUniv N ∧ sc.zlist ⊆ tgtUniv N
        ∧ ∀ u, sc.norm = some u → u ∈ tgtUniv N := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx
    obtain ⟨h21, h22⟩ := Finset.mem_product.mp h2
    refine ⟨h1, Finset.mem_powerset.mp h21, fun u hu => ?_⟩
    have hu' : x.2.2 = some u := hu
    rcases Finset.mem_insert.mp h22 with h | h
    · rw [h] at hu'
      exact absurd hu' (by simp)
    · obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp h
      rw [← hvu] at hu'
      rw [← Option.some_inj.mp hu']
      exact hv
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨c, z, u⟩ := sc
    have hmem : (c, z, u)
        ∈ (tgtUniv N) ×ˢ ((tgtUniv N).powerset
            ×ˢ insert none ((tgtUniv N).image some)) := by
      refine Finset.mem_product.mpr ⟨h1, Finset.mem_product.mpr
        ⟨Finset.mem_powerset.mpr h2, ?_⟩⟩
      match u with
      | none => exact Finset.mem_insert_self _ _
      | some v =>
          exact Finset.mem_insert_of_mem
            (Finset.mem_image_of_mem some (h3 v rfl))
    rw [screenUniv]
    exact Finset.mem_image.mpr ⟨(c, z, u), hmem, rfl⟩

/-- **The grammar is closed inside the bounded screen family**: every
successor of a bounded screen is bounded.  Consequently the screen
family generated from any seed inside `screenUniv N` is finite, of
size at most `|screenUniv N|`. -/
theorem screenSucc_subset {N : ℕ} {S : Finset ℕ} {sc : GScreen}
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hsc : sc ∈ screenUniv N) :
    screenSucc S sc ⊆ screenUniv N := by
  obtain ⟨h1, h2, h3⟩ := mem_screenUniv.mp hsc
  intro sc' hsc'
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hsc'
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  refine mem_screenUniv.mpr
    ⟨tgtSucc_subset hN hS h1 hp1, zsucc_subset hN hS h2, fun u hu => ?_⟩
  have hu' : p.2 = some u := hu
  cases hn : sc.norm with
  | none =>
      rw [hn] at hp2
      simp only [normSucc, Finset.mem_singleton] at hp2
      rw [hp2] at hu'
      exact absurd hu' (by simp)
  | some v =>
      rw [hn] at hp2
      simp only [normSucc] at hp2
      obtain ⟨w, hw, hwp⟩ := Finset.mem_image.mp hp2
      rw [← hwp] at hu'
      rw [← Option.some_inj.mp hu']
      exact tgtSucc_subset hN hS (h3 v hn) hw

end GraphMarkovMatching
