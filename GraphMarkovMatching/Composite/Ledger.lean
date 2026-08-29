/-
The finite ledger glue (`arbitrary_offspring_matching.tex`,
`sec:composite`, the rank paragraph in the proof of
`thm:composite-acyclic` and its matrix conclusion
`eq:composite-nilpotent`): from the combinatorial acyclicity of the
common block to nilpotence of a concrete transfer matrix over a finite
index of screens.

* `no_common_step_cycle`: no directed cycle (`Relation.TransGen`) of
  common full-successor steps passes through good screens, where good
  means F-diagonal-free, zero-list nonempty, and anchored at some depth;
  the cycle unfolds to a periodic path of common steps, which
  `no_live_common_cycle` forbids;
* `ledger_nilpotent` (`eq:composite-nilpotent`): a transfer matrix over
  a finite ledger of screens whose support consists of good common steps
  is annihilated by `Fintype.card` applications, by
  `nilpotent_of_acyclic`;
* `letterUniv`, `screenUniv`, `mem_screenUniv`, `screenUniv_card_le`: a
  finite universe of letters, the induced finite universe of screens
  (cells from the letter universe, zero lists among its subsets), and the
  product-powerset cardinality bound;
* `no_step_cycle`, `ledger_nilpotentE`: the entrance-inclusive analogues
  over `CommonStepE` edges via `no_live_step_cycle`, under the standing
  membership of the declared pairs of both sides in the common support;
* `no_step_cycleS`, `ledger_nilpotentES`: the source-entrance analogues
  over `CommonStepES` edges via `no_live_step_cycleS`, under the
  standing membership of the declared pairs of the source side in the
  common support.
-/
import GraphMarkovMatching.Composite.Anchor
import GraphMarkovMatching.Composite.Rank
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

namespace GraphMarkovMatching
namespace Composite

/-- A transitive step decomposes into a finite chain of single steps,
recorded as a function on `ℕ` together with the chain length. -/
private lemma exists_chain {β : Type*} {R : β → β → Prop} {a b : β}
    (h : Relation.TransGen R a b) :
    ∃ n : ℕ, ∃ f : ℕ → β, 1 ≤ n ∧ f 0 = a ∧ f n = b ∧
      ∀ i < n, R (f i) (f (i + 1)) := by
  induction h with
  | @single c hac =>
      refine ⟨1, fun i => if i = 0 then a else c, le_rfl, by simp, by simp, ?_⟩
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa using hac
  | @tail c d hac hcd ih =>
      obtain ⟨n, f, hn, hf0, hfn, hstep⟩ := ih
      refine ⟨n + 1, fun i => if i ≤ n then f i else d, by omega, ?_, ?_, ?_⟩
      · have h0 : (0 : ℕ) ≤ n := Nat.zero_le n
        simpa [h0] using hf0
      · have hneg : ¬ (n + 1 ≤ n) := by omega
        simp [hneg]
      · intro i hi
        rcases Nat.lt_or_ge i n with hilt | hige
        · have h1 : i ≤ n := by omega
          have h2 : i + 1 ≤ n := by omega
          simpa [h1, h2] using hstep i hilt
        · have hieq : i = n := by omega
          subst hieq
          have hpos : i ≤ i := le_rfl
          have hneg : ¬ (i + 1 ≤ i) := by omega
          simpa [hpos, hneg, hfn] using hcd

/-- **No cycle of good common steps** (`thm:composite-acyclic`, rank
paragraph).
A directed cycle of common full-successor steps through screens that are
F-diagonal-free, zero-list nonempty, and anchored at some depth is
impossible: the cycle unfolds to a periodic path of common steps, and
`no_live_common_cycle` forbids such a path. -/
theorem no_common_step_cycle
    (S : Finset ℕ) (hSne : S.Nonempty) (Esrc Etgt : Finset (ℕ × ℕ))
    (Good : Screen → Prop)
    (hdiag : ∀ s, Good s → ¬(s.cell = Letter.F ∧ Letter.F ∈ s.zlist))
    (hzne : ∀ s, Good s → s.zlist.Nonempty)
    (hanch : ∀ s, Good s → ∃ δ, ScreenAnchored S Esrc Etgt δ s) :
    ∀ s, ¬ Relation.TransGen
      (fun u u' => CommonStep S Etgt u u' ∧ Good u ∧ Good u') s s := by
  intro s hcyc
  obtain ⟨n, f, hn, hf0, hfn, hchain⟩ := exists_chain hcyc
  have hmodlt : ∀ j : ℕ, j % n < n := fun j => Nat.mod_lt j (by omega)
  have hgood : ∀ j : ℕ, Good (f (j % n)) := fun j => (hchain _ (hmodlt j)).2.1
  -- the cyclic extension steps by common steps at every index
  have hstep : ∀ j : ℕ, CommonStep S Etgt (f (j % n)) (f ((j + 1) % n)) := by
    intro j
    have hR := (hchain (j % n) (hmodlt j)).1
    rcases Nat.lt_or_ge (j % n + 1) n with hlt | hge
    · have heq : (j + 1) % n = j % n + 1 := by
        have hdm : n * (j / n) + j % n = j := Nat.div_add_mod j n
        have h1 : j + 1 = n * (j / n) + (j % n + 1) := by omega
        rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      rw [heq]
      exact hR
    · have hn1 : j % n + 1 = n := by
        have := hmodlt j
        omega
      have heq : (j + 1) % n = 0 := by
        have hdm : n * (j / n) + j % n = j := Nat.div_add_mod j n
        have hmul : n * (j / n + 1) = n * (j / n) + n := by ring
        have h1 : j + 1 = n * (j / n + 1) := by omega
        rw [h1, Nat.mul_mod_right]
      have hfn0 : f (j % n + 1) = f 0 := by rw [hn1, hfn, hf0]
      rw [heq, ← hfn0]
      exact hR
  have hper : ∀ j : ℕ, f ((j + n) % n) = f (j % n) := by
    intro j
    rw [Nat.add_mod_right]
  obtain ⟨δ0, hδ0⟩ := hanch _ (hgood 0)
  exact no_live_common_cycle S hSne Esrc Etgt (fun j => f (j % n)) n hn
    hstep hper δ0 hδ0 (hzne _ (hgood 0)) (fun j => hdiag (f (j % n)) (hgood j))

/-- **Nilpotence of the ledger transfer matrix**
(`eq:composite-nilpotent`).  Over a finite index of screens, a transfer
matrix whose support consists of good common steps is annihilated by
`Fintype.card` applications: a support cycle would transport through the
index map to a cycle of good common steps. -/
theorem ledger_nilpotent
    (S : Finset ℕ) (hSne : S.Nonempty) (Esrc Etgt : Finset (ℕ × ℕ))
    (Good : Screen → Prop)
    (hdiag : ∀ s, Good s → ¬(s.cell = Letter.F ∧ Letter.F ∈ s.zlist))
    (hzne : ∀ s, Good s → s.zlist.Nonempty)
    (hanch : ∀ s, Good s → ∃ δ, ScreenAnchored S Esrc Etgt δ s)
    {ι : Type*} [Fintype ι] {α : Type*} [NonUnitalNonAssocSemiring α]
    (emb : ι → Screen) (Nmat : ι → ι → α)
    (hsupp : ∀ i j, Nmat i j ≠ 0 →
      CommonStep S Etgt (emb i) (emb j) ∧ Good (emb i) ∧ Good (emb j)) :
    ∀ v : ι → α, (matApply Nmat)^[Fintype.card ι] v = fun _ => 0 := by
  intro v
  refine nilpotent_of_acyclic Nmat (fun i hcyc => ?_) v
  have htrans : Relation.TransGen
      (fun u u' => CommonStep S Etgt u u' ∧ Good u ∧ Good u')
      (emb i) (emb i) := by
    refine Relation.TransGen.lift emb ?_ i i hcyc
    intro a b hab
    exact hsupp a b hab
  exact no_common_step_cycle S hSne Esrc Etgt Good hdiag hzne hanch
    (emb i) htrans

/-- A finite universe of letters: the fresh letter, the forced letters up
to the largest common return depth, the exposed letters of the support,
and the markers of the declared pairs at stages `1` to `dmax`. -/
def letterUniv (S : Finset ℕ) (C : Finset (ℕ × ℕ)) (dmax : ℕ) :
    Finset Letter :=
  {Letter.F} ∪ (Finset.range (S.sup id + 1)).image Letter.Z
    ∪ S.image Letter.Fk
    ∪ C.biUnion fun p => (Finset.Icc 1 dmax).image fun i => Letter.M p.1 p.2 i

/-- The finite universe of screens over a letter universe: cells from the
letter universe, zero lists among its subsets. -/
def screenUniv (S : Finset ℕ) (C : Finset (ℕ × ℕ)) (dmax : ℕ) :
    Finset Screen :=
  (letterUniv S C dmax ×ˢ (letterUniv S C dmax).powerset).image
    fun q => Screen.mk q.1 q.2

lemma mem_screenUniv {S : Finset ℕ} {C : Finset (ℕ × ℕ)} {dmax : ℕ}
    {s : Screen} : s ∈ screenUniv S C dmax ↔
      s.cell ∈ letterUniv S C dmax ∧ s.zlist ⊆ letterUniv S C dmax := by
  constructor
  · intro hs
    obtain ⟨q, hq, hqs⟩ := Finset.mem_image.mp hs
    obtain ⟨hc, hz⟩ := Finset.mem_product.mp hq
    rw [← hqs]
    exact ⟨hc, Finset.mem_powerset.mp hz⟩
  · rintro ⟨hc, hz⟩
    exact Finset.mem_image.mpr ⟨(s.cell, s.zlist),
      Finset.mem_product.mpr ⟨hc, Finset.mem_powerset.mpr hz⟩, rfl⟩

/-- The screen universe is at most product-powerset large. -/
lemma screenUniv_card_le (S : Finset ℕ) (C : Finset (ℕ × ℕ)) (dmax : ℕ) :
    (screenUniv S C dmax).card ≤
      (letterUniv S C dmax).card * 2 ^ (letterUniv S C dmax).card := by
  calc (screenUniv S C dmax).card
      ≤ (letterUniv S C dmax ×ˢ (letterUniv S C dmax).powerset).card :=
        Finset.card_image_le
    _ = (letterUniv S C dmax).card * 2 ^ (letterUniv S C dmax).card := by
        rw [Finset.card_product, Finset.card_powerset]

/-! ### Entrance-inclusive edges -/

/-- **No cycle of good entrance-inclusive steps** (`thm:composite-acyclic`,
rank paragraph, entrance-inclusive form).  A directed cycle of
entrance-inclusive full-successor steps through screens that are
F-diagonal-free, zero-list nonempty, and anchored at some depth is
impossible when every declared pair of either side lies in the common
support: the cycle unfolds to a periodic path of entrance-inclusive
steps, and `no_live_step_cycle` forbids such a path. -/
theorem no_step_cycle
    (S : Finset ℕ) (hSne : S.Nonempty) (Esrc Etgt : Finset (ℕ × ℕ))
    (hEsrc : ∀ p ∈ Esrc, p.1 ∈ S ∧ p.2 ∈ S)
    (hEtgt : ∀ p ∈ Etgt, p.1 ∈ S ∧ p.2 ∈ S)
    (Good : Screen → Prop)
    (hdiag : ∀ s, Good s → ¬(s.cell = Letter.F ∧ Letter.F ∈ s.zlist))
    (hzne : ∀ s, Good s → s.zlist.Nonempty)
    (hanch : ∀ s, Good s → ∃ δ, ScreenAnchored S Esrc Etgt δ s) :
    ∀ s, ¬ Relation.TransGen
      (fun u u' => CommonStepE S Etgt u u' ∧ Good u ∧ Good u') s s := by
  intro s hcyc
  obtain ⟨n, f, hn, hf0, hfn, hchain⟩ := exists_chain hcyc
  have hmodlt : ∀ j : ℕ, j % n < n := fun j => Nat.mod_lt j (by omega)
  have hgood : ∀ j : ℕ, Good (f (j % n)) := fun j => (hchain _ (hmodlt j)).2.1
  -- the cyclic extension steps by entrance-inclusive steps at every index
  have hstep : ∀ j : ℕ, CommonStepE S Etgt (f (j % n)) (f ((j + 1) % n)) := by
    intro j
    have hR := (hchain (j % n) (hmodlt j)).1
    rcases Nat.lt_or_ge (j % n + 1) n with hlt | hge
    · have heq : (j + 1) % n = j % n + 1 := by
        have hdm : n * (j / n) + j % n = j := Nat.div_add_mod j n
        have h1 : j + 1 = n * (j / n) + (j % n + 1) := by omega
        rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      rw [heq]
      exact hR
    · have hn1 : j % n + 1 = n := by
        have := hmodlt j
        omega
      have heq : (j + 1) % n = 0 := by
        have hdm : n * (j / n) + j % n = j := Nat.div_add_mod j n
        have hmul : n * (j / n + 1) = n * (j / n) + n := by ring
        have h1 : j + 1 = n * (j / n + 1) := by omega
        rw [h1, Nat.mul_mod_right]
      have hfn0 : f (j % n + 1) = f 0 := by rw [hn1, hfn, hf0]
      rw [heq, ← hfn0]
      exact hR
  have hper : ∀ j : ℕ, f ((j + n) % n) = f (j % n) := by
    intro j
    rw [Nat.add_mod_right]
  obtain ⟨δ0, hδ0⟩ := hanch _ (hgood 0)
  exact no_live_step_cycle S hSne Esrc Etgt hEsrc hEtgt (fun j => f (j % n))
    n hn hstep hper δ0 hδ0 (hzne _ (hgood 0))
    (fun j => hdiag (f (j % n)) (hgood j))

/-- **Nilpotence of the ledger transfer matrix, entrance-inclusive form**
(`eq:composite-nilpotent`).  Over a finite index of screens, a transfer
matrix whose support consists of good entrance-inclusive steps is
annihilated by `Fintype.card` applications: a support cycle would
transport through the index map to a cycle of good entrance-inclusive
steps. -/
theorem ledger_nilpotentE
    (S : Finset ℕ) (hSne : S.Nonempty) (Esrc Etgt : Finset (ℕ × ℕ))
    (hEsrc : ∀ p ∈ Esrc, p.1 ∈ S ∧ p.2 ∈ S)
    (hEtgt : ∀ p ∈ Etgt, p.1 ∈ S ∧ p.2 ∈ S)
    (Good : Screen → Prop)
    (hdiag : ∀ s, Good s → ¬(s.cell = Letter.F ∧ Letter.F ∈ s.zlist))
    (hzne : ∀ s, Good s → s.zlist.Nonempty)
    (hanch : ∀ s, Good s → ∃ δ, ScreenAnchored S Esrc Etgt δ s)
    {ι : Type*} [Fintype ι] {α : Type*} [NonUnitalNonAssocSemiring α]
    (emb : ι → Screen) (Nmat : ι → ι → α)
    (hsupp : ∀ i j, Nmat i j ≠ 0 →
      CommonStepE S Etgt (emb i) (emb j) ∧ Good (emb i) ∧ Good (emb j)) :
    ∀ v : ι → α, (matApply Nmat)^[Fintype.card ι] v = fun _ => 0 := by
  intro v
  refine nilpotent_of_acyclic Nmat (fun i hcyc => ?_) v
  have htrans : Relation.TransGen
      (fun u u' => CommonStepE S Etgt u u' ∧ Good u ∧ Good u')
      (emb i) (emb i) := by
    refine Relation.TransGen.lift emb ?_ i i hcyc
    intro a b hab
    exact hsupp a b hab
  exact no_step_cycle S hSne Esrc Etgt hEsrc hEtgt Good hdiag hzne hanch
    (emb i) htrans

/-! ### Source-entrance edges -/

/-- **No cycle of good source-entrance steps** (`thm:composite-acyclic`,
rank paragraph, source-entrance form).  A directed cycle of source-entrance
full-successor steps through screens that are F-diagonal-free,
zero-list nonempty, and anchored at some depth is impossible when every
declared pair of the source side lies in the common support: the cycle
unfolds to a periodic path of source-entrance steps, and
`no_live_step_cycleS` forbids such a path. -/
theorem no_step_cycleS
    (S : Finset ℕ) (hSne : S.Nonempty) (Esrc Etgt : Finset (ℕ × ℕ))
    (hEsrc : ∀ p ∈ Esrc, p.1 ∈ S ∧ p.2 ∈ S)
    (Good : Screen → Prop)
    (hdiag : ∀ s, Good s → ¬(s.cell = Letter.F ∧ Letter.F ∈ s.zlist))
    (hzne : ∀ s, Good s → s.zlist.Nonempty)
    (hanch : ∀ s, Good s → ∃ δ, ScreenAnchored S Esrc Etgt δ s) :
    ∀ s, ¬ Relation.TransGen
      (fun u u' => CommonStepES S Esrc Etgt u u' ∧ Good u ∧ Good u') s s := by
  intro s hcyc
  obtain ⟨n, f, hn, hf0, hfn, hchain⟩ := exists_chain hcyc
  have hmodlt : ∀ j : ℕ, j % n < n := fun j => Nat.mod_lt j (by omega)
  have hgood : ∀ j : ℕ, Good (f (j % n)) := fun j => (hchain _ (hmodlt j)).2.1
  -- the cyclic extension steps by source-entrance steps at every index
  have hstep : ∀ j : ℕ,
      CommonStepES S Esrc Etgt (f (j % n)) (f ((j + 1) % n)) := by
    intro j
    have hR := (hchain (j % n) (hmodlt j)).1
    rcases Nat.lt_or_ge (j % n + 1) n with hlt | hge
    · have heq : (j + 1) % n = j % n + 1 := by
        have hdm : n * (j / n) + j % n = j := Nat.div_add_mod j n
        have h1 : j + 1 = n * (j / n) + (j % n + 1) := by omega
        rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      rw [heq]
      exact hR
    · have hn1 : j % n + 1 = n := by
        have := hmodlt j
        omega
      have heq : (j + 1) % n = 0 := by
        have hdm : n * (j / n) + j % n = j := Nat.div_add_mod j n
        have hmul : n * (j / n + 1) = n * (j / n) + n := by ring
        have h1 : j + 1 = n * (j / n + 1) := by omega
        rw [h1, Nat.mul_mod_right]
      have hfn0 : f (j % n + 1) = f 0 := by rw [hn1, hfn, hf0]
      rw [heq, ← hfn0]
      exact hR
  have hper : ∀ j : ℕ, f ((j + n) % n) = f (j % n) := by
    intro j
    rw [Nat.add_mod_right]
  obtain ⟨δ0, hδ0⟩ := hanch _ (hgood 0)
  exact no_live_step_cycleS S hSne Esrc Etgt hEsrc (fun j => f (j % n))
    n hn hstep hper δ0 hδ0 (hzne _ (hgood 0))
    (fun j => hdiag (f (j % n)) (hgood j))

/-- **Nilpotence of the ledger transfer matrix, source-entrance form**
(`eq:composite-nilpotent`).  Over a finite index of screens, a
transfer matrix whose support consists of good source-entrance steps is
annihilated by `Fintype.card` applications: a support cycle would
transport through the index map to a cycle of good source-entrance
steps. -/
theorem ledger_nilpotentES
    (S : Finset ℕ) (hSne : S.Nonempty) (Esrc Etgt : Finset (ℕ × ℕ))
    (hEsrc : ∀ p ∈ Esrc, p.1 ∈ S ∧ p.2 ∈ S)
    (Good : Screen → Prop)
    (hdiag : ∀ s, Good s → ¬(s.cell = Letter.F ∧ Letter.F ∈ s.zlist))
    (hzne : ∀ s, Good s → s.zlist.Nonempty)
    (hanch : ∀ s, Good s → ∃ δ, ScreenAnchored S Esrc Etgt δ s)
    {ι : Type*} [Fintype ι] {α : Type*} [NonUnitalNonAssocSemiring α]
    (emb : ι → Screen) (Nmat : ι → ι → α)
    (hsupp : ∀ i j, Nmat i j ≠ 0 →
      CommonStepES S Esrc Etgt (emb i) (emb j) ∧ Good (emb i) ∧ Good (emb j)) :
    ∀ v : ι → α, (matApply Nmat)^[Fintype.card ι] v = fun _ => 0 := by
  intro v
  refine nilpotent_of_acyclic Nmat (fun i hcyc => ?_) v
  have htrans : Relation.TransGen
      (fun u u' => CommonStepES S Esrc Etgt u u' ∧ Good u ∧ Good u')
      (emb i) (emb i) := by
    refine Relation.TransGen.lift emb ?_ i i hcyc
    intro a b hab
    exact hsupp a b hab
  exact no_step_cycleS S hSne Esrc Etgt hEsrc Good hdiag hzne hanch
    (emb i) htrans

end Composite
end GraphMarkovMatching
