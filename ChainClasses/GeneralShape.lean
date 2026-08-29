/-
`sec:general-shapes` of `matching_classes_general.tex`: `def:shape-general`,
shapes at general arity.

A shape is a neck of `m ≥ 1` vertices together with a finite, possibly empty,
list of bushes at each neck vertex, the last list being the exit bouquet of
the terminating split. The bushes are finite rooted trees of arbitrary arity
(`RTree` of `Dilution.lean`), the offspring bound entering as the inductive
predicate `DegLe`.

* `GShape`, `GShape.realise`, `GShape.size`: the pair `(m,(β₁,…,β_m))`, its
  realisation with the entry at the root and the bushes of `β_i` attached at
  the `i`-th neck vertex, and the vertex count `size_eq`, `m` plus the sizes
  of the bushes.
* `RTree.DegLe`: offspring numbers in `{0,…,J}`; `realise_degLe` checks that a
  realisation whose bouquets leave room for the neck stays in the class.
* `Countable GShape`: the countability of `𝒮` that makes `rep_D` and the
  events built from it measurable, through the prefix-free code of `RTree`.
-/
import Mathlib.Tactic
import ChainClasses.Dilution

namespace ChainClasses

namespace RTree

/-- The number of vertices of a forest splits over an append. -/
lemma sizeF_append : ∀ l₁ l₂ : List RTree, sizeF (l₁ ++ l₂) = sizeF l₁ + sizeF l₂
  | [], l₂ => by simp [sizeF]
  | c :: cs, l₂ => by
      simp only [List.cons_append, sizeF, sizeF_append cs l₂]
      omega

/-- Offspring numbers in `{0,…,J}`: every vertex has at most `J` children. -/
inductive DegLe (J : ℕ) : RTree → Prop where
  | node : ∀ {cs : List RTree}, cs.length ≤ J → (∀ c ∈ cs, DegLe J c) →
      DegLe J (.node cs)

/-- The offspring bound is monotone. -/
lemma DegLe.mono {J J' : ℕ} (hJJ' : J ≤ J') : ∀ {t : RTree}, DegLe J t → DegLe J' t := by
  intro t
  induction t using RTree.ind with
  | _ cs ih =>
      rintro ⟨hlen, hall⟩
      exact ⟨hlen.trans hJJ', fun c hc => ih c hc (hall c hc)⟩

end RTree

/-- **`def:shape-general`**: a shape is a neck of `m = necks + 1 ≥ 1` vertices
together with a list of bushes at each neck vertex, the last list being the
exit bouquet of the terminating split. -/
structure GShape where
  necks : ℕ
  dec : Fin (necks + 1) → List RTree

namespace GShape

/-- The neck length `m` of `def:shape-general`. -/
def neckLen (σ : GShape) : ℕ := σ.necks + 1

/-- The bush lists in neck order, entry first. -/
def decs (σ : GShape) : List (List RTree) := List.ofFn σ.dec

/-- The realisation of a decorated neck, read from the entry down: a neck
vertex carries its bushes and the rest of the neck as children, the exit only
its bouquet. -/
def realiseAux : List (List RTree) → RTree
  | [] => .node []
  | [β] => .node β
  | β :: r :: rest => .node (β ++ [realiseAux (r :: rest)])

/-- **`def:shape-general`**, the realisation: the path `v_1⋯v_m` with the
bushes of `β_i` attached at `v_i` by an edge, rooted at the entry `v_1`. -/
def realise (σ : GShape) : RTree := realiseAux σ.decs

/-- `|σ|`, the number of vertices of the realisation. -/
def size (σ : GShape) : ℕ := σ.realise.size

lemma realiseAux_size : ∀ bs : List (List RTree), bs ≠ [] →
    (realiseAux bs).size = bs.length + (bs.map RTree.sizeF).sum
  | [], h => absurd rfl h
  | [β], _ => by
      simp [realiseAux, RTree.size]
  | β :: r :: rest, _ => by
      have ih := realiseAux_size (r :: rest) (by simp)
      simp only [realiseAux, RTree.size, RTree.sizeF_append, List.map_cons,
        List.sum_cons, List.length_cons] at ih ⊢
      simp only [RTree.sizeF]
      omega

lemma decs_length (σ : GShape) : σ.decs.length = σ.necks + 1 := by
  rw [decs, List.length_ofFn]

lemma decs_ne_nil (σ : GShape) : σ.decs ≠ [] := by
  intro h
  have := σ.decs_length
  rw [h] at this
  simp at this

/-- **`def:shape-general`**, the size: `m` neck vertices plus the vertices of
the bushes. -/
lemma size_eq (σ : GShape) :
    σ.size = σ.neckLen + (σ.decs.map RTree.sizeF).sum := by
  rw [size, realise, realiseAux_size σ.decs σ.decs_ne_nil, decs_length, neckLen]

lemma neckLen_le_size (σ : GShape) : σ.neckLen ≤ σ.size := by
  rw [size_eq]
  exact Nat.le_add_right _ _

lemma realiseAux_degLe {J : ℕ} : ∀ bs : List (List RTree),
    (∀ β ∈ bs, β.length + 1 ≤ J) → (∀ β ∈ bs, ∀ t ∈ β, RTree.DegLe J t) →
    RTree.DegLe J (realiseAux bs)
  | [], _, _ => ⟨by simp, by simp⟩
  | [β], hlen, hall => by
      refine ⟨?_, ?_⟩
      · have := hlen β (by simp)
        simpa using Nat.le_of_succ_le this
      · intro c hc
        exact hall β (by simp) c hc
  | β :: r :: rest, hlen, hall => by
      have ih := realiseAux_degLe (r :: rest)
        (fun γ hγ => hlen γ (List.mem_cons_of_mem β hγ))
        (fun γ hγ => hall γ (List.mem_cons_of_mem β hγ))
      refine ⟨?_, ?_⟩
      · have := hlen β (by simp)
        simpa using this
      · intro c hc
        rcases List.mem_append.mp hc with hc' | hc'
        · exact hall β (by simp) c hc'
        · rw [List.mem_singleton.mp hc']
          exact ih

/-- A realisation whose bush lists leave room for the neck edge has offspring
numbers in `{0,…,J}`. -/
lemma realise_degLe {J : ℕ} (σ : GShape)
    (hlen : ∀ i, (σ.dec i).length + 1 ≤ J)
    (hall : ∀ i, ∀ t ∈ σ.dec i, RTree.DegLe J t) :
    RTree.DegLe J σ.realise := by
  refine realiseAux_degLe σ.decs (fun β hβ => ?_) (fun β hβ => ?_) <;>
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hβ
  · exact hlen i
  · exact hall i

/-- `𝒮` is countable at general arity, so `rep_D` and the events built from
it are measurable. -/
instance : Countable GShape := by
  have hinj : Function.Injective
      (fun σ : GShape => (⟨σ.necks, σ.dec⟩ : Σ n : ℕ, Fin (n + 1) → List RTree)) := by
    rintro ⟨n, f⟩ ⟨m, g⟩ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    rw [heq_eq_eq] at h2
    rw [h2]
  exact hinj.countable

end GShape

end ChainClasses