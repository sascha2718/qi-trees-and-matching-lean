import Mathlib.Tactic
import ChainClasses.General.GeneralShape

/-!
`sec:general-relabel` of `matching_classes_general.tex`,
`it:general-dilution`: the greedy cut of `thm:dilution` at general arity.

The cut is the recursion of `Dilution.lean` run on rose trees: walking up from
the leaves, the part being accumulated is cut off as soon as it reaches `s`
vertices.  What changes at arity `J` is only the part bound: a cut is made at
a vertex whose children's remainders are each below `s`, and there are now up
to `J` of them, so a part has at most `1 + J(s-1) ≤ Js` vertices in place of
`2s-1`.  The count is `dilution_count` unchanged, and the scale lemmas
`cube_bound` and `inv_le_nine_rpow` are arity-free; the comparability of a
shape with its contraction is `markedQI_gContractTree` of
`GeneralContraction`.

* `remSize`/`remSizeF`, `cutCount`/`cutCountF`, `maxPart`/`maxPartF`: the
  greedy cut on trees and forests.
* `remSize_lt`: the accumulator never reaches `s`.
* `maxPart_le`: every part of a tree with offspring numbers in `{0,…,J}` has
  at most `1 + J(s-1)` vertices; `part_le_mul` absorbs this into `Js`.
* `cut_le`, `cutCount_le_div`: at most `|t|/s` parts are cut off, so cut and
  remainder together are at most `|t|/s + 1` parts.
-/

namespace ChainClasses

namespace RTree

/-! ### The greedy cut on rose trees -/

mutual

/-- The size of the remainder left by the greedy cut at scale `s`: the part
being accumulated is cut off as soon as it reaches `s` vertices. -/
def remSize (s : ℕ) : RTree → ℕ
  | .node cs => if s ≤ 1 + remSizeF s cs then 0 else 1 + remSizeF s cs

/-- The remainder of a forest: the accumulators of the children. -/
def remSizeF (s : ℕ) : List RTree → ℕ
  | [] => 0
  | c :: cs => remSize s c + remSizeF s cs

end

mutual

/-- The number of parts the greedy cut produces. -/
def cutCount (s : ℕ) : RTree → ℕ
  | .node cs => cutCountF s cs + if s ≤ 1 + remSizeF s cs then 1 else 0

/-- The number of parts cut inside a forest. -/
def cutCountF (s : ℕ) : List RTree → ℕ
  | [] => 0
  | c :: cs => cutCount s c + cutCountF s cs

end

mutual

/-- The largest part the greedy cut produces, `0` if there is none. -/
def maxPart (s : ℕ) : RTree → ℕ
  | .node cs =>
      max (maxPartF s cs) (if s ≤ 1 + remSizeF s cs then 1 + remSizeF s cs else 0)

/-- The largest part cut inside a forest. -/
def maxPartF (s : ℕ) : List RTree → ℕ
  | [] => 0
  | c :: cs => max (maxPart s c) (maxPartF s cs)

end

variable {s : ℕ}

/-- The invariant of the cut: the remainder never reaches `s` vertices. -/
lemma remSize_lt (hs : 1 ≤ s) (t : RTree) : remSize s t < s := by
  cases t with
  | node cs => rw [remSize]; split <;> omega

/-- The remainder of a forest of `k` children is at most `k(s-1)`. -/
lemma remSizeF_le (hs : 1 ≤ s) : ∀ cs : List RTree,
    remSizeF s cs ≤ cs.length * (s - 1)
  | [] => by rw [remSizeF]; simp
  | c :: cs => by
      have h1 := remSize_lt hs c
      have h2 := remSizeF_le hs cs
      rw [remSizeF, List.length_cons]
      have h3 : remSize s c ≤ s - 1 := by omega
      calc remSize s c + remSizeF s cs ≤ (s - 1) + cs.length * (s - 1) :=
            Nat.add_le_add h3 h2
        _ = (cs.length + 1) * (s - 1) := by ring

lemma maxPartF_le {bound : ℕ} : ∀ cs : List RTree,
    (∀ c ∈ cs, maxPart s c ≤ bound) → maxPartF s cs ≤ bound
  | [] => fun _ => by rw [maxPartF]; omega
  | c :: cs => fun h => by
      rw [maxPartF]
      exact max_le (h c (List.mem_cons_self ..))
        (maxPartF_le cs fun d hd => h d (List.mem_cons_of_mem c hd))

/-- **`it:general-dilution`, the part bound**: every part of a tree with
offspring numbers in `{0,…,J}` has at most `1 + J(s-1)` vertices: a cut is
made at a vertex whose up to `J` children's remainders are each below `s`. -/
theorem maxPart_le (hs : 1 ≤ s) {J : ℕ} {t : RTree} (hdeg : DegLe J t) :
    maxPart s t ≤ 1 + J * (s - 1) := by
  induction t using ind with
  | _ cs ih =>
      obtain ⟨hlen, hall⟩ := hdeg
      rw [maxPart]
      have h1 : maxPartF s cs ≤ 1 + J * (s - 1) :=
        maxPartF_le cs fun c hc => ih c hc (hall c hc)
      have h2 : remSizeF s cs ≤ cs.length * (s - 1) := remSizeF_le hs cs
      have h3 : cs.length * (s - 1) ≤ J * (s - 1) := Nat.mul_le_mul_right _ hlen
      refine max_le h1 ?_
      split <;> omega

/-- The general part bound absorbs into `Js`, the marked scale of the
contraction. -/
lemma part_le_mul {J : ℕ} (hJ : 1 ≤ J) (hs : 1 ≤ s) : 1 + J * (s - 1) ≤ J * s := by
  obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [show 1 + s' - 1 = s' from by omega, Nat.mul_add, Nat.mul_one]
  omega

/-- The parts are disjoint and each carries at least `s` vertices. -/
lemma cutF_le : ∀ cs : List RTree,
    (∀ c ∈ cs, s * cutCount s c + remSize s c ≤ c.size) →
    s * cutCountF s cs + remSizeF s cs ≤ sizeF cs
  | [] => fun _ => by rw [cutCountF, remSizeF, sizeF]; omega
  | c :: cs => fun h => by
      have h1 := h c (List.mem_cons_self ..)
      have h2 := cutF_le cs fun d hd => h d (List.mem_cons_of_mem c hd)
      rw [cutCountF, remSizeF, sizeF, Nat.mul_add]
      omega

/-- `s·(number of parts) + (remainder) ≤ |t|`. -/
lemma cut_le (t : RTree) : s * cutCount s t + remSize s t ≤ t.size := by
  induction t using ind with
  | _ cs ih =>
      have hF := cutF_le cs fun c hc => ih c hc
      rw [cutCount, remSize, size]
      split_ifs with h
      · simp only [Nat.mul_add, Nat.mul_one]
        omega
      · simp only [Nat.mul_add, Nat.mul_zero]
        omega

/-- **`it:general-dilution`, the count**: at most `|t|/s` parts are cut off,
so cut and remainder together are at most `|t|/s + 1` parts, each of at most
`1 + J(s-1)` vertices. -/
theorem cutCount_le_div (hs : 1 ≤ s) (t : RTree) : cutCount s t ≤ t.size / s := by
  have h := cut_le (s := s) t
  have h1 : s * cutCount s t ≤ t.size := by omega
  rw [Nat.mul_comm] at h1
  exact (Nat.le_div_iff_mul_le (by omega)).mpr h1

end RTree

end ChainClasses