import Mathlib.Tactic

/-!
`sec:shape-harris` of `matching_classes_simple.tex`: `def:shape`, the shapes
and their realisations.

A shape is a neck length together with a decoration of each interior neck
vertex, and its realisation is the finite rooted tree obtained by attaching the
decorations along a path. Both are combinatorial, so both are defined outright
here; the metric on the realisation, which `sec:shape-net` compares through
marked quasi-isometries, is not.

* `Tri`: finite rooted trees with offspring numbers in `{0,1,2}`, the bushes of
  `def:shape` and the shape realisations. `code` is a prefix-free two-bit code,
  injective by `code_append_inj`, so `Tri` is countable and its trees of a
  given size are few (`Dilution.lean`).
* `Shape`, `Shape.realise`, `Shape.size`: the pair `(m,(b_1,…,b_{m-1}))`, its
  realisation with the entry at the root and the exit at the far end of the
  neck, and the number of vertices. `size_eq` is the count of `def:shape`,
  `m` plus the sizes of the decorations.
* `Countable Shape`: the countability of `𝒮` that makes `rep_D` and the events
  built from it measurable.
* `Tri.del`: the leaf deletion of `thm:shape-connected`, a leaf of a nonempty
  decoration; `eq_of_size_le_one` is the base of that descent. The deletion map
  is a `1`-marked quasi-isometry, which the metric on realisations would state.
-/

namespace ChainClasses

/-- Finite rooted trees with at most two children per vertex: the bushes of
`def:shape` and the realisations of shapes. -/
inductive Tri where
  | leaf : Tri
  | one : Tri → Tri
  | two : Tri → Tri → Tri
  deriving DecidableEq

namespace Tri

/-- The number of vertices. -/
def size : Tri → ℕ
  | leaf => 1
  | one t => 1 + t.size
  | two l r => 1 + l.size + r.size

lemma size_pos (t : Tri) : 0 < t.size := by
  cases t <;> simp [size]

/-- The number of vertices of a decoration, the empty one having none. -/
def optSize : Option Tri → ℕ
  | none => 0
  | some t => t.size

@[simp] lemma optSize_none : optSize none = 0 := rfl

@[simp] lemma optSize_some (t : Tri) : optSize (some t) = t.size := rfl

lemma optSize_eq_fun : optSize = fun b : Option Tri => b.elim 0 Tri.size := by
  funext b; cases b <;> rfl

/-- A root above a possibly empty tree. -/
def graftOne : Option Tri → Tri
  | none => leaf
  | some t => one t

/-- A root above `l` and a possibly empty tree. -/
def graftTwo (l : Tri) : Option Tri → Tri
  | none => one l
  | some r => two l r

/-- Delete one leaf, descending into the last child subtree: `none` for a
single vertex, whose deletion leaves nothing. -/
def del : Tri → Option Tri
  | leaf => none
  | one t => some (graftOne t.del)
  | two l r => some (graftTwo l r.del)

lemma size_graftOne (o : Option Tri) : (graftOne o).size = optSize o + 1 := by
  cases o with
  | none => simp [graftOne, size]
  | some t => simp only [graftOne, optSize_some, size]; omega

lemma size_graftTwo (l : Tri) (o : Option Tri) :
    (graftTwo l o).size = l.size + optSize o + 1 := by
  cases o with
  | none => simp only [graftTwo, optSize_none, size]; omega
  | some r => simp only [graftTwo, optSize_some, size]; omega

/-- Deleting a leaf drops exactly one vertex. -/
lemma optSize_del : ∀ t : Tri, optSize t.del + 1 = t.size
  | leaf => rfl
  | one t => by
      have ih := optSize_del t
      simp only [del, optSize_some, size_graftOne, size]
      omega
  | two l r => by
      have ih := optSize_del r
      simp only [del, optSize_some, size_graftTwo, size]
      omega

/-- A prefix-free code with two bits per vertex: `00` for a leaf, `01` before
the single child, `10` before the two children. -/
def code : Tri → List Bool
  | leaf => [false, false]
  | one t => false :: true :: t.code
  | two l r => true :: false :: (l.code ++ r.code)

lemma code_length (t : Tri) : t.code.length = 2 * t.size := by
  induction t with
  | leaf => rfl
  | one t ih => simp only [code, size, List.length_cons, ih]; omega
  | two l r ihl ihr =>
      simp only [code, size, List.length_cons, List.length_append, ihl, ihr]; omega

/-- The code is prefix-free: a coded tree determines both itself and the rest
of the word. -/
lemma code_append_inj : ∀ (t₁ t₂ : Tri) (u₁ u₂ : List Bool),
    t₁.code ++ u₁ = t₂.code ++ u₂ → t₁ = t₂ ∧ u₁ = u₂ := by
  intro t₁
  induction t₁ with
  | leaf =>
      intro t₂ u₁ u₂ h
      cases t₂ with
      | leaf => simp only [code, List.cons_append, List.nil_append, List.cons.injEq,
          true_and] at h; exact ⟨rfl, h⟩
      | one t => simp [code] at h
      | two l r => simp [code] at h
  | one a iha =>
      intro t₂ u₁ u₂ h
      cases t₂ with
      | leaf => simp [code] at h
      | one b =>
          simp only [code, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨hb, hu⟩ := iha b u₁ u₂ h
          exact ⟨by rw [hb], hu⟩
      | two l r => simp [code] at h
  | two a b iha ihb =>
      intro t₂ u₁ u₂ h
      cases t₂ with
      | leaf => simp [code] at h
      | one t => simp [code] at h
      | two c d =>
          simp only [code, List.cons_append, List.cons.injEq, true_and,
            List.append_assoc] at h
          obtain ⟨hac, h2⟩ := iha c (b.code ++ u₁) (d.code ++ u₂) h
          obtain ⟨hbd, hu⟩ := ihb d u₁ u₂ h2
          exact ⟨by rw [hac, hbd], hu⟩

lemma code_injective : Function.Injective code := by
  intro t₁ t₂ h
  exact (code_append_inj t₁ t₂ [] [] (by rw [h])).1

instance : Countable Tri := code_injective.countable

end Tri

/-- **`def:shape`**: a shape is a neck of `m = necks + 1 ≥ 1` vertices together
with a decoration of each of the `m-1` interior neck vertices, each decoration
empty or a finite tree with offspring numbers in `{0,1,2}`. -/
structure Shape where
  necks : ℕ
  dec : Fin necks → Option Tri

namespace Shape

/-- The neck length `m` of `def:shape`. -/
def neckLen (σ : Shape) : ℕ := σ.necks + 1

/-- The decorations in neck order. -/
def decs (σ : Shape) : List (Option Tri) := List.ofFn σ.dec

/-- The realisation of a decorated neck, read from the exit backwards: a
decorated neck vertex carries its bush and the rest of the neck as its two
children. -/
def realiseAux : List (Option Tri) → Tri
  | [] => Tri.leaf
  | none :: bs => Tri.one (realiseAux bs)
  | some b :: bs => Tri.two b (realiseAux bs)

/-- **`def:shape`**, the realisation: the path `v_1⋯v_m` with the nonempty
decorations attached, rooted at the entry `v_1`, the exit `v_m` being the far
end of the neck. -/
def realise (σ : Shape) : Tri := realiseAux σ.decs

/-- `|σ|`, the number of vertices of the realisation. -/
def size (σ : Shape) : ℕ := σ.realise.size

lemma realiseAux_size : ∀ bs : List (Option Tri),
    (realiseAux bs).size = (bs.length + 1) + (bs.map (fun b => b.elim 0 Tri.size)).sum
  | [] => by simp [realiseAux, Tri.size]
  | none :: bs => by
      simp only [realiseAux, Tri.size, List.length_cons, List.map_cons, List.sum_cons,
        Option.elim, realiseAux_size bs]
      omega
  | some b :: bs => by
      simp only [realiseAux, Tri.size, List.length_cons, List.map_cons, List.sum_cons,
        Option.elim, realiseAux_size bs]
      omega

lemma decs_length (σ : Shape) : σ.decs.length = σ.necks := by
  rw [decs, List.length_ofFn]

/-- **`def:shape`**, the size: `m` neck vertices plus the vertices of the
decorations. -/
lemma size_eq (σ : Shape) :
    σ.size = σ.neckLen + (σ.decs.map (fun b => b.elim 0 Tri.size)).sum := by
  rw [size, realise, realiseAux_size, decs_length, neckLen]

lemma neckLen_pos (σ : Shape) : 0 < σ.neckLen := Nat.succ_pos _

lemma neckLen_le_size (σ : Shape) : σ.neckLen ≤ σ.size := by
  rw [size_eq]; exact Nat.le_add_right _ _

/-- **`def:shape`**, the size in the form the deletion below uses. -/
lemma size_eq' (σ : Shape) : σ.size = σ.neckLen + (σ.decs.map Tri.optSize).sum := by
  rw [size_eq, Tri.optSize_eq_fun]

/-- The shape with the given decorations in neck order. -/
def ofList (l : List (Option Tri)) : Shape := ⟨l.length, l.get⟩

lemma decs_ofList (l : List (Option Tri)) : (ofList l).decs = l := List.ofFn_get l

lemma size_ofList (l : List (Option Tri)) :
    (ofList l).size = (l.length + 1) + (l.map Tri.optSize).sum := by
  rw [size_eq', decs_ofList]; rfl

lemma sum_optSize_replicate (n : ℕ) :
    ((List.replicate n (none : Option Tri)).map Tri.optSize).sum = 0 := by
  induction n with
  | zero => rfl
  | succ n _ => simp [List.replicate_succ]

/-- **`thm:shape-connected`**, the combinatorial half: deleting one leaf of the
realisation of a shape of size at least two, a leaf of a nonempty decoration if
there is one and the exit otherwise, leaves a shape of size one less. -/
lemma necks_eq_zero_of_size_le_one {σ : Shape} (h : σ.size ≤ 1) : σ.necks = 0 := by
  have hs := size_eq' σ
  rw [neckLen] at hs
  omega

/-- **`thm:shape-connected`**, the base of the descent: the one-vertex shape is
the only shape of size one. -/
lemma eq_of_size_le_one {σ τ : Shape} (hσ : σ.size ≤ 1) (hτ : τ.size ≤ 1) : σ = τ := by
  have hσ0 := necks_eq_zero_of_size_le_one hσ
  have hτ0 := necks_eq_zero_of_size_le_one hτ
  obtain ⟨n, f⟩ := σ
  obtain ⟨m, g⟩ := τ
  simp only at hσ0 hτ0
  subst hσ0
  subst hτ0
  simp only [Shape.mk.injEq, heq_eq_eq, true_and]
  funext i
  exact i.elim0

/-- `𝒮` is countable, so `rep_D` and the events built from it are
measurable. -/
instance : Countable Shape := by
  have hinj : Function.Injective
      (fun σ : Shape => (⟨σ.necks, σ.dec⟩ : Σ n : ℕ, Fin n → Option Tri)) := by
    rintro ⟨n, f⟩ ⟨m, g⟩ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    rw [heq_eq_eq] at h2
    rw [h2]
  exact hinj.countable

end Shape

end ChainClasses
