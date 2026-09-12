import Mathlib.Tactic
import ChainClasses.Shape.ContractTree
import ChainClasses.Shape.ShapeShrink

/-!
`thm:shape-shrink` (`it:shape-shrink`) of `gw_classes_simple.tex`: the
two middle moves of the shrinking and the composition that assembles it.

The greedy cut of `Contraction.lean` sends the realisation of a shape onto the
contracted tree by a `2s`-marked quasi-isometry, and `ShapeShrink.lean` sends a
shape into the support of the law by a `2`-marked one.  Between the two the
proof passes through a tree with at most two children per vertex and a marked
vertex.  This module supplies that passage: the binarisation as a tree, and the
neck construction with its metric.

* `triSpace`: a finite tree with a marked vertex as a marked metric space, the
  entry at the root and the exit at the mark.
* `Tri.part_append`, `Tri.urList`, `Tri.childList`: the cut read inside a
  subtree, the vertices of one part and the children of one part.
  `Tri.rawSize_le` counts a part at at most `2s-1` vertices and
  `Tri.length_childList_le_four_mul` its children at at most `4s`, which is
  what bounds the stretch of a path through a vertex the binarisation
  replaces.
* `Tri.binAddr`, `Tri.decode`, `Tri.binList`, `Tri.binOf`: the first move as
  an address map.  A part sits one step into the first-child slot of its
  part-parent and then along the spine of its siblings (`Tri.blk`);
  `Tri.decode_binAddr` reads the address back, so `Tri.binAddr_inj` names each
  part once, `Tri.prefix_mem_binList` makes the addresses prefix-closed and
  `Tri.binOf` is the tree they cut out, of size `Tri.size_binOf_le`.  The two
  distance bounds are `Tri.treeDist_binAddr_le_dist` and
  `Tri.dist_le_treeDist_binAddr`, and `binarisesAt` is the `4s`-marked
  quasi-isometry they give.
* `Tri.markBush`, `Tri.neckList`, `Tri.neckShape`: **the second move**, the
  neck construction.  The root-to-mark path becomes the neck, the subtree
  hanging at a neck vertex becomes its bush, the subtrees hanging at the mark
  are merged through one joint vertex, and a fresh exit is appended below the
  mark.  `Tri.size_neckShape_le` is its size clause.
* `Tri.markMap`, `Tri.neckMap`, `markedQI_neck`: the address map of the second
  move and the `2`-marked, hence `6`-marked, quasi-isometry it carries; the
  map changes every distance by at most one and has `1`-dense image.
* `markedQI_shape_shrink`: **the composition**, `thm:shape-shrink`
  (`it:shape-shrink`) at the constant `2592 s²` and the size bound
  `16(n/s+1)`; `markedQI_shape_shrink_of_le` reads it at the paper's scale
  `s = ⌊√(D/2592)⌋`, which `shrinkScale_sq_le` supplies.
-/

namespace ChainClasses

open Shape (realiseAux)

/-! ### A tree with a marked vertex as a marked space -/

/-- A finite tree with a marked vertex, as a marked metric space: the entry at
the root and the exit at the mark. -/
def triSpace {t : Tri} {e : Word} (he : t.IsAddr e) : MarkedSpace where
  carrier := t.Vert
  entry := ⟨[], t.isAddr_nil⟩
  exit := ⟨e, he⟩

/-- The distance of two vertices of a marked tree. -/
@[simp] lemma dist_triSpace {t : Tri} {e : Word} (he : t.IsAddr e)
    (u v : (triSpace he).carrier) : dist u v = (treeDist u.1 v.1 : ℝ) := rfl

/-- The entry is the root. -/
@[simp] lemma entry_triSpace {t : Tri} {e : Word} (he : t.IsAddr e) :
    (triSpace he).entry.1 = [] := rfl

/-- The exit is the mark. -/
@[simp] lemma exit_triSpace {t : Tri} {e : Word} (he : t.IsAddr e) :
    (triSpace he).exit.1 = e := rfl

namespace Tri

/-! ### The size of a part and the number of its children -/

/-- **`thm:shape-shrink`**: a part of the greedy cut has at most `2s-1`
vertices, each of the at most two children of its root passing up fewer than
`s`. -/
lemma rawSize_le (s : ℕ) (hs : 1 ≤ s) (t : Tri) : rawSize s t ≤ 2 * s - 1 := by
  cases t with
  | leaf => simp only [rawSize]; omega
  | one t =>
      have := remSize_lt s hs t
      simp only [rawSize]; omega
  | two l r =>
      have h1 := remSize_lt s hs l
      have h2 := remSize_lt s hs r
      simp only [rawSize]; omega

/-- The maximal cut vertices of a subtree are at most one more than the
remainder it passes up: a cut root is the only one, and an uncut root passes up
one vertex for each of them. -/
lemma length_cutForest_le (s : ℕ) : ∀ t : Tri, (cutForest s t).length ≤ remSize s t + 1 := by
  intro t
  induction t with
  | leaf =>
      by_cases h : IsCut s (.leaf : Tri)
      · rw [cutForest_leaf, if_pos h]; simp
      · rw [cutForest_leaf, if_neg h]; simp
  | one t ih =>
      by_cases h : IsCut s (.one t)
      · rw [cutForest_one, if_pos h]; simp
      · rw [cutForest_one, if_neg h, remSize_of_not_isCut h]
        simp only [rawSize]
        omega
  | two l r ihl ihr =>
      by_cases h : IsCut s (.two l r)
      · rw [cutForest_two, if_pos h]; simp
      · rw [cutForest_two, if_neg h, remSize_of_not_isCut h]
        simp only [rawSize, List.length_append]
        omega

/-! ### The second move: the neck construction -/

/-- The bush the mark contributes: the subtrees hanging at the mark, merged
through one joint vertex when there are two. -/
def markBush : Tri → Option Tri
  | .leaf => none
  | .one t => some t
  | .two l r => some (.two l r)

@[simp] lemma markBush_leaf : markBush .leaf = none := rfl
@[simp] lemma markBush_one (t : Tri) : markBush (.one t) = some t := rfl
@[simp] lemma markBush_two (l r : Tri) : markBush (.two l r) = some (.two l r) := rfl

/-- **The second move**: the decorations of the shape the neck construction
produces.  Each vertex of the root-to-mark path passes on the subtree hanging
off the path as its bush, the mark passes on its merged subtrees, and the
neck runs one vertex further, to the fresh exit. -/
def neckList : Tri → Word → List (Option Tri)
  | t, [] => [markBush t]
  | .leaf, _ :: _ => [none]
  | .one _, true :: _ => [none]
  | .one t, false :: v => none :: neckList t v
  | .two l r, false :: v => some r :: neckList l v
  | .two l r, true :: v => some l :: neckList r v

@[simp] lemma neckList_nil (t : Tri) : neckList t [] = [markBush t] := by
  cases t <;> rfl

@[simp] lemma neckList_one_false (t : Tri) (v : Word) :
    neckList (.one t) (false :: v) = none :: neckList t v := rfl

@[simp] lemma neckList_one_true (t : Tri) (v : Word) :
    neckList (.one t) (true :: v) = [none] := rfl

@[simp] lemma neckList_two_false (l r : Tri) (v : Word) :
    neckList (.two l r) (false :: v) = some r :: neckList l v := rfl

@[simp] lemma neckList_two_true (l r : Tri) (v : Word) :
    neckList (.two l r) (true :: v) = some l :: neckList r v := rfl

@[simp] lemma neckList_leaf_cons (a : Bool) (v : Word) :
    neckList .leaf (a :: v) = [none] := rfl

/-- **The second move**: the shape the neck construction produces. -/
def neckShape (t : Tri) (e : Word) : Shape := Shape.ofList (neckList t e)

/-- **`thm:shape-shrink` (`it:shape-shrink`), the size of the second
move**: the neck construction adds the fresh exit and at most one joint
vertex. -/
theorem size_realiseAux_neckList : ∀ (t : Tri) (e : Word),
    (realiseAux (neckList t e)).size ≤ t.size + 2 := by
  intro t e
  induction e generalizing t with
  | nil =>
      cases t with
      | leaf => simp only [neckList_nil, markBush_leaf, realiseAux, size]; omega
      | one t => simp only [neckList_nil, markBush_one, realiseAux, size]; omega
      | two l r => simp only [neckList_nil, markBush_two, realiseAux, size]; omega
  | cons a v ih =>
      cases t with
      | leaf => simp only [neckList_leaf_cons, realiseAux, size]; omega
      | one t =>
          cases a with
          | true => simp only [neckList_one_true, realiseAux, size]; have := t.size_pos; omega
          | false =>
              have h := ih t
              simp only [neckList_one_false, realiseAux, size]
              omega
      | two l r =>
          cases a with
          | false =>
              have h := ih l
              simp only [neckList_two_false, realiseAux, size]
              omega
          | true =>
              have h := ih r
              simp only [neckList_two_true, realiseAux, size]
              omega

/-- The same count at the shape. -/
theorem size_neckShape_le (t : Tri) (e : Word) : (neckShape t e).size ≤ t.size + 2 := by
  have h := size_realiseAux_neckList t e
  have hs : (neckShape t e).size = (realiseAux (neckList t e)).size := by
    simp only [neckShape, Shape.size, Shape.realise, Shape.decs_ofList]
  omega

/-! ### The address map of the second move -/

/-- The address map at the mark: the merged subtrees sit in the bush of the
last neck vertex, one step deeper when there are two of them. -/
def markMap : Tri → Word → Word
  | .leaf, _ => []
  | .one _, [] => []
  | .one _, false :: z => false :: z
  | .one _, true :: _ => []
  | .two _ _, [] => []
  | .two _ _, c :: z => false :: c :: z

@[simp] lemma markMap_leaf (w : Word) : markMap .leaf w = [] := rfl
@[simp] lemma markMap_one_nil (t : Tri) : markMap (.one t) [] = [] := rfl
@[simp] lemma markMap_one_false (t : Tri) (z : Word) :
    markMap (.one t) (false :: z) = false :: z := rfl
@[simp] lemma markMap_one_true (t : Tri) (z : Word) : markMap (.one t) (true :: z) = [] := rfl
@[simp] lemma markMap_two_nil (l r : Tri) : markMap (.two l r) [] = [] := rfl
@[simp] lemma markMap_two_cons (l r : Tri) (c : Bool) (z : Word) :
    markMap (.two l r) (c :: z) = false :: c :: z := rfl

/-- **The address map of the second move**: a vertex of the root-to-mark path
keeps its place on the neck, a vertex hanging off the path keeps its place in
the bush, and the subtrees at the mark descend one further step. -/
def neckMap : Tri → Word → Word → Word
  | t, [], w => markMap t w
  | .leaf, _ :: _, _ => []
  | .one _, true :: _, _ => []
  | .one t, false :: v, w =>
      match w with
      | [] => []
      | false :: z => false :: neckMap t v z
      | true :: _ => []
  | .two l _, false :: v, w =>
      match w with
      | [] => []
      | false :: z => true :: neckMap l v z
      | true :: z => false :: z
  | .two _ r, true :: v, w =>
      match w with
      | [] => []
      | false :: z => false :: z
      | true :: z => true :: neckMap r v z

@[simp] lemma neckMap_nil (t : Tri) (w : Word) : neckMap t [] w = markMap t w := by
  cases t <;> rfl

@[simp] lemma neckMap_leaf_cons (a : Bool) (v w : Word) : neckMap .leaf (a :: v) w = [] := rfl

@[simp] lemma neckMap_one_true (t : Tri) (v w : Word) : neckMap (.one t) (true :: v) w = [] := rfl

@[simp] lemma neckMap_one_false_nil (t : Tri) (v : Word) :
    neckMap (.one t) (false :: v) [] = [] := rfl

@[simp] lemma neckMap_one_false_false (t : Tri) (v z : Word) :
    neckMap (.one t) (false :: v) (false :: z) = false :: neckMap t v z := rfl

@[simp] lemma neckMap_one_false_true (t : Tri) (v z : Word) :
    neckMap (.one t) (false :: v) (true :: z) = [] := rfl

@[simp] lemma neckMap_two_false_nil (l r : Tri) (v : Word) :
    neckMap (.two l r) (false :: v) [] = [] := rfl

@[simp] lemma neckMap_two_false_false (l r : Tri) (v z : Word) :
    neckMap (.two l r) (false :: v) (false :: z) = true :: neckMap l v z := rfl

@[simp] lemma neckMap_two_false_true (l r : Tri) (v z : Word) :
    neckMap (.two l r) (false :: v) (true :: z) = false :: z := rfl

@[simp] lemma neckMap_two_true_nil (l r : Tri) (v : Word) :
    neckMap (.two l r) (true :: v) [] = [] := rfl

@[simp] lemma neckMap_two_true_false (l r : Tri) (v z : Word) :
    neckMap (.two l r) (true :: v) (false :: z) = false :: z := rfl

@[simp] lemma neckMap_two_true_true (l r : Tri) (v z : Word) :
    neckMap (.two l r) (true :: v) (true :: z) = true :: neckMap r v z := rfl

/-! ### The address map at the mark -/

/-- The map at the mark deepens by at most one step. -/
lemma length_markMap (t : Tri) {w : Word} (hw : t.IsAddr w) :
    w.length ≤ (markMap t w).length ∧ (markMap t w).length ≤ w.length + 1 := by
  cases t with
  | leaf => rw [eq_nil_of_isAddr_leaf hw]; simp
  | one t =>
      cases w with
      | nil => simp
      | cons a z =>
          cases a with
          | false => simp
          | true => exact absurd hw (isAddr_one_true t z)
  | two l r =>
      cases w with
      | nil => simp
      | cons a z => simp

/-- The map at the mark lands in the realisation of the shape. -/
lemma isAddr_markMap (t : Tri) {w : Word} (hw : t.IsAddr w) :
    (realiseAux [markBush t]).IsAddr (markMap t w) := by
  cases t with
  | leaf => simp [realiseAux]
  | one t =>
      cases w with
      | nil => simp [realiseAux]
      | cons a z =>
          cases a with
          | false => simpa [realiseAux] using hw
          | true => exact absurd hw (isAddr_one_true t z)
  | two l r =>
      cases w with
      | nil => simp [realiseAux]
      | cons a z => simpa [realiseAux] using hw

/-- The map at the mark changes every distance by at most one. -/
lemma markMap_dist_bounds (t : Tri) {u v : Word} (hu : t.IsAddr u) (hv : t.IsAddr v) :
    treeDist (markMap t u) (markMap t v) ≤ treeDist u v + 1 ∧
      treeDist u v ≤ treeDist (markMap t u) (markMap t v) + 1 := by
  cases t with
  | leaf =>
      rw [eq_nil_of_isAddr_leaf hu, eq_nil_of_isAddr_leaf hv]
      simp
  | one t =>
      cases u with
      | nil =>
          cases v with
          | nil => simp
          | cons b z =>
              cases b with
              | false => simp
              | true => exact absurd hv (isAddr_one_true t z)
      | cons a z =>
          cases a with
          | true => exact absurd hu (isAddr_one_true t z)
          | false =>
              cases v with
              | nil => simp
              | cons b z' =>
                  cases b with
                  | false => simp
                  | true => exact absurd hv (isAddr_one_true t z')
  | two l r =>
      cases u with
      | nil =>
          cases v with
          | nil => simp
          | cons b z => simp
      | cons a z =>
          cases v with
          | nil => simp
          | cons b z' => simp

/-- The image of the map at the mark misses only the fresh exit and the joint
vertex, each adjacent to a vertex it hits. -/
lemma dense_markMap (t : Tri) {y : Word} (hy : (realiseAux [markBush t]).IsAddr y) :
    ∃ w, t.IsAddr w ∧ treeDist (markMap t w) y ≤ 1 := by
  cases t with
  | leaf =>
      refine ⟨[], by simp, ?_⟩
      simp only [realiseAux, markBush_leaf] at hy
      cases y with
      | nil => simp
      | cons a z =>
          cases a with
          | false =>
              have hz : z = [] := eq_nil_of_isAddr_leaf (by simpa using hy)
              subst hz
              simp
          | true => exact absurd hy (isAddr_one_true _ z)
  | one t =>
      simp only [realiseAux, markBush_one] at hy
      cases y with
      | nil => exact ⟨[], by simp, by simp⟩
      | cons a z =>
          cases a with
          | false =>
              refine ⟨false :: z, by simpa using hy, ?_⟩
              simp
          | true =>
              have hz : z = [] := eq_nil_of_isAddr_leaf (by simpa using hy)
              subst hz
              exact ⟨[], by simp, by simp⟩
  | two l r =>
      simp only [realiseAux, markBush_two] at hy
      cases y with
      | nil => exact ⟨[], by simp, by simp⟩
      | cons a z =>
          cases a with
          | false =>
              cases z with
              | nil => exact ⟨[], by simp, by simp⟩
              | cons c z' =>
                  refine ⟨c :: z', by simpa using hy, ?_⟩
                  simp
          | true =>
              have hz : z = [] := eq_nil_of_isAddr_leaf (by simpa using hy)
              subst hz
              exact ⟨[], by simp, by simp⟩

/-! ### The address map of the second move, by induction along the neck -/

/-- The neck construction deepens by at most one step. -/
lemma length_neckMap : ∀ (t : Tri) (e w : Word), t.IsAddr e → t.IsAddr w →
    w.length ≤ (neckMap t e w).length ∧ (neckMap t e w).length ≤ w.length + 1 := by
  intro t e
  induction e generalizing t with
  | nil => intro w _ hw; simpa using length_markMap t hw
  | cons a v ih =>
      intro w he hw
      cases t with
      | leaf => exact absurd he (isAddr_leaf_cons a v)
      | one t =>
          cases a with
          | true => exact absurd he (isAddr_one_true t v)
          | false =>
              cases w with
              | nil => simp
              | cons b z =>
                  cases b with
                  | false =>
                      have := ih t z he hw
                      simpa using this
                  | true => exact absurd hw (isAddr_one_true t z)
      | two l r =>
          cases a with
          | false =>
              cases w with
              | nil => simp
              | cons b z =>
                  cases b with
                  | false =>
                      have := ih l z he hw
                      simpa using this
                  | true => simp
          | true =>
              cases w with
              | nil => simp
              | cons b z =>
                  cases b with
                  | false => simp
                  | true =>
                      have := ih r z he hw
                      simpa using this

/-- The neck construction maps addresses to addresses. -/
lemma isAddr_neckMap : ∀ (t : Tri) (e w : Word), t.IsAddr e → t.IsAddr w →
    (realiseAux (neckList t e)).IsAddr (neckMap t e w) := by
  intro t e
  induction e generalizing t with
  | nil => intro w _ hw; simpa using isAddr_markMap t hw
  | cons a v ih =>
      intro w he hw
      cases t with
      | leaf => exact absurd he (isAddr_leaf_cons a v)
      | one t =>
          cases a with
          | true => exact absurd he (isAddr_one_true t v)
          | false =>
              cases w with
              | nil => simp
              | cons b z =>
                  cases b with
                  | false => simpa [realiseAux] using ih t z he hw
                  | true => exact absurd hw (isAddr_one_true t z)
      | two l r =>
          cases a with
          | false =>
              cases w with
              | nil => simp
              | cons b z =>
                  cases b with
                  | false => simpa [realiseAux] using ih l z he hw
                  | true => simpa [realiseAux] using hw
          | true =>
              cases w with
              | nil => simp
              | cons b z =>
                  cases b with
                  | false => simpa [realiseAux] using hw
                  | true => simpa [realiseAux] using ih r z he hw

/-- **The second move is almost an isometry**: the neck construction changes
every distance by at most one, the subtrees at the mark descending one step and
nothing else moving. -/
lemma neckMap_dist_bounds : ∀ (t : Tri) (e x y : Word), t.IsAddr e → t.IsAddr x → t.IsAddr y →
    treeDist (neckMap t e x) (neckMap t e y) ≤ treeDist x y + 1 ∧
      treeDist x y ≤ treeDist (neckMap t e x) (neckMap t e y) + 1 := by
  intro t e
  induction e generalizing t with
  | nil => intro x y _ hx hy; simpa using markMap_dist_bounds t hx hy
  | cons a v ih =>
      intro x y he hx hy
      cases t with
      | leaf => exact absurd he (isAddr_leaf_cons a v)
      | one t =>
          cases a with
          | true => exact absurd he (isAddr_one_true t v)
          | false =>
              cases x with
              | nil =>
                  cases y with
                  | nil => simp
                  | cons b z =>
                      cases b with
                      | false =>
                          have hl := length_neckMap t v z he hy
                          simp only [neckMap_one_false_nil, neckMap_one_false_false,
                            treeDist_nil_left, List.length_cons]
                          omega
                      | true => exact absurd hy (isAddr_one_true t z)
              | cons b z =>
                  cases b with
                  | true => exact absurd hx (isAddr_one_true t z)
                  | false =>
                      cases y with
                      | nil =>
                          have hl := length_neckMap t v z he hx
                          simp only [neckMap_one_false_nil, neckMap_one_false_false,
                            treeDist_nil_right, List.length_cons]
                          omega
                      | cons c z' =>
                          cases c with
                          | true => exact absurd hy (isAddr_one_true t z')
                          | false => simpa using ih t z z' he hx hy
      | two l r =>
          cases a with
          | false =>
              cases x with
              | nil =>
                  cases y with
                  | nil => simp
                  | cons b z =>
                      cases b with
                      | false =>
                          have hl := length_neckMap l v z he hy
                          simp only [neckMap_two_false_nil, neckMap_two_false_false,
                            treeDist_nil_left, List.length_cons]
                          omega
                      | true =>
                          simp only [neckMap_two_false_nil, neckMap_two_false_true,
                            treeDist_nil_left, List.length_cons]
                          omega
              | cons b z =>
                  cases y with
                  | nil =>
                      cases b with
                      | false =>
                          have hl := length_neckMap l v z he hx
                          simp only [neckMap_two_false_nil, neckMap_two_false_false,
                            treeDist_nil_right, List.length_cons]
                          omega
                      | true =>
                          simp only [neckMap_two_false_nil, neckMap_two_false_true,
                            treeDist_nil_right, List.length_cons]
                          omega
                  | cons c z' =>
                      cases b with
                      | false =>
                          cases c with
                          | false => simpa using ih l z z' he hx hy
                          | true =>
                              have hl := length_neckMap l v z he hx
                              simp only [neckMap_two_false_false, neckMap_two_false_true,
                                treeDist_true_false, treeDist_false_true]
                              omega
                      | true =>
                          cases c with
                          | false =>
                              have hl := length_neckMap l v z' he hy
                              simp only [neckMap_two_false_false, neckMap_two_false_true,
                                treeDist_true_false, treeDist_false_true]
                              omega
                          | true =>
                              simp only [neckMap_two_false_true, treeDist_cons_cons_self]
                              omega
          | true =>
              cases x with
              | nil =>
                  cases y with
                  | nil => simp
                  | cons b z =>
                      cases b with
                      | false =>
                          simp only [neckMap_two_true_nil, neckMap_two_true_false,
                            treeDist_nil_left, List.length_cons]
                          omega
                      | true =>
                          have hl := length_neckMap r v z he hy
                          simp only [neckMap_two_true_nil, neckMap_two_true_true,
                            treeDist_nil_left, List.length_cons]
                          omega
              | cons b z =>
                  cases y with
                  | nil =>
                      cases b with
                      | false =>
                          simp only [neckMap_two_true_nil, neckMap_two_true_false,
                            treeDist_nil_right, List.length_cons]
                          omega
                      | true =>
                          have hl := length_neckMap r v z he hx
                          simp only [neckMap_two_true_nil, neckMap_two_true_true,
                            treeDist_nil_right, List.length_cons]
                          omega
                  | cons c z' =>
                      cases b with
                      | false =>
                          cases c with
                          | false =>
                              simp only [neckMap_two_true_false, treeDist_cons_cons_self]
                              omega
                          | true =>
                              have hl := length_neckMap r v z' he hy
                              simp only [neckMap_two_true_false, neckMap_two_true_true,
                                treeDist_false_true]
                              omega
                      | true =>
                          cases c with
                          | false =>
                              have hl := length_neckMap r v z he hx
                              simp only [neckMap_two_true_false, neckMap_two_true_true,
                                treeDist_true_false]
                              omega
                          | true => simpa using ih r z z' he hx hy

/-- The neck construction fixes the root. -/
@[simp] lemma neckMap_root (t : Tri) (e : Word) : neckMap t e [] = [] := by
  cases e with
  | nil => cases t <;> rfl
  | cons a v =>
      cases t with
      | leaf => rfl
      | one t => cases a <;> rfl
      | two l r => cases a <;> rfl

/-- The image of the neck construction misses only the fresh exit and the
joint vertex, each adjacent to a vertex it hits. -/
lemma dense_neckMap : ∀ (t : Tri) (e y : Word), t.IsAddr e →
    (realiseAux (neckList t e)).IsAddr y →
    ∃ w, t.IsAddr w ∧ treeDist (neckMap t e w) y ≤ 1 := by
  intro t e
  induction e generalizing t with
  | nil => intro y _ hy; simpa using dense_markMap t (by simpa using hy)
  | cons a v ih =>
      intro y he hy
      cases t with
      | leaf => exact absurd he (isAddr_leaf_cons a v)
      | one t =>
          cases a with
          | true => exact absurd he (isAddr_one_true t v)
          | false =>
              cases y with
              | nil => exact ⟨[], by simp, by simp⟩
              | cons b z =>
                  cases b with
                  | false =>
                      obtain ⟨w, hw, hd⟩ := ih t z he (by simpa [realiseAux] using hy)
                      exact ⟨false :: w, hw, by simpa using hd⟩
                  | true =>
                      exact absurd hy (by simp [realiseAux])
      | two l r =>
          cases a with
          | false =>
              cases y with
              | nil => exact ⟨[], by simp, by simp⟩
              | cons b z =>
                  cases b with
                  | false =>
                      refine ⟨true :: z, by simpa [realiseAux] using hy, ?_⟩
                      simp
                  | true =>
                      obtain ⟨w, hw, hd⟩ := ih l z he (by simpa [realiseAux] using hy)
                      exact ⟨false :: w, hw, by simpa using hd⟩
          | true =>
              cases y with
              | nil => exact ⟨[], by simp, by simp⟩
              | cons b z =>
                  cases b with
                  | false =>
                      refine ⟨false :: z, by simpa [realiseAux] using hy, ?_⟩
                      simp
                  | true =>
                      obtain ⟨w, hw, hd⟩ := ih r z he (by simpa [realiseAux] using hy)
                      exact ⟨true :: w, hw, by simpa using hd⟩

/-- The mark lands one step above the exit of the shape, the fresh vertex the
neck construction appends. -/
lemma neckMap_exit : ∀ (t : Tri) (e : Word), t.IsAddr e →
    treeDist (neckMap t e e) (Shape.neckAddr (neckList t e)) ≤ 1 := by
  intro t e
  induction e generalizing t with
  | nil => intro _; simp
  | cons a v ih =>
      intro he
      cases t with
      | leaf => exact absurd he (isAddr_leaf_cons a v)
      | one t =>
          cases a with
          | true => exact absurd he (isAddr_one_true t v)
          | false => simpa using ih t he
      | two l r =>
          cases a with
          | false => simpa using ih l he
          | true => simpa using ih r he

end Tri

/-! ### The second move as a marked quasi-isometry -/

/-- **`thm:shape-shrink` (`it:shape-shrink`), the second move**: the
neck construction is a `2`-marked quasi-isometry of a tree with a marked vertex
onto a shape.  It changes every distance by at most one and its image is
`1`-dense. -/
theorem markedQI_neck {t : Tri} {e : Word} (he : t.IsAddr e) :
    MarkedQI 2 (triSpace he) (shapeSpace (Tri.neckShape t e)) := by
  rw [Tri.neckShape, shapeSpace_ofList]
  refine ⟨fun u => ⟨Tri.neckMap t e u.1, Tri.isAddr_neckMap t e u.1 he u.2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    have h := (Tri.neckMap_dist_bounds t e a.1 b.1 he a.2 b.2).1
    have hnat : treeDist (Tri.neckMap t e a.1) (Tri.neckMap t e b.1)
        ≤ 2 * treeDist a.1 b.1 + 2 := by omega
    show ((treeDist (Tri.neckMap t e a.1) (Tri.neckMap t e b.1) : ℕ) : ℝ)
      ≤ 2 * ((treeDist a.1 b.1 : ℕ) : ℝ) + 2
    exact_mod_cast hnat
  · intro a b
    have h := (Tri.neckMap_dist_bounds t e a.1 b.1 he a.2 b.2).2
    have hnat : treeDist a.1 b.1
        ≤ 2 * treeDist (Tri.neckMap t e a.1) (Tri.neckMap t e b.1) + 2 * 2 := by omega
    show ((treeDist a.1 b.1 : ℕ) : ℝ)
      ≤ 2 * ((treeDist (Tri.neckMap t e a.1) (Tri.neckMap t e b.1) : ℕ) : ℝ) + 2 * 2
    exact_mod_cast hnat
  · intro y
    obtain ⟨w, hw, hd⟩ := Tri.dense_neckMap t e y.1 he y.2
    refine ⟨⟨w, hw⟩, ?_⟩
    show ((treeDist (Tri.neckMap t e w) y.1 : ℕ) : ℝ) ≤ 2
    have : treeDist (Tri.neckMap t e w) y.1 ≤ 2 := by omega
    exact_mod_cast this
  · show ((treeDist (Tri.neckMap t e []) [] : ℕ) : ℝ) ≤ 2
    rw [Tri.neckMap_root]
    norm_num
  · have hd := Tri.neckMap_exit t e he
    show ((treeDist (Tri.neckMap t e e) (Shape.neckAddr (Tri.neckList t e)) : ℕ) : ℝ) ≤ 2
    have : treeDist (Tri.neckMap t e e) (Shape.neckAddr (Tri.neckList t e)) ≤ 2 := by omega
    exact_mod_cast this

/-- The same at the paper's scale. -/
theorem markedQI_six_neck {t : Tri} {e : Word} (he : t.IsAddr e) :
    MarkedQI 6 (triSpace he) (shapeSpace (Tri.neckShape t e)) :=
  (markedQI_neck he).mono (by norm_num) (by norm_num)

namespace Tri

variable {s : ℕ}

/-! ### The part of a vertex, read inside a subtree -/

/-- **Locality of the cut.**  The part of `p ++ v` is the part of `v` inside
the subtree at `p`, carried down by `p`, and the part of `p` itself when that
part is the root of the subtree. -/
lemma part_append : ∀ (T : Tri) (p v : Word),
    part s T (p ++ v) =
      if part s (subAt T p) v = [] then part s T p
      else p ++ part s (subAt T p) v := by
  intro T p
  induction p generalizing T with
  | nil =>
      intro v
      simp only [List.nil_append, subAt_nil, part_nil]
      split
      · assumption
      · rfl
  | cons a p ih =>
      intro v
      have hsub : subAt (subAt T [a]) p = subAt T (a :: p) := by
        rw [← subAt_append]; simp
      have hIH := ih (subAt T [a]) v
      rw [hsub] at hIH
      have hcons : (a :: p) ++ v = a :: (p ++ v) := by simp
      rw [hcons, part_cons, hIH]
      by_cases hX : part s (subAt T (a :: p)) v = []
      · simp only [if_pos hX]
        exact (part_cons T a p).symm
      · simp only [if_neg hX]
        have hne : p ++ part s (subAt T (a :: p)) v ≠ [] := by
          intro h
          simp only [List.append_eq_nil_iff] at h
          exact hX h.2
        rw [if_neg hne]
        simp

/-- The part of a vertex below a part root is the part root exactly when the
vertex tops no part of its own inside the subtree. -/
lemma part_append_eq_self_iff {T : Tri} {p : Word} (hp : part s T p = p) (v : Word) :
    part s T (p ++ v) = p ↔ part s (subAt T p) v = [] := by
  rw [part_append, hp]
  constructor
  · intro h
    by_contra hX
    rw [if_neg hX] at h
    have hlen := congrArg List.length h
    simp only [List.length_append] at hlen
    have : part s (subAt T p) v = [] := List.length_eq_zero_iff.mp (by omega)
    exact hX this
  · intro hX
    rw [if_pos hX]

/-! ### The vertices of one part -/

/-- The vertices of the part topped by the root: the root itself, together with
the vertices of the parts of the children the cut does not sever. -/
def urList (s : ℕ) : Tri → List Word
  | .leaf => [[]]
  | .one t => [] :: (if IsCut s t then [] else (urList s t).map (fun w => false :: w))
  | .two l r =>
      [] :: ((if IsCut s l then [] else (urList s l).map (fun w => false :: w)) ++
        (if IsCut s r then [] else (urList s r).map (fun w => true :: w)))

@[simp] lemma urList_leaf : urList s .leaf = [[]] := rfl

@[simp] lemma urList_one (t : Tri) :
    urList s (.one t) =
      [] :: (if IsCut s t then [] else (urList s t).map (fun w => false :: w)) := rfl

@[simp] lemma urList_two (l r : Tri) :
    urList s (.two l r) =
      [] :: ((if IsCut s l then [] else (urList s l).map (fun w => false :: w)) ++
        (if IsCut s r then [] else (urList s r).map (fun w => true :: w))) := rfl

/-- The step rule of `part_cons` collapses to the root exactly when the vertex
tops no part below and the child is not cut. -/
private lemma branch_eq_nil_iff (a : Bool) (X : Word) (c : Prop) [Decidable c] :
    (if X = [] then (if c then [a] else ([] : Word)) else a :: X) = [] ↔ X = [] ∧ ¬ c := by
  by_cases hX : X = []
  · rw [if_pos hX]
    by_cases hc : c <;> simp [hc, hX]
  · rw [if_neg hX]
    simp [hX]

/-- Membership in one branch of the list, with the cut condition read off. -/
private lemma mem_cond_map {c : Prop} [Decidable c] (a b : Bool) (L : List Word) (v : Word) :
    (b :: v) ∈ (if c then ([] : List Word) else L.map (fun w => a :: w))
      ↔ ¬ c ∧ b = a ∧ v ∈ L := by
  by_cases h : c
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]
    simp only [List.mem_map, h, not_false_iff, true_and]
    constructor
    · rintro ⟨w, hw, heq⟩
      simp only [List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨rfl, hw⟩
    · rintro ⟨rfl, hv⟩
      exact ⟨v, hv, rfl⟩

/-- The length of one branch of the list is the remainder the child passes
up. -/
private lemma length_cond_map {c : Prop} [Decidable c] (a : Bool) (L : List Word) (n : ℕ)
    (hL : L.length = n) :
    ((if c then ([] : List Word) else L.map (fun w => a :: w))).length = if c then 0 else n := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; simp
  · rw [if_neg h, if_neg h, List.length_map, hL]

/-- **The size of a part**: the vertices of the part topped by the root are
counted by the remainder the root accumulates. -/
lemma length_urList : ∀ t : Tri, (urList s t).length = rawSize s t := by
  intro t
  induction t with
  | leaf => simp only [urList_leaf, List.length_cons, List.length_nil, rawSize]
  | one t ih =>
      rw [urList_one, rawSize, remSize_eq]
      simp only [List.length_cons, length_cond_map false (urList s t) (rawSize s t) ih]
      omega
  | two l r ihl ihr =>
      rw [urList_two, rawSize, remSize_eq, remSize_eq]
      simp only [List.length_cons, List.length_append,
        length_cond_map false (urList s l) (rawSize s l) ihl,
        length_cond_map true (urList s r) (rawSize s r) ihr]
      omega

/-- **The vertices of one part**, identified: the addresses `urList` lists are
exactly those whose part is the root. -/
lemma mem_urList : ∀ (t : Tri) (v : Word), v ∈ urList s t ↔ t.IsAddr v ∧ part s t v = [] := by
  intro t
  induction t with
  | leaf =>
      intro v
      rw [urList_leaf, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨isAddr_nil _, part_nil _⟩
      · rintro ⟨hv, -⟩; exact eq_nil_of_isAddr_leaf hv
  | one t ih =>
      intro v
      cases v with
      | nil =>
          simp only [urList_one, List.mem_cons, true_or, true_iff]
          exact ⟨isAddr_nil _, part_nil _⟩
      | cons b v =>
          cases b with
          | false =>
              rw [urList_one, part_one_false, isAddr_one_false,
                branch_eq_nil_iff, ← and_assoc, ← ih v]
              simp only [List.mem_cons, mem_cond_map]
              constructor
              · rintro (h | ⟨hc, -, hv⟩)
                · exact absurd h (by simp)
                · exact ⟨hv, hc⟩
              · rintro ⟨hv, hc⟩
                exact Or.inr ⟨hc, trivial, hv⟩
          | true =>
              have hfalse : ¬ ((Tri.one t).IsAddr (true :: v) ∧ part s (Tri.one t) (true :: v) = []) := by
                rintro ⟨hv, -⟩
                exact absurd hv (isAddr_one_true t v)
              have hnot : (true :: v) ∉ urList s (Tri.one t) := by
                rw [urList_one]
                simp only [List.mem_cons, mem_cond_map]
                rintro (h | ⟨-, h, -⟩)
                · exact absurd h (by simp)
                · exact absurd h (by simp)
              exact iff_of_false hnot hfalse
  | two l r ihl ihr =>
      intro v
      cases v with
      | nil =>
          simp only [urList_two, List.mem_cons, true_or, true_iff]
          exact ⟨isAddr_nil _, part_nil _⟩
      | cons b v =>
          cases b with
          | false =>
              rw [urList_two, part_two_false, isAddr_two_false, branch_eq_nil_iff,
                ← and_assoc, ← ihl v]
              simp only [List.mem_cons, List.mem_append, mem_cond_map]
              constructor
              · rintro (h | ⟨hc, -, hv⟩ | ⟨-, h, -⟩)
                · exact absurd h (by simp)
                · exact ⟨hv, hc⟩
                · exact absurd h (by simp)
              · rintro ⟨hv, hc⟩
                exact Or.inr (Or.inl ⟨hc, trivial, hv⟩)
          | true =>
              rw [urList_two, part_two_true, isAddr_two_true, branch_eq_nil_iff,
                ← and_assoc, ← ihr v]
              simp only [List.mem_cons, List.mem_append, mem_cond_map]
              constructor
              · rintro (h | ⟨-, h, -⟩ | ⟨hc, -, hv⟩)
                · exact absurd h (by simp)
                · exact absurd h (by simp)
                · exact ⟨hv, hc⟩
              · rintro ⟨hv, hc⟩
                exact Or.inr (Or.inr ⟨hc, trivial, hv⟩)

/-! ### The children of a part -/

/-- The part roots whose part-parent is `p`, in the order `partList` reads
them: the children of `p` in the contraction. -/
def childList (s : ℕ) (T : Tri) (p : Word) : List Word :=
  (partList s T).filter (fun q => decide (q ≠ [] ∧ part s T q.dropLast = p))

lemma mem_childList {T : Tri} {p q : Word} :
    q ∈ childList s T p ↔
      (T.IsAddr q ∧ part s T q = q) ∧ q ≠ [] ∧ part s T q.dropLast = p := by
  rw [childList, List.mem_filter, mem_partList_iff]
  simp

/-- The children of a part are listed once each. -/
lemma nodup_childList (T : Tri) (p : Word) : (childList s T p).Nodup :=
  (nodup_partList T).filter _

/-- Every child of `p` is a vertex of the part of `p` with one more letter, so
the children inject into the vertices of that part paired with a letter. -/
lemma childList_subset {T : Tri} {p : Word} (hp : part s T p = p) :
    childList s T p ⊆
      (urList s (subAt T p)).map (fun v => p ++ v ++ [false]) ++
        (urList s (subAt T p)).map (fun v => p ++ v ++ [true]) := by
  intro q hq
  rw [mem_childList] at hq
  obtain ⟨⟨hqaddr, -⟩, hqne, hqp⟩ := hq
  obtain ⟨u, a, hua⟩ : ∃ (u : Word) (a : Bool), q = u ++ [a] := by
    rcases List.eq_nil_or_concat q with h | ⟨u, a, hu⟩
    · exact absurd h hqne
    · exact ⟨u, a, by rw [hu]; simp⟩
  subst hua
  have hu : part s T u = p := by simpa using hqp
  have hpu : p <+: u := hu ▸ part_prefix T u
  obtain ⟨v, rfl⟩ := hpu
  have haddr : T.IsAddr (p ++ v) :=
    T.isAddr_of_prefix (List.prefix_append (p ++ v) [a]) hqaddr
  have hv : part s (subAt T p) v = [] := (part_append_eq_self_iff hp v).mp hu
  have hmem : v ∈ urList s (subAt T p) := (mem_urList _ v).mpr ⟨isAddr_subAt T p v haddr, hv⟩
  cases a with
  | false => exact List.mem_append_left _ (List.mem_map_of_mem hmem)
  | true => exact List.mem_append_right _ (List.mem_map_of_mem hmem)

/-- **The branching of the contraction**: a part has at most `2` children for
each of its vertices. -/
lemma length_childList_le {T : Tri} {p : Word} (hp : part s T p = p) :
    (childList s T p).length ≤ 2 * rawSize s (subAt T p) := by
  have hle : (childList s T p).length ≤
      ((urList s (subAt T p)).map (fun v => p ++ v ++ [false]) ++
        (urList s (subAt T p)).map (fun v => p ++ v ++ [true])).length :=
    (List.subperm_of_subset (nodup_childList T p) (childList_subset hp)).length_le
  rw [List.length_append, List.length_map, List.length_map, length_urList] at hle
  omega

/-- **`thm:shape-shrink`, the branching of the contraction**: a part has at
most `4s` children, its at most `2s-1` vertices carrying at most two each.
This is what bounds the stretch of a path through a vertex the binarisation
replaces. -/
theorem length_childList_le_four_mul (hs : 1 ≤ s) {T : Tri} {p : Word}
    (hp : part s T p = p) : (childList s T p).length ≤ 4 * s := by
  have h1 := length_childList_le (s := s) hp
  have h2 := rawSize_le s hs (subAt T p)
  omega

/-! ### The address of a part in the binarised tree -/

/-- The part-parent of a part root: the part of its parent in the ambient
tree. -/
def pparent (s : ℕ) (T : Tri) (q : Word) : Word := part s T q.dropLast

/-- The place of a part among the children of its part-parent. -/
def childIdx (s : ℕ) (T : Tri) (q : Word) : ℕ := (childList s T (pparent s T q)).idxOf q

/-- One block of a binarised address: the step into the first-child slot,
followed by one step along the spine of siblings for each place the child sits
from the front. -/
def blk (i : ℕ) : Word := false :: List.replicate i true

@[simp] lemma length_blk (i : ℕ) : (blk i).length = i + 1 := by simp [blk]

/-- The prefixes of one block: the empty word and the shorter blocks. -/
lemma prefix_blk_iff {x : Word} {i : ℕ} : x <+: blk i ↔ x = [] ∨ ∃ j ≤ i, x = blk j := by
  constructor
  · intro h
    cases x with
    | nil => exact Or.inl rfl
    | cons a x =>
        rw [blk, List.cons_prefix_cons] at h
        obtain ⟨rfl, hx⟩ := h
        have hall : ∀ b ∈ x, b = true := fun b hb => List.eq_of_mem_replicate (hx.subset hb)
        have hxr : x = List.replicate x.length true := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
        have hlen : x.length ≤ i := by simpa using hx.length_le
        exact Or.inr ⟨x.length, hlen, by rw [blk, ← hxr]⟩
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact List.nil_prefix
    · rw [blk, blk, List.cons_prefix_cons]
      refine ⟨rfl, ⟨List.replicate (i - j) true, ?_⟩⟩
      rw [← List.replicate_add]
      congr 1
      omega

/-- **The address of a part in the binarised tree**: the root part sits at the
root, and every other part one step into the first-child slot of its
part-parent, then along the spine of siblings to its own place. -/
def binAddr (s : ℕ) (T : Tri) (q : Word) : Word :=
  if _hq : q = [] then [] else binAddr s T (pparent s T q) ++ blk (childIdx s T q)
termination_by q.length
decreasing_by
  have h1 : (part s T q.dropLast).length ≤ q.dropLast.length := length_part_le T q.dropLast
  have h2 : q.dropLast.length = q.length - 1 := List.length_dropLast
  have h3 : q.length ≠ 0 := fun h => _hq (List.length_eq_zero_iff.mp h)
  simp only [pparent]
  omega

@[simp] lemma binAddr_nil (T : Tri) : binAddr s T [] = [] := by rw [binAddr]; simp

lemma binAddr_of_ne_nil {T : Tri} {q : Word} (hq : q ≠ []) :
    binAddr s T q = binAddr s T (pparent s T q) ++ blk (childIdx s T q) := by
  rw [binAddr, dif_neg hq]

/-- A part root other than the root is one of the children of its
part-parent. -/
lemma mem_childList_pparent {T : Tri} {q : Word} (hq : T.IsAddr q) (hpq : part s T q = q)
    (hne : q ≠ []) : q ∈ childList s T (pparent s T q) :=
  mem_childList.mpr ⟨⟨hq, hpq⟩, hne, rfl⟩

/-- The children of a part carry the places `0, 1, …` in order. -/
lemma binAddr_getElem {T : Tri} {p : Word} {j : ℕ}
    (hj : j < (childList s T p).length) :
    binAddr s T (childList s T p)[j] = binAddr s T p ++ blk j := by
  have hmem : (childList s T p)[j] ∈ childList s T p := List.getElem_mem hj
  have hpar : pparent s T (childList s T p)[j] = p := (mem_childList.mp hmem).2.2
  have hne : (childList s T p)[j] ≠ [] := (mem_childList.mp hmem).2.1
  have hidx : childIdx s T (childList s T p)[j] = j := by
    rw [childIdx, hpar]
    exact (nodup_childList T p).idxOf_getElem j hj
  rw [binAddr_of_ne_nil hne, hpar, hidx]

/-- The part-parent of a part root sits strictly higher in the ambient tree. -/
lemma length_pparent_lt {T : Tri} {q : Word} (hq : q ≠ []) :
    (pparent s T q).length < q.length := by
  have h1 : (part s T q.dropLast).length ≤ q.dropLast.length := length_part_le T q.dropLast
  have h2 : q.dropLast.length = q.length - 1 := List.length_dropLast
  have h3 : q.length ≠ 0 := fun h => hq (List.length_eq_zero_iff.mp h)
  simp only [pparent]
  omega

/-! ### Reading a binarised address back -/

/-- The step into the first-child slot: the first child of a part, the part
itself when it has none. -/
def stepChild (s : ℕ) (T : Tri) (p : Word) : Word := (childList s T p).getD 0 p

/-- The step along the spine of siblings: the next child of the part-parent,
the part itself when there is none. -/
def stepSib (s : ℕ) (T : Tri) (q : Word) : Word :=
  (childList s T (pparent s T q)).getD (childIdx s T q + 1) q

/-- **Reading a binarised address back**: `false` steps into the first-child
slot and `true` steps along the spine of siblings. -/
def decode (s : ℕ) (T : Tri) (p : Word) : Word → Word
  | [] => p
  | false :: rest => decode s T (stepChild s T p) rest
  | true :: rest => decode s T (stepSib s T p) rest

@[simp] lemma decode_nil (T : Tri) (p : Word) : decode s T p [] = p := rfl

@[simp] lemma decode_false (T : Tri) (p : Word) (rest : Word) :
    decode s T p (false :: rest) = decode s T (stepChild s T p) rest := rfl

@[simp] lemma decode_true (T : Tri) (p : Word) (rest : Word) :
    decode s T p (true :: rest) = decode s T (stepSib s T p) rest := rfl

lemma decode_append (T : Tri) (p : Word) : ∀ u v : Word,
    decode s T p (u ++ v) = decode s T (decode s T p u) v := by
  intro u
  induction u generalizing p with
  | nil => intro v; simp
  | cons a u ih => intro v; cases a <;> simp [ih]

/-- Reading an index off the list of children, when it is in range. -/
private lemma getD_of_lt {L : List Word} {n : ℕ} (h : n < L.length) (a : Word) :
    L.getD n a = L[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The place of a part, unfolded. -/
lemma childIdx_eq (T : Tri) (q : Word) :
    childIdx s T q = (childList s T (pparent s T q)).idxOf q := rfl

/-- A child names its part-parent. -/
lemma pparent_of_mem_childList {T : Tri} {p q : Word} (h : q ∈ childList s T p) :
    pparent s T q = p := (mem_childList.mp h).2.2

/-- The part-parent of the `j`-th child is the part. -/
lemma pparent_getD {T : Tri} {p : Word} {j : ℕ} (h : j < (childList s T p).length) :
    pparent s T ((childList s T p).getD j p) = p := by
  rw [getD_of_lt h]
  exact pparent_of_mem_childList (List.getElem_mem h)

/-- The `j`-th child carries the place `j`. -/
lemma childIdx_getD {T : Tri} {p : Word} {j : ℕ} (h : j < (childList s T p).length) :
    childIdx s T ((childList s T p).getD j p) = j := by
  rw [getD_of_lt h, childIdx_eq, pparent_of_mem_childList (List.getElem_mem h)]
  exact (nodup_childList T p).idxOf_getElem j h

/-- One step along the spine of siblings moves to the next child. -/
lemma stepSib_getD {T : Tri} {p : Word} {j : ℕ} (h : j + 1 < (childList s T p).length) :
    stepSib s T ((childList s T p).getD j p) = (childList s T p).getD (j + 1) p := by
  have hj : j < (childList s T p).length := by omega
  rw [stepSib, pparent_getD hj, childIdx_getD hj, getD_of_lt h, getD_of_lt h]

/-- Walking along the spine of siblings from the `j`-th child reaches the
`(j+i)`-th. -/
lemma decode_replicate_true {T : Tri} {p : Word} : ∀ (i j : ℕ),
    j + i < (childList s T p).length →
    decode s T ((childList s T p).getD j p) (List.replicate i true)
      = (childList s T p).getD (j + i) p := by
  intro i
  induction i with
  | zero => intro j h; simp
  | succ i ih =>
      intro j h
      rw [List.replicate_succ, decode_true, stepSib_getD (by omega), ih (j + 1) (by omega)]
      congr 1
      omega

/-- **The address determines the part**: reading a binarised address back
returns the part it names. -/
lemma decode_binAddr {T : Tri} : ∀ (n : ℕ) (q : Word), q.length ≤ n → T.IsAddr q →
    part s T q = q → decode s T [] (binAddr s T q) = q := by
  intro n
  induction n with
  | zero =>
      intro q hq _ _
      have : q = [] := List.length_eq_zero_iff.mp (by omega)
      subst this
      simp
  | succ n ih =>
      intro q hq hqa hqp
      by_cases hne : q = []
      · subst hne; simp
      · have hlen := length_pparent_lt (s := s) (T := T) hne
        have hpa : T.IsAddr (pparent s T q) :=
          T.isAddr_of_prefix (part_prefix T q.dropLast)
            (T.isAddr_of_prefix q.dropLast_prefix hqa)
        have hpp : part s T (pparent s T q) = pparent s T q := part_idem T _
        have hmem : q ∈ childList s T (pparent s T q) := mem_childList_pparent hqa hqp hne
        have hi : childIdx s T q < (childList s T (pparent s T q)).length :=
          List.idxOf_lt_length_of_mem hmem
        have hget : (childList s T (pparent s T q)).getD (childIdx s T q) (pparent s T q) = q := by
          rw [getD_of_lt hi]
          exact List.getElem_idxOf hi
        rw [binAddr_of_ne_nil hne, decode_append, ih _ (by omega) hpa hpp, blk, decode_false,
          stepChild, decode_replicate_true (childIdx s T q) 0 (by omega), Nat.zero_add, hget]

/-- **The binarised address is a faithful name for the part.** -/
lemma binAddr_inj {T : Tri} {q q' : Word} (hqa : T.IsAddr q) (hqp : part s T q = q)
    (hq'a : T.IsAddr q') (hq'p : part s T q' = q') (h : binAddr s T q = binAddr s T q') :
    q = q' := by
  have h1 := decode_binAddr (s := s) (T := T) q.length q le_rfl hqa hqp
  have h2 := decode_binAddr (s := s) (T := T) q'.length q' le_rfl hq'a hq'p
  rw [← h1, ← h2, h]

/-! ### The binarised addresses -/

/-- The addresses the parts occupy in the binarised tree. -/
def binList (s : ℕ) (T : Tri) : List Word := (partList s T).map (binAddr s T)

lemma mem_binList {T : Tri} {q : Word} (hq : T.IsAddr q) (hp : part s T q = q) :
    binAddr s T q ∈ binList s T :=
  List.mem_map_of_mem ((mem_partList_iff T).mpr ⟨hq, hp⟩)

lemma exists_of_mem_binList {T : Tri} {x : Word} (hx : x ∈ binList s T) :
    ∃ q, T.IsAddr q ∧ part s T q = q ∧ binAddr s T q = x := by
  rw [binList, List.mem_map] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  exact ⟨q, ((mem_partList_iff T).mp hq).1, ((mem_partList_iff T).mp hq).2, rfl⟩

/-- Cancelling a common head from a prefix relation. -/
private lemma append_prefix_cancel {a y w : Word} (h : a ++ y <+: a ++ w) : y <+: w := by
  obtain ⟨t, ht⟩ := h
  rw [List.append_assoc] at ht
  exact ⟨t, List.append_cancel_left ht⟩

/-- **The binarised addresses are prefix-closed**: every prefix of the address
of a part is the address of a part, namely of an ancestor or of an earlier
sibling of one. -/
lemma prefix_mem_binList {T : Tri} : ∀ (n : ℕ) (q : Word), q.length ≤ n → T.IsAddr q →
    part s T q = q → ∀ y, y <+: binAddr s T q → y ∈ binList s T := by
  have hroot : ([] : Word) ∈ binList s T := by
    have := mem_binList (s := s) (T := T) (q := []) (isAddr_nil T) (part_nil T)
    rwa [binAddr_nil] at this
  intro n
  induction n with
  | zero =>
      intro q hq _ _ y hy
      have : q = [] := List.length_eq_zero_iff.mp (by omega)
      subst this
      rw [binAddr_nil, List.prefix_nil] at hy
      subst hy
      exact hroot
  | succ n ih =>
      intro q hq hqa hqp y hy
      by_cases hne : q = []
      · subst hne
        rw [binAddr_nil, List.prefix_nil] at hy
        subst hy
        exact hroot
      · have hlen := length_pparent_lt (s := s) (T := T) hne
        have hpa : T.IsAddr (pparent s T q) :=
          T.isAddr_of_prefix (part_prefix T q.dropLast)
            (T.isAddr_of_prefix q.dropLast_prefix hqa)
        have hpp : part s T (pparent s T q) = pparent s T q := part_idem T _
        have hmem : q ∈ childList s T (pparent s T q) := mem_childList_pparent hqa hqp hne
        have hi : childIdx s T q < (childList s T (pparent s T q)).length :=
          List.idxOf_lt_length_of_mem hmem
        have hsplit := binAddr_of_ne_nil (s := s) (T := T) hne
        rw [hsplit] at hy
        have hpref : binAddr s T (pparent s T q) <+: binAddr s T (pparent s T q) ++
            blk (childIdx s T q) := List.prefix_append _ _
        rcases le_or_gt y.length (binAddr s T (pparent s T q)).length with hle | hgt
        · exact ih _ (by omega) hpa hpp y (prefix_of_prefix_of_length_le hy hpref hle)
        · obtain ⟨z, rfl⟩ : binAddr s T (pparent s T q) <+: y :=
            prefix_of_prefix_of_length_le hpref hy (by omega)
          have hz : z <+: blk (childIdx s T q) := append_prefix_cancel hy
          rcases prefix_blk_iff.mp hz with rfl | ⟨j, hj, rfl⟩
          · simpa using ih _ (by omega) hpa hpp _ (List.prefix_refl _)
          · have hjlt : j < (childList s T (pparent s T q)).length := by omega
            have hgetmem : (childList s T (pparent s T q))[j] ∈
                childList s T (pparent s T q) := List.getElem_mem hjlt
            have hc := mem_childList.mp hgetmem
            have := mem_binList (s := s) hc.1.1 hc.1.2
            rwa [binAddr_getElem hjlt] at this

/-- A part is joined to its part-parent by an edge of the contraction. -/
lemma adj_of_pparent_eq {T : Tri} {p q : PartVert s T} (hne : q.1 ≠ [])
    (h : pparent s T q.1 = p.1) : (partGraph s T).Adj p q := by
  obtain ⟨u, a, hua⟩ : ∃ (u : Word) (a : Bool), q.1 = u ++ [a] := by
    rcases List.eq_nil_or_concat q.1 with h' | ⟨u, a, hu⟩
    · exact absurd h' hne
    · exact ⟨u, a, by rw [hu]; simp⟩
  refine Or.inl ⟨u, a, hua, ?_⟩
  rw [← h]
  simp only [pparent, hua, List.dropLast_concat]

/-- Two parts joined by an edge are at distance one. -/
private lemma dist_le_one_of_adj {T : Tri} {p q : PartVert s T}
    (h : (partGraph s T).Adj p q) : (partGraph s T).dist p q ≤ 1 :=
  SimpleGraph.dist_le (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)

/-- **The lower bound of the binarisation**: if the address of one part is a
prefix of the address of another, the two parts are at most twice their
difference in depth apart in the contraction. -/
lemma dist_le_of_binAddr_prefix {T : Tri} : ∀ (n : ℕ) (x m : PartVert s T), x.1.length ≤ n →
    binAddr s T m.1 <+: binAddr s T x.1 →
    (partGraph s T).dist m x ≤ 2 * ((binAddr s T x.1).length - (binAddr s T m.1).length) := by
  have base : ∀ (x m : PartVert s T), x.1 = [] → binAddr s T m.1 <+: binAddr s T x.1 →
      (partGraph s T).dist m x ≤ 2 * ((binAddr s T x.1).length - (binAddr s T m.1).length) := by
    intro x m hx0 hpre
    have hxb : binAddr s T x.1 = [] := by rw [hx0, binAddr_nil]
    rw [hxb, List.prefix_nil] at hpre
    have hm0 : m.1 = x.1 := binAddr_inj m.2.1 m.2.2 x.2.1 x.2.2 (by rw [hpre, hxb])
    rw [Subtype.ext hm0]
    simp
  intro n
  induction n with
  | zero =>
      intro x m hx hpre
      exact base x m (List.length_eq_zero_iff.mp (by omega)) hpre
  | succ n ih =>
      intro x m hx hpre
      by_cases hne : x.1 = []
      · exact base x m hne hpre
      · have hpa : T.IsAddr (pparent s T x.1) :=
          T.isAddr_of_prefix (part_prefix T x.1.dropLast)
            (T.isAddr_of_prefix x.1.dropLast_prefix x.2.1)
        have hpp : part s T (pparent s T x.1) = pparent s T x.1 := part_idem T _
        obtain ⟨p, hp1⟩ : ∃ p : PartVert s T, p.1 = pparent s T x.1 := ⟨⟨_, hpa, hpp⟩, rfl⟩
        have hplen : p.1.length ≤ n := by
          have := length_pparent_lt (s := s) (T := T) hne
          rw [hp1]
          omega
        have hmem : x.1 ∈ childList s T p.1 := by
          rw [hp1]
          exact mem_childList_pparent x.2.1 x.2.2 hne
        have hi : childIdx s T x.1 < (childList s T p.1).length :=
          by rw [hp1]; exact List.idxOf_lt_length_of_mem (by rw [← hp1]; exact hmem)
        have hsplit : binAddr s T x.1 = binAddr s T p.1 ++ blk (childIdx s T x.1) := by
          rw [hp1]; exact binAddr_of_ne_nil hne
        have hxlen : (binAddr s T x.1).length
            = (binAddr s T p.1).length + childIdx s T x.1 + 1 := by
          rw [hsplit]; simp; omega
        have hadj : (partGraph s T).Adj p x := adj_of_pparent_eq hne hp1.symm
        have hdadj := dist_le_one_of_adj hadj
        have htri := (partGraph_connected (s := s) (T := T)).dist_triangle
          (u := m) (v := p) (w := x)
        rcases le_or_gt (binAddr s T m.1).length (binAddr s T p.1).length with hle | hgt
        · have hmp' : binAddr s T m.1 <+: binAddr s T p.1 :=
            prefix_of_prefix_of_length_le hpre (hsplit ▸ List.prefix_append _ _) hle
          have hih := ih p m hplen hmp'
          omega
        · rw [hsplit] at hpre
          obtain ⟨z, hz⟩ : binAddr s T p.1 <+: binAddr s T m.1 :=
            prefix_of_prefix_of_length_le (List.prefix_append _ _) hpre (by omega)
          rw [← hz] at hpre
          have hzb : z <+: blk (childIdx s T x.1) := append_prefix_cancel hpre
          rcases prefix_blk_iff.mp hzb with hznil | ⟨j, hj, hzj⟩
          · exfalso
            rw [hznil] at hz
            simp only [List.append_nil] at hz
            rw [← hz] at hgt
            omega
          · have hjlt : j < (childList s T p.1).length := by omega
            have hgetmem : (childList s T p.1)[j] ∈ childList s T p.1 := List.getElem_mem hjlt
            have hc := mem_childList.mp hgetmem
            have hmb : binAddr s T m.1 = binAddr s T (childList s T p.1)[j] := by
              rw [binAddr_getElem hjlt, ← hz, hzj]
            have hmeq : m.1 = (childList s T p.1)[j] :=
              binAddr_inj m.2.1 m.2.2 hc.1.1 hc.1.2 hmb
            have hmlen : (binAddr s T m.1).length = (binAddr s T p.1).length + j + 1 := by
              rw [← hz, hzj]; simp; omega
            rcases eq_or_lt_of_le hj with hje | hjlt'
            · have hidx : childIdx s T x.1 = (childList s T p.1).idxOf x.1 := by
                rw [childIdx_eq, ← hp1]
              have hget : (childList s T p.1).getD (childIdx s T x.1) x.1 = x.1 := by
                rw [hidx, getD_of_lt (hidx ▸ hi)]
                exact List.getElem_idxOf (hidx ▸ hi)
              have hxeq : x.1 = (childList s T p.1)[j] := by
                rw [← getD_of_lt hjlt x.1, hje, hget]
              rw [Subtype.ext (hmeq.trans hxeq.symm)]
              simp
            · have hpar : pparent s T m.1 = p.1 := by
                rw [hmeq]; exact pparent_of_mem_childList hgetmem
              have hadjm : (partGraph s T).Adj p m :=
                adj_of_pparent_eq (by rw [hmeq]; exact hc.2.1) hpar
              have hdm := dist_le_one_of_adj hadjm
              rw [SimpleGraph.dist_comm] at hdm
              omega

/-- **The upper bound of the binarisation**: one edge of the contraction spans
at most `4s` edges of the binarised tree, a part having at most `4s`
children. -/
lemma treeDist_binAddr_le_of_adj (hs : 1 ≤ s) {T : Tri} {p q : PartVert s T}
    (h : (partGraph s T).Adj p q) :
    treeDist (binAddr s T p.1) (binAddr s T q.1) ≤ 4 * s := by
  have key : ∀ {p q : PartVert s T}, PartStep p q →
      treeDist (binAddr s T p.1) (binAddr s T q.1) ≤ 4 * s := by
    rintro p q ⟨u, a, h1, h2⟩
    have hne : q.1 ≠ [] := by rw [h1]; simp
    have hpar : pparent s T q.1 = p.1 := by
      rw [pparent, h1, List.dropLast_concat]
      exact h2.symm
    have hsplit : binAddr s T q.1 = binAddr s T p.1 ++ blk (childIdx s T q.1) := by
      rw [binAddr_of_ne_nil hne, hpar]
    have hpref : binAddr s T p.1 <+: binAddr s T q.1 := hsplit ▸ List.prefix_append _ _
    have hmem : q.1 ∈ childList s T p.1 := by
      rw [← hpar]; exact mem_childList_pparent q.2.1 q.2.2 hne
    have hi : childIdx s T q.1 < (childList s T p.1).length := by
      rw [childIdx_eq, hpar]; exact List.idxOf_lt_length_of_mem hmem
    have hcount := length_childList_le_four_mul (s := s) hs (T := T) (p := p.1) p.2.2
    rw [treeDist_of_prefix hpref, hsplit]
    simp only [List.length_append, length_blk]
    omega
  rcases h with h | h
  · exact key h
  · rw [treeDist_comm]; exact key h

lemma treeDist_binAddr_le_walk (hs : 1 ≤ s) {T : Tri} {p q : PartVert s T}
    (w : (partGraph s T).Walk p q) :
    treeDist (binAddr s T p.1) (binAddr s T q.1) ≤ 4 * s * w.length := by
  induction w with
  | nil => simp
  | @cons a b c hab _ ih =>
      have h1 := treeDist_binAddr_le_of_adj hs hab
      have h2 := treeDist_triangle (binAddr s T a.1) (binAddr s T b.1) (binAddr s T c.1)
      simp only [SimpleGraph.Walk.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- **The upper bound**, along a geodesic of the contraction. -/
lemma treeDist_binAddr_le_dist (hs : 1 ≤ s) {T : Tri} (p q : PartVert s T) :
    treeDist (binAddr s T p.1) (binAddr s T q.1) ≤ 4 * s * (partGraph s T).dist p q := by
  obtain ⟨w, hw⟩ := ((partGraph_connected (s := s) (T := T)) p q).exists_walk_length_eq_dist
  have h := treeDist_binAddr_le_walk hs w
  rwa [hw] at h

/-- **The lower bound**, through the wedge: the meet of two binarised addresses
is again the address of a part, and each of the two parts climbs to it. -/
lemma dist_le_treeDist_binAddr {T : Tri} (p q : PartVert s T) :
    (partGraph s T).dist p q ≤ 2 * treeDist (binAddr s T p.1) (binAddr s T q.1) := by
  have hwp := wedge_prefix_left (binAddr s T p.1) (binAddr s T q.1)
  have hwq := wedge_prefix_right (binAddr s T p.1) (binAddr s T q.1)
  have hw : wedge (binAddr s T p.1) (binAddr s T q.1) ∈ binList s T :=
    prefix_mem_binList _ p.1 le_rfl p.2.1 p.2.2 _ hwp
  obtain ⟨m, hma, hmp, hm⟩ := exists_of_mem_binList hw
  have hmv : (⟨m, hma, hmp⟩ : PartVert s T).1 = m := rfl
  have h1 := dist_le_of_binAddr_prefix (s := s) (T := T) p.1.length p ⟨m, hma, hmp⟩ le_rfl
    (by rw [hmv, hm]; exact hwp)
  have h2 := dist_le_of_binAddr_prefix (s := s) (T := T) q.1.length q ⟨m, hma, hmp⟩ le_rfl
    (by rw [hmv, hm]; exact hwq)
  have htri := (partGraph_connected (s := s) (T := T)).dist_triangle
    (u := p) (v := (⟨m, hma, hmp⟩ : PartVert s T)) (w := q)
  rw [SimpleGraph.dist_comm] at h1
  have hlen : treeDist (binAddr s T p.1) (binAddr s T q.1)
      + 2 * (wedge (binAddr s T p.1) (binAddr s T q.1)).length
      = (binAddr s T p.1).length + (binAddr s T q.1).length :=
    treeDist_add_wedge_length _ _
  have hle1 := hwp.length_le
  have hle2 := hwq.length_le
  rw [hmv, hm] at h1 h2
  omega

/-! ### The addresses of a tree, as a list -/

/-- The addresses of a tree, in the order the tree is read. -/
def addrList : Tri → List Word
  | .leaf => [[]]
  | .one t => [] :: (addrList t).map (fun w => false :: w)
  | .two l r =>
      [] :: ((addrList l).map (fun w => false :: w) ++ (addrList r).map (fun w => true :: w))

@[simp] lemma addrList_leaf : addrList .leaf = [[]] := rfl

@[simp] lemma addrList_one (t : Tri) :
    addrList (.one t) = [] :: (addrList t).map (fun w => false :: w) := rfl

@[simp] lemma addrList_two (l r : Tri) :
    addrList (.two l r) =
      [] :: ((addrList l).map (fun w => false :: w) ++
        (addrList r).map (fun w => true :: w)) := rfl

lemma length_addrList : ∀ t : Tri, (addrList t).length = t.size := by
  intro t
  induction t with
  | leaf => simp [size]
  | one t ih => simp only [addrList_one, List.length_cons, List.length_map, ih, size]; omega
  | two l r ihl ihr =>
      simp only [addrList_two, List.length_cons, List.length_append, List.length_map,
        ihl, ihr, size]
      omega

lemma mem_addrList : ∀ (t : Tri) (v : Word), v ∈ addrList t ↔ t.IsAddr v := by
  intro t
  induction t with
  | leaf =>
      intro v
      rw [addrList_leaf, List.mem_singleton]
      exact ⟨fun h => by rw [h]; simp, fun h => eq_nil_of_isAddr_leaf h⟩
  | one t ih =>
      intro v
      cases v with
      | nil => simp
      | cons b v => cases b <;> simp [ih]
  | two l r ihl ihr =>
      intro v
      cases v with
      | nil => simp
      | cons b v => cases b <;> simp [ihl, ihr]

lemma nodup_addrList : ∀ t : Tri, (addrList t).Nodup := by
  intro t
  induction t with
  | leaf => simp
  | one t ih =>
      refine List.nodup_cons.mpr ⟨?_, ih.map fun _ _ h => by simpa using h⟩
      intro hc
      rw [List.mem_map] at hc
      obtain ⟨z, -, hz⟩ := hc
      exact absurd hz (by simp)
  | two l r ihl ihr =>
      have hl : ((addrList l).map (fun w => false :: w)).Nodup :=
        ihl.map fun _ _ h => by simpa using h
      have hr : ((addrList r).map (fun w => true :: w)).Nodup :=
        ihr.map fun _ _ h => by simpa using h
      have happ : ((addrList l).map (fun w => false :: w) ++
          (addrList r).map (fun w => true :: w)).Nodup := by
        refine List.Nodup.append hl hr ?_
        intro x hx hx'
        rw [List.mem_map] at hx hx'
        obtain ⟨y, -, rfl⟩ := hx
        obtain ⟨z, -, hz⟩ := hx'
        exact absurd hz (by simp)
      refine List.nodup_cons.mpr ⟨?_, happ⟩
      intro hc
      rw [List.mem_append] at hc
      rcases hc with hc | hc <;> rw [List.mem_map] at hc <;> obtain ⟨z, -, hz⟩ := hc <;>
        exact absurd hz (by simp)

/-- A depth bound for a finite set of addresses. -/
def maxLen (L : List Word) : ℕ := L.foldr (fun x acc => max x.length acc) 0

lemma le_maxLen : ∀ {L : List Word} {x : Word}, x ∈ L → x.length ≤ maxLen L := by
  intro L
  induction L with
  | nil => intro x h; simp at h
  | cons a as ih =>
      intro x h
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [maxLen, List.foldr_cons]
        exact le_max_left _ _
      · simp only [maxLen, List.foldr_cons]
        exact le_trans (ih h') (le_max_right _ _)

/-! ### A tree from a prefix-closed list of addresses -/

/-- The tree carrying a prefix-closed list of addresses, a leaf filling every
absent first-child slot. -/
def triOfList (L : List Word) : ℕ → Word → Tri
  | 0, _ => .leaf
  | n + 1, w =>
      if w ++ [true] ∈ L then
        .two (triOfList L n (w ++ [false])) (triOfList L n (w ++ [true]))
      else if w ++ [false] ∈ L then .one (triOfList L n (w ++ [false]))
      else .leaf

/-- A list of addresses closed under taking prefixes. -/
def PrefixClosedList (L : List Word) : Prop := ∀ x y : Word, x <+: y → y ∈ L → x ∈ L

/-- Off the list the tree carries a single vertex. -/
lemma triOfList_of_not_mem {L : List Word} (h : PrefixClosedList L) (n : ℕ) {w : Word}
    (hw : w ∉ L) : triOfList L n w = .leaf := by
  cases n with
  | zero => rfl
  | succ n =>
      have h1 : w ++ [true] ∉ L := fun hc => hw (h _ _ (List.prefix_append w [true]) hc)
      have h2 : w ++ [false] ∉ L := fun hc => hw (h _ _ (List.prefix_append w [false]) hc)
      rw [triOfList, if_neg h1, if_neg h2]

/-- Every listed address is an address of the tree. -/
lemma isAddr_triOfList {L : List Word} (h : PrefixClosedList L) :
    ∀ (n : ℕ) (w v : Word), w ++ v ∈ L → v.length ≤ n → (triOfList L n w).IsAddr v := by
  intro n
  induction n with
  | zero =>
      intro w v _ hlen
      have : v = [] := List.length_eq_zero_iff.mp (by omega)
      subst this
      simp
  | succ n ih =>
      intro w v hv hlen
      cases v with
      | nil => simp
      | cons b v =>
          cases b with
          | false =>
              have hsplit : w ++ false :: v = (w ++ [false]) ++ v := by simp
              rw [hsplit] at hv
              have hf : w ++ [false] ∈ L :=
                h _ _ (List.prefix_append _ _) hv
              by_cases ht : w ++ [true] ∈ L
              · rw [triOfList, if_pos ht, isAddr_two_false]
                exact ih _ _ hv (by simpa using hlen)
              · rw [triOfList, if_neg ht, if_pos hf, isAddr_one_false]
                exact ih _ _ hv (by simpa using hlen)
          | true =>
              have hsplit : w ++ true :: v = (w ++ [true]) ++ v := by simp
              rw [hsplit] at hv
              have ht : w ++ [true] ∈ L := h _ _ (List.prefix_append _ _) hv
              rw [triOfList, if_pos ht, isAddr_two_true]
              exact ih _ _ hv (by simpa using hlen)

/-- Every address of the tree is listed, or is a leaf filling an absent
first-child slot just below a listed one. -/
lemma mem_or_dummy_triOfList {L : List Word} (h : PrefixClosedList L) :
    ∀ (n : ℕ) (w v : Word), w ∈ L → (triOfList L n w).IsAddr v →
      w ++ v ∈ L ∨ ∃ u, v = u ++ [false] ∧ w ++ u ∈ L := by
  intro n
  induction n with
  | zero =>
      intro w v hw hv
      have : v = [] := eq_nil_of_isAddr_leaf hv
      subst this
      exact Or.inl (by simpa using hw)
  | succ n ih =>
      intro w v hw hv
      by_cases ht : w ++ [true] ∈ L
      · rw [triOfList, if_pos ht] at hv
        cases v with
        | nil => exact Or.inl (by simpa using hw)
        | cons b v =>
            cases b with
            | false =>
                rw [isAddr_two_false] at hv
                by_cases hf : w ++ [false] ∈ L
                · rcases ih _ _ hf hv with hl | ⟨u, rfl, hu⟩
                  · exact Or.inl (by simpa using hl)
                  · exact Or.inr ⟨false :: u, by simp, by simpa using hu⟩
                · rw [triOfList_of_not_mem h n hf] at hv
                  have : v = [] := eq_nil_of_isAddr_leaf hv
                  subst this
                  exact Or.inr ⟨[], by simp, by simpa using hw⟩
            | true =>
                rw [isAddr_two_true] at hv
                rcases ih _ _ ht hv with hl | ⟨u, rfl, hu⟩
                · exact Or.inl (by simpa using hl)
                · exact Or.inr ⟨true :: u, by simp, by simpa using hu⟩
      · by_cases hf : w ++ [false] ∈ L
        · rw [triOfList, if_neg ht, if_pos hf] at hv
          cases v with
          | nil => exact Or.inl (by simpa using hw)
          | cons b v =>
              cases b with
              | false =>
                  rw [isAddr_one_false] at hv
                  rcases ih _ _ hf hv with hl | ⟨u, rfl, hu⟩
                  · exact Or.inl (by simpa using hl)
                  · exact Or.inr ⟨false :: u, by simp, by simpa using hu⟩
              | true => exact absurd hv (isAddr_one_true _ v)
        · rw [triOfList, if_neg ht, if_neg hf] at hv
          have : v = [] := eq_nil_of_isAddr_leaf hv
          subst this
          exact Or.inl (by simpa using hw)

/-! ### The binarised tree of a contraction -/

lemma prefixClosed_binList (T : Tri) : PrefixClosedList (binList s T) := by
  intro x y hxy hy
  obtain ⟨q, hqa, hqp, rfl⟩ := exists_of_mem_binList hy
  exact prefix_mem_binList _ q le_rfl hqa hqp x hxy

lemma nil_mem_binList (T : Tri) : ([] : Word) ∈ binList s T := by
  have h := mem_binList (s := s) (T := T) (q := []) (isAddr_nil T) (part_nil T)
  rwa [binAddr_nil] at h

/-- **The first move**: the tree carrying the binarised addresses of the
parts. -/
def binOf (s : ℕ) (T : Tri) : Tri :=
  triOfList (binList s T) (maxLen (binList s T)) []

lemma isAddr_binOf {T : Tri} {q : Word} (hqa : T.IsAddr q) (hqp : part s T q = q) :
    (binOf s T).IsAddr (binAddr s T q) := by
  refine isAddr_triOfList (prefixClosed_binList T) _ [] _ ?_ ?_
  · simpa using mem_binList hqa hqp
  · exact le_maxLen (mem_binList hqa hqp)

/-- **`thm:shape-shrink`, the size of the first move**: the binarised tree has
at most twice the vertices of the contraction, the extra ones being the leaves
that fill an absent first-child slot. -/
theorem size_binOf_le (T : Tri) : (binOf s T).size ≤ 2 * (contractTree s T).size := by
  have hsub : addrList (binOf s T) ⊆
      binList s T ++ (binList s T).map (fun x => x ++ [false]) := by
    intro v hv
    have hva := (mem_addrList _ v).mp hv
    rcases mem_or_dummy_triOfList (prefixClosed_binList T) _ [] v (nil_mem_binList T) hva
      with hl | ⟨u, rfl, hu⟩
    · exact List.mem_append_left _ (by simpa using hl)
    · exact List.mem_append_right _ (List.mem_map_of_mem (by simpa using hu))
  have hle := (List.subperm_of_subset (nodup_addrList (binOf s T)) hsub).length_le
  rw [length_addrList, List.length_append, List.length_map] at hle
  have hcount : (binList s T).length = (contractTree s T).size := by
    rw [binList, List.length_map, length_partList]
  omega

end Tri

/-! ### The composition -/

/-- **The first move**, as a statement: at scale `s` the contraction of a tree
with a marked part is `4s`-comparable to a tree with at most two children per
vertex and a marked vertex, of at most twice the size of the contraction. -/
def BinarisesAt (s : ℕ) : Prop :=
  ∀ (T : Tri) (e : Word) (he : T.IsAddr e),
    ∃ (B : Tri) (m : Word) (hm : B.IsAddr m),
      B.size ≤ 2 * (Tri.contractTree s T).size ∧
        MarkedQI (4 * s : ℝ) (partSpace s he) (triSpace hm)

/-- **`thm:shape-shrink` (`it:shape-shrink`), the first move**: the
binarisation is a `4s`-marked quasi-isometry of the contraction onto the tree
`Tri.binOf` carrying the binarised addresses of the parts.  A part sits one
step into the first-child slot of its part-parent and then along the spine of
its siblings, so one edge of the contraction spans at most `4s` edges, and a
geodesic of the binarised tree passes through the meet of the two addresses,
which is again the address of a part. -/
theorem binarisesAt {s : ℕ} (hs : 1 ≤ s) : BinarisesAt s := by
  intro T e he
  have hpa : T.IsAddr (Tri.part s T e) := T.isAddr_of_prefix (Tri.part_prefix T e) he
  have hpp : Tri.part s T (Tri.part s T e) = Tri.part s T e := Tri.part_idem T e
  refine ⟨Tri.binOf s T, Tri.binAddr s T (Tri.part s T e), Tri.isAddr_binOf hpa hpp,
    Tri.size_binOf_le T, ?_⟩
  have hs0 : (0 : ℝ) ≤ 4 * (s : ℝ) := by positivity
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ 4 * (s : ℝ) := by linarith
  refine ⟨fun p => ⟨Tri.binAddr s T p.1, Tri.isAddr_binOf p.2.1 p.2.2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    have h := Tri.treeDist_binAddr_le_dist hs a b
    have hnat : treeDist (Tri.binAddr s T a.1) (Tri.binAddr s T b.1)
        ≤ 4 * s * (partGraph s T).dist a b + 4 * s := by omega
    show ((treeDist (Tri.binAddr s T a.1) (Tri.binAddr s T b.1) : ℕ) : ℝ)
      ≤ 4 * (s : ℝ) * (((partGraph s T).dist a b : ℕ) : ℝ) + 4 * (s : ℝ)
    exact_mod_cast hnat
  · intro a b
    have h := Tri.dist_le_treeDist_binAddr a b
    have h2 : 2 * treeDist (Tri.binAddr s T a.1) (Tri.binAddr s T b.1)
        ≤ 4 * s * treeDist (Tri.binAddr s T a.1) (Tri.binAddr s T b.1) :=
      Nat.mul_le_mul_right _ (by omega)
    have hnat : (partGraph s T).dist a b
        ≤ 4 * s * treeDist (Tri.binAddr s T a.1) (Tri.binAddr s T b.1) + 4 * s * (4 * s) := by
      omega
    show (((partGraph s T).dist a b : ℕ) : ℝ)
      ≤ 4 * (s : ℝ) * ((treeDist (Tri.binAddr s T a.1) (Tri.binAddr s T b.1) : ℕ) : ℝ)
        + 4 * (s : ℝ) * (4 * (s : ℝ))
    exact_mod_cast hnat
  · intro y
    rcases Tri.mem_or_dummy_triOfList (Tri.prefixClosed_binList T) _ [] y.1
      (Tri.nil_mem_binList T) y.2 with hl | ⟨u, hu, hum⟩
    · obtain ⟨q, hqa, hqp, hq⟩ := Tri.exists_of_mem_binList (by simpa using hl)
      refine ⟨⟨q, hqa, hqp⟩, ?_⟩
      show ((treeDist (Tri.binAddr s T q) y.1 : ℕ) : ℝ) ≤ 4 * (s : ℝ)
      rw [hq, treeDist_self]
      simp
    · obtain ⟨q, hqa, hqp, hq⟩ := Tri.exists_of_mem_binList (by simpa using hum)
      refine ⟨⟨q, hqa, hqp⟩, ?_⟩
      have hone : treeDist (Tri.binAddr s T q) y.1 = 1 := by
        rw [hq, hu, treeDist_of_prefix (List.prefix_append u [false])]
        simp
      show ((treeDist (Tri.binAddr s T q) y.1 : ℕ) : ℝ) ≤ 4 * (s : ℝ)
      rw [hone]
      simpa using hs1
  · show ((treeDist (Tri.binAddr s T ([] : Word)) [] : ℕ) : ℝ) ≤ 4 * (s : ℝ)
    rw [Tri.binAddr_nil, treeDist_self]
    simp
  · show ((treeDist (Tri.binAddr s T (Tri.part s T e))
      (Tri.binAddr s T (Tri.part s T e)) : ℕ) : ℝ) ≤ 4 * (s : ℝ)
    rw [treeDist_self]
    simp

/-- **`thm:shape-shrink` (`it:shape-shrink`)**: at scale `s ≥ 1` every
shape `σ` of size `n` admits a shape `σ₀` in the support with
`|σ₀| ≤ 16(n/s+1)` and a `2592 s²`-marked quasi-isometry `σ → σ₀`.  The
contraction of `thm:dilution` is `2s`-marked, the binarisation `4s`-marked, the
neck construction `6`-marked and the support fix `2`-marked, and the
composition bound of `thm:shape-net` multiplies these to
`27·2s·4s·6·2 = 2592 s²`; the sizes run `k ≤ n/s+1` parts, at most `2k`
vertices after binarising, at most `2k+2` in the shape and at most `4k+4 ≤ 16k`
after the fix. -/
theorem markedQI_shape_shrink {s : ℕ} (hs : 1 ≤ s) (σ : Shape) :
    ∃ σ₀ : Shape, Shape.Supported σ₀ ∧ σ₀.size ≤ 16 * (σ.size / s + 1) ∧
      MarkedQI (2592 * (s : ℝ) ^ 2) (shapeSpace σ) (shapeSpace σ₀) := by
  obtain ⟨B, m, hm, hBsize, hbinqi⟩ :=
    binarisesAt hs (realiseAux σ.decs) (Shape.neckAddr σ.decs) (Shape.isAddr_neckAddr σ.decs)
  refine ⟨(Tri.neckShape B m).fix, supported_fix _, ?_, ?_⟩
  · -- the size arithmetic
    have h1 : (Tri.contractTree s (realiseAux σ.decs)).size ≤ σ.size / s + 1 := by
      have h := Tri.size_contractTree_le_div (s := s) hs (realiseAux σ.decs)
      have hsz : (realiseAux σ.decs).size = σ.size := rfl
      rwa [hsz] at h
    have h2 := Tri.size_neckShape_le B m
    have h3 := size_fix_le (Tri.neckShape B m)
    obtain ⟨q, hq⟩ : ∃ q, σ.size / s = q := ⟨_, rfl⟩
    rw [hq] at h1 ⊢
    omega
  · -- the constant arithmetic
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have hA : (1 : ℝ) ≤ 2 * (s : ℝ) := by linarith
    have hB : (1 : ℝ) ≤ 4 * (s : ℝ) := by linarith
    have hC : (1 : ℝ) ≤ 3 * (2 * (s : ℝ)) * (4 * (s : ℝ)) := by nlinarith
    have hD : (1 : ℝ) ≤ 3 * (3 * (2 * (s : ℝ)) * (4 * (s : ℝ))) * 6 := by nlinarith
    have step1 := markedQI_comp hA hB (markedQI_contract_shape hs σ) hbinqi
    have step2 := markedQI_comp hC (by norm_num : (1 : ℝ) ≤ 6) step1 (markedQI_six_neck hm)
    have step3 := markedQI_comp hD (by norm_num : (1 : ℝ) ≤ 2) step2
      (markedQI_two_shape_fix (Tri.neckShape B m))
    have hconst : 3 * (3 * (3 * (2 * (s : ℝ)) * (4 * (s : ℝ))) * 6) * 2
        = 2592 * (s : ℝ) ^ 2 := by ring
    rwa [hconst] at step3

/-- **`thm:shape-shrink` (`it:shape-shrink`), the choice of scale**: at
`s = ⌊√(D/2592)⌋` the constant of the composition is at most `D`. -/
lemma shrinkScale_sq_le (D : ℕ) : 2592 * (Nat.sqrt (D / 2592) : ℝ) ^ 2 ≤ (D : ℝ) := by
  have h : 2592 * Nat.sqrt (D / 2592) ^ 2 ≤ D := by
    have h1 : Nat.sqrt (D / 2592) ^ 2 ≤ D / 2592 := Nat.sqrt_le' _
    have h2 : 2592 * (D / 2592) ≤ D := by omega
    calc 2592 * Nat.sqrt (D / 2592) ^ 2 ≤ 2592 * (D / 2592) := by
          exact Nat.mul_le_mul_left _ h1
      _ ≤ D := h2
  exact_mod_cast h

/-- **`thm:shape-shrink` (`it:shape-shrink`)** at the paper's scale: for
`s ≥ 1` with `2592 s² ≤ D`, which `shrinkScale_sq_le` supplies at
`s = ⌊√(D/2592)⌋`, every shape `σ` of size `n` admits a shape `σ₀` in the
support with `|σ₀| ≤ 16(n/s+1)` and a `D`-marked quasi-isometry `σ → σ₀`. -/
theorem markedQI_shape_shrink_of_le {s : ℕ} {D : ℝ} (hs : 1 ≤ s)
    (hD : 2592 * (s : ℝ) ^ 2 ≤ D) (σ : Shape) :
    ∃ σ₀ : Shape, Shape.Supported σ₀ ∧ σ₀.size ≤ 16 * (σ.size / s + 1) ∧
      MarkedQI D (shapeSpace σ) (shapeSpace σ₀) := by
  obtain ⟨σ₀, hsup, hsize, hqi⟩ := markedQI_shape_shrink hs σ
  exact ⟨σ₀, hsup, hsize, hqi.mono (by positivity) hD⟩

end ChainClasses
