import Mathlib.Tactic
import Mathlib.Data.Nat.Nth
import ChainClasses.Chain.Labelling
import ChainClasses.Scalar.MarkedQI
import ChainClasses.Shape.Shape

/-!
`sec:shape-harris` and `sec:shape-net` of `matching_classes_simple.tex`: the
metric realisation of `def:shape`, the marked spaces that `thm:shape-net`
compares, and the leaf deletion of `thm:shape-connected`.

A vertex of a realisation is recorded by its address, a word over the two
letters, so the vertex set of a tree is a subtree of the ambient `𝒩` and its
metric is the restriction of `treeDist`: the child of a `one` and the first
child of a `two` sit at `false`, the second child of a `two` at `true`.  The
distance is therefore inherited rather than rebuilt, and `treeDist_eq_one_iff`
identifies it as the graph metric of the parent-child adjacency.

* `Tri.IsAddr`, `Tri.Vert`: the addresses of a tree and the vertex set they
  form, a metric space by `treeDist_triangle`, with `Tri.Adj` the parent-child
  adjacency and `Tri.dist_eq_one_iff_adj` the identification of the metric.
* `Shape.neckAddr`, `shapeSpace`: **`def:shape`**, the realisation as a marked
  space, the entry at the root and the exit at the far end of the neck;
  `dist_entry_exit` is the neck length less one.
* `Shrinks`, `Tri.exists_shrinks_del`, `exists_markedQI_shrink`:
  **`thm:shape-connected`**, the leaf deletion as a `1`-marked quasi-isometry.
  A leaf of the first nonempty decoration is deleted if there is one and the
  exit otherwise, and the deleted vertex is sent to its neighbour.
* `shapeEnum`, `shapeFamily`: **`def:shape-net`**, the enumeration of `𝒮` by
  size.  The code of the realisation read as a number (`shapeKey`) is injective
  and grows with the size, since `numOf` lists the shorter words first, so the
  enumeration is the increasing one of the range of that key.
* `size_repIdx_le`, `netLink_connected_shapeFamily`: **`thm:shape-net`** and
  **`thm:shape-connected`** for the shapes themselves.
-/

namespace ChainClasses

open Shape (realiseAux)

/-! ### The vertex set of a realisation -/

/-- The addresses of a finite tree: the child of a `one` and the first child of
a `two` sit at `false`, the second child of a `two` at `true`. -/
def Tri.IsAddr : Tri → Word → Prop
  | .leaf, [] => True
  | .leaf, _ :: _ => False
  | .one _, [] => True
  | .one t, false :: w => t.IsAddr w
  | .one _, true :: _ => False
  | .two _ _, [] => True
  | .two l _, false :: w => l.IsAddr w
  | .two _ r, true :: w => r.IsAddr w

/-- The root is an address. -/
@[simp] lemma Tri.isAddr_nil (t : Tri) : t.IsAddr [] := by cases t <;> trivial

/-- A single vertex carries nothing below its root. -/
@[simp] lemma Tri.isAddr_leaf_cons (a : Bool) (w : Word) : ¬ Tri.leaf.IsAddr (a :: w) := id

/-- The addresses below the child of a `one`. -/
@[simp] lemma Tri.isAddr_one_false (t : Tri) (w : Word) :
    (Tri.one t).IsAddr (false :: w) ↔ t.IsAddr w := Iff.rfl

/-- A `one` has no second child. -/
@[simp] lemma Tri.isAddr_one_true (t : Tri) (w : Word) :
    ¬ (Tri.one t).IsAddr (true :: w) := id

/-- The addresses below the first child of a `two`. -/
@[simp] lemma Tri.isAddr_two_false (l r : Tri) (w : Word) :
    (Tri.two l r).IsAddr (false :: w) ↔ l.IsAddr w := Iff.rfl

/-- The addresses below the second child of a `two`. -/
@[simp] lemma Tri.isAddr_two_true (l r : Tri) (w : Word) :
    (Tri.two l r).IsAddr (true :: w) ↔ r.IsAddr w := Iff.rfl

/-- Only the root is an address of a single vertex. -/
lemma Tri.eq_nil_of_isAddr_leaf {w : Word} (h : Tri.leaf.IsAddr w) : w = [] := by
  cases w with
  | nil => rfl
  | cons a w => exact absurd h (Tri.isAddr_leaf_cons a w)

/-- The address set is closed under prefixes, so it is a subtree of `𝒩`. -/
lemma Tri.isAddr_of_prefix : ∀ (t : Tri) {p w : Word}, p <+: w → t.IsAddr w → t.IsAddr p := by
  intro t
  induction t with
  | leaf =>
      intro p w hp hw
      rw [Tri.eq_nil_of_isAddr_leaf hw] at hp
      rw [List.prefix_nil.mp hp]
      simp
  | one t ih =>
      intro p w hp hw
      cases p with
      | nil => simp
      | cons a p =>
          cases w with
          | nil => simp at hp
          | cons b w =>
              rw [List.cons_prefix_cons] at hp
              obtain ⟨rfl, hp⟩ := hp
              cases a with
              | false => exact ih hp hw
              | true => exact absurd hw (Tri.isAddr_one_true t w)
  | two l r ihl ihr =>
      intro p w hp hw
      cases p with
      | nil => simp
      | cons a p =>
          cases w with
          | nil => simp at hp
          | cons b w =>
              rw [List.cons_prefix_cons] at hp
              obtain ⟨rfl, hp⟩ := hp
              cases a with
              | false => exact ihl hp hw
              | true => exact ihr hp hw

/-- The vertex set of a tree: the words that address its vertices. -/
def Tri.Vert (t : Tri) : Type := {w : Word // t.IsAddr w}

/-- The graph metric of a tree, restricted from the ambient tree along the
addresses. -/
instance Tri.instMetricSpaceVert (t : Tri) : MetricSpace t.Vert where
  dist u v := (treeDist u.1 v.1 : ℝ)
  dist_self u := by simp
  dist_comm u v := by simp only [treeDist_comm u.1 v.1]
  dist_triangle u v w := by
    have := treeDist_triangle u.1 v.1 w.1
    exact_mod_cast this
  eq_of_dist_eq_zero {u v} h := by
    have : treeDist u.1 v.1 = 0 := by exact_mod_cast h
    exact Subtype.ext (treeDist_eq_zero_iff.mp this)

/-- The distance of two vertices is the distance of their addresses. -/
@[simp] lemma Tri.dist_vert (t : Tri) (u v : t.Vert) :
    dist u v = (treeDist u.1 v.1 : ℝ) := rfl

/-- The parent-child adjacency on the vertex set. -/
def Tri.Adj {t : Tri} (u v : t.Vert) : Prop :=
  (∃ b, v.1 = u.1 ++ [b]) ∨ (∃ b, u.1 = v.1 ++ [b])

/-- The metric of `Tri.Vert` is the graph metric of `Tri.Adj`. -/
lemma Tri.dist_eq_one_iff_adj {t : Tri} (u v : t.Vert) : dist u v = 1 ↔ Tri.Adj u v := by
  rw [Tri.dist_vert]
  constructor
  · intro h
    exact treeDist_eq_one_iff.mp (by exact_mod_cast h)
  · intro h
    have : treeDist u.1 v.1 = 1 := treeDist_eq_one_iff.mpr h
    rw [this]
    norm_num

/-! ### Shapes as marked spaces -/

/-- The address of the exit: the neck descends to `true` at a decorated vertex
and to `false` at an undecorated one. -/
def Shape.neckAddr : List (Option Tri) → Word
  | [] => []
  | none :: bs => false :: Shape.neckAddr bs
  | some _ :: bs => true :: Shape.neckAddr bs

/-- A neck of one vertex has its exit at the root. -/
@[simp] lemma Shape.neckAddr_nil : Shape.neckAddr [] = [] := rfl

/-- An undecorated neck vertex passes the neck to `false`. -/
@[simp] lemma Shape.neckAddr_none (bs : List (Option Tri)) :
    Shape.neckAddr (none :: bs) = false :: Shape.neckAddr bs := rfl

/-- A decorated neck vertex passes the neck to `true`. -/
@[simp] lemma Shape.neckAddr_some (b : Tri) (bs : List (Option Tri)) :
    Shape.neckAddr (some b :: bs) = true :: Shape.neckAddr bs := rfl

/-- The exit sits at the depth of the number of decorations. -/
@[simp] lemma Shape.neckAddr_length (l : List (Option Tri)) :
    (Shape.neckAddr l).length = l.length := by
  induction l with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [ih]

/-- The exit is a vertex of the realisation. -/
lemma Shape.isAddr_neckAddr (l : List (Option Tri)) :
    (realiseAux l).IsAddr (Shape.neckAddr l) := by
  induction l with
  | nil => simp
  | cons b bs ih => cases b <;> simpa [realiseAux] using ih

/-- **`def:shape`**: the realisation of a decorated neck as a marked space, the
entry at the root and the exit at the far end of the neck. -/
def listSpace (l : List (Option Tri)) : MarkedSpace where
  carrier := (realiseAux l).Vert
  entry := ⟨[], by simp⟩
  exit := ⟨Shape.neckAddr l, Shape.isAddr_neckAddr l⟩

/-- **`def:shape`**: the realisation of a shape as a marked space. -/
def shapeSpace (σ : Shape) : MarkedSpace := listSpace σ.decs

/-- The distance of two vertices of a realisation. -/
@[simp] lemma dist_listSpace (l : List (Option Tri)) (u v : (listSpace l).carrier) :
    dist u v = (treeDist u.1 v.1 : ℝ) := rfl

/-- The entry is the root. -/
@[simp] lemma entry_listSpace (l : List (Option Tri)) : (listSpace l).entry.1 = [] := rfl

/-- The exit is the far end of the neck. -/
@[simp] lemma exit_listSpace (l : List (Option Tri)) :
    (listSpace l).exit.1 = Shape.neckAddr l := rfl

/-- The shape assembled from a list of decorations realises that list. -/
lemma shapeSpace_ofList (l : List (Option Tri)) : shapeSpace (Shape.ofList l) = listSpace l := by
  rw [shapeSpace, Shape.decs_ofList]

/-- **`def:shape`**: the entry and the exit of a shape are the two ends of its
neck, at distance the neck length less one. -/
lemma dist_entry_exit (σ : Shape) :
    dist (shapeSpace σ).entry (shapeSpace σ).exit = (σ.necks : ℝ) := by
  rw [shapeSpace, dist_listSpace, entry_listSpace, exit_listSpace]
  rw [treeDist_nil_left, Shape.neckAddr_length, Shape.decs_length]

/-! ### Deleting a leaf -/

/-- A `k`-shrink of `T` onto `T'`: an address map onto the addresses of `T'`
that fixes the root and changes distances by at most `k`. -/
structure Shrinks (k : ℕ) (T T' : Tri) (f : Word → Word) : Prop where
  maps : ∀ w, T.IsAddr w → T'.IsAddr (f w)
  root : f [] = []
  surj : ∀ y, T'.IsAddr y → ∃ w, T.IsAddr w ∧ f w = y
  upper : ∀ u v, T.IsAddr u → T.IsAddr v → treeDist (f u) (f v) ≤ treeDist u v + k
  lower : ∀ u v, T.IsAddr u → T.IsAddr v → treeDist u v ≤ treeDist (f u) (f v) + k

/-- A shrink shortens no address by more than `k`. -/
lemma Shrinks.length_le {k : ℕ} {T T' : Tri} {f : Word → Word} (hf : Shrinks k T T' f)
    {w : Word} (hw : T.IsAddr w) : (f w).length ≤ w.length + k := by
  have h := hf.upper [] w (by simp) hw
  rw [hf.root] at h
  simpa using h

/-- A shrink lengthens no address by more than `k`. -/
lemma Shrinks.le_length {k : ℕ} {T T' : Tri} {f : Word → Word} (hf : Shrinks k T T' f)
    {w : Word} (hw : T.IsAddr w) : w.length ≤ (f w).length + k := by
  have h := hf.lower [] w (by simp) hw
  rw [hf.root] at h
  simpa using h

/-- The identity is a `0`-shrink. -/
lemma Shrinks.refl (t : Tri) : Shrinks 0 t t id :=
  ⟨fun _ hw => hw, rfl, fun y hy => ⟨y, hy, rfl⟩, by simp, by simp⟩

/-- Two maps applied below the two children of the root. -/
def branch (g h : Word → Word) : Word → Word
  | [] => []
  | false :: w => false :: g w
  | true :: w => true :: h w

/-- The root is fixed. -/
@[simp] lemma branch_nil (g h : Word → Word) : branch g h [] = [] := rfl

/-- The first subtree carries `g`. -/
@[simp] lemma branch_false (g h : Word → Word) (w : Word) :
    branch g h (false :: w) = false :: g w := rfl

/-- The second subtree carries `h`. -/
@[simp] lemma branch_true (g h : Word → Word) (w : Word) :
    branch g h (true :: w) = true :: h w := rfl

/-- Shrinking the two subtrees of a branching root. -/
lemma Shrinks.two {j k : ℕ} {l l' r r' : Tri} {g h : Word → Word}
    (hg : Shrinks j l l' g) (hh : Shrinks k r r' h) :
    Shrinks (j + k) (Tri.two l r) (Tri.two l' r') (branch g h) := by
  have key : ∀ u v, (Tri.two l r).IsAddr u → (Tri.two l r).IsAddr v →
      treeDist (branch g h u) (branch g h v) ≤ treeDist u v + (j + k) ∧
      treeDist u v ≤ treeDist (branch g h u) (branch g h v) + (j + k) := by
    rintro (_ | ⟨a, u⟩) (_ | ⟨b, v⟩) hu hv
    · simp
    · cases b with
      | false =>
          rw [Tri.isAddr_two_false] at hv
          have h1 := hg.length_le hv
          have h2 := hg.le_length hv
          simp only [branch_nil, branch_false, treeDist_nil_left, List.length_cons]
          omega
      | true =>
          rw [Tri.isAddr_two_true] at hv
          have h1 := hh.length_le hv
          have h2 := hh.le_length hv
          simp only [branch_nil, branch_true, treeDist_nil_left, List.length_cons]
          omega
    · cases a with
      | false =>
          rw [Tri.isAddr_two_false] at hu
          have h1 := hg.length_le hu
          have h2 := hg.le_length hu
          simp only [branch_nil, branch_false, treeDist_nil_right, List.length_cons]
          omega
      | true =>
          rw [Tri.isAddr_two_true] at hu
          have h1 := hh.length_le hu
          have h2 := hh.le_length hu
          simp only [branch_nil, branch_true, treeDist_nil_right, List.length_cons]
          omega
    · cases a with
      | false =>
          rw [Tri.isAddr_two_false] at hu
          cases b with
          | false =>
              rw [Tri.isAddr_two_false] at hv
              have h1 := hg.upper u v hu hv
              have h2 := hg.lower u v hu hv
              simp only [branch_false, treeDist_cons_cons_self]
              omega
          | true =>
              rw [Tri.isAddr_two_true] at hv
              have h1 := hg.length_le hu
              have h2 := hg.le_length hu
              have h3 := hh.length_le hv
              have h4 := hh.le_length hv
              simp only [branch_false, branch_true, treeDist_false_true]
              omega
      | true =>
          rw [Tri.isAddr_two_true] at hu
          cases b with
          | false =>
              rw [Tri.isAddr_two_false] at hv
              have h1 := hh.length_le hu
              have h2 := hh.le_length hu
              have h3 := hg.length_le hv
              have h4 := hg.le_length hv
              simp only [branch_false, branch_true, treeDist_true_false]
              omega
          | true =>
              rw [Tri.isAddr_two_true] at hv
              have h1 := hh.upper u v hu hv
              have h2 := hh.lower u v hu hv
              simp only [branch_true, treeDist_cons_cons_self]
              omega
  refine ⟨?_, rfl, ?_, fun u v hu hv => (key u v hu hv).1, fun u v hu hv => (key u v hu hv).2⟩
  · rintro (_ | ⟨a, w⟩) hw
    · simp
    · cases a with
      | false => exact hg.maps w hw
      | true => exact hh.maps w hw
  · rintro (_ | ⟨a, y⟩) hy
    · exact ⟨[], by simp, rfl⟩
    · cases a with
      | false =>
          obtain ⟨w, hw, hfw⟩ := hg.surj y hy
          exact ⟨false :: w, hw, by rw [branch_false, hfw]⟩
      | true =>
          obtain ⟨w, hw, hfw⟩ := hh.surj y hy
          exact ⟨true :: w, hw, by rw [branch_true, hfw]⟩

/-- Shrinking the subtree of a single-child root. -/
lemma Shrinks.one {k : ℕ} {t t' : Tri} {g h : Word → Word} (hg : Shrinks k t t' g) :
    Shrinks k (Tri.one t) (Tri.one t') (branch g h) := by
  have key : ∀ u v, (Tri.one t).IsAddr u → (Tri.one t).IsAddr v →
      treeDist (branch g h u) (branch g h v) ≤ treeDist u v + k ∧
      treeDist u v ≤ treeDist (branch g h u) (branch g h v) + k := by
    rintro (_ | ⟨a, u⟩) (_ | ⟨b, v⟩) hu hv
    · simp
    · cases b with
      | false =>
          rw [Tri.isAddr_one_false] at hv
          have h1 := hg.length_le hv
          have h2 := hg.le_length hv
          simp only [branch_nil, branch_false, treeDist_nil_left, List.length_cons]
          omega
      | true => exact absurd hv (Tri.isAddr_one_true t v)
    · cases a with
      | false =>
          rw [Tri.isAddr_one_false] at hu
          have h1 := hg.length_le hu
          have h2 := hg.le_length hu
          simp only [branch_nil, branch_false, treeDist_nil_right, List.length_cons]
          omega
      | true => exact absurd hu (Tri.isAddr_one_true t u)
    · cases a with
      | false =>
          rw [Tri.isAddr_one_false] at hu
          cases b with
          | false =>
              rw [Tri.isAddr_one_false] at hv
              have h1 := hg.upper u v hu hv
              have h2 := hg.lower u v hu hv
              simp only [branch_false, treeDist_cons_cons_self]
              omega
          | true => exact absurd hv (Tri.isAddr_one_true t v)
      | true => exact absurd hu (Tri.isAddr_one_true t u)
  refine ⟨?_, rfl, ?_, fun u v hu hv => (key u v hu hv).1, fun u v hu hv => (key u v hu hv).2⟩
  · rintro (_ | ⟨a, w⟩) hw
    · simp
    · cases a with
      | false => exact hg.maps w hw
      | true => exact absurd hw (Tri.isAddr_one_true t w)
  · rintro (_ | ⟨a, y⟩) hy
    · exact ⟨[], by simp, rfl⟩
    · cases a with
      | false =>
          obtain ⟨w, hw, hfw⟩ := hg.surj y hy
          exact ⟨false :: w, hw, by rw [branch_false, hfw]⟩
      | true => exact absurd hy (Tri.isAddr_one_true t' y)

/-- The two addresses of a single edge. -/
lemma Tri.isAddr_one_leaf {w : Word} (h : (Tri.one Tri.leaf).IsAddr w) :
    w = [] ∨ w = [false] := by
  cases w with
  | nil => exact Or.inl rfl
  | cons a w =>
      cases a with
      | false =>
          rw [Tri.isAddr_one_false] at h
          rw [Tri.eq_nil_of_isAddr_leaf h]
          exact Or.inr rfl
      | true => exact absurd h (Tri.isAddr_one_true Tri.leaf w)

/-- Deleting the only child of the root: both vertices go to the root. -/
lemma shrinks_collapse : Shrinks 1 (Tri.one Tri.leaf) Tri.leaf (fun _ => []) := by
  refine ⟨fun w _ => by simp, rfl, fun y hy => ⟨[], by simp, (Tri.eq_nil_of_isAddr_leaf hy).symm⟩,
    by simp, ?_⟩
  intro u v hu hv
  rcases Tri.isAddr_one_leaf hu with rfl | rfl <;> rcases Tri.isAddr_one_leaf hv with rfl | rfl <;>
    simp

/-- Deleting the second child of the root, a leaf. -/
def dropRight : Word → Word
  | [] => []
  | false :: w => false :: w
  | true :: _ => []

/-- The root is fixed. -/
@[simp] lemma dropRight_nil : dropRight [] = [] := rfl

/-- The first subtree is fixed. -/
@[simp] lemma dropRight_false (w : Word) : dropRight (false :: w) = false :: w := rfl

/-- The deleted vertex goes to its neighbour, the root. -/
@[simp] lemma dropRight_true (w : Word) : dropRight (true :: w) = [] := rfl

/-- `thm:shape-connected`: deleting the second child of the root when it is a
leaf is a `1`-shrink. -/
lemma shrinks_dropRight (l : Tri) :
    Shrinks 1 (Tri.two l Tri.leaf) (Tri.one l) dropRight := by
  have key : ∀ u v, (Tri.two l Tri.leaf).IsAddr u → (Tri.two l Tri.leaf).IsAddr v →
      treeDist (dropRight u) (dropRight v) ≤ treeDist u v + 1 ∧
      treeDist u v ≤ treeDist (dropRight u) (dropRight v) + 1 := by
    rintro (_ | ⟨a, u⟩) (_ | ⟨b, v⟩) hu hv
    · simp
    · cases b with
      | false => simp
      | true =>
          rw [Tri.isAddr_two_true] at hv
          rw [Tri.eq_nil_of_isAddr_leaf hv]
          simp
    · cases a with
      | false => simp
      | true =>
          rw [Tri.isAddr_two_true] at hu
          rw [Tri.eq_nil_of_isAddr_leaf hu]
          simp
    · cases a with
      | false =>
          cases b with
          | false => simp
          | true =>
              rw [Tri.isAddr_two_true] at hv
              rw [Tri.eq_nil_of_isAddr_leaf hv]
              simp
      | true =>
          rw [Tri.isAddr_two_true] at hu
          rw [Tri.eq_nil_of_isAddr_leaf hu]
          cases b with
          | false => simp
          | true =>
              rw [Tri.isAddr_two_true] at hv
              rw [Tri.eq_nil_of_isAddr_leaf hv]
              simp
  refine ⟨?_, rfl, ?_, fun u v hu hv => (key u v hu hv).1, fun u v hu hv => (key u v hu hv).2⟩
  · rintro (_ | ⟨a, w⟩) hw
    · simp
    · cases a with
      | false => simpa using hw
      | true => simp
  · rintro (_ | ⟨a, y⟩) hy
    · exact ⟨[], by simp, rfl⟩
    · cases a with
      | false => exact ⟨false :: y, hy, rfl⟩
      | true => exact absurd hy (Tri.isAddr_one_true l y)

/-- Deleting the first child of the root, a leaf: the second subtree slides
across to the free slot. -/
def slide : Word → Word
  | [] => []
  | false :: _ => []
  | true :: w => false :: w

/-- The root is fixed. -/
@[simp] lemma slide_nil : slide [] = [] := rfl

/-- The deleted vertex goes to its neighbour, the root. -/
@[simp] lemma slide_false (w : Word) : slide (false :: w) = [] := rfl

/-- The second subtree slides into the free slot. -/
@[simp] lemma slide_true (w : Word) : slide (true :: w) = false :: w := rfl

/-- `thm:shape-connected`: deleting the first child of the root when it is a
leaf is a `1`-shrink. -/
lemma shrinks_slide (r : Tri) :
    Shrinks 1 (Tri.two Tri.leaf r) (Tri.one r) slide := by
  have key : ∀ u v, (Tri.two Tri.leaf r).IsAddr u → (Tri.two Tri.leaf r).IsAddr v →
      treeDist (slide u) (slide v) ≤ treeDist u v + 1 ∧
      treeDist u v ≤ treeDist (slide u) (slide v) + 1 := by
    rintro (_ | ⟨a, u⟩) (_ | ⟨b, v⟩) hu hv
    · simp
    · cases b with
      | false =>
          rw [Tri.isAddr_two_false] at hv
          rw [Tri.eq_nil_of_isAddr_leaf hv]
          simp
      | true => simp
    · cases a with
      | false =>
          rw [Tri.isAddr_two_false] at hu
          rw [Tri.eq_nil_of_isAddr_leaf hu]
          simp
      | true => simp
    · cases a with
      | false =>
          rw [Tri.isAddr_two_false] at hu
          rw [Tri.eq_nil_of_isAddr_leaf hu]
          cases b with
          | false =>
              rw [Tri.isAddr_two_false] at hv
              rw [Tri.eq_nil_of_isAddr_leaf hv]
              simp
          | true => simp
      | true =>
          cases b with
          | false =>
              rw [Tri.isAddr_two_false] at hv
              rw [Tri.eq_nil_of_isAddr_leaf hv]
              simp
          | true => simp
  refine ⟨?_, rfl, ?_, fun u v hu hv => (key u v hu hv).1, fun u v hu hv => (key u v hu hv).2⟩
  · rintro (_ | ⟨a, w⟩) hw
    · simp
    · cases a with
      | false => simp
      | true => simpa using hw
  · rintro (_ | ⟨a, y⟩) hy
    · exact ⟨[], by simp, rfl⟩
    · cases a with
      | false => exact ⟨true :: y, hy, rfl⟩
      | true => exact absurd hy (Tri.isAddr_one_true r y)

/-- Only a single vertex has nothing left to delete. -/
lemma Tri.del_eq_none_iff {t : Tri} : t.del = none ↔ t = Tri.leaf := by
  cases t <;> simp [Tri.del]

/-- **`thm:shape-connected`**, inside a decoration: the leaf deletion `Tri.del`
is a `1`-shrink of the tree onto what it leaves. -/
lemma Tri.exists_shrinks_del : ∀ t t' : Tri, t.del = some t' → ∃ f, Shrinks 1 t t' f := by
  intro t
  induction t with
  | leaf => intro t' h; simp [Tri.del] at h
  | one s ih =>
      intro t' h
      simp only [Tri.del] at h
      cases hs : s.del with
      | none =>
          rw [hs] at h
          simp only [Tri.graftOne, Option.some.injEq] at h
          subst h
          have hsl : s = Tri.leaf := Tri.del_eq_none_iff.mp hs
          subst hsl
          exact ⟨_, shrinks_collapse⟩
      | some s' =>
          rw [hs] at h
          simp only [Tri.graftOne, Option.some.injEq] at h
          subst h
          obtain ⟨g, hgs⟩ := ih s' hs
          exact ⟨branch g id, hgs.one⟩
  | two l r _ ihr =>
      intro t' h
      simp only [Tri.del] at h
      cases hr : r.del with
      | none =>
          rw [hr] at h
          simp only [Tri.graftTwo, Option.some.injEq] at h
          subst h
          have hrl : r = Tri.leaf := Tri.del_eq_none_iff.mp hr
          subst hrl
          exact ⟨_, shrinks_dropRight l⟩
      | some r' =>
          rw [hr] at h
          simp only [Tri.graftTwo, Option.some.injEq] at h
          subst h
          obtain ⟨g, hgs⟩ := ihr r' hr
          exact ⟨_, (Shrinks.refl l).two hgs⟩

/-! ### The shrunk shape -/

/-- A neck of two or more vertices, or one carrying a decoration, has at least
two vertices. -/
lemma two_le_realiseAux_size (b : Option Tri) (bs : List (Option Tri)) :
    2 ≤ (realiseAux (b :: bs)).size := by
  have h := Tri.size_pos (realiseAux bs)
  cases b with
  | none => simp only [realiseAux, Tri.size]; omega
  | some d => have := Tri.size_pos d; simp only [realiseAux, Tri.size]; omega

/-- **`thm:shape-connected`**: deleting one leaf of a realisation of two or more
vertices, a leaf of the first nonempty decoration if there is one and the exit
otherwise, leaves a decorated neck of one vertex less, and the deletion is a
`1`-shrink carrying the exit to the exit. -/
theorem exists_shrinks_realiseAux : ∀ l : List (Option Tri), 2 ≤ (realiseAux l).size →
    ∃ (l' : List (Option Tri)) (f : Word → Word),
      (realiseAux l').size + 1 = (realiseAux l).size ∧
      f (Shape.neckAddr l) = Shape.neckAddr l' ∧
      Shrinks 1 (realiseAux l) (realiseAux l') f := by
  intro l
  induction l with
  | nil => intro h; simp [realiseAux, Tri.size] at h
  | cons b bs ih =>
      intro _
      cases b with
      | none =>
          cases bs with
          | nil =>
              refine ⟨[], fun _ => [], ?_, rfl, shrinks_collapse⟩
              simp [realiseAux, Tri.size]
          | cons c cs =>
              obtain ⟨bs', g, hsize, hneck, hshr⟩ := ih (two_le_realiseAux_size c cs)
              refine ⟨none :: bs', branch g id, ?_, ?_, hshr.one⟩
              · simp only [realiseAux, Tri.size]; omega
              · simp [hneck]
      | some d =>
          by_cases hd : d = Tri.leaf
          · subst hd
            refine ⟨none :: bs, slide, ?_, rfl, shrinks_slide _⟩
            simp only [realiseAux, Tri.size]; omega
          · obtain ⟨d', hd'⟩ : ∃ d', d.del = some d' :=
              Option.ne_none_iff_exists'.mp fun hc => hd (Tri.del_eq_none_iff.mp hc)
            obtain ⟨g, hg⟩ := Tri.exists_shrinks_del d d' hd'
            have hsz := Tri.optSize_del d
            rw [hd', Tri.optSize_some] at hsz
            refine ⟨some d' :: bs, branch g id, ?_, rfl, hg.two (Shrinks.refl _)⟩
            simp only [realiseAux, Tri.size]
            omega

/-- A `1`-shrink carrying the exit to the exit is a `1`-marked quasi-isometry
of the marked spaces. -/
lemma markedQI_one_of_shrinks {l l' : List (Option Tri)} {f : Word → Word}
    (hf : Shrinks 1 (realiseAux l) (realiseAux l') f)
    (hneck : f (Shape.neckAddr l) = Shape.neckAddr l') :
    MarkedQI 1 (listSpace l) (listSpace l') := by
  refine ⟨fun w => ⟨f w.1, hf.maps w.1 w.2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    have h := hf.upper a.1 b.1 a.2 b.2
    simp only [dist_listSpace, one_mul]
    exact_mod_cast h
  · intro a b
    have h := hf.lower a.1 b.1 a.2 b.2
    simp only [dist_listSpace, one_mul, mul_one]
    exact_mod_cast h
  · intro y
    obtain ⟨w, hw, hfw⟩ := hf.surj y.1 y.2
    refine ⟨⟨w, hw⟩, ?_⟩
    simp only [dist_listSpace, hfw, treeDist_self]
    norm_num
  · simp only [dist_listSpace, entry_listSpace, hf.root, treeDist_self]
    norm_num
  · simp only [dist_listSpace, exit_listSpace, hneck, treeDist_self]
    norm_num

/-- **`thm:shape-connected`**: every shape of size at least two admits a
`1`-marked quasi-isometry onto a shape of size one less, the deletion of a leaf
of its realisation. -/
theorem exists_markedQI_shrink (σ : Shape) (hσ : 2 ≤ σ.size) :
    ∃ τ : Shape, τ.size + 1 = σ.size ∧ MarkedQI 1 (shapeSpace σ) (shapeSpace τ) := by
  have hs : σ.size = (realiseAux σ.decs).size := rfl
  obtain ⟨l', f, hsize, hneck, hshr⟩ := exists_shrinks_realiseAux σ.decs (hs ▸ hσ)
  have hs' : (Shape.ofList l').size = (realiseAux l').size := by
    simp only [Shape.size, Shape.realise, Shape.decs_ofList]
  refine ⟨Shape.ofList l', by rw [hs', hs]; exact hsize, ?_⟩
  rw [shapeSpace_ofList, shapeSpace]
  exact markedQI_one_of_shrinks hshr hneck

/-! ### The enumeration of the shapes by size -/

/-- The standard bijection of the words with the naturals, which lists the
shorter words first. -/
def numOf : Word → ℕ
  | [] => 0
  | false :: w => 2 * numOf w + 1
  | true :: w => 2 * numOf w + 2

/-- The empty word comes first. -/
@[simp] lemma numOf_nil : numOf [] = 0 := rfl

/-- The value of a word beginning with the first letter. -/
@[simp] lemma numOf_false (w : Word) : numOf (false :: w) = 2 * numOf w + 1 := rfl

/-- The value of a word beginning with the second letter. -/
@[simp] lemma numOf_true (w : Word) : numOf (true :: w) = 2 * numOf w + 2 := rfl

/-- The words of length `k` fill the block from `2^k - 1` to `2^{k+1} - 2`. -/
lemma numOf_bounds (w : Word) :
    2 ^ w.length ≤ numOf w + 1 ∧ numOf w + 2 ≤ 2 ^ (w.length + 1) := by
  induction w with
  | nil => simp
  | cons b w ih =>
      obtain ⟨h1, h2⟩ := ih
      have hp : 2 ^ (w.length + 1) = 2 * 2 ^ w.length := by ring
      have hp2 : 2 ^ (w.length + 1 + 1) = 2 * 2 ^ (w.length + 1) := by ring
      cases b <;> simp only [numOf_false, numOf_true, List.length_cons] <;> omega

/-- The shorter of two words comes first. -/
lemma numOf_lt_of_length_lt {u v : Word} (h : u.length < v.length) : numOf u < numOf v := by
  obtain ⟨h1, h2⟩ := numOf_bounds u
  obtain ⟨h3, h4⟩ := numOf_bounds v
  have : (2 : ℕ) ^ (u.length + 1) ≤ 2 ^ v.length := Nat.pow_le_pow_right (by norm_num) h
  omega

/-- Distinct words carry distinct numbers. -/
lemma numOf_injective : Function.Injective numOf := by
  intro u
  induction u with
  | nil =>
      intro v h
      cases v with
      | nil => rfl
      | cons b v =>
          exfalso
          have := numOf_lt_of_length_lt (u := ([] : Word)) (v := b :: v) (by simp)
          omega
  | cons a u ih =>
      intro v h
      cases v with
      | nil =>
          exfalso
          have := numOf_lt_of_length_lt (u := ([] : Word)) (v := a :: u) (by simp)
          omega
      | cons b v =>
          cases a with
          | false =>
              cases b with
              | false =>
                  have h2 : numOf u = numOf v := by simp only [numOf_false] at h; omega
                  rw [ih h2]
              | true => exfalso; simp only [numOf_false, numOf_true] at h; omega
          | true =>
              cases b with
              | false => exfalso; simp only [numOf_false, numOf_true] at h; omega
              | true =>
                  have h2 : numOf u = numOf v := by simp only [numOf_true] at h; omega
                  rw [ih h2]

/-- A decorated neck is read off its realisation. -/
lemma Shape.realiseAux_injective : Function.Injective realiseAux := by
  intro l
  induction l with
  | nil =>
      intro l' h
      cases l' with
      | nil => rfl
      | cons c cs => cases c <;> simp [realiseAux] at h
  | cons b bs ih =>
      intro l' h
      cases l' with
      | nil => cases b <;> simp [realiseAux] at h
      | cons c cs =>
          cases b with
          | none =>
              cases c with
              | none =>
                  simp only [realiseAux, Tri.one.injEq] at h
                  rw [ih h]
              | some e => simp [realiseAux] at h
          | some d =>
              cases c with
              | none => simp [realiseAux] at h
              | some e =>
                  simp only [realiseAux, Tri.two.injEq] at h
                  obtain ⟨rfl, h2⟩ := h
                  rw [ih h2]

/-- A shape is determined by its decorations in neck order. -/
lemma Shape.eq_of_decs_eq {σ τ : Shape} (h : σ.decs = τ.decs) : σ = τ := by
  have hn : σ.necks = τ.necks := by
    have hl := congrArg List.length h
    rwa [Shape.decs_length, Shape.decs_length] at hl
  obtain ⟨n, f⟩ := σ
  obtain ⟨m, g⟩ := τ
  simp only at hn
  subst hn
  simp only [Shape.mk.injEq, heq_eq_eq, true_and]
  exact List.ofFn_injective h

/-- **`def:shape`**: a shape is determined by its realisation. -/
lemma Shape.realise_injective : Function.Injective Shape.realise :=
  fun _ _ h => Shape.eq_of_decs_eq (Shape.realiseAux_injective h)

/-- The key of the enumeration: the code of the realisation read as a number,
so that a larger shape has a larger key. -/
def shapeKey (σ : Shape) : ℕ := numOf σ.realise.code

/-- The key determines the shape. -/
lemma shapeKey_injective : Function.Injective shapeKey := fun _ _ h =>
  Shape.realise_injective (Tri.code_injective (numOf_injective h))

/-- The key grows with the size, which is what makes the enumeration one by
size. -/
lemma shapeKey_lt_of_size_lt {σ τ : Shape} (h : σ.size < τ.size) : shapeKey σ < shapeKey τ := by
  refine numOf_lt_of_length_lt ?_
  rw [Tri.code_length, Tri.code_length]
  have : σ.realise.size < τ.realise.size := h
  omega

/-- `𝒮` is infinite: the bare paths have every size. -/
instance : Infinite Shape := by
  refine Infinite.of_injective (fun n : ℕ => Shape.ofList (List.replicate n (none : Option Tri)))
    fun n m h => ?_
  have hs := congrArg Shape.size h
  rw [Shape.size_ofList, Shape.size_ofList, Shape.sum_optSize_replicate,
    Shape.sum_optSize_replicate, List.length_replicate, List.length_replicate] at hs
  omega

/-- One key occurs for each of the infinitely many shapes. -/
lemma shapeKey_range_infinite : (setOf (fun k => k ∈ Set.range shapeKey)).Infinite := by
  rw [Set.setOf_mem_eq]
  exact Set.infinite_range_of_injective shapeKey_injective

/-- **`def:shape-net`**: the enumeration of `𝒮` by size, the ties broken by the
key. -/
noncomputable def shapeEnum (n : ℕ) : Shape :=
  Function.invFun shapeKey (Nat.nth (fun k => k ∈ Set.range shapeKey) n)

/-- The `n`-th shape carries the `n`-th key. -/
lemma shapeKey_shapeEnum (n : ℕ) :
    shapeKey (shapeEnum n) = Nat.nth (fun k => k ∈ Set.range shapeKey) n :=
  Function.invFun_eq (Nat.nth_mem_of_infinite shapeKey_range_infinite n)

/-- The enumeration lists each shape once. -/
lemma shapeEnum_injective : Function.Injective shapeEnum := by
  intro m n h
  have hk := congrArg shapeKey h
  rw [shapeKey_shapeEnum, shapeKey_shapeEnum] at hk
  exact Nat.nth_injective shapeKey_range_infinite hk

/-- The enumeration lists every shape. -/
lemma shapeEnum_surjective : Function.Surjective shapeEnum := by
  classical
  intro σ
  refine ⟨Nat.count (fun k => k ∈ Set.range shapeKey) (shapeKey σ), shapeKey_injective ?_⟩
  rw [shapeKey_shapeEnum]
  exact Nat.nth_count (p := fun k => k ∈ Set.range shapeKey) ⟨σ, rfl⟩

/-- **`def:shape-net`**: the enumeration is by size. -/
lemma size_shapeEnum_monotone : Monotone fun n => (shapeEnum n).size := by
  intro m n hmn
  by_contra hlt
  push Not at hlt
  have h1 := shapeKey_lt_of_size_lt hlt
  rw [shapeKey_shapeEnum, shapeKey_shapeEnum] at h1
  have := (Nat.nth_lt_nth shapeKey_range_infinite).mp h1
  omega

/-- **`def:shape-net`**: the shapes enumerated by size, as marked spaces. -/
noncomputable def shapeFamily (n : ℕ) : MarkedSpace := shapeSpace (shapeEnum n)

/-! ### The net on shapes -/

/-- The one-vertex shape, the least in the enumeration by size. -/
lemma size_ofList_nil : (Shape.ofList []).size = 1 := by
  simp only [Shape.size, Shape.realise, Shape.decs_ofList]
  rfl

/-- **`thm:shape-net`** and **`thm:shape-connected`** at shapes: over an
enumeration of `𝒮` by size, the label graph `G_D` is connected. -/
theorem netLink_connected_shape {Dq : ℝ} (hD : 1 ≤ Dq) (E : ℕ → Shape)
    (hinj : Function.Injective E) (hsurj : Function.Surjective E)
    (hmono : Monotone fun n => (E n).size) {a b : ℕ}
    (ha : netMem (fun n => shapeSpace (E n)) Dq a)
    (hb : netMem (fun n => shapeSpace (E n)) Dq b) :
    Relation.ReflTransGen (NetLink (fun n => shapeSpace (E n)) Dq) a b := by
  have hzero : (E 0).size ≤ 1 := by
    obtain ⟨k, hk⟩ := hsurj (Shape.ofList [])
    have h := hmono (Nat.zero_le k)
    simp only [hk, size_ofList_nil] at h
    exact h
  refine netLink_connected _ Dq hD hmono (fun n hn => hinj (Shape.eq_of_size_le_one hn hzero))
    (fun n hn => ?_) ha hb
  obtain ⟨τ, hsize, hqi⟩ := exists_markedQI_shrink (E n) hn
  obtain ⟨m, rfl⟩ := hsurj τ
  exact ⟨m, by omega, hqi⟩

/-- **`thm:shape-net`**: `|rep_D(σ)| ≤ |σ|` for the net on shapes. -/
theorem size_repIdx_le {Dq : ℝ} (hD : 1 ≤ Dq) (n : ℕ) :
    (shapeEnum (repIdx shapeFamily Dq n)).size ≤ (shapeEnum n).size :=
  sz_repIdx_le shapeFamily Dq hD size_shapeEnum_monotone n

/-- **`thm:shape-connected`**: the label graph `G_D` on the shapes enumerated by
size is connected. -/
theorem netLink_connected_shapeFamily {Dq : ℝ} (hD : 1 ≤ Dq) {a b : ℕ}
    (ha : netMem shapeFamily Dq a) (hb : netMem shapeFamily Dq b) :
    Relation.ReflTransGen (NetLink shapeFamily Dq) a b :=
  netLink_connected_shape hD shapeEnum shapeEnum_injective shapeEnum_surjective
    size_shapeEnum_monotone ha hb

end ChainClasses
