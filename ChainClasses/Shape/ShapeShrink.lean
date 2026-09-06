import Mathlib.Tactic
import ChainClasses.Shape.ShapeMetric

/-!
The two geometric steps of `sec:shapes` that the metric on realisations makes
reachable: the collapse of a shape of small diameter in `thm:shape-eta`, and
the support fix of `thm:shape-shrink` (`it:shape-fix`).

* `Tri.treeDist_lt_size`: a tree with `n` vertices has diameter at most `n-1`,
  so a shape of size at most `D²` collapses onto the one-vertex shape.
* `markedQI_collapse`, `repIdx_shapeFamily_eq_zero_of_size_le`: the collapse
  and its consequence, that every class other than `v₀` has all its members of
  size exceeding `D²`, which is the hypothesis `hgvan` of `shape_eta_le`.
* `Tri.Full`, `Shape.Supported`: the support of the shape law when
  `θ₁' = 0`, namely a bush at every interior neck vertex and no bush vertex
  with exactly one child.
* `Tri.fix`, `Shape.fix`, `fixMap`: the support fix, attaching a one-vertex
  bush at every bare neck vertex and a leaf at every bush vertex with one
  child, together with the address map that carries the neck of a shape onto
  the neck of its fix.
* `markedQI_shape_fix`, `size_fix_le`, `fix_eq_self`: the three clauses of
  `thm:shape-shrink` (`it:shape-fix`).
-/

namespace ChainClasses

open Shape (realiseAux)

/-! ### The diameter of a finite tree -/

/-- The depth of a tree is less than its size: the addresses down to a vertex
are distinct vertices. -/
lemma Tri.length_lt_size : ∀ (t : Tri) {w : Word}, t.IsAddr w → w.length < t.size := by
  intro t
  induction t with
  | leaf =>
      intro w hw
      rw [Tri.eq_nil_of_isAddr_leaf hw]
      simp [Tri.size]
  | one t ih =>
      intro w hw
      cases w with
      | nil =>
          have := t.size_pos
          simp only [Tri.size, List.length_nil]
          omega
      | cons a w =>
          cases a with
          | false =>
              have := ih (Tri.isAddr_one_false t w |>.mp hw)
              simp only [Tri.size, List.length_cons]
              omega
          | true => exact absurd hw (Tri.isAddr_one_true t w)
  | two l r ihl ihr =>
      intro w hw
      cases w with
      | nil =>
          have := l.size_pos
          have := r.size_pos
          simp only [Tri.size, List.length_nil]
          omega
      | cons a w =>
          cases a with
          | false =>
              have := ihl (Tri.isAddr_two_false l r w |>.mp hw)
              have := r.size_pos
              simp only [Tri.size, List.length_cons]
              omega
          | true =>
              have := ihr (Tri.isAddr_two_true l r w |>.mp hw)
              have := l.size_pos
              simp only [Tri.size, List.length_cons]
              omega

/-- **The diameter of a tree with `n` vertices is at most `n-1`**: the geodesic
between two vertices runs through distinct vertices of the tree. -/
lemma Tri.treeDist_lt_size : ∀ (t : Tri) {u v : Word}, t.IsAddr u → t.IsAddr v →
    treeDist u v < t.size := by
  intro t
  induction t with
  | leaf =>
      intro u v hu hv
      rw [Tri.eq_nil_of_isAddr_leaf hu, Tri.eq_nil_of_isAddr_leaf hv]
      simp [Tri.size]
  | one t ih =>
      intro u v hu hv
      have hdepth : ∀ {w : Word}, (Tri.one t).IsAddr w → w.length < (Tri.one t).size :=
        fun hw => Tri.length_lt_size _ hw
      cases u with
      | nil =>
          rw [treeDist_nil_left]
          exact hdepth hv
      | cons a u =>
          cases v with
          | nil =>
              rw [treeDist_nil_right]
              exact hdepth hu
          | cons b v =>
              cases a with
              | true => exact absurd hu (Tri.isAddr_one_true t u)
              | false =>
                  cases b with
                  | true => exact absurd hv (Tri.isAddr_one_true t v)
                  | false =>
                      rw [treeDist_cons_cons_self]
                      have := ih hu hv
                      simp only [Tri.size]
                      omega
  | two l r ihl ihr =>
      intro u v hu hv
      have hdepth : ∀ {w : Word}, (Tri.two l r).IsAddr w → w.length < (Tri.two l r).size :=
        fun hw => Tri.length_lt_size _ hw
      cases u with
      | nil =>
          rw [treeDist_nil_left]
          exact hdepth hv
      | cons a u =>
          cases v with
          | nil =>
              rw [treeDist_nil_right]
              exact hdepth hu
          | cons b v =>
              cases a with
              | false =>
                  cases b with
                  | false =>
                      rw [treeDist_cons_cons_self]
                      have := ihl hu hv
                      have := r.size_pos
                      simp only [Tri.size]
                      omega
                  | true =>
                      rw [treeDist_false_true]
                      have h1 := Tri.length_lt_size l hu
                      have h2 := Tri.length_lt_size r hv
                      simp only [Tri.size]
                      omega
              | true =>
                  cases b with
                  | false =>
                      rw [treeDist_true_false]
                      have h1 := Tri.length_lt_size r hu
                      have h2 := Tri.length_lt_size l hv
                      simp only [Tri.size]
                      omega
                  | true =>
                      rw [treeDist_cons_cons_self]
                      have := ihr hu hv
                      have := l.size_pos
                      simp only [Tri.size]
                      omega

/-! ### The collapse of a shape of small diameter -/

/-- The one-vertex shape has a single vertex. -/
instance : Subsingleton (listSpace []).carrier := by
  refine ⟨fun u v => Subtype.ext ?_⟩
  rw [Tri.eq_nil_of_isAddr_leaf u.2, Tri.eq_nil_of_isAddr_leaf v.2]

/-- **`thm:shape-eta`, the collapse**: a shape of size at most `K²` is
`K`-comparable to the one-vertex shape, the map sending every vertex to the one
vertex. -/
theorem markedQI_collapse {K : ℝ} (hK : 1 ≤ K) (σ : Shape) (hσ : (σ.size : ℝ) ≤ K * K) :
    MarkedQI K (shapeSpace σ) (listSpace []) := by
  refine markedQI_of_subsingleton hK fun a b => ?_
  have h : treeDist a.1 b.1 < σ.size := Tri.treeDist_lt_size _ a.2 b.2
  have hle : (treeDist a.1 b.1 : ℝ) ≤ (σ.size : ℝ) := by exact_mod_cast h.le
  show (treeDist a.1 b.1 : ℝ) ≤ K * K
  exact hle.trans hσ

/-- **`thm:shape-eta`, the hypothesis `hgvan`**: at scale `D` every shape of
size at most `D²` is represented by the one-vertex shape, so every class other
than `v₀` has all its members of size exceeding `D²`. -/
theorem repIdx_shapeFamily_eq_zero_of_size_le {Dq : ℝ} (hD : 1 ≤ Dq) {n : ℕ}
    (h : ((shapeEnum n).size : ℝ) ≤ Dq * Dq) :
    repIdx shapeFamily Dq n = 0 := by
  refine repIdx_eq_zero shapeFamily Dq ?_
  have hzero : shapeFamily 0 = listSpace [] := by
    have h0 : (shapeEnum 0).size ≤ 1 := by
      obtain ⟨m, hm⟩ := shapeEnum_surjective (Shape.ofList [])
      have hmono := size_shapeEnum_monotone (Nat.zero_le m)
      simp only [hm, size_ofList_nil] at hmono
      exact hmono
    have := Shape.eq_of_size_le_one h0 (le_of_eq size_ofList_nil)
    rw [shapeFamily, this, shapeSpace_ofList]
  rw [hzero]
  exact markedQI_collapse hD _ h

/-! ### The support of the shape law at `θ₁' = 0` -/

/-- A tree with no vertex of exactly one child: the bushes of the shape law
when `θ₁' = 0`, the conjugate law then charging only `0` and `2`. -/
def Tri.Full : Tri → Prop
  | .leaf => True
  | .one _ => False
  | .two l r => l.Full ∧ r.Full

/-- A decoration in the support: present, and full. -/
def Tri.optFull : Option Tri → Prop
  | none => False
  | some t => t.Full

/-- **`thm:shape-shrink`, the support at `θ₁' = 0`**: a bush at every interior
neck vertex, and no bush vertex with exactly one child. -/
def Shape.Supported (σ : Shape) : Prop := ∀ b ∈ σ.decs, Tri.optFull b

/-! ### The fix -/

/-- Attach a leaf at every vertex with exactly one child. -/
def Tri.fix : Tri → Tri
  | .leaf => .leaf
  | .one t => .two t.fix .leaf
  | .two l r => .two l.fix r.fix

/-- Attach a one-vertex bush at a bare neck vertex, and fix the bush of a
decorated one. -/
def Tri.optFix : Option Tri → Option Tri
  | none => some .leaf
  | some t => some t.fix

@[simp] lemma Tri.optFix_none : Tri.optFix none = some Tri.leaf := rfl

@[simp] lemma Tri.optFix_some (t : Tri) : Tri.optFix (some t) = some t.fix := rfl

/-- The fix lands in the support. -/
lemma Tri.full_fix : ∀ t : Tri, t.fix.Full
  | .leaf => trivial
  | .one t => ⟨t.full_fix, trivial⟩
  | .two l r => ⟨l.full_fix, r.full_fix⟩

lemma Tri.optFull_optFix (b : Option Tri) : Tri.optFull (Tri.optFix b) := by
  cases b with
  | none => exact trivial
  | some t => exact t.full_fix

/-- The fix at most doubles the size: each added leaf is charged to a distinct
vertex. -/
lemma Tri.size_fix_le : ∀ t : Tri, t.fix.size ≤ 2 * t.size
  | .leaf => by simp [Tri.fix, Tri.size]
  | .one t => by
      have := t.size_fix_le
      simp only [Tri.fix, Tri.size]
      omega
  | .two l r => by
      have := l.size_fix_le
      have := r.size_fix_le
      simp only [Tri.fix, Tri.size]
      omega

lemma Tri.optSize_optFix_le (b : Option Tri) :
    Tri.optSize (Tri.optFix b) ≤ 2 * Tri.optSize b + 1 := by
  cases b with
  | none => simp [Tri.optFix, Tri.optSize, Tri.size]
  | some t =>
      have := t.size_fix_le
      simpa using this.trans (by omega)

/-- A tree already in the support is its own fix. -/
lemma Tri.fix_of_full : ∀ {t : Tri}, t.Full → t.fix = t
  | .leaf, _ => rfl
  | .one _, h => absurd h id
  | .two l r, h => by
      rw [Tri.fix, Tri.fix_of_full h.1, Tri.fix_of_full h.2]

lemma Tri.optFix_of_optFull : ∀ {b : Option Tri}, Tri.optFull b → Tri.optFix b = b
  | none, h => absurd h id
  | some _, h => by rw [Tri.optFix, Tri.fix_of_full h]

/-- The fix only adds addresses. -/
lemma Tri.isAddr_fix : ∀ (t : Tri) {w : Word}, t.IsAddr w → t.fix.IsAddr w := by
  intro t
  induction t with
  | leaf =>
      intro w hw
      rw [Tri.eq_nil_of_isAddr_leaf hw]
      simp
  | one t ih =>
      intro w hw
      cases w with
      | nil => simp
      | cons a w =>
          cases a with
          | false => exact ih hw
          | true => exact absurd hw (Tri.isAddr_one_true t w)
  | two l r ihl ihr =>
      intro w hw
      cases w with
      | nil => simp
      | cons a w => cases a with
        | false => exact ihl hw
        | true => exact ihr hw

/-- The added vertices are leaves hanging one step below a vertex of the
original tree, so the inclusion has `1`-dense image. -/
lemma Tri.exists_isAddr_near : ∀ (t : Tri) {y : Word}, t.fix.IsAddr y →
    ∃ w, t.IsAddr w ∧ treeDist w y ≤ 1 := by
  intro t
  induction t with
  | leaf =>
      intro y hy
      rw [Tri.eq_nil_of_isAddr_leaf hy]
      exact ⟨[], by simp, by simp⟩
  | one t ih =>
      intro y hy
      cases y with
      | nil => exact ⟨[], by simp, by simp⟩
      | cons a y =>
          cases a with
          | false =>
              obtain ⟨w, hw, hd⟩ := ih hy
              exact ⟨false :: w, hw, by rwa [treeDist_cons_cons_self]⟩
          | true =>
              rw [Tri.eq_nil_of_isAddr_leaf hy]
              exact ⟨[], by simp, by simp⟩
  | two l r ihl ihr =>
      intro y hy
      cases y with
      | nil => exact ⟨[], by simp, by simp⟩
      | cons a y =>
          cases a with
          | false =>
              obtain ⟨w, hw, hd⟩ := ihl hy
              exact ⟨false :: w, hw, by rwa [treeDist_cons_cons_self]⟩
          | true =>
              obtain ⟨w, hw, hd⟩ := ihr hy
              exact ⟨true :: w, hw, by rwa [treeDist_cons_cons_self]⟩

/-! ### The address map of the fix -/

/-- The address map of the support fix.  A bare neck vertex acquires a bush, so
the neck slides from `false` to `true` there; a decorated one keeps its neck
letter and its bush addresses. -/
def fixMap : List (Option Tri) → Word → Word
  | [], w => w
  | none :: _, [] => []
  | none :: bs, false :: w => true :: fixMap bs w
  | none :: _, true :: w => true :: w
  | some _ :: _, [] => []
  | some _ :: _, false :: w => false :: w
  | some _ :: bs, true :: w => true :: fixMap bs w

@[simp] lemma fixMap_nil_word : ∀ l : List (Option Tri), fixMap l [] = []
  | [] => rfl
  | none :: _ => rfl
  | some _ :: _ => rfl

/-- The map preserves depth: every step consumes one letter and emits one. -/
lemma fixMap_length : ∀ (l : List (Option Tri)) (w : Word), (fixMap l w).length = w.length
  | [], w => rfl
  | none :: _, [] => rfl
  | none :: bs, false :: w => by simp [fixMap, fixMap_length bs w]
  | none :: _, true :: w => by simp [fixMap]
  | some _ :: _, [] => rfl
  | some _ :: _, false :: w => by simp [fixMap]
  | some _ :: bs, true :: w => by simp [fixMap, fixMap_length bs w]

/-- The map lands in the fixed realisation. -/
lemma isAddr_fixMap : ∀ (l : List (Option Tri)) {w : Word}, (realiseAux l).IsAddr w →
    (realiseAux (l.map Tri.optFix)).IsAddr (fixMap l w) := by
  intro l
  induction l with
  | nil =>
      intro w hw
      rw [Tri.eq_nil_of_isAddr_leaf hw]
      simp
  | cons b bs ih =>
      cases b with
      | none =>
          intro w hw
          cases w with
          | nil => simp
          | cons a w =>
              cases a with
              | false => exact ih hw
              | true => exact absurd hw (Tri.isAddr_one_true _ w)
      | some t =>
          intro w hw
          cases w with
          | nil => simp
          | cons a w =>
              cases a with
              | false => exact Tri.isAddr_fix t hw
              | true => exact ih hw

/-- The map preserves distances: it is a relabelling of the letters along the
neck, not a change of shape. -/
lemma treeDist_fixMap : ∀ (l : List (Option Tri)) {u v : Word},
    (realiseAux l).IsAddr u → (realiseAux l).IsAddr v →
    treeDist (fixMap l u) (fixMap l v) = treeDist u v := by
  intro l
  induction l with
  | nil =>
      intro u v hu hv
      rw [Tri.eq_nil_of_isAddr_leaf hu, Tri.eq_nil_of_isAddr_leaf hv]
      rfl
  | cons b bs ih =>
      cases b with
      | none =>
          intro u v hu hv
          cases u with
          | nil =>
              cases v with
              | nil => rfl
              | cons a v =>
                  cases a with
                  | true => exact absurd hv (Tri.isAddr_one_true _ v)
                  | false =>
                      simp only [fixMap, treeDist_nil_left,
                        List.length_cons, fixMap_length]
          | cons a u =>
              cases a with
              | true => exact absurd hu (Tri.isAddr_one_true _ u)
              | false =>
                  cases v with
                  | nil =>
                      simp only [fixMap, treeDist_nil_right,
                        List.length_cons, fixMap_length]
                  | cons a' v =>
                      cases a' with
                      | true => exact absurd hv (Tri.isAddr_one_true _ v)
                      | false =>
                          simp only [fixMap, treeDist_cons_cons_self]
                          exact ih hu hv
      | some t =>
          intro u v hu hv
          cases u with
          | nil =>
              cases v with
              | nil => rfl
              | cons a v =>
                  cases a with
                  | false =>
                      simp only [fixMap, treeDist_nil_left]
                  | true =>
                      simp only [fixMap, treeDist_nil_left,
                        List.length_cons, fixMap_length]
          | cons a u =>
              cases a with
              | false =>
                  cases v with
                  | nil => simp only [fixMap, treeDist_nil_right]
                  | cons a' v =>
                      cases a' with
                      | false => simp only [fixMap]
                      | true =>
                          simp only [fixMap, treeDist_false_true, fixMap_length]
              | true =>
                  cases v with
                  | nil =>
                      simp only [fixMap, treeDist_nil_right,
                        List.length_cons, fixMap_length]
                  | cons a' v =>
                      cases a' with
                      | false =>
                          simp only [fixMap, treeDist_true_false, fixMap_length]
                      | true =>
                          simp only [fixMap, treeDist_cons_cons_self]
                          exact ih hu hv

/-- The image is `1`-dense: the only vertices it misses are the added leaves,
each adjacent to a vertex it hits. -/
lemma dense_fixMap : ∀ (l : List (Option Tri)) {y : Word},
    (realiseAux (l.map Tri.optFix)).IsAddr y →
    ∃ w, (realiseAux l).IsAddr w ∧ treeDist (fixMap l w) y ≤ 1 := by
  intro l
  induction l with
  | nil =>
      intro y hy
      rw [Tri.eq_nil_of_isAddr_leaf hy]
      exact ⟨[], by simp, by simp⟩
  | cons b bs ih =>
      cases b with
      | none =>
          intro y hy
          cases y with
          | nil => exact ⟨[], by simp, by simp⟩
          | cons a y =>
              cases a with
              | false =>
                  rw [Tri.eq_nil_of_isAddr_leaf hy]
                  exact ⟨[], by simp, by simp⟩
              | true =>
                  obtain ⟨w, hw, hd⟩ := ih hy
                  exact ⟨false :: w, hw, by simpa [fixMap] using hd⟩
      | some t =>
          intro y hy
          cases y with
          | nil => exact ⟨[], by simp, by simp⟩
          | cons a y =>
              cases a with
              | false =>
                  obtain ⟨w, hw, hd⟩ := Tri.exists_isAddr_near t hy
                  exact ⟨false :: w, hw, by simpa [fixMap] using hd⟩
              | true =>
                  obtain ⟨w, hw, hd⟩ := ih hy
                  exact ⟨true :: w, hw, by simpa [fixMap] using hd⟩

/-- The neck of a shape is carried onto the neck of its fix, every neck vertex
of the fix being decorated. -/
lemma fixMap_neckAddr : ∀ l : List (Option Tri),
    fixMap l (Shape.neckAddr l) = Shape.neckAddr (l.map Tri.optFix)
  | [] => rfl
  | none :: bs => by
      simp only [Shape.neckAddr_none, fixMap, List.map_cons, Tri.optFix_none,
        Shape.neckAddr_some, List.cons.injEq, true_and]
      exact fixMap_neckAddr bs
  | some t :: bs => by
      simp only [Shape.neckAddr_some, fixMap, List.map_cons, Tri.optFix_some,
        List.cons.injEq, true_and]
      exact fixMap_neckAddr bs

/-! ### The support fix as a marked quasi-isometry -/

/-- A distance-preserving address map with `1`-dense image carrying root to
root and exit to exit is a `1`-marked quasi-isometry. -/
lemma markedQI_one_of_isom {l l' : List (Option Tri)} {f : Word → Word}
    (hmaps : ∀ w, (realiseAux l).IsAddr w → (realiseAux l').IsAddr (f w))
    (hdist : ∀ u v, (realiseAux l).IsAddr u → (realiseAux l).IsAddr v →
      treeDist (f u) (f v) = treeDist u v)
    (hdense : ∀ y, (realiseAux l').IsAddr y →
      ∃ w, (realiseAux l).IsAddr w ∧ treeDist (f w) y ≤ 1)
    (hroot : f [] = []) (hneck : f (Shape.neckAddr l) = Shape.neckAddr l') :
    MarkedQI 1 (listSpace l) (listSpace l') := by
  refine ⟨fun w => ⟨f w.1, hmaps w.1 w.2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    have h := hdist a.1 b.1 a.2 b.2
    simp only [dist_listSpace, one_mul, h]
    have : (0 : ℝ) ≤ (treeDist a.1 b.1 : ℝ) := by positivity
    linarith
  · intro a b
    have h := hdist a.1 b.1 a.2 b.2
    simp only [dist_listSpace, one_mul, mul_one, h]
    have : (0 : ℝ) ≤ (treeDist a.1 b.1 : ℝ) := by positivity
    linarith
  · intro y
    obtain ⟨w, hw, hd⟩ := hdense y.1 y.2
    refine ⟨⟨w, hw⟩, ?_⟩
    simp only [dist_listSpace]
    exact_mod_cast hd
  · simp only [dist_listSpace, entry_listSpace, hroot, treeDist_self]
    norm_num
  · simp only [dist_listSpace, exit_listSpace, hneck, treeDist_self]
    norm_num

/-- **The support fix of a shape**: a bush at every bare interior neck vertex,
and a leaf at every bush vertex with one child. -/
def Shape.fix (σ : Shape) : Shape := Shape.ofList (σ.decs.map Tri.optFix)

@[simp] lemma Shape.decs_fix (σ : Shape) : σ.fix.decs = σ.decs.map Tri.optFix :=
  Shape.decs_ofList _

/-- **`thm:shape-shrink` (`it:shape-fix`)**: the fix lies in the
support. -/
theorem supported_fix (σ : Shape) : Shape.Supported σ.fix := by
  intro b hb
  rw [Shape.decs_fix, List.mem_map] at hb
  obtain ⟨c, -, rfl⟩ := hb
  exact Tri.optFull_optFix c

/-- The sum bound behind the size clause: each decoration at most doubles and
each bare neck vertex gains one vertex. -/
lemma sum_optSize_optFix_le : ∀ l : List (Option Tri),
    ((l.map Tri.optFix).map Tri.optSize).sum ≤ 2 * (l.map Tri.optSize).sum + l.length
  | [] => by simp
  | b :: bs => by
      have hb := Tri.optSize_optFix_le b
      have := sum_optSize_optFix_le bs
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- **`thm:shape-shrink` (`it:shape-fix`)**: the fix at most doubles
the size. -/
theorem size_fix_le (σ : Shape) : σ.fix.size ≤ 2 * σ.size := by
  have hsum := sum_optSize_optFix_le σ.decs
  have hσ := Shape.size_eq' σ
  rw [Shape.neckLen] at hσ
  rw [Shape.fix, Shape.size_ofList, List.length_map, Shape.decs_length]
  rw [Shape.decs_length] at hsum
  omega

/-- **`thm:shape-shrink` (`it:shape-fix`)**: a shape already in the
support is its own fix. -/
theorem fix_eq_self {σ : Shape} (hσ : Shape.Supported σ) : σ.fix = σ := by
  refine Shape.eq_of_decs_eq ?_
  rw [Shape.decs_fix]
  have key : ∀ l : List (Option Tri), (∀ b ∈ l, Tri.optFull b) → l.map Tri.optFix = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a as ih =>
        intro h
        rw [List.map_cons, Tri.optFix_of_optFull (h a (List.mem_cons_self ..)),
          ih fun b hb => h b (List.mem_cons_of_mem _ hb)]
  exact key σ.decs hσ

/-- **`thm:shape-shrink` (`it:shape-fix`)**: the inclusion of a shape
in its support fix is a `1`-marked, hence `2`-marked, quasi-isometry. -/
theorem markedQI_shape_fix (σ : Shape) : MarkedQI 1 (shapeSpace σ) (shapeSpace σ.fix) := by
  rw [shapeSpace, Shape.fix, shapeSpace_ofList]
  exact markedQI_one_of_isom (f := fixMap σ.decs)
    (fun w hw => isAddr_fixMap σ.decs hw)
    (fun u v hu hv => treeDist_fixMap σ.decs hu hv)
    (fun y hy => dense_fixMap σ.decs hy)
    (fixMap_nil_word σ.decs) (fixMap_neckAddr σ.decs)

/-- The same at the paper's scale. -/
theorem markedQI_two_shape_fix (σ : Shape) : MarkedQI 2 (shapeSpace σ) (shapeSpace σ.fix) :=
  (markedQI_shape_fix σ).mono zero_le_one (by norm_num)

end ChainClasses
