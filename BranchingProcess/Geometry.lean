/-
The coarse geometry of trees behind `thm:hair-separation` and `thm:three-rays`
of `gw_classes_simple.tex`.  Both propositions are deterministic statements
about arbitrary infinite trees, and both are proved here over Mathlib's
`SimpleGraph` in its graph metric.

* `IsQIWith`, `QuasiIsometric`: `def:qi` of `prelims.tex` with the three
  constants equal, read between two graphs in their graph metrics.
* `Between`: `m` lies on every walk from `u` to `v`.  The three tree facts the
  arguments run on are `between_of_mem_support`, `between_iff_dist_add` and
  `between_or`.
* `exists_between_dist_le`: the stability step.  In a tree every vertex
  separating the images of the endpoints is within `D` of the image of the
  source walk, so the stability constant of quasi-geodesics is `D` itself and
  no hyperbolicity enters.
* `IsRay`, `IsLine`: rays and lines as maps `ℕ → V` and `ℤ → V` that are
  isometric onto their images.  `IsLine.exists_far` is the form the separation
  consumes: one of the two half-rays runs away from any given vertex through
  the splitting point.
* `IsHair`: a component of the complement of a single vertex, of depth `h`,
  with `between_of_notMem_componentCompl` for the separation it provides.
* `not_quasiIsometric_of_hair_of_line`: `thm:hair-separation`.
* `rayGraph`, with `rayGraph_dist` and `rayGraph_isTree`: the ray `ℕ` with the
  path-graph structure.
* `IsRay.eq_of_between` and `dist_ray_branch`: a geodesic out of the initial
  vertex of a ray runs along the ray, and two rays meeting only at that vertex
  are at distance the sum of the parameters.
* `not_quasiIsometric_rayGraph`: `thm:three-rays`.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

namespace BranchingProcess

open SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}

/-! ### Quasi-isometries -/

/-- `f` is a `D`-quasi-isometry from `G` to `G'`: `def:qi` of `prelims.tex`
with all three constants equal to `D`, the lower bound carried in the
subtraction-free form `d ≤ D d' + D²`. -/
structure IsQIWith (D : ℕ) (G : SimpleGraph V) (G' : SimpleGraph V') (f : V → V') : Prop where
  upper : ∀ x y, G'.dist (f x) (f y) ≤ D * G.dist x y + D
  lower : ∀ x y, G.dist x y ≤ D * G'.dist (f x) (f y) + D * D
  dense : ∀ y', ∃ x, G'.dist (f x) y' ≤ D

/-- `G` and `G'` are quasi-isometric: some map is a `D`-quasi-isometry for
some `D`. -/
def QuasiIsometric (G : SimpleGraph V) (G' : SimpleGraph V') : Prop :=
  ∃ (D : ℕ) (f : V → V'), IsQIWith D G G' f

/-! ### Betweenness -/

/-- `m` lies between `u` and `v`: every walk from `u` to `v` meets `m`. -/
def Between (G : SimpleGraph V) (u m v : V) : Prop :=
  ∀ p : G.Walk u v, m ∈ p.support

/-- The left endpoint lies between itself and any vertex. -/
lemma between_left (G : SimpleGraph V) (u v : V) : Between G u u v :=
  fun p => p.start_mem_support

/-- Betweenness is symmetric in its outer arguments. -/
lemma Between.symm {u m v : V} (h : Between G u m v) : Between G v m u := by
  intro p
  have hp := h p.reverse
  rwa [Walk.support_reverse, List.mem_reverse] at hp

/-- A vertex between two others splits the distance. -/
lemma Between.dist_add (hG : G.Connected) {u m v : V} (h : Between G u m v) :
    G.dist u m + G.dist m v = G.dist u v := by
  classical
  obtain ⟨p, -, hlen⟩ := hG.exists_path_of_dist u v
  have hm : m ∈ p.support := h p
  have h1 : G.dist u m ≤ (p.takeUntil m hm).length := dist_le _
  have h2 : G.dist m v ≤ (p.dropUntil m hm).length := dist_le _
  have h3 : (p.takeUntil m hm).length + (p.dropUntil m hm).length = p.length := by
    rw [← Walk.length_append, p.take_spec hm]
  have h4 : G.dist u v ≤ G.dist u m + G.dist m v := hG.dist_triangle
  omega

/-- In a tree a vertex on one path from `u` to `v` lies on every walk from `u`
to `v`: the unique path is a bypass of every walk. -/
lemma between_of_mem_support (hG : G.IsTree) {u v m : V} {p : G.Walk u v}
    (hp : p.IsPath) (hm : m ∈ p.support) : Between G u m v := by
  classical
  intro q
  obtain ⟨r, -, hr⟩ := hG.existsUnique_path u v
  have hq : q.bypass = p := (hr _ q.bypass_isPath).trans (hr p hp).symm
  exact q.support_bypass_subset_support (by rw [hq]; exact hm)

/-- In a tree, betweenness is the additivity of the distance. -/
lemma between_iff_dist_add (hG : G.IsTree) {u m v : V} :
    Between G u m v ↔ G.dist u m + G.dist m v = G.dist u v := by
  refine ⟨fun h => h.dist_add hG.connected, fun h => ?_⟩
  obtain ⟨p, -, hp⟩ := hG.connected.exists_path_of_dist u m
  obtain ⟨q, -, hq⟩ := hG.connected.exists_path_of_dist m v
  have hlen : (p.append q).length = G.dist u v := by
    rw [Walk.length_append, hp, hq, h]
  exact between_of_mem_support hG ((p.append q).isPath_of_length_eq_dist hlen)
    ((Walk.mem_support_append_iff p q).2 (Or.inl p.end_mem_support))

/-- In a tree, a vertex separating `u` from `w` separates `u` from `v` or `v`
from `w`: the concatenation of the two paths through `v` is a walk from `u` to
`w`. -/
lemma between_or (hG : G.IsTree) {u m w : V} (h : Between G u m w) (v : V) :
    Between G u m v ∨ Between G v m w := by
  obtain ⟨p, hp, -⟩ := hG.connected.exists_path_of_dist u v
  obtain ⟨q, hq, -⟩ := hG.connected.exists_path_of_dist v w
  rcases (Walk.mem_support_append_iff p q).1 (h (p.append q)) with h1 | h1
  · exact Or.inl (between_of_mem_support hG hp h1)
  · exact Or.inr (between_of_mem_support hG hq h1)

/-! ### Stability of quasi-geodesics in a tree -/

/-- **Stability.** Let `f` be a `D`-quasi-isometry into a tree and let `m`
separate `f x` from `f y`.  Then some vertex of any walk from `x` to `y` has
its image within `D` of `m`.  Consecutive vertices of the walk have images at
distance at most `2D`, and a consecutive pair straddling `m` would be at
distance more than `2D` if both were more than `D` from `m`. -/
theorem exists_between_dist_le (hG' : G'.IsTree) {D : ℕ} {f : V → V'}
    (hf : IsQIWith D G G' f) {x y : V} (p : G.Walk x y) {m : V'}
    (hm : Between G' (f x) m (f y)) :
    ∃ i ≤ p.length, G'.dist (f (p.getVert i)) m ≤ D := by
  by_contra hcon
  have hcon : ∀ i, i ≤ p.length → D < G'.dist (f (p.getVert i)) m := by
    intro i hi
    by_contra hle
    exact hcon ⟨i, hi, not_lt.1 hle⟩
  have key : ∀ n, n ≤ p.length → ¬ Between G' (f x) m (f (p.getVert n)) := by
    intro n
    induction n with
    | zero =>
      intro _ hb
      have h0 : m ∈ (Walk.nil : G'.Walk (f (p.getVert 0)) (f (p.getVert 0))).support := by
        rw [p.getVert_zero] at hb ⊢
        exact hb Walk.nil
      rw [Walk.support_nil, List.mem_singleton] at h0
      have := hcon 0 (Nat.zero_le _)
      rw [h0, dist_self] at this
      omega
    | succ k ih =>
      intro hk hb
      rcases between_or hG' hb (f (p.getVert k)) with h1 | h1
      · exact ih (by omega) h1
      · have hd := h1.dist_add hG'.connected
        have hA := hcon k (by omega)
        have hB := hcon (k + 1) hk
        have hadj : G.Adj (p.getVert k) (p.getVert (k + 1)) := p.adj_getVert_succ (by omega)
        have hup := hf.upper (p.getVert k) (p.getVert (k + 1))
        rw [dist_eq_one_iff_adj.2 hadj] at hup
        rw [SimpleGraph.dist_comm (u := m) (v := f (p.getVert (k + 1)))] at hd
        omega
  exact key p.length le_rfl (by rw [p.getVert_length]; exact hm)

/-! ### Rays and lines -/

/-- A ray: a map `ℕ → V` isometric onto its image. -/
def IsRay (G : SimpleGraph V) (r : ℕ → V) : Prop :=
  ∀ m n, G.dist (r m) (r n) = Nat.dist m n

/-- A line: a map `ℤ → V` isometric onto its image. -/
def IsLine (G : SimpleGraph V) (l : ℤ → V) : Prop :=
  ∀ m n, G.dist (l m) (l n) = (m - n).natAbs

/-- A line leaves a vertex through two distinct neighbours. -/
lemma IsLine.ne {l : ℤ → V} (hl : IsLine G l) (k : ℤ) : l (k + 1) ≠ l (k - 1) := by
  intro h
  have := hl (k + 1) (k - 1)
  rw [h, dist_self] at this
  omega

/-- **The two half-rays.**  Given a vertex `w` and a parameter `k` on a line of
a tree, one of the two half-rays at `l k` runs away from `w` through `l k`: it
carries, at each distance `n`, a vertex `z` with `l k` between `w` and `z`. -/
lemma IsLine.exists_far (hG : G.IsTree) {l : ℤ → V} (hl : IsLine G l) (k : ℤ) (w : V)
    (n : ℕ) : ∃ z, G.dist (l k) z = n ∧ Between G w (l k) z := by
  have h1 : Between G (l (k + n)) (l k) (l (k - n)) := by
    rw [between_iff_dist_add hG, hl, hl, hl]
    omega
  rcases between_or hG h1 w with h2 | h2
  · exact ⟨l (k + n), by rw [hl]; omega, h2.symm⟩
  · exact ⟨l (k - n), by rw [hl]; omega, h2⟩

/-! ### Hairs -/

/-- `P` is a hair of depth `h` at `c`: a connected component of the complement
of `{c}`, contained in the ball of radius `h` around `c` and meeting its
boundary. -/
def IsHair (G : SimpleGraph V) (c : V) (P : Set V) (h : ℕ) : Prop :=
  (∃ C : G.ComponentCompl ({c} : Set V), (C : Set V) = P) ∧
    (∀ v ∈ P, G.dist v c ≤ h) ∧ ∃ v ∈ P, G.dist v c = h

/-- A walk missing `c` and ending in a component of the complement of `{c}`
starts in that component. -/
lemma mem_componentCompl_of_walk {c : V} {C : G.ComponentCompl ({c} : Set V)} :
    ∀ {a b : V} (W : G.Walk a b), c ∉ W.support → b ∈ C → a ∈ C := by
  intro a b W
  induction W with
  | nil => exact fun _ h => h
  | @cons u v w hadj W ih =>
    intro hc hb
    have h1 : c ∉ W.support := fun h => hc (by simp [h])
    have h2 : u ∉ ({c} : Set V) := by
      simp only [Set.mem_singleton_iff]
      rintro rfl
      exact hc (by simp)
    exact ComponentCompl.mem_of_adj v u (ih h1 hb) h2 hadj.symm

/-- **The separation by a hair.**  A vertex outside a component of the
complement of `{c}` is separated from every vertex of that component by `c`. -/
lemma between_of_notMem_componentCompl {c : V} {C : G.ComponentCompl ({c} : Set V)} {x q : V}
    (hx : x ∈ C) (hq : q ∉ C) : Between G q c x := by
  intro W
  by_contra hc
  exact hq (mem_componentCompl_of_walk W hc hx)

/-! ### Hairs against lines -/

/-- **`thm:hair-separation`.**  A tree with hairs of unbounded depth is not
quasi-isometric to a tree all of whose vertices lie within a bounded distance
of a line. -/
theorem not_quasiIsometric_of_hair_of_line {R : ℕ} (hG : G.IsTree) (hG' : G'.IsTree)
    (hhair : ∀ n : ℕ, ∃ (c : V) (P : Set V) (h : ℕ), n < h ∧ IsHair G c P h)
    (hline : ∀ u : V', ∃ (l : ℤ → V') (k : ℤ), IsLine G' l ∧ G'.dist u (l k) ≤ R) :
    ¬ QuasiIsometric G G' := by
  rintro ⟨D, f, hf⟩
  obtain ⟨c, P, h, hh, ⟨C, hCP⟩, hball, x, hxP, hxd⟩ := hhair (D * (D + R) + D * D)
  obtain ⟨l, k, hl, hly⟩ := hline (f x)
  obtain ⟨z, hzd, hzb⟩ := hl.exists_far hG' k (f c) (D * h + 2 * D + 1)
  obtain ⟨p, hp⟩ := hf.dense z
  -- the line vertex is at distance at least `L` from `f c` along `[f c, z]`
  have hwz : G'.dist (f c) (l k) + (D * h + 2 * D + 1) = G'.dist (f c) z := by
    have := hzb.dist_add hG'.connected
    omega
  -- the preimage `p` of a far point on the line lies outside the hair
  have hpP : p ∉ P := by
    intro hmem
    have h1 : G.dist p c ≤ h := hball p hmem
    have h2 : D * G.dist p c ≤ D * h := Nat.mul_le_mul_left D h1
    have h3 := hf.upper p c
    have h4 : G'.dist (f c) z ≤ G'.dist (f c) (f p) + G'.dist (f p) z := hG'.connected.dist_triangle
    rw [SimpleGraph.dist_comm (u := f c) (v := f p)] at h4
    omega
  -- the line vertex lies between `f c` and `f p`
  have hb2 : Between G' (f c) (l k) (f p) := by
    rcases between_or hG' hzb (f p) with h1 | h1
    · exact h1
    · exfalso
      have := h1.dist_add hG'.connected
      omega
  -- stability produces a vertex of `[c, p]` whose image is close to the line vertex
  obtain ⟨pw, hpw, -⟩ := hG.connected.exists_path_of_dist c p
  obtain ⟨i, -, hqd⟩ := exists_between_dist_le hG' hf pw hb2
  have hqb : Between G c (pw.getVert i) p :=
    between_of_mem_support hG hpw (pw.getVert_mem_support i)
  -- that vertex is separated from the deep vertex of the hair by `c`
  have hpc : Between G p c x := by
    refine between_of_notMem_componentCompl (C := C) ?_ ?_
    · rw [← SetLike.mem_coe, hCP]; exact hxP
    · rw [← SetLike.mem_coe, hCP]; exact hpP
  have hqc : Between G (pw.getVert i) c x := by
    rcases between_or hG hpc (pw.getVert i) with h1 | h1
    · have e1 := h1.dist_add hG.connected
      have e2 := hqb.dist_add hG.connected
      rw [SimpleGraph.dist_comm (u := p) (v := c),
        SimpleGraph.dist_comm (u := p) (v := pw.getVert i)] at e1
      have hzero : G.dist c (pw.getVert i) = 0 := by omega
      rw [← ((hG.connected c (pw.getVert i)).dist_eq_zero_iff).1 hzero]
      exact between_left G c x
    · exact h1
  -- far from the deep vertex, yet close to it
  have hfar : h ≤ G.dist (pw.getVert i) x := by
    have := hqc.dist_add hG.connected
    rw [SimpleGraph.dist_comm (u := x) (v := c)] at hxd
    omega
  have hclose : G.dist (pw.getVert i) x ≤ D * (D + R) + D * D := by
    have h1 : G'.dist (f (pw.getVert i)) (f x) ≤ D + R := by
      have h2 : G'.dist (f (pw.getVert i)) (f x)
          ≤ G'.dist (f (pw.getVert i)) (l k) + G'.dist (l k) (f x) := hG'.connected.dist_triangle
      rw [SimpleGraph.dist_comm (u := l k) (v := f x)] at h2
      omega
    calc G.dist (pw.getVert i) x
        ≤ D * G'.dist (f (pw.getVert i)) (f x) + D * D := hf.lower _ _
      _ ≤ D * (D + R) + D * D := by gcongr
  exact absurd (hfar.trans hclose) (not_le.2 hh)

/-! ### The ray -/

/-- The ray: `ℕ` with the path-graph structure. -/
def rayGraph : SimpleGraph ℕ where
  Adj m n := m + 1 = n ∨ n + 1 = m
  symm := ⟨by intro a b h; omega⟩
  loopless := ⟨by intro a h; omega⟩

/-- Adjacency in the ray: the two vertices differ by one. -/
@[simp] lemma rayGraph_adj {m n : ℕ} : rayGraph.Adj m n ↔ m + 1 = n ∨ n + 1 = m := Iff.rfl

/-- The walk climbing `k` steps from `a`. -/
def rayUp (a : ℕ) : (k : ℕ) → rayGraph.Walk a (a + k)
  | 0 => Walk.nil
  | k + 1 => (rayUp a k).concat (by simp only [rayGraph_adj]; omega)

/-- The climbing walk has the expected length. -/
@[simp] lemma rayUp_length (a k : ℕ) : (rayUp a k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rayUp, Walk.length_concat, ih]

/-- The ray is connected: climbing joins any two vertices. -/
lemma rayGraph_reachable (a b : ℕ) : rayGraph.Reachable a b := by
  rcases le_total a b with hab | hab
  · exact ⟨(rayUp a (b - a)).copy rfl (by omega)⟩
  · exact ⟨((rayUp b (a - b)).copy rfl (by omega)).reverse⟩

/-- The climbing walk bounds the graph metric of the ray. -/
lemma rayGraph_dist_le (a b : ℕ) : rayGraph.dist a b ≤ Nat.dist a b := by
  rcases le_total a b with hab | hab
  · have h := dist_le ((rayUp a (b - a)).copy rfl (show a + (b - a) = b by omega))
    rw [Walk.length_copy, rayUp_length, ← Nat.dist_eq_sub_of_le hab] at h
    exact h
  · have h := dist_le (((rayUp b (a - b)).copy rfl (show b + (a - b) = a by omega)).reverse)
    rw [Walk.length_reverse, Walk.length_copy, rayUp_length,
      ← Nat.dist_eq_sub_of_le_right hab] at h
    exact h

/-- Each step of a walk in the ray moves the parameter by one, so the natural
distance bounds the length. -/
lemma rayGraph_le_length : ∀ {a b : ℕ} (W : rayGraph.Walk a b), Nat.dist a b ≤ W.length := by
  intro a b W
  induction W with
  | nil => simp
  | @cons u v w hadj W ih =>
    rw [rayGraph_adj] at hadj
    rw [Walk.length_cons]
    unfold Nat.dist at ih ⊢
    omega

/-- The graph metric of the ray is the natural distance. -/
lemma rayGraph_dist (a b : ℕ) : rayGraph.dist a b = Nat.dist a b := by
  refine le_antisymm (rayGraph_dist_le a b) ?_
  obtain ⟨W, hW⟩ := (rayGraph_reachable a b).exists_walk_length_eq_dist
  exact hW ▸ rayGraph_le_length W

/-- The ray is connected. -/
lemma rayGraph_connected : rayGraph.Connected := ⟨rayGraph_reachable⟩

/-- The ray is acyclic: deleting an edge separates the vertices below it from
those above. -/
lemma rayGraph_isAcyclic : rayGraph.IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  rw [isBridge_iff]
  rintro ⟨W⟩
  rw [rayGraph_adj] at huv
  have hstep : ∀ a c : ℕ, (rayGraph.deleteEdges {s(u, v)}).Adj a c →
      (a ≤ min u v ↔ c ≤ min u v) := by
    intro a c hac
    rw [deleteEdges_adj, rayGraph_adj] at hac
    obtain ⟨h1, h2⟩ := hac
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at h2
    omega
  have key : ∀ {a b : ℕ}, (rayGraph.deleteEdges {s(u, v)}).Walk a b →
      (a ≤ min u v ↔ b ≤ min u v) := by
    intro a b W
    induction W with
    | nil => exact Iff.rfl
    | cons h _ ih => exact (hstep _ _ h).trans ih
  have := key W
  omega

/-- The ray is a tree. -/
lemma rayGraph_isTree : rayGraph.IsTree := ⟨rayGraph_connected, rayGraph_isAcyclic⟩

/-! ### Three rays against the ray -/

/-- A geodesic out of the initial vertex of a ray runs along the ray: a vertex
between `r 0` and `r n` is the vertex of the ray at its own distance from
`r 0`. -/
lemma IsRay.eq_of_between (hG : G.IsTree) {r : ℕ → V} (hr : IsRay G r) {n : ℕ} {u : V}
    (hu : Between G (r 0) u (r n)) : u = r (G.dist (r 0) u) := by
  have hsplit := hu.dist_add hG.connected
  rw [hr] at hsplit
  unfold Nat.dist at hsplit
  have hzero : G.dist u (r (G.dist (r 0) u)) = 0 := by
    rcases between_or hG hu (r (G.dist (r 0) u)) with h1 | h1
    · have h2 := h1.dist_add hG.connected
      rw [hr] at h2
      unfold Nat.dist at h2
      omega
    · have h2 := h1.dist_add hG.connected
      rw [hr, SimpleGraph.dist_comm (u := r (G.dist (r 0) u)) (v := u)] at h2
      unfold Nat.dist at h2
      omega
  exact ((hG.connected u _).dist_eq_zero_iff).1 hzero

/-- **Two rays branch.**  Two rays of a tree leaving a common initial vertex
and meeting only there are at distance the sum of the parameters. -/
lemma dist_ray_branch (hG : G.IsTree) {r s : ℕ → V} (hr : IsRay G r) (hs : IsRay G s)
    (h0 : r 0 = s 0) (hmeet : ∀ m n, r m = s n → r m = r 0) (m n : ℕ) :
    G.dist (r m) (s n) = m + n := by
  induction n with
  | zero =>
    rw [← h0, hr]
    unfold Nat.dist
    omega
  | succ n ih =>
    have hadj : G.Adj (s n) (s (n + 1)) := by
      rw [← dist_eq_one_iff_adj, hs]
      unfold Nat.dist
      omega
    rcases hG.dist_eq_dist_add_one_of_adj (r m) hadj with h1 | h1
    swap
    · omega
    -- the remaining case puts `s (n+1)` between `r m` and `s n`, which is impossible
    exfalso
    have hb : Between G (r m) (s (n + 1)) (s n) := by
      rw [between_iff_dist_add hG, hs]
      unfold Nat.dist
      omega
    have hd0 : G.dist (r 0) (s (n + 1)) = n + 1 := by
      rw [h0, hs]
      unfold Nat.dist
      omega
    rcases between_or hG hb (r 0) with h2 | h2
    · have h3 := hr.eq_of_between hG h2.symm
      rw [hd0] at h3
      have h4 := hmeet (n + 1) (n + 1) h3.symm
      rw [h3, h4, dist_self] at hd0
      omega
    · have h3 := h2.dist_add hG.connected
      rw [hd0, h0, hs, hs] at h3
      unfold Nat.dist at h3
      omega

/-- **`thm:three-rays`.**  A tree carrying three rays that pairwise meet only
in their common initial vertex is not quasi-isometric to the ray. -/
theorem not_quasiIsometric_rayGraph (hG : G.IsTree) {v : V} {ray : Fin 3 → ℕ → V}
    (hray : ∀ i, IsRay G (ray i)) (hbase : ∀ i, ray i 0 = v)
    (hmeet : ∀ i j, i ≠ j → ∀ m n, ray i m = ray j n → ray i m = v) :
    ¬ QuasiIsometric G rayGraph := by
  rintro ⟨D, f, hf⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ, ρ = D * D + D * D + 1 := ⟨_, rfl⟩
  have key : ∀ i j : Fin 3, i ≠ j →
      Nat.dist (f v) (f (ray i ρ)) + Nat.dist (f (ray i ρ)) (f (ray j ρ))
        = Nat.dist (f v) (f (ray j ρ)) → False := by
    intro i j hij hd
    have hb : Between rayGraph (f v) (f (ray i ρ)) (f (ray j ρ)) := by
      rw [between_iff_dist_add rayGraph_isTree, rayGraph_dist, rayGraph_dist, rayGraph_dist]
      exact hd
    obtain ⟨W, hW, -⟩ := hG.connected.exists_path_of_dist v (ray j ρ)
    obtain ⟨t, -, htd⟩ := exists_between_dist_le rayGraph_isTree hf W hb
    have hqb : Between G v (W.getVert t) (ray j ρ) :=
      between_of_mem_support hG hW (W.getVert_mem_support t)
    have hqray : W.getVert t = ray j (G.dist v (W.getVert t)) := by
      have h1 : Between G (ray j 0) (W.getVert t) (ray j ρ) := by rw [hbase j]; exact hqb
      have h2 := (hray j).eq_of_between hG h1
      rwa [hbase j] at h2
    have hbranch := dist_ray_branch hG (hray j) (hray i) (by rw [hbase, hbase])
      (fun a b hab => by rw [hbase j]; exact hmeet j i (Ne.symm hij) a b hab)
      (G.dist v (W.getVert t)) ρ
    have hfar : ρ ≤ G.dist (W.getVert t) (ray i ρ) := by
      rw [hqray, hbranch]
      omega
    have hclose : G.dist (W.getVert t) (ray i ρ) ≤ D * D + D * D := by
      calc G.dist (W.getVert t) (ray i ρ)
          ≤ D * rayGraph.dist (f (W.getVert t)) (f (ray i ρ)) + D * D := hf.lower _ _
        _ ≤ D * D + D * D := by gcongr
    exact absurd (hfar.trans hclose) (by omega)
  have H :
      Nat.dist (f v) (f (ray 0 ρ)) + Nat.dist (f (ray 0 ρ)) (f (ray 1 ρ))
          = Nat.dist (f v) (f (ray 1 ρ)) ∨
      Nat.dist (f v) (f (ray 1 ρ)) + Nat.dist (f (ray 1 ρ)) (f (ray 0 ρ))
          = Nat.dist (f v) (f (ray 0 ρ)) ∨
      Nat.dist (f v) (f (ray 0 ρ)) + Nat.dist (f (ray 0 ρ)) (f (ray 2 ρ))
          = Nat.dist (f v) (f (ray 2 ρ)) ∨
      Nat.dist (f v) (f (ray 2 ρ)) + Nat.dist (f (ray 2 ρ)) (f (ray 0 ρ))
          = Nat.dist (f v) (f (ray 0 ρ)) ∨
      Nat.dist (f v) (f (ray 1 ρ)) + Nat.dist (f (ray 1 ρ)) (f (ray 2 ρ))
          = Nat.dist (f v) (f (ray 2 ρ)) ∨
      Nat.dist (f v) (f (ray 2 ρ)) + Nat.dist (f (ray 2 ρ)) (f (ray 1 ρ))
          = Nat.dist (f v) (f (ray 1 ρ)) := by
    unfold Nat.dist
    omega
  rcases H with h | h | h | h | h | h
  · exact key 0 1 (by decide) h
  · exact key 1 0 (by decide) h
  · exact key 0 2 (by decide) h
  · exact key 2 0 (by decide) h
  · exact key 1 2 (by decide) h
  · exact key 2 1 (by decide) h

end BranchingProcess
