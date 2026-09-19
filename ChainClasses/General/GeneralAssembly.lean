import Mathlib.Tactic
import ChainClasses.Scalar.GluedTransfer
import ChainClasses.Shape.Assembly
import ChainClasses.General.GeneralShapeShrink
import ChainClasses.Shape.AddrMetric

/-!
`sec:general-relabel` of `matching_classes_general.tex`, item `thm:general-glued`:
the assembly of a family of shapes at general arity and `thm:glued-transfer` over
it.

The assembly is carried by addresses, as in `Assembly.lean`: the copy of `σ_w` is
planted at the address `gCopyAddr σ w`, a vertex is a pair `⟨w, p⟩` of the word naming
the copy and an address `p` inside the realisation of `σ_w`, and it sits at
`gCopyAddr σ w ++ p`.  The one change from the binary case is the planting offset.
The exit of a general shape is not a leaf: its children are the bushes of its
bouquet, `J'` of them say, so the copy at `w ++ [j]` is planted at the child `J' + j`
of the exit of the copy at `w`, past the bouquet, and the address layer keeps the
copies apart because no address of a realisation reaches past its bouquet
(`GShape.wedgeN_eq_wedgeN_exitAddr`).  The index words run over the full `ℕ`-ary tree.
The metric is the address metric `addrDist` of `AddrMetric.lean` read through the
code, which `RTree.dist_vert_eq_addrDist` identifies with the graph metric of the
realisations, so the two distance formulas are the wedge computations of the binary
case verbatim and the arithmetic of `GluedTransfer.lean` applies unchanged.

* `GShape.exit_prefix_cases`, `GShape.wedgeN_eq_wedgeN_exitAddr`: an address of a
  realisation extending the exit is the exit or a bouquet address, the fact that makes
  the planting past the bouquet faithful, and the wedge computation it feeds.
* `gCopyAddr`, `gCopyAddr_concat`, `gCopyAddr_length`: the planting of the copies,
  its recursion, and its depth, the total neck length of the copies above `w`.
* `gNeckSum`, `gCopyAddr_length_of_prefix`: the sum `∑_{u<t<v} m_t` of the two
  distance formulas and the depth increment it measures.
* `GAssembly`, `GAssembly.code`, `GAssembly.instMetricSpace`: the vertex set of the
  assembly and its metric.
* `GAssembly.dist_same`, `GAssembly.dist_anc` (**`eq:assembly-anc`**) and
  `GAssembly.dist_div` (**`eq:assembly-div`**): the three distance formulas, in the
  form `d = A + B + e + N` that `glued_dist_same` and `glued_dist_bounds` consume.
* `GAssembly.Adj`, `GAssembly.dist_eq_one_iff_adj`: the metric is the graph metric
  of the gluing, the copies being joined by an edge from an exit to the entries
  planted below it.
* `GAssembly.neckSum_bounds`, `GAssembly.glue`, `GAssembly.glue_dist_bounds_anc`,
  `GAssembly.glue_dist_bounds_div`, `GAssembly.glue_dense` and
  `GAssembly.glued_transfer`: **`thm:glued-transfer`** at general arity
  (**`thm:general-glued`**), the per-shape maps read copy by copy, an
  `8K²`-quasi-isometry of the assemblies.
-/

namespace ChainClasses

/-! ### The exit reaches no further than its bouquet -/

open GShape (realiseAux)

/-- An address of a realisation extending the exit is the exit itself or an address
in a bush of the exit bouquet `β`. -/
lemma isAddr_realiseAux_exit_cases :
    ∀ (init : List (List RTree)) (β : List RTree) {p : List ℕ},
      RTree.IsAddr (realiseAux (init ++ [β])) p → gExitAddr (init ++ [β]) <+: p →
      p = gExitAddr (init ++ [β]) ∨
        ∃ i v, i < β.length ∧ p = gExitAddr (init ++ [β]) ++ i :: v := by
  intro init
  induction init with
  | nil =>
      intro β p hp _
      rw [List.nil_append] at hp ⊢
      rw [gExitAddr_singleton]
      cases p with
      | nil => exact Or.inl rfl
      | cons i v =>
          rw [show realiseAux [β] = .node β from rfl, RTree.isAddr_cons] at hp
          obtain ⟨hi, -⟩ := hp
          exact Or.inr ⟨i, v, hi, rfl⟩
  | cons γ init ih =>
      intro β p hp hpre
      obtain ⟨r, rest, hr⟩ : ∃ r rest, init ++ [β] = r :: rest := by
        cases init <;> simp
      rw [List.cons_append, hr] at hp hpre ⊢
      rw [show realiseAux (γ :: r :: rest) = .node (γ ++ [realiseAux (r :: rest)]) from rfl]
        at hp
      rw [gExitAddr_cons₂] at hpre ⊢
      obtain ⟨s, rfl⟩ := hpre
      rw [List.cons_append, isAddr_append_last_eq] at hp
      have h := ih β (p := gExitAddr (r :: rest) ++ s) (by rw [hr]; exact hp)
        (by rw [hr]; exact List.prefix_append _ _)
      rw [hr] at h
      rcases h with h | ⟨i, v, hi, h⟩
      · exact Or.inl (by rw [List.cons_append, h])
      · exact Or.inr ⟨i, v, hi, by rw [List.cons_append, h, List.cons_append]⟩

/-- **`def:shape-general`**: an address of a realisation extending the exit is the
exit itself or an address in a bush of its bouquet, so no address of the realisation
reaches the children of the exit past the bouquet. -/
lemma GShape.exit_prefix_cases (σ : GShape) {p : List ℕ} (hp : RTree.IsAddr σ.realise p)
    (hpre : σ.exitAddr <+: p) :
    p = σ.exitAddr ∨ ∃ i v, i < σ.bouquet.length ∧ p = σ.exitAddr ++ i :: v := by
  have h := isAddr_realiseAux_exit_cases σ.neckList σ.bouquet (p := p)
    (by rw [← GShape.decs_eq_append]; exact hp) (by rw [← GShape.decs_eq_append]; exact hpre)
  rwa [← GShape.decs_eq_append] at h

/-- The wedge of an address of a realisation with anything reaching past the bouquet
is its wedge with the exit: the branch parts at the exit at the latest. -/
lemma GShape.wedgeN_eq_wedgeN_exitAddr (σ : GShape) {p R : List ℕ} {j : ℕ}
    (hp : RTree.IsAddr σ.realise p) (hR : σ.exitAddr ++ [σ.bouquet.length + j] <+: R) :
    wedgeN p R = wedgeN p σ.exitAddr := by
  have hnR : σ.exitAddr <+: R := (List.prefix_append _ _).trans hR
  have hg1 : wedgeN p σ.exitAddr <+: p := wedgeN_prefix_left _ _
  have hg2 : wedgeN p σ.exitAddr <+: σ.exitAddr := wedgeN_prefix_right _ _
  have hle : wedgeN p σ.exitAddr <+: wedgeN p R := prefix_wedgeN hg1 (hg2.trans hnR)
  rcases List.prefix_or_prefix_of_prefix (wedgeN_prefix_right p R) hnR with h | h
  · have h2 : wedgeN p R <+: wedgeN p σ.exitAddr := prefix_wedgeN (wedgeN_prefix_left p R) h
    exact h2.eq_of_length (le_antisymm h2.length_le hle.length_le)
  · have hnp : σ.exitAddr <+: p := h.trans (wedgeN_prefix_left p R)
    rcases σ.exit_prefix_cases hp hnp with rfl | ⟨i, v, hi, rfl⟩
    · rw [wedgeN_of_prefix hnR, wedgeN_self]
    · have hne : i ≠ σ.bouquet.length + j := by omega
      rw [wedgeN_of_diverge hne ⟨v, by simp⟩ hR, wedgeN_comm,
        wedgeN_of_prefix (List.prefix_append _ _)]

/-- The exit sits one letter per neck edge below the entry. -/
lemma gExitAddr_length : ∀ L : List (List RTree), (gExitAddr L).length = L.length - 1
  | [] => rfl
  | [_] => rfl
  | β :: r :: rest => by
      rw [gExitAddr_cons₂, List.length_cons, gExitAddr_length (r :: rest)]
      simp

/-- The depth of the exit is the number of neck edges. -/
lemma GShape.exitAddr_length (σ : GShape) : σ.exitAddr.length = σ.necks := by
  rw [GShape.exitAddr, gExitAddr_length, GShape.decs_length]
  rfl

/-! ### Planting the copies -/

/-- The address at which the copy of `σ_w` is planted in the assembly: the copy at
`w ++ [j]` hangs at the child past the bouquet, at index `|bouquet| + j`, of the exit of
the copy at `w`. -/
def gCopyAddr (σ : List ℕ → GShape) (w : List ℕ) : List ℕ :=
  (w.foldl (fun p j => (p.1 ++ [j], p.2 ++ (σ p.1).exitAddr ++ [(σ p.1).bouquet.length + j]))
    (([] : List ℕ), ([] : List ℕ))).2

/-- The first fold component records the consumed prefix. -/
lemma gCopyAddr_foldl_fst (σ : List ℕ → GShape) (w a b : List ℕ) :
    (w.foldl (fun p j => (p.1 ++ [j], p.2 ++ (σ p.1).exitAddr ++ [(σ p.1).bouquet.length + j]))
      (a, b)).1 = a ++ w := by
  induction w generalizing a b with
  | nil => simp
  | cons j t ih =>
      simpa using ih (a ++ [j]) (b ++ (σ a).exitAddr ++ [(σ a).bouquet.length + j])

/-- The copy at the root sits at the root. -/
@[simp] lemma gCopyAddr_nil (σ : List ℕ → GShape) : gCopyAddr σ [] = [] := rfl

/-- The recursion of the assembly: the copy at `w ++ [j]` is planted at the child
`|bouquet| + j` of the exit of the copy at `w`. -/
lemma gCopyAddr_concat (σ : List ℕ → GShape) (w : List ℕ) (j : ℕ) :
    gCopyAddr σ (w ++ [j])
      = gCopyAddr σ w ++ (σ w).exitAddr ++ [(σ w).bouquet.length + j] := by
  have h := gCopyAddr_foldl_fst σ w [] []
  rw [List.nil_append] at h
  simp only [gCopyAddr, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [h]

/-- The planting only appends: it is monotone for the prefix order. -/
lemma gCopyAddr_prefix (σ : List ℕ → GShape) {w w' : List ℕ} (h : w <+: w') :
    gCopyAddr σ w <+: gCopyAddr σ w' := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc]
      calc gCopyAddr σ w <+: gCopyAddr σ (w ++ u) := ih
        _ <+: gCopyAddr σ (w ++ u ++ [j]) := by
            rw [gCopyAddr_concat]
            exact (List.prefix_append _ _).trans (List.prefix_append _ _)

/-- The depth of a copy is the total neck length of the copies above it. -/
lemma gCopyAddr_length (σ : List ℕ → GShape) (w : List ℕ) :
    (gCopyAddr σ w).length = ∑ i ∈ Finset.range w.length, (σ (w.take i)).neckLen := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w j ih =>
      have hcong : ∀ i ∈ Finset.range w.length,
          (σ ((w ++ [j]).take i)).neckLen = (σ (w.take i)).neckLen := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [List.take_append_of_le_length (by omega)]
      rw [gCopyAddr_concat]
      simp only [List.length_append, List.length_singleton, GShape.exitAddr_length,
        Finset.sum_range_succ]
      rw [Finset.sum_congr rfl hcong, List.take_left, ← ih, GShape.neckLen]
      omega

/-- **The neck sum of `eq:assembly-anc` and `eq:assembly-div`**: the total neck
length `∑_{u<t<v} m_t` of the copies strictly between `u` and `v`. -/
def gNeckSum (σ : List ℕ → GShape) (u v : List ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico (u.length + 1) v.length, (σ (v.take i)).neckLen

/-- The depth increment from a copy to a copy below it: one whole neck, then the
necks of the copies in between. -/
lemma gCopyAddr_length_of_prefix (σ : List ℕ → GShape) {u v : List ℕ} (huv : u <+: v)
    (hne : u ≠ v) :
    (gCopyAddr σ v).length = (gCopyAddr σ u).length + (σ u).neckLen + gNeckSum σ u v := by
  have hlt : u.length < v.length := by
    rcases huv.length_le.lt_or_eq with h | h
    · exact h
    · exact absurd (huv.eq_of_length h) hne
  have hu : u = v.take u.length := List.prefix_iff_eq_take.mp huv
  have hlow : ∀ i ∈ Finset.range u.length,
      (σ (v.take i)).neckLen = (σ (u.take i)).neckLen := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hu, List.take_take, Nat.min_eq_left hi.le]
  have hsplit : ∑ i ∈ Finset.range v.length, (σ (v.take i)).neckLen
      = (∑ i ∈ Finset.range u.length, (σ (v.take i)).neckLen)
        + ∑ i ∈ Finset.Ico u.length v.length, (σ (v.take i)).neckLen := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) hlt.le]
  have hbot : ∑ i ∈ Finset.Ico u.length v.length, (σ (v.take i)).neckLen
      = (σ u).neckLen + gNeckSum σ u v := by
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt, ← hu]
    rfl
  rw [gCopyAddr_length, gCopyAddr_length, hsplit, hbot, Finset.sum_congr rfl hlow]
  omega

/-! ### The distance formulas at the level of addresses -/

/-- Inside one copy the distance is the distance of the addresses. -/
lemma addrDist_gCopyAddr_same (σ : List ℕ → GShape) (u p q : List ℕ) :
    addrDist (gCopyAddr σ u ++ p) (gCopyAddr σ u ++ q) = addrDist p q :=
  addrDist_append_append _ _ _

/-- **`eq:assembly-anc`** at the level of addresses: from a vertex of the copy at `u`
to a vertex of a copy strictly below it, the geodesic leaves through the exit of the
copy at `u`, crosses one edge, traverses the intermediate copies, and descends to the
vertex from the entry of its copy. -/
lemma addrDist_gCopyAddr_anc (σ : List ℕ → GShape) {u v : List ℕ} (huv : u <+: v)
    (hne : u ≠ v) {p : List ℕ} (hp : RTree.IsAddr (σ u).realise p) (q : List ℕ) :
    addrDist (gCopyAddr σ u ++ p) (gCopyAddr σ v ++ q)
      = addrDist p (σ u).exitAddr + 1 + gNeckSum σ u v + q.length := by
  obtain ⟨s, rfl⟩ := huv
  cases s with
  | nil => exact absurd (by simp) hne
  | cons j t =>
      have hstep : gCopyAddr σ u ++ (σ u).exitAddr ++ [(σ u).bouquet.length + j]
          <+: gCopyAddr σ (u ++ j :: t) := by
        rw [← gCopyAddr_concat]
        exact gCopyAddr_prefix σ ⟨t, by simp⟩
      obtain ⟨r, hr⟩ := hstep
      have hcode : gCopyAddr σ (u ++ j :: t) ++ q
          = gCopyAddr σ u
            ++ (((σ u).exitAddr ++ [(σ u).bouquet.length + j]) ++ (r ++ q)) := by
        rw [← hr]; simp only [List.append_assoc]
      have hw : wedgeN (gCopyAddr σ u ++ p)
            (gCopyAddr σ u ++ (((σ u).exitAddr ++ [(σ u).bouquet.length + j]) ++ (r ++ q)))
          = gCopyAddr σ u ++ wedgeN p (σ u).exitAddr := by
        rw [wedgeN_append_append, (σ u).wedgeN_eq_wedgeN_exitAddr hp (List.prefix_append _ _)]
      have h1 := addrDist_add_wedgeN_length (gCopyAddr σ u ++ p)
        (gCopyAddr σ u ++ (((σ u).exitAddr ++ [(σ u).bouquet.length + j]) ++ (r ++ q)))
      rw [hw] at h1
      have h2 := addrDist_add_wedgeN_length p (σ u).exitAddr
      have hrlen := congrArg List.length hr
      simp only [List.length_append, List.length_singleton] at hrlen
      have hlen := gCopyAddr_length_of_prefix σ (u := u) (v := u ++ j :: t) ⟨j :: t, rfl⟩ hne
      have hnlen : (σ u).exitAddr.length = (σ u).necks := (σ u).exitAddr_length
      have hneck : (σ u).neckLen = (σ u).necks + 1 := rfl
      rw [hcode]
      simp only [List.length_append, List.length_singleton] at h1
      omega

/-- **`eq:assembly-div`** at the level of addresses: from a vertex of the copy at `u`
to a vertex of the copy at a diverging `v`, the two branches climb to the entries of
their copies, traverse the intermediate copies, and meet at the exit of the copy at
the wedge, which may carry any number of outgoing edges. -/
lemma addrDist_gCopyAddr_div (σ : List ℕ → GShape) {u v : List ℕ} (hu : ¬ u <+: v)
    (hv : ¬ v <+: u) (p q : List ℕ) :
    addrDist (gCopyAddr σ u ++ p) (gCopyAddr σ v ++ q)
      = p.length + q.length + 2 + gNeckSum σ (wedgeN u v) u + gNeckSum σ (wedgeN u v) v := by
  obtain ⟨z, a, b, hab, hzu, hzv⟩ := exists_divergeN hu hv
  have hz : wedgeN u v = z := wedgeN_of_diverge hab hzu hzv
  have hzu' : z <+: u := (List.prefix_append z [a]).trans hzu
  have hzv' : z <+: v := (List.prefix_append z [b]).trans hzv
  have hzune : z ≠ u := by
    intro h
    have := hzu.length_le
    rw [← h] at this
    simp at this
  have hzvne : z ≠ v := by
    intro h
    have := hzv.length_le
    rw [← h] at this
    simp at this
  have hpu : gCopyAddr σ z ++ (σ z).exitAddr ++ [(σ z).bouquet.length + a]
      <+: gCopyAddr σ u := by
    rw [← gCopyAddr_concat]
    exact gCopyAddr_prefix σ hzu
  have hpv : gCopyAddr σ z ++ (σ z).exitAddr ++ [(σ z).bouquet.length + b]
      <+: gCopyAddr σ v := by
    rw [← gCopyAddr_concat]
    exact gCopyAddr_prefix σ hzv
  have hab' : (σ z).bouquet.length + a ≠ (σ z).bouquet.length + b := by omega
  have hw : wedgeN (gCopyAddr σ u ++ p) (gCopyAddr σ v ++ q)
      = gCopyAddr σ z ++ (σ z).exitAddr :=
    wedgeN_of_diverge hab' (hpu.trans (List.prefix_append _ _))
      (hpv.trans (List.prefix_append _ _))
  have h1 := addrDist_add_wedgeN_length (gCopyAddr σ u ++ p) (gCopyAddr σ v ++ q)
  rw [hw] at h1
  have hlenu := gCopyAddr_length_of_prefix σ hzu' hzune
  have hlenv := gCopyAddr_length_of_prefix σ hzv' hzvne
  have hnlen : (σ z).exitAddr.length = (σ z).necks := (σ z).exitAddr_length
  have hneck : (σ z).neckLen = (σ z).necks + 1 := rfl
  rw [hz]
  simp only [List.length_append] at h1
  omega

/-! ### The assembly as a metric space -/

/-- **The assembly of a family of shapes at general arity**: a vertex is an address
inside the realisation of the shape at `w`, tagged by the word `w` naming its copy. -/
structure GAssembly (σ : List ℕ → GShape) where
  /-- The word naming the copy. -/
  copy : List ℕ
  /-- The address inside the realisation of the shape at that copy. -/
  vert : (gShapeSpace (σ copy)).carrier

namespace GAssembly

variable {σ : List ℕ → GShape}

/-- The address of a vertex of the assembly in the ambient tree: the planting of its
copy followed by its address inside the copy. -/
def code (x : GAssembly σ) : List ℕ := gCopyAddr σ x.copy ++ x.vert.1

/-- A vertex of the assembly is determined by its copy and its address. -/
lemma vert_eq : ∀ {x y : GAssembly σ}, x.copy = y.copy → x.vert.1 = y.vert.1 → x = y := by
  rintro ⟨u, p, hp⟩ ⟨v, q, hq⟩ h1 h2
  simp only at h1 h2
  subst h1
  subst h2
  rfl

/-- The three relative positions of two copies. -/
lemma copy_trichotomy (u v : List ℕ) :
    u = v ∨ (u <+: v ∧ u ≠ v) ∨ (v <+: u ∧ v ≠ u) ∨ (¬ u <+: v ∧ ¬ v <+: u) := by
  by_cases h1 : u <+: v
  · by_cases h2 : v <+: u
    · exact Or.inl (h1.eq_of_length (le_antisymm h1.length_le h2.length_le))
    · exact Or.inr (Or.inl ⟨h1, fun h => h2 (h ▸ List.prefix_refl _)⟩)
  · by_cases h2 : v <+: u
    · exact Or.inr (Or.inr (Or.inl ⟨h2, fun h => h1 (h ▸ List.prefix_refl _)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))

/-- Distinct vertices carry distinct addresses. -/
lemma code_injective : Function.Injective (code (σ := σ)) := by
  rintro ⟨u, p⟩ ⟨v, q⟩ h
  simp only [code] at h
  have h0 : addrDist (gCopyAddr σ u ++ p.1) (gCopyAddr σ v ++ q.1) = 0 :=
    addrDist_eq_zero_iff.mpr h
  rcases copy_trichotomy u v with rfl | ⟨huv, hne⟩ | ⟨hvu, hne⟩ | ⟨hu, hv⟩
  · refine vert_eq rfl ?_
    rw [addrDist_gCopyAddr_same] at h0
    exact addrDist_eq_zero_iff.mp h0
  · rw [addrDist_gCopyAddr_anc σ huv hne (RTree.mem_addrList_iff.mp p.2)] at h0
    omega
  · rw [addrDist_comm, addrDist_gCopyAddr_anc σ hvu hne (RTree.mem_addrList_iff.mp q.2)] at h0
    omega
  · rw [addrDist_gCopyAddr_div σ hu hv] at h0
    omega

/-- The metric of the assembly, restricted from the ambient tree along the
addresses. -/
instance instMetricSpace (σ : List ℕ → GShape) : MetricSpace (GAssembly σ) where
  dist x y := (addrDist (code x) (code y) : ℝ)
  dist_self x := by simp
  dist_comm x y := by simp only [addrDist_comm (code x) (code y)]
  dist_triangle x y z := by
    have := addrDist_triangle (code x) (code y) (code z)
    exact_mod_cast this
  eq_of_dist_eq_zero {x y} h := by
    have h0 : addrDist (code x) (code y) = 0 := by exact_mod_cast h
    exact code_injective (addrDist_eq_zero_iff.mp h0)

/-- The distance of two vertices is the distance of their addresses. -/
@[simp] lemma dist_code (x y : GAssembly σ) :
    dist x y = (addrDist (code x) (code y) : ℝ) := rfl

/-- The distance inside a realisation is the distance of the addresses. -/
@[simp] lemma dist_gShapeSpace (τ : GShape) (p q : (gShapeSpace τ).carrier) :
    dist p q = (addrDist p.1 q.1 : ℝ) :=
  RTree.dist_vert_eq_addrDist p q

/-- The entry of a realisation is its root. -/
@[simp] lemma entry_gShapeSpace_val (τ : GShape) : (gShapeSpace τ).entry.1 = ([] : List ℕ) := rfl

/-- The exit of a realisation is its terminating split. -/
@[simp] lemma exit_gShapeSpace_val (τ : GShape) : (gShapeSpace τ).exit.1 = τ.exitAddr := by
  rw [exit_gShapeSpace]

/-! ### The distance formulas -/

/-- Every shape carries at least one neck vertex: the hypothesis `1 ≤ m` of
`neck_bounds` and `neck_sum_bounds`. -/
lemma one_le_neckLen (τ : GShape) : (1 : ℝ) ≤ (τ.neckLen : ℝ) := by
  rw [GShape.neckLen]
  push_cast
  linarith [(Nat.cast_nonneg τ.necks : (0 : ℝ) ≤ τ.necks)]

/-- **`def:shape-general`**: the entry and the exit of a shape are the two ends of
its neck, at distance the neck length less one. -/
lemma dist_entry_exit (τ : GShape) :
    dist (gShapeSpace τ).entry (gShapeSpace τ).exit = (τ.necks : ℝ) := by
  rw [dist_gShapeSpace, entry_gShapeSpace_val, exit_gShapeSpace_val, addrDist_nil_left,
    GShape.exitAddr_length]

/-- **`thm:glued-transfer`, inside one copy**: every copy is an induced subtree, so
its internal distances agree with those of the assembly. -/
theorem dist_same (σ : List ℕ → GShape) (u : List ℕ) (p q : (gShapeSpace (σ u)).carrier) :
    dist (⟨u, p⟩ : GAssembly σ) ⟨u, q⟩ = dist p q := by
  simp only [dist_code, code, dist_gShapeSpace, addrDist_gCopyAddr_same]

/-- **`eq:assembly-anc`**: for `x` in the copy at `u` and `y` in the copy at a `v`
strictly below `u`, the distance is the distance of `x` to the exit of its copy, plus
the distance of `y` to the entry of its copy, plus one, plus the total neck length of
the copies strictly between `u` and `v`. -/
theorem dist_anc (σ : List ℕ → GShape) {u v : List ℕ} (huv : u <+: v) (hne : u ≠ v)
    (p : (gShapeSpace (σ u)).carrier) (q : (gShapeSpace (σ v)).carrier) :
    dist (⟨u, p⟩ : GAssembly σ) ⟨v, q⟩
      = dist p (gShapeSpace (σ u)).exit + dist q (gShapeSpace (σ v)).entry + 1
        + ∑ i ∈ Finset.Ico (u.length + 1) v.length, ((σ (v.take i)).neckLen : ℝ) := by
  simp only [dist_code, code, dist_gShapeSpace, entry_gShapeSpace_val, exit_gShapeSpace_val]
  rw [addrDist_gCopyAddr_anc σ huv hne (RTree.mem_addrList_iff.mp p.2)]
  simp only [gNeckSum, addrDist_nil_right]
  push_cast
  ring

/-- **`eq:assembly-div`**: for `x` in the copy at `u` and `y` in the copy at a
diverging `v`, the distance is the distance of `x` to the entry of its copy, plus the
distance of `y` to the entry of its copy, plus two, plus the total neck lengths of the
copies strictly between the wedge and each of `u` and `v`; the two branches meet at
the exit of the copy at the wedge, whatever its number of outgoing edges. -/
theorem dist_div (σ : List ℕ → GShape) {u v : List ℕ} (hu : ¬ u <+: v) (hv : ¬ v <+: u)
    (p : (gShapeSpace (σ u)).carrier) (q : (gShapeSpace (σ v)).carrier) :
    dist (⟨u, p⟩ : GAssembly σ) ⟨v, q⟩
      = dist p (gShapeSpace (σ u)).entry + dist q (gShapeSpace (σ v)).entry + 2
        + (∑ i ∈ Finset.Ico ((wedgeN u v).length + 1) u.length, ((σ (u.take i)).neckLen : ℝ)
          + ∑ i ∈ Finset.Ico ((wedgeN u v).length + 1) v.length,
              ((σ (v.take i)).neckLen : ℝ)) := by
  simp only [dist_code, code, dist_gShapeSpace, entry_gShapeSpace_val]
  rw [addrDist_gCopyAddr_div σ hu hv]
  simp only [gNeckSum, addrDist_nil_right]
  push_cast
  ring

/-! ### The gluing edges -/

/-- The gluing edge of the assembly: the exit of the copy at `w` is joined to the
entry of the copy at `w ++ [j]`. -/
def IsGlue (x y : GAssembly σ) : Prop :=
  ∃ j : ℕ, y.copy = x.copy ++ [j] ∧ x.vert.1 = (σ x.copy).exitAddr ∧ y.vert.1 = []

/-- The adjacency of the assembly: the parent-child adjacency of the realisation
inside a copy, read on addresses as in `RTree.rtreeGraph_adj_iff`, together with the
gluing edges between the copies. -/
def Adj (x y : GAssembly σ) : Prop :=
  (x.copy = y.copy ∧ ((∃ b, y.vert.1 = x.vert.1 ++ [b]) ∨ ∃ b, x.vert.1 = y.vert.1 ++ [b]))
    ∨ IsGlue x y ∨ IsGlue y x

/-- A vertex at distance one from a vertex of a copy strictly above it is the entry
of a copy glued to the exit above. -/
lemma isGlue_of_dist_eq_one {u v : List ℕ} (huv : u <+: v) (hne : u ≠ v)
    (p : (gShapeSpace (σ u)).carrier) (q : (gShapeSpace (σ v)).carrier)
    (h : addrDist (gCopyAddr σ u ++ p.1) (gCopyAddr σ v ++ q.1) = 1) :
    IsGlue (⟨u, p⟩ : GAssembly σ) ⟨v, q⟩ := by
  rw [addrDist_gCopyAddr_anc σ huv hne (RTree.mem_addrList_iff.mp p.2)] at h
  have hlt : u.length < v.length := by
    rcases huv.length_le.lt_or_eq with h' | h'
    · exact h'
    · exact absurd (huv.eq_of_length h') hne
  have hsum : gNeckSum σ u v = 0 := by omega
  have hshort : v.length ≤ u.length + 1 := by
    by_contra hc
    rw [Nat.not_le] at hc
    have hmem : u.length + 1 ∈ Finset.Ico (u.length + 1) v.length :=
      Finset.mem_Ico.mpr ⟨le_refl _, hc⟩
    have hle := Finset.single_le_sum
      (f := fun i => (σ (v.take i)).neckLen) (fun i _ => Nat.zero_le _) hmem
    have hpos : 0 < (σ (v.take (u.length + 1))).neckLen := Nat.succ_pos _
    rw [← gNeckSum, hsum] at hle
    omega
  obtain ⟨s, rfl⟩ := huv
  have hslen : s.length = 1 := by
    simp only [List.length_append] at hlt hshort
    omega
  obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hslen
  have hzero : addrDist p.1 (σ u).exitAddr = 0 := by omega
  have hqlen : q.1.length = 0 := by omega
  exact ⟨j, rfl, addrDist_eq_zero_iff.mp hzero, List.length_eq_zero_iff.mp hqlen⟩

/-- **The assembly is glued along edges**: its metric is the graph metric of the
parent-child adjacency inside the copies together with the edges joining each exit to
the entries planted below it. -/
theorem dist_eq_one_iff_adj (x y : GAssembly σ) : dist x y = 1 ↔ Adj x y := by
  obtain ⟨u, p⟩ := x
  obtain ⟨v, q⟩ := y
  have hcast : dist (⟨u, p⟩ : GAssembly σ) ⟨v, q⟩ = 1
      ↔ addrDist (gCopyAddr σ u ++ p.1) (gCopyAddr σ v ++ q.1) = 1 := by
    simp only [dist_code, code]
    exact_mod_cast Iff.rfl
  rw [hcast]
  constructor
  · intro h
    rcases copy_trichotomy u v with rfl | ⟨huv, hne⟩ | ⟨hvu, hne⟩ | ⟨hu, hv⟩
    · rw [addrDist_gCopyAddr_same] at h
      exact Or.inl ⟨rfl, addrDist_eq_one_iff.mp h⟩
    · exact Or.inr (Or.inl (isGlue_of_dist_eq_one huv hne p q h))
    · rw [addrDist_comm] at h
      exact Or.inr (Or.inr (isGlue_of_dist_eq_one hvu hne q p h))
    · rw [addrDist_gCopyAddr_div σ hu hv] at h
      omega
  · rintro (⟨rfl, hadj⟩ | ⟨j, hv, hp, hq⟩ | ⟨j, hu, hq, hp⟩)
    · rw [addrDist_gCopyAddr_same]
      exact addrDist_eq_one_iff.mpr hadj
    · simp only at hv hp hq
      subst hv
      rw [addrDist_gCopyAddr_anc σ ⟨[j], rfl⟩ (by simp) (RTree.mem_addrList_iff.mp p.2), hp, hq]
      simp only [gNeckSum, addrDist_self, List.length_append, List.length_nil,
        List.length_singleton, Finset.Ico_self, Finset.sum_empty]
      omega
    · simp only at hu hq hp
      subst hu
      rw [addrDist_comm,
        addrDist_gCopyAddr_anc σ ⟨[j], rfl⟩ (by simp) (RTree.mem_addrList_iff.mp q.2), hq, hp]
      simp only [gNeckSum, addrDist_self, List.length_append, List.length_nil,
        List.length_singleton, Finset.Ico_self, Finset.sum_empty]
      omega

/-! ### The glued transfer -/

variable {σ' : List ℕ → GShape}

/-- **`thm:glued-transfer`**, the glued map: the per-shape maps, copy by copy. -/
def glue (φ : ∀ w : List ℕ, (gShapeSpace (σ w)).carrier → (gShapeSpace (σ' w)).carrier)
    (x : GAssembly σ) : GAssembly σ' := ⟨x.copy, φ x.copy x.vert⟩

/-- **`thm:glued-transfer`**, the neck sums: the comparison of `neck_bounds`, summed
over the intermediate copies. -/
lemma neckSum_bounds {K : ℝ} (hK : 1 ≤ K)
    (hφ : ∀ w, MarkedQI K (gShapeSpace (σ w)) (gShapeSpace (σ' w))) (a b : ℕ) (v : List ℕ) :
    (∑ i ∈ Finset.Ico a b, ((σ (v.take i)).neckLen : ℝ))
        ≤ 8 * K ^ 2 * ∑ i ∈ Finset.Ico a b, ((σ' (v.take i)).neckLen : ℝ)
      ∧ (∑ i ∈ Finset.Ico a b, ((σ' (v.take i)).neckLen : ℝ))
        ≤ 4 * K * ∑ i ∈ Finset.Ico a b, ((σ (v.take i)).neckLen : ℝ) := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hlen : ∀ τ : GShape, ((τ.neckLen : ℝ)) = (τ.necks : ℝ) + 1 := by
    intro τ; rw [GShape.neckLen]; push_cast; ring
  refine neck_sum_bounds _ hK (fun i _ => ?_) (fun i _ => ?_) (fun i _ => ?_) (fun i _ => ?_)
  · exact one_le_neckLen _
  · exact one_le_neckLen _
  · obtain ⟨f, hf⟩ := hφ (v.take i)
    have h := (neck_le_of_markedQI hK0 hf).1
    rw [dist_entry_exit, dist_entry_exit] at h
    rw [hlen, hlen]
    linarith
  · obtain ⟨f, hf⟩ := hφ (v.take i)
    have h := (neck_le_of_markedQI hK0 hf).2
    rw [dist_entry_exit, dist_entry_exit] at h
    rw [hlen, hlen]
    linarith

/-- **`thm:glued-transfer`** for two vertices in the ancestor position: the glued map
transfers the two mark distances and the neck sum of `eq:assembly-anc`, and every
constant fits `8K²`. -/
theorem glue_dist_bounds_anc {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : List ℕ, (gShapeSpace (σ w)).carrier → (gShapeSpace (σ' w)).carrier}
    (hφ : ∀ w, IsMarkedQI K (gShapeSpace (σ w)) (gShapeSpace (σ' w)) (φ w))
    {u v : List ℕ} (huv : u <+: v) (hne : u ≠ v)
    (p : (gShapeSpace (σ u)).carrier) (q : (gShapeSpace (σ v)).carrier) :
    dist (glue φ (⟨u, p⟩ : GAssembly σ)) (glue φ ⟨v, q⟩)
          ≤ 8 * K ^ 2 * dist (⟨u, p⟩ : GAssembly σ) ⟨v, q⟩ + 8 * K ^ 2
      ∧ dist (⟨u, p⟩ : GAssembly σ) ⟨v, q⟩
          ≤ 8 * K ^ 2 * dist (glue φ (⟨u, p⟩ : GAssembly σ)) (glue φ ⟨v, q⟩)
            + (8 * K ^ 2) ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hA := dist_mark_bounds hK0 (hφ u) (hφ u).exit p
  have hB := dist_mark_bounds hK0 (hφ v) (hφ v).entry q
  have hN := neckSum_bounds hK (fun w => ⟨φ w, hφ w⟩) (u.length + 1) v.length v
  exact glued_dist_bounds hK dist_nonneg dist_nonneg
    (Finset.sum_nonneg fun i _ => by positivity) dist_nonneg dist_nonneg zero_le_one
    hA.1 hA.2 hB.1 hB.2 hN.2 hN.1 (dist_anc σ huv hne p q) (dist_anc σ' huv hne (φ u p) (φ v q))

/-- **`thm:glued-transfer`** for two vertices in diverging copies: the same
comparison over `eq:assembly-div`, the neck sum now running over both branches. -/
theorem glue_dist_bounds_div {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : List ℕ, (gShapeSpace (σ w)).carrier → (gShapeSpace (σ' w)).carrier}
    (hφ : ∀ w, IsMarkedQI K (gShapeSpace (σ w)) (gShapeSpace (σ' w)) (φ w))
    {u v : List ℕ} (hu : ¬ u <+: v) (hv : ¬ v <+: u)
    (p : (gShapeSpace (σ u)).carrier) (q : (gShapeSpace (σ v)).carrier) :
    dist (glue φ (⟨u, p⟩ : GAssembly σ)) (glue φ ⟨v, q⟩)
          ≤ 8 * K ^ 2 * dist (⟨u, p⟩ : GAssembly σ) ⟨v, q⟩ + 8 * K ^ 2
      ∧ dist (⟨u, p⟩ : GAssembly σ) ⟨v, q⟩
          ≤ 8 * K ^ 2 * dist (glue φ (⟨u, p⟩ : GAssembly σ)) (glue φ ⟨v, q⟩)
            + (8 * K ^ 2) ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hA := dist_mark_bounds hK0 (hφ u) (hφ u).entry p
  have hB := dist_mark_bounds hK0 (hφ v) (hφ v).entry q
  have hNu := neckSum_bounds hK (fun w => ⟨φ w, hφ w⟩) ((wedgeN u v).length + 1) u.length u
  have hNv := neckSum_bounds hK (fun w => ⟨φ w, hφ w⟩) ((wedgeN u v).length + 1) v.length v
  refine glued_dist_bounds hK dist_nonneg dist_nonneg (by positivity) dist_nonneg dist_nonneg
    (by norm_num) hA.1 hA.2 hB.1 hB.2 ?_ ?_ (dist_div σ hu hv p q)
    (dist_div σ' hu hv (φ u p) (φ v q))
  · have h1 := hNu.2
    have h2 := hNv.2
    linarith
  · have h1 := hNu.1
    have h2 := hNv.1
    linarith

/-- **`thm:glued-transfer`**, coarse density: every vertex of the target assembly is
within `K` of the image, copy by copy. -/
lemma glue_dense {K : ℝ}
    {φ : ∀ w : List ℕ, (gShapeSpace (σ w)).carrier → (gShapeSpace (σ' w)).carrier}
    (hφ : ∀ w, IsMarkedQI K (gShapeSpace (σ w)) (gShapeSpace (σ' w)) (φ w))
    (y : GAssembly σ') :
    ∃ x : GAssembly σ, dist (glue φ x) y ≤ K := by
  obtain ⟨w, r⟩ := y
  obtain ⟨a, ha⟩ := (hφ w).dense r
  refine ⟨⟨w, a⟩, ?_⟩
  have h : dist (glue φ (⟨w, a⟩ : GAssembly σ)) (⟨w, r⟩ : GAssembly σ')
      = dist (φ w a) r := dist_same σ' w _ _
  rw [h]
  exact ha

/-- **`thm:glued-transfer`** at general arity (**`thm:general-glued`**): two families
of shapes that are `K`-comparable copy by copy have `8K²`-quasi-isometric assemblies,
the glued map being the per-shape maps read copy by copy. -/
theorem glued_transfer {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : List ℕ, (gShapeSpace (σ w)).carrier → (gShapeSpace (σ' w)).carrier}
    (hφ : ∀ w, IsMarkedQI K (gShapeSpace (σ w)) (gShapeSpace (σ' w)) (φ w)) :
    (∀ x y : GAssembly σ, dist (glue φ x) (glue φ y) ≤ 8 * K ^ 2 * dist x y + 8 * K ^ 2)
      ∧ (∀ x y : GAssembly σ, dist x y
          ≤ 8 * K ^ 2 * dist (glue φ x) (glue φ y) + (8 * K ^ 2) ^ 2)
      ∧ ∀ y : GAssembly σ', ∃ x : GAssembly σ, dist (glue φ x) y ≤ 8 * K ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have key : ∀ x y : GAssembly σ,
      dist (glue φ x) (glue φ y) ≤ 8 * K ^ 2 * dist x y + 8 * K ^ 2
        ∧ dist x y ≤ 8 * K ^ 2 * dist (glue φ x) (glue φ y) + (8 * K ^ 2) ^ 2 := by
    rintro ⟨u, p⟩ ⟨v, q⟩
    rcases copy_trichotomy u v with rfl | ⟨huv, hne⟩ | ⟨hvu, hne⟩ | ⟨hu, hv⟩
    · have e1 : dist (glue φ (⟨u, p⟩ : GAssembly σ)) (glue φ ⟨u, q⟩)
          = dist (φ u p) (φ u q) := dist_same σ' u _ _
      have e2 : dist (⟨u, p⟩ : GAssembly σ) ⟨u, q⟩ = dist p q := dist_same σ u p q
      rw [e1, e2]
      refine glued_dist_same hK dist_nonneg dist_nonneg ((hφ u).upper p q) ?_
      rw [pow_two]
      exact (hφ u).lower p q
    · exact glue_dist_bounds_anc hK hφ huv hne p q
    · obtain ⟨h1, h2⟩ := glue_dist_bounds_anc hK hφ hvu hne q p
      rw [dist_comm (glue φ (⟨u, p⟩ : GAssembly σ)), dist_comm (⟨u, p⟩ : GAssembly σ)]
      exact ⟨h1, h2⟩
    · exact glue_dist_bounds_div hK hφ hu hv p q
  refine ⟨fun x y => (key x y).1, fun x y => (key x y).2, fun y => ?_⟩
  obtain ⟨x, hx⟩ := glue_dense hφ y
  exact ⟨x, hx.trans (by nlinarith)⟩

end GAssembly

end ChainClasses
