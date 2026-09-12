import ChainClasses.General.GeneralShapeMetric

/-!
`sec:general-relabel` of `matching_classes_general.tex`: `thm:shape-connected` at
general arity, the leaf deletion of a realisation as a `1`-marked quasi-isometry, and
the connectivity of the label graph `G_D` over the enumeration of `𝒮` by size.

The deleted vertex is the rightmost leaf, the last child of its parent all the way
down, so the addresses of the shrunk tree are exactly the addresses of the tree with
the deleted one removed: no sibling is renamed.  The metric side is then graph
combinatorics alone: the inclusion of the shrunk vertex set is a parent-child
homomorphism, the retraction sending the deleted leaf to its parent moves one point by
one step, and both contract graph distances, which is the `1`-marked quasi-isometry.
The rightmost path of a realisation runs along the neck through the terminating split
into its bouquet, so the deletion shortens the last bouquet when there is one and
otherwise deletes the exit, whose parent is the new exit.

* `exists_walk_le_of_step`, `dist_le_dist_of_step`: a map sending edges to edges or
  equalities contracts graph distances.
* `markedQI_gSpace_del`: **the deletion of one leaf address is a `1`-marked
  quasi-isometry**, for marks equal to the deleted leaf or fixed by the deletion.
* `del_last_singleton`, `del_lift`, `exists_forest_del`: the rightmost leaf of a
  forest, its deletion, and the lift of a deletion through a last child.
* `exists_del_realiseAux`, `gOfList`, `exists_markedQI_gShrink`:
  **`thm:shape-connected` at general arity**, every shape of size at least two admits
  a `1`-marked quasi-isometry onto a shape of size one less.
* `netLink_connected_gShapeFamily`: **`thm:shape-connected`**, the label graph `G_D`
  on the general shapes enumerated by size is connected.
-/

namespace ChainClasses

open RTree

/-! ### Maps that contract graph distances -/

/-- A map sending edges to edges or equalities maps walks to walks of no greater
length. -/
lemma exists_walk_le_of_step {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}
    {f : V → V'} (hf : ∀ u v, G.Adj u v → f u = f v ∨ G'.Adj (f u) (f v))
    {x y : V} (p : G.Walk x y) : ∃ q : G'.Walk (f x) (f y), q.length ≤ p.length := by
  induction p with
  | nil => exact ⟨.nil, le_rfl⟩
  | cons h p ih =>
      obtain ⟨q, hq⟩ := ih
      rcases hf _ _ h with heq | hadj
      · refine ⟨q.copy heq.symm rfl, ?_⟩
        rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_cons]
        omega
      · refine ⟨.cons hadj q, ?_⟩
        rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons]
        omega

/-- A map sending edges to edges or equalities contracts graph distances. -/
lemma dist_le_dist_of_step {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}
    {f : V → V'} (hf : ∀ u v, G.Adj u v → f u = f v ∨ G'.Adj (f u) (f v))
    (hG : G.Connected) (x y : V) : G'.dist (f x) (f y) ≤ G.dist x y := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x y
  obtain ⟨q, hq⟩ := exists_walk_le_of_step hf p
  exact (SimpleGraph.dist_le q).trans (by omega)

/-! ### The deletion of one leaf address -/

section Del

variable {t t' : RTree} {ℓ : List ℕ}

/-- The deletion data: the shrunk tree carries exactly the addresses of the tree other
than the deleted leaf. -/
def IsAddrDel (t t' : RTree) (ℓ : List ℕ) : Prop :=
  IsAddr t ℓ ∧ ℓ ≠ [] ∧ (∀ w, IsAddr t w → w.dropLast ≠ ℓ) ∧
    ∀ w, IsAddr t' w ↔ IsAddr t w ∧ w ≠ ℓ

/-- Membership form of the deletion data. -/
lemma IsAddrDel.mem (h : IsAddrDel t t' ℓ) (w : List ℕ) :
    w ∈ addrList t' ↔ w ∈ addrList t ∧ w ≠ ℓ := by
  rw [mem_addrList_iff, mem_addrList_iff]
  exact h.2.2.2 w

/-- The parent of the deleted leaf survives the deletion. -/
lemma IsAddrDel.dropLast_mem (h : IsAddrDel t t' ℓ) : ℓ.dropLast ∈ addrList t' := by
  refine (h.mem _).mpr ⟨dropLast_mem_addrList t ℓ (mem_addrList_iff.mpr h.1), ?_⟩
  intro hc
  have hlen := congrArg List.length hc
  rw [List.length_dropLast] at hlen
  have hpos : 0 < ℓ.length := List.length_pos_iff.mpr h.2.1
  omega

/-- The distance of a marked space of a rose tree is the graph distance. -/
@[simp] lemma dist_gSpace {t : RTree} {e : List ℕ} (x y : (gSpace t e).carrier) :
    dist x y = ((rtreeGraph t).dist x y : ℝ) := rfl

/-- **The deletion of one leaf address is a `1`-marked quasi-isometry**: the inclusion
and the retraction to the parent contract distances, and the marks are the deleted
leaf, sent to its parent, or a surviving address, fixed. -/
theorem markedQI_gSpace_del {e e' : List ℕ} (hdel : IsAddrDel t t' ℓ)
    (he : IsAddr t e)
    (hee' : (e ≠ ℓ ∧ e' = e) ∨ (e = ℓ ∧ e' = ℓ.dropLast)) :
    MarkedQI 1 (gSpace t e) (gSpace t' e') := by
  classical
  obtain ⟨hℓ, hℓne, hleaf, hiff⟩ := hdel
  have hmem : ∀ w, w ∈ addrList t' ↔ w ∈ addrList t ∧ w ≠ ℓ :=
    IsAddrDel.mem ⟨hℓ, hℓne, hleaf, hiff⟩
  have hpar : ℓ.dropLast ∈ addrList t' :=
    IsAddrDel.dropLast_mem ⟨hℓ, hℓne, hleaf, hiff⟩
  -- the retraction and the inclusion
  set r : Vert t → Vert t' := fun x =>
    if hx : x.1 = ℓ then ⟨ℓ.dropLast, hpar⟩ else ⟨x.1, (hmem _).mpr ⟨x.2, hx⟩⟩ with hr
  set j : Vert t' → Vert t := fun y => ⟨y.1, ((hmem _).mp y.2).1⟩ with hj
  have hrval : ∀ x : Vert t, x.1 ≠ ℓ → (r x).1 = x.1 := by
    intro x hx
    rw [hr]
    simp [hx]
  have hrℓ : ∀ x : Vert t, x.1 = ℓ → (r x).1 = ℓ.dropLast := by
    intro x hx
    rw [hr]
    simp [hx]
  have hjval : ∀ y : Vert t', (j y).1 = y.1 := fun y => rfl
  -- the retraction sends edges to edges or equalities
  have hrstep : ∀ u v : Vert t, (rtreeGraph t).Adj u v →
      r u = r v ∨ (rtreeGraph t').Adj (r u) (r v) := by
    intro u v huv
    rw [rtreeGraph_adj] at huv
    obtain ⟨hne, hrel⟩ := huv
    by_cases hu : u.1 = ℓ
    · by_cases hv : v.1 = ℓ
      · exact absurd (Subtype.ext (hu.trans hv.symm)) hne
      · refine Or.inl (Subtype.ext ?_)
        rw [hrℓ u hu, hrval v hv]
        rcases hrel with h1 | h1
        · exact absurd (by rw [← h1, hu]) (hleaf v.1 (mem_addrList_iff.mp v.2))
        · rw [h1, hu]
    · by_cases hv : v.1 = ℓ
      · refine Or.inl (Subtype.ext ?_)
        rw [hrval u hu, hrℓ v hv]
        rcases hrel with h1 | h1
        · rw [h1, hv]
        · exact absurd (by rw [← h1, hv]) (hleaf u.1 (mem_addrList_iff.mp u.2))
      · refine Or.inr ?_
        rw [rtreeGraph_adj]
        constructor
        · intro hc
          refine hne (Subtype.ext ?_)
          have h1 := congrArg Subtype.val hc
          rwa [hrval u hu, hrval v hv] at h1
        · rw [hrval u hu, hrval v hv]
          exact hrel
  -- the inclusion sends edges to edges
  have hjstep : ∀ u v : Vert t', (rtreeGraph t').Adj u v →
      j u = j v ∨ (rtreeGraph t).Adj (j u) (j v) := by
    intro u v huv
    rw [rtreeGraph_adj] at huv
    refine Or.inr ?_
    rw [rtreeGraph_adj]
    constructor
    · intro hc
      apply huv.1
      apply Subtype.ext
      have h1 : (j u).1 = (j v).1 := congrArg Subtype.val hc
      exact h1
    · exact huv.2
  have hrj : ∀ y : Vert t', r (j y) = y := by
    intro y
    have hy : (j y).1 ≠ ℓ := ((hmem _).mp y.2).2
    exact Subtype.ext (hrval (j y) hy)
  -- the retraction moves each point by at most one step
  have hjrN : ∀ x : Vert t, (rtreeGraph t).dist x (j (r x)) ≤ 1 := by
    intro x
    by_cases hx : x.1 = ℓ
    · have hjrx : (j (r x)).1 = ℓ.dropLast := hrℓ x hx
      have hadj : (rtreeGraph t).Adj x (j (r x)) := by
        rw [rtreeGraph_adj]
        constructor
        · intro hc
          have hlen := congrArg (fun w : List ℕ => w.length) (congrArg Subtype.val hc)
          simp only [hjrx, hx, List.length_dropLast] at hlen
          have hpos : 0 < ℓ.length := List.length_pos_iff.mpr hℓne
          omega
        · exact Or.inr (by rw [hjrx, hx])
      have := SimpleGraph.dist_le (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
      simpa using this
    · have hfix : j (r x) = x := Subtype.ext (hrval x hx)
      rw [hfix, SimpleGraph.dist_self]
      omega
  -- distances contract both ways
  have hrdistN : ∀ u v : Vert t,
      (rtreeGraph t').dist (r u) (r v) ≤ (rtreeGraph t).dist u v :=
    fun u v => dist_le_dist_of_step hrstep (rtreeGraph_connected t) u v
  have hjdistN : ∀ u v : Vert t',
      (rtreeGraph t).dist (j u) (j v) ≤ (rtreeGraph t').dist u v :=
    fun u v => dist_le_dist_of_step hjstep (rtreeGraph_connected t') u v
  -- at most one endpoint is the deleted leaf
  have hlowerN : ∀ u v : Vert t,
      (rtreeGraph t).dist u v ≤ (rtreeGraph t').dist (r u) (r v) + 1 := by
    intro u v
    have htri1 := (rtreeGraph_connected t).dist_triangle
      (u := u) (v := j (r u)) (w := j (r v))
    have htri2 := (rtreeGraph_connected t).dist_triangle
      (u := u) (v := j (r v)) (w := v)
    have hmid := hjdistN (r u) (r v)
    by_cases hu : u.1 = ℓ
    · by_cases hv : v.1 = ℓ
      · have huv : u = v := Subtype.ext (hu.trans hv.symm)
        rw [huv, SimpleGraph.dist_self]
        omega
      · have h1 := hjrN u
        have h2 : j (r v) = v := Subtype.ext (hrval v hv)
        rw [h2] at htri1 hmid
        omega
    · have h1 : j (r u) = u := Subtype.ext (hrval u hu)
      have h2 := hjrN v
      have h2' : (rtreeGraph t).dist (j (r v)) v ≤ 1 := by
        rwa [SimpleGraph.dist_comm]
      rw [h1] at hmid
      omega
  -- assemble
  have hemem : e ∈ addrList t := mem_addrList_iff.mpr he
  refine ⟨r, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    rw [dist_gSpace, dist_gSpace, one_mul]
    exact_mod_cast (hrdistN a b).trans (Nat.le_succ _)
  · intro a b
    rw [dist_gSpace, dist_gSpace, one_mul, mul_one]
    exact_mod_cast hlowerN a b
  · intro y
    refine ⟨j y, ?_⟩
    rw [hrj y, dist_self]
    norm_num
  · have hroot : r (gSpace t e).entry = (gSpace t' e').entry := by
      refine Subtype.ext ?_
      exact hrval (rootVert t) fun hc => hℓne hc.symm
    rw [hroot, dist_self]
    norm_num
  · have hexit : (gSpace t e).exit = ⟨e, hemem⟩ := exit_gSpace_of_mem hemem
    rcases hee' with ⟨hne, he'⟩ | ⟨heℓ, he'⟩
    · rw [he']
      have he'mem : e ∈ addrList t' := (hmem _).mpr ⟨hemem, hne⟩
      have hfix : r (gSpace t e).exit = (gSpace t' e).exit := by
        rw [hexit, exit_gSpace_of_mem he'mem]
        exact Subtype.ext (hrval ⟨e, hemem⟩ hne)
      rw [hfix, dist_self]
      norm_num
    · rw [he']
      have hfix : r (gSpace t e).exit = (gSpace t' ℓ.dropLast).exit := by
        rw [hexit, exit_gSpace_of_mem hpar]
        exact Subtype.ext (hrℓ ⟨e, hemem⟩ heℓ)
      rw [hfix, dist_self]
      norm_num

end Del

/-! ### The rightmost leaf and its deletion -/

/-- Below the length of the forest, an address of the widened node reads the forest. -/
lemma isAddr_append_last_lt {cs : List RTree} {c : RTree} {i : ℕ} {v : List ℕ}
    (hi : i < cs.length) :
    IsAddr (.node (cs ++ [c])) (i :: v) ↔ IsAddr (.node cs) (i :: v) := by
  rw [isAddr_cons, isAddr_cons]
  constructor
  · rintro ⟨h, hv⟩
    refine ⟨hi, ?_⟩
    rwa [List.getElem_append_left hi] at hv
  · rintro ⟨h, hv⟩
    refine ⟨by simp only [List.length_append, List.length_cons, List.length_nil]; omega, ?_⟩
    rwa [List.getElem_append_left hi]

/-- At the length of the forest, an address of the widened node reads the last
child. -/
lemma isAddr_append_last_eq {cs : List RTree} {c : RTree} {v : List ℕ} :
    IsAddr (.node (cs ++ [c])) (cs.length :: v) ↔ IsAddr c v := by
  rw [isAddr_cons]
  constructor
  · rintro ⟨h, hv⟩
    rwa [show (cs ++ [c])[cs.length] = c by simp] at hv
  · intro hv
    refine ⟨by simp, ?_⟩
    rwa [show (cs ++ [c])[cs.length] = c by simp]

/-- No address starts past the arity. -/
lemma not_isAddr_of_length_le {cs : List RTree} {i : ℕ} {v : List ℕ}
    (hi : cs.length ≤ i) : ¬ IsAddr (.node cs) (i :: v) := by
  rw [isAddr_cons]
  rintro ⟨h, -⟩
  omega

/-- **Deleting a last child that is a leaf**: the addresses drop exactly the deleted
one, and no other vertex moves. -/
lemma del_last_singleton (init : List RTree) :
    IsAddrDel (.node (init ++ [.node []])) (.node init) [init.length] := by
  refine ⟨?_, by simp, ?_, ?_⟩
  · rw [isAddr_append_last_eq]
    exact isAddr_nil _
  · intro w hw
    cases w with
    | nil => simp
    | cons i v =>
        cases v with
        | nil => simp
        | cons a v' =>
            intro hc
            rw [dropLast_cons_of_ne_nil i (by simp)] at hc
            rw [List.cons.injEq] at hc
            obtain ⟨rfl, hc2⟩ := hc
            have hv' : (a :: v') = [a] := by
              have := congrArg List.length hc2
              rw [List.length_dropLast] at this
              simp only [List.length_cons, List.length_nil] at this
              have : v' = [] := List.length_eq_zero_iff.mp (by omega)
              rw [this]
            rw [hv'] at hw
            rw [isAddr_append_last_eq] at hw
            exact absurd hw (by rw [isAddr_cons]; rintro ⟨h, -⟩; simp at h)
  · intro w
    cases w with
    | nil => simp [isAddr_nil]
    | cons i v =>
        rcases lt_trichotomy i init.length with hi | rfl | hi
        · rw [isAddr_append_last_lt hi]
          constructor
          · intro h
            refine ⟨h, ?_⟩
            intro hc
            rw [List.cons.injEq] at hc
            omega
          · exact fun h => h.1
        · constructor
          · intro h
            exact absurd h (not_isAddr_of_length_le le_rfl)
          · rintro ⟨h, hne⟩
            rw [isAddr_append_last_eq] at h
            cases v with
            | nil => exact absurd rfl hne
            | cons a v' =>
                exact absurd h (by rw [isAddr_cons]; rintro ⟨hlt, -⟩; simp at hlt)
        · constructor
          · intro h
            exact absurd h (not_isAddr_of_length_le (by omega))
          · rintro ⟨h, -⟩
            exact absurd h (not_isAddr_of_length_le
              (by simp only [List.length_append, List.length_cons, List.length_nil]; omega))

/-- **The lift of a deletion through a last child**: deleting inside the last child of
a node deletes the corresponding address of the node. -/
lemma del_lift {u u' : RTree} {ℓ : List ℕ} (β : List RTree) (h : IsAddrDel u u' ℓ) :
    IsAddrDel (.node (β ++ [u])) (.node (β ++ [u'])) (β.length :: ℓ) := by
  obtain ⟨hℓ, hℓne, hleaf, hiff⟩ := h
  refine ⟨?_, by simp, ?_, ?_⟩
  · rw [isAddr_append_last_eq]
    exact hℓ
  · intro w hw
    cases w with
    | nil => simp
    | cons i v =>
        cases v with
        | nil => simp
        | cons a v' =>
            intro hc
            rw [dropLast_cons_of_ne_nil i (by simp)] at hc
            rw [List.cons.injEq] at hc
            obtain ⟨rfl, hc2⟩ := hc
            rw [isAddr_append_last_eq] at hw
            exact absurd hc2 (hleaf (a :: v') hw)
  · intro w
    cases w with
    | nil => simp [isAddr_nil]
    | cons i v =>
        rcases lt_trichotomy i β.length with hi | rfl | hi
        · rw [isAddr_append_last_lt hi, isAddr_append_last_lt hi]
          constructor
          · intro hv
            refine ⟨hv, ?_⟩
            intro hc
            rw [List.cons.injEq] at hc
            omega
          · exact fun hv => hv.1
        · rw [isAddr_append_last_eq, isAddr_append_last_eq, hiff]
          constructor
          · rintro ⟨hv, hne⟩
            exact ⟨hv, by simpa using hne⟩
          · rintro ⟨hv, hne⟩
            exact ⟨hv, by simpa using hne⟩
        · constructor
          · intro hv
            exact absurd hv (not_isAddr_of_length_le
              (by simp only [List.length_append, List.length_cons, List.length_nil]; omega))
          · rintro ⟨hv, -⟩
            exact absurd hv (not_isAddr_of_length_le
              (by simp only [List.length_append, List.length_cons, List.length_nil]; omega))

/-- **The rightmost leaf of a forest**: some leaf, the last child of its parent all
the way down, whose deletion removes exactly its address. -/
theorem exists_forest_del (β : List RTree) (hβ : β ≠ []) :
    ∃ (β' : List RTree) (ℓ : List ℕ),
      RTree.sizeF β' + 1 = RTree.sizeF β ∧ IsAddrDel (.node β) (.node β') ℓ := by
  generalize hn : RTree.sizeF β = n
  induction n using Nat.strong_induction_on generalizing β with
  | _ n ih =>
      obtain ⟨init, c, rfl⟩ : ∃ init c, β = init ++ [c] := by
        rcases List.eq_nil_or_concat β with rfl | ⟨init, c, hc⟩
        · exact absurd rfl hβ
        · exact ⟨init, c, by rw [hc, List.concat_eq_append]⟩
      obtain ⟨ds⟩ := c
      rcases eq_or_ne ds [] with rfl | hds
      · refine ⟨init, [init.length], ?_, del_last_singleton init⟩
        rw [RTree.sizeF_append] at hn
        simp only [RTree.sizeF, RTree.size] at hn
        omega
      · obtain ⟨es, d, rfl⟩ : ∃ es d, ds = es ++ [d] := by
          rcases List.eq_nil_or_concat ds with rfl | ⟨es, d, hc⟩
          · exact absurd rfl hds
          · exact ⟨es, d, by rw [hc, List.concat_eq_append]⟩
        have hn' : RTree.sizeF init + (1 + RTree.sizeF (es ++ [d])) = n := by
          rw [RTree.sizeF_append] at hn
          simp only [RTree.sizeF, RTree.size] at hn
          omega
        have hlt : RTree.sizeF (es ++ [d]) < n := by omega
        obtain ⟨ds', ℓd, hsz, hdel⟩ :=
          ih (RTree.sizeF (es ++ [d])) hlt (es ++ [d]) (by simp) rfl
        refine ⟨init ++ [.node ds'], init.length :: ℓd, ?_, del_lift init hdel⟩
        rw [RTree.sizeF_append]
        simp only [RTree.sizeF, RTree.size]
        omega

/-! ### The shrink of a shape -/

/-- **The deletion at the level of bush lists**: every realisation of two or more
vertices loses its rightmost leaf, a bush leaf of the terminating split when the
bouquet is nonempty and the exit itself otherwise, and the exit follows. -/
theorem exists_del_realiseAux :
    ∀ L : List (List RTree), L ≠ [] → 2 ≤ (GShape.realiseAux L).size →
      ∃ (L' : List (List RTree)) (ℓ : List ℕ),
        L' ≠ [] ∧
        (GShape.realiseAux L').size + 1 = (GShape.realiseAux L).size ∧
        IsAddrDel (GShape.realiseAux L) (GShape.realiseAux L') ℓ ∧
        ((gExitAddr L ≠ ℓ ∧ gExitAddr L' = gExitAddr L) ∨
          (gExitAddr L = ℓ ∧ gExitAddr L' = ℓ.dropLast))
  | [], hL, _ => absurd rfl hL
  | [β], _, hsize => by
      have hβ : β ≠ [] := by
        rintro rfl
        rw [show GShape.realiseAux [([] : List RTree)] = .node [] from rfl] at hsize
        rw [RTree.size] at hsize
        simp [RTree.sizeF] at hsize
      obtain ⟨β', ℓ, hsz, hdel⟩ := exists_forest_del β hβ
      refine ⟨[β'], ℓ, by simp, ?_, hdel, Or.inl ⟨?_, rfl⟩⟩
      · rw [show GShape.realiseAux [β'] = .node β' from rfl,
          show GShape.realiseAux [β] = .node β from rfl, RTree.size, RTree.size]
        omega
      · rw [gExitAddr_singleton]
        exact fun hc => hdel.2.1 hc.symm
  | β :: r :: rest, _, _ => by
      by_cases hsub : 2 ≤ (GShape.realiseAux (r :: rest)).size
      · obtain ⟨L'', ℓs, hL''ne, hsz, hdel, hexit⟩ :=
          exists_del_realiseAux (r :: rest) (by simp) hsub
        obtain ⟨r', rest', rfl⟩ : ∃ a b, L'' = a :: b := by
          cases L'' with
          | nil => exact absurd rfl hL''ne
          | cons a b => exact ⟨a, b, rfl⟩
        refine ⟨β :: r' :: rest', β.length :: ℓs, by simp, ?_, ?_, ?_⟩
        · rw [show GShape.realiseAux (β :: r' :: rest')
              = .node (β ++ [GShape.realiseAux (r' :: rest')]) from rfl,
            show GShape.realiseAux (β :: r :: rest)
              = .node (β ++ [GShape.realiseAux (r :: rest)]) from rfl,
            RTree.size, RTree.size, RTree.sizeF_append, RTree.sizeF_append]
          simp only [RTree.sizeF]
          omega
        · rw [show GShape.realiseAux (β :: r' :: rest')
              = .node (β ++ [GShape.realiseAux (r' :: rest')]) from rfl,
            show GShape.realiseAux (β :: r :: rest)
              = .node (β ++ [GShape.realiseAux (r :: rest)]) from rfl]
          exact del_lift β hdel
        · rw [gExitAddr_cons₂, gExitAddr_cons₂]
          rcases hexit with ⟨hne, heq⟩ | ⟨heq, heq'⟩
          · refine Or.inl ⟨?_, by rw [heq]⟩
            intro hc
            rw [List.cons.injEq] at hc
            exact hne hc.2
          · refine Or.inr ⟨by rw [heq], ?_⟩
            rw [heq', dropLast_cons_of_ne_nil β.length hdel.2.1]
      · have hone : (GShape.realiseAux (r :: rest)).size = 1 := by
          have h1 := RTree.size_pos (GShape.realiseAux (r :: rest))
          omega
        have hrest : rest = [] := by
          cases rest with
          | nil => rfl
          | cons c cs =>
              rw [show GShape.realiseAux (r :: c :: cs)
                  = .node (r ++ [GShape.realiseAux (c :: cs)]) from rfl, RTree.size,
                RTree.sizeF_append] at hone
              simp only [RTree.sizeF] at hone
              have := RTree.size_pos (GShape.realiseAux (c :: cs))
              omega
        subst hrest
        have hr : r = [] := by
          rw [show GShape.realiseAux [r] = .node r from rfl, RTree.size] at hone
          exact sizeF_eq_zero_iff.mp (by omega)
        subst hr
        refine ⟨[β], [β.length], by simp, ?_, ?_, Or.inr ⟨rfl, rfl⟩⟩
        · rw [show GShape.realiseAux [β] = .node β from rfl,
            show GShape.realiseAux (β :: [([] : List RTree)])
              = .node (β ++ [GShape.realiseAux [([] : List RTree)]]) from rfl,
            show GShape.realiseAux [([] : List RTree)] = .node [] from rfl,
            RTree.size, RTree.size, RTree.sizeF_append]
          simp only [RTree.sizeF, RTree.size]
          omega
        · rw [show GShape.realiseAux (β :: [([] : List RTree)])
              = .node (β ++ [GShape.realiseAux [([] : List RTree)]]) from rfl,
            show GShape.realiseAux [([] : List RTree)] = .node [] from rfl,
            show GShape.realiseAux [β] = .node β from rfl]
          exact del_last_singleton β

/-! ### The connectivity of the label graph -/

/-- A shape from a nonempty list of bush lists. -/
def gOfList (L : List (List RTree)) : GShape :=
  ⟨L.length - 1, fun i => L.getD (i : ℕ) []⟩

lemma decs_gOfList {L : List (List RTree)} (hL : L ≠ []) : (gOfList L).decs = L := by
  have hpos : 1 ≤ L.length := List.length_pos_iff.mpr hL
  refine List.ext_getElem ?_ ?_
  · rw [GShape.decs_length]
    show L.length - 1 + 1 = L.length
    omega
  · intro i h1 h2
    show (List.ofFn (gOfList L).dec)[i] = L[i]
    simp only [List.getElem_ofFn]
    exact List.getD_eq_getElem L [] h2

/-- **`thm:shape-connected` at general arity, the descent step**: every shape of size
at least two admits a `1`-marked quasi-isometry onto a shape of size one less, the
deletion of the rightmost leaf of its realisation. -/
theorem exists_markedQI_gShrink (σ : GShape) (hσ : 2 ≤ σ.size) :
    ∃ τ : GShape, τ.size + 1 = σ.size ∧ MarkedQI 1 (gShapeSpace σ) (gShapeSpace τ) := by
  obtain ⟨L', ℓ, hL'ne, hsz, hdel, hexit⟩ :=
    exists_del_realiseAux σ.decs σ.decs_ne_nil hσ
  refine ⟨gOfList L', ?_, ?_⟩
  · show (gOfList L').realise.size + 1 = σ.size
    rw [GShape.realise, decs_gOfList hL'ne]
    exact hsz
  · have hsp : gShapeSpace (gOfList L')
        = gSpace (GShape.realiseAux L') (gExitAddr L') := by
      rw [gShapeSpace, GShape.realise, GShape.exitAddr, decs_gOfList hL'ne]
    rw [hsp]
    exact markedQI_gSpace_del hdel (isAddr_realiseAux_gExitAddr σ.decs) hexit

/-- **`thm:shape-connected` at general arity**: the label graph `G_D` on the general
shapes enumerated by size is connected. -/
theorem netLink_connected_gShapeFamily {Dq : ℝ} (hD : 1 ≤ Dq) {a b : ℕ}
    (ha : netMem gShapeFamily Dq a) (hb : netMem gShapeFamily Dq b) :
    Relation.ReflTransGen (NetLink gShapeFamily Dq) a b := by
  have hzero : (gShapeEnum 0).size ≤ 1 := by
    obtain ⟨k, hk⟩ := gShapeEnum_surjective ⟨0, fun _ => []⟩
    have h := size_gShapeEnum_monotone (Nat.zero_le k)
    simp only [hk, size_bareNeck] at h
    exact h
  refine netLink_connected gShapeFamily Dq hD size_gShapeEnum_monotone
    (fun n hn => ?_) (fun n hn => ?_) ha hb
  · exact gShapeEnum_injective (GShape.eq_of_size_le_one hn hzero)
  · obtain ⟨τ, hsize, hqi⟩ := exists_markedQI_gShrink (gShapeEnum n) hn
    refine ⟨gShapeIdx τ, ?_, ?_⟩
    · rw [gShapeEnum_gShapeIdx]
      omega
    · show MarkedQI 1 (gShapeSpace (gShapeEnum n)) (gShapeSpace (gShapeEnum (gShapeIdx τ)))
      rw [gShapeEnum_gShapeIdx]
      exact hqi

end ChainClasses
