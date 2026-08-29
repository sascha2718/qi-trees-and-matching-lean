/-
`sec:general-relabel` of `matching_classes_general.tex`: the deterministic layer of
`thm:conditional-iid`, the shape field of a sample at general bounded support.

The `N = 2` field of `ShapeDecomposition` reads its shapes off ambient vertices through
the entry map, which the isometry with the assembly needs.  The law does not: here the
field is read off the skeleton recursion alone.  Descending from the root, `neckIter`
follows the unique surviving subtree, `gSplitDepth` counts the steps to the first vertex
with two surviving children, and the shape of `def:shape-general` collects the dying
subtrees of every vertex passed, the exit bouquet being the dying subtrees of the split
itself.  A copy below the split is addressed by a word whose letters pick surviving
children of successive splits, and `redSub` is the subfield the address leads to, so the
recursion `gShapeAt c (i :: u) = gShapeAt (gSplitBush c i) u` holds by definition.

* `ambSub`: the field of the subtree at an ambient vertex.
* `rtreeOf`, `sampleHeight`, `bushRTree`: a dying subtree read as a rose tree, the fuel
  exceeding its height.
* `gDecList`: the dying subtrees of the root, by rank, as the bush list of one shape
  vertex.
* `neckIter`, `gSplitDepth`, `gSplitField`, `gArity`, `gSplitBush`: the descent to the
  first split, the split subfield, its arity, and its surviving subtrees.
* `gShapeRoot`, `redSub`, `gShapeAt`, `gArityAt`: **the shape field with exit
  bouquets**, the shape and the arity of the copy at a reduced-skeleton address.
* `GShape.eq_of_decs`, `GShape.neckList`, `GShape.bouquet`, `GShape.decs_eq_append`: a
  shape is its bush lists, split into the neck lists and the exit bouquet.
* `gShapeRoot_split_iff` and `gShapeRoot_neck_iff`: the two readings of the field at
  the root, at a split and one step down a neck, which the law recursion of
  `GeneralShapeLaw` consumes.  The arity clause `2 ≤ κ` is what excludes the junk of a
  descent that never splits, so no splitting hypothesis is needed.
* `FibreMeasurableG` with its combinators, `measurableSet_sInf_mem_eq`, and the
  measurability of the field.
-/
import ChainClasses.GeneralShape
import BranchingProcess.Harris

namespace ChainClasses

open MeasureTheory
open BranchingProcess (sample Survives survivors skeletonDegree Offspring sampleMeasure
  survivalMeasure bushMeasure bushAt dyingAt)

/-- A vertex of the ambient `N`-ary tree, and likewise an address in the reduced
skeleton, whose letters pick surviving children of successive splits. -/
abbrev GWord (N : ℕ) : Type := BranchingProcess.Word N

variable {N : ℕ}

/-! ### The field at an ambient vertex -/

/-- The offspring field of the subtree at an ambient vertex. -/
def ambSub (c : GWord N → ℕ) (v : GWord N) : GWord N → ℕ := fun w ↦ c (v ++ w)

@[simp] lemma ambSub_nil (c : GWord N → ℕ) : ambSub c [] = c := by
  funext w
  rw [ambSub, List.nil_append]

lemma ambSub_apply (c : GWord N → ℕ) (v w : GWord N) : ambSub c v w = c (v ++ w) := rfl

lemma ambSub_ambSub (c : GWord N → ℕ) (v u : GWord N) :
    ambSub (ambSub c v) u = ambSub c (v ++ u) := by
  funext w
  simp [ambSub, List.append_assoc]

/-! ### A dying subtree as a rose tree -/

/-- A subtree read off an offspring field as a rose tree: the fuel bounds the depth, and
a vertex has one child per offspring number below the alphabet bound. -/
def rtreeOf : ℕ → (GWord N → ℕ) → RTree
  | 0, _ => .node []
  | n + 1, d =>
      .node (List.ofFn fun i : Fin (min (d []) N) ↦
        rtreeOf n (ambSub d [⟨(i : ℕ), lt_of_lt_of_le i.isLt (min_le_right _ _)⟩]))

/-- The height of a finite sample: the least bound on the lengths of its vertices. -/
noncomputable def sampleHeight (d : GWord N → ℕ) : ℕ :=
  sInf {n | ∀ u ∈ sample d, u.length ≤ n}

/-- **`def:shape-general`**, a bush: a dying subtree read as a rose tree, the fuel
exceeding its height. -/
noncomputable def bushRTree (d : GWord N → ℕ) : RTree := rtreeOf (sampleHeight d) d

/-! ### The decoration of the root -/

/-- The dying subtrees of the root, by rank, as the bush list of one vertex of a
shape. -/
noncomputable def gDecList (c : GWord N → ℕ) : List RTree :=
  List.ofFn fun m : Fin (c [] - skeletonDegree c) ↦ bushRTree (dyingAt c (m : ℕ))

lemma gDecList_def (c : GWord N → ℕ) :
    gDecList c
      = List.ofFn fun m : Fin (c [] - skeletonDegree c) ↦ bushRTree (dyingAt c (m : ℕ)) :=
  rfl

lemma length_gDecList (c : GWord N → ℕ) :
    (gDecList c).length = c [] - skeletonDegree c := by
  rw [gDecList_def, List.length_ofFn]

lemma getElem_gDecList (c : GWord N → ℕ) {m : ℕ} (hm : m < (gDecList c).length) :
    (gDecList c)[m] = bushRTree (dyingAt c m) := by
  simp [gDecList_def]

/-- The skeleton degree is at most the offspring count: the surviving children are
children. -/
lemma skeletonDegree_le_root (c : GWord N → ℕ) : skeletonDegree c ≤ c [] := by
  have hsub := BranchingProcess.survivors_subset c
  have hcard : skeletonDegree c ≤ (BranchingProcess.childSet N (c [])).card :=
    Finset.card_le_card hsub
  refine hcard.trans ?_
  have hinj : Set.InjOn (fun i : Fin N ↦ (i : ℕ))
      ↑(BranchingProcess.childSet N (c [])) := fun i _ j _ h ↦ Fin.ext h
  have himage : ∀ i ∈ BranchingProcess.childSet N (c []),
      (i : ℕ) ∈ Finset.range (c []) := by
    intro i hi
    rw [Finset.mem_range]
    exact BranchingProcess.mem_childSet.mp hi
  calc (BranchingProcess.childSet N (c [])).card
      = ((BranchingProcess.childSet N (c [])).image (fun i : Fin N ↦ (i : ℕ))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (c [])).card := Finset.card_le_card (by
        intro m hm
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
        exact himage i hi)
    _ = c [] := Finset.card_range _

/-! ### The descent to the first split -/

/-- The descent along the neck: each step passes to the first surviving subtree. -/
noncomputable def neckIter : (GWord N → ℕ) → ℕ → (GWord N → ℕ)
  | c, 0 => c
  | c, n + 1 => neckIter (bushAt c 0) n

@[simp] lemma neckIter_zero (c : GWord N → ℕ) : neckIter c 0 = c := rfl

lemma neckIter_succ (c : GWord N → ℕ) (n : ℕ) :
    neckIter c (n + 1) = neckIter (bushAt c 0) n := rfl

/-- **`eq:lambda-def` in the skeleton**: the depth of the first split along the neck of
the root. -/
noncomputable def gSplitDepth (c : GWord N → ℕ) : ℕ :=
  sInf {n | 2 ≤ skeletonDegree (neckIter c n)}

/-- The subfield at the split ending the chain of the root. -/
noncomputable def gSplitField (c : GWord N → ℕ) : GWord N → ℕ := neckIter c (gSplitDepth c)

/-- The arity of the split ending the chain of the root. -/
noncomputable def gArity (c : GWord N → ℕ) : ℕ := skeletonDegree (gSplitField c)

/-- The surviving subtrees of that split: the copies handed to the letters. -/
noncomputable def gSplitBush (c : GWord N → ℕ) (m : ℕ) : GWord N → ℕ :=
  bushAt (gSplitField c) m

/-- At a split the descent stops at once. -/
lemma gSplitDepth_eq_zero {c : GWord N → ℕ} (h : 2 ≤ skeletonDegree c) :
    gSplitDepth c = 0 :=
  Nat.le_zero.mp (Nat.sInf_le (by simpa using h))

@[simp] lemma gSplitField_of_depth_zero {c : GWord N → ℕ} (h : gSplitDepth c = 0) :
    gSplitField c = c := by
  rw [gSplitField, h, neckIter_zero]

/-- A descent that splits at all has a genuine first split. -/
lemma splitSet_nonempty_of_ne_zero {c : GWord N → ℕ} (h : gSplitDepth c ≠ 0) :
    {n | 2 ≤ skeletonDegree (neckIter c n)}.Nonempty := by
  by_contra hno
  rw [Set.not_nonempty_iff_eq_empty] at hno
  rw [gSplitDepth, hno, Nat.sInf_empty] at h
  exact h rfl

/-- An arity of two or more certifies that the descent splits. -/
lemma splitSet_nonempty_of_arity {c : GWord N → ℕ} (h : 2 ≤ gArity c) :
    {n | 2 ≤ skeletonDegree (neckIter c n)}.Nonempty := by
  by_contra hno
  rw [Set.not_nonempty_iff_eq_empty] at hno
  have h0 : gSplitDepth c = 0 := by rw [gSplitDepth, hno, Nat.sInf_empty]
  have haritydeg : gArity c = skeletonDegree c := by
    rw [gArity, gSplitField_of_depth_zero h0]
  have hmem : (0 : ℕ) ∈ {n | 2 ≤ skeletonDegree (neckIter c n)} := by
    simp only [Set.mem_setOf_eq, neckIter_zero]
    omega
  rw [hno] at hmem
  exact absurd hmem (Set.notMem_empty 0)

/-- The split set one step down a neck. -/
lemma splitSet_nonempty_down {c : GWord N → ℕ} (h1 : skeletonDegree c = 1)
    (hne : {n | 2 ≤ skeletonDegree (neckIter c n)}.Nonempty) :
    {n | 2 ≤ skeletonDegree (neckIter (bushAt c 0) n)}.Nonempty := by
  obtain ⟨n, hn⟩ := hne
  cases n with
  | zero =>
      simp only [Set.mem_setOf_eq, neckIter_zero] at hn
      omega
  | succ m =>
      rw [Set.mem_setOf_eq, neckIter_succ] at hn
      exact ⟨m, hn⟩

/-- **The descent one step down**: at a root with one surviving child the depth of the
first split is one more than in the surviving subtree. -/
lemma gSplitDepth_succ {c : GWord N → ℕ} (h1 : skeletonDegree c = 1)
    (hne : {n | 2 ≤ skeletonDegree (neckIter (bushAt c 0) n)}.Nonempty) :
    gSplitDepth c = gSplitDepth (bushAt c 0) + 1 := by
  have hmem : gSplitDepth (bushAt c 0)
      ∈ {n | 2 ≤ skeletonDegree (neckIter (bushAt c 0) n)} := Nat.sInf_mem hne
  have hup : gSplitDepth (bushAt c 0) + 1 ∈ {n | 2 ≤ skeletonDegree (neckIter c n)} := by
    rw [Set.mem_setOf_eq, neckIter_succ]
    exact hmem
  have hle : gSplitDepth c ≤ gSplitDepth (bushAt c 0) + 1 := Nat.sInf_le hup
  have h0 : gSplitDepth c ≠ 0 := by
    intro h0
    have hmem0 : (0 : ℕ) ∈ {n | 2 ≤ skeletonDegree (neckIter c n)} := by
      rw [← h0, gSplitDepth]
      exact Nat.sInf_mem ⟨_, hup⟩
    simp only [Set.mem_setOf_eq, neckIter_zero] at hmem0
    omega
  obtain ⟨m, hm⟩ : ∃ m, gSplitDepth c = m + 1 := ⟨gSplitDepth c - 1, by omega⟩
  have hmm : m + 1 ∈ {n | 2 ≤ skeletonDegree (neckIter c n)} := by
    rw [← hm, gSplitDepth]
    exact Nat.sInf_mem ⟨_, hup⟩
  rw [Set.mem_setOf_eq, neckIter_succ] at hmm
  have hlow : gSplitDepth (bushAt c 0) ≤ m :=
    Nat.sInf_le (show m ∈ {n | 2 ≤ skeletonDegree (neckIter (bushAt c 0) n)} from hmm)
  omega

/-- The split ending the chain, one step down a neck. -/
lemma gSplitField_step {c : GWord N → ℕ} (h1 : skeletonDegree c = 1)
    (hne : {n | 2 ≤ skeletonDegree (neckIter (bushAt c 0) n)}.Nonempty) :
    gSplitField c = gSplitField (bushAt c 0) := by
  rw [gSplitField, gSplitDepth_succ h1 hne, neckIter_succ, gSplitField]

lemma gArity_step {c : GWord N → ℕ} (h1 : skeletonDegree c = 1)
    (hne : {n | 2 ≤ skeletonDegree (neckIter (bushAt c 0) n)}.Nonempty) :
    gArity c = gArity (bushAt c 0) := by
  rw [gArity, gSplitField_step h1 hne, gArity]

lemma gSplitBush_step {c : GWord N → ℕ} (h1 : skeletonDegree c = 1)
    (hne : {n | 2 ≤ skeletonDegree (neckIter (bushAt c 0) n)}.Nonempty) (m : ℕ) :
    gSplitBush c m = gSplitBush (bushAt c 0) m := by
  rw [gSplitBush, gSplitField_step h1 hne, gSplitBush]

/-! ### The shape field -/

/-- **`def:shape-general` read in the sample**: the shape at the root, the bush list of
every vertex passed on the way to the first split, the exit bouquet being the dying
subtrees of the split itself. -/
noncomputable def gShapeRoot (c : GWord N → ℕ) : GShape where
  necks := gSplitDepth c
  dec := fun i ↦ gDecList (neckIter c (i : ℕ))

/-- The subfield at a reduced-skeleton address: each letter picks a surviving child of
the current split. -/
noncomputable def redSub : (GWord N → ℕ) → GWord N → (GWord N → ℕ)
  | c, [] => c
  | c, (i :: u) => redSub (gSplitBush c (i : ℕ)) u

@[simp] lemma redSub_nil (c : GWord N → ℕ) : redSub c [] = c := rfl

@[simp] lemma redSub_cons (c : GWord N → ℕ) (i : Fin N) (u : GWord N) :
    redSub c (i :: u) = redSub (gSplitBush c (i : ℕ)) u := rfl

/-- **The shape field with exit bouquets**: the shape of the copy at a reduced-skeleton
address. -/
noncomputable def gShapeAt (c : GWord N → ℕ) (u : GWord N) : GShape := gShapeRoot (redSub c u)

/-- **The arity field**: the arity of the terminating split of the copy at a
reduced-skeleton address. -/
noncomputable def gArityAt (c : GWord N → ℕ) (u : GWord N) : ℕ := gArity (redSub c u)

@[simp] lemma gShapeAt_nil (c : GWord N → ℕ) : gShapeAt c [] = gShapeRoot c := rfl

lemma gShapeAt_cons (c : GWord N → ℕ) (i : Fin N) (u : GWord N) :
    gShapeAt c (i :: u) = gShapeAt (gSplitBush c (i : ℕ)) u := rfl

@[simp] lemma gArityAt_nil (c : GWord N → ℕ) : gArityAt c [] = gArity c := rfl

lemma gArityAt_cons (c : GWord N → ℕ) (i : Fin N) (u : GWord N) :
    gArityAt c (i :: u) = gArityAt (gSplitBush c (i : ℕ)) u := rfl

/-! ### A shape is its bush lists -/

namespace GShape

/-- A shape is determined by its bush lists. -/
lemma eq_of_decs : ∀ {σ τ : GShape}, σ.decs = τ.decs → σ = τ := by
  rintro ⟨n, f⟩ ⟨m, g⟩ h
  have hlen : n = m := by
    have hl := congrArg List.length h
    simpa [GShape.decs] using hl
  subst hlen
  have hf : f = g := List.ofFn_injective h
  rw [hf]

/-- The bush lists of the neck vertices, the exit excluded. -/
def neckList (σ : GShape) : List (List RTree) :=
  List.ofFn fun i : Fin σ.necks ↦ σ.dec i.castSucc

/-- The exit bouquet, the bush list of the terminating split. -/
def bouquet (σ : GShape) : List RTree := σ.dec (Fin.last σ.necks)

/-- The bush lists are the neck lists followed by the exit bouquet. -/
lemma decs_eq_append (σ : GShape) : σ.decs = σ.neckList ++ [σ.bouquet] := by
  rw [decs, List.ofFn_succ', List.concat_eq_append]
  rfl

end GShape

/-- The bush lists of the shape at the root, one per vertex of the descent. -/
lemma decs_gShapeRoot (c : GWord N → ℕ) :
    (gShapeRoot c).decs
      = List.ofFn fun i : Fin (gSplitDepth c + 1) ↦ gDecList (neckIter c (i : ℕ)) := rfl

/-- A family read at the values of `Fin (n + 1)`, unfolded at a known length. -/
lemma ofFn_val_one_eq_singleton {α : Type*} {n : ℕ} (h : n = 0) (f : ℕ → α) :
    (List.ofFn fun i : Fin (n + 1) ↦ f (i : ℕ)) = [f 0] := by
  subst h
  simp [List.ofFn_succ]

/-- A family read at the values of `Fin (n + 1)`, decomposed at the head. -/
lemma ofFn_val_succ_eq_cons {α : Type*} {n m : ℕ} (h : n = m + 1) (f : ℕ → α) :
    (List.ofFn fun i : Fin (n + 1) ↦ f (i : ℕ))
      = f 0 :: List.ofFn fun i : Fin (m + 1) ↦ f ((i : ℕ) + 1) := by
  subst h
  rw [List.ofFn_succ]
  simp

/-- At a split the shape of the root is one bouquet. -/
lemma decs_gShapeRoot_of_depth_zero {c : GWord N → ℕ} (h : gSplitDepth c = 0) :
    (gShapeRoot c).decs = [gDecList c] := by
  rw [decs_gShapeRoot, ofFn_val_one_eq_singleton h (fun k ↦ gDecList (neckIter c k)),
    neckIter_zero]

/-- One neck step prepends the bush list of the root to the shape of the surviving
subtree. -/
lemma decs_gShapeRoot_cons {c : GWord N → ℕ} (h1 : skeletonDegree c = 1)
    (hne : {n | 2 ≤ skeletonDegree (neckIter (bushAt c 0) n)}.Nonempty) :
    (gShapeRoot c).decs = gDecList c :: (gShapeRoot (bushAt c 0)).decs := by
  have hd := gSplitDepth_succ h1 hne
  rw [decs_gShapeRoot, decs_gShapeRoot,
    ofFn_val_succ_eq_cons hd (fun k ↦ gDecList (neckIter c k))]
  simp only [neckIter_zero, neckIter_succ]

/-! ### The two readings of the field at the root -/

/-- **The root at a split**: the shape has one bush list exactly when the root is its
own split; the list is then the exit bouquet and the arity is the skeleton degree.  The
arity clause is what excludes a descent that never splits. -/
lemma gShapeRoot_split_iff {c : GWord N → ℕ} {β : List RTree} {κ : ℕ} (hκ : 2 ≤ κ) :
    ((gShapeRoot c).decs = [β] ∧ gArity c = κ)
      ↔ skeletonDegree c = κ ∧ gDecList c = β := by
  constructor
  · rintro ⟨hdecs, harity⟩
    have hlen : gSplitDepth c + 1 = 1 := by
      have hl := congrArg List.length hdecs
      rwa [decs_gShapeRoot, List.length_ofFn, List.length_cons, List.length_nil] at hl
    have hzero : gSplitDepth c = 0 := by omega
    have hβ : (gShapeRoot c).decs = [gDecList c] := decs_gShapeRoot_of_depth_zero hzero
    rw [hdecs] at hβ
    refine ⟨?_, (List.cons_eq_cons.mp hβ).1.symm⟩
    rw [← harity, gArity, gSplitField_of_depth_zero hzero]
  · rintro ⟨hdeg, hdec⟩
    have hzero : gSplitDepth c = 0 := gSplitDepth_eq_zero (by omega)
    refine ⟨by rw [decs_gShapeRoot_of_depth_zero hzero, hdec], ?_⟩
    rw [gArity, gSplitField_of_depth_zero hzero, hdeg]

/-- **The root at a neck vertex**: the shape has a bush list followed by at least one
more exactly when the root has one surviving child whose subtree carries the rest, and
the arity, the split subtrees and their constraints pass to that subtree.  Junk is
excluded on the left by the second bush list and on the right by the arity clause. -/
lemma gShapeRoot_neck_iff {c : GWord N → ℕ} (hsurv : Survives c) {β : List RTree}
    {M : List (List RTree)} (hM : M ≠ []) {κ : ℕ} (hκ : 2 ≤ κ)
    (A : ℕ → Set (GWord N → ℕ)) :
    ((gShapeRoot c).decs = β :: M ∧ gArity c = κ
        ∧ ∀ m : ℕ, m < κ → gSplitBush c m ∈ A m)
      ↔ skeletonDegree c = 1 ∧ gDecList c = β
          ∧ ((gShapeRoot (bushAt c 0)).decs = M ∧ gArity (bushAt c 0) = κ
              ∧ ∀ m : ℕ, m < κ → gSplitBush (bushAt c 0) m ∈ A m) := by
  constructor
  · rintro ⟨hdecs, harity, hbush⟩
    have hlen : gSplitDepth c + 1 = M.length + 1 := by
      have hl := congrArg List.length hdecs
      rwa [decs_gShapeRoot, List.length_ofFn, List.length_cons] at hl
    have hMpos : 1 ≤ M.length := List.length_pos_iff.mpr hM
    have hdne : gSplitDepth c ≠ 0 := by omega
    have hSne := splitSet_nonempty_of_ne_zero hdne
    have h0 : (0 : ℕ) ∉ {n | 2 ≤ skeletonDegree (neckIter c n)} := by
      intro h0
      have := Nat.sInf_le h0
      rw [← gSplitDepth] at this
      omega
    have hdeg1 : skeletonDegree c = 1 := by
      have hle : skeletonDegree c ≤ 1 := by
        by_contra hgt
        exact h0 (by simpa using (by omega : 2 ≤ skeletonDegree c))
      have hne0 : skeletonDegree c ≠ 0 :=
        BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp hsurv
      omega
    have hne' := splitSet_nonempty_down hdeg1 hSne
    have hrec := decs_gShapeRoot_cons hdeg1 hne'
    rw [hdecs] at hrec
    obtain ⟨hβ, hMdecs⟩ := List.cons_eq_cons.mp hrec
    refine ⟨hdeg1, hβ.symm, hMdecs.symm, ?_, ?_⟩
    · rw [← gArity_step hdeg1 hne']
      exact harity
    · intro m hm
      rw [← gSplitBush_step hdeg1 hne' m]
      exact hbush m hm
  · rintro ⟨hdeg1, hdec, hMdecs, harity, hbush⟩
    have hne' : {n | 2 ≤ skeletonDegree (neckIter (bushAt c 0) n)}.Nonempty :=
      splitSet_nonempty_of_arity (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [decs_gShapeRoot_cons hdeg1 hne', hdec, hMdecs]
    · rw [gArity_step hdeg1 hne']
      exact harity
    · intro m hm
      rw [gSplitBush_step hdeg1 hne' m]
      exact hbush m hm

/-! ### Countably valued functions of the field, presented by their fibres -/

/-- **A countably valued function of the offspring field, presented by its fibres**, at
general arity.  The values below are rose trees, lists and shapes, none of which carries
a measurable structure, so measurability is stated as the events `{c | f c = x}`. -/
def FibreMeasurableG {X : Type*} (f : (GWord N → ℕ) → X) : Prop :=
  ∀ x : X, MeasurableSet {c : GWord N → ℕ | f c = x}

namespace FibreMeasurableG

lemma congr {X : Type*} {f g : (GWord N → ℕ) → X} (hf : FibreMeasurableG f)
    (h : ∀ c, f c = g c) : FibreMeasurableG g := by
  intro x
  have he : {c : GWord N → ℕ | g c = x} = {c : GWord N → ℕ | f c = x} := by
    ext c
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h c]
  rw [he]
  exact hf x

lemma const {X : Type*} (x₀ : X) : FibreMeasurableG (fun _ : GWord N → ℕ ↦ x₀) := by
  intro x
  by_cases h : x₀ = x
  · have he : {c : GWord N → ℕ | x₀ = x} = Set.univ := by ext c; simp [h]
    rw [he]
    exact MeasurableSet.univ
  · have he : {c : GWord N → ℕ | x₀ = x} = ∅ := by ext c; simp [h]
    rw [he]
    exact MeasurableSet.empty

/-- A countable family of values is an event. -/
lemma preimage {X : Type*} [Countable X] {f : (GWord N → ℕ) → X}
    (hf : FibreMeasurableG f) (s : Set X) : MeasurableSet {c : GWord N → ℕ | f c ∈ s} := by
  have he : {c : GWord N → ℕ | f c ∈ s} = ⋃ x ∈ s, {c : GWord N → ℕ | f c = x} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    exact ⟨fun hc ↦ ⟨f c, hc, rfl⟩, by rintro ⟨x, hx, rfl⟩; exact hx⟩
  rw [he]
  exact MeasurableSet.biUnion (Set.to_countable _) fun x _ ↦ hf x

lemma map {X Y : Type*} [Countable X] {g : (GWord N → ℕ) → X}
    (hg : FibreMeasurableG g) (φ : X → Y) : FibreMeasurableG (fun c ↦ φ (g c)) := fun y ↦ by
  have he : {c : GWord N → ℕ | φ (g c) = y} = {c : GWord N → ℕ | g c ∈ {x : X | φ x = y}} :=
    rfl
  rw [he]
  exact hg.preimage _

lemma prod {X Y : Type*} {f : (GWord N → ℕ) → X} {g : (GWord N → ℕ) → Y}
    (hf : FibreMeasurableG f) (hg : FibreMeasurableG g) :
    FibreMeasurableG (fun c ↦ (f c, g c)) := by
  rintro ⟨x, y⟩
  have he : {c : GWord N → ℕ | (f c, g c) = (x, y)}
      = {c : GWord N → ℕ | f c = x} ∩ {c : GWord N → ℕ | g c = y} := by
    ext c
    simp [Prod.ext_iff]
  rw [he]
  exact (hf x).inter (hg y)

/-- Substituting a countably valued function into a family keeps the fibres events. -/
lemma comp {X Y : Type*} [Countable X] {g : (GWord N → ℕ) → X}
    {h : X → (GWord N → ℕ) → Y} (hg : FibreMeasurableG g)
    (hh : ∀ x, FibreMeasurableG (h x)) : FibreMeasurableG (fun c ↦ h (g c) c) := by
  intro y
  have he : {c : GWord N → ℕ | h (g c) c = y}
      = ⋃ x : X, ({c : GWord N → ℕ | g c = x} ∩ {c : GWord N → ℕ | h x c = y}) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun hc ↦ ⟨g c, rfl, hc⟩, by rintro ⟨x, hx, hc⟩; rw [hx]; exact hc⟩
  rw [he]
  exact MeasurableSet.iUnion fun x ↦ (hg x).inter (hh x y)

lemma pi {X ι : Type*} [Countable ι] {g : ι → (GWord N → ℕ) → X}
    (hg : ∀ i, FibreMeasurableG (g i)) : FibreMeasurableG (fun c ↦ fun i ↦ g i c) := by
  intro f
  have he : {c : GWord N → ℕ | (fun i ↦ g i c) = f} = ⋂ i, {c : GWord N → ℕ | g i c = f i} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter, funext_iff]
  rw [he]
  exact MeasurableSet.iInter fun i ↦ hg i (f i)

end FibreMeasurableG

/-- The first index at which a family of events occurs is countably valued and its
fibres are events. -/
lemma measurableSet_sInf_mem_eq {α : Type*} [MeasurableSpace α] {P : ℕ → Set α}
    (hP : ∀ k, MeasurableSet (P k)) (n : ℕ) :
    MeasurableSet {a : α | sInf {k | a ∈ P k} = n} := by
  have hle : ∀ (a : α) (k : ℕ), a ∈ P k → sInf {k | a ∈ P k} ≤ k :=
    fun a k hk ↦ Nat.sInf_le (show k ∈ {k | a ∈ P k} from hk)
  have hmem : ∀ (a : α) (k : ℕ), a ∈ P k → a ∈ P (sInf {k | a ∈ P k}) :=
    fun a k hk ↦ Nat.sInf_mem (s := {k | a ∈ P k}) ⟨k, hk⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have he : {a : α | sInf {k | a ∈ P k} = 0} = P 0 ∪ ⋂ k : ℕ, (P k)ᶜ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iInter, Set.mem_compl_iff]
      constructor
      · intro h
        by_cases hex : ∃ k, a ∈ P k
        · obtain ⟨k, hk⟩ := hex
          have ha := hmem a k hk
          rw [h] at ha
          exact Or.inl ha
        · exact Or.inr fun k hk ↦ hex ⟨k, hk⟩
      · rintro (h0 | hall)
        · exact Nat.le_zero.mp (hle a 0 h0)
        · have hempty : {k | a ∈ P k} = ∅ := by ext k; simp [hall k]
          rw [hempty, Nat.sInf_empty]
    rw [he]
    exact (hP 0).union (MeasurableSet.iInter fun k ↦ (hP k).compl)
  · have he : {a : α | sInf {k | a ∈ P k} = n}
        = P n ∩ ⋂ k ∈ Finset.range n, (P k)ᶜ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
        Finset.mem_range]
      constructor
      · intro h
        have hex : ∃ k, a ∈ P k := by
          by_contra hno
          have hempty : {k | a ∈ P k} = ∅ := by
            ext k
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            exact fun hk ↦ hno ⟨k, hk⟩
          rw [hempty, Nat.sInf_empty] at h
          omega
        obtain ⟨k, hk⟩ := hex
        refine ⟨by rw [← h]; exact hmem a k hk, fun j hj hjc ↦ ?_⟩
        have := hle a j hjc
        omega
      · rintro ⟨hn', hmin⟩
        refine le_antisymm (hle a n hn') ?_
        by_contra hlt
        rw [not_le] at hlt
        exact hmin _ hlt (hmem a n hn')
    rw [he]
    exact (hP n).inter (MeasurableSet.biInter (Set.to_countable _) fun k _ ↦ (hP k).compl)

/-! ### The field is measurable -/

/-- The field at an ambient vertex is a measurable function of the field. -/
lemma measurable_ambSub (v : GWord N) : Measurable (fun c : GWord N → ℕ ↦ ambSub c v) :=
  measurable_pi_lambda _ fun w ↦ measurable_pi_apply (v ++ w)

lemma fibreMeasurableG_coord (v : GWord N) : FibreMeasurableG (fun c : GWord N → ℕ ↦ c v) := by
  intro j
  have he : {c : GWord N → ℕ | c v = j} = (fun c : GWord N → ℕ ↦ c v) ⁻¹' {j} := rfl
  rw [he]
  exact measurable_pi_apply v MeasurableSet.of_discrete

lemma fibreMeasurableG_skeletonDegree :
    FibreMeasurableG (skeletonDegree : (GWord N → ℕ) → ℕ) := fun k ↦
  BranchingProcess.measurableSet_skeletonDegree_eq k

/-- The height of the sample of a field is countably valued with measurable fibres. -/
lemma fibreMeasurableG_sampleHeight : FibreMeasurableG (sampleHeight : (GWord N → ℕ) → ℕ) := by
  intro m
  have hP : ∀ n : ℕ,
      MeasurableSet {d : GWord N → ℕ | ∀ u ∈ sample d, u.length ≤ n} := by
    intro n
    have he : {d : GWord N → ℕ | ∀ u ∈ sample d, u.length ≤ n}
        = ⋂ u ∈ {u : GWord N | n < u.length}, {d : GWord N → ℕ | u ∈ sample d}ᶜ := by
      ext d
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
      constructor
      · intro h u hu hmem
        have hlen := h u hmem
        have hu' : n < u.length := hu
        omega
      · intro h u hu
        by_contra hlt
        exact h u (show n < u.length by omega) hu
    rw [he]
    exact MeasurableSet.biInter (Set.to_countable _)
      fun u _ ↦ (BranchingProcess.measurableSet_mem_sample u).compl
  exact measurableSet_sInf_mem_eq hP m

/-- A rose tree read at a fixed fuel is countably valued with measurable fibres. -/
lemma fibreMeasurableG_rtreeOf : ∀ n : ℕ, FibreMeasurableG (rtreeOf (N := N) n)
  | 0 => FibreMeasurableG.const _
  | n + 1 => by
      have key : ∀ j : ℕ, FibreMeasurableG (fun d : GWord N → ℕ ↦
          RTree.node (List.ofFn fun i : Fin (min j N) ↦
            rtreeOf n (ambSub d [⟨(i : ℕ), lt_of_lt_of_le i.isLt (min_le_right _ _)⟩]))) := by
        intro j
        have hvec : FibreMeasurableG (fun d : GWord N → ℕ ↦
            (fun i : Fin (min j N) ↦
              rtreeOf n (ambSub d [⟨(i : ℕ), lt_of_lt_of_le i.isLt (min_le_right _ _)⟩]))) :=
          FibreMeasurableG.pi fun i ↦ fun t ↦
            measurable_ambSub _ (fibreMeasurableG_rtreeOf n t)
        exact hvec.map (fun v ↦ RTree.node (List.ofFn v))
      exact (FibreMeasurableG.comp (g := fun d : GWord N → ℕ ↦ d [])
        (fibreMeasurableG_coord []) key).congr fun _ ↦ rfl

/-- A dying subtree read as a rose tree is countably valued with measurable fibres. -/
lemma fibreMeasurableG_bushRTree : FibreMeasurableG (bushRTree : (GWord N → ℕ) → RTree) :=
  (FibreMeasurableG.comp fibreMeasurableG_sampleHeight
    fun n ↦ fibreMeasurableG_rtreeOf n).congr fun _ ↦ rfl

/-- The bush list of the root is countably valued with measurable fibres. -/
lemma fibreMeasurableG_gDecList : FibreMeasurableG (gDecList : (GWord N → ℕ) → List RTree) := by
  have hcount : FibreMeasurableG (fun c : GWord N → ℕ ↦ c [] - skeletonDegree c) :=
    ((fibreMeasurableG_coord []).prod fibreMeasurableG_skeletonDegree).map
      fun p ↦ p.1 - p.2
  have key : ∀ r : ℕ, FibreMeasurableG (fun c : GWord N → ℕ ↦
      List.ofFn fun m : Fin r ↦ bushRTree (dyingAt c (m : ℕ))) := by
    intro r
    have hvec : FibreMeasurableG (fun c : GWord N → ℕ ↦
        (fun m : Fin r ↦ bushRTree (dyingAt c (m : ℕ)))) :=
      FibreMeasurableG.pi fun m ↦ fun t ↦
        BranchingProcess.measurable_dyingAt (m : ℕ) (fibreMeasurableG_bushRTree t)
    exact hvec.map List.ofFn
  exact (FibreMeasurableG.comp hcount key).congr fun _ ↦ rfl

/-- The descent is a measurable function of the field. -/
lemma measurable_neckIter : ∀ n : ℕ, Measurable (fun c : GWord N → ℕ ↦ neckIter c n)
  | 0 => measurable_id
  | n + 1 => (measurable_neckIter n).comp (BranchingProcess.measurable_bushAt 0)

/-- The depth of the first split is countably valued with measurable fibres. -/
lemma fibreMeasurableG_gSplitDepth :
    FibreMeasurableG (gSplitDepth : (GWord N → ℕ) → ℕ) := by
  intro n
  exact measurableSet_sInf_mem_eq
    (P := fun k ↦ {c : GWord N → ℕ | 2 ≤ skeletonDegree (neckIter c k)})
    (fun k ↦ measurable_neckIter k
      (fibreMeasurableG_skeletonDegree.preimage {m : ℕ | 2 ≤ m})) n

/-- The subfield at the split is a measurable function of the field. -/
lemma measurable_gSplitField : Measurable (gSplitField : (GWord N → ℕ) → GWord N → ℕ) := by
  intro t ht
  have he : gSplitField ⁻¹' t
      = ⋃ n : ℕ, ({c : GWord N → ℕ | gSplitDepth c = n}
          ∩ (fun c : GWord N → ℕ ↦ neckIter c n) ⁻¹' t) := by
    ext c
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hc
      exact ⟨gSplitDepth c, rfl, hc⟩
    · rintro ⟨n, hn, hc⟩
      rwa [gSplitField, hn]
  rw [he]
  exact MeasurableSet.iUnion fun n ↦
    (fibreMeasurableG_gSplitDepth n).inter (measurable_neckIter n ht)

lemma fibreMeasurableG_gArity : FibreMeasurableG (gArity : (GWord N → ℕ) → ℕ) := fun k ↦
  measurable_gSplitField (BranchingProcess.measurableSet_skeletonDegree_eq k)

lemma measurable_gSplitBush (m : ℕ) :
    Measurable (fun c : GWord N → ℕ ↦ gSplitBush c m) :=
  (BranchingProcess.measurable_bushAt m).comp measurable_gSplitField

lemma measurable_redSub (u : GWord N) : Measurable (fun c : GWord N → ℕ ↦ redSub c u) := by
  induction u with
  | nil => exact measurable_id
  | cons i u ih => exact ih.comp (measurable_gSplitBush (i : ℕ))

/-- The shape of the root is countably valued with measurable fibres. -/
lemma fibreMeasurableG_gShapeRoot :
    FibreMeasurableG (gShapeRoot : (GWord N → ℕ) → GShape) := by
  have key : ∀ n : ℕ, FibreMeasurableG (fun c : GWord N → ℕ ↦
      (⟨n, fun i : Fin (n + 1) ↦ gDecList (neckIter c (i : ℕ))⟩ : GShape)) := by
    intro n
    have hvec : FibreMeasurableG (fun c : GWord N → ℕ ↦
        (fun i : Fin (n + 1) ↦ gDecList (neckIter c (i : ℕ)))) :=
      FibreMeasurableG.pi fun i ↦ fun l ↦
        measurable_neckIter (i : ℕ) (fibreMeasurableG_gDecList l)
    exact hvec.map fun f ↦ (⟨n, f⟩ : GShape)
  exact (FibreMeasurableG.comp fibreMeasurableG_gSplitDepth key).congr fun _ ↦ rfl

/-- **The shape field is measurable**: for every copy and every shape the event that the
copy carries the shape is measurable. -/
theorem fibreMeasurableG_gShapeAt (u : GWord N) :
    FibreMeasurableG (fun c : GWord N → ℕ ↦ gShapeAt c u) := fun σ ↦
  measurable_redSub u (fibreMeasurableG_gShapeRoot σ)

/-- **The arity field is measurable.** -/
theorem fibreMeasurableG_gArityAt (u : GWord N) :
    FibreMeasurableG (fun c : GWord N → ℕ ↦ gArityAt c u) := fun k ↦
  measurable_redSub u (fibreMeasurableG_gArity k)

end ChainClasses
