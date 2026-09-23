import Mathlib.Data.Set.Finite.List
import ChainClasses.General.GeneralShapeLaw
import ChainClasses.Shape.ContractAddr
import BranchingProcess.Progeny

/-!
`thm:mass-uniform` of `matching_classes_general.tex`, the bush factors: the point mass
of a prescribed bush under the conjugate law, at general bounded support.

A bush enters the masses of `GeneralShapeLaw` through the events `{d | bushRTree d = t}`.
The tree a subtree realises is determined by its sample alone: `rtreeOf` reads only the
sample coordinates, and its fuel is immaterial past any height bound.  A rose tree with
degrees in the support therefore pins the event down to a sample equality, whose mass
`BranchingProcess.Progeny` bounds below by one factor per vertex, and the bound
transfers with the exponent `|t|`, the sample of the witness field having at most `|t|`
vertices.

* `sampleHeight_spec`, `rtreeOf_eq_of_bound`, `bushRTree_eq_rtreeOf`: the fuel is
  immaterial past any height bound of a finite subtree.
* `rtreeOf_eq_of_sample_eq`, `bushRTree_eq_of_sample_eq`: **the realised tree is
  determined by the sample**.
* `RTree.degR`, `fieldOfR`: the offspring field cutting out a prescribed rose tree.
* `length_lt_size_of_mem_sample_fieldOfR`, `not_survives_fieldOfR`,
  `ncard_sample_fieldOfR_le`: its sample is finite with at most `|t|` vertices.
* `rtreeOf_fieldOfR`, `bushRTree_fieldOfR`: the field realises the tree it is cut from.
* `RTree.ChargedT`, `pminOff`: degrees in the support, and the least positive mass of
  the law.
* `bushMassR`, `ofReal_pow_le_bushMassR`: **the point mass of a bush**, one factor of
  `pminOff θ` per vertex.
-/

namespace ChainClasses

open MeasureTheory
open scoped ENNReal
open BranchingProcess (sample Survives skeletonDegree Offspring sampleMeasure
  survivalMeasure bushMeasure)

variable {J N : ℕ}

/-! ### The fuel is immaterial past a height bound -/

/-- The sample height is a genuine bound once the subtree is finite. -/
lemma sampleHeight_spec {d : GWord N → ℕ} (hfin : ¬ Survives d) :
    ∀ u ∈ sample d, u.length ≤ sampleHeight d := by
  have hfin' : (sample d : Set (GWord N)).Finite := Set.not_infinite.mp hfin
  obtain ⟨n, hn⟩ := (hfin'.image List.length).bddAbove
  have hmem : n ∈ {n | ∀ u ∈ sample d, u.length ≤ n} := fun u hu ↦ hn ⟨u, hu, rfl⟩
  exact Nat.sInf_mem ⟨n, hmem⟩

/-- A child of the root of a sample, unfolded through `ambSub`. -/
lemma mem_sample_cons_ambSub {d : GWord N → ℕ} {i : Fin N} {u : GWord N} :
    i :: u ∈ sample d ↔ (i : ℕ) < d [] ∧ u ∈ sample (ambSub d [i]) :=
  BranchingProcess.mem_sample_cons_iff

/-- The sample of a child subfield inherits a height bound, one shorter. -/
lemma sample_bound_ambSub {d : GWord N → ℕ} {n : ℕ}
    (hn : ∀ u ∈ sample d, u.length ≤ n + 1) (i : Fin N) (hi : (i : ℕ) < d []) :
    ∀ u ∈ sample (ambSub d [i]), u.length ≤ n := by
  intro u hu
  have hmem : i :: u ∈ sample d := mem_sample_cons_ambSub.mpr ⟨hi, hu⟩
  have := hn _ hmem
  simp only [List.length_cons] at this
  omega

/-- **The fuel is immaterial past a height bound**: any fuel at least a bound on the
sample reads the same tree as the bound itself. -/
lemma rtreeOf_eq_of_bound : ∀ (n : ℕ) {d : GWord N → ℕ},
    (∀ u ∈ sample d, u.length ≤ n) → ∀ {m : ℕ}, n ≤ m → rtreeOf m d = rtreeOf n d := by
  intro n
  induction n with
  | zero =>
      intro d hd m _
      have hmin : min (d []) N = 0 := by
        by_contra h0
        have hN : 0 < N := by omega
        have h1 : 0 < d [] := by omega
        have hmem : (⟨0, hN⟩ : Fin N) :: ([] : GWord N) ∈ sample d :=
          mem_sample_cons_ambSub.mpr ⟨h1, BranchingProcess.nil_mem_sample _⟩
        have := hd _ hmem
        simp at this
      cases m with
      | zero => rfl
      | succ m =>
          show RTree.node _ = RTree.node []
          refine congrArg RTree.node (List.eq_nil_of_length_eq_zero ?_)
          rw [List.length_ofFn, hmin]
  | succ n ih =>
      intro d hd m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      show RTree.node _ = RTree.node _
      refine congrArg RTree.node (congrArg List.ofFn (funext fun i ↦ ?_))
      have hi : ((⟨(i : ℕ), lt_of_lt_of_le i.isLt (min_le_right _ _)⟩ : Fin N) : ℕ)
          < d [] := lt_of_lt_of_le i.isLt (min_le_left _ _)
      exact ih (sample_bound_ambSub hd _ hi) (by omega)

/-- The tree a finite subtree realises, read at any height bound. -/
lemma bushRTree_eq_rtreeOf {d : GWord N → ℕ} (hfin : ¬ Survives d) {n : ℕ}
    (hn : ∀ u ∈ sample d, u.length ≤ n) : bushRTree d = rtreeOf n d := by
  rw [bushRTree]
  rcases le_total (sampleHeight d) n with h | h
  · exact (rtreeOf_eq_of_bound (sampleHeight d) (sampleHeight_spec hfin) h).symm
  · exact rtreeOf_eq_of_bound n hn h

/-! ### The realised tree is determined by the sample -/

/-- Two fields with the same sample have the same number of children at the root, up to
the alphabet bound. -/
lemma min_root_eq_of_sample_eq {c e : GWord N → ℕ}
    (h : (sample c : Set (GWord N)) = (sample e : Set (GWord N))) :
    min (c []) N = min (e []) N := by
  have hmem : ∀ i : Fin N, ((i : ℕ) < c [] ↔ (i : ℕ) < e []) := by
    intro i
    have h1 : (i :: ([] : GWord N)) ∈ sample c ↔ (i :: ([] : GWord N)) ∈ sample e := by
      constructor <;> intro hx
      · exact (show (i :: ([] : GWord N)) ∈ (sample e : Set (GWord N)) from
          h ▸ (hx : (i :: ([] : GWord N)) ∈ (sample c : Set (GWord N))))
      · exact (show (i :: ([] : GWord N)) ∈ (sample c : Set (GWord N)) from
          h.symm ▸ (hx : (i :: ([] : GWord N)) ∈ (sample e : Set (GWord N))))
    simpa [mem_sample_cons_ambSub, BranchingProcess.nil_mem_sample] using h1
  refine le_antisymm ?_ ?_
  · refine le_min ?_ (min_le_right _ _)
    by_contra hb
    push Not at hb
    have hbN : e [] < N := lt_of_lt_of_le hb (min_le_right _ _)
    have hba : (e [] : ℕ) < c [] := lt_of_lt_of_le hb (min_le_left _ _)
    exact absurd ((hmem ⟨e [], hbN⟩).mp hba) (lt_irrefl _)
  · refine le_min ?_ (min_le_right _ _)
    by_contra hb
    push Not at hb
    have hbN : c [] < N := lt_of_lt_of_le hb (min_le_right _ _)
    have hba : (c [] : ℕ) < e [] := lt_of_lt_of_le hb (min_le_left _ _)
    exact absurd ((hmem ⟨c [], hbN⟩).mpr hba) (lt_irrefl _)

/-- The samples of the child subfields of two fields with the same sample agree. -/
lemma sample_ambSub_eq_of_sample_eq {c e : GWord N → ℕ}
    (h : (sample c : Set (GWord N)) = (sample e : Set (GWord N))) {i : Fin N}
    (hic : (i : ℕ) < c []) (hie : (i : ℕ) < e []) :
    (sample (ambSub c [i]) : Set (GWord N)) = (sample (ambSub e [i]) : Set (GWord N)) := by
  ext u
  constructor <;> intro hu
  · have hmem : i :: u ∈ sample c := mem_sample_cons_ambSub.mpr ⟨hic, hu⟩
    have hmem' : (i :: u) ∈ (sample e : Set (GWord N)) := by
      rw [← h]
      exact hmem
    exact (mem_sample_cons_ambSub.mp hmem').2
  · have hmem : i :: u ∈ sample e := mem_sample_cons_ambSub.mpr ⟨hie, hu⟩
    have hmem' : (i :: u) ∈ (sample c : Set (GWord N)) := by
      rw [h]
      exact hmem
    exact (mem_sample_cons_ambSub.mp hmem').2

/-- **The read tree is determined by the sample**: at every fuel, two fields with the
same sample read the same tree. -/
lemma rtreeOf_eq_of_sample_eq : ∀ (n : ℕ) {c e : GWord N → ℕ},
    (sample c : Set (GWord N)) = (sample e : Set (GWord N)) →
    rtreeOf n c = rtreeOf n e := by
  intro n
  induction n with
  | zero => intro c e _; rfl
  | succ n ih =>
      intro c e h
      have hmin := min_root_eq_of_sample_eq h
      show RTree.node _ = RTree.node _
      refine congrArg RTree.node (List.ext_getElem (by rw [List.length_ofFn,
        List.length_ofFn, hmin]) ?_)
      intro k h1 h2
      rw [List.length_ofFn] at h1 h2
      simp only [List.getElem_ofFn]
      have hkc : k < c [] := lt_of_lt_of_le h1 (min_le_left _ _)
      have hke : k < e [] := lt_of_lt_of_le h2 (min_le_left _ _)
      have hkN : k < N := lt_of_lt_of_le h1 (min_le_right _ _)
      exact ih (sample_ambSub_eq_of_sample_eq h (i := ⟨k, hkN⟩) hkc hke)

/-- **The bush is determined by the sample.** -/
theorem bushRTree_eq_of_sample_eq {c e : GWord N → ℕ}
    (h : (sample c : Set (GWord N)) = (sample e : Set (GWord N))) :
    bushRTree c = bushRTree e := by
  have hsh : sampleHeight c = sampleHeight e := by
    rw [sampleHeight, sampleHeight]
    congr 1
    ext n
    have hmem : ∀ u : GWord N, u ∈ sample c ↔ u ∈ sample e := by
      intro u
      constructor <;> intro hu
      · show u ∈ (sample e : Set (GWord N))
        rw [← h]
        exact hu
      · show u ∈ (sample c : Set (GWord N))
        rw [h]
        exact hu
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun hn u hu ↦ hn u ((hmem u).mpr hu), fun hn u hu ↦ hn u ((hmem u).mp hu)⟩
  rw [bushRTree, bushRTree, hsh, rtreeOf_eq_of_sample_eq _ h]

/-! ### The field cutting out a prescribed rose tree -/

/-- The number of children at the root. -/
def RTree.degR : RTree → ℕ
  | .node cs => cs.length

@[simp] lemma RTree.degR_node (cs : List RTree) : (RTree.node cs).degR = cs.length := rfl

/-- A child is no larger than the whole forest. -/
lemma RTree.size_getElem_le_sizeF : ∀ (cs : List RTree) (k : ℕ) (h : k < cs.length),
    (cs[k]'h).size ≤ RTree.sizeF cs
  | c :: cs, 0, _ => by
      rw [RTree.sizeF]
      have hget : (c :: cs)[0]'(by simp) = c := rfl
      rw [hget]
      omega
  | c :: cs, k + 1, h => by
      rw [RTree.sizeF]
      have hk : k < cs.length := by simpa using h
      have hrec := RTree.size_getElem_le_sizeF cs k hk
      have hget : (c :: cs)[k + 1]'h = cs[k]'hk := rfl
      rw [hget]
      have := RTree.size_pos c
      omega

/-- **The offspring field cutting out a rose tree**: the count at an address of the
tree is its number of children there, and zero off the tree. -/
def fieldOfR : RTree → GWord N → ℕ
  | t, [] => t.degR
  | .node cs, (i :: u) => if h : (i : ℕ) < cs.length then fieldOfR (cs[(i : ℕ)]'h) u else 0

@[simp] lemma fieldOfR_nil (t : RTree) : fieldOfR (N := N) t [] = t.degR := by
  cases t with | node cs => rfl

lemma fieldOfR_cons (cs : List RTree) (i : Fin N) (u : GWord N) :
    fieldOfR (.node cs) (i :: u)
      = if h : (i : ℕ) < cs.length then fieldOfR (cs[(i : ℕ)]'h) u else 0 := rfl

/-- The child subfield of the field of a tree is the field of the child. -/
lemma ambSub_fieldOfR (cs : List RTree) (i : Fin N) (h : (i : ℕ) < cs.length) :
    ambSub (fieldOfR (.node cs)) [i] = fieldOfR (cs[(i : ℕ)]'h) := by
  funext w
  rw [ambSub_apply]
  show fieldOfR (.node cs) (i :: w) = _
  rw [fieldOfR_cons, dite_eq_left h]

/-- Every vertex of the sample of the field of a tree sits strictly inside the size. -/
lemma length_lt_size_of_mem_sample_fieldOfR :
    ∀ (v : GWord N) (t : RTree), v ∈ sample (fieldOfR t) → v.length < t.size := by
  intro v
  induction v with
  | nil =>
      intro t _
      simpa using RTree.size_pos t
  | cons i u ih =>
      rintro ⟨cs⟩ hv
      obtain ⟨hi, hu⟩ := mem_sample_cons_ambSub.mp hv
      rw [fieldOfR_nil, RTree.degR_node] at hi
      rw [ambSub_fieldOfR cs i hi] at hu
      have hlt := ih _ hu
      have hle := RTree.size_getElem_le_sizeF cs (i : ℕ) hi
      rw [RTree.size]
      simp only [List.length_cons]
      omega

/-- The field of a tree cuts out a finite sample. -/
lemma not_survives_fieldOfR (t : RTree) : ¬ Survives (fieldOfR (N := N) t) := by
  rw [BranchingProcess.Survives, Set.not_infinite]
  refine Set.Finite.subset (List.finite_length_le (Fin N) t.size) fun v hv ↦ ?_
  have := length_lt_size_of_mem_sample_fieldOfR v t hv
  exact Set.mem_ofPred_eq ▸ (by omega : v.length ≤ t.size)

/-! ### The sample of the field has at most `|t|` vertices -/

/-- A vertex of the sample of the field of a tree is an address of the tree. -/
lemma isAddr_map_val_of_mem_sample :
    ∀ (v : GWord N) (t : RTree), v ∈ sample (fieldOfR t) →
      RTree.IsAddr t (v.map Fin.val) := by
  intro v
  induction v with
  | nil => intro t _; simp
  | cons i u ih =>
      rintro ⟨cs⟩ hv
      obtain ⟨hi, hu⟩ := mem_sample_cons_ambSub.mp hv
      rw [fieldOfR_nil, RTree.degR_node] at hi
      rw [ambSub_fieldOfR cs i hi] at hu
      rw [List.map_cons, RTree.isAddr_cons]
      exact ⟨hi, ih _ hu⟩

/-- **The sample of the field of a tree has at most `|t|` vertices**: its vertices
inject into the addresses of the tree. -/
lemma ncard_sample_fieldOfR_le (t : RTree) :
    (sample (fieldOfR (N := N) t) : Set (GWord N)).ncard ≤ t.size := by
  classical
  have hfin : (sample (fieldOfR (N := N) t) : Set (GWord N)).Finite :=
    Set.not_infinite.mp (not_survives_fieldOfR t)
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have hmaps : ∀ v ∈ hfin.toFinset, v.map Fin.val ∈ (RTree.addrList t).toFinset := by
    intro v hv
    rw [List.mem_toFinset, RTree.mem_addrList_iff]
    exact isAddr_map_val_of_mem_sample v t (by
      have := (Set.Finite.mem_toFinset hfin).mp hv
      exact this)
  have hinj : Set.InjOn (fun v : GWord N ↦ v.map Fin.val) ↑hfin.toFinset :=
    fun a _ b _ h ↦ List.map_injective_iff.mpr Fin.val_injective h
  calc hfin.toFinset.card
      ≤ (RTree.addrList t).toFinset.card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ (RTree.addrList t).length := (RTree.addrList t).toFinset_card_le
    _ = t.size := RTree.length_addrList t

/-! ### The field realises the tree it is cut from -/

/-- Degrees within the alphabet let the field reproduce the tree, at any fuel past the
size. -/
lemma rtreeOf_fieldOfR (hJN : J ≤ N) : ∀ {t : RTree}, RTree.DegLe J t →
    ∀ {n : ℕ}, t.size ≤ n → rtreeOf n (fieldOfR (N := N) t) = t := by
  intro t
  induction t using RTree.ind with
  | _ cs ih =>
      rintro ⟨hlen, hall⟩ n hn
      have hpos := RTree.size_pos (RTree.node cs)
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hminN : min (fieldOfR (N := N) (RTree.node cs) []) N = cs.length := by
        rw [fieldOfR_nil, RTree.degR_node]
        exact min_eq_left (le_trans hlen hJN)
      show RTree.node _ = RTree.node cs
      refine congrArg RTree.node (List.ext_getElem (by rw [List.length_ofFn, hminN]) ?_)
      intro k h1 h2
      rw [List.length_ofFn] at h1
      simp only [List.getElem_ofFn]
      have hkcs : k < cs.length := by omega
      have hkN : k < N := lt_of_lt_of_le hkcs (le_trans hlen hJN)
      rw [ambSub_fieldOfR cs _ hkcs]
      have hsize : (cs[k]'hkcs).size ≤ n' := by
        have h1 := RTree.size_getElem_le_sizeF cs k hkcs
        have h2 : (RTree.node cs).size = 1 + RTree.sizeF cs := rfl
        omega
      exact ih _ (cs.getElem_mem hkcs) (hall _ (cs.getElem_mem hkcs)) hsize

/-- **The field of a tree realises the tree**: its bush is the tree it was cut from. -/
theorem bushRTree_fieldOfR (hJN : J ≤ N) {t : RTree} (ht : RTree.DegLe J t) :
    bushRTree (fieldOfR (N := N) t) = t := by
  have hbound : ∀ u ∈ sample (fieldOfR (N := N) t), u.length ≤ t.size := by
    intro u hu
    have := length_lt_size_of_mem_sample_fieldOfR u t hu
    omega
  rw [bushRTree_eq_rtreeOf (not_survives_fieldOfR t) hbound]
  exact rtreeOf_fieldOfR hJN ht le_rfl

/-! ### Degrees in the support -/

/-- **A charged rose tree**: every vertex degree carries positive mass. -/
inductive RTree.ChargedT (θ : Offspring J) : RTree → Prop where
  | node : ∀ {cs : List RTree}, 0 < θ cs.length → (∀ c ∈ cs, RTree.ChargedT θ c) →
      RTree.ChargedT θ (.node cs)

/-- A charged tree keeps its degrees within the support bound. -/
lemma RTree.ChargedT.degLe {θ : Offspring J} : ∀ {t : RTree},
    RTree.ChargedT θ t → RTree.DegLe J t := by
  intro t
  induction t using RTree.ind with
  | _ cs ih =>
      rintro ⟨hpos, hall⟩
      refine ⟨?_, fun c hc ↦ ih c hc (hall c hc)⟩
      by_contra hgt
      rw [θ.vanishing cs.length (by omega)] at hpos
      exact lt_irrefl 0 hpos

/-- **The least positive mass of the law**: the minimum of the mass function over its
support, one when the law is degenerate. -/
noncomputable def pminOff (θ : Offspring J) : ℝ :=
  if h : ((Finset.range (J + 1)).filter fun j ↦ 0 < θ j).Nonempty then
    ((Finset.range (J + 1)).filter fun j ↦ 0 < θ j).inf' h θ
  else 1

lemma pminOff_pos (θ : Offspring J) : 0 < pminOff θ := by
  rw [pminOff]
  split
  · rename_i h
    rw [Finset.lt_inf'_iff]
    exact fun j hj ↦ (Finset.mem_filter.mp hj).2
  · norm_num

lemma pminOff_le {θ : Offspring J} {d : ℕ} (hd : 0 < θ d) : pminOff θ ≤ θ d := by
  have hdJ : d ≤ J := by
    by_contra hgt
    rw [θ.vanishing d (by omega)] at hd
    exact lt_irrefl 0 hd
  have hmem : d ∈ (Finset.range (J + 1)).filter fun j ↦ 0 < θ j :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hd⟩
  rw [pminOff, dite_eq_left ⟨d, hmem⟩]
  exact Finset.inf'_le θ hmem

lemma pminOff_le_one (θ : Offspring J) : pminOff θ ≤ 1 := by
  rw [pminOff]
  split
  · rename_i h
    obtain ⟨j, hj⟩ := h
    exact le_trans (Finset.inf'_le θ hj) (θ.mass_le_one j)
  · exact le_rfl

/-! ### The point mass of a bush -/

/-- **The mass of a bush**: the conjugate-law mass of the event that a dying subtree
realises the prescribed rose tree, the factor the masses of `GeneralShapeLaw` carry
per bush. -/
noncomputable def bushMassR (θ : Offspring J) (t : RTree) : ℝ≥0∞ :=
  bushMeasure (N := N) θ {d : GWord N → ℕ | bushRTree d = t}

/-- The constraint sets of a bush list are the bush masses. -/
lemma bushMeasure_listSets {θ : Offspring J} {β : List RTree} {m : ℕ}
    (hm : m < β.length) :
    bushMeasure (N := N) θ (listSets β m) = bushMassR (N := N) θ (β[m]'hm) := by
  rw [listSets, dite_eq_left hm, bushMassR]

/-- **`thm:mass-uniform`, the bush factor**: a charged bush carries at least one factor
of the least positive mass per vertex. -/
theorem ofReal_pow_le_bushMassR (θ : Offspring J) (hJN : J ≤ N) {t : RTree}
    (hch : RTree.ChargedT θ t) :
    ENNReal.ofReal (pminOff θ ^ t.size) ≤ bushMassR (N := N) θ t := by
  classical
  set e : GWord N → ℕ := fieldOfR t with he
  have hfin : (sample e : Set (GWord N)).Finite :=
    Set.not_infinite.mp (not_survives_fieldOfR t)
  -- the sample equality forces the bush
  have hsub : {c : GWord N → ℕ | (sample c : Set (GWord N)) = (sample e : Set (GWord N))}
      ⊆ {c : GWord N → ℕ | bushRTree c = t} := by
    intro c hc
    rw [Set.mem_ofPred_eq, bushRTree_eq_of_sample_eq hc, he, bushRTree_fieldOfR hJN hch.degLe]
  -- one factor per vertex of the sample
  have hmass : ∀ v ∈ sample e, pminOff θ ≤ θ (e v) := by
    have key : ∀ (v : GWord N) (s : RTree), RTree.ChargedT θ s →
        v ∈ sample (fieldOfR (N := N) s) → pminOff θ ≤ θ (fieldOfR s v) := by
      intro v
      induction v with
      | nil =>
          rintro ⟨cs⟩ hch' _
          obtain ⟨hpos, -⟩ := hch'
          rw [fieldOfR_nil, RTree.degR_node]
          exact pminOff_le hpos
      | cons i u ih =>
          rintro ⟨cs⟩ hch' hv
          obtain ⟨hi, hu⟩ := mem_sample_cons_ambSub.mp hv
          rw [fieldOfR_nil, RTree.degR_node] at hi
          rw [ambSub_fieldOfR cs i hi] at hu
          obtain ⟨-, hall⟩ := hch'
          have hval : fieldOfR (N := N) (RTree.node cs) (i :: u)
              = fieldOfR (cs[(i : ℕ)]'hi) u := by
            rw [fieldOfR_cons, dite_eq_left hi]
          rw [hval]
          exact ih _ (hall _ (cs.getElem_mem hi)) hu
    exact fun v hv ↦ key v t hch hv
  have hpoint := BranchingProcess.ofReal_pow_le_bushMeasure_sample_eq θ hfin hmass
  refine le_trans ?_ (le_trans hpoint (measure_mono hsub))
  rw [← ENNReal.ofReal_pow (pminOff_pos θ).le]
  refine ENNReal.ofReal_le_ofReal ?_
  exact pow_le_pow_of_le_one (pminOff_pos θ).le (pminOff_le_one θ)
    (ncard_sample_fieldOfR_le t)

end ChainClasses
