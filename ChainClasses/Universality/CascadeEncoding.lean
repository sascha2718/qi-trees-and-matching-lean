import ChainClasses.General.GeneralAssembly
import ChainClasses.General.GeneralShrink
import ChainClasses.General.GeneralDecomposition
import ChainClasses.General.GeneralShapeTail
import ChainClasses.General.GeneralBushPoint
import ChainClasses.Bushy.AssemblyRelabel
import ChainClasses.Bushy.ShapeDecomposition
import ChainClasses.General.GeneralCascade
import ChainClasses.Universality.BushyCross

/-!
`thm:hairy-general` of `trichotomy.tex`, the deterministic geometry, first part: binary
words and ambient words read over `ℕ`, the cascade encoding `CascadeEnc` abstractly, the
shape family over `𝔹` and the two index sets, the two assemblies, the neck sums over
`𝔹`, and the quasi-isometry of the `𝔹`-assembly with the skeleton assembly.  The
relabelling along automorphisms follows in `AssemblyAut`.
-/

namespace ChainClasses

open BranchingProcess (sample Survives survivors skeletonDegree)

/-! ### Binary words and ambient words read over `ℕ` -/

/-- A binary word read as a word over `ℕ`, `false` as `0` and `true` as `1`. -/
def bnat (x : List Bool) : List ℕ := x.map Bool.toNat

@[simp] lemma bnat_nil : bnat [] = [] := rfl

@[simp] lemma bnat_append (x y : List Bool) : bnat (x ++ y) = bnat x ++ bnat y := by
  simp [bnat]

@[simp] lemma bnat_length (x : List Bool) : (bnat x).length = x.length := by simp [bnat]

@[simp] lemma bnat_take (x : List Bool) (i : ℕ) : (bnat x).take i = bnat (x.take i) := by
  simp [bnat, List.map_take]

lemma bnat_injective : Function.Injective bnat :=
  List.map_injective_iff.mpr (fun a b h ↦ by cases a <;> cases b <;> simp_all)

/-- The reading preserves the prefix order in both directions. -/
lemma bnat_prefix_iff {x y : List Bool} : bnat x <+: bnat y ↔ x <+: y := by
  constructor
  · intro h
    have hlen : x.length ≤ y.length := by simpa using h.length_le
    have heq : bnat x = bnat (y.take x.length) := by
      rw [← bnat_take, List.prefix_iff_eq_take.mp h, bnat_length]
    rw [bnat_injective heq]
    exact List.take_prefix _ _
  · exact fun h ↦ h.map _

/-- A word over `ℕ` read back as a binary word, `1` as `true` and anything else as
`false`. -/
def unbnat (w : List ℕ) : List Bool := w.map fun i ↦ decide (i = 1)

@[simp] lemma unbnat_bnat (x : List Bool) : unbnat (bnat x) = x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      simp only [unbnat, bnat, List.map_cons] at ih ⊢
      rw [ih]
      cases b <;> simp

/-- A word over `ℕ` with letters `0` and `1` only. -/
def IsBin (w : List ℕ) : Prop := ∀ i ∈ w, i ≤ 1

lemma isBin_bnat (x : List Bool) : IsBin (bnat x) := by
  intro i hi
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hi
  cases b <;> simp

lemma IsBin.of_prefix {w w' : List ℕ} (h : IsBin w') (hp : w <+: w') : IsBin w :=
  fun i hi ↦ h i (hp.subset hi)

lemma bnat_unbnat {w : List ℕ} (h : IsBin w) : bnat (unbnat w) = w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      have hi : i ≤ 1 := h i List.mem_cons_self
      have hw : IsBin w := fun j hj ↦ h j (List.mem_cons_of_mem i hj)
      simp only [bnat, unbnat, List.map_cons] at ih ⊢
      rw [ih hw]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl <;> simp

/-- A word over `Fin N` read as a word over `ℕ`. -/
def vals {N : ℕ} (u : BranchingProcess.Word N) : List ℕ := u.map Fin.val

variable {N : ℕ}

@[simp] lemma vals_nil : vals ([] : BranchingProcess.Word N) = [] := rfl

@[simp] lemma vals_append (u v : BranchingProcess.Word N) : vals (u ++ v) = vals u ++ vals v := by
  simp [vals]

@[simp] lemma vals_cons (i : Fin N) (u : BranchingProcess.Word N) :
    vals (i :: u) = (i : ℕ) :: vals u := rfl

@[simp] lemma vals_length (u : BranchingProcess.Word N) : (vals u).length = u.length := by
  simp [vals]

@[simp] lemma vals_take (u : BranchingProcess.Word N) (i : ℕ) :
    (vals u).take i = vals (u.take i) := by
  simp [vals, List.map_take]

lemma vals_injective : Function.Injective (vals (N := N)) :=
  List.map_injective_iff.mpr Fin.val_injective

lemma vals_prefix_iff {u v : BranchingProcess.Word N} : vals u <+: vals v ↔ u <+: v := by
  constructor
  · intro h
    have hlen : u.length ≤ v.length := by simpa using h.length_le
    have heq : vals u = vals (v.take u.length) := by
      rw [← vals_take, List.prefix_iff_eq_take.mp h, vals_length]
    rw [vals_injective heq]
    exact List.take_prefix _ _
  · exact fun h ↦ h.map _

/-- The wedge of two ambient words is read over `ℕ` as the wedge of their readings. -/
lemma wedgeN_vals (u v : BranchingProcess.Word N) :
    wedgeN (vals u) (vals v) = vals (BranchingProcess.wedge u v) := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
      cases v with
      | nil => simp
      | cons b v =>
          rw [vals_cons, vals_cons, wedgeN_cons_cons, BranchingProcess.wedge_cons_cons]
          by_cases hab : a = b
          · subst hab
            simp [ih]
          · rw [ite_eq_right (fun h ↦ hab (Fin.ext h)), ite_eq_right hab]
            rfl

/-- The tree metric of the ambient tree is the address metric of the readings. -/
lemma addrDist_vals (u v : BranchingProcess.Word N) :
    addrDist (vals u) (vals v) = BranchingProcess.treeDist u v := by
  rw [addrDist, BranchingProcess.treeDist, wedgeN_vals, vals_length, vals_length, vals_length]

/-- A word over `ℕ` read back over `Fin N`, the letters outside the alphabet dropped. -/
def unval (N : ℕ) (w : List ℕ) : BranchingProcess.Word N :=
  w.filterMap fun i ↦ if h : i < N then some ⟨i, h⟩ else none

@[simp] lemma unval_vals (u : BranchingProcess.Word N) : unval N (vals u) = u := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      simp only [vals_cons, unval, List.filterMap_cons, dite_eq_left a.isLt, Fin.eta]
      rw [unval] at ih
      rw [ih]

/-! ### The cascade encoding, abstractly -/

/-- **The cascade encoding of a reduced skeleton into `𝔹`, abstractly.**  A skeleton
address `u` over `Fin N` is encoded by a binary word `enc u`, the child `u ++ [i]` by the
slot word `slot u i` appended to it.  The arity field `k` cuts the skeleton out of the
`N`-ary tree as `sample k`, and the slots of one vertex are nonempty, of length at most
`L`, and pairwise prefix-incomparable, so the encoding is injective and reflects the
prefix order on the skeleton.  `EngineBridge` instantiates this with the engine's
cascades. -/
structure CascadeEnc (N L : ℕ) where
  /-- The arity field: `u ++ [i]` is a skeleton address iff `u` is and `i < k u`. -/
  k : GWord N → ℕ
  /-- The encoding of the skeleton addresses. -/
  enc : GWord N → List Bool
  /-- The slot word of the `i`-th child of `u`. -/
  slot : GWord N → ℕ → List Bool
  enc_nil : enc [] = []
  enc_concat : ∀ (u : GWord N) (i : Fin N), enc (u ++ [i]) = enc u ++ slot u (i : ℕ)
  slot_ne_nil : ∀ (u : GWord N) (i : ℕ), i < k u → slot u i ≠ []
  slot_length_le : ∀ (u : GWord N) (i : ℕ), i < k u → (slot u i).length ≤ L
  slot_prefix : ∀ (u : GWord N) (i j : ℕ), i < k u → j < k u → slot u i <+: slot u j → i = j

namespace CascadeEnc

variable {L : ℕ} (E : CascadeEnc N L)

/-- The reduced skeleton cut out by the arity field. -/
abbrev Skel (u : GWord N) : Prop := u ∈ sample E.k

lemma skel_nil : E.Skel [] := BranchingProcess.nil_mem_sample _

lemma skel_of_prefix {u v : GWord N} (hv : E.Skel v) (h : u <+: v) : E.Skel u :=
  BranchingProcess.Subtree.mem_of_prefix h hv

lemma skel_concat_iff {u : GWord N} {i : Fin N} :
    E.Skel (u ++ [i]) ↔ E.Skel u ∧ (i : ℕ) < E.k u :=
  BranchingProcess.mem_sample_append_singleton

/-- The encoding only appends along the skeleton: it is monotone for the prefix order. -/
lemma enc_prefix {u v : GWord N} (h : u <+: v) : E.enc u <+: E.enc v := by
  obtain ⟨s, rfl⟩ := h
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s j ih =>
      rw [← List.append_assoc, E.enc_concat]
      exact ih.trans (List.prefix_append _ _)

/-- The slot of a skeleton child is nonempty, so the encoding grows strictly. -/
lemma enc_length_lt {u v : GWord N} (hv : E.Skel v) (h : u <+: v) (hne : u ≠ v) :
    (E.enc u).length < (E.enc v).length := by
  obtain ⟨s, rfl⟩ := h
  cases s with
  | nil => exact absurd (by simp) hne
  | cons j s =>
      have hmem : E.Skel (u ++ [j]) := E.skel_of_prefix hv ⟨s, by simp⟩
      have hj : (j : ℕ) < E.k u := (E.skel_concat_iff.mp hmem).2
      have h1 : E.enc (u ++ [j]) <+: E.enc (u ++ j :: s) := E.enc_prefix ⟨s, by simp⟩
      have h2 := h1.length_le
      rw [E.enc_concat, List.length_append] at h2
      have h3 : 0 < (E.slot u j).length := List.length_pos_iff.mpr (E.slot_ne_nil u j hj)
      omega

/-- **The encoding reflects the prefix order on the skeleton**: the slots of a vertex
being prefix-incomparable, an encoded address extending an encoded address extends it
through the slot of the right child. -/
lemma prefix_of_enc_prefix : ∀ {s t : GWord N}, E.Skel s → E.Skel t →
    E.enc s <+: E.enc t → s <+: t := by
  intro s
  induction s using List.reverseRecOn with
  | nil => intro t _ _ _; exact List.nil_prefix
  | append_singleton s i ih =>
      intro t hs ht h
      obtain ⟨hs', hi⟩ := E.skel_concat_iff.mp hs
      rw [E.enc_concat] at h
      have hst : s <+: t := ih hs' ht ((List.prefix_append _ _).trans h)
      obtain ⟨r, rfl⟩ := hst
      cases r with
      | nil =>
          exfalso
          have h2 := h.length_le
          rw [List.append_nil, List.length_append] at h2
          have h3 : 0 < (E.slot s i).length := List.length_pos_iff.mpr (E.slot_ne_nil s i hi)
          omega
      | cons i' r' =>
          have hi'mem : E.Skel (s ++ [i']) := E.skel_of_prefix ht ⟨r', by simp⟩
          have hi' : (i' : ℕ) < E.k s := (E.skel_concat_iff.mp hi'mem).2
          have h2 : E.enc s ++ E.slot s i' <+: E.enc (s ++ i' :: r') := by
            rw [← E.enc_concat]
            exact E.enc_prefix ⟨r', by simp⟩
          have hii' : (i : ℕ) = i' := by
            rcases List.prefix_or_prefix_of_prefix h h2 with h3 | h3
            · exact E.slot_prefix s i i' hi hi' ((List.prefix_append_right_inj _).mp h3)
            · exact (E.slot_prefix s i' i hi' hi ((List.prefix_append_right_inj _).mp h3)).symm
          rw [Fin.ext hii']
          exact ⟨r', by simp⟩

/-- The encoding is injective on the skeleton. -/
lemma enc_injOn {s t : GWord N} (hs : E.Skel s) (ht : E.Skel t) (h : E.enc s = E.enc t) :
    s = t :=
  (E.prefix_of_enc_prefix hs ht (h ▸ List.prefix_refl _)).eq_of_length
    (le_antisymm (E.prefix_of_enc_prefix hs ht (h ▸ List.prefix_refl _)).length_le
      (E.prefix_of_enc_prefix ht hs (h ▸ List.prefix_refl _)).length_le)

/-- Along a chain of the skeleton the encoding lengths compare as the lengths. -/
lemma enc_length_lt_iff {v s t : GWord N} (hv : E.Skel v) (hs : s <+: v) (ht : t <+: v) :
    (E.enc s).length < (E.enc t).length ↔ s.length < t.length := by
  have hsk : E.Skel s := E.skel_of_prefix hv hs
  have htk : E.Skel t := E.skel_of_prefix hv ht
  rcases List.prefix_or_prefix_of_prefix hs ht with h | h
  · by_cases hne : s = t
    · subst hne
      simp
    · exact iff_of_true (E.enc_length_lt htk h hne)
        (BranchingProcess.length_lt_of_prefix_ne h hne)
  · have h1 : (E.enc t).length ≤ (E.enc s).length := (E.enc_prefix h).length_le
    have h2 : t.length ≤ s.length := h.length_le
    exact iff_of_false (by omega) (by omega)

/-- **The encoding stretches a chain by a factor between one and `L`.** -/
lemma enc_length_bounds {u v : GWord N} (hv : E.Skel v) (h : u <+: v) :
    (E.enc u).length + (v.length - u.length) ≤ (E.enc v).length
      ∧ (E.enc v).length ≤ (E.enc u).length + L * (v.length - u.length) := by
  obtain ⟨s, rfl⟩ := h
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s j ih =>
      have hmem : E.Skel (u ++ s ++ [j]) := by rwa [List.append_assoc]
      have hj : (j : ℕ) < E.k (u ++ s) := (E.skel_concat_iff.mp hmem).2
      obtain ⟨ih1, ih2⟩ := ih (E.skel_of_prefix hmem (List.prefix_append _ _))
      rw [← List.append_assoc, E.enc_concat]
      have h1 : 0 < (E.slot (u ++ s) j).length :=
        List.length_pos_iff.mpr (E.slot_ne_nil _ _ hj)
      have h2 := E.slot_length_le _ _ hj
      have h3 : (u ++ s).length - u.length = s.length := by simp
      have h4 : (u ++ s ++ [j]).length - u.length = s.length + 1 := by simp
      have h5 : L * (s.length + 1) = L * s.length + L := by ring
      rw [h3] at ih1 ih2
      rw [h4, List.length_append, h5]
      omega

/-! ### The shape family over `𝔹` and the two index sets -/

/-- The copy words of the `𝔹`-assembly that carry a shape: the encoded skeleton
addresses, read over `ℕ`. -/
def IsImage (w : List ℕ) : Prop := ∃ u, E.Skel u ∧ w = bnat (E.enc u)

/-- **The index set of the `𝔹`-assembly**: the prefix closure of the encoded skeleton,
the encoded addresses together with the internal vertices of their cascades. -/
def InClosure (w : List ℕ) : Prop := ∃ u, E.Skel u ∧ w <+: bnat (E.enc u)

lemma InClosure.of_prefix {w w' : List ℕ} (h : E.InClosure w') (hp : w <+: w') :
    E.InClosure w := by
  obtain ⟨u, hu, hw⟩ := h
  exact ⟨u, hu, hp.trans hw⟩

lemma inClosure_enc {u : GWord N} (hu : E.Skel u) : E.InClosure (bnat (E.enc u)) :=
  ⟨u, hu, List.prefix_refl _⟩

lemma InClosure.isBin {w : List ℕ} (h : E.InClosure w) : IsBin w := by
  obtain ⟨u, -, hw⟩ := h
  exact (isBin_bnat _).of_prefix hw

/-- A word strictly between an encoded address and the encoding of one of its skeleton
children is an internal vertex of the cascade: it encodes no skeleton address. -/
lemma not_isImage_of_between {t : GWord N} (ht : E.Skel t) {j : Fin N} (hj : (j : ℕ) < E.k t)
    {w : List ℕ} (h1 : bnat (E.enc t) <+: w) (h2 : w <+: bnat (E.enc (t ++ [j])))
    (hne1 : w ≠ bnat (E.enc t)) (hne2 : w ≠ bnat (E.enc (t ++ [j]))) : ¬ E.IsImage w := by
  rintro ⟨t', ht', rfl⟩
  have htj : E.Skel (t ++ [j]) := E.skel_concat_iff.mpr ⟨ht, hj⟩
  have h1' : t <+: t' := E.prefix_of_enc_prefix ht ht' (bnat_prefix_iff.mp h1)
  have h2' : t' <+: t ++ [j] := E.prefix_of_enc_prefix ht' htj (bnat_prefix_iff.mp h2)
  rcases List.prefix_concat_iff.mp h2' with h | h
  · exact hne2 (by rw [h])
  · exact hne1 (by rw [h1'.eq_of_length (le_antisymm h1'.length_le h.length_le)])

open Classical in
/-- **The shape family over `𝔹`** (**`thm:hairy-general`**): the shape of a skeleton
address at its encoding, the one-vertex shape everywhere else, in particular at the
internal vertices of the cascades, the forced slots of the engine. -/
noncomputable def bFamily (σ : GWord N → GShape) (w : List ℕ) : GShape :=
  if h : ∃ u, E.Skel u ∧ w = bnat (E.enc u) then σ h.choose else gOne

variable {E}

lemma bFamily_enc {σ : GWord N → GShape} {u : GWord N} (hu : E.Skel u) :
    E.bFamily σ (bnat (E.enc u)) = σ u := by
  have h : ∃ u', E.Skel u' ∧ bnat (E.enc u) = bnat (E.enc u') := ⟨u, hu, rfl⟩
  rw [bFamily, dite_eq_left h]
  have hspec := h.choose_spec
  have : h.choose = u := E.enc_injOn hspec.1 hu (bnat_injective hspec.2).symm
  rw [this]

lemma bFamily_of_not_isImage {σ : GWord N → GShape} {w : List ℕ} (h : ¬ E.IsImage w) :
    E.bFamily σ w = gOne := by
  have h' : ¬ ∃ u, E.Skel u ∧ w = bnat (E.enc u) := h
  rw [bFamily, dite_eq_right h']

lemma bFamily_of_not_isBin {σ : GWord N → GShape} {w : List ℕ} (h : ¬ IsBin w) :
    E.bFamily σ w = gOne :=
  bFamily_of_not_isImage fun ⟨_, _, hw⟩ ↦ h (hw ▸ isBin_bnat _)

/-- A copy word carrying a shape other than the one-vertex shape encodes a skeleton
address. -/
lemma isImage_of_bFamily_ne {σ : GWord N → GShape} {w : List ℕ}
    (h : E.bFamily σ w ≠ gOne) : E.IsImage w := by
  by_contra hc
  exact h (bFamily_of_not_isImage hc)

end CascadeEnc

/-! ### The two assemblies -/

/-- The shape family of a skeleton read over `ℕ`. -/
def liftN (N : ℕ) (σ : GWord N → GShape) (w : List ℕ) : GShape := σ (unval N w)

@[simp] lemma liftN_vals (σ : GWord N → GShape) (u : GWord N) : liftN N σ (vals u) = σ u := by
  rw [liftN, unval_vals]

/-- **The `𝔹`-assembly** (**`thm:hairy-general`**): the assembly of the shape family
over `𝔹`, over the prefix closure of the encoded skeleton. -/
@[implicit_reducible]
def BAssembly {L : ℕ} (E : CascadeEnc N L) (σ : GWord N → GShape) : Type :=
  {x : GAssembly (E.bFamily σ) // E.InClosure x.copy}

noncomputable instance {L : ℕ} (E : CascadeEnc N L) (σ : GWord N → GShape) :
    MetricSpace (BAssembly E σ) :=
  Subtype.metricSpace

lemma BAssembly.dist_val {L : ℕ} {E : CascadeEnc N L} {σ : GWord N → GShape}
    (x y : BAssembly E σ) : dist x y = dist x.1 y.1 := rfl

/-- A vertex of a realisation transported along an equality of shapes. -/
def castVert {τ τ' : GShape} (h : τ = τ') (p : (gShapeSpace τ).carrier) :
    (gShapeSpace τ').carrier :=
  ⟨p.1, h ▸ p.2⟩

@[simp] lemma castVert_val {τ τ' : GShape} (h : τ = τ') (p : (gShapeSpace τ).carrier) :
    (castVert h p).1 = p.1 := rfl

@[simp] lemma castVert_rfl {τ : GShape} (p : (gShapeSpace τ).carrier) : castVert rfl p = p := rfl

lemma dist_castVert {τ τ' : GShape} (h : τ = τ') (p q : (gShapeSpace τ).carrier) :
    dist (castVert h p) (castVert h q) = dist p q := by
  subst h; rfl

lemma dist_castVert_exit {τ τ' : GShape} (h : τ = τ') (p : (gShapeSpace τ).carrier) :
    dist (castVert h p) (gShapeSpace τ').exit = dist p (gShapeSpace τ).exit := by
  subst h; rfl

lemma dist_castVert_entry {τ τ' : GShape} (h : τ = τ') (p : (gShapeSpace τ).carrier) :
    dist (castVert h p) (gShapeSpace τ').entry = dist p (gShapeSpace τ).entry := by
  subst h; rfl

/-- The one-vertex shape has the root as its only address. -/
lemma eq_nil_of_gOne {τ : GShape} (h : τ = gOne) (p : (gShapeSpace τ).carrier) : p.1 = [] := by
  subst h
  obtain ⟨w, hw⟩ := p
  have hw' : w ∈ RTree.addrList (RTree.node []) := hw
  rw [RTree.addrList_node, RTree.addrListF_nil, List.mem_singleton] at hw'
  exact hw'

/-- **The assembly of a shape family over its reduced skeleton**: a vertex is an address
inside the realisation of the shape at a skeleton address `u`, tagged by `u`. -/
structure SkelAssembly (k : GWord N → ℕ) (σ : GWord N → GShape) where
  /-- The skeleton address naming the copy. -/
  copy : GWord N
  /-- The copy is a skeleton address. -/
  skel : copy ∈ sample k
  /-- The address inside the realisation of the shape at that copy. -/
  vert : (gShapeSpace (σ copy)).carrier

namespace SkelAssembly

variable {k : GWord N → ℕ} {σ : GWord N → GShape}

/-- The skeleton assembly inside the assembly over all words of `ℕ`. -/
def toG (x : SkelAssembly k σ) : GAssembly (liftN N σ) :=
  ⟨vals x.copy, castVert (liftN_vals σ x.copy).symm x.vert⟩

@[simp] lemma toG_copy (x : SkelAssembly k σ) : (toG x).copy = vals x.copy := rfl

@[simp] lemma toG_vert_val (x : SkelAssembly k σ) : (toG x).vert.1 = x.vert.1 := rfl

lemma ext : ∀ {x y : SkelAssembly k σ}, x.copy = y.copy → x.vert.1 = y.vert.1 → x = y := by
  rintro ⟨u, hu, p, hp⟩ ⟨v, hv, q, hq⟩ h1 h2
  simp only at h1 h2
  subst h1
  subst h2
  rfl

lemma toG_injective : Function.Injective (toG (k := k) (σ := σ)) := by
  intro x y h
  have h1 : vals x.copy = vals y.copy := congrArg GAssembly.copy h
  have h2 : x.vert.1 = y.vert.1 := by
    have := congrArg (fun z : GAssembly (liftN N σ) ↦ z.vert.1) h
    simpa using this
  exact ext (vals_injective h1) h2

/-- The metric of the skeleton assembly, restricted from the assembly over all words. -/
noncomputable instance instMetricSpace : MetricSpace (SkelAssembly k σ) :=
  MetricSpace.induced toG toG_injective inferInstance

lemma dist_toG (x y : SkelAssembly k σ) : dist x y = dist (toG x) (toG y) := rfl

/-- The sums of `eq:assembly-anc` and `eq:assembly-div` read over the skeleton. -/
lemma neckSum_vals (a b : ℕ) (v : GWord N) :
    ∑ i ∈ Finset.Ico a b, ((liftN N σ ((vals v).take i)).neckLen : ℝ)
      = ∑ i ∈ Finset.Ico a b, ((σ (v.take i)).neckLen : ℝ) := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [vals_take, liftN_vals]

lemma neckSum_vals_nat (a b : ℕ) (v : GWord N) :
    ∑ i ∈ Finset.Ico a b, (liftN N σ ((vals v).take i)).neckLen
      = ∑ i ∈ Finset.Ico a b, (σ (v.take i)).neckLen := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [vals_take, liftN_vals]

/-- Inside one copy the distance is the distance of the addresses. -/
theorem dist_same {u : GWord N} (hu : u ∈ sample k) (p q : (gShapeSpace (σ u)).carrier) :
    dist (⟨u, hu, p⟩ : SkelAssembly k σ) ⟨u, hu, q⟩ = dist p q := by
  rw [dist_toG]
  exact (GAssembly.dist_same (liftN N σ) (vals u) _ _).trans (dist_castVert _ p q)

/-- **`eq:assembly-anc`** over the skeleton. -/
theorem dist_anc {u v : GWord N} (hu : u ∈ sample k) (hv : v ∈ sample k) (huv : u <+: v)
    (hne : u ≠ v) (p : (gShapeSpace (σ u)).carrier) (q : (gShapeSpace (σ v)).carrier) :
    dist (⟨u, hu, p⟩ : SkelAssembly k σ) ⟨v, hv, q⟩
      = dist p (gShapeSpace (σ u)).exit + dist q (gShapeSpace (σ v)).entry + 1
        + ∑ i ∈ Finset.Ico (u.length + 1) v.length, ((σ (v.take i)).neckLen : ℝ) := by
  rw [dist_toG]
  have hne' : vals u ≠ vals v := fun h ↦ hne (vals_injective h)
  rw [toG, toG, GAssembly.dist_anc (liftN N σ) (vals_prefix_iff.mpr huv) hne',
    dist_castVert_exit, dist_castVert_entry, vals_length, vals_length, neckSum_vals]

/-- **`eq:assembly-div`** over the skeleton. -/
theorem dist_div {u v : GWord N} (hu : u ∈ sample k) (hv : v ∈ sample k) (huv : ¬ u <+: v)
    (hvu : ¬ v <+: u) (p : (gShapeSpace (σ u)).carrier) (q : (gShapeSpace (σ v)).carrier) :
    dist (⟨u, hu, p⟩ : SkelAssembly k σ) ⟨v, hv, q⟩
      = dist p (gShapeSpace (σ u)).entry + dist q (gShapeSpace (σ v)).entry + 2
        + (∑ i ∈ Finset.Ico ((BranchingProcess.wedge u v).length + 1) u.length,
              ((σ (u.take i)).neckLen : ℝ)
          + ∑ i ∈ Finset.Ico ((BranchingProcess.wedge u v).length + 1) v.length,
              ((σ (v.take i)).neckLen : ℝ)) := by
  rw [dist_toG]
  have huv' : ¬ vals u <+: vals v := fun h ↦ huv (vals_prefix_iff.mp h)
  have hvu' : ¬ vals v <+: vals u := fun h ↦ hvu (vals_prefix_iff.mp h)
  rw [toG, toG, GAssembly.dist_div (liftN N σ) huv' hvu', dist_castVert_entry,
    dist_castVert_entry, vals_length, vals_length, wedgeN_vals, vals_length, neckSum_vals,
    neckSum_vals]

end SkelAssembly

/-! ### The neck sums over `𝔹` -/

namespace CascadeEnc

variable {L : ℕ} {E : CascadeEnc N L} {σ : GWord N → GShape}

/-- **The neck counts along a cascade path**: between two cut-offs, the neck counts of
the shapes at the prefixes of an encoded address are those of the skeleton shapes
between the corresponding cut-offs, the internal cascade vertices contributing nothing,
the one-vertex shape having no neck edge. -/
lemma bNecks_sum_eq {v : GWord N} (hv : E.Skel v) {a b a' b' : ℕ}
    (hb : b ≤ (E.enc v).length) (hb' : b' ≤ v.length + 1)
    (hcond : ∀ t, t <+: v →
      ((a ≤ (E.enc t).length ∧ (E.enc t).length < b) ↔ (a' ≤ t.length ∧ t.length < b'))) :
    ∑ i ∈ Finset.Ico a b, (E.bFamily σ ((bnat (E.enc v)).take i)).necks
      = ∑ j ∈ Finset.Ico a' b', (σ (v.take j)).necks := by
  symm
  refine Finset.sum_bij_ne_zero (fun j _ _ ↦ (E.enc (v.take j)).length) ?_ ?_ ?_ ?_
  · intro j hj _
    rw [Finset.mem_Ico] at hj
    have hjl : j ≤ v.length := by omega
    have hlen : (v.take j).length = j := by rw [List.length_take, min_eq_left hjl]
    exact Finset.mem_Ico.mpr
      ((hcond (v.take j) (List.take_prefix _ _)).mpr (by rw [hlen]; exact hj))
  · intro j₁ hj₁ _ j₂ hj₂ _ h
    rw [Finset.mem_Ico] at hj₁ hj₂
    have h1 : (v.take j₁).length = j₁ := by rw [List.length_take, min_eq_left (by omega)]
    have h2 : (v.take j₂).length = j₂ := by rw [List.length_take, min_eq_left (by omega)]
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := (E.enc_length_lt_iff hv (List.take_prefix j₁ v) (List.take_prefix j₂ v)).mpr
        (by rw [h1, h2]; exact hlt)
      omega
    · have := (E.enc_length_lt_iff hv (List.take_prefix j₂ v) (List.take_prefix j₁ v)).mpr
        (by rw [h1, h2]; exact hlt)
      omega
  · intro i hi hne
    rw [Finset.mem_Ico] at hi
    have himg : E.IsImage ((bnat (E.enc v)).take i) :=
      isImage_of_bFamily_ne fun h ↦ hne (by rw [h]; rfl)
    obtain ⟨t, ht, hteq⟩ := himg
    rw [bnat_take] at hteq
    have hteq' : (E.enc v).take i = E.enc t := bnat_injective hteq
    have htv : t <+: v := E.prefix_of_enc_prefix ht hv (hteq' ▸ List.take_prefix _ _)
    have hlen : (E.enc t).length = i := by
      rw [← hteq', List.length_take, min_eq_left (by omega)]
    have hcond' := (hcond t htv).mp ⟨by omega, by omega⟩
    have htake : v.take t.length = t := (List.prefix_iff_eq_take.mp htv).symm
    refine ⟨t.length, Finset.mem_Ico.mpr hcond', ?_, ?_⟩
    · rw [htake]
      intro h0
      apply hne
      rw [bnat_take, hteq, bFamily_enc ht]
      exact h0
    · rw [htake, hlen]
  · intro j hj _
    rw [Finset.mem_Ico] at hj
    have hpre : E.enc (v.take j) <+: E.enc v := E.enc_prefix (List.take_prefix _ _)
    rw [bnat_take, ← List.prefix_iff_eq_take.mp hpre,
      bFamily_enc (E.skel_of_prefix hv (List.take_prefix _ _))]

/-- The neck lengths along a cascade path: the neck counts plus one per term. -/
lemma bNeckLen_sum_eq {v : GWord N} (hv : E.Skel v) {a b a' b' : ℕ}
    (hb : b ≤ (E.enc v).length) (hb' : b' ≤ v.length + 1)
    (hcond : ∀ t, t <+: v →
      ((a ≤ (E.enc t).length ∧ (E.enc t).length < b) ↔ (a' ≤ t.length ∧ t.length < b'))) :
    ∑ i ∈ Finset.Ico a b, (E.bFamily σ ((bnat (E.enc v)).take i)).neckLen + (b' - a')
      = ∑ j ∈ Finset.Ico a' b', (σ (v.take j)).neckLen + (b - a) := by
  have h := bNecks_sum_eq (σ := σ) hv hb hb' hcond
  simp only [GShape.neckLen, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
    smul_eq_mul, mul_one]
  omega

/-- Every neck sum dominates the number of its terms. -/
lemma card_le_neckSum (τ : List ℕ → GShape) (a b : ℕ) (w : List ℕ) :
    b - a ≤ ∑ i ∈ Finset.Ico a b, (τ (w.take i)).neckLen := by
  have h := Finset.card_nsmul_le_sum (Finset.Ico a b) (fun i ↦ (τ (w.take i)).neckLen) 1
    (fun i _ ↦ Nat.succ_pos _)
  rwa [Nat.card_Ico, smul_eq_mul, mul_one] at h

/-- **The neck sum of `eq:assembly-anc` over `𝔹`**: the skeleton neck sum plus the
number of internal cascade vertices crossed. -/
lemma bNeckSum_anc {u v : GWord N} (hv : E.Skel v) (huv : u <+: v) (hne : u ≠ v) :
    ∑ i ∈ Finset.Ico ((E.enc u).length + 1) (E.enc v).length,
          (E.bFamily σ ((bnat (E.enc v)).take i)).neckLen + (v.length - u.length)
      = ∑ j ∈ Finset.Ico (u.length + 1) v.length, (σ (v.take j)).neckLen
          + ((E.enc v).length - (E.enc u).length) := by
  have hlt : u.length < v.length := BranchingProcess.length_lt_of_prefix_ne huv hne
  have helt : (E.enc u).length < (E.enc v).length := E.enc_length_lt hv huv hne
  have h := bNeckLen_sum_eq (σ := σ) hv (a := (E.enc u).length + 1) (b := (E.enc v).length)
    (a' := u.length + 1) (b' := v.length) le_rfl (by omega) (fun t ht ↦ by
      have h1 := E.enc_length_lt_iff hv huv ht
      have h2 := E.enc_length_lt_iff hv ht (List.prefix_refl _)
      omega)
  omega

/-- The three relative positions of two skeleton addresses. -/
lemma copy_trichotomyW (u v : GWord N) :
    u = v ∨ (u <+: v ∧ u ≠ v) ∨ (v <+: u ∧ v ≠ u) ∨ (¬ u <+: v ∧ ¬ v <+: u) := by
  by_cases h1 : u <+: v
  · by_cases h2 : v <+: u
    · exact Or.inl (h1.eq_of_length (le_antisymm h1.length_le h2.length_le))
    · exact Or.inr (Or.inl ⟨h1, fun h ↦ h2 (h ▸ List.prefix_refl _)⟩)
  · by_cases h2 : v <+: u
    · exact Or.inr (Or.inr (Or.inl ⟨h2, fun h ↦ h1 (h ▸ List.prefix_refl _)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))

/-- First divergence of two prefix-incomparable skeleton addresses. -/
lemma exists_divergeW {u v : GWord N} (h1 : ¬ u <+: v) (h2 : ¬ v <+: u) :
    ∃ (z : GWord N) (a b : Fin N), a ≠ b ∧ z ++ [a] <+: u ∧ z ++ [b] <+: v := by
  induction u generalizing v with
  | nil => exact absurd List.nil_prefix h1
  | cons x t ih =>
      cases v with
      | nil => exact absurd List.nil_prefix h2
      | cons x' t' =>
          by_cases hx : x = x'
          · subst hx
            have h1' : ¬ t <+: t' := fun hp ↦ h1 (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
            have h2' : ¬ t' <+: t := fun hp ↦ h2 (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
            obtain ⟨z, a, b, hab, hza, hzb⟩ := ih h1' h2'
            exact ⟨x :: z, a, b, hab, List.cons_prefix_cons.mpr ⟨rfl, hza⟩,
              List.cons_prefix_cons.mpr ⟨rfl, hzb⟩⟩
          · exact ⟨[], x, x', hx, ⟨t, rfl⟩, ⟨t', rfl⟩⟩

/-- The wedge of two words leaving a common prefix by distinct letters. -/
lemma wedge_of_divergeW {z u v : GWord N} {a b : Fin N} (hab : a ≠ b) (hza : z ++ [a] <+: u)
    (hzb : z ++ [b] <+: v) : BranchingProcess.wedge u v = z := by
  obtain ⟨r, rfl⟩ := hza
  obtain ⟨r', rfl⟩ := hzb
  rw [List.append_assoc, List.append_assoc, List.singleton_append, List.singleton_append]
  exact wedgeN_diverge hab

/-- **The wedge of two encoded addresses** sits inside the cascade of the wedge of the
addresses: it extends the encoding of the wedge and stops short of the encoding of
either child. -/
lemma wedge_enc_bounds {z u v : GWord N} (hu : E.Skel u) (hv : E.Skel v) {a b : Fin N}
    (hab : a ≠ b) (hza : z ++ [a] <+: u) (hzb : z ++ [b] <+: v) :
    (E.enc z).length ≤ (wedgeN (bnat (E.enc u)) (bnat (E.enc v))).length
      ∧ (wedgeN (bnat (E.enc u)) (bnat (E.enc v))).length < (E.enc (z ++ [a])).length := by
  have hz : z <+: u := (List.prefix_append _ _).trans hza
  have hpre : bnat (E.enc z) <+: wedgeN (bnat (E.enc u)) (bnat (E.enc v)) :=
    prefix_wedgeN (bnat_prefix_iff.mpr (E.enc_prefix hz))
      (bnat_prefix_iff.mpr (E.enc_prefix ((List.prefix_append _ _).trans hzb)))
  refine ⟨by simpa using hpre.length_le, ?_⟩
  by_contra hc
  rw [Nat.not_lt] at hc
  have hza' : bnat (E.enc (z ++ [a])) <+: bnat (E.enc u) := bnat_prefix_iff.mpr (E.enc_prefix hza)
  have hzb' : bnat (E.enc (z ++ [b])) <+: bnat (E.enc v) := bnat_prefix_iff.mpr (E.enc_prefix hzb)
  have h1 : bnat (E.enc (z ++ [a])) <+: wedgeN (bnat (E.enc u)) (bnat (E.enc v)) :=
    List.prefix_of_prefix_length_le hza' (wedgeN_prefix_left _ _) (by simpa using hc)
  have h2 : bnat (E.enc (z ++ [a])) <+: bnat (E.enc v) := h1.trans (wedgeN_prefix_right _ _)
  have hzk : E.Skel z := E.skel_of_prefix hu hz
  have ha : (a : ℕ) < E.k z := (E.skel_concat_iff.mp (E.skel_of_prefix hu hza)).2
  have hb : (b : ℕ) < E.k z := (E.skel_concat_iff.mp (E.skel_of_prefix hv hzb)).2
  rw [bnat_prefix_iff, E.enc_concat] at h2 hzb'
  have hab' : (a : ℕ) = b := by
    rcases List.prefix_or_prefix_of_prefix h2 hzb' with h | h
    · exact E.slot_prefix z a b ha hb ((List.prefix_append_right_inj _).mp h)
    · exact (E.slot_prefix z b a hb ha ((List.prefix_append_right_inj _).mp h)).symm
  exact hab (Fin.ext hab')

/-- **The neck sum of `eq:assembly-div` over `𝔹`, one branch**: from the wedge of the
encoded addresses down to the encoded address of `u`, the skeleton neck sum from the
wedge `z` plus the number of internal cascade vertices crossed. -/
lemma bNeckSum_div {z u v : GWord N} (hu : E.Skel u) (hv : E.Skel v) {a b : Fin N}
    (hab : a ≠ b) (hza : z ++ [a] <+: u) (hzb : z ++ [b] <+: v) :
    ∑ i ∈ Finset.Ico ((wedgeN (bnat (E.enc u)) (bnat (E.enc v))).length + 1) (E.enc u).length,
          (E.bFamily σ ((bnat (E.enc u)).take i)).neckLen + (u.length - z.length)
      = ∑ j ∈ Finset.Ico (z.length + 1) u.length, (σ (u.take j)).neckLen
          + ((E.enc u).length - (wedgeN (bnat (E.enc u)) (bnat (E.enc v))).length) := by
  obtain ⟨hw1, hw2⟩ := wedge_enc_bounds hu hv hab hza hzb
  have hz : z <+: u := (List.prefix_append _ _).trans hza
  have hzlt : z.length < u.length := by
    have := hza.length_le
    simp only [List.length_append, List.length_singleton] at this
    omega
  have hzalen : (E.enc (z ++ [a])).length ≤ (E.enc u).length := (E.enc_prefix hza).length_le
  have h := bNeckLen_sum_eq (σ := σ) hu
    (a := (wedgeN (bnat (E.enc u)) (bnat (E.enc v))).length + 1) (b := (E.enc u).length)
    (a' := z.length + 1) (b' := u.length) le_rfl (by omega) (fun t ht ↦ by
      have h2 := E.enc_length_lt_iff hu ht (List.prefix_refl _)
      constructor
      · rintro ⟨h3, h4⟩
        refine ⟨?_, h2.mp h4⟩
        by_contra hc
        rw [Nat.not_le] at hc
        have htz : t <+: z := List.prefix_of_prefix_length_le ht hz (by omega)
        have := (E.enc_prefix htz).length_le
        omega
      · rintro ⟨h3, h4⟩
        refine ⟨?_, h2.mpr h4⟩
        have hzat : z ++ [a] <+: t := List.prefix_of_prefix_length_le hza ht (by simp; omega)
        have := (E.enc_prefix hzat).length_le
        omega)
  omega

/-! ### The `𝔹`-assembly is quasi-isometric to the skeleton assembly -/

variable (E σ)

/-- **The `𝔹`-assembly read from the skeleton assembly**: the copy at a skeleton address
goes to the copy at its encoding, carrying the same shape. -/
noncomputable def skelToB (x : SkelAssembly E.k σ) : BAssembly E σ :=
  ⟨⟨bnat (E.enc x.copy), castVert (bFamily_enc x.skel).symm x.vert⟩, E.inClosure_enc x.skel⟩

variable {E σ}

lemma skelToB_val (x : SkelAssembly E.k σ) :
    (skelToB E σ x).1 = ⟨bnat (E.enc x.copy), castVert (bFamily_enc x.skel).symm x.vert⟩ := rfl

/-- Every vertex of the `𝔹`-assembly lies at or within one cascade of an encoded copy:
a cut-off of an encoded skeleton address is an encoded address, or lies strictly inside
the cascade below one. -/
lemma exists_near_image {u : GWord N} (hu : E.Skel u) {w : List ℕ} (hw : w <+: bnat (E.enc u)) :
    ∃ t, E.Skel t ∧ bnat (E.enc t) <+: w ∧ w.length ≤ (E.enc t).length + L ∧
      (w = bnat (E.enc t) ∨ ∃ j : Fin N, (j : ℕ) < E.k t ∧ w <+: bnat (E.enc (t ++ [j]))
        ∧ w ≠ bnat (E.enc (t ++ [j]))) := by
  induction u using List.reverseRecOn with
  | nil =>
      rw [E.enc_nil, bnat_nil, List.prefix_nil] at hw
      subst hw
      exact ⟨[], E.skel_nil, by simp [E.enc_nil], by simp [E.enc_nil], Or.inl (by simp [E.enc_nil])⟩
  | append_singleton u j ih =>
      obtain ⟨hu', hj⟩ := E.skel_concat_iff.mp hu
      rw [E.enc_concat, bnat_append] at hw
      rcases List.prefix_or_prefix_of_prefix hw (List.prefix_append _ _) with h | h
      · exact ih hu' h
      · by_cases heq : w = bnat (E.enc (u ++ [j]))
        · have hlen : w.length = (E.enc (u ++ [j])).length := by rw [heq, bnat_length]
          exact ⟨u ++ [j], hu, heq ▸ List.prefix_refl _, by omega, Or.inl heq⟩
        · refine ⟨u, hu', h, ?_, Or.inr ⟨j, hj, by rw [E.enc_concat, bnat_append]; exact hw, heq⟩⟩
          have h1 := hw.length_le
          have h2 := E.slot_length_le u j hj
          simp only [List.length_append, bnat_length] at h1
          omega

/-- **The comparison in the ancestor position**: the two neck sums differ by the number
of internal cascade vertices crossed, at most `L - 1` per skeleton edge, and the
skeleton sum dominates the number of skeleton edges. -/
lemma skelToB_bounds_anc (hL : 1 ≤ L) {u v : GWord N} (hu : E.Skel u) (hv : E.Skel v)
    (huv : u <+: v) (hne : u ≠ v) (p : (gShapeSpace (σ u)).carrier)
    (q : (gShapeSpace (σ v)).carrier) :
    dist (⟨u, hu, p⟩ : SkelAssembly E.k σ) ⟨v, hv, q⟩
        ≤ dist (skelToB E σ ⟨u, hu, p⟩) (skelToB E σ ⟨v, hv, q⟩)
      ∧ dist (skelToB E σ ⟨u, hu, p⟩) (skelToB E σ ⟨v, hv, q⟩)
        ≤ L * dist (⟨u, hu, p⟩ : SkelAssembly E.k σ) ⟨v, hv, q⟩ := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  rw [BAssembly.dist_val, skelToB_val, skelToB_val]
  dsimp only
  have hne' : bnat (E.enc u) ≠ bnat (E.enc v) :=
    fun h ↦ hne (E.enc_injOn hu hv (bnat_injective h))
  rw [SkelAssembly.dist_anc hu hv huv hne, GAssembly.dist_anc (E.bFamily σ)
    (bnat_prefix_iff.mpr (E.enc_prefix huv)) hne', dist_castVert_exit, dist_castVert_entry,
    bnat_length, bnat_length, ← Nat.cast_sum, ← Nat.cast_sum]
  have hB := bNeckSum_anc (σ := σ) hv huv hne
  have hbd := E.enc_length_bounds hv huv
  have hcard := card_le_neckSum (liftN N σ) (u.length + 1) v.length (vals v)
  rw [SkelAssembly.neckSum_vals_nat] at hcard
  have hlt := BranchingProcess.length_lt_of_prefix_ne huv hne
  set SB := ∑ i ∈ Finset.Ico ((E.enc u).length + 1) (E.enc v).length,
    (E.bFamily σ ((bnat (E.enc v)).take i)).neckLen with hSB
  set Sσ := ∑ j ∈ Finset.Ico (u.length + 1) v.length, (σ (v.take j)).neckLen with hSσ
  set n := v.length - u.length with hn
  set m := (E.enc v).length - (E.enc u).length with hm
  have hm1 : n ≤ m := by omega
  have hm2 : m ≤ L * n := by omega
  have hSBn : SB + n = Sσ + m := hB
  have hA := dist_nonneg (x := p) (y := (gShapeSpace (σ u)).exit)
  have hBq := dist_nonneg (x := q) (y := (gShapeSpace (σ v)).entry)
  have hn1 : 1 ≤ n := by omega
  have hSBR : (SB : ℝ) + n = Sσ + m := by exact_mod_cast hSBn
  have hm1R : (n : ℝ) ≤ m := by exact_mod_cast hm1
  have hm2R : (m : ℝ) ≤ L * n := by exact_mod_cast hm2
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hcardR : (n : ℝ) ≤ 1 + Sσ := by
    have : n ≤ 1 + Sσ := by omega
    exact_mod_cast this
  have hprod : ((L : ℝ) - 1) * n ≤ (L - 1) * (1 + Sσ) :=
    mul_le_mul_of_nonneg_left hcardR (by linarith)
  constructor
  · linarith
  · nlinarith

/-- **The comparison in the diverging position**: on each branch the neck sum over `𝔹`
from the wedge exceeds the skeleton neck sum by at most `L - 1` per skeleton edge. -/
lemma skelToB_bounds_div (hL : 1 ≤ L) {u v : GWord N} (hu : E.Skel u) (hv : E.Skel v)
    (huv : ¬ u <+: v) (hvu : ¬ v <+: u) (p : (gShapeSpace (σ u)).carrier)
    (q : (gShapeSpace (σ v)).carrier) :
    dist (⟨u, hu, p⟩ : SkelAssembly E.k σ) ⟨v, hv, q⟩
        ≤ dist (skelToB E σ ⟨u, hu, p⟩) (skelToB E σ ⟨v, hv, q⟩)
      ∧ dist (skelToB E σ ⟨u, hu, p⟩) (skelToB E σ ⟨v, hv, q⟩)
        ≤ L * dist (⟨u, hu, p⟩ : SkelAssembly E.k σ) ⟨v, hv, q⟩ := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  rw [BAssembly.dist_val, skelToB_val, skelToB_val]
  dsimp only
  have huv' : ¬ bnat (E.enc u) <+: bnat (E.enc v) :=
    fun h ↦ huv (E.prefix_of_enc_prefix hu hv (bnat_prefix_iff.mp h))
  have hvu' : ¬ bnat (E.enc v) <+: bnat (E.enc u) :=
    fun h ↦ hvu (E.prefix_of_enc_prefix hv hu (bnat_prefix_iff.mp h))
  obtain ⟨z, a, b, hab, hza, hzb⟩ := exists_divergeW huv hvu
  rw [SkelAssembly.dist_div hu hv huv hvu, GAssembly.dist_div (E.bFamily σ) huv' hvu',
    dist_castVert_entry, dist_castVert_entry, bnat_length, bnat_length,
    wedge_of_divergeW hab hza hzb, ← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_sum,
    ← Nat.cast_sum]
  have hBu := bNeckSum_div (σ := σ) hu hv hab hza hzb
  have hBv := bNeckSum_div (σ := σ) hv hu hab.symm hzb hza
  rw [wedgeN_comm] at hBv
  obtain ⟨hw1, hw2⟩ := wedge_enc_bounds hu hv hab hza hzb
  obtain ⟨hw1', hw2'⟩ := wedge_enc_bounds hv hu hab.symm hzb hza
  rw [wedgeN_comm] at hw1' hw2'
  have hz : z <+: u := (List.prefix_append _ _).trans hza
  have hz' : z <+: v := (List.prefix_append _ _).trans hzb
  have hbdu := E.enc_length_bounds hu hz
  have hbdv := E.enc_length_bounds hv hz'
  have hbdu' := E.enc_length_bounds hu hza
  have hbdv' := E.enc_length_bounds hv hzb
  have hcardu := card_le_neckSum (liftN N σ) (z.length + 1) u.length (vals u)
  have hcardv := card_le_neckSum (liftN N σ) (z.length + 1) v.length (vals v)
  rw [SkelAssembly.neckSum_vals_nat] at hcardu hcardv
  have hzlt : z.length < u.length := by
    have := hza.length_le
    simp only [List.length_append, List.length_singleton] at this
    omega
  have hzlt' : z.length < v.length := by
    have := hzb.length_le
    simp only [List.length_append, List.length_singleton] at this
    omega
  have hzalen : (z ++ [a]).length = z.length + 1 := by simp
  have hzblen : (z ++ [b]).length = z.length + 1 := by simp
  rw [hzalen] at hbdu'
  rw [hzblen] at hbdv'
  set ω := (wedgeN (bnat (E.enc u)) (bnat (E.enc v))).length with hω
  set SBu := ∑ i ∈ Finset.Ico (ω + 1) (E.enc u).length,
    (E.bFamily σ ((bnat (E.enc u)).take i)).neckLen with hSBu
  set SBv := ∑ i ∈ Finset.Ico (ω + 1) (E.enc v).length,
    (E.bFamily σ ((bnat (E.enc v)).take i)).neckLen with hSBv
  set Su := ∑ j ∈ Finset.Ico (z.length + 1) u.length, (σ (u.take j)).neckLen with hSu
  set Sv := ∑ j ∈ Finset.Ico (z.length + 1) v.length, (σ (v.take j)).neckLen with hSv
  set nu := u.length - z.length with hnu
  set nv := v.length - z.length with hnv
  set mu := (E.enc u).length - ω with hmu
  set mv := (E.enc v).length - ω with hmv
  have hu1 : nu ≤ mu := by omega
  have hu2 : mu ≤ L * nu := by omega
  have hv1 : nv ≤ mv := by omega
  have hv2 : mv ≤ L * nv := by omega
  have hSBun : SBu + nu = Su + mu := hBu
  have hSBvn : SBv + nv = Sv + mv := hBv
  have hA := dist_nonneg (x := p) (y := (gShapeSpace (σ u)).entry)
  have hBq := dist_nonneg (x := q) (y := (gShapeSpace (σ v)).entry)
  have hnu1 : 1 ≤ nu := by omega
  have hnv1 : 1 ≤ nv := by omega
  have hSBuR : (SBu : ℝ) + nu = Su + mu := by exact_mod_cast hSBun
  have hSBvR : (SBv : ℝ) + nv = Sv + mv := by exact_mod_cast hSBvn
  have hu1R : (nu : ℝ) ≤ mu := by exact_mod_cast hu1
  have hu2R : (mu : ℝ) ≤ L * nu := by exact_mod_cast hu2
  have hv1R : (nv : ℝ) ≤ mv := by exact_mod_cast hv1
  have hv2R : (mv : ℝ) ≤ L * nv := by exact_mod_cast hv2
  have hcarduR : (nu : ℝ) ≤ 1 + Su := by
    have : nu ≤ 1 + Su := by omega
    exact_mod_cast this
  have hcardvR : (nv : ℝ) ≤ 1 + Sv := by
    have : nv ≤ 1 + Sv := by omega
    exact_mod_cast this
  have hprodu : ((L : ℝ) - 1) * nu ≤ (L - 1) * (1 + Su) :=
    mul_le_mul_of_nonneg_left hcarduR (by linarith)
  have hprodv : ((L : ℝ) - 1) * nv ≤ (L - 1) * (1 + Sv) :=
    mul_le_mul_of_nonneg_left hcardvR (by linarith)
  constructor
  · linarith
  · nlinarith

/-- **Coarse density of the encoded copies**: every vertex of the `𝔹`-assembly is
within `L` of the image, an internal cascade vertex lying within `L` of the exit of the
encoded copy above it. -/
lemma skelToB_dense (y : BAssembly E σ) : ∃ x, dist (skelToB E σ x) y ≤ L := by
  obtain ⟨⟨w, q⟩, u, hu, hw⟩ := y
  dsimp only at hw
  obtain ⟨t, ht, htw, hlen, hcase⟩ := exists_near_image hu hw
  by_cases hweq : w = bnat (E.enc t)
  · subst hweq
    refine ⟨⟨t, ht, castVert (bFamily_enc ht) q⟩, ?_⟩
    rw [BAssembly.dist_val, skelToB_val]
    dsimp only
    rw [GAssembly.dist_same, GAssembly.dist_gShapeSpace, castVert_val, castVert_val,
      addrDist_self]
    exact_mod_cast Nat.zero_le L
  · obtain ⟨j, hj, hwj, hwj'⟩ := hcase.resolve_left hweq
    have hnot : ∀ w', bnat (E.enc t) <+: w' → w' <+: w → w' ≠ bnat (E.enc t) →
        E.bFamily σ w' = gOne := by
      intro w' h1 h2 h3
      refine bFamily_of_not_isImage (E.not_isImage_of_between ht hj h1 (h2.trans hwj) h3 ?_)
      intro h4
      have h5 := h2.length_le
      have h6 := hwj.length_le
      rw [h4] at h5
      have : w = bnat (E.enc (t ++ [j])) := hwj.eq_of_length (le_antisymm h6 h5)
      exact hwj' this
    refine ⟨⟨t, ht, (gShapeSpace (σ t)).exit⟩, ?_⟩
    rw [BAssembly.dist_val, skelToB_val]
    dsimp only
    rw [GAssembly.dist_anc (E.bFamily σ) htw (Ne.symm hweq), dist_castVert_exit, dist_self,
      GAssembly.dist_gShapeSpace, GAssembly.entry_gShapeSpace_val,
      eq_nil_of_gOne (hnot w htw (List.prefix_refl _) hweq) q, addrDist_self, bnat_length]
    have hterm : ∀ i ∈ Finset.Ico ((E.enc t).length + 1) w.length,
        ((E.bFamily σ (w.take i)).neckLen : ℝ) = 1 := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have h1 : bnat (E.enc t) <+: w.take i :=
        List.prefix_of_prefix_length_le htw (List.take_prefix _ _)
          (by rw [bnat_length, List.length_take, min_eq_left hi.2.le]; omega)
      have h3 : w.take i ≠ bnat (E.enc t) := by
        intro h
        have := congrArg List.length h
        rw [List.length_take, min_eq_left hi.2.le, bnat_length] at this
        omega
      rw [hnot _ h1 (List.take_prefix _ _) h3]
      norm_num [GShape.neckLen, gOne]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    have h1 := htw.length_le
    rw [bnat_length] at h1
    have h2 : (E.enc t).length < w.length := by
      rcases Nat.lt_or_ge (E.enc t).length w.length with h | h
      · exact h
      · exact absurd (htw.eq_of_length (by rw [bnat_length]; omega)) (Ne.symm hweq)
    have h3 : ((w.length - ((E.enc t).length + 1) : ℕ) : ℝ) = w.length - (E.enc t).length - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [h3]
    have h4 : (w.length : ℝ) ≤ (E.enc t).length + L := by exact_mod_cast hlen
    push_cast
    linarith

/-- **The `𝔹`-assembly is quasi-isometric to the skeleton assembly**
(**`thm:hairy-general`**): reading the copies at their encodings is an `L`-quasi-isometry
of the assemblies.  Inside a copy nothing changes; between copies the neck sums over `𝔹`
exceed those over the skeleton by the number of internal cascade vertices crossed, at most
`L - 1` per skeleton edge; and every internal cascade vertex lies within `L` of the exit
above it. -/
theorem skelToB_isQIMap (hL : 1 ≤ L) : IsQIMap (L : ℝ) (skelToB E σ) := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have key : ∀ x y : SkelAssembly E.k σ,
      dist x y ≤ dist (skelToB E σ x) (skelToB E σ y)
        ∧ dist (skelToB E σ x) (skelToB E σ y) ≤ L * dist x y := by
    rintro ⟨u, hu, p⟩ ⟨v, hv, q⟩
    rcases copy_trichotomyW u v with rfl | ⟨huv, hne⟩ | ⟨hvu, hne⟩ | ⟨huv, hvu⟩
    · rw [BAssembly.dist_val, skelToB_val, skelToB_val]
      dsimp only
      rw [SkelAssembly.dist_same, GAssembly.dist_same, dist_castVert]
      have := dist_nonneg (x := p) (y := q)
      exact ⟨le_rfl, by nlinarith⟩
    · exact skelToB_bounds_anc hL hu hv huv hne p q
    · obtain ⟨h1, h2⟩ := skelToB_bounds_anc hL hv hu hvu hne q p
      rw [dist_comm, dist_comm (skelToB E σ _)]
      exact ⟨h1, h2⟩
    · exact skelToB_bounds_div hL hu hv huv hvu p q
  refine ⟨fun x y ↦ ?_, fun x y ↦ ?_, skelToB_dense⟩
  · have := (key x y).2
    linarith
  · have h1 := (key x y).1
    have h2 := dist_nonneg (x := skelToB E σ x) (y := skelToB E σ y)
    nlinarith

end CascadeEnc

end ChainClasses
