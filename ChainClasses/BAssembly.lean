/-
`thm:hairy-general` of `trichotomy.tex`, the deterministic geometry: the alignment of the
two label fields lives on `𝔹`, not on the reduced skeletons, and the assembly that the
glued transfer of `it:general-glued` runs over is the `𝔹`-assembly, the shape of a
skeleton vertex placed at its cascade root and a one-vertex shape at every forced slot.
Four deterministic facts carry the proof from there to a quasi-isometry of the samples.

A hairy sample at general arity is isometric to the assembly of its own shapes over its
reduced skeleton, by the address translation of `ShapeDecomposition` redone at general
arity: a word of the assembly is read letter by letter, the letter read at a vertex of the
sample being chosen by the letter map of that vertex, which sends the bush indices of a
neck vertex to its dying children in letter order and the neck or copy indices after them
to its surviving children.  The cascade encoding enters abstractly, as a map of skeleton
addresses to binary words appending one nonempty slot word of length at most `L` per
edge, the slots of one vertex pairwise prefix-incomparable; `EngineBridge` instantiates
it with the engine's cascades.  Reading the copies at their encodings is then an
`L`-quasi-isometry of the skeleton assembly onto the `𝔹`-assembly, the neck sums of
`eq:assembly-anc` and `eq:assembly-div` over `𝔹` exceeding those over the skeleton by the
number of internal cascade vertices crossed.  An automorphism of `𝔹` matching the shape
labels relabels one `𝔹`-assembly onto the other, and `thm:glued-transfer` at general
arity glues the matched shapes into an `8K²`-quasi-isometry.  The composition is a
quasi-isometry of the sample graphs at the constant `216 L L'² K²`.

* `bnat`, `unbnat`, `IsBin`, `vals`, `unval`: binary words and ambient words read over
  `ℕ`, the alphabet the assemblies of `GeneralAssembly` are indexed by.
* `CascadeEnc`: **the cascade encoding, abstractly**, the arity field `k`, the encoding
  `enc` and its slots; `CascadeEnc.prefix_of_enc_prefix`, `CascadeEnc.enc_injOn`,
  `CascadeEnc.enc_length_bounds`: the encoding reflects the prefix order on the skeleton
  `sample k` and stretches a chain by a factor between one and `L`.
* `CascadeEnc.bFamily`, `CascadeEnc.InClosure`, `BAssembly`: **the shape family over `𝔹`
  and the `𝔹`-assembly** of **`thm:hairy-general`**, over the prefix closure of the
  encoded skeleton, the one-vertex shape at the internal cascade vertices.
* `SkelAssembly` with `dist_same`, `dist_anc`, `dist_div`: the assembly of a shape family
  over its reduced skeleton, the distance formulas of `GeneralAssembly` read over the
  skeleton.
* `CascadeEnc.bNecks_sum_eq`, `CascadeEnc.bNeckSum_anc`, `CascadeEnc.bNeckSum_div`: **the
  neck sums over `𝔹`**, the skeleton neck sums plus the internal cascade vertices crossed.
* `CascadeEnc.skelToB`, `CascadeEnc.skelToB_isQIMap`: **the `𝔹`-assembly is
  `L`-quasi-isometric to the skeleton assembly**.
* `IsTreeAutOn`, `GAssembly.relabel`, `GAssembly.dist_relabel`, `bAut`,
  `isTreeAutOn_bAut`: **the relabelling of an assembly along an automorphism of `𝔹`**, an
  isometry on the binary copies.
* `CascadeEnc.qi_of_bShape_matching`: **the deterministic core of `thm:hairy-general`**
  over `𝔹`, an automorphism matching the encoded skeletons and the shape labels at `K`
  gives an `8K²`-quasi-isometry of the `𝔹`-assemblies.
* `IsQIMap.comp`, `IsQIMap.exists_symm`, `isQIWith_of_skel_qi`,
  `CascadeEnc.sample_qi_of_bShape_matching_of_isometric`: the composition, over abstract
  isometries of the samples with their skeleton assemblies.
* `transN` with `transN_addrDist`: the address translation of a field of letter maps over
  `ℕ`, an isometry when the letter maps are injective.
* `dyingSet`, `survLetter`, `dyingLetter`, `letterMap` with `letterMap_lt_iff`,
  `letterMap_injective`, `letterMap_surj`: **the letter map of a vertex**, a bijection of
  the child indices of the realisation onto the children of the vertex.
* `neckAddr`, `isAddr_realiseAux_neck_concat`, `isAddr_realiseAux_bush`,
  `isAddr_realiseAux_cases`: **the addresses of a realisation** at general arity, the
  neck vertices, their children, and the bushes.
* `IsGHairySample`: the deterministic hypotheses of **`thm:hairy-general`**, offspring
  within the alphabet, survival, and every neck ray meeting a split.
* `neckPath`, `neckIter_eq_ambSub_neckPath`, `gEntryV`, `redSub_eq_ambSub_gEntryV`: the
  descent of `GeneralDecomposition` located in the ambient tree, the copies being the
  subtrees at the entry vertices.
* `SkelAssembly.exists_code_concat_iff`, `transSampleN`, `transSampleN_neck`,
  `transSampleN_gCopyAddr`, `transSampleN_bush`, `transSampleN_code_spec`: **the
  dictionary**, the children of a vertex of the skeleton assembly and of its translate.
* `gAssembly_isometric_sample`: **`thm:shape-iid` at general arity, the isometry**, the
  premise of **`it:general-glued`**: a hairy sample is isometric to the assembly of its
  shapes over its reduced skeleton.
* `sample_qi_of_bShape_matching`: **`thm:hairy-general`, the deterministic core**: two
  hairy samples with encoded skeletons matched by an automorphism of `𝔹` at
  comparability `K` are `⌈216 L L'² K²⌉`-quasi-isometric as graphs.
-/
import ChainClasses.GeneralAssembly
import ChainClasses.GeneralShrink
import ChainClasses.GeneralDecomposition
import ChainClasses.GeneralShapeTail
import ChainClasses.GeneralBushPoint
import ChainClasses.AssemblyRelabel
import ChainClasses.ShapeDecomposition
import ChainClasses.GeneralCascade
import ChainClasses.HairyCross

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
          · rw [if_neg (fun h ↦ hab (Fin.ext h)), if_neg hab]
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
      simp only [vals_cons, unval, List.filterMap_cons, dif_pos a.isLt, Fin.eta]
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

/-- The encoding is an order embedding of the skeleton. -/
lemma enc_prefix_iff {s t : GWord N} (hs : E.Skel s) (ht : E.Skel t) :
    E.enc s <+: E.enc t ↔ s <+: t :=
  ⟨E.prefix_of_enc_prefix hs ht, E.enc_prefix⟩

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

lemma enc_length_le_iff {v s t : GWord N} (hv : E.Skel v) (hs : s <+: v) (ht : t <+: v) :
    (E.enc s).length ≤ (E.enc t).length ↔ s.length ≤ t.length := by
  rw [← Nat.not_lt, ← Nat.not_lt, E.enc_length_lt_iff hv ht hs]

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

lemma inClosure_of_isImage {w : List ℕ} (h : E.IsImage w) : E.InClosure w := by
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨u, hu, List.prefix_refl _⟩

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
  rw [bFamily, dif_pos h]
  have hspec := h.choose_spec
  have : h.choose = u := E.enc_injOn hspec.1 hu (bnat_injective hspec.2).symm
  rw [this]

lemma bFamily_of_not_isImage {σ : GWord N → GShape} {w : List ℕ} (h : ¬ E.IsImage w) :
    E.bFamily σ w = gOne := by
  have h' : ¬ ∃ u, E.Skel u ∧ w = bnat (E.enc u) := h
  rw [bFamily, dif_neg h']

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

/-! ### Relabelling an assembly along a tree automorphism -/

/-- A map of words acting as a tree automorphism on a set of words: it preserves
lengths, preserves and reflects the prefix order, and commutes with truncation. -/
structure IsTreeAutOn (S : List ℕ → Prop) (f : List ℕ → List ℕ) : Prop where
  length : ∀ w, S w → (f w).length = w.length
  prefix_iff : ∀ u v, S u → S v → (f u <+: f v ↔ u <+: v)
  take : ∀ v, S v → ∀ i, f (v.take i) = (f v).take i

namespace IsTreeAutOn

variable {S : List ℕ → Prop} {f : List ℕ → List ℕ}

lemma injOn (hf : IsTreeAutOn S f) {u v : List ℕ} (hu : S u) (hv : S v) (h : f u = f v) :
    u = v := by
  have h1 : u <+: v := (hf.prefix_iff u v hu hv).mp (h ▸ List.prefix_refl _)
  have h2 : v <+: u := (hf.prefix_iff v u hv hu).mp (h ▸ List.prefix_refl _)
  exact h1.eq_of_length (le_antisymm h1.length_le h2.length_le)

/-- A tree automorphism preserves the depth of the wedge. -/
lemma wedgeN_length (hS : ∀ u v, u <+: v → S v → S u) (hf : IsTreeAutOn S f) {u v : List ℕ}
    (hu : S u) (hv : S v) : (wedgeN (f u) (f v)).length = (wedgeN u v).length := by
  set z := wedgeN u v with hz
  have hzu : z = u.take z.length := List.prefix_iff_eq_take.mp (wedgeN_prefix_left u v)
  have hzv : z = v.take z.length := List.prefix_iff_eq_take.mp (wedgeN_prefix_right u v)
  have h1 : f z <+: f u := (hf.prefix_iff z u (hS z u (wedgeN_prefix_left u v) hu) hu).mpr
    (wedgeN_prefix_left u v)
  have h2 : f z <+: f v := (hf.prefix_iff z v (hS z v (wedgeN_prefix_right u v) hv) hv).mpr
    (wedgeN_prefix_right u v)
  have hle : z.length ≤ (wedgeN (f u) (f v)).length := by
    have := (prefix_wedgeN h1 h2).length_le
    rwa [hf.length z (hS z u (wedgeN_prefix_left u v) hu)] at this
  refine le_antisymm ?_ hle
  set m := (wedgeN (f u) (f v)).length with hm
  have hmu : m ≤ u.length := by
    have := wedgeN_length_le_left (f u) (f v)
    rwa [hf.length u hu] at this
  have hmv : m ≤ v.length := by
    have := wedgeN_length_le_right (f u) (f v)
    rwa [hf.length v hv] at this
  have hωu : wedgeN (f u) (f v) = f (u.take m) := by
    rw [hf.take u hu, ← List.prefix_iff_eq_take.mp (wedgeN_prefix_left (f u) (f v))]
  have hωv : wedgeN (f u) (f v) = f (v.take m) := by
    rw [hf.take v hv, ← List.prefix_iff_eq_take.mp (wedgeN_prefix_right (f u) (f v))]
  have heq : u.take m = v.take m :=
    hf.injOn (hS _ u (List.take_prefix _ _) hu) (hS _ v (List.take_prefix _ _) hv)
      (hωu.symm.trans hωv)
  have hpre : u.take m <+: wedgeN u v :=
    prefix_wedgeN (List.take_prefix _ _) (heq ▸ List.take_prefix _ _)
  have := hpre.length_le
  rwa [List.length_take, min_eq_left hmu] at this

end IsTreeAutOn

namespace GAssembly

/-- **The relabelling of an assembly along a map of copy words**: the copy at `w` of
the assembly of `σ ∘ f` is the copy at `f w` of the assembly of `σ`, carrying the same
shape and hence the same vertices. -/
def relabel (f : List ℕ → List ℕ) (σ : List ℕ → GShape)
    (x : GAssembly (fun w ↦ σ (f w))) : GAssembly σ :=
  ⟨f x.copy, x.vert⟩

@[simp] lemma relabel_copy (f : List ℕ → List ℕ) (σ : List ℕ → GShape)
    (x : GAssembly (fun w ↦ σ (f w))) : (relabel f σ x).copy = f x.copy := rfl

/-- **The relabelling is an isometry on the copies where the map is a tree
automorphism**: each of the three distance formulas is preserved, the map preserving
lengths, prefixes, truncations and wedges. -/
theorem dist_relabel {S : List ℕ → Prop} (hS : ∀ u v, u <+: v → S v → S u)
    {f : List ℕ → List ℕ} (hf : IsTreeAutOn S f) (σ : List ℕ → GShape)
    (x y : GAssembly (fun w ↦ σ (f w))) (hx : S x.copy) (hy : S y.copy) :
    dist (relabel f σ x) (relabel f σ y) = dist x y := by
  obtain ⟨u, p⟩ := x
  obtain ⟨v, q⟩ := y
  dsimp only at hx hy
  show dist (⟨f u, p⟩ : GAssembly σ) ⟨f v, q⟩ = dist (⟨u, p⟩ : GAssembly (fun w ↦ σ (f w))) ⟨v, q⟩
  have hsum : ∀ (a b : ℕ) (w : List ℕ), S w →
      ∑ i ∈ Finset.Ico a b, ((σ ((f w).take i)).neckLen : ℝ)
        = ∑ i ∈ Finset.Ico a b, ((σ (f (w.take i))).neckLen : ℝ) := by
    intro a b w hw
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hf.take w hw]
  rcases copy_trichotomy u v with rfl | ⟨huv, hne⟩ | ⟨hvu, hne⟩ | ⟨huv, hvu⟩
  · rw [dist_same σ (f u) p q, dist_same (fun w ↦ σ (f w)) u p q]
  · have hne' : f u ≠ f v := fun h ↦ hne (hf.injOn hx hy h)
    rw [dist_anc σ ((hf.prefix_iff u v hx hy).mpr huv) hne' p q,
      dist_anc (fun w ↦ σ (f w)) huv hne p q, hf.length u hx, hf.length v hy, hsum _ _ v hy]
  · have hne' : f v ≠ f u := fun h ↦ hne (hf.injOn hy hx h)
    rw [dist_comm (⟨f u, p⟩ : GAssembly σ), dist_comm (⟨u, p⟩ : GAssembly (fun w ↦ σ (f w))),
      dist_anc σ ((hf.prefix_iff v u hy hx).mpr hvu) hne' q p,
      dist_anc (fun w ↦ σ (f w)) hvu hne q p, hf.length u hx, hf.length v hy, hsum _ _ u hx]
  · have huv' : ¬ f u <+: f v := fun h ↦ huv ((hf.prefix_iff u v hx hy).mp h)
    have hvu' : ¬ f v <+: f u := fun h ↦ hvu ((hf.prefix_iff v u hy hx).mp h)
    rw [dist_div σ huv' hvu' p q, dist_div (fun w ↦ σ (f w)) huv hvu p q, hf.length u hx,
      hf.length v hy, hf.wedgeN_length hS hx hy, hsum _ _ u hx, hsum _ _ v hy]

end GAssembly

/-! ### Automorphisms of `𝔹` on words over `ℕ` -/

@[simp] lemma unbnat_length (w : List ℕ) : (unbnat w).length = w.length := by simp [unbnat]

@[simp] lemma unbnat_take (w : List ℕ) (i : ℕ) : unbnat (w.take i) = (unbnat w).take i := by
  simp [unbnat, List.map_take]

open Classical in
/-- **An automorphism of `𝔹` read on words over `ℕ`**: the portrait automorphism
`autOf π` on the binary words, the identity elsewhere, so that the non-binary words,
which carry no shape, stay off the encoded skeletons. -/
noncomputable def bAut (π : Word → Bool ≃ Bool) (w : List ℕ) : List ℕ :=
  if IsBin w then bnat (autOf π (unbnat w)) else w

lemma bAut_of_isBin (π : Word → Bool ≃ Bool) {w : List ℕ} (h : IsBin w) :
    bAut π w = bnat (autOf π (unbnat w)) := by
  rw [bAut, if_pos h]

lemma bAut_bnat (π : Word → Bool ≃ Bool) (x : Word) : bAut π (bnat x) = bnat (autOf π x) := by
  rw [bAut_of_isBin π (isBin_bnat x), unbnat_bnat]

lemma bAut_of_not_isBin (π : Word → Bool ≃ Bool) {w : List ℕ} (h : ¬ IsBin w) :
    bAut π w = w := by
  rw [bAut, if_neg h]

/-- The binary words are prefix-closed. -/
lemma isBin_of_prefix {u v : List ℕ} (h : u <+: v) (hv : IsBin v) : IsBin u := hv.of_prefix h

/-- **The automorphism acts as a tree automorphism on the binary words.** -/
lemma isTreeAutOn_bAut (π : Word → Bool ≃ Bool) : IsTreeAutOn IsBin (bAut π) where
  length w hw := by rw [bAut_of_isBin π hw, bnat_length, autOf_length, unbnat_length]
  prefix_iff u v hu hv := by
    rw [bAut_of_isBin π hu, bAut_of_isBin π hv, bnat_prefix_iff, autOf_prefix_iff,
      ← bnat_prefix_iff, bnat_unbnat hu, bnat_unbnat hv]
  take v hv i := by
    rw [bAut_of_isBin π hv, bAut_of_isBin π (hv.of_prefix (List.take_prefix _ _)), unbnat_take,
      autOf_take, bnat_take]

/-! ### The deterministic core over `𝔹` -/

namespace CascadeEnc

variable {N' L L' : ℕ}

/-- **The deterministic core of `thm:hairy-general`**: if an automorphism `π` of `𝔹`
carries the encoded skeleton of one sample onto that of the other and matches the shape
labels, the shape at `w` and the shape at `autOf π w` being `K`-comparable at every
binary word, then the two `𝔹`-assemblies admit an `8K²`-quasi-isometry.  The per-copy
maps are glued by `thm:glued-transfer` at general arity into a quasi-isometry onto the
assembly of the relabelled family, and the relabelling along `π` identifies that assembly
with the `𝔹`-assembly of the second sample. -/
theorem qi_of_bShape_matching {E : CascadeEnc N L} {E' : CascadeEnc N' L'}
    {σ : GWord N → GShape} {σ' : GWord N' → GShape} {K : ℝ} (hK : 1 ≤ K)
    (π : Word → Bool ≃ Bool)
    (hπ : ∀ w : Word, E.InClosure (bnat w) ↔ E'.InClosure (bnat (autOf π w)))
    (hcomp : ∀ w : Word, MarkedQI K (gShapeSpace (E.bFamily σ (bnat w)))
      (gShapeSpace (E'.bFamily σ' (bnat (autOf π w))))) :
    ∃ f : BAssembly E σ → BAssembly E' σ', IsQIMap (8 * K ^ 2) f := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hcomp' : ∀ w : List ℕ, MarkedQI K (gShapeSpace (E.bFamily σ w))
      (gShapeSpace (E'.bFamily σ' (bAut π w))) := by
    intro w
    by_cases hw : IsBin w
    · have h := hcomp (unbnat w)
      rwa [bnat_unbnat hw, ← bAut_of_isBin π hw] at h
    · rw [bAut_of_not_isBin π hw, bFamily_of_not_isBin hw, bFamily_of_not_isBin hw]
      exact markedQI_id hK _
  choose φ hφ using hcomp'
  obtain ⟨hup, hlow, -⟩ := GAssembly.glued_transfer (σ := E.bFamily σ)
    (σ' := fun w ↦ E'.bFamily σ' (bAut π w)) hK hφ
  have hcl : ∀ w, E.InClosure w → E'.InClosure (bAut π w) := by
    intro w hw
    have hb := hw.isBin
    rw [bAut_of_isBin π hb]
    exact (hπ (unbnat w)).mp (by rwa [bnat_unbnat hb])
  have hcl' : ∀ w, E'.InClosure w → ∃ w', E.InClosure w' ∧ bAut π w' = w := by
    intro w hw
    have hb := hw.isBin
    obtain ⟨x, hx⟩ := autOf_surjective π (unbnat w)
    refine ⟨bnat x, (hπ x).mpr (by rw [hx, bnat_unbnat hb]; exact hw), ?_⟩
    rw [bAut_bnat, hx, bnat_unbnat hb]
  have hrel : ∀ a b : GAssembly (fun w ↦ E'.bFamily σ' (bAut π w)),
      E.InClosure a.copy → E.InClosure b.copy →
      dist (GAssembly.relabel (bAut π) (E'.bFamily σ') a)
          (GAssembly.relabel (bAut π) (E'.bFamily σ') b) = dist a b := fun a b ha hb ↦
    GAssembly.dist_relabel (fun _ _ h hv ↦ isBin_of_prefix h hv) (isTreeAutOn_bAut π) _ _ _
      ha.isBin hb.isBin
  refine ⟨fun x ↦ ⟨GAssembly.relabel (bAut π) (E'.bFamily σ') (GAssembly.glue φ x.1),
    hcl _ x.2⟩, ?_, ?_, ?_⟩
  · intro a b
    rw [BAssembly.dist_val, BAssembly.dist_val]
    dsimp only
    rw [hrel _ _ a.2 b.2]
    exact hup a.1 b.1
  · intro a b
    rw [BAssembly.dist_val, BAssembly.dist_val]
    dsimp only
    rw [hrel _ _ a.2 b.2]
    exact hlow a.1 b.1
  · rintro ⟨⟨w, r⟩, hw⟩
    obtain ⟨w', hw', hw'eq⟩ := hcl' w hw
    have hshape : E'.bFamily σ' (bAut π w') = E'.bFamily σ' w := by rw [hw'eq]
    set z : GAssembly (fun w ↦ E'.bFamily σ' (bAut π w)) := ⟨w', castVert hshape.symm r⟩ with hz
    have hzrel : GAssembly.relabel (bAut π) (E'.bFamily σ') z = ⟨w, r⟩ :=
      GAssembly.vert_eq hw'eq rfl
    obtain ⟨a, ha⟩ := (hφ w').dense (castVert hshape.symm r)
    refine ⟨⟨⟨w', a⟩, hw'⟩, ?_⟩
    rw [BAssembly.dist_val]
    dsimp only
    rw [← hzrel, hrel _ z hw' hw']
    have h : dist (GAssembly.glue φ (⟨w', a⟩ : GAssembly (E.bFamily σ))) z
        = dist (φ w' a) (castVert hshape.symm r) := GAssembly.dist_same _ w' _ _
    rw [h]
    exact ha.trans (by nlinarith)

end CascadeEnc

/-! ### Composing quasi-isometries of metric spaces -/

/-- Quasi-isometries of metric spaces compose, at the constant `3KK'`. -/
lemma IsQIMap.comp {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    {K K' : ℝ} (hK : 1 ≤ K) (hK' : 1 ≤ K') {f : X → Y} {g : Y → Z} (hf : IsQIMap K f)
    (hg : IsQIMap K' g) : IsQIMap (3 * K * K') (g ∘ f) := by
  have hK0 : 0 ≤ K := by linarith
  have hK0' : 0 ≤ K' := by linarith
  have hKK' : 1 ≤ K * K' := one_le_mul_of_one_le_of_one_le hK hK'
  refine ⟨fun a b ↦ ?_, fun a b ↦ ?_, fun z ↦ ?_⟩
  · have h1 := hg.upper (f a) (f b)
    have h2 := hf.upper a b
    have h3 := mul_le_mul_of_nonneg_left h2 hK0'
    have h4 := dist_nonneg (x := a) (y := b)
    have h5 : 0 ≤ K * K' * dist a b := by positivity
    have h6 : K' ≤ K * K' := by nlinarith
    simp only [Function.comp]
    linarith
  · have h1 := hf.lower a b
    have h2 := hg.lower (f a) (f b)
    have h3 := mul_le_mul_of_nonneg_left h2 hK0
    have h4 := dist_nonneg (x := g (f a)) (y := g (f b))
    have h5 : 0 ≤ K * K' * dist (g (f a)) (g (f b)) := by positivity
    have h6 : 0 ≤ K * K' ^ 2 * (K - 1) := mul_nonneg (by positivity) (by linarith)
    have h7 : 0 ≤ K ^ 2 * (K' ^ 2 - 1) := mul_nonneg (by positivity) (by nlinarith)
    have h8 : 0 ≤ K ^ 2 * K' ^ 2 := by positivity
    simp only [Function.comp]
    linarith
  · obtain ⟨y, hy⟩ := hg.dense z
    obtain ⟨x, hx⟩ := hf.dense y
    refine ⟨x, ?_⟩
    have h1 := dist_triangle (g (f x)) (g y) z
    have h2 := hg.upper (f x) y
    have h3 : K' * dist (f x) y ≤ K' * K := mul_le_mul_of_nonneg_left hx hK0'
    have h4 : K' ≤ K * K' := by nlinarith
    simp only [Function.comp]
    linarith

/-- A quasi-isometry of metric spaces has a quasi-inverse, at the constant `3K²`. -/
lemma IsQIMap.exists_symm {X Y : Type*} [MetricSpace X] [MetricSpace Y] {K : ℝ} (hK : 1 ≤ K)
    {f : X → Y} (hf : IsQIMap K f) : ∃ g : Y → X, IsQIMap (3 * K ^ 2) g := by
  choose g hg using hf.dense
  have hK0 : 0 ≤ K := by linarith
  have hK2 : K ≤ 3 * K ^ 2 := by nlinarith
  refine ⟨g, fun y y' ↦ ?_, fun y y' ↦ ?_, fun x ↦ ?_⟩
  · have h1 := hf.lower (g y) (g y')
    have h2 := dist_triangle (f (g y)) y (f (g y'))
    have h3 := dist_triangle y y' (f (g y'))
    have h4 := hg y
    have h5 := hg y'
    rw [dist_comm] at h5
    have h6 : K * dist (f (g y)) (f (g y')) ≤ K * (2 * K + dist y y') :=
      mul_le_mul_of_nonneg_left (by linarith) hK0
    have h7 : K * dist y y' ≤ 3 * K ^ 2 * dist y y' :=
      mul_le_mul_of_nonneg_right hK2 dist_nonneg
    linarith
  · have h1 := hf.upper (g y) (g y')
    have h2 := dist_triangle y (f (g y)) (f (g y'))
    have h3 := dist_triangle y (f (g y')) y'
    have h4 := hg y
    have h5 := hg y'
    rw [dist_comm] at h4
    have h6 := dist_nonneg (x := g y) (y := g y')
    have h7 : K * dist (g y) (g y') ≤ 3 * K ^ 2 * dist (g y) (g y') :=
      mul_le_mul_of_nonneg_right hK2 h6
    have h8 : 3 * K ≤ (3 * K ^ 2) ^ 2 := by nlinarith
    linarith
  · refine ⟨f x, ?_⟩
    have h1 := hf.lower (g (f x)) x
    have h2 := hg (f x)
    have h3 : K * dist (f (g (f x))) (f x) ≤ K * K := mul_le_mul_of_nonneg_left h2 hK0
    have h4 := sq_nonneg K
    nlinarith

/-! ### From the skeleton assemblies to the sample graphs -/

/-- **A quasi-isometry of the skeleton assemblies is one of the sample graphs**, read
through isometries identifying each sample with the assembly of its shapes, the real
constant rounded up. -/
theorem isQIWith_of_skel_qi {N' : ℕ} {c : GWord N → ℕ} {c' : GWord N' → ℕ}
    {k : GWord N → ℕ} {σ : GWord N → GShape} {k' : GWord N' → ℕ} {σ' : GWord N' → GShape}
    {Φ : SkelAssembly k σ → {v : GWord N // v ∈ sample c}} (hΦ : Function.Bijective Φ)
    (hΦd : ∀ x y, (BranchingProcess.treeDist (Φ x).1 (Φ y).1 : ℝ) = dist x y)
    {Φ' : SkelAssembly k' σ' → {v : GWord N' // v ∈ sample c'}} (hΦ' : Function.Bijective Φ')
    (hΦd' : ∀ x y, (BranchingProcess.treeDist (Φ' x).1 (Φ' y).1 : ℝ) = dist x y)
    {C : ℝ} (hC : 0 ≤ C) {g : SkelAssembly k σ → SkelAssembly k' σ'} (hg : IsQIMap C g) :
    ∃ F : {v : GWord N // v ∈ sample c} → {v : GWord N' // v ∈ sample c'},
      BranchingProcess.IsQIWith ⌈C⌉₊ (wordGraphN (· ∈ sample c)) (wordGraphN (· ∈ sample c')) F := by
  set e := Equiv.ofBijective Φ hΦ
  have heapp : ∀ x, Φ (e.symm x) = x := fun x ↦ e.apply_symm_apply x
  have hT : PrefixClosedN (fun v : GWord N ↦ v ∈ sample c) :=
    fun _ _ h hv ↦ BranchingProcess.Subtree.mem_of_prefix h hv
  have hT' : PrefixClosedN (fun v : GWord N' ↦ v ∈ sample c') :=
    fun _ _ h hv ↦ BranchingProcess.Subtree.mem_of_prefix h hv
  have hCK : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  have hK0 : (0 : ℝ) ≤ ⌈C⌉₊ := Nat.cast_nonneg _
  refine ⟨fun x ↦ Φ' (g (e.symm x)), ⟨?_, ?_, ?_⟩⟩
  · intro a b
    rw [wordGraphN_dist hT, wordGraphN_dist hT']
    have h := hg.upper (e.symm a) (e.symm b)
    rw [← hΦd', ← hΦd (e.symm a) (e.symm b), heapp, heapp] at h
    have hd := Nat.cast_nonneg (α := ℝ) (BranchingProcess.treeDist a.1 b.1)
    have h2 : C * (BranchingProcess.treeDist a.1 b.1 : ℝ) ≤ ⌈C⌉₊ * BranchingProcess.treeDist a.1 b.1 :=
      mul_le_mul_of_nonneg_right hCK hd
    have hcast : (BranchingProcess.treeDist (Φ' (g (e.symm a))).1 (Φ' (g (e.symm b))).1 : ℝ)
        ≤ ((⌈C⌉₊ * BranchingProcess.treeDist a.1 b.1 + ⌈C⌉₊ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  · intro a b
    rw [wordGraphN_dist hT, wordGraphN_dist hT']
    have h := hg.lower (e.symm a) (e.symm b)
    rw [← hΦd', ← hΦd (e.symm a) (e.symm b), heapp, heapp] at h
    have hd := Nat.cast_nonneg (α := ℝ)
      (BranchingProcess.treeDist (Φ' (g (e.symm a))).1 (Φ' (g (e.symm b))).1)
    have h2 : C * (BranchingProcess.treeDist (Φ' (g (e.symm a))).1 (Φ' (g (e.symm b))).1 : ℝ)
        ≤ ⌈C⌉₊ * BranchingProcess.treeDist (Φ' (g (e.symm a))).1 (Φ' (g (e.symm b))).1 :=
      mul_le_mul_of_nonneg_right hCK hd
    have h3 : C ^ 2 ≤ (⌈C⌉₊ : ℝ) * ⌈C⌉₊ := by
      have := mul_le_mul hCK hCK hC hK0
      nlinarith
    have hcast : (BranchingProcess.treeDist a.1 b.1 : ℝ)
        ≤ ((⌈C⌉₊ * BranchingProcess.treeDist (Φ' (g (e.symm a))).1 (Φ' (g (e.symm b))).1
          + ⌈C⌉₊ * ⌈C⌉₊ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  · intro b
    set e' := Equiv.ofBijective Φ' hΦ'
    obtain ⟨x, hx⟩ := hg.dense (e'.symm b)
    refine ⟨Φ x, ?_⟩
    rw [wordGraphN_dist hT']
    rw [← hΦd'] at hx
    have hb : Φ' (e'.symm b) = b := e'.apply_symm_apply b
    rw [hb] at hx
    have hx' : e.symm (Φ x) = x := e.symm_apply_apply x
    rw [hx']
    exact_mod_cast hx.trans hCK

/-! ### The composition, over abstract sample isometries -/

namespace CascadeEnc

/-- **`thm:hairy-general`, the deterministic assembly over abstract sample isometries**:
two samples that are isometric to the assemblies of their shape fields over their reduced
skeletons, encoded into `𝔹` at depths `L` and `L'`, with an automorphism of `𝔹`
matching the encoded skeletons and the shape labels at comparability `K`, are
`⌈216 L L'² K²⌉`-quasi-isometric: the sample is read as its skeleton assembly, then as its
`𝔹`-assembly (an `L`-quasi-isometry), the matching glues the shapes (`8K²`), and the
second sample is read back through a quasi-inverse of its own reading (`3L'²`). -/
theorem sample_qi_of_bShape_matching_of_isometric {N' L L' : ℕ} {E : CascadeEnc N L}
    {E' : CascadeEnc N' L'} {σ : GWord N → GShape} {σ' : GWord N' → GShape}
    {c : GWord N → ℕ} {c' : GWord N' → ℕ} (hL : 1 ≤ L) (hL' : 1 ≤ L') {K : ℝ} (hK : 1 ≤ K)
    (π : Word → Bool ≃ Bool)
    (hπ : ∀ w : Word, E.InClosure (bnat w) ↔ E'.InClosure (bnat (autOf π w)))
    (hcomp : ∀ w : Word, MarkedQI K (gShapeSpace (E.bFamily σ (bnat w)))
      (gShapeSpace (E'.bFamily σ' (bnat (autOf π w)))))
    {Φ : SkelAssembly E.k σ → {v : GWord N // v ∈ sample c}} (hΦ : Function.Bijective Φ)
    (hΦd : ∀ x y, (BranchingProcess.treeDist (Φ x).1 (Φ y).1 : ℝ) = dist x y)
    {Φ' : SkelAssembly E'.k σ' → {v : GWord N' // v ∈ sample c'}} (hΦ' : Function.Bijective Φ')
    (hΦd' : ∀ x y, (BranchingProcess.treeDist (Φ' x).1 (Φ' y).1 : ℝ) = dist x y) :
    ∃ F : {v : GWord N // v ∈ sample c} → {v : GWord N' // v ∈ sample c'},
      BranchingProcess.IsQIWith ⌈216 * L * L' ^ 2 * K ^ 2⌉₊
        (wordGraphN (· ∈ sample c)) (wordGraphN (· ∈ sample c')) F := by
  obtain ⟨f, hf⟩ := qi_of_bShape_matching hK π hπ hcomp
  have h1 := skelToB_isQIMap (E := E) (σ := σ) hL
  have h2 := skelToB_isQIMap (E := E') (σ := σ') hL'
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLr' : (1 : ℝ) ≤ L' := by exact_mod_cast hL'
  have hK8 : (1 : ℝ) ≤ 8 * K ^ 2 := by nlinarith
  obtain ⟨h, hh⟩ := h2.exists_symm hLr'
  have hg := (h1.comp hLr hK8 hf).comp (by nlinarith) (by nlinarith) hh
  have hconst : 3 * (3 * (L : ℝ) * (8 * K ^ 2)) * (3 * (L' : ℝ) ^ 2)
      = 216 * L * L' ^ 2 * K ^ 2 := by ring
  rw [hconst] at hg
  exact isQIWith_of_skel_qi hΦ hΦd hΦ' hΦd' (by positivity) hg

end CascadeEnc

/-! ### Letterwise translations of addresses over `ℕ` -/

/-- **The address translation of a field of letter maps**, over `ℕ`: the word `a` is
read letter by letter, the letter `m` at the vertex already reached being sent to
`Λ v m`.  The translation preserves lengths and the prefix order, so it is an isometry as
soon as every `Λ v` is injective. -/
def transN (Λ : List ℕ → ℕ → ℕ) (a : List ℕ) : List ℕ :=
  a.foldl (fun v m ↦ v ++ [Λ v m]) []

section transN

variable {Λ : List ℕ → ℕ → ℕ}

@[simp] lemma transN_nil : transN Λ [] = [] := rfl

/-- The recursion of the translation: one further letter is read at the vertex reached. -/
lemma transN_concat (a : List ℕ) (m : ℕ) :
    transN Λ (a ++ [m]) = transN Λ a ++ [Λ (transN Λ a) m] := by
  simp [transN, List.foldl_append]

@[simp] lemma transN_length (a : List ℕ) : (transN Λ a).length = a.length := by
  induction a using List.reverseRecOn with
  | nil => rfl
  | append_singleton a m ih => simp [transN_concat, ih]

/-- The translation only appends, so it is monotone for the prefix order. -/
lemma transN_prefix {a a' : List ℕ} (h : a <+: a') : transN Λ a <+: transN Λ a' := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc, transN_concat]
      exact ih.trans (List.prefix_append _ _)

/-- **The translation is injective** when the letter maps are. -/
lemma transN_injective (hΛ : ∀ v, Function.Injective (Λ v)) : Function.Injective (transN Λ) := by
  intro a
  induction a using List.reverseRecOn with
  | nil =>
      intro a' h
      have hlen := congrArg List.length h
      simp only [transN_nil, transN_length, List.length_nil] at hlen
      exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | append_singleton a b ih =>
      intro a' h
      rcases List.eq_nil_or_concat a' with rfl | ⟨a₀, b₀, rfl⟩
      · have hlen := congrArg List.length h
        simp only [transN_length, List.length_append, List.length_singleton,
          List.length_nil] at hlen
        omega
      · rw [List.concat_eq_append] at h ⊢
        rw [transN_concat, transN_concat] at h
        have hlen : (transN Λ a).length = (transN Λ a₀).length := by
          have := congrArg List.length h
          simp only [List.length_append, List.length_singleton, transN_length] at this
          simp only [transN_length]
          omega
        obtain ⟨h1, h2⟩ := List.append_inj h hlen
        have ha : a = a₀ := ih h1
        subst ha
        have hb : Λ (transN Λ a) b = Λ (transN Λ a) b₀ := by simpa using h2
        rw [hΛ _ hb]

/-- A prefix of a translated word is the translation of the prefix. -/
lemma transN_take (a : List ℕ) (k : ℕ) : transN Λ (a.take k) = (transN Λ a).take k := by
  have hpre : transN Λ (a.take k) <+: transN Λ a := transN_prefix (List.take_prefix k a)
  rw [List.prefix_iff_eq_take.mp hpre, transN_length, List.length_take]
  rcases le_total k a.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_of_length_le (by simp),
      List.take_of_length_le (by simpa using h)]

/-- **The translation reflects the prefix order.** -/
lemma transN_prefix_iff (hΛ : ∀ v, Function.Injective (Λ v)) {a a' : List ℕ} :
    transN Λ a <+: transN Λ a' ↔ a <+: a' := by
  refine ⟨fun h ↦ ?_, transN_prefix⟩
  have heq : transN Λ a = transN Λ (a'.take a.length) := by
    rw [transN_take, List.prefix_iff_eq_take.mp h, transN_length]
  rw [transN_injective hΛ heq]
  exact List.take_prefix _ _

/-- The translation carries wedges to wedges. -/
lemma transN_wedgeN (hΛ : ∀ v, Function.Injective (Λ v)) (a a' : List ℕ) :
    wedgeN (transN Λ a) (transN Λ a') = transN Λ (wedgeN a a') := by
  have hle : transN Λ (wedgeN a a') <+: wedgeN (transN Λ a) (transN Λ a') :=
    prefix_wedgeN (transN_prefix (wedgeN_prefix_left a a'))
      (transN_prefix (wedgeN_prefix_right a a'))
  set z := wedgeN (transN Λ a) (transN Λ a') with hz
  have hza : z <+: transN Λ a := wedgeN_prefix_left _ _
  have hza' : z <+: transN Λ a' := wedgeN_prefix_right _ _
  have hzt : z = transN Λ (a.take z.length) := by
    rw [transN_take, ← List.prefix_iff_eq_take.mp hza]
  have h1 : a.take z.length <+: a := List.take_prefix _ _
  have h2 : a.take z.length <+: a' := by
    rw [← transN_prefix_iff hΛ, ← hzt]
    exact hza'
  have h3 : a.take z.length <+: wedgeN a a' := prefix_wedgeN h1 h2
  have hlen : z.length ≤ (transN Λ (wedgeN a a')).length := by
    have h4 := (transN_prefix (Λ := Λ) h3).length_le
    rw [← hzt] at h4
    exact h4
  exact (hle.eq_of_length (le_antisymm hle.length_le hlen)).symm

/-- **The translation is an isometry** of the address metric. -/
theorem transN_addrDist (hΛ : ∀ v, Function.Injective (Λ v)) (a a' : List ℕ) :
    addrDist (transN Λ a) (transN Λ a') = addrDist a a' := by
  rw [addrDist, addrDist, transN_wedgeN hΛ, transN_length, transN_length, transN_length]

end transN

/-! ### The letter map of a vertex of a sample -/

open BranchingProcess (childSet bushAt dyingAt)

/-- The dying children of the root of a field: the children that are not survivors. -/
noncomputable def dyingSet (d : GWord N → ℕ) : Finset (Fin N) := childSet N (d []) \ survivors d

/-- The letter of the `j`-th surviving child of the root, in letter order; past the
skeleton degree a junk letter outside the alphabet. -/
noncomputable def survLetter (d : GWord N → ℕ) (j : ℕ) : ℕ :=
  if h : j < (survivors d).card then (((survivors d).orderEmbOfFin rfl ⟨j, h⟩ : Fin N) : ℕ)
  else N + j

/-- The letter of the `m`-th dying child of the root, in letter order; past their
number a junk letter outside the alphabet. -/
noncomputable def dyingLetter (d : GWord N → ℕ) (m : ℕ) : ℕ :=
  if h : m < (dyingSet d).card then (((dyingSet d).orderEmbOfFin rfl ⟨m, h⟩ : Fin N) : ℕ)
  else N + m

/-- **The letter map of a vertex**: the child indices of the realisation of a shape, the
bushes first and the surviving children after them, sent to the letters of the ambient
tree naming those children. -/
noncomputable def letterMap (d : GWord N → ℕ) (m : ℕ) : ℕ :=
  if m < (dyingSet d).card then dyingLetter d m else survLetter d (m - (dyingSet d).card)

lemma survivors_card_add_dyingSet_card {d : GWord N → ℕ} (hd : d [] ≤ N) :
    (dyingSet d).card + skeletonDegree d = d [] := by
  rw [dyingSet, skeletonDegree, Finset.card_sdiff_of_subset (BranchingProcess.survivors_subset d),
    BranchingProcess.card_childSet hd]
  have := Finset.card_le_card (BranchingProcess.survivors_subset d)
  rw [BranchingProcess.card_childSet hd] at this
  omega

lemma survLetter_of_lt {d : GWord N → ℕ} {j : ℕ} (h : j < (survivors d).card) :
    survLetter d j = (((survivors d).orderEmbOfFin rfl ⟨j, h⟩ : Fin N) : ℕ) := by
  rw [survLetter, dif_pos h]

lemma survLetter_mem {d : GWord N → ℕ} {j : ℕ} (h : j < (survivors d).card) :
    ∃ i ∈ survivors d, survLetter d j = (i : ℕ) :=
  ⟨_, Finset.orderEmbOfFin_mem _ _ _, survLetter_of_lt h⟩

lemma survLetter_lt {d : GWord N → ℕ} {j : ℕ} (h : j < (survivors d).card) :
    survLetter d j < N := by
  rw [survLetter_of_lt h]
  exact Fin.isLt _

lemma survLetter_of_le {d : GWord N → ℕ} {j : ℕ} (h : (survivors d).card ≤ j) :
    survLetter d j = N + j := by
  rw [survLetter, dif_neg (by omega)]

lemma dyingLetter_of_lt {d : GWord N → ℕ} {m : ℕ} (h : m < (dyingSet d).card) :
    dyingLetter d m = (((dyingSet d).orderEmbOfFin rfl ⟨m, h⟩ : Fin N) : ℕ) := by
  rw [dyingLetter, dif_pos h]

lemma dyingLetter_mem {d : GWord N → ℕ} {m : ℕ} (h : m < (dyingSet d).card) :
    ∃ i ∈ dyingSet d, dyingLetter d m = (i : ℕ) :=
  ⟨_, Finset.orderEmbOfFin_mem _ _ _, dyingLetter_of_lt h⟩

lemma mem_dyingSet {d : GWord N → ℕ} {i : Fin N} :
    i ∈ dyingSet d ↔ (i : ℕ) < d [] ∧ i ∉ survivors d := by
  rw [dyingSet, Finset.mem_sdiff, BranchingProcess.mem_childSet]

/-- The letter map sends the child indices below the offspring count onto letters below
it, and nothing else there. -/
lemma letterMap_lt_iff {d : GWord N → ℕ} (hd : d [] ≤ N) (m : ℕ) :
    letterMap d m < d [] ↔ m < d [] := by
  have hsum := survivors_card_add_dyingSet_card hd
  rw [skeletonDegree] at hsum
  rw [letterMap]
  by_cases hm : m < (dyingSet d).card
  · rw [if_pos hm]
    obtain ⟨i, hi, hieq⟩ := dyingLetter_mem hm
    rw [hieq]
    exact iff_of_true (mem_dyingSet.mp hi).1 (by omega)
  · rw [if_neg hm]
    by_cases hj : m - (dyingSet d).card < (survivors d).card
    · obtain ⟨i, hi, hieq⟩ := survLetter_mem hj
      rw [hieq]
      exact iff_of_true (BranchingProcess.mem_survivors.mp hi).1 (by omega)
    · rw [survLetter_of_le (by omega)]
      exact iff_of_false (by omega) (by omega)

/-- The letter map is injective: distinct bushes get distinct letters, distinct surviving
children likewise, a bush and a surviving child never share a letter, and the junk
letters lie outside the alphabet. -/
lemma letterMap_injective (d : GWord N → ℕ) : Function.Injective (letterMap d) := by
  intro m m' h
  simp only [letterMap] at h
  have hdy : ∀ {a b : ℕ} (ha : a < (dyingSet d).card) (hb : b < (dyingSet d).card),
      dyingLetter d a = dyingLetter d b → a = b := by
    intro a b ha hb hab
    rw [dyingLetter_of_lt ha, dyingLetter_of_lt hb] at hab
    have := ((dyingSet d).orderEmbOfFin rfl).injective (Fin.ext hab)
    simpa using this
  have hsv : ∀ {a b : ℕ}, survLetter d a = survLetter d b → a = b := by
    intro a b hab
    by_cases ha : a < (survivors d).card
    · by_cases hb : b < (survivors d).card
      · rw [survLetter_of_lt ha, survLetter_of_lt hb] at hab
        have := ((survivors d).orderEmbOfFin rfl).injective (Fin.ext hab)
        simpa using this
      · rw [survLetter_of_lt ha, survLetter_of_le (by omega)] at hab
        have := Fin.isLt ((survivors d).orderEmbOfFin rfl ⟨a, ha⟩)
        omega
    · by_cases hb : b < (survivors d).card
      · rw [survLetter_of_le (by omega), survLetter_of_lt hb] at hab
        have := Fin.isLt ((survivors d).orderEmbOfFin rfl ⟨b, hb⟩)
        omega
      · rw [survLetter_of_le (by omega), survLetter_of_le (by omega)] at hab
        omega
  have hmix : ∀ {a b : ℕ}, a < (dyingSet d).card → dyingLetter d a ≠ survLetter d b := by
    intro a b ha hab
    obtain ⟨i, hi, hieq⟩ := dyingLetter_mem ha
    by_cases hb : b < (survivors d).card
    · obtain ⟨i', hi', hieq'⟩ := survLetter_mem hb
      rw [hieq, hieq'] at hab
      have : i = i' := Fin.ext hab
      subst this
      exact (mem_dyingSet.mp hi).2 hi'
    · rw [hieq, survLetter_of_le (by omega)] at hab
      have := i.isLt
      omega
  by_cases hm : m < (dyingSet d).card <;> by_cases hm' : m' < (dyingSet d).card
  · rw [if_pos hm, if_pos hm'] at h
    exact hdy hm hm' h
  · rw [if_pos hm, if_neg hm'] at h
    exact absurd h (hmix hm)
  · rw [if_neg hm, if_pos hm'] at h
    exact absurd h.symm (hmix hm')
  · rw [if_neg hm, if_neg hm'] at h
    have := hsv h
    omega

/-- Every element of a finite set of letters is enumerated by its rank. -/
lemma exists_orderEmbOfFin_eq {S : Finset (Fin N)} {i : Fin N} (hi : i ∈ S) :
    ∃ m, ∃ h : m < S.card, S.orderEmbOfFin rfl ⟨m, h⟩ = i := by
  have hmem : i ∈ Set.range (S.orderEmbOfFin (rfl : S.card = S.card)) := by
    rw [Finset.range_orderEmbOfFin]
    exact hi
  obtain ⟨⟨m, hm⟩, hmeq⟩ := hmem
  exact ⟨m, hm, hmeq⟩

/-- The letter map is onto the children: every child letter is the image of a child
index below the offspring count. -/
lemma letterMap_surj {d : GWord N → ℕ} (hd : d [] ≤ N) {j : ℕ} (hj : j < d []) :
    ∃ m, m < d [] ∧ letterMap d m = j := by
  have hsum := survivors_card_add_dyingSet_card hd
  set i : Fin N := ⟨j, by omega⟩ with hi
  by_cases hs : i ∈ survivors d
  · obtain ⟨m, hm, hmeq⟩ := exists_orderEmbOfFin_eq hs
    refine ⟨(dyingSet d).card + m, by rw [skeletonDegree] at hsum; omega, ?_⟩
    rw [letterMap, if_neg (by omega), Nat.add_sub_cancel_left, survLetter_of_lt hm, hmeq]
  · have hdy : i ∈ dyingSet d := mem_dyingSet.mpr ⟨hj, hs⟩
    obtain ⟨m, hm, hmeq⟩ := exists_orderEmbOfFin_eq hdy
    exact ⟨m, by omega, by rw [letterMap, if_pos hm, dyingLetter_of_lt hm, hmeq]⟩

/-- In a dying subtree every child is a dying child and the letter map is the identity
on the children. -/
lemma letterMap_of_not_survives {d : GWord N → ℕ} (hd : d [] ≤ N) (hfin : ¬ Survives d) {m : ℕ}
    (hm : m < d []) : letterMap d m = m := by
  have hemp : survivors d = ∅ := BranchingProcess.not_survives_iff_survivors_eq_empty.mp hfin
  have hdy : dyingSet d = childSet N (d []) := by rw [dyingSet, hemp, Finset.sdiff_empty]
  have hcard : (dyingSet d).card = d [] := by rw [hdy, BranchingProcess.card_childSet hd]
  have hm' : m < (dyingSet d).card := by omega
  rw [letterMap, if_pos hm', dyingLetter_of_lt hm']
  have hf : (fun x : Fin (dyingSet d).card ↦ (⟨(x : ℕ), by omega⟩ : Fin N))
      = (dyingSet d).orderEmbOfFin rfl := by
    refine Finset.orderEmbOfFin_unique rfl (fun x ↦ ?_) (fun x y hxy ↦ ?_)
    · rw [mem_dyingSet, hemp]
      have := x.isLt
      exact ⟨by simp only; omega, Finset.notMem_empty _⟩
    · exact hxy
  have := congrFun hf ⟨m, hm'⟩
  simp only at this
  rw [← this]

/-! ### The addresses of a realisation at general arity -/

open RTree (IsAddr)
open GShape (realiseAux)

/-- The address of the `i`-th neck vertex of the realisation of a bush-list: one letter
per neck vertex passed, naming the child past its bushes. -/
def neckAddr (L : List (List RTree)) (i : ℕ) : List ℕ := (L.take i).map List.length

@[simp] lemma neckAddr_zero (L : List (List RTree)) : neckAddr L 0 = [] := rfl

lemma neckAddr_cons (β : List RTree) (M : List (List RTree)) (i : ℕ) :
    neckAddr (β :: M) (i + 1) = β.length :: neckAddr M i := by
  simp [neckAddr]

lemma neckAddr_length {L : List (List RTree)} {i : ℕ} (hi : i ≤ L.length) :
    (neckAddr L i).length = i := by
  rw [neckAddr, List.length_map, List.length_take, min_eq_left hi]

/-- One further neck vertex extends the neck address by the number of bushes. -/
lemma neckAddr_succ {L : List (List RTree)} {i : ℕ} (hi : i < L.length) :
    neckAddr L (i + 1) = neckAddr L i ++ [L[i].length] := by
  rw [neckAddr, neckAddr, List.take_add_one, List.getElem?_eq_getElem hi, List.map_append]
  rfl

/-- The neck addresses are nested. -/
lemma neckAddr_prefix (L : List (List RTree)) {i j : ℕ} (hij : i ≤ j) :
    neckAddr L i <+: neckAddr L j := by
  rw [neckAddr, neckAddr]
  exact (List.take_prefix_take_left hij).map _

/-- The exit is the last neck address. -/
lemma gExitAddr_eq_neckAddr : ∀ L : List (List RTree), gExitAddr L = neckAddr L (L.length - 1)
  | [] => rfl
  | [_] => rfl
  | β :: r :: rest => by
      rw [gExitAddr_cons₂, gExitAddr_eq_neckAddr (r :: rest), List.length_cons,
        Nat.add_sub_cancel, List.length_cons, Nat.add_sub_cancel, ← neckAddr_cons]
      rfl

/-- **The children of a neck vertex**: its bushes, and the next neck vertex when there
is one. -/
lemma isAddr_realiseAux_neck_concat : ∀ (L : List (List RTree)) (i : ℕ) (hi : i < L.length)
    (m : ℕ), IsAddr (realiseAux L) (neckAddr L i ++ [m])
      ↔ (m < L[i].length ∨ (m = L[i].length ∧ i + 1 < L.length))
  | [], i, hi, _ => by simp at hi
  | [β], 0, _, m => by
      rw [neckAddr_zero, List.nil_append, show realiseAux [β] = .node β from rfl,
        RTree.isAddr_cons]
      simp
  | [β], i + 1, hi, _ => by simp at hi
  | β :: r :: rest, 0, _, m => by
      rw [neckAddr_zero, List.nil_append,
        show realiseAux (β :: r :: rest) = .node (β ++ [realiseAux (r :: rest)]) from rfl,
        RTree.isAddr_cons]
      simp only [List.length_append, List.getElem_cons_zero, List.length_cons, List.length_nil]
      constructor
      · rintro ⟨h, -⟩
        omega
      · intro h
        refine ⟨by omega, ?_⟩
        rcases h with h | ⟨h, -⟩
        · rw [List.getElem_append_left h]
          exact RTree.isAddr_nil _
        · subst h
          rw [List.getElem_append_right le_rfl]
          simp
  | β :: r :: rest, i + 1, hi, m => by
      rw [neckAddr_cons, List.cons_append,
        show realiseAux (β :: r :: rest) = .node (β ++ [realiseAux (r :: rest)]) from rfl,
        isAddr_append_last_eq, isAddr_realiseAux_neck_concat (r :: rest) i (by simpa using hi)]
      simp

/-- **The bush of a neck vertex**: the addresses below the `m`-th bush index of the `i`-th
neck vertex are the addresses of that bush. -/
lemma isAddr_realiseAux_bush : ∀ (L : List (List RTree)) (i : ℕ) (hi : i < L.length) (m : ℕ)
    (hm : m < L[i].length) (z : List ℕ),
    IsAddr (realiseAux L) (neckAddr L i ++ m :: z) ↔ IsAddr L[i][m] z
  | [], i, hi, _, _, _ => by simp at hi
  | [β], 0, _, m, hm, z => by
      rw [neckAddr_zero, List.nil_append, show realiseAux [β] = .node β from rfl,
        RTree.isAddr_cons]
      simp only [List.getElem_cons_zero] at hm ⊢
      exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hm, h⟩⟩
  | [β], i + 1, hi, _, _, _ => by simp at hi
  | β :: r :: rest, 0, _, m, hm, z => by
      rw [neckAddr_zero, List.nil_append,
        show realiseAux (β :: r :: rest) = .node (β ++ [realiseAux (r :: rest)]) from rfl]
      simp only [List.getElem_cons_zero] at hm ⊢
      rw [isAddr_append_last_lt hm, RTree.isAddr_cons]
      exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hm, h⟩⟩
  | β :: r :: rest, i + 1, hi, m, hm, z => by
      rw [neckAddr_cons, List.cons_append,
        show realiseAux (β :: r :: rest) = .node (β ++ [realiseAux (r :: rest)]) from rfl,
        isAddr_append_last_eq]
      exact isAddr_realiseAux_bush (r :: rest) i (by simpa using hi) m (by simpa using hm) z

/-- The neck vertices are addresses of the realisation. -/
lemma isAddr_realiseAux_neckAddr (L : List (List RTree)) {i : ℕ} (hi : i < L.length) :
    IsAddr (realiseAux L) (neckAddr L i) :=
  RTree.isAddr_of_prefix (isAddr_realiseAux_gExitAddr L)
    (by rw [gExitAddr_eq_neckAddr]; exact neckAddr_prefix L (by omega))

/-- **The addresses of a realisation**: every vertex is a neck vertex or a vertex of a
bush of a neck vertex. -/
lemma isAddr_realiseAux_cases : ∀ (L : List (List RTree)), L ≠ [] → ∀ {p : List ℕ},
    IsAddr (realiseAux L) p →
      (∃ i, i < L.length ∧ p = neckAddr L i) ∨
      (∃ i, ∃ hi : i < L.length, ∃ m, ∃ hm : m < L[i].length, ∃ z,
        IsAddr L[i][m] z ∧ p = neckAddr L i ++ m :: z)
  | [], h, _, _ => absurd rfl h
  | [β], _, p, hp => by
      cases p with
      | nil => exact Or.inl ⟨0, by simp, rfl⟩
      | cons m z =>
          rw [show realiseAux [β] = .node β from rfl, RTree.isAddr_cons] at hp
          obtain ⟨hm, hz⟩ := hp
          exact Or.inr ⟨0, by simp, m, by simpa using hm, z, by simpa using hz, rfl⟩
  | β :: r :: rest, _, p, hp => by
      cases p with
      | nil => exact Or.inl ⟨0, by simp, rfl⟩
      | cons m z =>
          rw [show realiseAux (β :: r :: rest) = .node (β ++ [realiseAux (r :: rest)]) from rfl]
            at hp
          by_cases hm : m < β.length
          · rw [isAddr_append_last_lt hm, RTree.isAddr_cons] at hp
            obtain ⟨_, hz⟩ := hp
            exact Or.inr ⟨0, by simp, m, by simpa using hm, z, by simpa using hz, rfl⟩
          · have hlen : m < (β ++ [realiseAux (r :: rest)]).length := by
              rw [RTree.isAddr_cons] at hp
              exact hp.1
            have hmeq : m = β.length := by
              simp only [List.length_append, List.length_singleton] at hlen
              omega
            subst hmeq
            rw [isAddr_append_last_eq] at hp
            rcases isAddr_realiseAux_cases (r :: rest) (by simp) hp with
              ⟨i, hi, rfl⟩ | ⟨i, hi, m', hm', z', hz', rfl⟩
            · exact Or.inl ⟨i + 1, by simpa using hi, (neckAddr_cons _ _ _).symm⟩
            · refine Or.inr ⟨i + 1, by simpa using hi, m', by simpa using hm', z',
                by simpa using hz', ?_⟩
              rw [neckAddr_cons]
              rfl

/-! ### The skeleton of a sample in the ambient tree -/

/-- **The deterministic hypotheses of `thm:hairy-general`** at general arity: the
offspring counts lie within the alphabet, the sample survives, and every neck ray of the
skeleton meets a split, which is the event `Ω₀` of `thm:chains` read for the skeleton. -/
structure IsGHairySample (c : GWord N → ℕ) : Prop where
  /-- The offspring counts lie within the alphabet. -/
  offspring : ∀ v, c v ≤ N
  /-- The sample is infinite. -/
  survives : Survives c
  /-- Every neck ray of the skeleton meets a split. -/
  splits : ∀ v : GWord N, Survives (ambSub c v) →
    ∃ n, 2 ≤ skeletonDegree (neckIter (ambSub c v) n)

/-- The descent, one step at the bottom. -/
lemma neckIter_succ' (d : GWord N → ℕ) : ∀ n, neckIter d (n + 1) = bushAt (neckIter d n) 0 := by
  intro n
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [neckIter_succ, ih, ← neckIter_succ]

/-- The descent of a surviving field stays in the skeleton. -/
lemma survives_neckIter {d : GWord N → ℕ} (hd : Survives d) : ∀ n, Survives (neckIter d n)
  | 0 => hd
  | n + 1 => by
      rw [neckIter_succ']
      exact BranchingProcess.survives_bushAt (Nat.pos_of_ne_zero
        (BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp (survives_neckIter hd n)))

lemma unval_singleton {ℓ : ℕ} (h : ℓ < N) : unval N [ℓ] = [⟨ℓ, h⟩] := by
  simp [unval, h]

lemma ambSub_root (e : GWord N → ℕ) (v : GWord N) : ambSub e v [] = e v := by
  rw [ambSub_apply, List.append_nil]

/-- The `j`-th surviving subtree is the subtree at the letter of the `j`-th surviving
child. -/
lemma bushAt_eq_ambSub {e : GWord N → ℕ} {j : ℕ} (hj : j < skeletonDegree e) :
    bushAt e j = ambSub e (unval N [survLetter e j]) := by
  have hj' : j < (survivors e).card := hj
  rw [BranchingProcess.bushAt_of_lt hj', survLetter_of_lt hj', unval_singleton (Fin.isLt _)]
  rfl

/-- The `m`-th dying subtree is the subtree at the letter of the `m`-th dying child. -/
lemma dyingAt_eq_ambSub {e : GWord N → ℕ} {m : ℕ} (hm : m < (dyingSet e).card) :
    dyingAt e m = ambSub e (unval N [dyingLetter e m]) := by
  rw [dyingLetter_of_lt hm, unval_singleton (Fin.isLt _)]
  show BranchingProcess.bushOf (dyingSet e) m e = _
  rw [BranchingProcess.bushOf, dif_pos hm]
  rfl

/-- A dying subtree does not survive. -/
lemma not_survives_dyingAt {e : GWord N → ℕ} {m : ℕ} (hm : m < (dyingSet e).card) :
    ¬ Survives (dyingAt e m) := by
  rw [dyingAt_eq_ambSub hm]
  obtain ⟨i, hi, hieq⟩ := dyingLetter_mem hm
  rw [hieq, unval_singleton i.isLt]
  intro hs
  exact (mem_dyingSet.mp hi).2 (BranchingProcess.mem_survivors.mpr ⟨(mem_dyingSet.mp hi).1, hs⟩)

/-- **The neck ray of the root in the ambient tree**: the path of the descent, one
surviving child after the other. -/
noncomputable def neckPath (d : GWord N → ℕ) : ℕ → GWord N
  | 0 => []
  | n + 1 => neckPath d n ++ unval N [survLetter (ambSub d (neckPath d n)) 0]

@[simp] lemma neckPath_zero (d : GWord N → ℕ) : neckPath d 0 = [] := rfl

/-- The descent is the field along the neck ray. -/
lemma neckIter_eq_ambSub_neckPath {d : GWord N → ℕ} (hd : Survives d) :
    ∀ n, neckIter d n = ambSub d (neckPath d n)
  | 0 => by simp
  | n + 1 => by
      have ih := neckIter_eq_ambSub_neckPath hd n
      have hs := survives_neckIter hd n
      rw [neckIter_succ', bushAt_eq_ambSub (j := 0) (Nat.pos_of_ne_zero
        (BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp hs)), ih, ambSub_ambSub]
      rfl

lemma skeletonDegree_neckIter_pos {d : GWord N → ℕ} (hd : Survives d) (n : ℕ) :
    0 < skeletonDegree (neckIter d n) :=
  Nat.pos_of_ne_zero
    (BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp (survives_neckIter hd n))

/-- The neck ray read over `ℕ`, one step. -/
lemma vals_neckPath_succ {d : GWord N → ℕ} (hd : Survives d) (n : ℕ) :
    vals (neckPath d (n + 1)) = vals (neckPath d n) ++ [survLetter (neckIter d n) 0] := by
  have hlt : survLetter (neckIter d n) 0 < N := survLetter_lt (skeletonDegree_neckIter_pos hd n)
  rw [neckPath, ← neckIter_eq_ambSub_neckPath hd n, unval_singleton hlt, vals_append]
  rfl

lemma neckPath_length {d : GWord N → ℕ} (hd : Survives d) : ∀ n, (neckPath d n).length = n
  | 0 => rfl
  | n + 1 => by
      have := congrArg List.length (vals_neckPath_succ hd n)
      simp only [vals_length, List.length_append, List.length_singleton] at this
      rw [this, neckPath_length hd n]

/-- The neck ray of a vertex of the sample stays in the sample. -/
lemma neckPath_mem_sample {c : GWord N → ℕ} {y : GWord N} (hy : y ∈ sample c)
    (hs : Survives (ambSub c y)) : ∀ n, y ++ neckPath (ambSub c y) n ∈ sample c
  | 0 => by simpa using hy
  | n + 1 => by
      have ih := neckPath_mem_sample hy hs n
      have hpos := skeletonDegree_neckIter_pos hs n
      have hlt : survLetter (neckIter (ambSub c y) n) 0 < N := survLetter_lt hpos
      rw [neckPath, ← neckIter_eq_ambSub_neckPath hs n, unval_singleton hlt, ← List.append_assoc,
        BranchingProcess.mem_sample_append_singleton]
      refine ⟨ih, ?_⟩
      obtain ⟨i, hi, hieq⟩ := survLetter_mem (d := neckIter (ambSub c y) n) hpos
      have h1 := (BranchingProcess.mem_survivors.mp hi).1
      rw [neckIter_eq_ambSub_neckPath hs n, ambSub_root, ambSub_apply] at h1
      simp only [hieq]
      exact h1

/-- Below its split, every vertex of a neck ray has one surviving child. -/
lemma skeletonDegree_neckIter_eq_one {d : GWord N → ℕ} (hd : Survives d) {i : ℕ}
    (hi : i < gSplitDepth d) : skeletonDegree (neckIter d i) = 1 := by
  have hnot : ¬ 2 ≤ skeletonDegree (neckIter d i) := fun hmem ↦
    absurd (Nat.sInf_le (show i ∈ {n | 2 ≤ skeletonDegree (neckIter d n)} from hmem))
      (not_le.mpr hi)
  have := skeletonDegree_neckIter_pos hd i
  omega

/-- **`thm:chains` at general arity**: the neck ray of a skeleton vertex ends at a split. -/
lemma two_le_gArity_of_splits {d : GWord N → ℕ}
    (hne : ∃ n, 2 ≤ skeletonDegree (neckIter d n)) : 2 ≤ gArity d :=
  Nat.sInf_mem (s := {n | 2 ≤ skeletonDegree (neckIter d n)}) hne

/-- The split ending the chain of the root, in the ambient tree. -/
noncomputable def splitPath (d : GWord N → ℕ) : GWord N := neckPath d (gSplitDepth d)

/-- **The entry vertex of a copy** (**`thm:shape-iid`** at general arity): the chain of
the root is followed to its split, and each letter of the address picks a surviving child
of the split reached. -/
noncomputable def gEntryV : (GWord N → ℕ) → GWord N → GWord N
  | _, [] => []
  | d, i :: u =>
      (splitPath d ++ unval N [survLetter (gSplitField d) i]) ++ gEntryV (gSplitBush d i) u

@[simp] lemma gEntryV_nil (d : GWord N → ℕ) : gEntryV d [] = [] := rfl

lemma gEntryV_cons (d : GWord N → ℕ) (i : Fin N) (u : GWord N) :
    gEntryV d (i :: u)
      = (splitPath d ++ unval N [survLetter (gSplitField d) i]) ++ gEntryV (gSplitBush d i) u :=
  rfl

/-- The recursion of the entry map at the last letter: the copy `uj` starts at the
`j`-th surviving child of the split ending the chain of `u`. -/
lemma gEntryV_concat (d : GWord N → ℕ) (u : GWord N) (j : Fin N) :
    gEntryV d (u ++ [j])
      = gEntryV d u ++ (splitPath (redSub d u)
          ++ unval N [survLetter (gSplitField (redSub d u)) j]) := by
  induction u generalizing d with
  | nil => simp [gEntryV_cons]
  | cons i u ih =>
      rw [List.cons_append, gEntryV_cons, ih, gEntryV_cons, redSub_cons]
      simp only [List.append_assoc]

/-- The skeleton of the arity field, one letter down. -/
lemma mem_sample_gArityAt_cons {d : GWord N → ℕ} {i : Fin N} {u : GWord N} :
    i :: u ∈ sample (gArityAt d) ↔ (i : ℕ) < gArity d ∧ u ∈ sample (gArityAt (gSplitBush d i)) := by
  rw [mem_sample_cons_ambSub, gArityAt_nil]
  have : ambSub (gArityAt d) [i] = gArityAt (gSplitBush d i) := by
    funext w
    rw [ambSub_apply, List.singleton_append, gArityAt_cons]
  rw [this]

/-- **The copies are the subtrees at the entry vertices**: along the reduced skeleton
the subfield of a copy is the ambient subfield at its entry vertex, and it survives. -/
lemma redSub_eq_ambSub_gEntryV {c : GWord N → ℕ} (hc : IsGHairySample c) :
    ∀ (u y : GWord N), Survives (ambSub c y) → u ∈ sample (gArityAt (ambSub c y)) →
      redSub (ambSub c y) u = ambSub c (y ++ gEntryV (ambSub c y) u)
        ∧ Survives (redSub (ambSub c y) u)
  | [], y, hs, _ => by simpa using hs
  | i :: u, y, hs, hu => by
      obtain ⟨hi, hu'⟩ := mem_sample_gArityAt_cons.mp hu
      have hbush : gSplitBush (ambSub c y) i
          = ambSub c (y ++ (splitPath (ambSub c y)
              ++ unval N [survLetter (gSplitField (ambSub c y)) i])) := by
        rw [gSplitBush, bushAt_eq_ambSub hi, gSplitField, neckIter_eq_ambSub_neckPath hs,
          ambSub_ambSub, ambSub_ambSub, splitPath]
      have hsurv' : Survives (gSplitBush (ambSub c y) i) := BranchingProcess.survives_bushAt hi
      rw [hbush] at hsurv' hu'
      obtain ⟨ih1, ih2⟩ := redSub_eq_ambSub_gEntryV hc u _ hsurv' hu'
      rw [ih1] at ih2
      rw [redSub_cons, hbush, gEntryV_cons, hbush, ih1]
      simp only [List.append_assoc, true_and]
      simp only [List.append_assoc] at ih2
      exact ih2

/-- The subfield of a copy, at the root. -/
lemma redSub_eq_ambSub_gEntryV' {c : GWord N → ℕ} (hc : IsGHairySample c) {u : GWord N}
    (hu : u ∈ sample (gArityAt c)) :
    redSub c u = ambSub c (gEntryV c u) ∧ Survives (redSub c u) := by
  have h := redSub_eq_ambSub_gEntryV hc u [] (by simpa using hc.survives) (by simpa using hu)
  simpa using h

/-- The entry vertices lie in the sample. -/
lemma gEntryV_mem_sample {c : GWord N → ℕ} (hc : IsGHairySample c) :
    ∀ (u y : GWord N), y ∈ sample c → Survives (ambSub c y) → u ∈ sample (gArityAt (ambSub c y)) →
      y ++ gEntryV (ambSub c y) u ∈ sample c
  | [], y, hy, _, _ => by simpa using hy
  | i :: u, y, hy, hs, hu => by
      obtain ⟨hi, hu'⟩ := mem_sample_gArityAt_cons.mp hu
      have hbush : gSplitBush (ambSub c y) i
          = ambSub c (y ++ (splitPath (ambSub c y)
              ++ unval N [survLetter (gSplitField (ambSub c y)) i])) := by
        rw [gSplitBush, bushAt_eq_ambSub hi, gSplitField, neckIter_eq_ambSub_neckPath hs,
          ambSub_ambSub, ambSub_ambSub, splitPath]
      have hsurv' : Survives (gSplitBush (ambSub c y) i) := BranchingProcess.survives_bushAt hi
      rw [hbush] at hsurv' hu'
      have hmem : y ++ (splitPath (ambSub c y)
          ++ unval N [survLetter (gSplitField (ambSub c y)) i]) ∈ sample c := by
        have hsp := neckPath_mem_sample hy hs (gSplitDepth (ambSub c y))
        have hlt : survLetter (gSplitField (ambSub c y)) i < N := survLetter_lt hi
        rw [← List.append_assoc, unval_singleton hlt,
          BranchingProcess.mem_sample_append_singleton]
        refine ⟨hsp, ?_⟩
        obtain ⟨i', hi', hieq⟩ := survLetter_mem (d := gSplitField (ambSub c y)) hi
        have h1 := (BranchingProcess.mem_survivors.mp hi').1
        rw [gSplitField, neckIter_eq_ambSub_neckPath hs, ambSub_root, ambSub_apply] at h1
        simp only [hieq]
        exact h1
      have ih := gEntryV_mem_sample hc u _ hmem hsurv' hu'
      rw [gEntryV_cons, hbush]
      simp only [List.append_assoc] at ih ⊢
      exact ih

/-! ### The children of a vertex of the skeleton assembly -/

namespace SkelAssembly

variable {k : GWord N → ℕ} {σ : GWord N → GShape}

/-- The address of a vertex of the skeleton assembly in the ambient tree of the assembly. -/
def code (x : SkelAssembly k σ) : List ℕ := GAssembly.code (toG x)

lemma code_eq (x : SkelAssembly k σ) :
    x.code = gCopyAddr (liftN N σ) (vals x.copy) ++ x.vert.1 := rfl

lemma code_injective : Function.Injective (code (k := k) (σ := σ)) :=
  fun _ _ h ↦ toG_injective (GAssembly.code_injective h)

/-- A word over `ℕ` ending in a letter of the alphabet is read from an ambient word. -/
lemma vals_eq_append_singleton_iff {v : GWord N} {w : List ℕ} {m : ℕ} :
    vals v = w ++ [m] ↔ ∃ (v' : GWord N) (j : Fin N), v = v' ++ [j] ∧ vals v' = w ∧ (j : ℕ) = m := by
  constructor
  · intro h
    rcases List.eq_nil_or_concat v with rfl | ⟨v', j, rfl⟩
    · have := congrArg List.length h
      simp at this
    · rw [List.concat_eq_append, vals_append, vals_cons, vals_nil] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by
        have := congrArg List.length h
        simp only [List.length_append, List.length_singleton] at this
        omega)
      exact ⟨v', j, List.concat_eq_append, h1, by simpa using h2⟩
  · rintro ⟨v', j, rfl, rfl, rfl⟩
    simp

/-- **The children of a vertex of the skeleton assembly**: inside a copy they are the
children of the realisation, and the exit of a copy is joined to the entries of the
copies below it, one per letter below the arity. -/
lemma exists_code_concat_iff (x : SkelAssembly k σ) (m : ℕ) :
    (∃ y : SkelAssembly k σ, y.code = x.code ++ [m])
      ↔ ((x.vert.1 = (σ x.copy).exitAddr
            ∧ ∃ j : Fin N, (j : ℕ) < k x.copy ∧ m = (σ x.copy).bouquet.length + j)
          ∨ IsAddr (σ x.copy).realise (x.vert.1 ++ [m])) := by
  obtain ⟨u, hu, p⟩ := x
  dsimp only
  constructor
  · rintro ⟨⟨v, hv, q⟩, hy⟩
    have hd1 : addrDist (GAssembly.code (toG ⟨u, hu, p⟩)) (GAssembly.code (toG ⟨v, hv, q⟩)) = 1 := by
      change addrDist (code ⟨u, hu, p⟩) (code ⟨v, hv, q⟩) = 1
      rw [hy, addrDist_append_right, List.length_singleton]
    have hadj : GAssembly.Adj (toG ⟨u, hu, p⟩) (toG ⟨v, hv, q⟩) := by
      refine (GAssembly.dist_eq_one_iff_adj _ _).mp ?_
      rw [GAssembly.dist_code, hd1]
      norm_num
    have hlen : (code ⟨v, hv, q⟩).length = (code ⟨u, hu, p⟩).length + 1 := by
      rw [hy]; simp
    simp only [code_eq, List.length_append] at hlen
    rcases hadj with ⟨hcopy, hor⟩ | ⟨j', hj', hglue, hnil⟩ | ⟨j', hj', hglue, hnil⟩
    · simp only [toG_copy] at hcopy
      have huv : u = v := vals_injective hcopy
      subst huv
      rcases hor with ⟨b, hb⟩ | ⟨b, hb⟩
      · simp only [toG_vert_val] at hb
        have hcode : code ⟨u, hu, q⟩ = code ⟨u, hu, p⟩ ++ [b] := by
          simp only [code_eq, hb, List.append_assoc]
        rw [hcode] at hy
        have hbm : b = m := by simpa using List.append_cancel_left hy
        subst hbm
        exact Or.inr (hb ▸ RTree.mem_addrList_iff.mp q.2)
      · exfalso
        simp only [toG_vert_val] at hb
        rw [hb] at hlen
        simp only [List.length_append, List.length_singleton] at hlen
        omega
    · simp only [toG_copy, toG_vert_val] at hj' hglue hnil
      obtain ⟨v', j, rfl, hv', hjm⟩ := vals_eq_append_singleton_iff.mp hj'
      have huv : u = v' := vals_injective hv'.symm
      subst huv
      have hj : (j : ℕ) < k u := (BranchingProcess.mem_sample_append_singleton.mp hv).2
      refine Or.inl ⟨by rw [hglue, liftN_vals], j, hj, ?_⟩
      simp only [code_eq, hnil, List.append_nil, vals_append, vals_cons, vals_nil,
        gCopyAddr_concat, liftN_vals, hglue, List.append_assoc] at hy
      have := List.append_cancel_left hy
      simpa using this.symm
    · exfalso
      simp only [toG_copy, toG_vert_val] at hj' hglue hnil
      obtain ⟨u', j, rfl, hu', hjm⟩ := vals_eq_append_singleton_iff.mp hj'
      have huv : v = u' := vals_injective hu'.symm
      subst huv
      simp only [vals_append, vals_cons, vals_nil, gCopyAddr_concat, List.length_append,
        hglue, hnil, List.length_singleton, List.length_nil] at hlen
      omega
  · rintro (⟨hexit, j, hj, rfl⟩ | hchild)
    · refine ⟨⟨u ++ [j], BranchingProcess.mem_sample_append_singleton.mpr ⟨hu, hj⟩,
        (gShapeSpace (σ (u ++ [j]))).entry⟩, ?_⟩
      simp only [code_eq, GAssembly.entry_gShapeSpace_val, List.append_nil, vals_append,
        vals_cons, vals_nil, gCopyAddr_concat, liftN_vals, hexit, List.append_assoc]
    · exact ⟨⟨u, hu, ⟨p.1 ++ [m], RTree.mem_addrList_iff.mpr hchild⟩⟩,
        by simp only [code_eq, List.append_assoc]⟩

end SkelAssembly

/-! ### The dictionary between the copies and the sample -/

/-- **The letter map of a sample**, read at words over `ℕ`: the letter map of the
subfield at the vertex the word names. -/
noncomputable def sampleLetterN (c : GWord N → ℕ) (w : List ℕ) : ℕ → ℕ :=
  letterMap (ambSub c (unval N w))

lemma sampleLetterN_injective (c : GWord N → ℕ) (w : List ℕ) :
    Function.Injective (sampleLetterN c w) :=
  letterMap_injective _

lemma sampleLetterN_vals (c : GWord N → ℕ) (y : GWord N) :
    sampleLetterN c (vals y) = letterMap (ambSub c y) := by
  rw [sampleLetterN, unval_vals]

/-- **The sample read from the skeleton assembly**: the address translation along the
letter map of the sample. -/
noncomputable def transSampleN (c : GWord N → ℕ) : List ℕ → List ℕ := transN (sampleLetterN c)

lemma transSampleN_injective (c : GWord N → ℕ) : Function.Injective (transSampleN c) :=
  transN_injective (sampleLetterN_injective c)

lemma transSampleN_concat (c : GWord N → ℕ) (a : List ℕ) (m : ℕ) :
    transSampleN c (a ++ [m]) = transSampleN c a ++ [sampleLetterN c (transSampleN c a) m] :=
  transN_concat a m

@[simp] lemma transSampleN_nil (c : GWord N → ℕ) : transSampleN c [] = [] := rfl

/-- The bush lists of the shape at the root, read off the descent. -/
lemma decs_gShapeRoot_length (d : GWord N → ℕ) :
    (gShapeRoot d).decs.length = gSplitDepth d + 1 :=
  GShape.decs_length _

lemma decs_gShapeRoot_ne_nil (d : GWord N → ℕ) : (gShapeRoot d).decs ≠ [] :=
  GShape.decs_ne_nil _

lemma decs_gShapeRoot_getElem (d : GWord N → ℕ) {i : ℕ} (hi : i < (gShapeRoot d).decs.length) :
    (gShapeRoot d).decs[i] = gDecList (neckIter d i) := by
  simp only [decs_gShapeRoot, List.getElem_ofFn]

lemma gShapeRoot_exitAddr (d : GWord N → ℕ) :
    (gShapeRoot d).exitAddr = neckAddr (gShapeRoot d).decs (gSplitDepth d) := by
  rw [GShape.exitAddr, gExitAddr_eq_neckAddr, decs_gShapeRoot_length, Nat.add_sub_cancel]

lemma gShapeRoot_bouquet (d : GWord N → ℕ) : (gShapeRoot d).bouquet = gDecList (gSplitField d) :=
  rfl

lemma gShapeRoot_realise (d : GWord N → ℕ) :
    (gShapeRoot d).realise = realiseAux (gShapeRoot d).decs := rfl

/-- The number of bushes of a vertex is the number of its dying children. -/
lemma length_gDecList_eq {e : GWord N → ℕ} (he : e [] ≤ N) :
    (gDecList e).length = (dyingSet e).card := by
  rw [length_gDecList]
  have := survivors_card_add_dyingSet_card he
  omega

lemma neckIter_root {c : GWord N → ℕ} {y : GWord N} (hs : Survives (ambSub c y)) (i : ℕ) :
    neckIter (ambSub c y) i [] = c (y ++ neckPath (ambSub c y) i) := by
  rw [neckIter_eq_ambSub_neckPath hs, ambSub_root, ambSub_apply]

/-- **The neck of a copy is the chain of its entry**: the translation carries the neck
addresses of the shape at a vertex to its neck ray. -/
lemma transSampleN_neck {c : GWord N → ℕ} (hc : IsGHairySample c) {a : List ℕ} {y : GWord N}
    (ha : transSampleN c a = vals y) (hs : Survives (ambSub c y)) :
    ∀ i, i ≤ gSplitDepth (ambSub c y) →
      transSampleN c (a ++ neckAddr (gShapeRoot (ambSub c y)).decs i)
        = vals (y ++ neckPath (ambSub c y) i)
  | 0, _ => by simpa using ha
  | i + 1, hi => by
      have ih := transSampleN_neck hc ha hs i (by omega)
      have hi' : i < (gShapeRoot (ambSub c y)).decs.length := by
        rw [decs_gShapeRoot_length]; omega
      have hN : neckIter (ambSub c y) i [] ≤ N := by
        rw [neckIter_root hs]
        exact hc.offspring _
      rw [neckAddr_succ hi', ← List.append_assoc, transSampleN_concat, ih, sampleLetterN_vals,
        ← ambSub_ambSub, ← neckIter_eq_ambSub_neckPath hs i, decs_gShapeRoot_getElem _ hi',
        length_gDecList_eq hN, vals_append, vals_append, vals_neckPath_succ hs i,
        ← List.append_assoc, letterMap, if_neg (lt_irrefl _), Nat.sub_self]

/-- The entry vertices lie in the sample, at the root. -/
lemma gEntryV_mem_sample' {c : GWord N → ℕ} (hc : IsGHairySample c) {u : GWord N}
    (hu : u ∈ sample (gArityAt c)) : gEntryV c u ∈ sample c := by
  have h := gEntryV_mem_sample hc u [] (BranchingProcess.nil_mem_sample c)
    (by simpa using hc.survives) (by simpa using hu)
  simpa using h

/-- **The entry of a copy**: the translation carries the planting of the copy at `u` to
its entry vertex. -/
lemma transSampleN_gCopyAddr {c : GWord N → ℕ} (hc : IsGHairySample c) :
    ∀ {u : GWord N}, u ∈ sample (gArityAt c) →
      transSampleN c (gCopyAddr (liftN N (gShapeAt c)) (vals u)) = vals (gEntryV c u) := by
  intro u
  induction u using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton u j ih =>
      intro hu
      obtain ⟨hu', hj⟩ := BranchingProcess.mem_sample_append_singleton.mp hu
      obtain ⟨hred, hsurv⟩ := redSub_eq_ambSub_gEntryV' hc hu'
      have hs : Survives (ambSub c (gEntryV c u)) := hred ▸ hsurv
      have hih := ih hu'
      have hsf : gSplitField (ambSub c (gEntryV c u))
          = neckIter (ambSub c (gEntryV c u)) (gSplitDepth (ambSub c (gEntryV c u))) := rfl
      have hN : gSplitField (ambSub c (gEntryV c u)) [] ≤ N := by
        rw [hsf, neckIter_root hs]
        exact hc.offspring _
      have hj' : (j : ℕ) < skeletonDegree (gSplitField (ambSub c (gEntryV c u))) := by
        have : gArityAt c u = gArity (redSub c u) := rfl
        rw [this, hred] at hj
        exact hj
      have hlt : survLetter (gSplitField (ambSub c (gEntryV c u))) j < N := survLetter_lt hj'
      rw [vals_append, vals_cons, vals_nil, gCopyAddr_concat, liftN_vals, gShapeAt, hred,
        gShapeRoot_exitAddr, transSampleN_concat, transSampleN_neck hc hih hs _ le_rfl,
        gShapeRoot_bouquet, gEntryV_concat, hred, splitPath, unval_singleton hlt,
        sampleLetterN_vals, ← ambSub_ambSub, ← neckIter_eq_ambSub_neckPath hs, ← hsf,
        length_gDecList_eq hN, letterMap, if_neg (by omega), Nat.add_sub_cancel_left]
      simp only [vals_append, vals_cons, vals_nil, List.append_assoc]

/-- A vertex of a finite subtree founds a finite subtree. -/
lemma not_survives_ambSub_of_mem {e : GWord N → ℕ} (hfin : ¬ Survives e) {v : GWord N}
    (hv : v ∈ sample e) : ¬ Survives (ambSub e v) := by
  intro hs
  have hs' : (sample (ambSub e v) : Set (GWord N)).Infinite := hs
  have hsub : (fun z : GWord N ↦ v ++ z) '' (sample (ambSub e v) : Set (GWord N))
      ⊆ (sample e : Set (GWord N)) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, BranchingProcess.append_mem_sample_iff]
    exact ⟨hv, hz⟩
  have himg := hs'.image (f := fun z : GWord N ↦ v ++ z)
    (fun z _ z' _ h ↦ List.append_cancel_left h)
  exact hfin (himg.mono hsub)

/-- **The translation inside a bush**: below a dying vertex the translation reads the
letters one for one. -/
lemma transSampleN_bush {c : GWord N → ℕ} (hc : IsGHairySample c) {a : List ℕ} {y : GWord N}
    (ha : transSampleN c a = vals y) (hfin : ¬ Survives (ambSub c y)) :
    ∀ v : GWord N, v ∈ sample (ambSub c y) → transSampleN c (a ++ vals v) = vals (y ++ v) := by
  intro v
  induction v using List.reverseRecOn with
  | nil => simpa using ha
  | append_singleton v j ih =>
      intro hv
      obtain ⟨hv', hj⟩ := BranchingProcess.mem_sample_append_singleton.mp hv
      have hnot : ¬ Survives (ambSub c (y ++ v)) := by
        rw [← ambSub_ambSub]
        exact not_survives_ambSub_of_mem hfin hv'
      have hj' : (j : ℕ) < ambSub c (y ++ v) [] := by
        rw [ambSub_root]
        exact hj
      rw [vals_append, vals_cons, vals_nil, ← List.append_assoc, transSampleN_concat, ih hv',
        sampleLetterN_vals, letterMap_of_not_survives (by rw [ambSub_root]; exact hc.offspring _)
          hnot hj', ← List.append_assoc, vals_append, vals_append, vals_cons, vals_nil,
        vals_append]

/-- **The addresses of a bush are the vertices of the dying subtree.** -/
lemma isAddr_bushRTree_iff {e : GWord N → ℕ} (he : ∀ v, e v ≤ N) (hfin : ¬ Survives e)
    (w : List ℕ) : IsAddr (bushRTree e) w ↔ ∃ v ∈ sample e, w = vals v := by
  constructor
  · intro hw
    obtain ⟨v, rfl⟩ := exists_map_val_eq w (lt_of_isAddr_rtreeOf _ e w hw)
    exact ⟨v, (mem_sample_iff_isAddr_rtreeOf _ he (sampleHeight_spec hfin) v).mpr hw, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact (mem_sample_iff_isAddr_rtreeOf _ he (sampleHeight_spec hfin) v).mp hv

/-! ### The vertices of the assembly and the vertices of the sample -/

/-- The neck-vertex case of the dictionary: a neck address of the shape at a vertex
translates to a vertex of its neck ray, whose children are counted by its bushes and its
surviving children. -/
lemma transSampleN_spec_neck {c : GWord N → ℕ} (hc : IsGHairySample c) {a : List ℕ}
    {y₀ : GWord N} (ha : transSampleN c a = vals y₀) (hy₀ : y₀ ∈ sample c)
    (hs : Survives (ambSub c y₀)) {i : ℕ} (hi : i < (gShapeRoot (ambSub c y₀)).decs.length) :
    ∃ v ∈ sample c, transSampleN c (a ++ neckAddr (gShapeRoot (ambSub c y₀)).decs i) = vals v ∧
      ∀ m, ((neckAddr (gShapeRoot (ambSub c y₀)).decs i = (gShapeRoot (ambSub c y₀)).exitAddr
            ∧ ∃ j : Fin N, (j : ℕ) < gArity (ambSub c y₀)
              ∧ m = (gShapeRoot (ambSub c y₀)).bouquet.length + j)
          ∨ IsAddr (gShapeRoot (ambSub c y₀)).realise
              (neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ [m])) ↔ m < c v := by
  have hLlen : (gShapeRoot (ambSub c y₀)).decs.length = gSplitDepth (ambSub c y₀) + 1 := decs_gShapeRoot_length (ambSub c y₀)
  have hin : i ≤ gSplitDepth (ambSub c y₀) := by omega
  have hroot : c (y₀ ++ neckPath (ambSub c y₀) i) = neckIter (ambSub c y₀) i [] := (neckIter_root hs i).symm
  have hN : neckIter (ambSub c y₀) i [] ≤ N := by rw [← hroot]; exact hc.offspring _
  have hcard : (gShapeRoot (ambSub c y₀)).decs[i].length = (dyingSet (neckIter (ambSub c y₀) i)).card := by
    rw [decs_gShapeRoot_getElem (ambSub c y₀) hi, length_gDecList_eq hN]
  have hsum := survivors_card_add_dyingSet_card hN
  refine ⟨y₀ ++ neckPath (ambSub c y₀) i, neckPath_mem_sample hy₀ hs i,
    transSampleN_neck hc ha hs i hin, fun m ↦ ?_⟩
  rw [hroot, gShapeRoot_realise, gShapeRoot_exitAddr,
    isAddr_realiseAux_neck_concat (gShapeRoot (ambSub c y₀)).decs i hi m, hcard, hLlen]
  rcases Nat.lt_or_ge i (gSplitDepth (ambSub c y₀)) with hlt | hge
  · have hdeg : skeletonDegree (neckIter (ambSub c y₀) i) = 1 := skeletonDegree_neckIter_eq_one hs hlt
    have hne : neckAddr (gShapeRoot (ambSub c y₀)).decs i ≠ neckAddr (gShapeRoot (ambSub c y₀)).decs (gSplitDepth (ambSub c y₀)) := by
      intro h
      have := congrArg List.length h
      rw [neckAddr_length (by omega), neckAddr_length (by omega)] at this
      omega
    simp only [hne, false_and, false_or]
    omega
  · have hin' : i = gSplitDepth (ambSub c y₀) := le_antisymm hin hge
    subst hin'
    have hκ : gArity (ambSub c y₀)
        = skeletonDegree (neckIter (ambSub c y₀) (gSplitDepth (ambSub c y₀))) := rfl
    have hbq : (gShapeRoot (ambSub c y₀)).bouquet.length
        = (dyingSet (neckIter (ambSub c y₀) (gSplitDepth (ambSub c y₀)))).card := by
      rw [gShapeRoot_bouquet, ← hcard, decs_gShapeRoot_getElem (ambSub c y₀) hi]
      rfl
    rw [hκ, hbq]
    constructor
    · rintro (⟨-, j, hj, rfl⟩ | h | ⟨-, h⟩)
      · omega
      · omega
      · omega
    · intro hm
      by_cases hm' : m < (dyingSet (neckIter (ambSub c y₀) (gSplitDepth (ambSub c y₀)))).card
      · exact Or.inr (Or.inl hm')
      · exact Or.inl ⟨rfl, ⟨m - (dyingSet (neckIter (ambSub c y₀) (gSplitDepth (ambSub c y₀)))).card,
          by omega⟩, by simp only; omega, by simp only; omega⟩

/-- The bush case of the dictionary: a bush address of the shape at a vertex translates
to a vertex of the dying subtree hanging off its neck ray, whose children are the
children of that vertex. -/
lemma transSampleN_spec_bush {c : GWord N → ℕ} (hc : IsGHairySample c) {a : List ℕ}
    {y₀ : GWord N} (ha : transSampleN c a = vals y₀) (hy₀ : y₀ ∈ sample c)
    (hs : Survives (ambSub c y₀)) {i : ℕ} (hi : i < (gShapeRoot (ambSub c y₀)).decs.length)
    {m₀ : ℕ} (hm₀ : m₀ < (gShapeRoot (ambSub c y₀)).decs[i].length) {z : List ℕ}
    (hz : IsAddr (gShapeRoot (ambSub c y₀)).decs[i][m₀] z) :
    ∃ v ∈ sample c,
      transSampleN c (a ++ (neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: z)) = vals v ∧
      ∀ m, ((neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: z
              = (gShapeRoot (ambSub c y₀)).exitAddr
            ∧ ∃ j : Fin N, (j : ℕ) < gArity (ambSub c y₀)
              ∧ m = (gShapeRoot (ambSub c y₀)).bouquet.length + j)
          ∨ IsAddr (gShapeRoot (ambSub c y₀)).realise
              ((neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: z) ++ [m])) ↔ m < c v := by
  have hLlen : (gShapeRoot (ambSub c y₀)).decs.length = gSplitDepth (ambSub c y₀) + 1 := decs_gShapeRoot_length (ambSub c y₀)
  have hin : i ≤ gSplitDepth (ambSub c y₀) := by omega
  have hroot : c (y₀ ++ neckPath (ambSub c y₀) i) = neckIter (ambSub c y₀) i [] := (neckIter_root hs i).symm
  have hN : neckIter (ambSub c y₀) i [] ≤ N := by rw [← hroot]; exact hc.offspring _
  have hLi : (gShapeRoot (ambSub c y₀)).decs[i] = gDecList (neckIter (ambSub c y₀) i) := decs_gShapeRoot_getElem (ambSub c y₀) hi
  have hcard : (gShapeRoot (ambSub c y₀)).decs[i].length = (dyingSet (neckIter (ambSub c y₀) i)).card := by
    rw [hLi, length_gDecList_eq hN]
  have hm₀' : m₀ < (dyingSet (neckIter (ambSub c y₀) i)).card := by rw [← hcard]; exact hm₀
  have hm₀'' : m₀ < (gDecList (neckIter (ambSub c y₀) i)).length := by
    rw [length_gDecList_eq hN]; exact hm₀'
  have hbush : (gShapeRoot (ambSub c y₀)).decs[i][m₀] = bushRTree (dyingAt (neckIter (ambSub c y₀) i) m₀) := by
    rw [List.getElem_of_eq hLi hm₀, getElem_gDecList _ hm₀'']
  rw [hbush] at hz
  have hy₁mem : y₀ ++ neckPath (ambSub c y₀) i ∈ sample c := neckPath_mem_sample hy₀ hs i
  have he1 : ambSub c (y₀ ++ neckPath (ambSub c y₀) i) = neckIter (ambSub c y₀) i := by
    rw [← ambSub_ambSub, neckIter_eq_ambSub_neckPath hs i]
  obtain ⟨ℓ, hℓ, hℓeq⟩ := dyingLetter_mem hm₀'
  have hℓlt : dyingLetter (neckIter (ambSub c y₀) i) m₀ < N := by rw [hℓeq]; exact ℓ.isLt
  have he2 : dyingAt (neckIter (ambSub c y₀) i) m₀
      = ambSub c (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀]) := by
    rw [dyingAt_eq_ambSub hm₀', ← ambSub_ambSub, he1]
  have hfin : ¬ Survives (ambSub c (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀])) :=
    he2 ▸ not_survives_dyingAt hm₀'
  have hN2 : ∀ v, ambSub c (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀]) v ≤ N :=
    fun v ↦ hc.offspring _
  rw [he2, isAddr_bushRTree_iff hN2 hfin] at hz
  obtain ⟨v, hv, rfl⟩ := hz
  have hy₂mem : y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀] ∈ sample c := by
    rw [unval_singleton hℓlt, BranchingProcess.mem_sample_append_singleton]
    refine ⟨hy₁mem, ?_⟩
    show dyingLetter (neckIter (ambSub c y₀) i) m₀ < c (y₀ ++ neckPath (ambSub c y₀) i)
    rw [hroot, hℓeq]
    exact (mem_dyingSet.mp hℓ).1
  have htrans2 : transSampleN c (a ++ neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ [m₀])
      = vals (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀]) := by
    rw [transSampleN_concat, transSampleN_neck hc ha hs i hin, sampleLetterN_vals, he1,
      letterMap, if_pos hm₀', unval_singleton hℓlt]
    simp only [vals_append, vals_cons, vals_nil]
  have htrans : transSampleN c (a ++ (neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: vals v))
      = vals (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀] ++ v) := by
    have heq : a ++ (neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: vals v)
        = (a ++ neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ [m₀]) ++ vals v := by
      simp [List.append_assoc]
    rw [heq]
    exact transSampleN_bush hc htrans2 hfin v hv
  refine ⟨_, (BranchingProcess.append_mem_sample_iff c _ v).mpr ⟨hy₂mem, hv⟩, htrans,
    fun m ↦ ?_⟩
  have hne : neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: vals v ≠ (gShapeRoot (ambSub c y₀)).exitAddr := by
    rw [gShapeRoot_exitAddr]
    intro h
    have hlen := congrArg List.length h
    have hin2 : i ≤ (gShapeRoot (ambSub c y₀)).decs.length := by omega
    have hn2 : gSplitDepth (ambSub c y₀) ≤ (gShapeRoot (ambSub c y₀)).decs.length := by omega
    simp only [List.length_append, List.length_cons, neckAddr_length hin2,
      neckAddr_length hn2] at hlen
    have hlt : i < gSplitDepth (ambSub c y₀) := by omega
    have h1 : neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ [m₀] <+: neckAddr (gShapeRoot (ambSub c y₀)).decs (gSplitDepth (ambSub c y₀)) := by
      rw [← h]
      exact ⟨vals v, by simp⟩
    have h2 : neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ [(gShapeRoot (ambSub c y₀)).decs[i].length]
        <+: neckAddr (gShapeRoot (ambSub c y₀)).decs (gSplitDepth (ambSub c y₀)) := by
      rw [← neckAddr_succ hi]
      exact neckAddr_prefix _ (by omega)
    have h3 := List.prefix_of_prefix_length_le h1 h2 (by simp)
    have h4 := h3.eq_of_length (by simp)
    have h5 := List.append_cancel_left h4
    simp only [List.cons.injEq, and_true] at h5
    omega
  simp only [hne, false_and, false_or]
  have hassoc : neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: vals v ++ [m]
      = neckAddr (gShapeRoot (ambSub c y₀)).decs i ++ m₀ :: (vals v ++ [m]) := by
    simp
  rw [hassoc, gShapeRoot_realise, isAddr_realiseAux_bush _ i hi m₀ hm₀, hbush, he2,
    isAddr_bushRTree_iff hN2 hfin]
  have hcv : c (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀] ++ v)
      = ambSub c (y₀ ++ neckPath (ambSub c y₀) i ++ unval N [dyingLetter (neckIter (ambSub c y₀) i) m₀]) v :=
    (ambSub_apply c _ v).symm
  rw [hcv]
  constructor
  · rintro ⟨v', hv', heq⟩
    obtain ⟨v'', j, rfl, hv'', rfl⟩ := SkelAssembly.vals_eq_append_singleton_iff.mp heq.symm
    have : v'' = v := vals_injective hv''
    subst this
    exact (BranchingProcess.mem_sample_append_singleton.mp hv').2
  · intro hm
    have hmN : m < N := lt_of_lt_of_le hm (hN2 v)
    exact ⟨v ++ [⟨m, hmN⟩], BranchingProcess.mem_sample_append_singleton.mpr ⟨hv, hm⟩, by simp⟩

/-- **The dictionary** (**`thm:shape-iid`** at general arity): the translation carries a
vertex of the skeleton assembly to a vertex of the sample, and the children of the two
agree through the letter map. -/
theorem transSampleN_code_spec {c : GWord N → ℕ} (hc : IsGHairySample c)
    (x : SkelAssembly (gArityAt c) (gShapeAt c)) :
    (∃ v ∈ sample c, transSampleN c x.code = vals v) ∧
      ∀ m : ℕ, (∃ y : SkelAssembly (gArityAt c) (gShapeAt c), y.code = x.code ++ [m])
        ↔ sampleLetterN c (transSampleN c x.code) m < c (unval N (transSampleN c x.code)) := by
  obtain ⟨u, hu, pw, hpw⟩ := x
  obtain ⟨hred, hsurv⟩ := redSub_eq_ambSub_gEntryV' hc hu
  have hs : Survives (ambSub c (gEntryV c u)) := hred ▸ hsurv
  have hy₀mem : gEntryV c u ∈ sample c := gEntryV_mem_sample' hc hu
  have ha := transSampleN_gCopyAddr hc hu
  have hshape : gShapeAt c u = gShapeRoot (ambSub c (gEntryV c u)) := by rw [gShapeAt, hred]
  have harity : gArityAt c u = gArity (ambSub c (gEntryV c u)) := by rw [gArityAt, hred]
  have hp : IsAddr (realiseAux (gShapeRoot (ambSub c (gEntryV c u))).decs) pw := by
    have := RTree.mem_addrList_iff.mp hpw
    rwa [hshape] at this
  have hmain : ∃ v ∈ sample c,
      transSampleN c (SkelAssembly.code ⟨u, hu, ⟨pw, hpw⟩⟩) = vals v ∧
      ∀ m, ((pw = (gShapeRoot (ambSub c (gEntryV c u))).exitAddr
            ∧ ∃ j : Fin N, (j : ℕ) < gArity (ambSub c (gEntryV c u))
              ∧ m = (gShapeRoot (ambSub c (gEntryV c u))).bouquet.length + j)
          ∨ IsAddr (gShapeRoot (ambSub c (gEntryV c u))).realise (pw ++ [m])) ↔ m < c v := by
    rw [SkelAssembly.code_eq]
    dsimp only
    rcases isAddr_realiseAux_cases _ (decs_gShapeRoot_ne_nil _) hp with
      ⟨i, hi, hpi⟩ | ⟨i, hi, m₀, hm₀, z, hz, hpz⟩
    · rw [hpi]
      exact transSampleN_spec_neck hc ha hy₀mem hs hi
    · rw [hpz]
      exact transSampleN_spec_bush hc ha hy₀mem hs hi hm₀ hz
  obtain ⟨v, hv, htrans, hcond⟩ := hmain
  refine ⟨⟨v, hv, htrans⟩, fun m ↦ ?_⟩
  rw [SkelAssembly.exists_code_concat_iff, htrans, sampleLetterN_vals, unval_vals]
  dsimp only
  rw [hshape, harity, hcond m]
  have h := letterMap_lt_iff (d := ambSub c v) (by rw [ambSub_root]; exact hc.offspring v) m
  rw [ambSub_root] at h
  exact h.symm

/-! ### The sample is the assembly of its shapes over its reduced skeleton -/

/-- Every vertex of the sample is the translation of a vertex of the skeleton assembly:
the chains of the skeleton and their bushes exhaust the sample. -/
lemma exists_code_transSampleN {c : GWord N → ℕ} (hc : IsGHairySample c) :
    ∀ v : GWord N, v ∈ sample c →
      ∃ x : SkelAssembly (gArityAt c) (gShapeAt c), transSampleN c x.code = vals v := by
  intro v
  induction v using List.reverseRecOn with
  | nil =>
      intro _
      exact ⟨⟨[], BranchingProcess.nil_mem_sample _, (gShapeSpace _).entry⟩,
        by simp [SkelAssembly.code_eq]⟩
  | append_singleton v j ih =>
      intro hv
      obtain ⟨hv', hj⟩ := BranchingProcess.mem_sample_append_singleton.mp hv
      obtain ⟨x, hx⟩ := ih hv'
      obtain ⟨m, -, hmeq⟩ := letterMap_surj (d := ambSub c v)
        (by rw [ambSub_root]; exact hc.offspring v) (by rw [ambSub_root]; exact hj)
      have hspec := (transSampleN_code_spec hc x).2 m
      rw [hx, sampleLetterN_vals, unval_vals] at hspec
      have hchild : letterMap (ambSub c v) m < c v := by rw [hmeq]; exact hj
      obtain ⟨y, hy⟩ := hspec.mpr hchild
      refine ⟨y, ?_⟩
      rw [hy, transSampleN_concat, hx, sampleLetterN_vals, hmeq, vals_append, vals_cons, vals_nil]

/-- **`thm:shape-iid` at general arity, the isometry** (the premise of
**`it:general-glued`**): a hairy sample is isometric to the assembly of its own shapes
over its reduced skeleton.  The isometry is the address translation: it reads the
letters of the assembly one for one, sending the neck of a copy to the chain of its entry
vertex, its bushes to the dying subtrees hanging off that chain, and the copies below
its exit to the surviving children of the split, so it preserves lengths and the prefix
order, and with them every distance. -/
theorem gAssembly_isometric_sample {c : GWord N → ℕ} (hc : IsGHairySample c) :
    ∃ Φ : SkelAssembly (gArityAt c) (gShapeAt c) → {v : GWord N // v ∈ sample c},
      Function.Bijective Φ ∧
      ∀ x y, (BranchingProcess.treeDist (Φ x).1 (Φ y).1 : ℝ) = dist x y := by
  have hmem : ∀ x : SkelAssembly (gArityAt c) (gShapeAt c),
      unval N (transSampleN c x.code) ∈ sample c
        ∧ vals (unval N (transSampleN c x.code)) = transSampleN c x.code := by
    intro x
    obtain ⟨v, hv, hx⟩ := (transSampleN_code_spec hc x).1
    rw [hx, unval_vals]
    exact ⟨hv, rfl⟩
  refine ⟨fun x ↦ ⟨unval N (transSampleN c x.code), (hmem x).1⟩, ⟨?_, ?_⟩, ?_⟩
  · intro x y h
    have h1 : unval N (transSampleN c x.code) = unval N (transSampleN c y.code) :=
      congrArg Subtype.val h
    have h2 : transSampleN c x.code = transSampleN c y.code := by
      rw [← (hmem x).2, ← (hmem y).2, h1]
    exact SkelAssembly.code_injective (transSampleN_injective c h2)
  · rintro ⟨v, hv⟩
    obtain ⟨x, hx⟩ := exists_code_transSampleN hc v hv
    exact ⟨x, Subtype.ext (by simp only; rw [hx, unval_vals])⟩
  · intro x y
    simp only
    rw [← addrDist_vals, (hmem x).2, (hmem y).2, transSampleN,
      transN_addrDist (sampleLetterN_injective c)]
    rfl

/-! ### `thm:hairy-general`, the deterministic core -/

/-- **`thm:hairy-general`, the deterministic core.**  Two hairy samples, over alphabets
`N` and `N'`, whose reduced skeletons are encoded into `𝔹` at depths `L` and `L'`, with an
automorphism `π` of `𝔹` carrying one encoded skeleton onto the other and matching the
shape labels at comparability `K`, are `⌈216 L L'² K²⌉`-quasi-isometric as graphs: each
sample is isometric to the assembly of its shapes over its reduced skeleton, that
assembly is `L`-quasi-isometric to the `𝔹`-assembly placing the shapes at the cascade
roots and one-vertex shapes at the forced slots, and the glued transfer over `𝔹` at `K`
assembles the matched shapes into an `8K²`-quasi-isometry of the `𝔹`-assemblies. -/
theorem sample_qi_of_bShape_matching {N' L L' : ℕ} {c : GWord N → ℕ} {c' : GWord N' → ℕ}
    (hc : IsGHairySample c) (hc' : IsGHairySample c') (E : CascadeEnc N L) (E' : CascadeEnc N' L')
    (hk : E.k = gArityAt c) (hk' : E'.k = gArityAt c') (hL : 1 ≤ L) (hL' : 1 ≤ L') {K : ℝ}
    (hK : 1 ≤ K) (π : Word → Bool ≃ Bool)
    (hπ : ∀ w : Word, E.InClosure (bnat w) ↔ E'.InClosure (bnat (autOf π w)))
    (hcomp : ∀ w : Word, MarkedQI K (gShapeSpace (E.bFamily (gShapeAt c) (bnat w)))
      (gShapeSpace (E'.bFamily (gShapeAt c') (bnat (autOf π w))))) :
    ∃ F : {v : GWord N // v ∈ sample c} → {v : GWord N' // v ∈ sample c'},
      BranchingProcess.IsQIWith ⌈216 * L * L' ^ 2 * K ^ 2⌉₊
        (wordGraphN (· ∈ sample c)) (wordGraphN (· ∈ sample c')) F := by
  obtain ⟨Φ, hΦ, hΦd⟩ := gAssembly_isometric_sample hc
  obtain ⟨Φ', hΦ', hΦd'⟩ := gAssembly_isometric_sample hc'
  obtain ⟨k, enc, slot, h1, h2, h3, h4, h5⟩ := E
  obtain ⟨k', enc', slot', h1', h2', h3', h4', h5'⟩ := E'
  dsimp only at hk hk'
  subst hk hk'
  exact CascadeEnc.sample_qi_of_bShape_matching_of_isometric hL hL' hK π hπ hcomp hΦ hΦd hΦ' hΦd'

end ChainClasses

