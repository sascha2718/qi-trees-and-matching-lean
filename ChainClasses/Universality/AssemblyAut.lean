import ChainClasses.Universality.CascadeEncoding

/-!
`thm:hairy-general`, the deterministic geometry, second part: relabelling an assembly along
a tree automorphism, automorphisms of `𝔹` on words over `ℕ`, the deterministic core over
`𝔹`, the passage from the skeleton assemblies to the sample graphs, and the composition
over abstract sample isometries.  The sample as an assembly follows in `SampleAssembly`.
-/

namespace ChainClasses

open BranchingProcess (sample Survives survivors skeletonDegree)

variable {N : ℕ}

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
  rw [bAut, ite_eq_left h]

lemma bAut_bnat (π : Word → Bool ≃ Bool) (x : Word) : bAut π (bnat x) = bnat (autOf π x) := by
  rw [bAut_of_isBin π (isBin_bnat x), unbnat_bnat]

lemma bAut_of_not_isBin (π : Word → Bool ≃ Bool) {w : List ℕ} (h : ¬ IsBin w) :
    bAut π w = w := by
  rw [bAut, ite_eq_right h]

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

end ChainClasses
