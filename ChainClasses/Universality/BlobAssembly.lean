import ChainClasses.Universality.BlobPresented

/-!
`thm:chain-general` of `trichotomy.tex`, the deterministic core: the glued transfer of
`it:general-glued` over the presented skeleton with the flat blob configurations in place
of the shapes, and the identification of a chain-regime sample with the assembly of its
presented blobs.

A presented blob of `def:blob` is a finite subtree of the reduced skeleton with several
The argument is built in five modules: `Piece`, `ChainBlob`, `BlobPiece`, `BlobPresented`
and this one, which carries the bridge to the bare-neck shapes, the quasi-isometries of
samples and the deterministic core; the account below covers all five.

exits: the presented neck, the absorbed splits reached within the revealing window, and
the revealed neck segments of the spent exits, with the unspent exits and the bottoms of
the spent segments as its ports, one per presented child.  The assembly of
`GeneralAssembly` plants one copy below the exit of each shape; here a piece carries a
list of ports, each with the free child index at which the next copy is planted, and the
copy at `w ++ [j]` hangs at the `j`-th port of the copy at `w`.  The index words run over
an index set in which each letter is below the port count of the piece it leaves, so no
junk copy is ever planted.  The metric is the address metric through the codes, and the
two distance formulas are those of the single-exit case with the port the index word uses
in place of the exit: the ancestor formula is unchanged, and the divergent formula gains
the distance between the two ports of the copy at the wedge the branches leave through.
The glued transfer then runs on the arithmetic of `GluedTransfer` with one more term, a
port quasi-isometry being a quasi-isometry moving the entry and every port by at most `K`.

In the chain regime every vertex has a child, so the reduced skeleton is the sample
itself, and a blob is read off the trace of the automaton `bExplore` as a list of
relative addresses of the sample: the neck, then below each exit of the split nothing,
the `R` revealed vertices, or the neck down to the absorbed split followed by the vertices
below its exits.  The ports are listed in the order the automaton hands the presented
children, so the handed subfield `bSubC` of a port is the field at its planted child,
and the cluster root of a presented address is the concatenation of the planted children
along it.  Every vertex of the sample is a vertex of the blob of some presented address,
the descent through the planted children terminating, and no vertex belongs to two
blobs, so the sample is isometric to the assembly of its blobs over its presented
skeleton.  A blob is a neck piece, everything beyond the far end of the presented neck
lying within `R(T + 2)` of it for the stopping bound `T` of the rule, and the collapse
onto the far end is the port quasi-isometry of `it:matched-flat`; the flat configurations
are bare-neck shapes, so their assembly over the presented skeleton is the assembly of
shapes the cascade encoding of `𝔹` consumes.

* `Piece`, `Piece.port`, `Piece.slot`, `Piece.root`, `Piece.wedgeN_eq_wedgeN_port`,
  `Piece.wedgeN_root_root`: multi-port pieces, the planting at a port, and the two wedge
  computations the distance formulas rest on.
* `PortSpace`, `IsPortQI`, `IsPortQI.comp`, `IsPortQI.symm`: multi-marked spaces and port
  quasi-isometries, composing at `3KK'` and inverting at `3K²`.
* `pCopyAddr`, `pNeck`, `pNeckSum`, `addrDist_pCopyAddr_anc`, `addrDist_pCopyAddr_div`:
  the planting of the copies, the neck length of a copy toward the letter the index word
  uses, and the two distance formulas at the level of addresses.
* `PIdx`, `PAssembly`, `PAssembly.instMetricSpace`, `PAssembly.dist_same`,
  `PAssembly.dist_anc`, `PAssembly.dist_div`: the assembly over an index set and its
  metric, with the three distance formulas in the form `d = A + B + e + N + P`.
* `blob_glued_dist_bounds`, `port_dist_bounds`, `PAssembly.glue`,
  `PAssembly.glued_transfer`, `PAssembly.glue_isQIMap`: **`it:general-glued` with several
  ports**, two families of pieces `K`-port comparable copy by copy having
  `8K²`-quasi-isometric assemblies.
* `pRep`, `flatPiece`, `collapseAddr`, `IsNeckPiece`, `collapse`, `isPortQI_collapse`:
  **`thm:matched-presentation` (`it:matched-flat`)** in the abstract: a neck piece
  of depth `Δ` beyond its far end is `(2Δ + 1)`-port comparable to its flat configuration.
* `pvals`, `addrDist_pvals`, `rep`, `IsChainField` with `survives`, `skeletonDegree_eq`,
  `bushAt_eq`, `neckIter_eq`, `gArity_eq`, `gSplitBush_eq`, `bHit_iff`, `neck_cases`: the
  chain regime deterministically, the Harris-decomposition subfields at ambient vertices.
* `splitVerts`, `hangVerts`, `splitPorts`, `hangPorts`, `BFit`, `BFitT`, `hdepth`: the blob
  read off a trace, the predicate that a trace fits the field, and the hit nesting.
* `prefix_mem_splitVerts`, `port_mem_splitVerts`, `root_not_mem_splitVerts`,
  `nodup_roots_splitPorts`, `mem_sample_of_mem_splitVerts`,
  `root_mem_sample_of_mem_splitPorts`, `cover_splitVerts`, `bFollow_splitPorts`,
  `bFit_of_bMatchL`, `length_le_of_mem_splitVerts`: the blob is prefix-closed, its ports
  are vertices, the planted children are distinct non-vertices in the sample, every
  sample vertex below the split is absorbed or handed on, the handed subfields are the
  fields at the planted children, the automaton's traces fit, and the depth bound.
* `blobVertsW`, `blobPortsW`, `blobPieceOf`, `blob_cover`: **`def:blob`** as a piece.
* `Presented`, `rootAt`, `blobPiece`, `presented_spec`, `presented_concat`, `blob_pIdx`,
  `pCopyAddr_blobPiece`: the presented skeleton, the cluster roots, and the blob pieces of
  a rule over a presented field.
* `exists_code_eq_pvals`, `exists_pvals_eq_code`, `blobAssembly_isometric_sample`: **the
  sample is isometric to the blob assembly over the presented skeleton**.
* `blobPiece_isNeckPiece`, `flatAt`, `flat_pIdx`, `blobPiece_flat_portQI`,
  `blob_flat_glued`: **`thm:matched-presentation` (`it:matched-flat`)** for the
  presented blobs, at `2R(T + 2) + 1`, and the glued flattening at `flatScale R T`.
* `flatG`, `pathTree`, `flatG_exitAddr`, `mem_addrList_flatG`, `flatToG`,
  `flatToG_isometry`: the flat configurations are the bare-neck shapes, and the flat
  assembly is the assembly of those shapes over the presented skeleton.
* `IsSampleQIN`, `isSampleQIN_of_isQIMap`, `quasiIsometric_of_isSampleQIN`: quasi-isometries
  transport to the samples and their graphs.
* `sample_qi_of_blob_matching`, `quasiIsometric_of_blob_matching`: **`thm:chain-general`, the deterministic core**: given
  quasi-isometries of the two flat assemblies with the `𝔹`-assemblies of the cascade
  encoding and a quasi-isometry between those, or the per-copy comparability of the
  encoded flat blobs after the automorphism, the two samples are quasi-isometric at an
  explicit constant.
-/

namespace ChainClasses

open BranchingProcess (sample Survives skeleton survivors skeletonDegree bushAt childSet)

variable {N : ℕ}

/-! ### The flat configurations are bare-neck shapes -/

/-- The bare neck of `n` edges as a shape: `n + 1` neck vertices, no bushes, an empty
bouquet. -/
def flatG (n : ℕ) : GShape := ⟨n, fun _ => []⟩

/-- The path of `n` edges as a rose tree. -/
def pathTree : ℕ → RTree
  | 0 => .node []
  | n + 1 => .node [pathTree n]

lemma flatG_decs (n : ℕ) : (flatG n).decs = List.replicate (n + 1) [] := by
  rw [GShape.decs, flatG]
  exact List.ofFn_const (n + 1) []

lemma realiseAux_replicate : ∀ n : ℕ,
    GShape.realiseAux (List.replicate (n + 1) []) = pathTree n
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ, List.replicate_succ]
      show RTree.node ([] ++ [GShape.realiseAux ([] :: List.replicate n [])]) = _
      rw [← List.replicate_succ, realiseAux_replicate n]
      rfl

lemma flatG_realise (n : ℕ) : (flatG n).realise = pathTree n := by
  rw [GShape.realise, flatG_decs, realiseAux_replicate]

lemma gExitAddr_replicate : ∀ n : ℕ, gExitAddr (List.replicate (n + 1) ([] : List RTree)) = pRep n
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ, List.replicate_succ, gExitAddr_cons₂, ← List.replicate_succ,
        gExitAddr_replicate n, pRep, pRep, List.replicate_succ]
      rfl

lemma flatG_exitAddr (n : ℕ) : (flatG n).exitAddr = pRep n := by
  rw [GShape.exitAddr, flatG_decs, gExitAddr_replicate]

lemma flatG_bouquet (n : ℕ) : (flatG n).bouquet = [] := rfl

/-- The addresses of the path are the neck vertices. -/
lemma isAddr_pathTree : ∀ (n : ℕ) (p : List ℕ), RTree.IsAddr (pathTree n) p ↔ p <+: pRep n
  | 0, [] => by simp
  | 0, i :: q => by
      rw [pathTree, RTree.isAddr_cons]
      simp
  | n + 1, [] => by simp
  | n + 1, i :: q => by
      rw [pathTree, RTree.isAddr_cons, pRep, List.replicate_succ, List.cons_prefix_cons, ← pRep]
      constructor
      · rintro ⟨hi, h⟩
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨rfl, (isAddr_pathTree n q).mp (by simpa using h)⟩
      · rintro ⟨rfl, h⟩
        exact ⟨by simp, by simpa using (isAddr_pathTree n q).mpr h⟩

/-- The vertices of the bare-neck shape are the neck vertices. -/
lemma mem_addrList_flatG (n : ℕ) (p : List ℕ) :
    p ∈ RTree.addrList (flatG n).realise ↔ p <+: pRep n := by
  rw [RTree.mem_addrList_iff, flatG_realise, isAddr_pathTree]

section FlatBridge

variable (nk ar : List ℕ → ℕ) {Idx : List ℕ → Prop}
  (hI : PIdx (fun w => flatPiece (nk w) (ar w)) Idx)

include hI in
/-- The plantings of the flat pieces and of the bare-neck shapes agree on the index set. -/
lemma gCopyAddr_flatG {w : List ℕ} (hw : Idx w) :
    gCopyAddr (fun w => flatG (nk w)) w = pCopyAddr (fun w => flatPiece (nk w) (ar w)) w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w j ih =>
      obtain ⟨hw', hj⟩ := hI w j hw
      rw [gCopyAddr_concat, pCopyAddr_concat, ih hw', flatG_exitAddr, flatG_bouquet,
        List.length_nil, Nat.zero_add, flatPiece_root_of_lt (by simpa using hj), List.append_assoc]

/-- The flat assembly inside the assembly of the bare-neck shapes. -/
noncomputable def flatToG (x : PAssembly (fun w => flatPiece (nk w) (ar w)) Idx hI) :
    {y : GAssembly (fun w => flatG (nk w)) // Idx y.copy} :=
  ⟨⟨x.copy, ⟨x.vert.1, (mem_addrList_flatG _ _).mpr x.vert.2⟩⟩, x.idx⟩

/-- **The assembly of the flat configurations is the assembly of the bare-neck shapes over
the index set**, isometrically. -/
theorem flatToG_isometry :
    Function.Bijective (flatToG nk ar hI)
      ∧ ∀ x y, dist (flatToG nk ar hI x) (flatToG nk ar hI y) = dist x y := by
  have hcode : ∀ x : PAssembly (fun w => flatPiece (nk w) (ar w)) Idx hI,
      GAssembly.code (flatToG nk ar hI x).1 = x.code := by
    intro x
    rw [GAssembly.code, PAssembly.code]
    show gCopyAddr (fun w => flatG (nk w)) x.copy ++ x.vert.1 = _
    rw [gCopyAddr_flatG nk ar hI x.idx]
  refine ⟨⟨fun x y h => ?_, fun y => ?_⟩, fun x y => ?_⟩
  · have h1 := hcode x
    rw [h] at h1
    exact PAssembly.code_injective (h1.symm.trans (hcode y))
  · obtain ⟨⟨w, p, hp⟩, hw⟩ := y
    exact ⟨⟨w, hw, ⟨p, (mem_addrList_flatG _ _).mp hp⟩⟩, rfl⟩
  · show dist (flatToG nk ar hI x).1 (flatToG nk ar hI y).1 = _
    rw [GAssembly.dist_code, PAssembly.dist_code, hcode, hcode]

end FlatBridge

/-! ### Quasi-isometries of samples -/

/-- **`def:qi` between two samples**, read in the tree metric of the ambient trees, with
all three constants equal to `K`. -/
def IsSampleQIN (K : ℝ) {N N' : ℕ} {c : GWord N → ℕ} {c' : GWord N' → ℕ}
    (F : {v : GWord N // v ∈ sample c} → {v : GWord N' // v ∈ sample c'}) : Prop :=
  (∀ a b : {v : GWord N // v ∈ sample c}, (BranchingProcess.treeDist (F a).1 (F b).1 : ℝ)
      ≤ K * (BranchingProcess.treeDist a.1 b.1 : ℝ) + K) ∧
    (∀ a b : {v : GWord N // v ∈ sample c}, (BranchingProcess.treeDist a.1 b.1 : ℝ)
      ≤ K * (BranchingProcess.treeDist (F a).1 (F b).1 : ℝ) + K ^ 2) ∧
    ∀ b : {v : GWord N' // v ∈ sample c'}, ∃ a : {v : GWord N // v ∈ sample c},
      (BranchingProcess.treeDist (F a).1 b.1 : ℝ) ≤ K

/-- **The transport to the samples**: a quasi-isometry between two metric spaces each
isometric to a sample is a quasi-isometry of the samples. -/
theorem isSampleQIN_of_isQIMap {N N' : ℕ} {c : GWord N → ℕ} {c' : GWord N' → ℕ}
    {X X' : Type*} [MetricSpace X] [MetricSpace X'] {L : ℝ}
    {Φ : X → {v : GWord N // v ∈ sample c}} (hΦ : Function.Bijective Φ)
    (hΦd : ∀ x y, (BranchingProcess.treeDist (Φ x).1 (Φ y).1 : ℝ) = dist x y)
    {Φ' : X' → {v : GWord N' // v ∈ sample c'}} (hΦ' : Function.Bijective Φ')
    (hΦd' : ∀ x y, (BranchingProcess.treeDist (Φ' x).1 (Φ' y).1 : ℝ) = dist x y)
    {f : X → X'} (hf : IsQIMap L f) :
    ∃ F : {v : GWord N // v ∈ sample c} → {v : GWord N' // v ∈ sample c'}, IsSampleQIN L F := by
  set e := Equiv.ofBijective Φ hΦ
  set e' := Equiv.ofBijective Φ' hΦ'
  have heapp : ∀ x, Φ (e.symm x) = x := fun x ↦ e.apply_symm_apply x
  have heapp' : ∀ x, Φ' (e'.symm x) = x := fun x ↦ e'.apply_symm_apply x
  refine ⟨fun x ↦ Φ' (f (e.symm x)), fun a b ↦ ?_, fun a b ↦ ?_, fun b ↦ ?_⟩
  · rw [hΦd' (f (e.symm a)) (f (e.symm b))]
    have hab : (BranchingProcess.treeDist a.1 b.1 : ℝ) = dist (e.symm a) (e.symm b) := by
      rw [← hΦd (e.symm a) (e.symm b), heapp, heapp]
    rw [hab]
    exact hf.upper _ _
  · rw [hΦd' (f (e.symm a)) (f (e.symm b))]
    have hab : (BranchingProcess.treeDist a.1 b.1 : ℝ) = dist (e.symm a) (e.symm b) := by
      rw [← hΦd (e.symm a) (e.symm b), heapp, heapp]
    rw [hab]
    exact hf.lower _ _
  · obtain ⟨a, ha⟩ := hf.dense (e'.symm b)
    refine ⟨Φ a, ?_⟩
    have hsymm : e.symm (Φ a) = a := e.symm_apply_apply a
    have hd := hΦd' (f a) (e'.symm b)
    rw [heapp' b] at hd
    show (BranchingProcess.treeDist (Φ' (f (e.symm (Φ a)))).1 b.1 : ℝ) ≤ L
    rw [hsymm, hd]
    exact ha

/-- **A quasi-isometry of samples is a quasi-isometry of their graphs**, at the integer
ceiling of the constant. -/
theorem quasiIsometric_of_isSampleQIN {N N' : ℕ} {c : GWord N → ℕ} {c' : GWord N' → ℕ} {K : ℝ}
    (hK : 0 ≤ K) {F : {v : GWord N // v ∈ sample c} → {v : GWord N' // v ∈ sample c'}}
    (hF : IsSampleQIN K F) :
    BranchingProcess.IsQIWith ⌈K⌉₊ (gSampleGraph c) (gSampleGraph c') F := by
  have hle : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
  refine ⟨fun x y => ?_, fun x y => ?_, fun y => ?_⟩
  · rw [wordGraphN_dist (prefixClosedN_sample c'), wordGraphN_dist (prefixClosedN_sample c)]
    have h := hF.1 x y
    have hd : (0 : ℝ) ≤ (BranchingProcess.treeDist x.1 y.1 : ℝ) := Nat.cast_nonneg _
    have : (BranchingProcess.treeDist (F x).1 (F y).1 : ℝ)
        ≤ (⌈K⌉₊ : ℝ) * (BranchingProcess.treeDist x.1 y.1 : ℝ) + ⌈K⌉₊ := by
      nlinarith
    exact_mod_cast this
  · rw [wordGraphN_dist (prefixClosedN_sample c'), wordGraphN_dist (prefixClosedN_sample c)]
    have h := hF.2.1 x y
    have hd : (0 : ℝ) ≤ (BranchingProcess.treeDist (F x).1 (F y).1 : ℝ) := Nat.cast_nonneg _
    have hsq : K ^ 2 ≤ (⌈K⌉₊ : ℝ) * ⌈K⌉₊ := by nlinarith
    have : (BranchingProcess.treeDist x.1 y.1 : ℝ)
        ≤ (⌈K⌉₊ : ℝ) * (BranchingProcess.treeDist (F x).1 (F y).1 : ℝ) + ⌈K⌉₊ * ⌈K⌉₊ := by
      nlinarith
    exact_mod_cast this
  · obtain ⟨x, hx⟩ := hF.2.2 y
    refine ⟨x, ?_⟩
    rw [wordGraphN_dist (prefixClosedN_sample c')]
    exact_mod_cast hx.trans hle


/-! ### The deterministic core of `thm:chain-general` -/

/-- **The flattening scale** of a presentation with revealing depth `R` and stopping bound
`T`: the glued flattening is a quasi-isometry at `8(2R(T + 2) + 1)²`. -/
def flatScale (R T : ℕ) : ℝ := 8 * (2 * (R * (T + 2) : ℕ) + 1) ^ 2

lemma one_le_flatScale (R T : ℕ) : 1 ≤ flatScale R T := by
  rw [flatScale]
  have : (0 : ℝ) ≤ (R * (T + 2) : ℕ) := Nat.cast_nonneg _
  nlinarith

section Endpoint

variable [NeZero N] {N' : ℕ} [NeZero N'] (R : ℕ) {σ σ' : Type*} (ρr : BRule σ) (ρr' : BRule σ')

/-- **The deterministic core of `thm:chain-general`**, abstractly over the encoded
assemblies.  Two chain-regime samples are presented by blob rules with revealing depth
`R`.  Each sample is isometric to the assembly of its presented blobs over its presented
skeleton, which the glued flattening carries to the assembly of the flat configurations at
the flattening scale.  Given quasi-isometries of the two flat assemblies with two spaces
`B`, `B'` (the `𝔹`-assemblies of the cascade encoding) at a constant `Cenc`, and a
quasi-isometry `B → B'` at a constant `Cm` (the glued transfer over `𝔹` of the matched
flat blobs, after the automorphism), the two samples are quasi-isometric at the composite
constant. -/
theorem sample_qi_of_blob_matching (hR : 1 ≤ R)
    {ω : (GWord N → ℕ) × (List ℕ → σ)} {ω' : (GWord N' → ℕ) × (List ℕ → σ')}
    (hd : IsChainField N ω.1) (hd' : IsChainField N' ω'.1)
    {B B' : Type*} [MetricSpace B] [MetricSpace B'] {Cenc Cm : ℝ} (hCenc : 1 ≤ Cenc)
    (hCm : 1 ≤ Cm)
    {e : PAssembly (flatAt R ρr ω) (Presented R ρr ω) (flat_pIdx R ρr ω) → B}
    (he : IsQIMap Cenc e)
    {e' : PAssembly (flatAt R ρr' ω') (Presented R ρr' ω') (flat_pIdx R ρr' ω') → B'}
    (he' : IsQIMap Cenc e') {g : B → B'} (hg : IsQIMap Cm g) :
    ∃ F : {v : GWord N // v ∈ sample ω.1} → {v : GWord N' // v ∈ sample ω'.1},
      IsSampleQIN (3 * (3 * (3 * (3 * flatScale R ρr.T * Cenc) * Cm) * (3 * Cenc ^ 2))
        * (3 * flatScale R ρr'.T ^ 2)) F := by
  have hK₁ := one_le_flatScale R ρr.T
  have hK₁' := one_le_flatScale R ρr'.T
  obtain ⟨g₁, hg₁⟩ := blob_flat_glued R ρr hR hd
  obtain ⟨g₁', hg₁'⟩ := blob_flat_glued R ρr' hR hd'
  obtain ⟨g₂, hg₂⟩ := hg₁'.exists_symm hK₁'
  obtain ⟨e₂, he₂⟩ := he'.exists_symm hCenc
  have h1 := IsQIMap.comp hK₁ hCenc hg₁ he
  have h1K : (1 : ℝ) ≤ 3 * flatScale R ρr.T * Cenc := by nlinarith
  have h2 := IsQIMap.comp h1K hCm h1 hg
  have h2K : (1 : ℝ) ≤ 3 * (3 * flatScale R ρr.T * Cenc) * Cm := by nlinarith
  have h3K : (1 : ℝ) ≤ 3 * Cenc ^ 2 := by nlinarith
  have h3 := IsQIMap.comp h2K h3K h2 he₂
  have h4K : (1 : ℝ) ≤ 3 * (3 * (3 * flatScale R ρr.T * Cenc) * Cm) * (3 * Cenc ^ 2) := by
    nlinarith
  have h5K : (1 : ℝ) ≤ 3 * flatScale R ρr'.T ^ 2 := by nlinarith
  have h4 := IsQIMap.comp h4K h5K h3 hg₂
  obtain ⟨Φ, hΦ, hΦd⟩ := blobAssembly_isometric_sample R ρr hR hd
  obtain ⟨Φ', hΦ', hΦd'⟩ := blobAssembly_isometric_sample R ρr' hR hd'
  exact isSampleQIN_of_isQIMap hΦ hΦd hΦ' hΦd' h4

/-- The two samples, as graphs, are quasi-isometric. -/
theorem quasiIsometric_of_blob_matching (hR : 1 ≤ R)
    {ω : (GWord N → ℕ) × (List ℕ → σ)} {ω' : (GWord N' → ℕ) × (List ℕ → σ')}
    (hd : IsChainField N ω.1) (hd' : IsChainField N' ω'.1)
    {B B' : Type*} [MetricSpace B] [MetricSpace B'] {Cenc Cm : ℝ} (hCenc : 1 ≤ Cenc)
    (hCm : 1 ≤ Cm)
    {e : PAssembly (flatAt R ρr ω) (Presented R ρr ω) (flat_pIdx R ρr ω) → B}
    (he : IsQIMap Cenc e)
    {e' : PAssembly (flatAt R ρr' ω') (Presented R ρr' ω') (flat_pIdx R ρr' ω') → B'}
    (he' : IsQIMap Cenc e') {g : B → B'} (hg : IsQIMap Cm g) :
    BranchingProcess.QuasiIsometric (gSampleGraph ω.1) (gSampleGraph ω'.1) := by
  obtain ⟨F, hF⟩ := sample_qi_of_blob_matching R ρr ρr' hR hd hd' hCenc hCm he he' hg
  have hK₁ := one_le_flatScale R ρr.T
  have hK₁' := one_le_flatScale R ρr'.T
  refine ⟨_, F, quasiIsometric_of_isSampleQIN ?_ hF⟩
  positivity

end Endpoint

end ChainClasses

