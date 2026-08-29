/-
`thm:chain-general` of `trichotomy.tex`, the deterministic core: the glued transfer of
`it:general-glued` over the presented skeleton with the flat blob configurations in place
of the shapes, and the identification of a chain-regime sample with the assembly of its
presented blobs.

A presented blob of `def:blob` is a finite subtree of the reduced skeleton with several
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
* `pRep`, `flatPiece`, `collapseAddr`, `IsNeckPiece`, `collapse`, `isPortQI_collapse`,
  `portQI_flat_symm`: **`thm:matched-presentation`\labelcref{it:matched-flat}** in the
  abstract: a neck piece of depth `Δ` beyond its far end is `(2Δ + 1)`-port comparable to
  its flat configuration, and conversely.
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
  `blob_flat_glued`: **`thm:matched-presentation`\labelcref{it:matched-flat}** for the
  presented blobs, at `2R(T + 2) + 1`, and the glued flattening at `flatScale R T`.
* `flatG`, `pathTree`, `flatG_exitAddr`, `mem_addrList_flatG`, `flatToG`,
  `flatToG_isometry`: the flat configurations are the bare-neck shapes, and the flat
  assembly is the assembly of those shapes over the presented skeleton.
* `IsQIMap.symm` (with `IsQIMap.comp` of `BAssembly`), `IsSampleQIN`, `isSampleQIN_of_isQIMap`,
  `quasiIsometric_of_isSampleQIN`: quasi-isometries compose and invert, and transport to
  the samples and their graphs.
* `sample_qi_of_blob_matching`, `sample_qi_of_blob_matching'`,
  `quasiIsometric_of_blob_matching`: **`thm:chain-general`, the deterministic core**: given
  quasi-isometries of the two flat assemblies with the `𝔹`-assemblies of the cascade
  encoding and a quasi-isometry between those, or the per-copy comparability of the
  encoded flat blobs after the automorphism, the two samples are quasi-isometric at an
  explicit constant.
-/
import ChainClasses.GeneralAssembly
import ChainClasses.BlobField
import ChainClasses.BlobRoot
import ChainClasses.GeneralObstructions
import ChainClasses.MatchedPresentation
import ChainClasses.ChainCross
import ChainClasses.AssemblyRelabel
import ChainClasses.GeneralCascade
import ChainClasses.BAssembly

namespace ChainClasses

/-! ### Pieces: finite trees with an entry and a list of ports -/

/-- **A piece**: a prefix-closed set of addresses, read as a rooted tree with the root as
its entry, together with a list of ports, each an address of the piece paired with a free
child index at which a copy is planted; the planted child is no address of the piece, and
distinct ports plant at distinct children. -/
structure Piece where
  /-- The addresses of the piece. -/
  mem : List ℕ → Prop
  /-- The root is an address. -/
  nil_mem : mem []
  /-- The address set is closed under prefixes. -/
  mem_of_prefix : ∀ {p q : List ℕ}, p <+: q → mem q → mem p
  /-- The ports, each with the free child index at which a copy is planted. -/
  ports : List (List ℕ × ℕ)
  /-- Every port is an address. -/
  port_mem : ∀ x ∈ ports, mem x.1
  /-- The child at which a copy is planted is no address of the piece. -/
  slot_free : ∀ x ∈ ports, ¬ mem (x.1 ++ [x.2])
  /-- Distinct ports plant at distinct children. -/
  ports_nodup : ports.Nodup

namespace Piece

/-- The vertices of a piece. -/
def carrier (X : Piece) : Type := {p : List ℕ // X.mem p}

/-- The number of ports. -/
def nports (X : Piece) : ℕ := X.ports.length

/-- The `j`-th port with its slot, the root with slot `0` past the last port. -/
def portSlot (X : Piece) (j : ℕ) : List ℕ × ℕ := X.ports.getD j ([], 0)

/-- The address of the `j`-th port. -/
def port (X : Piece) (j : ℕ) : List ℕ := (X.portSlot j).1

/-- The slot of the `j`-th port. -/
def slot (X : Piece) (j : ℕ) : ℕ := (X.portSlot j).2

/-- The address at which the copy planted at the `j`-th port sits: the port followed by
its slot. -/
def root (X : Piece) (j : ℕ) : List ℕ := X.port j ++ [X.slot j]

lemma portSlot_mem {X : Piece} {j : ℕ} (hj : j < X.nports) : X.portSlot j ∈ X.ports := by
  rw [portSlot, List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma portSlot_of_le {X : Piece} {j : ℕ} (hj : X.nports ≤ j) : X.portSlot j = ([], 0) :=
  List.getD_eq_default _ _ hj

/-- Every port, the junk ports included, is an address. -/
lemma port_mem' (X : Piece) (j : ℕ) : X.mem (X.port j) := by
  rcases lt_or_ge j X.nports with hj | hj
  · exact X.port_mem _ (portSlot_mem hj)
  · rw [port, portSlot_of_le hj]
    exact X.nil_mem

/-- Below the port count the planted child is no address. -/
lemma root_not_mem {X : Piece} {j : ℕ} (hj : j < X.nports) : ¬ X.mem (X.root j) :=
  X.slot_free _ (portSlot_mem hj)

/-- Distinct ports below the port count plant at distinct children. -/
lemma root_ne {X : Piece} {a b : ℕ} (ha : a < X.nports) (hb : b < X.nports) (hab : a ≠ b) :
    X.root a ≠ X.root b := by
  intro h
  have h1 : X.portSlot a = X.portSlot b := by
    have hp : X.port a = X.port b := by
      have := congrArg List.dropLast h
      simpa [root] using this
    have hs : X.slot a = X.slot b := by
      have := congrArg (fun l => l.getLast?) h
      simpa [root] using this
    exact Prod.ext hp hs
  rw [portSlot, portSlot, List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb] at h1
  exact hab (List.Nodup.getElem_inj_iff X.ports_nodup |>.mp h1)

/-- **The wedge through a port**: the wedge of an address of the piece with an address
reaching past a port into the planted child is its wedge with the port. -/
lemma wedgeN_eq_wedgeN_port (X : Piece) {p r : List ℕ} {j : ℕ} (hj : j < X.nports)
    (hp : X.mem p) (hr : X.root j <+: r) :
    wedgeN p r = wedgeN p (X.port j) := by
  have hnr : X.port j <+: r := (List.prefix_append _ _).trans hr
  have hg1 : wedgeN p (X.port j) <+: p := wedgeN_prefix_left _ _
  have hg2 : wedgeN p (X.port j) <+: X.port j := wedgeN_prefix_right _ _
  have hle : wedgeN p (X.port j) <+: wedgeN p r := prefix_wedgeN hg1 (hg2.trans hnr)
  rcases List.prefix_or_prefix_of_prefix (wedgeN_prefix_right p r) hnr with h | h
  · have h2 : wedgeN p r <+: wedgeN p (X.port j) := prefix_wedgeN (wedgeN_prefix_left p r) h
    exact h2.eq_of_length (le_antisymm h2.length_le hle.length_le)
  · have hnp : X.port j <+: p := h.trans (wedgeN_prefix_left p r)
    obtain ⟨v, rfl⟩ := hnp
    cases v with
    | nil =>
        rw [List.append_nil, wedgeN_of_prefix hnr, wedgeN_self]
    | cons i v =>
        have hne : i ≠ X.slot j := by
          intro hi
          subst hi
          exact root_not_mem hj (X.mem_of_prefix ⟨v, by simp [root]⟩ hp)
        rw [wedgeN_of_diverge hne ⟨v, by simp⟩ hr, wedgeN_comm,
          wedgeN_of_prefix (List.prefix_append _ _)]

/-- **The wedge of two planted children**: two addresses reaching past distinct ports into
their planted children meet at the wedge of the two ports. -/
lemma wedgeN_root_root (X : Piece) {a b : ℕ} (ha : a < X.nports) (hb : b < X.nports)
    (hab : a ≠ b) {r r' : List ℕ} (hr : X.root a <+: r) (hr' : X.root b <+: r') :
    wedgeN r r' = wedgeN (X.port a) (X.port b) := by
  have hpa : X.port a <+: r := (List.prefix_append _ _).trans hr
  have hpb : X.port b <+: r' := (List.prefix_append _ _).trans hr'
  by_cases h1 : X.port a <+: X.port b
  · rw [wedgeN_of_prefix h1]
    obtain ⟨v, hv⟩ := h1
    cases v with
    | nil =>
        rw [List.append_nil] at hv
        have hs : X.slot a ≠ X.slot b := by
          intro hs
          exact root_ne ha hb hab (by rw [root, root, hv, hs])
        exact wedgeN_of_diverge hs hr (hv ▸ hr')
    | cons i v =>
        have hne : X.slot a ≠ i := by
          intro hi
          subst hi
          exact root_not_mem ha (X.mem_of_prefix ⟨v, by rw [root, ← hv]; simp⟩
            (X.port_mem' b))
        exact wedgeN_of_diverge hne hr ((show X.port a ++ [i] <+: X.port b from
          ⟨v, by rw [← hv]; simp⟩).trans hpb)
  · by_cases h2 : X.port b <+: X.port a
    · rw [wedgeN_comm (X.port a), wedgeN_of_prefix h2]
      obtain ⟨v, hv⟩ := h2
      cases v with
      | nil =>
          rw [List.append_nil] at hv
          exact absurd (hv ▸ List.prefix_refl _) h1
      | cons i v =>
          have hne : X.slot b ≠ i := by
            intro hi
            subst hi
            exact root_not_mem hb (X.mem_of_prefix ⟨v, by rw [root, ← hv]; simp⟩
              (X.port_mem' a))
          rw [wedgeN_comm]
          exact wedgeN_of_diverge hne hr' ((show X.port b ++ [i] <+: X.port a from
            ⟨v, by rw [← hv]; simp⟩).trans hpa)
    · obtain ⟨z, i, i', hii', hzi, hzi'⟩ := exists_divergeN h1 h2
      rw [wedgeN_of_diverge hii' hzi hzi', wedgeN_of_diverge hii' (hzi.trans hpa) (hzi'.trans hpb)]

/-- The metric of a piece: the address metric. -/
noncomputable instance instMetricSpace (X : Piece) : MetricSpace X.carrier where
  dist x y := (addrDist x.1 y.1 : ℝ)
  dist_self x := by simp
  dist_comm x y := by simp only [addrDist_comm x.1 y.1]
  dist_triangle x y z := by
    have := addrDist_triangle x.1 y.1 z.1
    exact_mod_cast this
  eq_of_dist_eq_zero {x y} h := by
    have h0 : addrDist x.1 y.1 = 0 := by exact_mod_cast h
    exact Subtype.ext (addrDist_eq_zero_iff.mp h0)

@[simp] lemma dist_carrier {X : Piece} (x y : X.carrier) :
    dist x y = (addrDist x.1 y.1 : ℝ) := rfl

/-- The entry of a piece: its root. -/
def entry (X : Piece) : X.carrier := ⟨[], X.nil_mem⟩

/-- The `j`-th port of a piece as a vertex. -/
def portVert (X : Piece) (j : ℕ) : X.carrier := ⟨X.port j, X.port_mem' j⟩

@[simp] lemma entry_val (X : Piece) : (X.entry).1 = [] := rfl

@[simp] lemma portVert_val (X : Piece) (j : ℕ) : (X.portVert j).1 = X.port j := rfl

end Piece

/-! ### Multi-marked spaces and port quasi-isometries -/

/-- A metric space with an entry and a sequence of ports, the abstract stand-in for a piece
with its entry and its ports; the ports past the port count of a piece are its entry. -/
structure PortSpace where
  carrier : Type
  [str : MetricSpace carrier]
  entry : carrier
  port : ℕ → carrier

attribute [instance] PortSpace.str

/-- The port space of a piece. -/
noncomputable def Piece.space (X : Piece) : PortSpace where
  carrier := X.carrier
  entry := X.entry
  port := X.portVert

@[simp] lemma Piece.space_entry (X : Piece) : X.space.entry = X.entry := rfl

@[simp] lemma Piece.space_port (X : Piece) (j : ℕ) : X.space.port j = X.portVert j := rfl

/-- `f` is a `K`-port quasi-isometry: a `K`-quasi-isometry moving the entry and every port
by at most `K`. -/
structure IsPortQI (K : ℝ) (X Y : PortSpace) (f : X.carrier → Y.carrier) : Prop where
  upper : ∀ a b, dist (f a) (f b) ≤ K * dist a b + K
  lower : ∀ a b, dist a b ≤ K * dist (f a) (f b) + K * K
  dense : ∀ y, ∃ a, dist (f a) y ≤ K
  entry : dist (f X.entry) Y.entry ≤ K
  port : ∀ j, dist (f (X.port j)) (Y.port j) ≤ K

/-- `X` and `Y` are `K`-port comparable. -/
def PortQI (K : ℝ) (X Y : PortSpace) : Prop := ∃ f, IsPortQI K X Y f

/-- A port space read as a marked space with the `j`-th port as its exit. -/
def PortSpace.toMarked (X : PortSpace) (j : ℕ) : MarkedSpace :=
  ⟨X.carrier, X.entry, X.port j⟩

/-- A port quasi-isometry is a marked quasi-isometry for every port. -/
lemma IsPortQI.toMarked {K : ℝ} {X Y : PortSpace} {f : X.carrier → Y.carrier}
    (hf : IsPortQI K X Y f) (j : ℕ) : IsMarkedQI K (X.toMarked j) (Y.toMarked j) f :=
  ⟨hf.upper, hf.lower, hf.dense, hf.entry, hf.port j⟩

/-- The composition of a `K`-port and a `K'`-port quasi-isometry is `3KK'`-port. -/
lemma IsPortQI.comp {K K' : ℝ} {X Y Z : PortSpace} (hK : 1 ≤ K) (hK' : 1 ≤ K')
    {f : X.carrier → Y.carrier} {g : Y.carrier → Z.carrier}
    (hf : IsPortQI K X Y f) (hg : IsPortQI K' Y Z g) :
    IsPortQI (3 * K * K') X Z (fun x => g (f x)) := by
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  have hK'0 : (0 : ℝ) ≤ K' := zero_le_one.trans hK'
  refine ⟨fun a b => ?_, fun a b => ?_, fun z => ?_, ?_, fun j => ?_⟩
  · have h1 := hg.upper (f a) (f b)
    have h2 : K' * dist (f a) (f b) ≤ K' * (K * dist a b + K) :=
      mul_le_mul_of_nonneg_left (hf.upper a b) hK'0
    nlinarith [mul_nonneg (mul_nonneg hK0 hK'0) (dist_nonneg (x := a) (y := b))]
  · have h1 := hf.lower a b
    have h2 : K * dist (f a) (f b) ≤ K * (K' * dist (g (f a)) (g (f b)) + K' * K') :=
      mul_le_mul_of_nonneg_left (hg.lower (f a) (f b)) hK0
    have hK'2 : (1 : ℝ) ≤ K' * K' := by nlinarith
    have e1 : K * (K' * K') ≤ K * K' * (K * K') := by
      nlinarith [mul_nonneg (mul_nonneg hK'0 hK'0) hK0]
    have e2 : K * K ≤ K * K' * (K * K') := by nlinarith [mul_nonneg hK0 hK0]
    nlinarith [mul_nonneg (mul_nonneg hK0 hK'0) (dist_nonneg (x := g (f a)) (y := g (f b))),
      mul_nonneg (mul_nonneg hK0 hK'0) (mul_nonneg hK0 hK'0)]
  · obtain ⟨y, hy⟩ := hg.dense z
    obtain ⟨a, ha⟩ := hf.dense y
    refine ⟨a, ?_⟩
    have htri : dist (g (f a)) z ≤ dist (g (f a)) (g y) + dist (g y) z := dist_triangle _ _ _
    have h1 := hg.upper (f a) y
    have h2 : K' * dist (f a) y ≤ K' * K := mul_le_mul_of_nonneg_left ha hK'0
    nlinarith
  · have htri : dist (g (f X.entry)) Z.entry
        ≤ dist (g (f X.entry)) (g Y.entry) + dist (g Y.entry) Z.entry := dist_triangle _ _ _
    have h1 := hg.upper (f X.entry) Y.entry
    have h2 : K' * dist (f X.entry) Y.entry ≤ K' * K :=
      mul_le_mul_of_nonneg_left hf.entry hK'0
    have h3 := hg.entry
    nlinarith
  · have htri : dist (g (f (X.port j))) (Z.port j)
        ≤ dist (g (f (X.port j))) (g (Y.port j)) + dist (g (Y.port j)) (Z.port j) :=
      dist_triangle _ _ _
    have h1 := hg.upper (f (X.port j)) (Y.port j)
    have h2 : K' * dist (f (X.port j)) (Y.port j) ≤ K' * K :=
      mul_le_mul_of_nonneg_left (hf.port j) hK'0
    have h3 := hg.port j
    nlinarith

/-- A `K`-port quasi-isometry has a `3K²`-port quasi-inverse. -/
lemma IsPortQI.symm {K : ℝ} {X Y : PortSpace} (hK : 1 ≤ K) {f : X.carrier → Y.carrier}
    (hf : IsPortQI K X Y f) : ∃ g : Y.carrier → X.carrier, IsPortQI (3 * K ^ 2) Y X g := by
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  choose g hg using hf.dense
  have hmark : ∀ (mX : X.carrier) (mY : Y.carrier), dist (f mX) mY ≤ K →
      dist (g mY) mX ≤ 3 * K ^ 2 := by
    intro mX mY hm
    have h1 := hf.lower (g mY) mX
    have h2 : dist (f (g mY)) (f mX) ≤ dist (f (g mY)) mY + dist mY (f mX) := dist_triangle _ _ _
    have h3 : dist mY (f mX) ≤ K := by rw [dist_comm]; exact hm
    have h4 : K * dist (f (g mY)) (f mX) ≤ K * (dist (f (g mY)) mY + dist mY (f mX)) :=
      mul_le_mul_of_nonneg_left h2 hK0
    have h5 : K * dist (f (g mY)) mY ≤ K * K := mul_le_mul_of_nonneg_left (hg mY) hK0
    have h6 : K * dist mY (f mX) ≤ K * K := mul_le_mul_of_nonneg_left h3 hK0
    nlinarith
  refine ⟨g, fun a b => ?_, fun a b => ?_, fun x => ?_, hmark _ _ hf.entry,
    fun j => hmark _ _ (hf.port j)⟩
  · have h1 := hf.lower (g a) (g b)
    have h2 : dist (f (g a)) (f (g b)) ≤ dist (f (g a)) a + dist a b + dist b (f (g b)) :=
      dist_triangle4 _ _ _ _
    have h3 : dist b (f (g b)) ≤ K := by rw [dist_comm]; exact hg b
    have h4 : K * dist (f (g a)) (f (g b))
        ≤ K * (dist (f (g a)) a + dist a b + dist b (f (g b))) :=
      mul_le_mul_of_nonneg_left h2 hK0
    have h5 : K * dist (f (g a)) a ≤ K * K := mul_le_mul_of_nonneg_left (hg a) hK0
    have h6 : K * dist b (f (g b)) ≤ K * K := mul_le_mul_of_nonneg_left h3 hK0
    nlinarith [mul_nonneg (mul_nonneg hK0 (sub_nonneg.mpr hK)) (dist_nonneg (x := a) (y := b)),
      mul_nonneg (mul_nonneg hK0 hK0) (dist_nonneg (x := a) (y := b))]
  · have h2 : dist a b ≤ dist a (f (g a)) + dist (f (g a)) (f (g b)) + dist (f (g b)) b :=
      dist_triangle4 _ _ _ _
    have h3 : dist a (f (g a)) ≤ K := by rw [dist_comm]; exact hg a
    have h4 := hf.upper (g a) (g b)
    nlinarith [hg b,
      mul_nonneg (mul_nonneg hK0 (sub_nonneg.mpr hK)) (dist_nonneg (x := g a) (y := g b)),
      mul_nonneg (mul_nonneg hK0 hK0) (dist_nonneg (x := g a) (y := g b)),
      mul_nonneg hK0 (sub_nonneg.mpr (one_le_pow₀ hK (n := 3))), pow_nonneg hK0 4]
  · refine ⟨f x, ?_⟩
    have h1 := hf.lower (g (f x)) x
    have h2 : K * dist (f (g (f x))) (f x) ≤ K * K :=
      mul_le_mul_of_nonneg_left (hg (f x)) hK0
    nlinarith [sq_nonneg K]

/-! ### The assembly of a family of pieces -/

/-- The letter of an index word at a position, `0` past its end. -/
def letterAt (v : List ℕ) (i : ℕ) : ℕ := v.getD i 0

lemma letterAt_append_left {u : List ℕ} (t : List ℕ) {i : ℕ} (hi : i < u.length) :
    letterAt (u ++ t) i = letterAt u i := by
  rw [letterAt, letterAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi]

lemma letterAt_append_cons (u : List ℕ) (a : ℕ) (t : List ℕ) :
    letterAt (u ++ a :: t) u.length = a := by
  rw [letterAt, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

lemma letterAt_take {v : List ℕ} {i n : ℕ} (hi : i < n) : letterAt (v.take n) i = letterAt v i := by
  rw [letterAt, letterAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hi]

/-- The address at which the copy at `w` is planted: the copy at `w ++ [j]` hangs at the
root planted at the `j`-th port of the copy at `w`. -/
def pCopyAddr (σ : List ℕ → Piece) (w : List ℕ) : List ℕ :=
  (w.foldl (fun p j => (p.1 ++ [j], p.2 ++ (σ p.1).root j)) (([] : List ℕ), ([] : List ℕ))).2

lemma pCopyAddr_foldl_fst (σ : List ℕ → Piece) (w a b : List ℕ) :
    (w.foldl (fun p j => (p.1 ++ [j], p.2 ++ (σ p.1).root j)) (a, b)).1 = a ++ w := by
  induction w generalizing a b with
  | nil => simp
  | cons j t ih => simpa using ih (a ++ [j]) (b ++ (σ a).root j)

@[simp] lemma pCopyAddr_nil (σ : List ℕ → Piece) : pCopyAddr σ [] = [] := rfl

/-- The recursion of the assembly. -/
lemma pCopyAddr_concat (σ : List ℕ → Piece) (w : List ℕ) (j : ℕ) :
    pCopyAddr σ (w ++ [j]) = pCopyAddr σ w ++ (σ w).root j := by
  have h := pCopyAddr_foldl_fst σ w [] []
  rw [List.nil_append] at h
  simp only [pCopyAddr, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [h]

lemma pCopyAddr_prefix (σ : List ℕ → Piece) {w w' : List ℕ} (h : w <+: w') :
    pCopyAddr σ w <+: pCopyAddr σ w' := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc]
      calc pCopyAddr σ w <+: pCopyAddr σ (w ++ u) := ih
        _ <+: pCopyAddr σ (w ++ u ++ [j]) := by
            rw [pCopyAddr_concat]
            exact List.prefix_append _ _

/-- **The neck length of a copy toward a letter**: the depth of the port the letter uses,
plus one for the edge into the planted child. -/
def pNeck (σ : List ℕ → Piece) (t : List ℕ) (a : ℕ) : ℕ := ((σ t).port a).length + 1

lemma one_le_pNeck (σ : List ℕ → Piece) (t : List ℕ) (a : ℕ) :
    (1 : ℝ) ≤ (pNeck σ t a : ℝ) := by
  rw [pNeck]; push_cast; linarith [(Nat.cast_nonneg ((σ t).port a).length : (0 : ℝ) ≤ _)]

/-- The depth of a copy is the total neck length of the copies above it, each toward the
letter the index word uses there. -/
lemma pCopyAddr_length (σ : List ℕ → Piece) (w : List ℕ) :
    (pCopyAddr σ w).length
      = ∑ i ∈ Finset.range w.length, pNeck σ (w.take i) (letterAt w i) := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w j ih =>
      have hcong : ∀ i ∈ Finset.range w.length,
          pNeck σ ((w ++ [j]).take i) (letterAt (w ++ [j]) i) = pNeck σ (w.take i) (letterAt w i) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [List.take_append_of_le_length (by omega), letterAt_append_left _ hi]
      rw [pCopyAddr_concat]
      simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
      rw [Finset.sum_congr rfl hcong, List.take_left, ← ih, letterAt_append_cons, Piece.root,
        List.length_append, List.length_singleton, pNeck]

/-- **The neck sum**: the total neck length of the copies strictly between `u` and `v`,
each toward the letter `v` uses there. -/
def pNeckSum (σ : List ℕ → Piece) (u v : List ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico (u.length + 1) v.length, pNeck σ (v.take i) (letterAt v i)

/-- The depth increment from a copy to a copy below it. -/
lemma pCopyAddr_length_of_prefix (σ : List ℕ → Piece) {u v : List ℕ} (huv : u <+: v)
    (hne : u ≠ v) :
    (pCopyAddr σ v).length
      = (pCopyAddr σ u).length + pNeck σ u (letterAt v u.length) + pNeckSum σ u v := by
  have hlt : u.length < v.length := by
    rcases huv.length_le.lt_or_eq with h | h
    · exact h
    · exact absurd (huv.eq_of_length h) hne
  have hu : u = v.take u.length := List.prefix_iff_eq_take.mp huv
  have hlow : ∀ i ∈ Finset.range u.length,
      pNeck σ (v.take i) (letterAt v i) = pNeck σ (u.take i) (letterAt u i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hu, List.take_take, Nat.min_eq_left hi.le, letterAt_take hi]
  have hsplit : ∑ i ∈ Finset.range v.length, pNeck σ (v.take i) (letterAt v i)
      = (∑ i ∈ Finset.range u.length, pNeck σ (v.take i) (letterAt v i))
        + ∑ i ∈ Finset.Ico u.length v.length, pNeck σ (v.take i) (letterAt v i) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) hlt.le]
  have hbot : ∑ i ∈ Finset.Ico u.length v.length, pNeck σ (v.take i) (letterAt v i)
      = pNeck σ u (letterAt v u.length) + pNeckSum σ u v := by
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt, ← hu]
    rfl
  rw [pCopyAddr_length, pCopyAddr_length, hsplit, hbot, Finset.sum_congr rfl hlow]
  omega

/-! ### The distance formulas at the level of addresses -/

/-- **The ancestor formula**, at the level of addresses: from an address of the copy at `u`
to an address of a copy strictly below it, through the port the index word uses at `u`. -/
lemma addrDist_pCopyAddr_anc (σ : List ℕ → Piece) {u : List ℕ} {a : ℕ} {t : List ℕ}
    (ha : a < (σ u).nports) {p : List ℕ} (hp : (σ u).mem p) (q : List ℕ) :
    addrDist (pCopyAddr σ u ++ p) (pCopyAddr σ (u ++ a :: t) ++ q)
      = addrDist p ((σ u).port a) + 1 + pNeckSum σ u (u ++ a :: t) + q.length := by
  have hne : u ≠ u ++ a :: t := by simp
  have hstep : pCopyAddr σ u ++ (σ u).root a <+: pCopyAddr σ (u ++ a :: t) := by
    rw [← pCopyAddr_concat]
    exact pCopyAddr_prefix σ ⟨t, by simp⟩
  obtain ⟨r, hr⟩ := hstep
  have hcode : pCopyAddr σ (u ++ a :: t) ++ q
      = pCopyAddr σ u ++ ((σ u).root a ++ (r ++ q)) := by
    rw [← hr]; simp only [List.append_assoc]
  have hw : wedgeN (pCopyAddr σ u ++ p) (pCopyAddr σ u ++ ((σ u).root a ++ (r ++ q)))
      = pCopyAddr σ u ++ wedgeN p ((σ u).port a) := by
    rw [wedgeN_append_append, (σ u).wedgeN_eq_wedgeN_port ha hp (List.prefix_append _ _)]
  have h1 := addrDist_add_wedgeN_length (pCopyAddr σ u ++ p)
    (pCopyAddr σ u ++ ((σ u).root a ++ (r ++ q)))
  rw [hw] at h1
  have h2 := addrDist_add_wedgeN_length p ((σ u).port a)
  have hrlen := congrArg List.length hr
  have hroot : ((σ u).root a).length = ((σ u).port a).length + 1 := by
    simp [Piece.root]
  simp only [List.length_append] at hrlen
  have hlen := pCopyAddr_length_of_prefix σ (u := u) (v := u ++ a :: t) ⟨a :: t, rfl⟩ hne
  rw [letterAt_append_cons, pNeck] at hlen
  rw [hcode]
  simp only [List.length_append] at h1
  omega

/-- **The divergent formula**, at the level of addresses: from an address of the copy at
`z ++ a :: s` to one of the copy at `z ++ b :: t`, `a ≠ b`, the two branches climb to the
entries of their copies, traverse the intermediate copies, and meet in the copy at `z`,
between the two ports the letters `a` and `b` use. -/
lemma addrDist_pCopyAddr_div (σ : List ℕ → Piece) {z : List ℕ} {a b : ℕ} {s t : List ℕ}
    (hab : a ≠ b) (ha : a < (σ z).nports) (hb : b < (σ z).nports) (p q : List ℕ) :
    addrDist (pCopyAddr σ (z ++ a :: s) ++ p) (pCopyAddr σ (z ++ b :: t) ++ q)
      = p.length + q.length + 2 + pNeckSum σ z (z ++ a :: s) + pNeckSum σ z (z ++ b :: t)
        + addrDist ((σ z).port a) ((σ z).port b) := by
  have hzu : z <+: z ++ a :: s := ⟨a :: s, rfl⟩
  have hzv : z <+: z ++ b :: t := ⟨b :: t, rfl⟩
  have hzune : z ≠ z ++ a :: s := by simp
  have hzvne : z ≠ z ++ b :: t := by simp
  have hpu : pCopyAddr σ z ++ (σ z).root a <+: pCopyAddr σ (z ++ a :: s) := by
    rw [← pCopyAddr_concat]
    exact pCopyAddr_prefix σ ⟨s, by simp⟩
  have hpv : pCopyAddr σ z ++ (σ z).root b <+: pCopyAddr σ (z ++ b :: t) := by
    rw [← pCopyAddr_concat]
    exact pCopyAddr_prefix σ ⟨t, by simp⟩
  obtain ⟨r, hr⟩ := hpu
  obtain ⟨r', hr'⟩ := hpv
  have hcu : pCopyAddr σ (z ++ a :: s) ++ p = pCopyAddr σ z ++ ((σ z).root a ++ (r ++ p)) := by
    rw [← hr]; simp only [List.append_assoc]
  have hcv : pCopyAddr σ (z ++ b :: t) ++ q = pCopyAddr σ z ++ ((σ z).root b ++ (r' ++ q)) := by
    rw [← hr']; simp only [List.append_assoc]
  have hw : wedgeN (pCopyAddr σ (z ++ a :: s) ++ p) (pCopyAddr σ (z ++ b :: t) ++ q)
      = pCopyAddr σ z ++ wedgeN ((σ z).port a) ((σ z).port b) := by
    rw [hcu, hcv, wedgeN_append_append,
      (σ z).wedgeN_root_root ha hb hab (List.prefix_append _ _) (List.prefix_append _ _)]
  have h1 := addrDist_add_wedgeN_length (pCopyAddr σ (z ++ a :: s) ++ p)
    (pCopyAddr σ (z ++ b :: t) ++ q)
  rw [hw] at h1
  have h2 := addrDist_add_wedgeN_length ((σ z).port a) ((σ z).port b)
  have hlenu := pCopyAddr_length_of_prefix σ hzu hzune
  have hlenv := pCopyAddr_length_of_prefix σ hzv hzvne
  rw [letterAt_append_cons, pNeck] at hlenu hlenv
  simp only [List.length_append] at h1
  omega

/-! ### The assembly as a metric space -/

/-- **An index set for a family of pieces**: a set of index words in which the child
`w ++ [j]` is indexed only when `w` is and `j` is below the port count of the piece at
`w`. -/
def PIdx (σ : List ℕ → Piece) (Idx : List ℕ → Prop) : Prop :=
  ∀ w j, Idx (w ++ [j]) → Idx w ∧ j < (σ w).nports

lemma PIdx.of_prefix {σ : List ℕ → Piece} {Idx : List ℕ → Prop} (hI : PIdx σ Idx) :
    ∀ {u v : List ℕ}, u <+: v → Idx v → Idx u := by
  intro u v huv hv
  obtain ⟨s, rfl⟩ := huv
  induction s using List.reverseRecOn with
  | nil => simpa using hv
  | append_singleton s j ih =>
      rw [← List.append_assoc] at hv
      exact ih (hI _ _ hv).1

lemma PIdx.letter_lt {σ : List ℕ → Piece} {Idx : List ℕ → Prop} (hI : PIdx σ Idx)
    {u : List ℕ} {a : ℕ} {t : List ℕ} (hv : Idx (u ++ a :: t)) : a < (σ u).nports :=
  (hI u a (hI.of_prefix ⟨t, by simp⟩ hv)).2

/-- **The assembly of a family of pieces over an index set**: a vertex is an address of the
piece at an index word `w`, tagged by `w`. -/
structure PAssembly (σ : List ℕ → Piece) (Idx : List ℕ → Prop) (hI : PIdx σ Idx) where
  /-- The word naming the copy. -/
  copy : List ℕ
  /-- The word is indexed. -/
  idx : Idx copy
  /-- The address inside the piece at that copy. -/
  vert : (σ copy).carrier

namespace PAssembly

variable {σ : List ℕ → Piece} {Idx : List ℕ → Prop} {hI : PIdx σ Idx}

/-- The address of a vertex of the assembly in the ambient tree. -/
def code (x : PAssembly σ Idx hI) : List ℕ := pCopyAddr σ x.copy ++ x.vert.1

lemma vert_eq : ∀ {x y : PAssembly σ Idx hI}, x.copy = y.copy → x.vert.1 = y.vert.1 → x = y := by
  rintro ⟨u, hu, p, hp⟩ ⟨v, hv, q, hq⟩ h1 h2
  simp only at h1 h2
  subst h1
  subst h2
  rfl

/-- The three relative positions of two index words, the divergent one with its first
divergence. -/
lemma copy_cases (u v : List ℕ) :
    u = v ∨ (∃ a t, v = u ++ a :: t) ∨ (∃ a t, u = v ++ a :: t)
      ∨ ∃ z a b s t, a ≠ b ∧ u = z ++ a :: s ∧ v = z ++ b :: t := by
  by_cases h1 : u <+: v
  · obtain ⟨s, rfl⟩ := h1
    cases s with
    | nil => exact Or.inl (by simp)
    | cons a t => exact Or.inr (Or.inl ⟨a, t, rfl⟩)
  · by_cases h2 : v <+: u
    · obtain ⟨s, rfl⟩ := h2
      cases s with
      | nil => exact absurd (by simp) h1
      | cons a t => exact Or.inr (Or.inr (Or.inl ⟨a, t, rfl⟩))
    · obtain ⟨z, a, b, hab, ⟨s, rfl⟩, ⟨t, rfl⟩⟩ := exists_divergeN h1 h2
      exact Or.inr (Or.inr (Or.inr ⟨z, a, b, s, t, hab, by simp, by simp⟩))

/-- Distinct vertices carry distinct addresses. -/
lemma code_injective : Function.Injective (code (σ := σ) (Idx := Idx) (hI := hI)) := by
  rintro ⟨u, hu, p⟩ ⟨v, hv, q⟩ h
  simp only [code] at h
  have h0 : addrDist (pCopyAddr σ u ++ p.1) (pCopyAddr σ v ++ q.1) = 0 :=
    addrDist_eq_zero_iff.mpr h
  rcases copy_cases u v with rfl | ⟨a, t, rfl⟩ | ⟨a, t, rfl⟩ | ⟨z, a, b, s, t, hab, rfl, rfl⟩
  · refine vert_eq rfl ?_
    rw [addrDist_append_append] at h0
    exact addrDist_eq_zero_iff.mp h0
  · rw [addrDist_pCopyAddr_anc σ (hI.letter_lt hv) p.2] at h0
    omega
  · rw [addrDist_comm, addrDist_pCopyAddr_anc σ (hI.letter_lt hu) q.2] at h0
    omega
  · rw [addrDist_pCopyAddr_div σ hab (hI.letter_lt hu) (hI.letter_lt hv)] at h0
    omega

/-- The metric of the assembly, the address metric through the codes. -/
noncomputable instance instMetricSpace (σ : List ℕ → Piece) (Idx : List ℕ → Prop)
    (hI : PIdx σ Idx) : MetricSpace (PAssembly σ Idx hI) where
  dist x y := (addrDist (code x) (code y) : ℝ)
  dist_self x := by simp
  dist_comm x y := by simp only [addrDist_comm (code x) (code y)]
  dist_triangle x y z := by
    have := addrDist_triangle (code x) (code y) (code z)
    exact_mod_cast this
  eq_of_dist_eq_zero {x y} h := by
    have h0 : ((addrDist (code x) (code y) : ℕ) : ℝ) = 0 := h
    exact code_injective (addrDist_eq_zero_iff.mp (Nat.cast_eq_zero.mp h0))

@[simp] lemma dist_code (x y : PAssembly σ Idx hI) :
    dist x y = (addrDist (code x) (code y) : ℝ) := rfl

/-! ### The distance formulas -/

/-- The entry-to-port distance of a piece is the depth of the port. -/
lemma dist_entry_port (X : Piece) (j : ℕ) :
    dist X.entry (X.portVert j) = ((X.port j).length : ℝ) := by
  rw [Piece.dist_carrier, Piece.entry_val, Piece.portVert_val, addrDist_nil_left]

/-- The neck length toward a letter, read in the piece. -/
lemma pNeck_eq (σ : List ℕ → Piece) (t : List ℕ) (a : ℕ) :
    (pNeck σ t a : ℝ) = dist (σ t).entry ((σ t).portVert a) + 1 := by
  rw [pNeck, dist_entry_port]; push_cast; ring

/-- **Inside one copy** the distance is the distance of the piece. -/
theorem dist_same (u : List ℕ) (hu : Idx u) (p q : (σ u).carrier) :
    dist (⟨u, hu, p⟩ : PAssembly σ Idx hI) ⟨u, hu, q⟩ = dist p q := by
  simp only [dist_code, code, Piece.dist_carrier, addrDist_append_append]

/-- **The ancestor formula**: for `x` in the copy at `u` and `y` in the copy at
`u ++ a :: t`, the distance is the distance of `x` to the `a`-th port of its copy, plus
the distance of `y` to the entry of its copy, plus one, plus the neck sum of the copies
strictly between. -/
theorem dist_anc {u : List ℕ} {a : ℕ} {t : List ℕ} (hu : Idx u)
    (hv : Idx (u ++ a :: t)) (p : (σ u).carrier) (q : (σ (u ++ a :: t)).carrier) :
    dist (⟨u, hu, p⟩ : PAssembly σ Idx hI) ⟨u ++ a :: t, hv, q⟩
      = dist p ((σ u).portVert a) + dist q (σ (u ++ a :: t)).entry + 1
        + ∑ i ∈ Finset.Ico (u.length + 1) (u ++ a :: t).length,
            (pNeck σ ((u ++ a :: t).take i) (letterAt (u ++ a :: t) i) : ℝ) := by
  simp only [dist_code, code, Piece.dist_carrier, Piece.entry_val, Piece.portVert_val]
  rw [addrDist_pCopyAddr_anc σ (hI.letter_lt hv) p.2]
  simp only [pNeckSum, addrDist_nil_right]
  push_cast
  ring

/-- **The divergent formula**: for `x` in the copy at `z ++ a :: s` and `y` in the copy
at `z ++ b :: t`, `a ≠ b`, the distance is the two distances to the entries, plus two,
plus the two neck sums, plus the distance between the two ports of the copy at `z` the
branches leave through. -/
theorem dist_div {z : List ℕ} {a b : ℕ} {s t : List ℕ} (hab : a ≠ b)
    (hu : Idx (z ++ a :: s)) (hv : Idx (z ++ b :: t))
    (p : (σ (z ++ a :: s)).carrier) (q : (σ (z ++ b :: t)).carrier) :
    dist (⟨z ++ a :: s, hu, p⟩ : PAssembly σ Idx hI) ⟨z ++ b :: t, hv, q⟩
      = dist p (σ (z ++ a :: s)).entry + dist q (σ (z ++ b :: t)).entry + 2
        + (∑ i ∈ Finset.Ico (z.length + 1) (z ++ a :: s).length,
              (pNeck σ ((z ++ a :: s).take i) (letterAt (z ++ a :: s) i) : ℝ)
          + ∑ i ∈ Finset.Ico (z.length + 1) (z ++ b :: t).length,
              (pNeck σ ((z ++ b :: t).take i) (letterAt (z ++ b :: t) i) : ℝ))
        + dist ((σ z).portVert a) ((σ z).portVert b) := by
  simp only [dist_code, code, Piece.dist_carrier, Piece.entry_val, Piece.portVert_val]
  rw [addrDist_pCopyAddr_div σ hab (hI.letter_lt hu) (hI.letter_lt hv)]
  simp only [pNeckSum, addrDist_nil_right]
  push_cast
  ring

end PAssembly

/-! ### The glued transfer over pieces -/

/-- **The comparison off one copy, with the port term.**  Both distance formulas of the
assembly of pieces decompose the distance into two mark distances, a constant, a neck sum
and a port distance; the glued map transfers each group, and all constants fit `8K²`. -/
theorem blob_glued_dist_bounds {K A B N P A' B' N' P' e d d' : ℝ} (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 ≤ N) (hP : 0 ≤ P) (hA' : 0 ≤ A') (hB' : 0 ≤ B')
    (_hN' : 0 ≤ N') (hP' : 0 ≤ P') (he : 0 ≤ e)
    (hAup : A' ≤ K * A + 2 * K) (hAlo : A ≤ K * A' + 2 * K ^ 2)
    (hBup : B' ≤ K * B + 2 * K) (hBlo : B ≤ K * B' + 2 * K ^ 2)
    (hNup : N' ≤ 4 * K * N) (hNlo : N ≤ 8 * K ^ 2 * N')
    (hPup : P' ≤ K * P + 3 * K) (hPlo : P ≤ K * P' + 3 * K ^ 2)
    (hd : d = A + B + e + N + P) (hd' : d' = A' + B' + e + N' + P') :
    d' ≤ 8 * K ^ 2 * d + 8 * K ^ 2 ∧ d ≤ 8 * K ^ 2 * d' + (8 * K ^ 2) ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  have hKL : K ≤ 8 * K ^ 2 := by nlinarith
  have h4KL : 4 * K ≤ 8 * K ^ 2 := by nlinarith
  have h1L : (1 : ℝ) ≤ 8 * K ^ 2 := by nlinarith
  subst hd hd'
  constructor
  · have e1 : K * A ≤ 8 * K ^ 2 * A := mul_le_mul_of_nonneg_right hKL hA
    have e2 : K * B ≤ 8 * K ^ 2 * B := mul_le_mul_of_nonneg_right hKL hB
    have e3 : 4 * K * N ≤ 8 * K ^ 2 * N := mul_le_mul_of_nonneg_right h4KL hN
    have e5 : K * P ≤ 8 * K ^ 2 * P := mul_le_mul_of_nonneg_right hKL hP
    have e4 : e ≤ 8 * K ^ 2 * e := by nlinarith
    nlinarith
  · have e1 : K * A' ≤ 8 * K ^ 2 * A' := mul_le_mul_of_nonneg_right hKL hA'
    have e2 : K * B' ≤ 8 * K ^ 2 * B' := mul_le_mul_of_nonneg_right hKL hB'
    have e5 : K * P' ≤ 8 * K ^ 2 * P' := mul_le_mul_of_nonneg_right hKL hP'
    have e4 : e ≤ 8 * K ^ 2 * e := by nlinarith
    have e6 : 7 * K ^ 2 ≤ (8 * K ^ 2) ^ 2 := by nlinarith
    nlinarith

/-- The port comparison of a port quasi-isometry: the distance between two ports of the
target is controlled by the distance between the corresponding ports of the source. -/
lemma port_dist_bounds {K : ℝ} (hK : 0 ≤ K) {X Y : PortSpace} {f : X.carrier → Y.carrier}
    (hf : IsPortQI K X Y f) (a b : ℕ) :
    dist (Y.port a) (Y.port b) ≤ K * dist (X.port a) (X.port b) + 3 * K
      ∧ dist (X.port a) (X.port b) ≤ K * dist (Y.port a) (Y.port b) + 3 * K ^ 2 := by
  have ha : dist (Y.port a) (f (X.port a)) ≤ K := by rw [dist_comm]; exact hf.port a
  have hb : dist (f (X.port b)) (Y.port b) ≤ K := hf.port b
  constructor
  · have htri : dist (Y.port a) (Y.port b)
        ≤ dist (Y.port a) (f (X.port a)) + dist (f (X.port a)) (f (X.port b))
          + dist (f (X.port b)) (Y.port b) := dist_triangle4 _ _ _ _
    have hmid := hf.upper (X.port a) (X.port b)
    linarith
  · have htri : dist (f (X.port a)) (f (X.port b))
        ≤ dist (f (X.port a)) (Y.port a) + dist (Y.port a) (Y.port b)
          + dist (Y.port b) (f (X.port b)) := dist_triangle4 _ _ _ _
    have h1 : dist (f (X.port a)) (Y.port a) ≤ K := hf.port a
    have h2 : dist (Y.port b) (f (X.port b)) ≤ K := by rw [dist_comm]; exact hf.port b
    have hlow := hf.lower (X.port a) (X.port b)
    have hmul : K * dist (f (X.port a)) (f (X.port b))
        ≤ K * (dist (Y.port a) (Y.port b) + 2 * K) := by
      refine mul_le_mul_of_nonneg_left ?_ hK
      linarith
    nlinarith

namespace PAssembly

variable {σ σ' : List ℕ → Piece} {Idx : List ℕ → Prop} {hI : PIdx σ Idx} {hI' : PIdx σ' Idx}

/-- **The glued map**: the per-piece maps, copy by copy. -/
def glue (φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier) (x : PAssembly σ Idx hI) :
    PAssembly σ' Idx hI' := ⟨x.copy, x.idx, φ x.copy x.vert⟩

/-- The neck sums compare termwise through the port quasi-isometries, the neck of an
intermediate copy being read toward the port the index word uses there. -/
lemma neckSum_bounds (hI : PIdx σ Idx) {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier}
    (hφ : ∀ w, Idx w → IsPortQI K (σ w).space (σ' w).space (φ w)) (a b : ℕ) {v : List ℕ}
    (hv : Idx v) :
    (∑ i ∈ Finset.Ico a b, (pNeck σ (v.take i) (letterAt v i) : ℝ))
        ≤ 8 * K ^ 2 * ∑ i ∈ Finset.Ico a b, (pNeck σ' (v.take i) (letterAt v i) : ℝ)
      ∧ (∑ i ∈ Finset.Ico a b, (pNeck σ' (v.take i) (letterAt v i) : ℝ))
        ≤ 4 * K * ∑ i ∈ Finset.Ico a b, (pNeck σ (v.take i) (letterAt v i) : ℝ) := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hidx : ∀ i, Idx (v.take i) := fun i => hI.of_prefix (List.take_prefix i v) hv
  refine neck_sum_bounds _ hK (fun i _ => ?_) (fun i _ => ?_) (fun i _ => ?_) (fun i _ => ?_)
  · exact one_le_pNeck _ _ _
  · exact one_le_pNeck _ _ _
  · have h := (neck_le_of_markedQI hK0 ((hφ _ (hidx i)).toMarked (letterAt v i))).1
    rw [pNeck_eq, pNeck_eq]
    change dist (σ' (v.take i)).entry ((σ' (v.take i)).portVert (letterAt v i))
      ≤ K * dist (σ (v.take i)).entry ((σ (v.take i)).portVert (letterAt v i)) + 3 * K at h
    linarith
  · have h := (neck_le_of_markedQI hK0 ((hφ _ (hidx i)).toMarked (letterAt v i))).2
    rw [pNeck_eq, pNeck_eq]
    change dist (σ (v.take i)).entry ((σ (v.take i)).portVert (letterAt v i))
      ≤ K * dist (σ' (v.take i)).entry ((σ' (v.take i)).portVert (letterAt v i)) + 3 * K ^ 2 at h
    linarith

/-- The glued transfer in the ancestor position. -/
theorem glue_dist_bounds_anc {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier}
    (hφ : ∀ w, Idx w → IsPortQI K (σ w).space (σ' w).space (φ w))
    {u : List ℕ} {a : ℕ} {t : List ℕ} (hu : Idx u) (hv : Idx (u ++ a :: t))
    (p : (σ u).carrier) (q : (σ (u ++ a :: t)).carrier) :
    dist (glue (hI := hI) (hI' := hI') φ (⟨u, hu, p⟩ : PAssembly σ Idx hI)) (glue (hI := hI) (hI' := hI') φ ⟨u ++ a :: t, hv, q⟩)
          ≤ 8 * K ^ 2 * dist (⟨u, hu, p⟩ : PAssembly σ Idx hI) ⟨u ++ a :: t, hv, q⟩ + 8 * K ^ 2
      ∧ dist (⟨u, hu, p⟩ : PAssembly σ Idx hI) ⟨u ++ a :: t, hv, q⟩
          ≤ 8 * K ^ 2 * dist (glue (hI := hI) (hI' := hI') φ (⟨u, hu, p⟩ : PAssembly σ Idx hI))
              (glue (hI := hI) (hI' := hI') φ ⟨u ++ a :: t, hv, q⟩) + (8 * K ^ 2) ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hA : dist (φ u p) ((σ' u).portVert a) ≤ K * dist p ((σ u).portVert a) + 2 * K
      ∧ dist p ((σ u).portVert a) ≤ K * dist (φ u p) ((σ' u).portVert a) + 2 * K ^ 2 :=
    dist_mark_bounds hK0 ((hφ u hu).toMarked a) ((hφ u hu).port a) p
  have hB : dist (φ _ q) (σ' (u ++ a :: t)).entry ≤ K * dist q (σ (u ++ a :: t)).entry + 2 * K
      ∧ dist q (σ (u ++ a :: t)).entry
        ≤ K * dist (φ _ q) (σ' (u ++ a :: t)).entry + 2 * K ^ 2 :=
    dist_mark_bounds hK0 ((hφ _ hv).toMarked 0) (hφ _ hv).entry q
  have hN := neckSum_bounds hI hK hφ (u.length + 1) (u ++ a :: t).length hv
  exact blob_glued_dist_bounds hK dist_nonneg dist_nonneg
    (Finset.sum_nonneg fun i _ => by positivity) le_rfl dist_nonneg dist_nonneg
    (Finset.sum_nonneg fun i _ => by positivity) le_rfl zero_le_one
    hA.1 hA.2 hB.1 hB.2 hN.2 hN.1 (by linarith) (by nlinarith)
    (by rw [dist_anc hu hv p q]; ring)
    (by rw [glue, glue, dist_anc hu hv (φ u p) (φ _ q)]; ring)

/-- The glued transfer in the divergent position. -/
theorem glue_dist_bounds_div {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier}
    (hφ : ∀ w, Idx w → IsPortQI K (σ w).space (σ' w).space (φ w))
    {z : List ℕ} {a b : ℕ} {s t : List ℕ} (hab : a ≠ b) (hu : Idx (z ++ a :: s))
    (hv : Idx (z ++ b :: t)) (p : (σ (z ++ a :: s)).carrier) (q : (σ (z ++ b :: t)).carrier) :
    dist (glue (hI := hI) (hI' := hI') φ (⟨z ++ a :: s, hu, p⟩ : PAssembly σ Idx hI))
        (glue (hI := hI) (hI' := hI') φ ⟨z ++ b :: t, hv, q⟩)
          ≤ 8 * K ^ 2 * dist (⟨z ++ a :: s, hu, p⟩ : PAssembly σ Idx hI) ⟨z ++ b :: t, hv, q⟩
            + 8 * K ^ 2
      ∧ dist (⟨z ++ a :: s, hu, p⟩ : PAssembly σ Idx hI) ⟨z ++ b :: t, hv, q⟩
          ≤ 8 * K ^ 2 * dist (glue (hI := hI) (hI' := hI') φ (⟨z ++ a :: s, hu, p⟩ : PAssembly σ Idx hI))
              (glue (hI := hI) (hI' := hI') φ ⟨z ++ b :: t, hv, q⟩) + (8 * K ^ 2) ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hz : Idx z := hI.of_prefix ⟨a :: s, rfl⟩ hu
  have hA : dist (φ _ p) (σ' (z ++ a :: s)).entry ≤ K * dist p (σ (z ++ a :: s)).entry + 2 * K
      ∧ dist p (σ (z ++ a :: s)).entry
        ≤ K * dist (φ _ p) (σ' (z ++ a :: s)).entry + 2 * K ^ 2 :=
    dist_mark_bounds hK0 ((hφ _ hu).toMarked 0) (hφ _ hu).entry p
  have hB : dist (φ _ q) (σ' (z ++ b :: t)).entry ≤ K * dist q (σ (z ++ b :: t)).entry + 2 * K
      ∧ dist q (σ (z ++ b :: t)).entry
        ≤ K * dist (φ _ q) (σ' (z ++ b :: t)).entry + 2 * K ^ 2 :=
    dist_mark_bounds hK0 ((hφ _ hv).toMarked 0) (hφ _ hv).entry q
  have hNu := neckSum_bounds hI hK hφ (z.length + 1) (z ++ a :: s).length hu
  have hNv := neckSum_bounds hI hK hφ (z.length + 1) (z ++ b :: t).length hv
  have hP : dist ((σ' z).portVert a) ((σ' z).portVert b)
        ≤ K * dist ((σ z).portVert a) ((σ z).portVert b) + 3 * K
      ∧ dist ((σ z).portVert a) ((σ z).portVert b)
        ≤ K * dist ((σ' z).portVert a) ((σ' z).portVert b) + 3 * K ^ 2 :=
    port_dist_bounds hK0 (hφ z hz) a b
  have hdu := dist_div (hI := hI) hab hu hv p q
  have hdu' := dist_div (hI := hI') hab hu hv (φ _ p) (φ _ q)
  refine blob_glued_dist_bounds hK dist_nonneg dist_nonneg ?_ dist_nonneg
    dist_nonneg dist_nonneg ?_ dist_nonneg (by norm_num)
    hA.1 hA.2 hB.1 hB.2 ?_ ?_ hP.1 hP.2 hdu hdu'
  · positivity
  · positivity
  · have h1 := hNu.2
    have h2 := hNv.2
    linarith
  · have h1 := hNu.1
    have h2 := hNv.1
    linarith

/-- Coarse density of the glued map, copy by copy. -/
lemma glue_dense {K : ℝ} {φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier}
    (hφ : ∀ w, Idx w → IsPortQI K (σ w).space (σ' w).space (φ w)) (y : PAssembly σ' Idx hI') :
    ∃ x : PAssembly σ Idx hI, dist (glue φ x) y ≤ K := by
  obtain ⟨w, hw, r⟩ := y
  obtain ⟨a, ha⟩ := (hφ w hw).dense r
  refine ⟨⟨w, hw, a⟩, ?_⟩
  have h : dist (glue φ (⟨w, hw, a⟩ : PAssembly σ Idx hI)) (⟨w, hw, r⟩ : PAssembly σ' Idx hI')
      = dist (φ w a) r := dist_same w hw _ _
  rw [h]
  exact ha

/-- **The glued transfer over pieces** (**`it:general-glued`** with several ports): two
families of pieces that are `K`-port comparable copy by copy over a common index set
have `8K²`-quasi-isometric assemblies, the glued map being the per-piece maps read copy by
copy. -/
theorem glued_transfer (hI : PIdx σ Idx) (hI' : PIdx σ' Idx) {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier}
    (hφ : ∀ w, Idx w → IsPortQI K (σ w).space (σ' w).space (φ w)) :
    (∀ x y : PAssembly σ Idx hI,
        dist (glue (hI := hI) (hI' := hI') φ x) (glue φ y) ≤ 8 * K ^ 2 * dist x y + 8 * K ^ 2)
      ∧ (∀ x y : PAssembly σ Idx hI, dist x y
          ≤ 8 * K ^ 2 * dist (glue (hI := hI) (hI' := hI') φ x) (glue φ y) + (8 * K ^ 2) ^ 2)
      ∧ ∀ y : PAssembly σ' Idx hI', ∃ x : PAssembly σ Idx hI, dist (glue φ x) y ≤ 8 * K ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have key : ∀ x y : PAssembly σ Idx hI,
      dist (glue (hI := hI) (hI' := hI') φ x) (glue φ y) ≤ 8 * K ^ 2 * dist x y + 8 * K ^ 2
        ∧ dist x y ≤ 8 * K ^ 2 * dist (glue (hI := hI) (hI' := hI') φ x) (glue φ y) + (8 * K ^ 2) ^ 2 := by
    rintro ⟨u, hu, p⟩ ⟨v, hv, q⟩
    rcases copy_cases u v with rfl | ⟨a, t, rfl⟩ | ⟨a, t, rfl⟩ | ⟨z, a, b, s, t, hab, rfl, rfl⟩
    · have e1 : dist (glue (hI := hI) (hI' := hI') φ (⟨u, hu, p⟩ : PAssembly σ Idx hI)) (glue (hI := hI) (hI' := hI') φ ⟨u, hv, q⟩)
          = dist (φ u p) (φ u q) := dist_same u hu _ _
      have e2 : dist (⟨u, hu, p⟩ : PAssembly σ Idx hI) ⟨u, hv, q⟩ = dist p q :=
        dist_same u hu p q
      rw [e1, e2]
      refine glued_dist_same hK dist_nonneg dist_nonneg ((hφ u hu).upper p q) ?_
      rw [pow_two]
      exact (hφ u hu).lower p q
    · exact glue_dist_bounds_anc hK hφ hu hv p q
    · obtain ⟨h1, h2⟩ := glue_dist_bounds_anc (hI' := hI') hK hφ hv hu q p
      rw [dist_comm (glue (hI := hI) (hI' := hI') φ (⟨v ++ a :: t, hu, p⟩ : PAssembly σ Idx hI)),
        dist_comm (⟨v ++ a :: t, hu, p⟩ : PAssembly σ Idx hI)]
      exact ⟨h1, h2⟩
    · exact glue_dist_bounds_div hK hφ hab hu hv p q
  refine ⟨fun x y => (key x y).1, fun x y => (key x y).2, fun y => ?_⟩
  obtain ⟨x, hx⟩ := glue_dense hφ y
  exact ⟨x, hx.trans (by nlinarith)⟩

/-- The glued transfer as a quasi-isometry in the sense of `IsQIMap`. -/
theorem glue_isQIMap (hI : PIdx σ Idx) (hI' : PIdx σ' Idx) {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier}
    (hφ : ∀ w, Idx w → IsPortQI K (σ w).space (σ' w).space (φ w)) :
    IsQIMap (8 * K ^ 2) (glue (hI := hI) (hI' := hI') φ) :=
  ⟨(glued_transfer hI hI' hK hφ).1, (glued_transfer hI hI' hK hφ).2.1,
    (glued_transfer hI hI' hK hφ).2.2⟩

end PAssembly

/-! ### The flat configuration -/

/-- The address `n` steps down the neck: `n` zeros. -/
def pRep (n : ℕ) : List ℕ := List.replicate n 0

@[simp] lemma pRep_zero : pRep 0 = [] := rfl

@[simp] lemma pRep_length (n : ℕ) : (pRep n).length = n := by simp [pRep]

lemma pRep_succ (n : ℕ) : pRep (n + 1) = pRep n ++ [0] := by
  simp [pRep, List.replicate_succ']

lemma pRep_prefix_pRep {i n : ℕ} (h : i ≤ n) : pRep i <+: pRep n := by
  rw [pRep, pRep, List.prefix_replicate_iff]
  simp [h]

lemma pRep_prefix_iff {i n : ℕ} : pRep i <+: pRep n ↔ i ≤ n := by
  refine ⟨fun h => by simpa using h.length_le, pRep_prefix_pRep⟩

/-- A prefix of the neck is a neck vertex. -/
lemma eq_pRep_of_prefix {p : List ℕ} {n : ℕ} (h : p <+: pRep n) : p = pRep p.length := by
  rw [pRep, List.prefix_replicate_iff] at h
  exact h.2

/-- **The flat configuration**: a bare neck of `n` edges with `k` ports at its far end,
the `j`-th port planting at the child `j` of the far end. -/
def flatPiece (n k : ℕ) : Piece where
  mem p := p <+: pRep n
  nil_mem := List.nil_prefix
  mem_of_prefix := fun h1 h2 => h1.trans h2
  ports := (List.range k).map fun j => (pRep n, j)
  port_mem := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact List.prefix_refl _
  slot_free := by
    intro x hx h
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    have := h.length_le
    simp at this
  ports_nodup := by
    refine List.Nodup.map_on (fun a _ b _ h => ?_) List.nodup_range
    simpa using h

@[simp] lemma flatPiece_mem (n k : ℕ) (p : List ℕ) : (flatPiece n k).mem p ↔ p <+: pRep n :=
  Iff.rfl

@[simp] lemma flatPiece_nports (n k : ℕ) : (flatPiece n k).nports = k := by
  simp [Piece.nports, flatPiece]

lemma flatPiece_portSlot_of_lt {n k j : ℕ} (hj : j < k) :
    (flatPiece n k).portSlot j = (pRep n, j) := by
  rw [Piece.portSlot, List.getD_eq_getElem _ _ (by simp [flatPiece, hj])]
  simp [flatPiece]

lemma flatPiece_port_of_lt {n k j : ℕ} (hj : j < k) : (flatPiece n k).port j = pRep n := by
  rw [Piece.port, flatPiece_portSlot_of_lt hj]

lemma flatPiece_slot_of_lt {n k j : ℕ} (hj : j < k) : (flatPiece n k).slot j = j := by
  rw [Piece.slot, flatPiece_portSlot_of_lt hj]

lemma flatPiece_port_of_le {n k j : ℕ} (hj : k ≤ j) : (flatPiece n k).port j = [] := by
  rw [Piece.port, Piece.portSlot_of_le (by simpa using hj)]

lemma flatPiece_root_of_lt {n k j : ℕ} (hj : j < k) :
    (flatPiece n k).root j = pRep n ++ [j] := by
  rw [Piece.root, flatPiece_port_of_lt hj, flatPiece_slot_of_lt hj]

/-- The collapse onto the far end of the neck, on addresses. -/
def collapseAddr (n : ℕ) (p : List ℕ) : List ℕ := if pRep n <+: p then pRep n else p

lemma collapseAddr_of_prefix {n : ℕ} {p : List ℕ} (h : pRep n <+: p) :
    collapseAddr n p = pRep n := if_pos h

lemma collapseAddr_of_not_prefix {n : ℕ} {p : List ℕ} (h : ¬ pRep n <+: p) :
    collapseAddr n p = p := if_neg h

/-- The collapse does not increase distances. -/
lemma addrDist_collapseAddr_le {n : ℕ} {p q : List ℕ} (hp : p <+: pRep n ∨ pRep n <+: p)
    (hq : q <+: pRep n ∨ pRep n <+: q) :
    addrDist (collapseAddr n p) (collapseAddr n q) ≤ addrDist p q := by
  by_cases h1 : pRep n <+: p
  · by_cases h2 : pRep n <+: q
    · rw [collapseAddr_of_prefix h1, collapseAddr_of_prefix h2, addrDist_self]
      exact Nat.zero_le _
    · have hq' : q <+: pRep n := hq.resolve_right h2
      have e1 : addrDist (pRep n) q = n - q.length := by
        rw [addrDist_comm, addrDist_of_prefix hq', pRep_length]
      have e2 : addrDist p q = p.length - q.length := by
        rw [addrDist_comm, addrDist_of_prefix (hq'.trans h1)]
      have := h1.length_le
      rw [collapseAddr_of_prefix h1, collapseAddr_of_not_prefix h2, e1, e2]
      simp only [pRep_length] at this
      omega
  · by_cases h2 : pRep n <+: q
    · have hp' : p <+: pRep n := hp.resolve_right h1
      have e1 : addrDist p (pRep n) = n - p.length := by
        rw [addrDist_of_prefix hp', pRep_length]
      have e2 : addrDist p q = q.length - p.length := by
        rw [addrDist_of_prefix (hp'.trans h2)]
      have := h2.length_le
      rw [collapseAddr_of_not_prefix h1, collapseAddr_of_prefix h2, e1, e2]
      simp only [pRep_length] at this
      omega
    · rw [collapseAddr_of_not_prefix h1, collapseAddr_of_not_prefix h2]

/-- The collapse loses at most twice the depth below the far end. -/
lemma addrDist_le_collapseAddr {n Δ : ℕ} {p q : List ℕ} (hp : p <+: pRep n ∨ pRep n <+: p)
    (hq : q <+: pRep n ∨ pRep n <+: q) (hpd : pRep n <+: p → p.length ≤ n + Δ)
    (hqd : pRep n <+: q → q.length ≤ n + Δ) :
    addrDist p q ≤ addrDist (collapseAddr n p) (collapseAddr n q) + 2 * Δ := by
  by_cases h1 : pRep n <+: p
  · by_cases h2 : pRep n <+: q
    · rw [collapseAddr_of_prefix h1, collapseAddr_of_prefix h2, addrDist_self]
      have ht := addrDist_triangle p (pRep n) q
      have e1 : addrDist p (pRep n) = p.length - n := by
        rw [addrDist_comm, addrDist_of_prefix h1, pRep_length]
      have e2 : addrDist (pRep n) q = q.length - n := by
        rw [addrDist_of_prefix h2, pRep_length]
      have := hpd h1
      have := hqd h2
      omega
    · have hq' : q <+: pRep n := hq.resolve_right h2
      have e1 : addrDist (pRep n) q = n - q.length := by
        rw [addrDist_comm, addrDist_of_prefix hq', pRep_length]
      have e2 : addrDist p q = p.length - q.length := by
        rw [addrDist_comm, addrDist_of_prefix (hq'.trans h1)]
      have := hpd h1
      have := h1.length_le
      rw [collapseAddr_of_prefix h1, collapseAddr_of_not_prefix h2, e1, e2]
      simp only [pRep_length] at this
      omega
  · by_cases h2 : pRep n <+: q
    · have hp' : p <+: pRep n := hp.resolve_right h1
      have e1 : addrDist p (pRep n) = n - p.length := by
        rw [addrDist_of_prefix hp', pRep_length]
      have e2 : addrDist p q = q.length - p.length := by
        rw [addrDist_of_prefix (hp'.trans h2)]
      have := hqd h2
      have := h2.length_le
      rw [collapseAddr_of_not_prefix h1, collapseAddr_of_prefix h2, e1, e2]
      simp only [pRep_length] at this
      omega
    · rw [collapseAddr_of_not_prefix h1, collapseAddr_of_not_prefix h2]
      omega

/-- **A piece is a neck with everything else beyond its far end**: every address is a
neck vertex or extends the far end, the addresses beyond the far end reach at most `Δ`
deeper, and the ports all lie beyond the far end. -/
structure IsNeckPiece (X : Piece) (n Δ : ℕ) : Prop where
  neck : X.mem (pRep n)
  cases : ∀ p, X.mem p → p <+: pRep n ∨ pRep n <+: p
  depth : ∀ p, X.mem p → pRep n <+: p → p.length ≤ n + Δ
  port : ∀ j, j < X.nports → pRep n <+: X.port j

/-- The collapse of a neck piece onto its flat configuration, as a map of vertices. -/
def collapse (X : Piece) {n Δ : ℕ} (h : IsNeckPiece X n Δ) (x : X.carrier) :
    (flatPiece n X.nports).carrier :=
  ⟨collapseAddr n x.1, by
    rw [flatPiece_mem, collapseAddr]
    split
    · exact List.prefix_refl _
    · next hn => exact (h.cases x.1 x.2).resolve_right hn⟩

/-- **`thm:matched-presentation`\labelcref{it:matched-flat}, abstractly**: a neck piece
of depth `Δ` beyond its far end admits a `(2Δ + 1)`-port quasi-isometry onto its flat
configuration, the collapse of everything beyond the far end onto the far end. -/
theorem isPortQI_collapse (X : Piece) {n Δ : ℕ} (h : IsNeckPiece X n Δ) :
    IsPortQI (2 * Δ + 1) X.space (flatPiece n X.nports).space (collapse X h) := by
  have hL : (1 : ℝ) ≤ 2 * Δ + 1 := by
    have : (0 : ℝ) ≤ Δ := Nat.cast_nonneg Δ
    linarith
  have hup : ∀ a b : X.space.carrier,
      dist (collapse X h a : (flatPiece n X.nports).space.carrier) (collapse X h b)
        ≤ dist a b := by
    intro a b
    change ((addrDist (collapseAddr n a.1) (collapseAddr n b.1) : ℕ) : ℝ)
      ≤ ((addrDist a.1 b.1 : ℕ) : ℝ)
    exact_mod_cast addrDist_collapseAddr_le (h.cases a.1 a.2) (h.cases b.1 b.2)
  have hlo : ∀ a b : X.space.carrier, dist a b
      ≤ dist (collapse X h a : (flatPiece n X.nports).space.carrier) (collapse X h b)
        + 2 * Δ := by
    intro a b
    change ((addrDist a.1 b.1 : ℕ) : ℝ)
      ≤ ((addrDist (collapseAddr n a.1) (collapseAddr n b.1) : ℕ) : ℝ) + 2 * (Δ : ℝ)
    exact_mod_cast addrDist_le_collapseAddr (h.cases a.1 a.2) (h.cases b.1 b.2)
      (h.depth a.1 a.2) (h.depth b.1 b.2)
  have hfix : ∀ p : List ℕ, p <+: pRep n → collapseAddr n p = p := by
    intro p hp
    by_cases hn : pRep n <+: p
    · rw [collapseAddr_of_prefix hn]
      exact hn.eq_of_length (le_antisymm hn.length_le hp.length_le)
    · exact collapseAddr_of_not_prefix hn
  refine ⟨fun a b => ?_, fun a b => ?_, fun y => ?_, ?_, fun j => ?_⟩
  · have h2 : dist a b ≤ (2 * Δ + 1) * dist a b + (2 * Δ + 1) := by
      nlinarith [dist_nonneg (x := a) (y := b)]
    exact (hup a b).trans h2
  · have h2 : dist (collapse X h a : (flatPiece n X.nports).space.carrier) (collapse X h b)
        + 2 * Δ
        ≤ (2 * Δ + 1) * dist (collapse X h a : (flatPiece n X.nports).space.carrier)
            (collapse X h b) + (2 * Δ + 1) * (2 * Δ + 1) := by
      nlinarith [dist_nonneg (x := (collapse X h a : (flatPiece n X.nports).space.carrier))
        (y := collapse X h b)]
    exact (hlo a b).trans h2
  · obtain ⟨q, hq⟩ := y
    refine ⟨⟨q, X.mem_of_prefix hq h.neck⟩, ?_⟩
    have : collapse X h ⟨q, X.mem_of_prefix hq h.neck⟩ = ⟨q, hq⟩ :=
      Subtype.ext (hfix q hq)
    rw [this, dist_self]
    linarith
  · change dist (collapse X h X.entry) (flatPiece n X.nports).entry ≤ _
    have : collapse X h X.entry = (flatPiece n X.nports).entry :=
      Subtype.ext (hfix [] List.nil_prefix)
    rw [this, dist_self]
    linarith
  · change dist (collapse X h (X.portVert j)) ((flatPiece n X.nports).portVert j) ≤ _
    rcases lt_or_ge j X.nports with hj | hj
    · have : collapse X h (X.portVert j) = (flatPiece n X.nports).portVert j := by
        refine Subtype.ext ?_
        show collapseAddr n (X.port j) = (flatPiece n X.nports).port j
        rw [collapseAddr_of_prefix (h.port j hj), flatPiece_port_of_lt hj]
      rw [this, dist_self]
      linarith
    · have : collapse X h (X.portVert j) = (flatPiece n X.nports).portVert j := by
        refine Subtype.ext ?_
        show collapseAddr n (X.port j) = (flatPiece n X.nports).port j
        rw [Piece.port, Piece.portSlot_of_le hj, flatPiece_port_of_le hj]
        exact hfix [] List.nil_prefix
      rw [this, dist_self]
      linarith

/-- The converse: the flat configuration reaches the neck piece by a `3(2Δ+1)²`-port
quasi-isometry. -/
theorem portQI_flat_symm (X : Piece) {n Δ : ℕ} (h : IsNeckPiece X n Δ) :
    PortQI (3 * (2 * Δ + 1) ^ 2) (flatPiece n X.nports).space X.space := by
  have hL : (1 : ℝ) ≤ 2 * Δ + 1 := by
    have : (0 : ℝ) ≤ Δ := Nat.cast_nonneg Δ
    linarith
  exact (isPortQI_collapse X h).symm hL


/-! ### Words over `Fin N` read over `ℕ` -/

open BranchingProcess (sample Survives skeleton survivors skeletonDegree bushAt childSet)

variable {N : ℕ}

/-- A word over `Fin N` read as a word over `ℕ`. -/
def pvals (u : GWord N) : List ℕ := u.map Fin.val

@[simp] lemma pvals_nil : pvals ([] : GWord N) = [] := rfl

@[simp] lemma pvals_cons (i : Fin N) (u : GWord N) : pvals (i :: u) = (i : ℕ) :: pvals u := rfl

@[simp] lemma pvals_append (u v : GWord N) : pvals (u ++ v) = pvals u ++ pvals v := by
  simp [pvals]

@[simp] lemma pvals_length (u : GWord N) : (pvals u).length = u.length := by simp [pvals]

lemma pvals_injective : Function.Injective (pvals (N := N)) :=
  List.map_injective_iff.mpr Fin.val_injective

lemma pvals_prefix_iff {u v : GWord N} : pvals u <+: pvals v ↔ u <+: v := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := h
    have hlen : u.length ≤ v.length := by
      have := congrArg List.length hs
      simp at this
      omega
    have heq : pvals u = pvals (v.take u.length) := by
      have h2 : (pvals v).take u.length = pvals u := by
        rw [← hs, List.take_left' (by simp)]
      rw [pvals, ← List.map_take] at h2
      exact h2.symm
    rw [pvals_injective heq]
    exact List.take_prefix _ _
  · exact fun h => h.map _

lemma wedgeN_pvals (u v : GWord N) :
    wedgeN (pvals u) (pvals v) = pvals (BranchingProcess.wedge u v) := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
      cases v with
      | nil => simp
      | cons b v =>
          rw [pvals_cons, pvals_cons, wedgeN_cons_cons, BranchingProcess.wedge_cons_cons]
          by_cases hab : a = b
          · subst hab
            simp [ih]
          · rw [if_neg (fun h => hab (Fin.ext h)), if_neg hab]
            rfl

/-- The tree metric of the ambient tree is the address metric of the readings. -/
lemma addrDist_pvals (u v : GWord N) :
    addrDist (pvals u) (pvals v) = BranchingProcess.treeDist u v := by
  rw [addrDist, BranchingProcess.treeDist, wedgeN_pvals, pvals_length, pvals_length,
    pvals_length]

/-! ### The chain regime, deterministically -/

section Chain

variable [NeZero N]

/-- The vertex `n` steps down the neck of the ambient tree: `n` zeros. -/
def rep (N : ℕ) [NeZero N] (n : ℕ) : GWord N := List.replicate n 0

@[simp] lemma rep_zero : rep N 0 = [] := rfl

lemma rep_succ (n : ℕ) : rep N (n + 1) = rep N n ++ [0] := by
  simp [rep, List.replicate_succ']

lemma rep_succ' (n : ℕ) : rep N (n + 1) = 0 :: rep N n := rfl

@[simp] lemma rep_length (n : ℕ) : (rep N n).length = n := by simp [rep]

@[simp] lemma pvals_rep (n : ℕ) : pvals (rep N n) = pRep n := by
  simp [rep, pRep, pvals, List.map_replicate]

lemma rep_prefix_rep {i n : ℕ} (h : i ≤ n) : rep N i <+: rep N n := by
  rw [rep, rep, List.prefix_replicate_iff]
  simp [h]

lemma eq_rep_of_prefix {q : GWord N} {n : ℕ} (h : q <+: rep N n) : q = rep N q.length := by
  rw [rep, List.prefix_replicate_iff] at h
  exact h.2

/-- **A chain-regime field**: every vertex has at least one and at most `N` children, and
every neck terminates, some vertex of the chain of first children below any vertex having
at least two children. -/
structure IsChainField (N : ℕ) [NeZero N] (c : GWord N → ℕ) : Prop where
  one_le : ∀ v, 1 ≤ c v
  le_N : ∀ v, c v ≤ N
  split : ∀ v, ∃ n, 2 ≤ c (v ++ rep N n)

namespace IsChainField

variable {c : GWord N → ℕ}

lemma ambSub (hc : IsChainField N c) (v : GWord N) : IsChainField N (ChainClasses.ambSub c v) :=
  ⟨fun w => hc.one_le _, fun w => hc.le_N _, fun w => by
    obtain ⟨n, hn⟩ := hc.split (v ++ w)
    exact ⟨n, by rw [ambSub_apply, ← List.append_assoc]; exact hn⟩⟩

/-- The chain of first children lies in the sample. -/
lemma rep_mem_sample (hc : IsChainField N c) (n : ℕ) : rep N n ∈ sample c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [rep_succ, BranchingProcess.mem_sample_append_singleton]
      exact ⟨ih, by simpa using Nat.lt_of_lt_of_le Nat.zero_lt_one (hc.one_le (rep N n))⟩

/-- A chain-regime field survives. -/
lemma survives (hc : IsChainField N c) : Survives c :=
  Set.infinite_of_injective_forall_mem (fun a b h => by simpa using congrArg List.length h)
    hc.rep_mem_sample

/-- Every child survives. -/
lemma mem_survivors_iff (hc : IsChainField N c) (i : Fin N) :
    i ∈ survivors c ↔ (i : ℕ) < c [] := by
  rw [BranchingProcess.mem_survivors]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact (hc.ambSub [i]).survives

lemma survivors_eq (hc : IsChainField N c) : survivors c = childSet N (c []) := by
  ext i
  rw [hc.mem_survivors_iff, BranchingProcess.mem_childSet]

/-- The skeleton degree is the offspring count. -/
lemma skeletonDegree_eq (hc : IsChainField N c) : skeletonDegree c = c [] := by
  rw [skeletonDegree, hc.survivors_eq, BranchingProcess.card_childSet (hc.le_N [])]

/-- The `m`-th surviving subtree is the subtree at the child `m`. -/
lemma bushAt_eq (hc : IsChainField N c) {m : ℕ} (hm : m < c []) :
    bushAt c m = ChainClasses.ambSub c [⟨m, lt_of_lt_of_le hm (hc.le_N [])⟩] := by
  have hm' : m < (survivors c).card := by
    rw [← skeletonDegree, hc.skeletonDegree_eq]; exact hm
  rw [BranchingProcess.bushAt_of_lt hm']
  set i := (survivors c).orderEmbOfFin rfl ⟨m, hm'⟩ with hi
  have hmem : i ∈ survivors c := Finset.orderEmbOfFin_mem _ _ _
  have hrank := BranchingProcess.rankOf_orderEmbOfFin (survivors c) rfl ⟨m, hm'⟩
  rw [← hi] at hrank
  have hlt : (i : ℕ) < c [] := (hc.mem_survivors_iff i).mp hmem
  have hfilter : (survivors c).filter (· < i) = Finset.Iio i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Iio, hc.mem_survivors_iff]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨lt_trans (Fin.lt_def.mp h) hlt, h⟩
  have hval : (i : ℕ) = m := by
    rw [BranchingProcess.rankOf, hfilter, Fin.card_Iio] at hrank
    exact hrank
  funext w
  show c (i :: w) = c (⟨m, _⟩ :: w)
  congr 2
  exact Fin.ext hval

/-- The neck descent follows the chain of first children. -/
lemma neckIter_eq (hc : IsChainField N c) (n : ℕ) :
    neckIter c n = ChainClasses.ambSub c (rep N n) := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
      rw [neckIter_succ, hc.bushAt_eq (hc.one_le []), ih (hc.ambSub _), ambSub_ambSub, rep_succ']
      rfl

/-- The split set read in the field. -/
lemma splitSet_eq (hc : IsChainField N c) :
    {n | 2 ≤ skeletonDegree (neckIter c n)} = {n | 2 ≤ c (rep N n)} := by
  ext n
  simp only [Set.mem_setOf_eq, hc.neckIter_eq, (hc.ambSub _).skeletonDegree_eq, ambSub_apply,
    List.append_nil]

/-- The depth of the first split, in the field. -/
lemma gSplitDepth_eq (hc : IsChainField N c) :
    gSplitDepth c = sInf {n | 2 ≤ c (rep N n)} := by
  rw [gSplitDepth, hc.splitSet_eq]

lemma two_le_rep_gSplitDepth (hc : IsChainField N c) : 2 ≤ c (rep N (gSplitDepth c)) := by
  rw [hc.gSplitDepth_eq]
  obtain ⟨n, hn⟩ := hc.split []
  rw [List.nil_append] at hn
  exact Nat.sInf_mem (⟨n, hn⟩ : {n | 2 ≤ c (rep N n)}.Nonempty)

lemma rep_eq_one_of_lt (hc : IsChainField N c) {i : ℕ} (hi : i < gSplitDepth c) :
    c (rep N i) = 1 := by
  rw [hc.gSplitDepth_eq] at hi
  have := Nat.notMem_of_lt_sInf hi
  have h1 := hc.one_le (rep N i)
  simp only [Set.mem_setOf_eq, not_le] at this
  omega

lemma gSplitDepth_le (hc : IsChainField N c) {n : ℕ} (hn : 2 ≤ c (rep N n)) :
    gSplitDepth c ≤ n := by
  rw [hc.gSplitDepth_eq]
  exact Nat.sInf_le hn

lemma gSplitField_eq (hc : IsChainField N c) :
    gSplitField c = ChainClasses.ambSub c (rep N (gSplitDepth c)) := by
  rw [gSplitField, hc.neckIter_eq]

lemma gArity_eq (hc : IsChainField N c) : gArity c = c (rep N (gSplitDepth c)) := by
  rw [gArity, hc.gSplitField_eq, (hc.ambSub _).skeletonDegree_eq, ambSub_apply, List.append_nil]

lemma two_le_gArity (hc : IsChainField N c) : 2 ≤ gArity c := by
  rw [hc.gArity_eq]; exact hc.two_le_rep_gSplitDepth

lemma lt_N_of_lt_gArity (hc : IsChainField N c) {j : ℕ} (hj : j < gArity c) : j < N :=
  lt_of_lt_of_le (hc.gArity_eq ▸ hj) (hc.le_N _)

lemma gSplitBush_eq (hc : IsChainField N c) {j : ℕ} (hj : j < gArity c) :
    gSplitBush c j
      = ChainClasses.ambSub c (rep N (gSplitDepth c) ++ [⟨j, hc.lt_N_of_lt_gArity hj⟩]) := by
  rw [gSplitBush, hc.gSplitField_eq]
  have hj' : j < c (rep N (gSplitDepth c)) := hc.gArity_eq ▸ hj
  rw [(hc.ambSub _).bushAt_eq (by rw [ambSub_apply, List.append_nil]; exact hj'), ambSub_ambSub]

/-- The absorption test reads the depth of the first split. -/
lemma bHit_iff (hc : IsChainField N c) (R : ℕ) : bHit R c ↔ gSplitDepth c < R :=
  ⟨gSplitDepth_lt_of_bHit, fun h => bHit_of_depth_lt h hc.two_le_gArity⟩

/-- **The neck of a chain-regime sample**: a vertex of the sample is a vertex of the neck or
extends the first split by a letter below its offspring count. -/
lemma neck_cases (hc : IsChainField N c) {q : GWord N} (hq : q ∈ sample c) :
    q <+: rep N (gSplitDepth c)
      ∨ ∃ (j : Fin N) (q' : GWord N), q = rep N (gSplitDepth c) ++ j :: q'
          ∧ (j : ℕ) < c (rep N (gSplitDepth c)) := by
  set m := gSplitDepth c with hm
  have key : ∀ k i, i + k = m → rep N i <+: q →
      q <+: rep N m ∨ ∃ (j : Fin N) (q' : GWord N), q = rep N m ++ j :: q' ∧ (j : ℕ) < c (rep N m) := by
    intro k
    induction k with
    | zero =>
        intro i hi hpre
        rw [Nat.add_zero] at hi
        rw [← hi]
        obtain ⟨s, rfl⟩ := hpre
        cases s with
        | nil => exact Or.inl (by simp)
        | cons j q' =>
            refine Or.inr ⟨j, q', rfl, ?_⟩
            have h := (BranchingProcess.append_mem_sample_iff c (rep N i) (j :: q')).mp hq
            have h2 : [j] ∈ sample (fun u => c (rep N i ++ u)) :=
              BranchingProcess.Subtree.mem_of_prefix ⟨q', rfl⟩ h.2
            rw [BranchingProcess.singleton_mem_sample_iff] at h2
            simpa using h2
    | succ k ih =>
        intro i hi hpre
        obtain ⟨s, rfl⟩ := hpre
        cases s with
        | nil => exact Or.inl (by rw [List.append_nil]; exact rep_prefix_rep (by omega))
        | cons j q' =>
            have h := (BranchingProcess.append_mem_sample_iff c (rep N i) (j :: q')).mp hq
            have h2 : [j] ∈ sample (fun u => c (rep N i ++ u)) :=
              BranchingProcess.Subtree.mem_of_prefix ⟨q', rfl⟩ h.2
            rw [BranchingProcess.singleton_mem_sample_iff] at h2
            have hone : c (rep N i) = 1 := hc.rep_eq_one_of_lt (by omega)
            simp only [List.append_nil, hone] at h2
            have hj : j = 0 := Fin.ext (by simpa using h2)
            subst hj
            exact ih (i + 1) (by omega) ⟨q', by rw [rep_succ, List.append_assoc]; rfl⟩
  exact key m 0 (by simp) List.nil_prefix

end IsChainField

/-! ### The blob of a cluster root, read off its trace -/

/-- A natural number read as a letter, modulo `N`. -/
def ltr (N : ℕ) [NeZero N] (j : ℕ) : Fin N := Fin.ofNat N j

lemma val_ltr_of_lt {j : ℕ} (hj : j < N) : ((ltr N j : Fin N) : ℕ) = j := by
  simp [ltr, Nat.mod_eq_of_lt hj]

@[simp] lemma ltr_zero : ltr N 0 = 0 := Fin.ofNat_zero N

lemma ltr_val (b : Fin N) : ltr N (b : ℕ) = b := Fin.ext (val_ltr_of_lt b.isLt)

/-- The planted child of a port: the port followed by its slot. -/
def rootOf (x : GWord N × ℕ) : GWord N := x.1 ++ [ltr N x.2]

mutual

/-- **The vertices of a blob below the exits `j, j + 1, …` of the split at `s`**, relative to
the cluster root whose field is `d`: the vertices hanging below each exit in turn. -/
noncomputable def splitVerts (R : ℕ) (d : GWord N → ℕ) :
    GWord N → ℕ → List BTrace → List (GWord N)
  | _, _, [] => []
  | s, j, t :: ts => hangVerts R d s j t ++ splitVerts R d s (j + 1) ts

/-- **The vertices of a blob hanging below the exit `j` of the split at `s`** with trace
`t`: none for an unspent exit, the `R` revealed neck vertices for a spent one, and for a
hit the neck down to the absorbed split followed by the vertices below its exits. -/
noncomputable def hangVerts (R : ℕ) (d : GWord N → ℕ) :
    GWord N → ℕ → BTrace → List (GWord N)
  | _, _, .skip => []
  | s, j, .miss => (List.range R).map fun i => s ++ ltr N j :: rep N i
  | s, j, .hit l =>
      (List.range (gSplitDepth (ambSub d (s ++ [ltr N j])) + 1)).map
          (fun i => s ++ ltr N j :: rep N i)
        ++ splitVerts R d
            (s ++ ltr N j :: rep N (gSplitDepth (ambSub d (s ++ [ltr N j])))) 0 l

end

mutual

/-- **The ports of a blob at the exits `j, j + 1, …` of the split at `s`**, in the order the
automaton hands the presented children. -/
noncomputable def splitPorts (R : ℕ) (d : GWord N → ℕ) :
    GWord N → ℕ → List BTrace → List (GWord N × ℕ)
  | _, _, [] => []
  | s, j, t :: ts => hangPorts R d s j t ++ splitPorts R d s (j + 1) ts

/-- **The ports of a blob at the exit `j` of the split at `s`** with trace `t`: the split
itself with slot `j` for an unspent exit, the last revealed neck vertex with slot `0` for a
spent one, and for a hit the ports below the absorbed split. -/
noncomputable def hangPorts (R : ℕ) (d : GWord N → ℕ) :
    GWord N → ℕ → BTrace → List (GWord N × ℕ)
  | s, j, .skip => [(s, j)]
  | s, j, .miss => [(s ++ ltr N j :: rep N (R - 1), 0)]
  | s, j, .hit l =>
      splitPorts R d
        (s ++ ltr N j :: rep N (gSplitDepth (ambSub d (s ++ [ltr N j])))) 0 l

end

mutual

/-- **A trace list fits the exits `j, j + 1, …` of the split at `s`**: the list runs exactly
to the offspring count of the split, and each trace fits its exit. -/
def BFit (R : ℕ) (d : GWord N → ℕ) : GWord N → ℕ → List BTrace → Prop
  | s, j, [] => j = d s
  | s, j, t :: ts => BFitT R d s j t ∧ BFit R d s (j + 1) ts

/-- **A trace fits the exit `j` of the split at `s`**: a miss finds no split within the
revealing depth, a hit finds one, records its arity, and its child traces fit the exits
of the absorbed split. -/
def BFitT (R : ℕ) (d : GWord N → ℕ) : GWord N → ℕ → BTrace → Prop
  | _, _, .skip => True
  | s, j, .miss => R ≤ gSplitDepth (ambSub d (s ++ [ltr N j]))
  | s, j, .hit l =>
      gSplitDepth (ambSub d (s ++ [ltr N j])) < R
        ∧ l.length = gArity (ambSub d (s ++ [ltr N j]))
        ∧ BFit R d
            (s ++ ltr N j :: rep N (gSplitDepth (ambSub d (s ++ [ltr N j])))) 0 l

end

mutual

/-- The nesting depth of the hits of a trace. -/
def hdepth : BTrace → ℕ
  | .skip => 0
  | .miss => 0
  | .hit l => hdepthL l + 1

/-- The nesting depth of the hits of a list of traces. -/
def hdepthL : List BTrace → ℕ
  | [] => 0
  | t :: ts => max (hdepth t) (hdepthL ts)

end

@[simp] lemma hdepth_skip : hdepth .skip = 0 := by rw [hdepth]

@[simp] lemma hdepth_miss : hdepth .miss = 0 := by rw [hdepth]

lemma hdepth_hit (l : List BTrace) : hdepth (.hit l) = hdepthL l + 1 := by rw [hdepth]

@[simp] lemma hdepthL_nil : hdepthL [] = 0 := by rw [hdepthL]

lemma hdepthL_cons (t : BTrace) (ts : List BTrace) :
    hdepthL (t :: ts) = max (hdepth t) (hdepthL ts) := by rw [hdepthL]

omit [NeZero N] in
/-- The fuel bounds the nesting depth of the hits of the automaton's output. -/
lemma hdepthL_bExplore_le (R : ℕ) (dec : List (Option ℕ) → Bool) :
    ∀ (fuel : ℕ) (ds : List (GWord N → ℕ)) (st : Bool × List (Option ℕ)),
      hdepthL (bExplore R dec fuel ds st).1 ≤ fuel
  | _, [], _ => by simp
  | fuel, d :: rest, (stopped, evs) => by
      by_cases h : stopped = true ∨ dec evs = false
      · rw [bExplore_cons_stop R dec fuel d rest h]
        simp only [hdepthL_cons, hdepth_skip]
        simpa using hdepthL_bExplore_le R dec fuel rest (true, evs)
      · by_cases hd : bHit R d
        · match fuel with
          | 0 =>
              rw [bExplore_cons_hit_zero R dec rest h hd]
              simp only [hdepthL_cons, hdepth_skip]
              simpa using hdepthL_bExplore_le R dec 0 rest (true, evs)
          | fuel' + 1 =>
              rw [bExplore_cons_hit R dec fuel' rest h hd]
              simp only [hdepthL_cons, hdepth_hit]
              have h1 := hdepthL_bExplore_le R dec fuel' (bChildren d)
                (false, evs ++ [some (gArity d - 1)])
              have h2 := hdepthL_bExplore_le R dec (fuel' + 1) rest
                (bExplore R dec fuel' (bChildren d) (false, evs ++ [some (gArity d - 1)])).2
              omega
        · rw [bExplore_cons_miss R dec fuel rest h hd]
          simp only [hdepthL_cons, hdepth_miss]
          simpa using hdepthL_bExplore_le R dec fuel rest (false, evs ++ [none])
  termination_by fuel ds _ => (fuel, ds.length)
  decreasing_by
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.left _ _ (by omega)
    · exact Prod.Lex.right _ (by simp)
    · exact Prod.Lex.right _ (by simp)

section BlobLemmas

variable {R : ℕ} {d : GWord N → ℕ}

@[simp] lemma splitVerts_nil (s : GWord N) (j : ℕ) : splitVerts R d s j [] = [] := by
  rw [splitVerts]

lemma splitVerts_cons (s : GWord N) (j : ℕ) (t : BTrace) (ts : List BTrace) :
    splitVerts R d s j (t :: ts) = hangVerts R d s j t ++ splitVerts R d s (j + 1) ts := by
  rw [splitVerts]

@[simp] lemma hangVerts_skip (s : GWord N) (j : ℕ) : hangVerts R d s j .skip = [] := by
  rw [hangVerts]

lemma hangVerts_miss (s : GWord N) (j : ℕ) :
    hangVerts R d s j .miss = (List.range R).map fun i => s ++ ltr N j :: rep N i := by
  rw [hangVerts]

lemma hangVerts_hit (s : GWord N) (j : ℕ) (l : List BTrace) :
    hangVerts R d s j (.hit l)
      = (List.range (gSplitDepth (ambSub d (s ++ [ltr N j])) + 1)).map (fun i => s ++ ltr N j :: rep N i)
        ++ splitVerts R d (s ++ ltr N j :: rep N (gSplitDepth (ambSub d (s ++ [ltr N j])))) 0 l := by
  rw [hangVerts]

@[simp] lemma splitPorts_nil (s : GWord N) (j : ℕ) : splitPorts R d s j [] = [] := by
  rw [splitPorts]

lemma splitPorts_cons (s : GWord N) (j : ℕ) (t : BTrace) (ts : List BTrace) :
    splitPorts R d s j (t :: ts) = hangPorts R d s j t ++ splitPorts R d s (j + 1) ts := by
  rw [splitPorts]

@[simp] lemma hangPorts_skip (s : GWord N) (j : ℕ) : hangPorts R d s j .skip = [(s, j)] := by
  rw [hangPorts]

@[simp] lemma hangPorts_miss (s : GWord N) (j : ℕ) :
    hangPorts R d s j .miss = [(s ++ ltr N j :: rep N (R - 1), 0)] := by
  rw [hangPorts]

lemma hangPorts_hit (s : GWord N) (j : ℕ) (l : List BTrace) :
    hangPorts R d s j (.hit l) = splitPorts R d (s ++ ltr N j :: rep N (gSplitDepth (ambSub d (s ++ [ltr N j])))) 0 l := by
  rw [hangPorts]

@[simp] lemma bFit_nil (s : GWord N) (j : ℕ) : BFit R d s j [] ↔ j = d s := by
  rw [BFit]

lemma bFit_cons (s : GWord N) (j : ℕ) (t : BTrace) (ts : List BTrace) :
    BFit R d s j (t :: ts) ↔ BFitT R d s j t ∧ BFit R d s (j + 1) ts := by
  rw [BFit]

@[simp] lemma bFitT_skip (s : GWord N) (j : ℕ) : BFitT R d s j .skip := by
  rw [BFitT]; trivial

lemma bFitT_miss (s : GWord N) (j : ℕ) : BFitT R d s j .miss ↔ R ≤ gSplitDepth (ambSub d (s ++ [ltr N j])) := by
  rw [BFitT]

lemma bFitT_hit (s : GWord N) (j : ℕ) (l : List BTrace) :
    BFitT R d s j (.hit l)
      ↔ gSplitDepth (ambSub d (s ++ [ltr N j])) < R ∧ l.length = gArity (ambSub d (s ++ [ltr N j]))
          ∧ BFit R d (s ++ ltr N j :: rep N (gSplitDepth (ambSub d (s ++ [ltr N j])))) 0 l := by
  rw [BFitT]

/-- A fitting list runs exactly to the offspring count. -/
lemma BFit.length : ∀ {s : GWord N} {j : ℕ} {ts : List BTrace}, BFit R d s j ts →
    j + ts.length = d s
  | _, _, [], h => by rw [bFit_nil] at h; simp [h]
  | _, _, _ :: ts, h => by
      rw [bFit_cons] at h
      have := BFit.length h.2
      simp only [List.length_cons]
      omega

mutual

/-- The port count of one exit is its handed count. -/
lemma length_hangPorts_eq : ∀ (t : BTrace) (s : GWord N) (j : ℕ),
    (hangPorts R d s j t).length = bCount t
  | .skip, _, _ => by simp
  | .miss, _, _ => by simp
  | .hit l, s, j => by
      rw [hangPorts_hit, bCount_hit]
      exact length_splitPorts_eq l _ _

/-- The port count of a trace list is its handed count. -/
lemma length_splitPorts_eq : ∀ (ts : List BTrace) (s : GWord N) (j : ℕ),
    (splitPorts R d s j ts).length = bCountL ts
  | [], _, _ => by simp
  | t :: ts, s, j => by
      rw [splitPorts_cons, List.length_append, length_hangPorts_eq t s j,
        length_splitPorts_eq ts s (j + 1), bCountL_cons]

end


/-! #### The shape of the vertices and the ports -/

/-- Membership below a list of exits, exit by exit. -/
lemma mem_splitVerts_iff : ∀ (ts : List BTrace) (s : GWord N) (j : ℕ) {v : GWord N},
    v ∈ splitVerts R d s j ts ↔ ∃ i, ∃ hi : i < ts.length, v ∈ hangVerts R d s (j + i) ts[i]
  | [], s, j, v => by simp
  | t :: ts, s, j, v => by
      rw [splitVerts_cons, List.mem_append, mem_splitVerts_iff ts s (j + 1)]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact ⟨0, by simp, by simpa using h⟩
        · exact ⟨i + 1, by simp; omega, by
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using h⟩
      · rintro ⟨i, hi, h⟩
        cases i with
        | zero => exact Or.inl (by simpa using h)
        | succ i => exact Or.inr ⟨i, by simpa using hi, by
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using h⟩

/-- Membership among the ports of a list of exits, exit by exit. -/
lemma mem_splitPorts_iff : ∀ (ts : List BTrace) (s : GWord N) (j : ℕ) {x : GWord N × ℕ},
    x ∈ splitPorts R d s j ts ↔ ∃ i, ∃ hi : i < ts.length, x ∈ hangPorts R d s (j + i) ts[i]
  | [], s, j, x => by simp
  | t :: ts, s, j, x => by
      rw [splitPorts_cons, List.mem_append, mem_splitPorts_iff ts s (j + 1)]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact ⟨0, by simp, by simpa using h⟩
        · exact ⟨i + 1, by simp; omega, by
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using h⟩
      · rintro ⟨i, hi, h⟩
        cases i with
        | zero => exact Or.inl (by simpa using h)
        | succ i => exact Or.inr ⟨i, by simpa using hi, by
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using h⟩

mutual

/-- A vertex hanging below an exit extends the exit's child. -/
lemma mem_hangVerts_shape : ∀ (t : BTrace) (s : GWord N) (j : ℕ) {v : GWord N},
    v ∈ hangVerts R d s j t → ∃ q, v = s ++ ltr N j :: q
  | .skip, _, _, _, h => by simp at h
  | .miss, s, j, v, h => by
      rw [hangVerts_miss, List.mem_map] at h
      obtain ⟨i, -, rfl⟩ := h
      exact ⟨_, rfl⟩
  | .hit l, s, j, v, h => by
      rw [hangVerts_hit, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
        exact ⟨_, rfl⟩
      · obtain ⟨i, -, q, hq⟩ := mem_splitVerts_shape l _ _ h
        exact ⟨rep N (gSplitDepth (ambSub d (s ++ [ltr N j]))) ++ ltr N (0 + i) :: q, by
          rw [hq]; simp⟩

/-- A vertex below a list of exits extends the child of one of them. -/
lemma mem_splitVerts_shape : ∀ (ts : List BTrace) (s : GWord N) (j : ℕ) {v : GWord N},
    v ∈ splitVerts R d s j ts → ∃ i, i < ts.length ∧ ∃ q, v = s ++ ltr N (j + i) :: q
  | [], _, _, _, h => by simp at h
  | t :: ts, s, j, v, h => by
      rw [splitVerts_cons, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨q, hq⟩ := mem_hangVerts_shape t s j h
        exact ⟨0, by simp, q, by simpa using hq⟩
      · obtain ⟨i, hi, q, hq⟩ := mem_splitVerts_shape ts s (j + 1) h
        exact ⟨i + 1, by simp; omega, q, by rw [hq]; congr 3; omega⟩

end

mutual

/-- The planted child of a port below an exit extends the exit's child. -/
lemma mem_hangPorts_shape : ∀ (t : BTrace) (s : GWord N) (j : ℕ) {x : GWord N × ℕ},
    x ∈ hangPorts R d s j t → s ++ [ltr N j] <+: rootOf x
  | .skip, s, j, x, h => by
      rw [hangPorts_skip, List.mem_singleton] at h
      rw [h, rootOf]
  | .miss, s, j, x, h => by
      rw [hangPorts_miss, List.mem_singleton] at h
      rw [h, rootOf]
      exact ⟨rep N (R - 1) ++ [ltr N 0], by simp⟩
  | .hit l, s, j, x, h => by
      rw [hangPorts_hit] at h
      obtain ⟨i, -, hpre⟩ := mem_splitPorts_shape l _ _ h
      exact ((show s ++ [ltr N j] <+: s ++ ltr N j :: rep N (gSplitDepth (ambSub d (s ++ [ltr N j]))) from
        ⟨rep N (gSplitDepth (ambSub d (s ++ [ltr N j]))), by simp⟩).trans (List.prefix_append _ _)).trans hpre

/-- The planted child of a port below a list of exits extends the child of one of them. -/
lemma mem_splitPorts_shape : ∀ (ts : List BTrace) (s : GWord N) (j : ℕ) {x : GWord N × ℕ},
    x ∈ splitPorts R d s j ts → ∃ i, i < ts.length ∧ s ++ [ltr N (j + i)] <+: rootOf x
  | [], _, _, _, h => by simp at h
  | t :: ts, s, j, x, h => by
      rw [splitPorts_cons, List.mem_append] at h
      rcases h with h | h
      · exact ⟨0, by simp, by simpa using mem_hangPorts_shape t s j h⟩
      · obtain ⟨i, hi, hpre⟩ := mem_splitPorts_shape ts s (j + 1) h
        exact ⟨i + 1, by simp; omega, by rwa [show j + (i + 1) = j + 1 + i by omega]⟩

end

omit [NeZero N] in
/-- Two words extending a common stem by distinct letters are prefix-incomparable, and so
are their extensions. -/
lemma not_prefix_of_letter_ne {s : GWord N} {a b : Fin N} (hab : a ≠ b) {u v : GWord N}
    (hu : s ++ [a] <+: u) (hv : s ++ [b] <+: v) : ¬ u <+: v := by
  intro huv
  have h := hu.trans huv
  rcases List.prefix_or_prefix_of_prefix h hv with h' | h'
  · have := h'.eq_of_length (by simp)
    simp at this
    exact hab this
  · have := h'.eq_of_length (by simp)
    simp at this
    exact hab this.symm

/-! #### Prefix closure -/

/-- A prefix of a neck vertex below an exit is a neck vertex or a prefix of the split. -/
lemma prefix_neck_cases {s : GWord N} {a : Fin N} {i : ℕ} {u : GWord N}
    (h : u <+: s ++ a :: rep N i) :
    u <+: s ∨ ∃ i', i' ≤ i ∧ u = s ++ a :: rep N i' := by
  rcases List.prefix_or_prefix_of_prefix h (List.prefix_append s (a :: rep N i)) with h' | h'
  · exact Or.inl h'
  · obtain ⟨q, rfl⟩ := h'
    rw [List.prefix_append_right_inj] at h
    cases q with
    | nil => exact Or.inl (by simp)
    | cons b q =>
        rw [List.cons_prefix_cons] at h
        obtain ⟨rfl, hq⟩ := h
        refine Or.inr ⟨q.length, by simpa using hq.length_le, ?_⟩
        rw [eq_rep_of_prefix hq, rep_length]

mutual

/-- A prefix of a vertex hanging below an exit is a vertex hanging there or a prefix of
the split. -/
lemma prefix_mem_hangVerts : ∀ (t : BTrace) (s : GWord N) (j : ℕ) {u v : GWord N},
    v ∈ hangVerts R d s j t → u <+: v → u <+: s ∨ u ∈ hangVerts R d s j t
  | .skip, _, _, _, _, h, _ => by simp at h
  | .miss, s, j, u, v, h, huv => by
      rw [hangVerts_miss, List.mem_map] at h
      obtain ⟨i, hi, rfl⟩ := h
      rcases prefix_neck_cases huv with h' | ⟨i', hi', rfl⟩
      · exact Or.inl h'
      · refine Or.inr ?_
        rw [hangVerts_miss, List.mem_map]
        exact ⟨i', by rw [List.mem_range] at hi ⊢; omega, rfl⟩
  | .hit l, s, j, u, v, h, huv => by
      rw [hangVerts_hit, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
        rcases prefix_neck_cases huv with h' | ⟨i', hi', rfl⟩
        · exact Or.inl h'
        · refine Or.inr ?_
          rw [hangVerts_hit, List.mem_append, List.mem_map]
          exact Or.inl ⟨i', by rw [List.mem_range] at hi ⊢; omega, rfl⟩
      · rcases prefix_mem_splitVerts l _ _ h huv with h' | h'
        · rcases prefix_neck_cases h' with h'' | ⟨i', hi', rfl⟩
          · exact Or.inl h''
          · refine Or.inr ?_
            rw [hangVerts_hit, List.mem_append, List.mem_map]
            exact Or.inl ⟨i', by rw [List.mem_range]; omega, rfl⟩
        · refine Or.inr ?_
          rw [hangVerts_hit, List.mem_append]
          exact Or.inr h'

/-- A prefix of a vertex below a list of exits is such a vertex or a prefix of the split. -/
lemma prefix_mem_splitVerts : ∀ (ts : List BTrace) (s : GWord N) (j : ℕ) {u v : GWord N},
    v ∈ splitVerts R d s j ts → u <+: v → u <+: s ∨ u ∈ splitVerts R d s j ts
  | [], _, _, _, _, h, _ => by simp at h
  | t :: ts, s, j, u, v, h, huv => by
      rw [splitVerts_cons, List.mem_append] at h
      rcases h with h | h
      · rcases prefix_mem_hangVerts t s j h huv with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by rw [splitVerts_cons, List.mem_append]; exact Or.inl h')
      · rcases prefix_mem_splitVerts ts s (j + 1) h huv with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by rw [splitVerts_cons, List.mem_append]; exact Or.inr h')

end

/-! #### The ports are vertices and the planted children are not -/

mutual

/-- A port below an exit is the split itself or a vertex hanging below the exit. -/
lemma port_mem_hangVerts (hR : 1 ≤ R) : ∀ (t : BTrace) (s : GWord N) (j : ℕ) {x : GWord N × ℕ},
    x ∈ hangPorts R d s j t → x.1 = s ∨ x.1 ∈ hangVerts R d s j t
  | .skip, s, j, x, h => by
      rw [hangPorts_skip, List.mem_singleton] at h
      exact Or.inl (by rw [h])
  | .miss, s, j, x, h => by
      rw [hangPorts_miss, List.mem_singleton] at h
      refine Or.inr ?_
      rw [h, hangVerts_miss, List.mem_map]
      exact ⟨R - 1, by rw [List.mem_range]; omega, rfl⟩
  | .hit l, s, j, x, h => by
      rw [hangPorts_hit] at h
      refine Or.inr ?_
      rw [hangVerts_hit, List.mem_append]
      rcases port_mem_splitVerts hR l _ _ h with h' | h'
      · exact Or.inl (List.mem_map.mpr ⟨gSplitDepth (ambSub d (s ++ [ltr N j])), by simp, by rw [h']⟩)
      · exact Or.inr h'

/-- A port below a list of exits is the split itself or a vertex below one of them. -/
lemma port_mem_splitVerts (hR : 1 ≤ R) :
    ∀ (ts : List BTrace) (s : GWord N) (j : ℕ) {x : GWord N × ℕ},
    x ∈ splitPorts R d s j ts → x.1 = s ∨ x.1 ∈ splitVerts R d s j ts
  | [], _, _, _, h => by simp at h
  | t :: ts, s, j, x, h => by
      rw [splitPorts_cons, List.mem_append] at h
      rcases h with h | h
      · rcases port_mem_hangVerts hR t s j h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by rw [splitVerts_cons, List.mem_append]; exact Or.inl h')
      · rcases port_mem_splitVerts hR ts s (j + 1) h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by rw [splitVerts_cons, List.mem_append]; exact Or.inr h')

end


/-! #### The planted children are no vertices, and are pairwise distinct -/

/-- The planted child of a port below an exit is the root of the exit's child or deeper. -/
lemma length_root_of_mem_hangPorts {t : BTrace} {s : GWord N} {j : ℕ} {x : GWord N × ℕ}
    (h : x ∈ hangPorts R d s j t) : s.length + 1 ≤ (rootOf x).length := by
  have := (mem_hangPorts_shape t s j h).length_le
  simpa using this

/-- Two exits of one fitting list carry distinct letters. -/
lemma ofNat_ne_of_fit (hd : IsChainField N d) {s : GWord N} {j : ℕ} {ts : List BTrace}
    (hfit : BFit R d s j ts) {a b : ℕ} (ha : a < j + ts.length) (hb : b < j + ts.length)
    (hab : a ≠ b) : ltr N a ≠ ltr N b := by
  have hlen := hfit.length
  have hN := hd.le_N s
  intro h
  have := congrArg Fin.val h
  rw [val_ltr_of_lt (by omega), val_ltr_of_lt (by omega)] at this
  exact hab this

mutual

/-- The planted child of a port below an exit hangs below no exit of its list. -/
lemma root_not_mem_hangVerts (hR : 1 ≤ R) (hd : IsChainField N d) :
    ∀ (t : BTrace) (s : GWord N) (j : ℕ) {x : GWord N × ℕ}, BFitT R d s j t →
      x ∈ hangPorts R d s j t → rootOf x ∉ hangVerts R d s j t
  | .skip, _, _, _, _, _, h => by simp at h
  | .miss, s, j, x, _, hx, h => by
      rw [hangPorts_miss, List.mem_singleton] at hx
      rw [hangVerts_miss, List.mem_map] at h
      obtain ⟨i, hi, hv⟩ := h
      rw [List.mem_range] at hi
      rw [hx, rootOf] at hv
      have := congrArg List.length hv
      simp at this
      omega
  | .hit l, s, j, x, hfit, hx, h => by
      rw [bFitT_hit] at hfit
      rw [hangPorts_hit] at hx
      rw [hangVerts_hit, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨i, hi, hv⟩ := List.mem_map.mp h
        rw [List.mem_range] at hi
        obtain ⟨i', -, hpre⟩ := mem_splitPorts_shape l _ _ hx
        have h1 := hpre.length_le
        have h2 := congrArg List.length hv
        simp at h1 h2
        omega
      · exact root_not_mem_splitVerts hR hd l _ _ hfit.2.2 hx h

/-- The planted child of a port below a list of exits hangs below none of them. -/
lemma root_not_mem_splitVerts (hR : 1 ≤ R) (hd : IsChainField N d) :
    ∀ (ts : List BTrace) (s : GWord N) (j : ℕ) {x : GWord N × ℕ}, BFit R d s j ts →
      x ∈ splitPorts R d s j ts → rootOf x ∉ splitVerts R d s j ts
  | [], _, _, _, _, hx, _ => by simp at hx
  | t :: ts, s, j, x, hfit, hx, h => by
      have hlen := hfit.length
      rw [bFit_cons] at hfit
      rw [splitPorts_cons, List.mem_append] at hx
      rw [splitVerts_cons, List.mem_append] at h
      rcases hx with hx | hx <;> rcases h with h | h
      · exact root_not_mem_hangVerts hR hd t s j hfit.1 hx h
      · obtain ⟨i, hi, q, hq⟩ := mem_splitVerts_shape ts s (j + 1) h
        have hpre := mem_hangPorts_shape t s j hx
        have hne : ltr N j ≠ ltr N (j + 1 + i) := by
          refine ofNat_ne_of_fit hd (bFit_cons s j t ts |>.mpr hfit) ?_ ?_ (by omega)
          · simp
          · simp only [List.length_cons]; omega
        exact not_prefix_of_letter_ne hne hpre (show s ++ [ltr N (j + 1 + i)] <+: rootOf x from
          ⟨q, by rw [hq]; simp⟩) (List.prefix_refl _)
      · obtain ⟨i, hi, hpre⟩ := mem_splitPorts_shape ts s (j + 1) hx
        obtain ⟨q, hq⟩ := mem_hangVerts_shape t s j h
        have hne : ltr N (j + 1 + i) ≠ ltr N j := by
          refine ofNat_ne_of_fit hd (bFit_cons s j t ts |>.mpr hfit) ?_ ?_ (by omega)
          · simp only [List.length_cons]; omega
          · simp
        exact not_prefix_of_letter_ne hne hpre (show s ++ [ltr N j] <+: rootOf x from
          ⟨q, by rw [hq]; simp⟩) (List.prefix_refl _)
      · exact root_not_mem_splitVerts hR hd ts s (j + 1) hfit.2 hx h

end

mutual

/-- The planted children of the ports below one exit are pairwise distinct. -/
lemma nodup_roots_hangPorts (hd : IsChainField N d) :
    ∀ (t : BTrace) (s : GWord N) (j : ℕ), BFitT R d s j t →
      ((hangPorts R d s j t).map rootOf).Nodup
  | .skip, _, _, _ => by simp
  | .miss, _, _, _ => by simp
  | .hit l, s, j, hfit => by
      rw [bFitT_hit] at hfit
      rw [hangPorts_hit]
      exact nodup_roots_splitPorts hd l _ _ hfit.2.2

/-- The planted children of the ports below a list of exits are pairwise distinct. -/
lemma nodup_roots_splitPorts (hd : IsChainField N d) :
    ∀ (ts : List BTrace) (s : GWord N) (j : ℕ), BFit R d s j ts →
      ((splitPorts R d s j ts).map rootOf).Nodup
  | [], _, _, _ => by simp
  | t :: ts, s, j, hfit => by
      have hlen := hfit.length
      have hfit' := hfit
      rw [bFit_cons] at hfit
      rw [splitPorts_cons, List.map_append]
      refine List.Nodup.append (nodup_roots_hangPorts hd t s j hfit.1)
        (nodup_roots_splitPorts hd ts s (j + 1) hfit.2) ?_
      intro r hr hr'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hr'
      have hpre := mem_hangPorts_shape t s j hx
      obtain ⟨i, hi, hpre'⟩ := mem_splitPorts_shape ts s (j + 1) hy
      have hne : ltr N j ≠ ltr N (j + 1 + i) := by
        refine ofNat_ne_of_fit hd hfit' ?_ ?_ (by omega)
        · simp
        · simp only [List.length_cons]; omega
      exact not_prefix_of_letter_ne hne hpre hpre' (hxy ▸ List.prefix_refl _)

end


/-! #### The vertices and the planted children lie in the sample -/

/-- The child of a split vertex at an exit lies in the sample. -/
lemma exit_mem_sample (hd : IsChainField N d) {s : GWord N} (hs : s ∈ sample d) {j : ℕ}
    (hj : j < d s) : s ++ [ltr N j] ∈ sample d := by
  rw [BranchingProcess.mem_sample_append_singleton]
  exact ⟨hs, by rw [val_ltr_of_lt (lt_of_lt_of_le hj (hd.le_N s))]; exact hj⟩

/-- The chain of first children below a sample vertex lies in the sample. -/
lemma append_rep_mem_sample (hd : IsChainField N d) {s : GWord N} (hs : s ∈ sample d) (i : ℕ) :
    s ++ rep N i ∈ sample d :=
  (mem_sample_ambSub_iff hs).mp ((hd.ambSub s).rep_mem_sample i)

lemma neck_mem_sample (hd : IsChainField N d) {s : GWord N} (hs : s ∈ sample d) {j : ℕ}
    (hj : j < d s) (i : ℕ) : s ++ ltr N j :: rep N i ∈ sample d := by
  have := append_rep_mem_sample hd (exit_mem_sample hd hs hj) i
  simpa using this

mutual

/-- The vertices hanging below an exit lie in the sample. -/
lemma mem_sample_of_mem_hangVerts (hd : IsChainField N d) :
    ∀ (t : BTrace) (s : GWord N) (j : ℕ) {v : GWord N}, s ∈ sample d → j < d s →
      BFitT R d s j t → v ∈ hangVerts R d s j t → v ∈ sample d
  | .skip, _, _, _, _, _, _, h => by simp at h
  | .miss, s, j, v, hs, hj, _, h => by
      rw [hangVerts_miss, List.mem_map] at h
      obtain ⟨i, -, rfl⟩ := h
      exact neck_mem_sample hd hs hj i
  | .hit l, s, j, v, hs, hj, hfit, h => by
      rw [bFitT_hit] at hfit
      rw [hangVerts_hit, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
        exact neck_mem_sample hd hs hj i
      · exact mem_sample_of_mem_splitVerts hd l _ _ (neck_mem_sample hd hs hj _) hfit.2.2 h

/-- The vertices below a list of exits lie in the sample. -/
lemma mem_sample_of_mem_splitVerts (hd : IsChainField N d) :
    ∀ (ts : List BTrace) (s : GWord N) (j : ℕ) {v : GWord N}, s ∈ sample d →
      BFit R d s j ts → v ∈ splitVerts R d s j ts → v ∈ sample d
  | [], _, _, _, _, _, h => by simp at h
  | t :: ts, s, j, v, hs, hfit, h => by
      have hlen := hfit.length
      rw [bFit_cons] at hfit
      rw [splitVerts_cons, List.mem_append] at h
      rcases h with h | h
      · exact mem_sample_of_mem_hangVerts hd t s j hs (by simp at hlen; omega) hfit.1 h
      · exact mem_sample_of_mem_splitVerts hd ts s (j + 1) hs hfit.2 h

end

mutual

/-- The planted children of the ports below an exit lie in the sample. -/
lemma root_mem_sample_of_mem_hangPorts (hd : IsChainField N d) :
    ∀ (t : BTrace) (s : GWord N) (j : ℕ) {x : GWord N × ℕ}, s ∈ sample d → j < d s →
      BFitT R d s j t → x ∈ hangPorts R d s j t → rootOf x ∈ sample d
  | .skip, s, j, x, hs, hj, _, h => by
      rw [hangPorts_skip, List.mem_singleton] at h
      rw [h, rootOf]
      exact exit_mem_sample hd hs hj
  | .miss, s, j, x, hs, hj, _, h => by
      rw [hangPorts_miss, List.mem_singleton] at h
      rw [h, rootOf]
      rcases R with _ | R'
      · have h1 := neck_mem_sample hd hs hj 1
        rw [rep_succ', rep_zero] at h1
        simpa [ltr_zero] using h1
      · have h1 := neck_mem_sample hd hs hj (R' + 1)
        rw [Nat.succ_sub_one, rep_succ, ltr_zero] at *
        simpa using h1
  | .hit l, s, j, x, hs, hj, hfit, h => by
      rw [bFitT_hit] at hfit
      rw [hangPorts_hit] at h
      exact root_mem_sample_of_mem_splitPorts hd l _ _ (neck_mem_sample hd hs hj _) hfit.2.2 h

/-- The planted children of the ports below a list of exits lie in the sample. -/
lemma root_mem_sample_of_mem_splitPorts (hd : IsChainField N d) :
    ∀ (ts : List BTrace) (s : GWord N) (j : ℕ) {x : GWord N × ℕ}, s ∈ sample d →
      BFit R d s j ts → x ∈ splitPorts R d s j ts → rootOf x ∈ sample d
  | [], _, _, _, _, _, h => by simp at h
  | t :: ts, s, j, x, hs, hfit, h => by
      have hlen := hfit.length
      rw [bFit_cons] at hfit
      rw [splitPorts_cons, List.mem_append] at h
      rcases h with h | h
      · exact root_mem_sample_of_mem_hangPorts hd t s j hs (by simp at hlen; omega) hfit.1 h
      · exact root_mem_sample_of_mem_splitPorts hd ts s (j + 1) hs hfit.2 h

end

mutual

/-- The slots of the ports below an exit are letters. -/
lemma slot_lt_of_mem_hangPorts (hd : IsChainField N d) :
    ∀ (t : BTrace) (s : GWord N) (j : ℕ) {x : GWord N × ℕ}, j < d s →
      BFitT R d s j t → x ∈ hangPorts R d s j t → x.2 < N
  | .skip, s, j, x, hj, _, h => by
      rw [hangPorts_skip, List.mem_singleton] at h
      rw [h]
      exact lt_of_lt_of_le hj (hd.le_N s)
  | .miss, s, j, x, _, _, h => by
      rw [hangPorts_miss, List.mem_singleton] at h
      rw [h]
      exact Nat.pos_of_ne_zero (NeZero.ne N)
  | .hit l, s, j, x, _, hfit, h => by
      rw [bFitT_hit] at hfit
      rw [hangPorts_hit] at h
      exact slot_lt_of_mem_splitPorts hd l _ _ hfit.2.2 h

/-- The slots of the ports below a list of exits are letters. -/
lemma slot_lt_of_mem_splitPorts (hd : IsChainField N d) :
    ∀ (ts : List BTrace) (s : GWord N) (j : ℕ) {x : GWord N × ℕ},
      BFit R d s j ts → x ∈ splitPorts R d s j ts → x.2 < N
  | [], _, _, _, _, h => by simp at h
  | t :: ts, s, j, x, hfit, h => by
      have hlen := hfit.length
      rw [bFit_cons] at hfit
      rw [splitPorts_cons, List.mem_append] at h
      rcases h with h | h
      · exact slot_lt_of_mem_hangPorts hd t s j (by simp at hlen; omega) hfit.1 h
      · exact slot_lt_of_mem_splitPorts hd ts s (j + 1) hfit.2 h

end

/-! #### Every vertex of the sample below a split is absorbed or handed on -/

mutual

/-- **The cover below one exit**: a vertex of the sample below an exit is absorbed by the
blob or lies below the planted child of one of the exit's ports. -/
lemma cover_hangVerts (hR : 1 ≤ R) (hd : IsChainField N d) :
    ∀ (t : BTrace) (s : GWord N) (j : ℕ) {q : GWord N}, BFitT R d s j t → j < d s →
      s ++ ltr N j :: q ∈ sample d →
      s ++ ltr N j :: q ∈ hangVerts R d s j t
        ∨ ∃ x ∈ hangPorts R d s j t, rootOf x <+: s ++ ltr N j :: q
  | .skip, s, j, q, _, _, _ => by
      refine Or.inr ⟨(s, j), by simp, ?_⟩
      rw [rootOf]
      exact ⟨q, by simp⟩
  | .miss, s, j, q, hfit, hj, hq => by
      rw [bFitT_miss] at hfit
      have hqe : q ∈ sample (ambSub d (s ++ [ltr N j])) := by
        rw [mem_sample_ambSub_iff (exit_mem_sample hd (BranchingProcess.Subtree.mem_of_prefix
          (List.prefix_append _ _) hq) hj)]
        simpa using hq
      by_cases hlt : q.length < R
      · refine Or.inl ?_
        rw [hangVerts_miss, List.mem_map]
        refine ⟨q.length, List.mem_range.mpr hlt, ?_⟩
        have hpre : q <+: rep N (gSplitDepth (ambSub d (s ++ [ltr N j]))) := by
          rcases (hd.ambSub _).neck_cases hqe with h | ⟨b, q'', hq'', -⟩
          · exact h
          · exfalso
            have := congrArg List.length hq''
            simp at this
            omega
        rw [← eq_rep_of_prefix hpre]
      · refine Or.inr ⟨(s ++ ltr N j :: rep N (R - 1), 0), by simp, ?_⟩
        have hRq : rep N R <+: q := by
          rcases (hd.ambSub _).neck_cases hqe with h | ⟨b, q'', rfl, -⟩
          · rw [eq_rep_of_prefix h]
            exact rep_prefix_rep (by omega)
          · exact (rep_prefix_rep hfit).trans (List.prefix_append _ _)
        rw [rootOf]
        obtain ⟨q', rfl⟩ := hRq
        refine ⟨q', ?_⟩
        obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
        rw [Nat.succ_sub_one, rep_succ, ltr_zero]
        simp
  | .hit l, s, j, q, hfit, hj, hq => by
      rw [bFitT_hit] at hfit
      have hqe : q ∈ sample (ambSub d (s ++ [ltr N j])) := by
        rw [mem_sample_ambSub_iff (exit_mem_sample hd (BranchingProcess.Subtree.mem_of_prefix
          (List.prefix_append _ _) hq) hj)]
        simpa using hq
      rcases (hd.ambSub _).neck_cases hqe with h | ⟨b, q'', rfl, hb⟩
      · refine Or.inl ?_
        rw [hangVerts_hit, List.mem_append, List.mem_map]
        have := h.length_le
        rw [rep_length] at this
        refine Or.inl ⟨q.length, List.mem_range.mpr (by omega), ?_⟩
        rw [← eq_rep_of_prefix h]
      · have hb' : (b : ℕ) < d (s ++ ltr N j :: rep N (gSplitDepth (ambSub d (s ++ [ltr N j])))) := by
          rw [ambSub_apply] at hb
          simpa using hb
        have hbb : ltr N (b : ℕ) = b := Fin.ext (val_ltr_of_lt b.isLt)
        have hq' : s ++ ltr N j :: rep N (gSplitDepth (ambSub d (s ++ [ltr N j]))) ++ ltr N (b : ℕ) :: q'' ∈ sample d := by
          rw [hbb]; simpa using hq
        rcases cover_splitVerts hR hd l (s ++ ltr N j :: rep N (gSplitDepth (ambSub d (s ++ [ltr N j])))) 0 hfit.2.2 (Nat.zero_le _) hb' hq'
          with h | ⟨x, hx, hpre⟩
        · refine Or.inl ?_
          rw [hangVerts_hit, List.mem_append]
          refine Or.inr ?_
          rw [hbb] at h
          simpa using h
        · refine Or.inr ⟨x, by rw [hangPorts_hit]; exact hx, ?_⟩
          rw [hbb] at hpre
          simpa using hpre

/-- **The cover below a list of exits.** -/
lemma cover_splitVerts (hR : 1 ≤ R) (hd : IsChainField N d) :
    ∀ (ts : List BTrace) (s : GWord N) (j : ℕ) {a : ℕ} {q : GWord N}, BFit R d s j ts →
      j ≤ a → a < d s → s ++ ltr N a :: q ∈ sample d →
      s ++ ltr N a :: q ∈ splitVerts R d s j ts
        ∨ ∃ x ∈ splitPorts R d s j ts, rootOf x <+: s ++ ltr N a :: q
  | [], s, j, a, q, hfit, hja, ha, _ => by
      rw [bFit_nil] at hfit
      omega
  | t :: ts, s, j, a, q, hfit, hja, ha, hq => by
      rw [bFit_cons] at hfit
      rcases Nat.eq_or_lt_of_le hja with rfl | hlt
      · rcases cover_hangVerts hR hd t s j hfit.1 ha hq with h | ⟨x, hx, hpre⟩
        · exact Or.inl (by rw [splitVerts_cons, List.mem_append]; exact Or.inl h)
        · exact Or.inr ⟨x, by rw [splitPorts_cons, List.mem_append]; exact Or.inl hx, hpre⟩
      · rcases cover_splitVerts hR hd ts s (j + 1) hfit.2 hlt ha hq with h | ⟨x, hx, hpre⟩
        · exact Or.inl (by rw [splitVerts_cons, List.mem_append]; exact Or.inr h)
        · exact Or.inr ⟨x, by rw [splitPorts_cons, List.mem_append]; exact Or.inr hx, hpre⟩

end


/-! #### The presented children are the fields at the planted children -/

/-- The split ending the neck of the field at `s₀`, as an address relative to the cluster
root. -/
noncomputable def splitOf (d : GWord N → ℕ) (s₀ : GWord N) : GWord N :=
  s₀ ++ rep N (gSplitDepth (ambSub d s₀))

lemma splitOf_def (d : GWord N → ℕ) (s₀ : GWord N) :
    splitOf d s₀ = s₀ ++ rep N (gSplitDepth (ambSub d s₀)) := rfl

/-- The split below an exit is the split of the field at the exit's child. -/
lemma splitOf_exit (d : GWord N → ℕ) (s : GWord N) (j : ℕ) :
    splitOf d (s ++ [ltr N j]) = s ++ ltr N j :: rep N (gSplitDepth (ambSub d (s ++ [ltr N j]))) := by
  rw [splitOf_def, List.append_assoc]
  rfl

lemma gArity_ambSub_eq (hd : IsChainField N d) (s₀ : GWord N) :
    gArity (ambSub d s₀) = d (splitOf d s₀) := by
  rw [(hd.ambSub s₀).gArity_eq, ambSub_apply, splitOf_def]

/-- The surviving subtree at an exit is the field at the exit's child. -/
lemma gSplitBush_ambSub_eq (hd : IsChainField N d) (s₀ : GWord N) {j : ℕ}
    (hj : j < d (splitOf d s₀)) :
    gSplitBush (ambSub d s₀) j = ambSub d (splitOf d s₀ ++ [ltr N j]) := by
  have hj' : j < gArity (ambSub d s₀) := by rwa [gArity_ambSub_eq hd]
  have hlt : (⟨j, (hd.ambSub s₀).lt_N_of_lt_gArity hj'⟩ : Fin N) = ltr N j :=
    Fin.ext (by rw [val_ltr_of_lt ((hd.ambSub s₀).lt_N_of_lt_gArity hj')])
  rw [(hd.ambSub s₀).gSplitBush_eq hj', ambSub_ambSub, splitOf_def, List.append_assoc, hlt]

omit [NeZero N] in
lemma bFollow_nil_false (c : GWord N → ℕ) : bFollow R c ([], false) = c := by
  simp [bFollow]

omit [NeZero N] in
lemma bFollow_nil_true (c : GWord N → ℕ) : bFollow R c ([], true) = neckIter c R := by
  simp [bFollow]

omit [NeZero N] in
lemma getD_append_of_lt {α : Type*} {l₁ l₂ : List α} {i : ℕ} (hi : i < l₁.length) (a : α) :
    (l₁ ++ l₂).getD i a = l₁.getD i a := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

omit [NeZero N] in
lemma getD_append_of_le {α : Type*} {l₁ l₂ : List α} {i : ℕ} (hi : l₁.length ≤ i) (a : α) :
    (l₁ ++ l₂).getD i a = l₂.getD (i - l₁.length) a := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

mutual

/-- **The handed subfield of one exit**: following the path the automaton records reaches
the field at the planted child of the corresponding port. -/
lemma bFollow_hangPorts (hR : 1 ≤ R) (hd : IsChainField N d) :
    ∀ (t : BTrace) (s₀ : GWord N) (j i : ℕ), j < d (splitOf d s₀) →
      BFitT R d (splitOf d s₀) j t → i < bCount t →
      bFollow R (ambSub d s₀) (j :: (bPath t i).1, (bPath t i).2)
        = ambSub d (rootOf ((hangPorts R d (splitOf d s₀) j t).getD i ([], 0)))
  | .skip, s₀, j, i, hj, _, hi => by
      obtain rfl : i = 0 := by simp at hi; omega
      rw [bPath_skip, bFollow_cons, bFollow_nil_false, gSplitBush_ambSub_eq hd s₀ hj,
        hangPorts_skip, List.getD_cons_zero]
      rfl
  | .miss, s₀, j, i, hj, _, hi => by
      obtain rfl : i = 0 := by simp at hi; omega
      rw [bPath_miss, bFollow_cons, bFollow_nil_true, gSplitBush_ambSub_eq hd s₀ hj,
        (hd.ambSub _).neckIter_eq, ambSub_ambSub, hangPorts_miss, List.getD_cons_zero]
      obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
      simp only [rootOf, Nat.succ_sub_one, rep_succ, ltr_zero]
      simp
  | .hit l, s₀, j, i, hj, hfit, hi => by
      rw [bFitT_hit] at hfit
      rw [bPath_hit, bFollow_cons, gSplitBush_ambSub_eq hd s₀ hj, hangPorts_hit,
        ← splitOf_exit]
      rw [bCount_hit] at hi
      exact bFollow_splitPorts hR hd l (splitOf d s₀ ++ [ltr N j]) 0 i
        (by rw [splitOf_exit]; exact hfit.2.2) hi

/-- **The handed subfields of a list of exits.** -/
lemma bFollow_splitPorts (hR : 1 ≤ R) (hd : IsChainField N d) :
    ∀ (ts : List BTrace) (s₀ : GWord N) (j i : ℕ),
      BFit R d (splitOf d s₀) j ts → i < bCountL ts →
      bFollow R (ambSub d s₀) (bPathL j ts i)
        = ambSub d (rootOf ((splitPorts R d (splitOf d s₀) j ts).getD i ([], 0)))
  | [], _, _, _, _, hi => by simp at hi
  | t :: ts, s₀, j, i, hfit, hi => by
      have hlen := hfit.length
      rw [bFit_cons] at hfit
      rw [bPathL_cons, splitPorts_cons]
      by_cases hlt : i < bCount t
      · rw [if_pos hlt, getD_append_of_lt (by rw [length_hangPorts_eq]; exact hlt)]
        exact bFollow_hangPorts hR hd t s₀ j i (by simp at hlen; omega) hfit.1 hlt
      · rw [if_neg hlt, getD_append_of_le (by rw [length_hangPorts_eq]; omega),
          length_hangPorts_eq]
        rw [bCountL_cons] at hi
        exact bFollow_splitPorts hR hd ts s₀ (j + 1) (i - bCount t) hfit.2 (by omega)

end

/-! #### The automaton's traces fit -/

mutual

/-- A trace the sample realises fits its exit. -/
lemma bFitT_of_bMatch (hd : IsChainField N d) :
    ∀ (t : BTrace) (s₀ : GWord N) (j : ℕ), j < d (splitOf d s₀) →
      bMatch R t (gSplitBush (ambSub d s₀) j) → BFitT R d (splitOf d s₀) j t
  | .skip, _, _, _, _ => bFitT_skip _ _
  | .miss, s₀, j, hj, h => by
      rw [bMatch_miss, gSplitBush_ambSub_eq hd s₀ hj, (hd.ambSub _).bHit_iff, not_lt] at h
      rw [bFitT_miss]
      exact h
  | .hit l, s₀, j, hj, h => by
      rw [bMatch_hit, gSplitBush_ambSub_eq hd s₀ hj, (hd.ambSub _).bHit_iff] at h
      rw [bFitT_hit]
      refine ⟨h.1, h.2.1.symm, ?_⟩
      rw [← splitOf_exit]
      refine bFit_of_bMatchL hd l (splitOf d s₀ ++ [ltr N j]) 0 _ ?_ h.2.1.symm ?_
      · rw [Nat.zero_add, gArity_ambSub_eq hd]
      · rw [bChildren, List.range_eq_range'] at h
        exact h.2.2

/-- A list of traces the sample realises fits its exits. -/
lemma bFit_of_bMatchL (hd : IsChainField N d) :
    ∀ (ts : List BTrace) (s₀ : GWord N) (j n : ℕ), j + n = d (splitOf d s₀) → ts.length = n →
      bMatchL R ts ((List.range' j n).map (gSplitBush (ambSub d s₀))) →
      BFit R d (splitOf d s₀) j ts
  | [], s₀, j, n, hjn, hlen, _ => by
      rw [bFit_nil]
      simp at hlen
      omega
  | t :: ts, s₀, j, n, hjn, hlen, h => by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨ts.length, by simp at hlen; omega⟩
      rw [List.range'_succ, List.map_cons, bMatchL_cons] at h
      simp only [List.headD_cons, List.tail_cons] at h
      rw [bFit_cons]
      exact ⟨bFitT_of_bMatch hd t s₀ j (by omega) h.1,
        bFit_of_bMatchL hd ts s₀ (j + 1) n' (by omega) (by simp at hlen; omega) h.2⟩

end

omit [NeZero N] in
/-- The trace of the root's blob with its decision function, the form `bExplore_eq_iff`
reads. -/
lemma bTraceF_match {σ : Type*} (ρr : BRule σ) (d : GWord N → ℕ) (coin : σ) :
    (bTraceF R ρr d coin).length = gArity d
      ∧ bMatchL R (bTraceF R ρr d coin) (bChildren d) := by
  have h := (bExplore_eq_iff R (dec := fun evs ↦ ρr.decide (gArity d - 1) evs coin) (T := ρr.T)
    (fun evs hT => ρr.stop _ evs coin hT) (ρr.T + 1) (bChildren d) false [] (bTraceF R ρr d coin)
    (by simp)).mp rfl
  exact ⟨by rw [h.1, bChildren_length], h.2.2⟩

/-- **The automaton's traces fit the exits of the root's split.** -/
lemma bFit_bTraceF {σ : Type*} (hd : IsChainField N d) (ρr : BRule σ) (coin : σ) :
    BFit R d (splitOf d []) 0 (bTraceF R ρr d coin) := by
  obtain ⟨hlen, hmatch⟩ := bTraceF_match (R := R) ρr d coin
  refine bFit_of_bMatchL hd _ [] 0 (gArity d) ?_ hlen ?_
  · rw [Nat.zero_add, ← gArity_ambSub_eq hd, ambSub_nil]
  · rw [bChildren, List.range_eq_range'] at hmatch
    rw [ambSub_nil]
    exact hmatch

mutual

/-- Every hit of a fitting trace has at least two children: the traces are valid. -/
lemma BFit.bOkL : ∀ {ts : List BTrace} {s : GWord N} {j : ℕ}, IsChainField N d →
    BFit R d s j ts → BOkL ts
  | [], _, _, _, _ => fun t ht => by simp at ht
  | t :: ts, s, j, hd, hfit => by
      rw [bFit_cons] at hfit
      intro t' ht'
      rw [List.mem_cons] at ht'
      rcases ht' with rfl | ht'
      · exact BFitT.bOk hd hfit.1
      · exact BFit.bOkL hd hfit.2 t' ht'

/-- A fitting hit absorbs a genuine split. -/
lemma BFitT.bOk : ∀ {t : BTrace} {s : GWord N} {j : ℕ}, IsChainField N d →
    BFitT R d s j t → BOk t
  | .skip, _, _, _, _ => BOk_skip
  | .miss, _, _, _, _ => BOk_miss
  | .hit l, s, j, hd, hfit => by
      rw [bFitT_hit] at hfit
      rw [BOk_hit]
      refine ⟨by rw [hfit.2.1]; exact (hd.ambSub _).two_le_gArity, ?_⟩
      exact BFit.bOkL hd hfit.2.2

end


/-! #### The blob of a cluster root as a piece -/

lemma splitOf_nil (d : GWord N → ℕ) : splitOf d [] = rep N (gSplitDepth d) := by
  rw [splitOf_def, ambSub_nil, List.nil_append]

/-- **The vertices of the blob of a cluster root**, relative to the root: the presented neck
and the vertices below the exits of its split. -/
noncomputable def blobVertsW (R : ℕ) (d : GWord N → ℕ) (ts : List BTrace) : List (GWord N) :=
  (List.range (gSplitDepth d + 1)).map (rep N) ++ splitVerts R d (rep N (gSplitDepth d)) 0 ts

/-- **The ports of the blob of a cluster root**, in the order the automaton hands the
presented children. -/
noncomputable def blobPortsW (R : ℕ) (d : GWord N → ℕ) (ts : List BTrace) :
    List (GWord N × ℕ) :=
  splitPorts R d (rep N (gSplitDepth d)) 0 ts

lemma mem_blobVertsW {ts : List BTrace} {v : GWord N} :
    v ∈ blobVertsW R d ts
      ↔ (∃ i, i ≤ gSplitDepth d ∧ v = rep N i) ∨ v ∈ splitVerts R d (rep N (gSplitDepth d)) 0 ts := by
  rw [blobVertsW, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨i, hi, rfl⟩ | h)
    · exact Or.inl ⟨i, by rw [List.mem_range] at hi; omega, rfl⟩
    · exact Or.inr h
  · rintro (⟨i, hi, rfl⟩ | h)
    · exact Or.inl ⟨i, by rw [List.mem_range]; omega, rfl⟩
    · exact Or.inr h

/-- A prefix of a blob vertex is a blob vertex. -/
lemma prefix_mem_blobVertsW {ts : List BTrace} {u v : GWord N} (hv : v ∈ blobVertsW R d ts)
    (huv : u <+: v) : u ∈ blobVertsW R d ts := by
  rw [mem_blobVertsW] at hv ⊢
  rcases hv with ⟨i, hi, rfl⟩ | hv
  · refine Or.inl ⟨u.length, ?_, eq_rep_of_prefix huv⟩
    have := huv.length_le
    rw [rep_length] at this
    omega
  · rcases prefix_mem_splitVerts ts _ _ hv huv with h | h
    · refine Or.inl ⟨u.length, ?_, eq_rep_of_prefix h⟩
      have := h.length_le
      rw [rep_length] at this
      exact this
    · exact Or.inr h

/-- The blob vertices lie in the sample. -/
lemma mem_sample_of_mem_blobVertsW (hd : IsChainField N d) {ts : List BTrace}
    (hfit : BFit R d (rep N (gSplitDepth d)) 0 ts) {v : GWord N} (hv : v ∈ blobVertsW R d ts) :
    v ∈ sample d := by
  rw [mem_blobVertsW] at hv
  rcases hv with ⟨i, -, rfl⟩ | hv
  · exact hd.rep_mem_sample i
  · exact mem_sample_of_mem_splitVerts hd ts _ _ (hd.rep_mem_sample _) hfit hv

/-- The planted children of the blob's ports lie in the sample. -/
lemma root_mem_sample_of_mem_blobPortsW (hd : IsChainField N d) {ts : List BTrace}
    (hfit : BFit R d (rep N (gSplitDepth d)) 0 ts) {x : GWord N × ℕ} (hx : x ∈ blobPortsW R d ts) :
    rootOf x ∈ sample d :=
  root_mem_sample_of_mem_splitPorts hd ts _ _ (hd.rep_mem_sample _) hfit hx

/-- **Every vertex of the sample is a blob vertex or lies below a planted child.** -/
lemma blob_cover (hR : 1 ≤ R) (hd : IsChainField N d) {ts : List BTrace}
    (hfit : BFit R d (rep N (gSplitDepth d)) 0 ts) {q : GWord N} (hq : q ∈ sample d) :
    q ∈ blobVertsW R d ts ∨ ∃ x ∈ blobPortsW R d ts, rootOf x <+: q := by
  rcases hd.neck_cases hq with h | ⟨b, q'', rfl, hb⟩
  · refine Or.inl ?_
    rw [mem_blobVertsW]
    refine Or.inl ⟨q.length, ?_, eq_rep_of_prefix h⟩
    have := h.length_le
    rw [rep_length] at this
    exact this
  · have hq' : rep N (gSplitDepth d) ++ ltr N (b : ℕ) :: q'' ∈ sample d := by
      rw [ltr_val]; exact hq
    rcases cover_splitVerts hR hd ts (rep N (gSplitDepth d)) 0 hfit (Nat.zero_le _) hb hq'
      with h | ⟨x, hx, hpre⟩
    · refine Or.inl ?_
      rw [mem_blobVertsW]
      rw [ltr_val] at h
      exact Or.inr h
    · rw [ltr_val] at hpre
      exact Or.inr ⟨x, hx, hpre⟩

/-- The port count of the blob is the presented arity. -/
lemma length_blobPortsW (hd : IsChainField N d) {ts : List BTrace}
    (hfit : BFit R d (rep N (gSplitDepth d)) 0 ts) :
    (blobPortsW R d ts).length = gArity d + bShiftL ts := by
  rw [blobPortsW, length_splitPorts_eq, bCountL_eq_of_ok ts (BFit.bOkL hd hfit)]
  have := hfit.length
  rw [Nat.zero_add, hd.gArity_eq] at *
  omega

omit [NeZero N] in
/-- A prefix of a reading is the reading of a prefix. -/
lemma exists_prefix_of_prefix_pvals {p : List ℕ} {v : GWord N} (h : p <+: pvals v) :
    ∃ u, u <+: v ∧ pvals u = p := by
  refine ⟨v.take p.length, List.take_prefix _ _, ?_⟩
  have h1 : (pvals v).take p.length = p := by
    rw [List.prefix_iff_eq_take] at h
    exact h.symm
  rw [pvals, List.map_take]
  exact h1

/-- **The blob of a cluster root as a piece**: its vertices read over `ℕ`, its ports with
their slots. -/
noncomputable def blobPieceOf (R : ℕ) (d : GWord N → ℕ) (ts : List BTrace) (hR : 1 ≤ R)
    (hd : IsChainField N d) (hfit : BFit R d (rep N (gSplitDepth d)) 0 ts) : Piece where
  mem p := p ∈ (blobVertsW R d ts).map pvals
  nil_mem := List.mem_map.mpr ⟨[], by rw [mem_blobVertsW]; exact Or.inl ⟨0, Nat.zero_le _, rfl⟩, rfl⟩
  mem_of_prefix := by
    intro p q hpq hq
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
    obtain ⟨u, huv, rfl⟩ := exists_prefix_of_prefix_pvals hpq
    exact List.mem_map.mpr ⟨u, prefix_mem_blobVertsW hv huv, rfl⟩
  ports := (blobPortsW R d ts).map fun x => (pvals x.1, x.2)
  port_mem := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    refine List.mem_map.mpr ⟨x.1, ?_, rfl⟩
    rw [mem_blobVertsW]
    rcases port_mem_splitVerts hR ts _ _ hx with h | h
    · exact Or.inl ⟨_, le_rfl, h⟩
    · exact Or.inr h
  slot_free := by
    intro y hy hmem
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hslot := slot_lt_of_mem_splitPorts hd ts _ _ hfit hx
    have hroot : pvals x.1 ++ [x.2] = pvals (rootOf x) := by
      rw [rootOf, pvals_append, pvals_cons, pvals_nil, val_ltr_of_lt hslot]
    rw [hroot] at hmem
    obtain ⟨v, hv, hvx⟩ := List.mem_map.mp hmem
    rw [pvals_injective hvx] at hv
    rw [mem_blobVertsW] at hv
    rcases hv with ⟨i, hi, hrep⟩ | hv
    · obtain ⟨i', -, hpre⟩ := mem_splitPorts_shape ts _ _ hx
      have := hpre.length_le
      rw [hrep, rep_length] at this
      simp at this
      omega
    · exact root_not_mem_splitVerts hR hd ts _ _ hfit hx hv
  ports_nodup := by
    refine List.Nodup.map ?_ (List.Nodup.of_map rootOf (nodup_roots_splitPorts hd ts _ _ hfit))
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (pvals_injective hxy.1) hxy.2

omit [NeZero N] in
lemma getD_map_eq {α β : Type*} (f : α → β) (l : List α) (j : ℕ) (a : α) :
    (l.map f).getD j (f a) = f (l.getD j a) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    Option.getD_map]

section BlobPieceOf

variable (hR : 1 ≤ R) (hd : IsChainField N d) {ts : List BTrace}
  (hfit : BFit R d (rep N (gSplitDepth d)) 0 ts)

lemma blobPieceOf_mem (p : List ℕ) :
    (blobPieceOf R d ts hR hd hfit).mem p ↔ ∃ v ∈ blobVertsW R d ts, pvals v = p := by
  show p ∈ (blobVertsW R d ts).map pvals ↔ _
  rw [List.mem_map]

lemma blobPieceOf_nports : (blobPieceOf R d ts hR hd hfit).nports = gArity d + bShiftL ts := by
  show ((blobPortsW R d ts).map _).length = _
  rw [List.length_map, length_blobPortsW hd hfit]

lemma blobPieceOf_portSlot (j : ℕ) :
    (blobPieceOf R d ts hR hd hfit).portSlot j
      = (pvals ((blobPortsW R d ts).getD j ([], 0)).1, ((blobPortsW R d ts).getD j ([], 0)).2) := by
  show ((blobPortsW R d ts).map (fun x : GWord N × ℕ => (pvals x.1, x.2))).getD j ([], 0) = _
  have h := getD_map_eq (fun x : GWord N × ℕ => (pvals x.1, x.2)) (blobPortsW R d ts) j ([], 0)
  simpa using h

include hd hfit in
/-- The slot of every port, the junk ports included, is a letter. -/
lemma blobPieceOf_slot_lt (j : ℕ) : ((blobPortsW R d ts).getD j ([], 0)).2 < N := by
  rcases lt_or_ge j (blobPortsW R d ts).length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj]
    exact slot_lt_of_mem_splitPorts hd ts _ _ hfit (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ hj]
    exact Nat.pos_of_ne_zero (NeZero.ne N)

/-- The planted child of every port, read over `ℕ`. -/
lemma blobPieceOf_root (j : ℕ) :
    (blobPieceOf R d ts hR hd hfit).root j = pvals (rootOf ((blobPortsW R d ts).getD j ([], 0))) := by
  rw [Piece.root, Piece.port, Piece.slot, blobPieceOf_portSlot, rootOf, pvals_append, pvals_cons,
    pvals_nil, val_ltr_of_lt (blobPieceOf_slot_lt (R := R) hd hfit j)]

end BlobPieceOf


/-! #### The depth of a blob below its split -/

mutual

/-- A vertex hanging below an exit lies within `R` per level of hit nesting. -/
lemma length_le_of_mem_hangVerts : ∀ (t : BTrace) (s : GWord N) (j : ℕ) {v : GWord N},
    BFitT R d s j t → v ∈ hangVerts R d s j t → v.length ≤ s.length + R * (hdepth t + 1)
  | .skip, _, _, _, _, h => by simp at h
  | .miss, s, j, v, _, h => by
      rw [hangVerts_miss, List.mem_map] at h
      obtain ⟨i, hi, rfl⟩ := h
      rw [List.mem_range] at hi
      simp only [List.length_append, List.length_cons, rep_length, hdepth_miss]
      omega
  | .hit l, s, j, v, hfit, h => by
      rw [bFitT_hit] at hfit
      rw [hangVerts_hit, List.mem_append] at h
      rw [hdepth_hit]
      rcases h with h | h
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
        rw [List.mem_range] at hi
        simp only [List.length_append, List.length_cons, rep_length]
        nlinarith
      · have := length_le_of_mem_splitVerts l _ _ hfit.2.2 h
        simp only [List.length_append, List.length_cons, rep_length] at this
        nlinarith

/-- A vertex below a list of exits lies within `R` per level of hit nesting. -/
lemma length_le_of_mem_splitVerts : ∀ (ts : List BTrace) (s : GWord N) (j : ℕ) {v : GWord N},
    BFit R d s j ts → v ∈ splitVerts R d s j ts → v.length ≤ s.length + R * (hdepthL ts + 1)
  | [], _, _, _, _, h => by simp at h
  | t :: ts, s, j, v, hfit, h => by
      rw [bFit_cons] at hfit
      rw [splitVerts_cons, List.mem_append] at h
      rw [hdepthL_cons]
      rcases h with h | h
      · have := length_le_of_mem_hangVerts t s j hfit.1 h
        have hmono : R * (hdepth t + 1) ≤ R * (max (hdepth t) (hdepthL ts) + 1) :=
          Nat.mul_le_mul_left R (by omega)
        omega
      · have := length_le_of_mem_splitVerts ts s (j + 1) hfit.2 h
        have hmono : R * (hdepthL ts + 1) ≤ R * (max (hdepth t) (hdepthL ts) + 1) :=
          Nat.mul_le_mul_left R (by omega)
        omega

end

end BlobLemmas

/-! ### The presented skeleton and the blob pieces of a rule -/

section Presented

variable (R : ℕ) {σ : Type*} (ρr : BRule σ)

/-- The trace of the root's blob of a presented field. -/
noncomputable def blobTrace (ω : (GWord N → ℕ) × (List ℕ → σ)) : List BTrace :=
  bTraceF R ρr ω.1 (ω.2 [])

/-- **The presented skeleton**: the addresses the blob presentation hands down, each letter
below the presented arity of the blob it leaves. -/
def Presented : (GWord N → ℕ) × (List ℕ → σ) → List ℕ → Prop
  | _, [] => True
  | ω, i :: u => i < bArityC R ρr ω ∧ Presented (bSubC R ρr ω i) u

omit [NeZero N] in
@[simp] lemma presented_nil (ω : (GWord N → ℕ) × (List ℕ → σ)) : Presented R ρr ω [] := by
  rw [Presented]; trivial

omit [NeZero N] in
lemma presented_cons (ω : (GWord N → ℕ) × (List ℕ → σ)) (i : ℕ) (u : List ℕ) :
    Presented R ρr ω (i :: u) ↔ i < bArityC R ρr ω ∧ Presented R ρr (bSubC R ρr ω i) u := by
  rw [Presented]

/-- The planted child of the `i`-th port of the root's blob. -/
noncomputable def rootW (ω : (GWord N → ℕ) × (List ℕ → σ)) (i : ℕ) : GWord N :=
  rootOf ((blobPortsW R ω.1 (blobTrace R ρr ω)).getD i ([], 0))

/-- **The cluster root of a presented address**: the planted children along the address,
concatenated. -/
noncomputable def rootAt : (GWord N → ℕ) × (List ℕ → σ) → List ℕ → GWord N
  | _, [] => []
  | ω, i :: u => rootW R ρr ω i ++ rootAt (bSubC R ρr ω i) u

@[simp] lemma rootAt_nil (ω : (GWord N → ℕ) × (List ℕ → σ)) : rootAt R ρr ω [] = [] := rfl

lemma rootAt_cons (ω : (GWord N → ℕ) × (List ℕ → σ)) (i : ℕ) (u : List ℕ) :
    rootAt R ρr ω (i :: u) = rootW R ρr ω i ++ rootAt R ρr (bSubC R ρr ω i) u := rfl

/-- The trace of the root's blob fits. -/
lemma bFit_blobTrace {ω : (GWord N → ℕ) × (List ℕ → σ)} (hd : IsChainField N ω.1) :
    BFit R ω.1 (rep N (gSplitDepth ω.1)) 0 (blobTrace R ρr ω) := by
  have := bFit_bTraceF (R := R) hd ρr (ω.2 [])
  rwa [splitOf_nil] at this

open Classical in
/-- **The blob piece of a presented address**: the blob of the presented field there, and a
one-vertex piece off the presented skeleton. -/
noncomputable def blobPiece (ω : (GWord N → ℕ) × (List ℕ → σ)) (u : List ℕ) : Piece :=
  if h : 1 ≤ R ∧ IsChainField N (bAtC R ρr ω u).1 then
    blobPieceOf R (bAtC R ρr ω u).1 (blobTrace R ρr (bAtC R ρr ω u)) h.1 h.2
      (bFit_blobTrace R ρr h.2)
  else flatPiece 0 0

lemma blobPiece_eq {ω : (GWord N → ℕ) × (List ℕ → σ)} {u : List ℕ} (hR : 1 ≤ R)
    (h : IsChainField N (bAtC R ρr ω u).1) :
    blobPiece R ρr ω u
      = blobPieceOf R (bAtC R ρr ω u).1 (blobTrace R ρr (bAtC R ρr ω u)) hR h
          (bFit_blobTrace R ρr h) := by
  rw [blobPiece, dif_pos ⟨hR, h⟩]

/-- The presented arity is the handed count of the trace. -/
lemma bArityC_eq_bCountL {ω : (GWord N → ℕ) × (List ℕ → σ)} (hd : IsChainField N ω.1) :
    bArityC R ρr ω = bCountL (blobTrace R ρr ω) := by
  have hok : BOkL (bTraceF R ρr ω.1 (ω.2 [])) := BFit.bOkL hd (bFit_blobTrace R ρr hd)
  rw [bArityC, blobTrace, bCountL_eq_of_ok _ hok, (bTraceF_match (R := R) ρr ω.1 (ω.2 [])).1]

/-- The presented arity is the port count of the blob. -/
lemma bArityC_eq_length_blobPortsW {ω : (GWord N → ℕ) × (List ℕ → σ)}
    (hd : IsChainField N ω.1) :
    bArityC R ρr ω = (blobPortsW R ω.1 (blobTrace R ρr ω)).length := by
  rw [length_blobPortsW hd (bFit_blobTrace R ρr hd), bArityC, blobTrace]

/-- **The presented children are the fields at the planted children.** -/
lemma bSubC_fst_eq (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)} (hd : IsChainField N ω.1)
    {i : ℕ} (hi : i < bArityC R ρr ω) :
    (bSubC R ρr ω i).1 = ambSub ω.1 (rootW R ρr ω i) := by
  rw [bArityC_eq_bCountL R ρr hd] at hi
  have h := bFollow_splitPorts hR hd (blobTrace R ρr ω) [] 0 i
    (by rw [splitOf_nil]; exact bFit_blobTrace R ρr hd) hi
  rw [ambSub_nil, splitOf_nil] at h
  exact h

/-- The planted children of the root's blob lie in the sample. -/
lemma rootW_mem_sample {ω : (GWord N → ℕ) × (List ℕ → σ)} (hd : IsChainField N ω.1)
    {i : ℕ} (hi : i < bArityC R ρr ω) : rootW R ρr ω i ∈ sample ω.1 := by
  rw [bArityC_eq_length_blobPortsW R ρr hd] at hi
  rw [rootW, List.getD_eq_getElem _ _ hi]
  exact root_mem_sample_of_mem_blobPortsW hd (bFit_blobTrace R ρr hd) (List.getElem_mem hi)

/-- **The presented fields along the presented skeleton**: each is the field at the cluster
root of its address, a chain-regime field, the cluster root lying in the sample. -/
lemma presented_spec (hR : 1 ≤ R) : ∀ (u : List ℕ) (ω : (GWord N → ℕ) × (List ℕ → σ)),
    IsChainField N ω.1 → Presented R ρr ω u →
      IsChainField N (bAtC R ρr ω u).1 ∧ (bAtC R ρr ω u).1 = ambSub ω.1 (rootAt R ρr ω u)
        ∧ rootAt R ρr ω u ∈ sample ω.1
  | [], ω, hd, _ => ⟨hd, by simp, by simp⟩
  | i :: u, ω, hd, hu => by
      rw [presented_cons] at hu
      have hsub := bSubC_fst_eq R ρr hR hd hu.1
      have hd' : IsChainField N (bSubC R ρr ω i).1 := by rw [hsub]; exact hd.ambSub _
      obtain ⟨h1, h2, h3⟩ := presented_spec hR u (bSubC R ρr ω i) hd' hu.2
      refine ⟨by rw [bAtC_cons]; exact h1, ?_, ?_⟩
      · rw [bAtC_cons, h2, hsub, ambSub_ambSub, rootAt_cons]
      · rw [rootAt_cons]
        rw [hsub] at h3
        exact (mem_sample_ambSub_iff (rootW_mem_sample R ρr hd hu.1)).mp h3

omit [NeZero N] in
/-- The presented skeleton, one letter at a time from the right. -/
lemma presented_concat : ∀ (u : List ℕ) (ω : (GWord N → ℕ) × (List ℕ → σ)) (j : ℕ),
    Presented R ρr ω (u ++ [j]) ↔ Presented R ρr ω u ∧ j < bArityAtC R ρr ω u
  | [], ω, j => by simp [presented_cons]
  | i :: u, ω, j => by
      rw [List.cons_append, presented_cons, presented_cons, presented_concat u, bArityAtC_cons]
      tauto

/-- The cluster root, one letter at a time from the right. -/
lemma rootAt_concat : ∀ (u : List ℕ) (ω : (GWord N → ℕ) × (List ℕ → σ)) (j : ℕ),
    rootAt R ρr ω (u ++ [j]) = rootAt R ρr ω u ++ rootW R ρr (bAtC R ρr ω u) j
  | [], ω, j => by simp [rootAt_cons]
  | i :: u, ω, j => by
      rw [List.cons_append, rootAt_cons, rootAt_cons, rootAt_concat u, bAtC_cons,
        List.append_assoc]

/-- The port count of a presented blob is its presented arity. -/
lemma blobPiece_nports (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)}
    (hd : IsChainField N ω.1) {u : List ℕ} (hu : Presented R ρr ω u) :
    (blobPiece R ρr ω u).nports = bArityAtC R ρr ω u := by
  have h := (presented_spec R ρr hR u ω hd hu).1
  rw [blobPiece_eq R ρr hR h, blobPieceOf_nports, bArityAtC]
  rfl

/-- **The presented skeleton is an index set for the blob pieces.** -/
lemma blob_pIdx (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)} (hd : IsChainField N ω.1) :
    PIdx (blobPiece R ρr ω) (Presented R ρr ω) := by
  intro u j hu
  rw [presented_concat] at hu
  refine ⟨hu.1, ?_⟩
  rw [blobPiece_nports R ρr hR hd hu.1]
  exact hu.2

/-- The planted child of a port of a presented blob, read over `ℕ`. -/
lemma blobPiece_root (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)}
    (hd : IsChainField N ω.1) {u : List ℕ} (hu : Presented R ρr ω u) (j : ℕ) :
    (blobPiece R ρr ω u).root j = pvals (rootW R ρr (bAtC R ρr ω u) j) := by
  have h := (presented_spec R ρr hR u ω hd hu).1
  rw [blobPiece_eq R ρr hR h, blobPieceOf_root, rootW]

/-- **The planting of a presented blob is its cluster root.** -/
lemma pCopyAddr_blobPiece (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)}
    (hd : IsChainField N ω.1) (u : List ℕ) (hu : Presented R ρr ω u) :
    pCopyAddr (blobPiece R ρr ω) u = pvals (rootAt R ρr ω u) := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [presented_concat] at hu
      rw [pCopyAddr_concat, ih hu.1, blobPiece_root R ρr hR hd hu.1, rootAt_concat, pvals_append]

/-- The vertices of a presented blob, read over `ℕ`. -/
lemma blobPiece_mem (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)}
    (hd : IsChainField N ω.1) {u : List ℕ} (hu : Presented R ρr ω u) (p : List ℕ) :
    (blobPiece R ρr ω u).mem p
      ↔ ∃ v ∈ blobVertsW R (bAtC R ρr ω u).1 (blobTrace R ρr (bAtC R ρr ω u)), pvals v = p := by
  have h := (presented_spec R ρr hR u ω hd hu).1
  rw [blobPiece_eq R ρr hR h, blobPieceOf_mem]

/-- **Every vertex of the blob assembly is a vertex of the sample.** -/
lemma exists_code_eq_pvals (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)}
    (hd : IsChainField N ω.1)
    (x : PAssembly (blobPiece R ρr ω) (Presented R ρr ω) (blob_pIdx R ρr hR hd)) :
    ∃ v ∈ sample ω.1, pvals v = x.code := by
  obtain ⟨u, hu, p, hp⟩ := x
  rw [blobPiece_mem R ρr hR hd hu] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨h1, h2, h3⟩ := presented_spec R ρr hR u ω hd hu
  refine ⟨rootAt R ρr ω u ++ q, ?_, ?_⟩
  · rw [← mem_sample_ambSub_iff h3, ← h2]
    exact mem_sample_of_mem_blobVertsW h1 (bFit_blobTrace R ρr h1) hq
  · rw [PAssembly.code, pvals_append, pCopyAddr_blobPiece R ρr hR hd u hu]

/-- **Every vertex of the sample is a vertex of the blob assembly**: a vertex below the
cluster root of a presented address is absorbed by its blob or lies below a planted child,
and the descent terminates. -/
lemma exists_pvals_eq_code (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)}
    (hd : IsChainField N ω.1) {v : GWord N} (hv : v ∈ sample ω.1) :
    ∃ x : PAssembly (blobPiece R ρr ω) (Presented R ρr ω) (blob_pIdx R ρr hR hd),
      x.code = pvals v := by
  suffices key : ∀ n (u : List ℕ), Presented R ρr ω u → rootAt R ρr ω u <+: v →
      v.length - (rootAt R ρr ω u).length ≤ n →
      ∃ x : PAssembly (blobPiece R ρr ω) (Presented R ρr ω) (blob_pIdx R ρr hR hd),
        x.code = pvals v from
    key v.length [] (presented_nil R ρr ω) List.nil_prefix (by simp)
  intro n
  induction n with
  | zero =>
      intro u hu hpre hlen
      have heq : v = rootAt R ρr ω u := (hpre.eq_of_length (by have := hpre.length_le; omega)).symm
      refine ⟨⟨u, hu, [], (blobPiece R ρr ω u).nil_mem⟩, ?_⟩
      rw [PAssembly.code, List.append_nil, pCopyAddr_blobPiece R ρr hR hd u hu, heq]
  | succ n ih =>
      intro u hu hpre hlen
      obtain ⟨h1, h2, h3⟩ := presented_spec R ρr hR u ω hd hu
      obtain ⟨q, rfl⟩ := hpre
      have hq : q ∈ sample (bAtC R ρr ω u).1 := by
        rw [h2, mem_sample_ambSub_iff h3]
        exact hv
      rcases blob_cover hR h1 (bFit_blobTrace R ρr h1) hq with hmem | ⟨x, hx, hxq⟩
      · refine ⟨⟨u, hu, pvals q, (blobPiece_mem R ρr hR hd hu _).mpr ⟨q, hmem, rfl⟩⟩, ?_⟩
        rw [PAssembly.code, pCopyAddr_blobPiece R ρr hR hd u hu, pvals_append]
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have hi' : i < bArityAtC R ρr ω u := by
          rw [bArityAtC, bArityC_eq_length_blobPortsW R ρr h1]
          exact hi
        have hui : Presented R ρr ω (u ++ [i]) := (presented_concat R ρr u ω i).mpr ⟨hu, hi'⟩
        have hroot : rootAt R ρr ω (u ++ [i]) = rootAt R ρr ω u
            ++ rootOf (blobPortsW R (bAtC R ρr ω u).1 (blobTrace R ρr (bAtC R ρr ω u)))[i] := by
          rw [rootAt_concat, rootW, List.getD_eq_getElem _ _ hi]
        obtain ⟨q', hq'⟩ := hxq
        have hlen' : 1 ≤ (rootOf (blobPortsW R (bAtC R ρr ω u).1
            (blobTrace R ρr (bAtC R ρr ω u)))[i]).length := by
          rw [rootOf, List.length_append]
          simp
        refine ih (u ++ [i]) hui ⟨q', by rw [hroot, List.append_assoc, hq']⟩ ?_
        have e1 : q.length = (rootOf (blobPortsW R (bAtC R ρr ω u).1
            (blobTrace R ρr (bAtC R ρr ω u)))[i]).length + q'.length := by
          rw [← hq', List.length_append]
        rw [hroot]
        simp only [List.length_append] at hlen ⊢
        omega

/-- A reading of a sample vertex read back as a word, through the surjectivity of the
reading. -/
noncomputable def blobVertex (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)}
    (hd : IsChainField N ω.1)
    (x : PAssembly (blobPiece R ρr ω) (Presented R ρr ω) (blob_pIdx R ρr hR hd)) :
    {v : GWord N // v ∈ sample ω.1} :=
  ⟨Classical.choose (exists_code_eq_pvals R ρr hR hd x),
    (Classical.choose_spec (exists_code_eq_pvals R ρr hR hd x)).1⟩

lemma pvals_blobVertex (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)}
    (hd : IsChainField N ω.1)
    (x : PAssembly (blobPiece R ρr ω) (Presented R ρr ω) (blob_pIdx R ρr hR hd)) :
    pvals (blobVertex R ρr hR hd x).1 = x.code :=
  (Classical.choose_spec (exists_code_eq_pvals R ρr hR hd x)).2

/-- **The sample is isometric to the blob assembly over the presented skeleton**
(**`thm:chain-general`**, the geometry of the presentation): the map sending a vertex of
the assembly to the sample vertex whose reading is its code is a bijection preserving the
distances, the tree metric of the sample being the address metric of the readings. -/
theorem blobAssembly_isometric_sample (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)}
    (hd : IsChainField N ω.1) :
    ∃ Φ : PAssembly (blobPiece R ρr ω) (Presented R ρr ω) (blob_pIdx R ρr hR hd)
        → {v : GWord N // v ∈ sample ω.1},
      Function.Bijective Φ ∧ ∀ x y, (BranchingProcess.treeDist (Φ x).1 (Φ y).1 : ℝ) = dist x y := by
  refine ⟨blobVertex R ρr hR hd, ⟨?_, ?_⟩, ?_⟩
  · intro x y h
    have h1 := pvals_blobVertex R ρr hR hd x
    have h2 := pvals_blobVertex R ρr hR hd y
    rw [h] at h1
    exact PAssembly.code_injective (h1.symm.trans h2)
  · rintro ⟨v, hv⟩
    obtain ⟨x, hx⟩ := exists_pvals_eq_code R ρr hR hd hv
    refine ⟨x, Subtype.ext ?_⟩
    have h1 := pvals_blobVertex R ρr hR hd x
    rw [hx] at h1
    exact pvals_injective h1
  · intro x y
    rw [PAssembly.dist_code, ← addrDist_pvals, pvals_blobVertex, pvals_blobVertex]


/-! ### The flat configurations of the presented blobs -/

omit [NeZero N] in
/-- The nesting depth of the hits of the root's trace is bounded by the stopping bound. -/
lemma hdepthL_blobTrace_le (ω : (GWord N → ℕ) × (List ℕ → σ)) :
    hdepthL (blobTrace R ρr ω) ≤ ρr.T + 1 :=
  hdepthL_bExplore_le R _ (ρr.T + 1) (bChildren ω.1) (false, [])

/-- **`thm:matched-presentation`\labelcref{it:matched-flat}, the geometry**: a presented
blob is a neck piece, its presented neck followed by vertices within `R(T + 2)` of the split,
`T` the stopping bound of the rule. -/
theorem blobPiece_isNeckPiece (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)}
    (hd : IsChainField N ω.1) {u : List ℕ} (hu : Presented R ρr ω u) :
    IsNeckPiece (blobPiece R ρr ω u) (bNeckAtC R ρr ω u) (R * (ρr.T + 2)) := by
  have h := (presented_spec R ρr hR u ω hd hu).1
  set d := (bAtC R ρr ω u).1 with hdef
  set ts := blobTrace R ρr (bAtC R ρr ω u) with htsdef
  have hfit : BFit R d (rep N (gSplitDepth d)) 0 ts := bFit_blobTrace R ρr h
  have hmem : ∀ p, (blobPiece R ρr ω u).mem p ↔ ∃ v ∈ blobVertsW R d ts, pvals v = p :=
    blobPiece_mem R ρr hR hd hu
  have hneck : bNeckAtC R ρr ω u = gSplitDepth d := rfl
  have hdepth : hdepthL ts ≤ ρr.T + 1 := hdepthL_blobTrace_le R ρr _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmem, hneck]
    exact ⟨rep N (gSplitDepth d), mem_blobVertsW.mpr (Or.inl ⟨_, le_rfl, rfl⟩), pvals_rep _⟩
  · intro p hp
    rw [hmem] at hp
    obtain ⟨v, hv, rfl⟩ := hp
    rw [hneck]
    rw [mem_blobVertsW] at hv
    rcases hv with ⟨i, hi, rfl⟩ | hv
    · exact Or.inl (by rw [pvals_rep]; exact pRep_prefix_pRep hi)
    · obtain ⟨i, -, q, rfl⟩ := mem_splitVerts_shape ts _ _ hv
      exact Or.inr ⟨_, by rw [pvals_append, pvals_rep]⟩
  · intro p hp hpre
    rw [hmem] at hp
    obtain ⟨v, hv, rfl⟩ := hp
    rw [hneck] at hpre ⊢
    rw [pvals_length]
    rw [mem_blobVertsW] at hv
    rcases hv with ⟨i, hi, rfl⟩ | hv
    · rw [rep_length]; omega
    · have := length_le_of_mem_splitVerts ts _ _ hfit hv
      rw [rep_length] at this
      have hm : R * (hdepthL ts + 1) ≤ R * (ρr.T + 2) := Nat.mul_le_mul_left R (by omega)
      omega
  · intro j hj
    rw [hneck]
    rw [blobPiece_eq R ρr hR h] at hj ⊢
    rw [blobPieceOf_nports] at hj
    rw [Piece.port, blobPieceOf_portSlot]
    have hj' : j < (blobPortsW R d ts).length := by
      rw [length_blobPortsW h hfit]; exact hj
    rw [List.getD_eq_getElem _ _ hj']
    rcases port_mem_splitVerts hR ts _ _ (List.getElem_mem hj') with h' | h'
    · rw [h', pvals_rep]
    · obtain ⟨i, -, q, hq⟩ := mem_splitVerts_shape ts _ _ h'
      rw [hq, pvals_append, pvals_rep]
      exact List.prefix_append _ _

/-- **The flat configuration of a presented blob**: a bare neck of the presented neck length
with the presented arity of ports at its far end. -/
noncomputable def flatAt (ω : (GWord N → ℕ) × (List ℕ → σ)) (u : List ℕ) : Piece :=
  flatPiece (bNeckAtC R ρr ω u) (bArityAtC R ρr ω u)

omit [NeZero N] in
/-- The presented skeleton is an index set for the flat configurations. -/
lemma flat_pIdx (ω : (GWord N → ℕ) × (List ℕ → σ)) :
    PIdx (flatAt R ρr ω) (Presented R ρr ω) := by
  intro u j hu
  rw [presented_concat] at hu
  exact ⟨hu.1, by rw [flatAt, flatPiece_nports]; exact hu.2⟩

/-- **`thm:matched-presentation`\labelcref{it:matched-flat}**: every presented blob admits a
`(2R(T + 2) + 1)`-port quasi-isometry to its flat configuration. -/
theorem blobPiece_flat_portQI (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)}
    (hd : IsChainField N ω.1) (u : List ℕ) :
    ∃ f : (blobPiece R ρr ω u).carrier → (flatAt R ρr ω u).carrier,
      Presented R ρr ω u →
        IsPortQI (2 * (R * (ρr.T + 2) : ℕ) + 1) (blobPiece R ρr ω u).space (flatAt R ρr ω u).space f := by
  by_cases hu : Presented R ρr ω u
  · have e : flatAt R ρr ω u = flatPiece (bNeckAtC R ρr ω u) (blobPiece R ρr ω u).nports := by
      rw [flatAt, blobPiece_nports R ρr hR hd hu]
    rw [e]
    exact ⟨_, fun _ => isPortQI_collapse _ (blobPiece_isNeckPiece R ρr hR hd hu)⟩
  · exact ⟨fun _ => (flatAt R ρr ω u).entry, fun h => absurd h hu⟩

/-- **The glued flattening**: the blob assembly of a chain-regime sample is
`8(2R(T + 2) + 1)²`-quasi-isometric to the assembly of the flat configurations over the
presented skeleton. -/
theorem blob_flat_glued (hR : 1 ≤ R) {ω : (GWord N → ℕ) × (List ℕ → σ)}
    (hd : IsChainField N ω.1) :
    ∃ g : PAssembly (blobPiece R ρr ω) (Presented R ρr ω) (blob_pIdx R ρr hR hd)
        → PAssembly (flatAt R ρr ω) (Presented R ρr ω) (flat_pIdx R ρr ω),
      IsQIMap (8 * (2 * (R * (ρr.T + 2) : ℕ) + 1) ^ 2) g := by
  choose φ hφ using blobPiece_flat_portQI R ρr hR hd
  have hK : (1 : ℝ) ≤ 2 * (R * (ρr.T + 2) : ℕ) + 1 := by
    have : (0 : ℝ) ≤ (R * (ρr.T + 2) : ℕ) := Nat.cast_nonneg _
    linarith
  exact ⟨_, PAssembly.glue_isQIMap (blob_pIdx R ρr hR hd) (flat_pIdx R ρr ω) hK hφ⟩

end Presented

end Chain

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

lemma flatG_neckLen (n : ℕ) : (flatG n).neckLen = n + 1 := rfl

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

/-! ### Quasi-isometries compose -/

lemma IsQIMap.mono {K K' : ℝ} {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y}
    (hK : 0 ≤ K) (hKK' : K ≤ K') (hf : IsQIMap K f) : IsQIMap K' f := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun y => ?_⟩
  · have h1 := hf.upper a b
    have h2 : K * dist a b ≤ K' * dist a b := mul_le_mul_of_nonneg_right hKK' dist_nonneg
    linarith
  · have h1 := hf.lower a b
    have h2 : K * dist (f a) (f b) ≤ K' * dist (f a) (f b) :=
      mul_le_mul_of_nonneg_right hKK' dist_nonneg
    have h3 : K ^ 2 ≤ K' ^ 2 := by nlinarith
    linarith
  · obtain ⟨a, ha⟩ := hf.dense y
    exact ⟨a, ha.trans hKK'⟩

/-- A `K`-quasi-isometry has a `3K²`-quasi-inverse. -/
lemma IsQIMap.symm {K : ℝ} {X Y : Type*} [MetricSpace X] [MetricSpace Y] (hK : 1 ≤ K)
    {f : X → Y} (hf : IsQIMap K f) : ∃ g : Y → X, IsQIMap (3 * K ^ 2) g := by
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  choose g hg using hf.dense
  refine ⟨g, fun a b => ?_, fun a b => ?_, fun x => ?_⟩
  · have h1 := hf.lower (g a) (g b)
    have h2 : dist (f (g a)) (f (g b)) ≤ dist (f (g a)) a + dist a b + dist b (f (g b)) :=
      dist_triangle4 _ _ _ _
    have h3 : dist b (f (g b)) ≤ K := by rw [dist_comm]; exact hg b
    have h4 : K * dist (f (g a)) (f (g b))
        ≤ K * (dist (f (g a)) a + dist a b + dist b (f (g b))) :=
      mul_le_mul_of_nonneg_left h2 hK0
    have h5 : K * dist (f (g a)) a ≤ K * K := mul_le_mul_of_nonneg_left (hg a) hK0
    have h6 : K * dist b (f (g b)) ≤ K * K := mul_le_mul_of_nonneg_left h3 hK0
    nlinarith [mul_nonneg (mul_nonneg hK0 (sub_nonneg.mpr hK)) (dist_nonneg (x := a) (y := b)),
      mul_nonneg (mul_nonneg hK0 hK0) (dist_nonneg (x := a) (y := b))]
  · have h2 : dist a b ≤ dist a (f (g a)) + dist (f (g a)) (f (g b)) + dist (f (g b)) b :=
      dist_triangle4 _ _ _ _
    have h3 : dist a (f (g a)) ≤ K := by rw [dist_comm]; exact hg a
    have h4 := hf.upper (g a) (g b)
    nlinarith [hg b,
      mul_nonneg (mul_nonneg hK0 (sub_nonneg.mpr hK)) (dist_nonneg (x := g a) (y := g b)),
      mul_nonneg (mul_nonneg hK0 hK0) (dist_nonneg (x := g a) (y := g b)),
      mul_nonneg hK0 (sub_nonneg.mpr (one_le_pow₀ hK (n := 3))), pow_nonneg hK0 4]
  · refine ⟨f x, ?_⟩
    have h1 := hf.lower (g (f x)) x
    have h2 : K * dist (f (g (f x))) (f x) ≤ K * K :=
      mul_le_mul_of_nonneg_left (hg (f x)) hK0
    nlinarith [sq_nonneg K]

/-- A distance-preserving bijection transports a quasi-isometry along its inverse. -/
lemma IsQIMap.comp_isometry_symm {K : ℝ} {X X' Y : Type*} [MetricSpace X] [MetricSpace X']
    [MetricSpace Y] {Φ : X → X'} (hΦ : Function.Bijective Φ)
    (hΦd : ∀ x y, dist (Φ x) (Φ y) = dist x y) {f : X → Y} (hf : IsQIMap K f) :
    IsQIMap K (fun x' => f ((Equiv.ofBijective Φ hΦ).symm x')) := by
  set e := Equiv.ofBijective Φ hΦ
  have hd : ∀ x' y', dist (e.symm x') (e.symm y') = dist x' y' := by
    intro x' y'
    rw [← hΦd]
    show dist (e (e.symm x')) (e (e.symm y')) = _
    rw [e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨fun a b => ?_, fun a b => ?_, fun y => ?_⟩
  · rw [← hd]; exact hf.upper _ _
  · rw [← hd]; exact hf.lower _ _
  · obtain ⟨a, ha⟩ := hf.dense y
    exact ⟨e a, by simpa [e] using ha⟩

/-- A distance-preserving bijection transports a quasi-isometry on the target side. -/
lemma IsQIMap.isometry_comp {K : ℝ} {X Y Y' : Type*} [MetricSpace X] [MetricSpace Y]
    [MetricSpace Y'] {Φ : Y → Y'} (hΦ : Function.Surjective Φ)
    (hΦd : ∀ x y, dist (Φ x) (Φ y) = dist x y) {f : X → Y} (hf : IsQIMap K f) :
    IsQIMap K (fun x => Φ (f x)) := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun y' => ?_⟩
  · rw [hΦd]; exact hf.upper _ _
  · rw [hΦd]; exact hf.lower _ _
  · obtain ⟨y, rfl⟩ := hΦ y'
    obtain ⟨a, ha⟩ := hf.dense y
    exact ⟨a, by rw [hΦd]; exact ha⟩

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
  obtain ⟨g₂, hg₂⟩ := hg₁'.symm hK₁'
  obtain ⟨e₂, he₂⟩ := he'.symm hCenc
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

/-- **The deterministic core of `thm:chain-general`**, with the two encoded assemblies the
assemblies of two families of shapes over `𝔹` that are `K`-comparable copy by copy, the
second family already relabelled by the automorphism: the glued transfer of
`it:general-glued` over `𝔹` supplies the quasi-isometry of the encoded assemblies at
`8K²`. -/
theorem sample_qi_of_blob_matching' (hR : 1 ≤ R)
    {ω : (GWord N → ℕ) × (List ℕ → σ)} {ω' : (GWord N' → ℕ) × (List ℕ → σ')}
    (hd : IsChainField N ω.1) (hd' : IsChainField N' ω'.1)
    {τ τ' : List ℕ → GShape} {Cenc K : ℝ} (hCenc : 1 ≤ Cenc) (hK : 1 ≤ K)
    {e : PAssembly (flatAt R ρr ω) (Presented R ρr ω) (flat_pIdx R ρr ω) → GAssembly τ}
    (he : IsQIMap Cenc e)
    {e' : PAssembly (flatAt R ρr' ω') (Presented R ρr' ω') (flat_pIdx R ρr' ω') → GAssembly τ'}
    (he' : IsQIMap Cenc e')
    (hcomp : ∀ w, MarkedQI K (gShapeSpace (τ w)) (gShapeSpace (τ' w))) :
    ∃ F : {v : GWord N // v ∈ sample ω.1} → {v : GWord N' // v ∈ sample ω'.1},
      IsSampleQIN (3 * (3 * (3 * (3 * flatScale R ρr.T * Cenc) * (8 * K ^ 2)) * (3 * Cenc ^ 2))
        * (3 * flatScale R ρr'.T ^ 2)) F := by
  choose φ hφ using hcomp
  have hg : IsQIMap (8 * K ^ 2) (GAssembly.glue φ) :=
    ⟨(GAssembly.glued_transfer hK hφ).1, (GAssembly.glued_transfer hK hφ).2.1,
      (GAssembly.glued_transfer hK hφ).2.2⟩
  exact sample_qi_of_blob_matching R ρr ρr' hR hd hd' hCenc (by nlinarith) he he' hg

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

