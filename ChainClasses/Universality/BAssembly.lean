import ChainClasses.Universality.SampleAssembly

/-!
`thm:hairy-general` of `trichotomy.tex`, the deterministic geometry: the alignment of the
The geometry is built in four modules: `CascadeEncoding`, `AssemblyAut`, `SampleAssembly`
and this one, which states the deterministic core; the account below covers all four.

two label fields lives on `𝔹`, not on the reduced skeletons, and the assembly that the
glued transfer of `thm:general-glued` runs over is the `𝔹`-assembly, the shape of a
skeleton vertex placed at its cascade root and a one-vertex shape at every forced slot.
Four deterministic facts carry the proof from there to a quasi-isometry of the samples.

A bushy sample at general arity is isometric to the assembly of its own shapes over its
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
* `isQIWith_of_skel_qi`, `CascadeEnc.sample_qi_of_bShape_matching_of_isometric`: the
  composition, over abstract isometries of the samples with their skeleton assemblies.
* `transN` with `transN_addrDist`: the address translation of a field of letter maps over
  `ℕ`, an isometry when the letter maps are injective.
* `dyingSet`, `survLetter`, `dyingLetter`, `letterMap` with `letterMap_lt_iff`,
  `letterMap_injective`, `letterMap_surj`: **the letter map of a vertex**, a bijection of
  the child indices of the realisation onto the children of the vertex.
* `neckAddr`, `isAddr_realiseAux_neck_concat`, `isAddr_realiseAux_bush`,
  `isAddr_realiseAux_cases`: **the addresses of a realisation** at general arity, the
  neck vertices, their children, and the bushes.
* `IsGBushySample`: the deterministic hypotheses of **`thm:hairy-general`**, offspring
  within the alphabet, survival, and every neck ray meeting a split.
* `neckPath`, `neckIter_eq_ambSub_neckPath`, `gEntryV`, `redSub_eq_ambSub_gEntryV`: the
  descent of `GeneralDecomposition` located in the ambient tree, the copies being the
  subtrees at the entry vertices.
* `SkelAssembly.exists_code_concat_iff`, `transSampleN`, `transSampleN_neck`,
  `transSampleN_gCopyAddr`, `transSampleN_bush`, `transSampleN_code_spec`: **the
  dictionary**, the children of a vertex of the skeleton assembly and of its translate.
* `gAssembly_isometric_sample`: **`thm:shape-iid` at general arity, the isometry**, the
  premise of **`thm:general-glued`**: a bushy sample is isometric to the assembly of its
  shapes over its reduced skeleton.
* `sample_qi_of_bShape_matching`: **`thm:hairy-general`, the deterministic core**: two
  bushy samples with encoded skeletons matched by an automorphism of `𝔹` at
  comparability `K` are `⌈216 L L'² K²⌉`-quasi-isometric as graphs.
-/

namespace ChainClasses

open BranchingProcess (sample Survives survivors skeletonDegree)

variable {N : ℕ}

/-! ### `thm:hairy-general`, the deterministic core -/

/-- **`thm:hairy-general`, the deterministic core.**  Two bushy samples, over alphabets
`N` and `N'`, whose reduced skeletons are encoded into `𝔹` at depths `L` and `L'`, with an
automorphism `π` of `𝔹` carrying one encoded skeleton onto the other and matching the
shape labels at comparability `K`, are `⌈216 L L'² K²⌉`-quasi-isometric as graphs: each
sample is isometric to the assembly of its shapes over its reduced skeleton, that
assembly is `L`-quasi-isometric to the `𝔹`-assembly placing the shapes at the cascade
roots and one-vertex shapes at the forced slots, and the glued transfer over `𝔹` at `K`
assembles the matched shapes into an `8K²`-quasi-isometry of the `𝔹`-assemblies. -/
theorem sample_qi_of_bShape_matching {N' L L' : ℕ} {c : GWord N → ℕ} {c' : GWord N' → ℕ}
    (hc : IsGBushySample c) (hc' : IsGBushySample c') (E : CascadeEnc N L) (E' : CascadeEnc N' L')
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
