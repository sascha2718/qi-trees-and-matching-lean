import ChainClasses.Universality.BlobPiece

/-!
`thm:chain-general`, the deterministic core, fourth part: the presented skeleton and the
blob pieces of a rule, and the flat configurations of the presented blobs.  `BlobAssembly`
identifies the flat configurations with the bare-neck shapes and concludes.
-/

namespace ChainClasses

open BranchingProcess (sample Survives skeleton survivors skeletonDegree bushAt childSet)

variable {N : ℕ}

section Chain

variable [NeZero N]

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

/-- **`thm:matched-presentation` (`it:matched-flat`), the geometry**: a presented
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

/-- **`thm:matched-presentation` (`it:matched-flat`)**: every presented blob admits a
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

end ChainClasses
