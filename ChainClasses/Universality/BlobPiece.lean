import ChainClasses.Universality.ChainBlob

/-!
`thm:chain-general`, the deterministic core, third part: the lemmas about the blob of a
cluster root.  The shape of the vertices and the ports, prefix closure, the ports are
vertices and the planted children are not, the vertices and the planted children lie in
the sample, every vertex of the sample below a split is absorbed or handed on, the
presented children are the fields at the planted children, the automaton's traces fit,
the blob as a piece (`blobPieceOf`), and the depth of a blob below its split.  The
presented skeleton follows in `BlobPresented`.
-/

namespace ChainClasses

open BranchingProcess (sample Survives skeleton survivors skeletonDegree bushAt childSet)

variable {N : ℕ}

section Chain

variable [NeZero N]

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

end Chain

end ChainClasses
