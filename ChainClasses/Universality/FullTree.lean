import Mathlib.Tactic
import ChainClasses.General.GeneralCascade
import ChainClasses.Universality.GeneralObstructions
import ChainClasses.Chain.WordGraph

/-!
`thm:bushy` of `prelims.tex`: a rooted subtree of `𝒩(N)` in which every vertex has at
least two children is quasi-isometric to the binary tree `𝔹`.  The paper cites
Mosher, Sageev and Whyte; the proof here is direct and runs through the cascade of
`thm:merge` (`it:merge-split`).

The cascade of depth `L = ⌈log₂ N⌉` sends the tree to a prefix-closed set of binary
words in which every copy is a split, the slots of the children `0` and `1` leaving the
copy by distinct first bits, and every vertex lies at most `L` above the copy of a
vertex of the tree.  A prefix-closed set of binary words with a split within `M` below
every vertex is quasi-isometric to `𝔹` by contracting its unary runs: the binary tree
embeds by sending the root to the first split and the `b`-th child of a vertex to the
first split below the `b`-th child of its image.  The embedding is prefix-monotone,
stretches every edge into a path of length between `1` and `M + 1`, preserves wedges,
and every vertex of the set lies within `M` of its image, on the unary run the
embedding contracts.

* `IsSplit`, `SplitsWithin`, `SplitChoice`, `exists_minimal_split`, `firstSplit`,
  `splitChoice_firstSplit`: the first split at or below a vertex, the split of minimal
  depth, which every vertex below `v` is comparable with.
* `splitEmbed`, `splitEmbed_mem`, `splitEmbed_append`, `wedge_splitEmbed`,
  `treeDist_splitEmbed`: the embedding of `𝔹` and its metric control `d ≤ d' ≤ (M+1) d`.
* `exists_splitEmbed_near`: every vertex lies within `M` of the image.
* `splitEmbed_isQIWith`, `quasiIsometric_binary_of_splitsWithin`: **the unary-run
  contraction**, a prefix-closed set of binary words with a split within `M` below
  every vertex is quasi-isometric to `𝔹`.
* `isSplit_cascWord`, `cascSet_splitsWithin`: the cascade of a full tree has a split
  within `L` below every vertex.
* `fullTree_quasiIsometric_binary`: **`thm:bushy`**.
* `ae_forall_two_le_of_zero`, `fullTree_gSample`: **`thm:bushy` in regime (F)**: at
  `θ₀ = θ₁ = 0` the sample tree is almost surely quasi-isometric to `𝔹`.
-/

namespace ChainClasses

open SimpleGraph MeasureTheory
open BranchingProcess (QuasiIsometric IsQIWith Offspring sample survivalMeasure)

/-! ### The first split below a vertex -/

section Contraction

variable {S : Word → Prop} {M : ℕ}

/-- A split: a vertex both of whose children lie in `S`. -/
def IsSplit (S : Word → Prop) (w : Word) : Prop := S (w ++ [false]) ∧ S (w ++ [true])

/-- Every vertex of `S` has a split at most `M` below it. -/
def SplitsWithin (S : Word → Prop) (M : ℕ) : Prop :=
  ∀ v, S v → ∃ w, S w ∧ v <+: w ∧ w.length ≤ v.length + M ∧ IsSplit S w

/-- A choice `spl` of a first split at or below every vertex: `spl v` is a split of `S`
below `v`, at most `M` deeper, and every vertex of `S` below `v` is comparable with it,
so the vertices strictly above `spl v` and at or below `v` form a unary run. -/
structure SplitChoice (S : Word → Prop) (M : ℕ) (spl : Word → Word) : Prop where
  mem : ∀ v, S v → S (spl v)
  below : ∀ v, S v → v <+: spl v
  depth : ∀ v, S v → (spl v).length ≤ v.length + M
  isSplit : ∀ v, S v → IsSplit S (spl v)
  comparable : ∀ v u, S v → S u → v <+: u → u <+: spl v ∨ spl v <+: u

/-- A vertex with two distinct children in `S` is a split. -/
lemma isSplit_of_ne {a b : Bool} (hab : a ≠ b) {p : Word} (ha : S (p ++ [a]))
    (hb : S (p ++ [b])) : IsSplit S p :=
  match a, b, hab with
  | false, true, _ => ⟨ha, hb⟩
  | true, false, _ => ⟨hb, ha⟩
  | false, false, h => absurd rfl h
  | true, true, h => absurd rfl h

/-- **The split of minimal depth below a vertex** is comparable with every vertex of
`S` below it: a vertex leaving the path to it would create a shallower split. -/
lemma exists_minimal_split (hS : PrefixClosed S) (hM : SplitsWithin S M) {v : Word}
    (hv : S v) :
    ∃ w, S w ∧ v <+: w ∧ w.length ≤ v.length + M ∧ IsSplit S w ∧
      ∀ u, S u → v <+: u → u <+: w ∨ w <+: u := by
  classical
  obtain ⟨w₀, hw₀, hvw₀, hlen₀, hsplit₀⟩ := hM v hv
  have hex : ∃ n, ∃ w, S w ∧ v <+: w ∧ w.length = n ∧ IsSplit S w :=
    ⟨w₀.length, w₀, hw₀, hvw₀, rfl, hsplit₀⟩
  obtain ⟨w, hw, hvw, hlen, hsplit⟩ := Nat.find_spec hex
  have hmin : Nat.find hex ≤ w₀.length := Nat.find_min' hex ⟨w₀, hw₀, hvw₀, rfl, hsplit₀⟩
  refine ⟨w, hw, hvw, by omega, hsplit, fun u hu hvu => ?_⟩
  by_contra hcon
  obtain ⟨p, a, b, hab, hpa, hpb⟩ :=
    exists_diverge (fun h => hcon (Or.inl h)) (fun h => hcon (Or.inr h))
  have hp : p = wedge u w := (wedge_of_diverge hab hpa hpb).symm
  have hvp : v <+: p := hp ▸ prefix_wedge hvu hvw
  have hpS : IsSplit S p := isSplit_of_ne hab (hS hpa hu) (hS hpb hw)
  have hplen : p.length < Nat.find hex := by
    have := hpb.length_le
    simp only [List.length_append, List.length_singleton] at this
    omega
  exact Nat.find_min hex hplen
    ⟨p, hS ((List.prefix_append p [a]).trans hpa) hu, hvp, rfl, hpS⟩

open Classical in
/-- The first split at or below a vertex of `S`, the split of minimal depth; off `S`
the vertex itself. -/
noncomputable def firstSplit (hS : PrefixClosed S) (hM : SplitsWithin S M) (v : Word) :
    Word :=
  if hv : S v then Classical.choose (exists_minimal_split hS hM hv) else v

lemma firstSplit_spec (hS : PrefixClosed S) (hM : SplitsWithin S M) {v : Word} (hv : S v) :
    S (firstSplit hS hM v) ∧ v <+: firstSplit hS hM v ∧
      (firstSplit hS hM v).length ≤ v.length + M ∧ IsSplit S (firstSplit hS hM v) ∧
      ∀ u, S u → v <+: u → u <+: firstSplit hS hM v ∨ firstSplit hS hM v <+: u := by
  simp only [firstSplit, dif_pos hv]
  exact Classical.choose_spec (exists_minimal_split hS hM hv)

/-- The first split is a choice of splits. -/
theorem splitChoice_firstSplit (hS : PrefixClosed S) (hM : SplitsWithin S M) :
    SplitChoice S M (firstSplit hS hM) where
  mem _ hv := (firstSplit_spec hS hM hv).1
  below _ hv := (firstSplit_spec hS hM hv).2.1
  depth _ hv := (firstSplit_spec hS hM hv).2.2.1
  isSplit _ hv := (firstSplit_spec hS hM hv).2.2.2.1
  comparable _ u hv hu hvu := (firstSplit_spec hS hM hv).2.2.2.2 u hu hvu

/-! ### The embedding of the binary tree -/

/-- The embedding of the binary tree: the root goes to the first split, and the `b`-th
child of a vertex to the first split below the `b`-th child of its image. -/
def splitEmbed (spl : Word → Word) (w : Word) : Word :=
  w.foldl (fun acc b => spl (acc ++ [b])) (spl [])

@[simp] lemma splitEmbed_nil (spl : Word → Word) : splitEmbed spl [] = spl [] := rfl

lemma splitEmbed_concat (spl : Word → Word) (w : Word) (b : Bool) :
    splitEmbed spl (w ++ [b]) = spl (splitEmbed spl w ++ [b]) := by
  simp [splitEmbed, List.foldl_append]

variable {spl : Word → Word}

/-- Every image is a split of `S`. -/
lemma splitEmbed_mem (h : SplitChoice S M spl) (hroot : S []) (w : Word) :
    S (splitEmbed spl w) ∧ IsSplit S (splitEmbed spl w) := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨h.mem [] hroot, h.isSplit [] hroot⟩
  | append_singleton w b ih =>
      rw [splitEmbed_concat]
      have hb : S (splitEmbed spl w ++ [b]) := by
        cases b
        · exact ih.2.1
        · exact ih.2.2
      exact ⟨h.mem _ hb, h.isSplit _ hb⟩

/-- The children of an image lie in `S`. -/
lemma splitEmbed_child_mem (h : SplitChoice S M spl) (hroot : S []) (w : Word) (b : Bool) :
    S (splitEmbed spl w ++ [b]) := by
  cases b
  · exact (splitEmbed_mem h hroot w).2.1
  · exact (splitEmbed_mem h hroot w).2.2

/-- One edge of `𝔹` becomes a path below the child of the image. -/
lemma splitEmbed_concat_prefix (h : SplitChoice S M spl) (hroot : S []) (w : Word)
    (b : Bool) : splitEmbed spl w ++ [b] <+: splitEmbed spl (w ++ [b]) := by
  rw [splitEmbed_concat]
  exact h.below _ (splitEmbed_child_mem h hroot w b)

/-- One edge of `𝔹` becomes a path of length at most `M + 1`. -/
lemma splitEmbed_concat_length (h : SplitChoice S M spl) (hroot : S []) (w : Word)
    (b : Bool) : (splitEmbed spl (w ++ [b])).length ≤ (splitEmbed spl w).length + (M + 1) := by
  rw [splitEmbed_concat]
  have := h.depth _ (splitEmbed_child_mem h hroot w b)
  simp only [List.length_append, List.length_singleton] at this
  omega

/-- The embedding is prefix-monotone and stretches depth differences by a factor between
`1` and `M + 1`. -/
lemma splitEmbed_append (h : SplitChoice S M spl) (hroot : S []) (u s : Word) :
    splitEmbed spl u <+: splitEmbed spl (u ++ s) ∧
      (splitEmbed spl u).length + s.length ≤ (splitEmbed spl (u ++ s)).length ∧
      (splitEmbed spl (u ++ s)).length ≤ (splitEmbed spl u).length + (M + 1) * s.length := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s b ih =>
      rw [← List.append_assoc]
      obtain ⟨h1, h2, h3⟩ := ih
      have h4 := splitEmbed_concat_prefix h hroot (u ++ s) b
      have h5 := splitEmbed_concat_length h hroot (u ++ s) b
      have h6 := h4.length_le
      simp only [List.length_append, List.length_singleton] at h6 ⊢
      rw [Nat.mul_succ]
      exact ⟨h1.trans ((List.prefix_append _ _).trans h4), by omega, by omega⟩

/-- The embedding is prefix-monotone. -/
lemma splitEmbed_prefix (h : SplitChoice S M spl) (hroot : S []) {u w : Word}
    (huw : u <+: w) : splitEmbed spl u <+: splitEmbed spl w := by
  obtain ⟨s, rfl⟩ := huw
  exact (splitEmbed_append h hroot u s).1

/-- The embedding preserves wedges: two words diverging at `p` have images diverging at
the image of `p`, through its two children. -/
lemma wedge_splitEmbed (h : SplitChoice S M spl) (hroot : S []) (x y : Word) :
    wedge (splitEmbed spl x) (splitEmbed spl y) = splitEmbed spl (wedge x y) := by
  by_cases hxy : x <+: y
  · rw [wedge_of_prefix hxy, wedge_of_prefix (splitEmbed_prefix h hroot hxy)]
  by_cases hyx : y <+: x
  · rw [wedge_comm x y, wedge_of_prefix hyx, wedge_comm,
      wedge_of_prefix (splitEmbed_prefix h hroot hyx)]
  obtain ⟨p, a, b, hab, hpa, hpb⟩ := exists_diverge hxy hyx
  rw [wedge_of_diverge hab hpa hpb]
  refine wedge_of_diverge hab ?_ ?_
  · exact (splitEmbed_concat_prefix h hroot p a).trans (splitEmbed_prefix h hroot hpa)
  · exact (splitEmbed_concat_prefix h hroot p b).trans (splitEmbed_prefix h hroot hpb)

/-- **The metric control of the embedding**: `d ≤ d' ≤ (M + 1) d` between images. -/
lemma treeDist_splitEmbed (h : SplitChoice S M spl) (hroot : S []) (x y : Word) :
    treeDist x y ≤ treeDist (splitEmbed spl x) (splitEmbed spl y) ∧
      treeDist (splitEmbed spl x) (splitEmbed spl y) ≤ (M + 1) * treeDist x y := by
  have h1 := treeDist_add_wedge_length x y
  have h2 := treeDist_add_wedge_length (splitEmbed spl x) (splitEmbed spl y)
  rw [wedge_splitEmbed h hroot] at h2
  obtain ⟨sx, hsx⟩ := wedge_prefix_left x y
  obtain ⟨sy, hsy⟩ := wedge_prefix_right x y
  have hx := splitEmbed_append h hroot (wedge x y) sx
  have hy := splitEmbed_append h hroot (wedge x y) sy
  rw [hsx] at hx
  rw [hsy] at hy
  have hlx : x.length = (wedge x y).length + sx.length := by
    have := congrArg List.length hsx
    simp only [List.length_append] at this
    omega
  have hly : y.length = (wedge x y).length + sy.length := by
    have := congrArg List.length hsy
    simp only [List.length_append] at this
    omega
  have hd : treeDist x y = sx.length + sy.length := by omega
  rw [hd, Nat.mul_add]
  omega

/-- **Every vertex of `S` lies within `M` of an image**: it is an image, or it sits on
the unary run between the child of an image and the first split below that child. -/
lemma exists_splitEmbed_near (hS : PrefixClosed S) (h : SplitChoice S M spl) (hroot : S [])
    {z : Word} (hz : S z) : ∃ x, treeDist (splitEmbed spl x) z ≤ M := by
  suffices key : ∃ x, splitEmbed spl x = z ∨
      ∃ v, S v ∧ v <+: z ∧ z <+: splitEmbed spl x ∧ splitEmbed spl x = spl v by
    obtain ⟨x, hx | ⟨v, hv, hvz, hzx, hx⟩⟩ := key
    · exact ⟨x, by rw [hx, treeDist_self]; exact Nat.zero_le _⟩
    · refine ⟨x, ?_⟩
      rw [treeDist_comm, treeDist_of_prefix hzx, hx]
      have := h.depth v hv
      have := hvz.length_le
      omega
  induction z using List.reverseRecOn with
  | nil => exact ⟨[], Or.inr ⟨[], hroot, List.nil_prefix, List.nil_prefix, rfl⟩⟩
  | append_singleton z b ih =>
      have hzS : S z := hS (List.prefix_append z [b]) hz
      obtain ⟨x, hx | ⟨v, hv, hvz, hzx, hx⟩⟩ := ih hzS
      · refine ⟨x ++ [b], Or.inr ⟨z ++ [b], hz, List.prefix_refl _, ?_, ?_⟩⟩
        · rw [splitEmbed_concat, hx]
          exact h.below _ hz
        · rw [splitEmbed_concat, hx]
      · rcases h.comparable v (z ++ [b]) hv hz (hvz.trans (List.prefix_append z [b]))
          with hc | hc
        · exact ⟨x, Or.inr ⟨v, hv, hvz.trans (List.prefix_append z [b]),
            by rw [hx]; exact hc, hx⟩⟩
        · rw [← hx] at hc
          rcases List.prefix_concat_iff.mp hc with hc' | hc'
          · exact ⟨x, Or.inl hc'⟩
          · have hxz : splitEmbed spl x = z :=
              hc'.eq_of_length (le_antisymm hc'.length_le hzx.length_le)
            refine ⟨x ++ [b], Or.inr ⟨z ++ [b], hz, List.prefix_refl _, ?_, ?_⟩⟩
            · rw [splitEmbed_concat, hxz]
              exact h.below _ hz
            · rw [splitEmbed_concat, hxz]

/-! ### The unary-run contraction -/

/-- The embedding as a map of vertex sets. -/
def splitEmbedMap (h : SplitChoice S M spl) (hroot : S []) :
    {w : Word // (fun _ : Word => True) w} → {w : Word // S w} :=
  fun x => ⟨splitEmbed spl x.1, (splitEmbed_mem h hroot x.1).1⟩

/-- **The embedding is an `(M + 1)`-quasi-isometry** of `𝔹` into the graph of `S`. -/
theorem splitEmbed_isQIWith (hS : PrefixClosed S) (h : SplitChoice S M spl) (hroot : S []) :
    BranchingProcess.IsQIWith (M + 1) binaryGraph (wordGraph S) (splitEmbedMap h hroot) where
  upper x y := by
    rw [wordGraph_dist hS, wordGraph_dist prefixClosed_true]
    exact (treeDist_splitEmbed h hroot x.1 y.1).2.trans (Nat.le_add_right _ _)
  lower x y := by
    rw [wordGraph_dist hS, wordGraph_dist prefixClosed_true]
    have h1 := (treeDist_splitEmbed h hroot x.1 y.1).1
    have h2 := Nat.le_mul_of_pos_left
      (treeDist (splitEmbed spl x.1) (splitEmbed spl y.1)) (Nat.succ_pos M)
    exact h1.trans (h2.trans (Nat.le_add_right _ _))
  dense z := by
    obtain ⟨x, hx⟩ := exists_splitEmbed_near hS h hroot z.2
    refine ⟨⟨x, trivial⟩, ?_⟩
    rw [wordGraph_dist hS]
    exact hx.trans (Nat.le_succ M)

/-- **The unary-run contraction.** A prefix-closed set of binary words with a split
within `M` below every vertex is quasi-isometric to the binary tree `𝔹`. -/
theorem quasiIsometric_binary_of_splitsWithin (hS : PrefixClosed S) (hroot : S [])
    (hM : SplitsWithin S M) : QuasiIsometric (wordGraph S) binaryGraph :=
  QuasiIsometric.symm (wordGraph_connected hS ⟨⟨[], hroot⟩⟩)
    ⟨M + 1, _, splitEmbed_isQIWith hS (splitChoice_firstSplit hS hM) hroot⟩

end Contraction

/-! ### The cascade of a full tree -/

section Cascade

variable {N L : ℕ} {T : BranchingProcess.Word N → Prop}

/-- The slot of the child `0` leaves the copy by `false`. -/
lemma bitsL_zero_succ (L : ℕ) : bitsL (L + 1) 0 = false :: bitsL L 0 := by
  simp [bitsL_succ]

/-- The slot of the child `1` leaves the copy by `true`. -/
lemma bitsL_one_succ (L : ℕ) : bitsL (L + 1) 1 = true :: bitsL L 0 := by
  simp [bitsL_succ]

/-- **Every copy is a split** of the cascade of a full tree: the slots of the children
`0` and `1` leave the copy by distinct first bits. -/
lemma isSplit_cascWord (hN : 2 ≤ N) (hL : 1 ≤ L)
    (hfull : ∀ v, T v → T (v ++ [⟨0, by omega⟩]) ∧ T (v ++ [⟨1, by omega⟩]))
    {w : BranchingProcess.Word N} (hw : T w) : IsSplit (cascSet L T) (cascWord L w) := by
  obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  refine ⟨⟨w ++ [⟨0, by omega⟩], (hfull w hw).1, ?_⟩, ⟨w ++ [⟨1, by omega⟩], (hfull w hw).2, ?_⟩⟩
  · rw [cascWord_append, cascWord_cons, cascWord_nil, List.append_nil]
    show cascWord (L + 1) w ++ [false] <+: cascWord (L + 1) w ++ bitsL (L + 1) 0
    rw [bitsL_zero_succ]
    exact (List.prefix_append_right_inj _).mpr ⟨_, rfl⟩
  · rw [cascWord_append, cascWord_cons, cascWord_nil, List.append_nil]
    show cascWord (L + 1) w ++ [true] <+: cascWord (L + 1) w ++ bitsL (L + 1) 1
    rw [bitsL_one_succ]
    exact (List.prefix_append_right_inj _).mpr ⟨_, rfl⟩

/-- **The cascade of a full tree has a split within `L` below every vertex**: a cascade
vertex is a copy, or lies strictly inside the cascade of one split, at most `L` above
the copy of the child whose slot it leads to. -/
lemma cascSet_splitsWithin (hN : 2 ≤ N) (hL : 1 ≤ L) (hT : PrefixClosedN T)
    (hfull : ∀ v, T v → T (v ++ [⟨0, by omega⟩]) ∧ T (v ++ [⟨1, by omega⟩])) :
    SplitsWithin (cascSet L T) L := by
  rintro x ⟨w, hw, hxw⟩
  obtain ⟨w', hw'w, hw'x, hlen⟩ := exists_prefix_cascWord_near L w x hxw
  obtain ⟨s, rfl⟩ := hw'w
  cases s with
  | nil =>
      rw [List.append_nil] at hxw hw
      have hx : x = cascWord L w' :=
        hxw.eq_of_length (le_antisymm hxw.length_le hw'x.length_le)
      exact ⟨x, ⟨w', hw, hxw⟩, List.prefix_refl _, by omega,
        hx ▸ isSplit_cascWord hN hL hfull hw⟩
  | cons j s =>
      have hj : T (w' ++ [j]) :=
        hT ((List.prefix_append_right_inj w').mpr ⟨s, by simp⟩) hw
      have hxlen := hw'x.length_le
      rw [length_cascWord] at hxlen
      have hxj : x <+: cascWord L (w' ++ [j]) := by
        refine prefix_of_prefix_of_length_le hxw
          (cascWord_prefix L ((List.prefix_append_right_inj w').mpr ⟨s, by simp⟩)) ?_
        rw [length_cascWord]
        simp only [List.length_append, List.length_singleton, Nat.mul_succ]
        omega
      refine ⟨cascWord L (w' ++ [j]), cascSet_cascWord L hj, hxj, ?_,
        isSplit_cascWord hN hL hfull hj⟩
      rw [length_cascWord]
      simp only [List.length_append, List.length_singleton, Nat.mul_succ]
      omega

/-- **`thm:bushy`.** A rooted subtree of `𝒩(N)` in which every vertex has the children
`0` and `1` is quasi-isometric to the binary tree `𝔹`: the cascade of depth
`⌈log₂ N⌉` is a quasi-isometry onto a set of binary words with a split within
`⌈log₂ N⌉` below every vertex, and the unary-run contraction finishes. -/
theorem fullTree_quasiIsometric_binary (hN : 2 ≤ N) (T : BranchingProcess.Word N → Prop)
    (hT : PrefixClosedN T) (hroot : T [])
    (hfull : ∀ v, T v → T (v ++ [⟨0, by omega⟩]) ∧ T (v ++ [⟨1, by omega⟩])) :
    QuasiIsometric (wordGraphN T) binaryGraph :=
  QuasiIsometric.trans (wordGraph_connected prefixClosed_true ⟨⟨[], trivial⟩⟩)
    (cascade_quasiIsometric (Nat.le_pow_clog (by norm_num) N)
      (Nat.clog_pos (by norm_num) hN) hT)
    (quasiIsometric_binary_of_splitsWithin (prefixClosed_cascSet _ T)
      (cascSet_cascWord _ hroot)
      (cascSet_splitsWithin hN (Nat.clog_pos (by norm_num) hN) hT hfull))

end Cascade

/-! ### Regime (F) -/

section Sample

variable {J N : ℕ} (θ : Offspring J)

/-- At `θ₀ = θ₁ = 0` every vertex has at least two children, almost surely. -/
lemma ae_forall_two_le_of_zero (h0 : θ 0 = 0) (h1 : θ 1 = 0) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, ∀ v : GWord N, 2 ≤ c v := by
  refine ae_all_iff.mpr fun v => ?_
  rw [ae_iff]
  have hs : BranchingProcess.sampleMeasure (N := N) θ {c : GWord N → ℕ | ¬ 2 ≤ c v} = 0 := by
    have he : {c : GWord N → ℕ | ¬ 2 ≤ c v}
        = {c : GWord N → ℕ | c v = 0} ∪ {c : GWord N → ℕ | c v = 1} := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_union]
      omega
    rw [he]
    refine measure_union_null ?_ ?_
    · rw [BranchingProcess.sampleMeasure_coord θ v 0, h0, ENNReal.ofReal_zero]
    · rw [BranchingProcess.sampleMeasure_coord θ v 1, h1, ENNReal.ofReal_zero]
  rw [BranchingProcess.survivalMeasure_apply]
  exact mul_eq_zero.mpr (Or.inr (measure_mono_null Set.inter_subset_right hs))

/-- The alphabet has at least two letters once the law has no mass at zero and one. -/
lemma two_le_of_zero (hJN : J ≤ N) (h0 : θ 0 = 0) (h1 : θ 1 = 0) : 2 ≤ N := by
  by_contra hN
  have htot := θ.total
  have hJ : J ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hJ with rfl | rfl
  · simp [h0] at htot
  · simp [Finset.sum_range_succ, h0, h1] at htot

/-- **`thm:bushy` in regime (F).** At `θ₀ = θ₁ = 0` every vertex of the sample tree has
at least two children almost surely, so the sample tree is almost surely
quasi-isometric to the binary tree `𝔹`. -/
theorem fullTree_gSample (hJN : J ≤ N) (h0 : θ 0 = 0) (h1 : θ 1 = 0) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ,
      QuasiIsometric (wordGraphN (fun w : GWord N => w ∈ sample c)) binaryGraph := by
  have hN : 2 ≤ N := two_le_of_zero θ hJN h0 h1
  filter_upwards [ae_forall_two_le_of_zero θ h0 h1] with c hc
  refine fullTree_quasiIsometric_binary hN _ (prefixClosedN_sample c)
    (BranchingProcess.nil_mem_sample c) fun v hv => ⟨?_, ?_⟩
  · refine BranchingProcess.mem_sample_append_singleton.mpr ⟨hv, ?_⟩
    have := hc v
    show 0 < c v
    omega
  · refine BranchingProcess.mem_sample_append_singleton.mpr ⟨hv, ?_⟩
    have := hc v
    show 1 < c v
    omega

end Sample

end ChainClasses
