import ChainClasses.Universality.Piece

/-!
`thm:chain-general`, the deterministic core, second part: the chain regime deterministically
(`IsChainField`, the neck vertices `rep` and the descent to the next split), and the blob of
a cluster root read off its trace, its vertices and its ports.  The lemmas about blobs
follow in `BlobPiece`.
-/

namespace ChainClasses

open BranchingProcess (sample Survives skeleton survivors skeletonDegree bushAt childSet)

variable {N : ℕ}

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


end Chain

end ChainClasses
