/-
`thm:three-rays` for the sample tree of `sec:encoding`, and with it the ray
half of `thm:converse`.

`BranchingProcess.Geometry` proves the obstruction for an abstract tree: a tree
carrying three rays that pairwise meet only in their common initial vertex is
not quasi-isometric to the ray.  This file exhibits the three rays in the
sample tree.  On the event `Ω₀` every chain terminates, so a split vertex `u`
exists and a further split `v` sits below `u` in the subtree of its second
child; the two children of `v` carry two rays and the third climbs from `v`
past `u` and descends the other child of `u`.

* `splitV`, `rayWord`: the vertex and the three rays out of it.
* `not_quasiIsometric_rayGraph_of_splits`: the obstruction over the three
  membership hypotheses the rays need.
* `not_quasiIsometric_rayGraph_inTree`: those hypotheses on `Ω₀`.
* `converse_ae`: `thm:converse` on the constructed space, both halves in the
  graph setting through `ChainClasses.WordGraph`.
-/
import Mathlib.Tactic
import ChainClasses.WordGraph
import ChainClasses.Converse
import ChainClasses.TwoValue

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open BranchingProcess (IsRay QuasiIsometric rayGraph)

variable {T : Word → Prop}

/-! ### Isometric rays in the graph of a set of words -/

/-- A sequence of vertices stepping one edge at a time and receding from its
start at unit speed is an isometric ray: it is a geodesic from its start, and
every subsegment of a geodesic is a geodesic. -/
lemma isRay_of (hT : PrefixClosed T) (g : ℕ → {w : Word // T w})
    (hstep : ∀ n, treeDist (g n).1 (g (n + 1)).1 = 1)
    (hbase : ∀ n, treeDist (g 0).1 (g n).1 = n) :
    IsRay (wordGraph T) g := by
  have hle : ∀ m d : ℕ, treeDist (g m).1 (g (m + d)).1 ≤ d := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
        have h1 := treeDist_triangle (g m).1 (g (m + d)).1 (g (m + d + 1)).1
        have h2 := hstep (m + d)
        have hrw : m + (d + 1) = m + d + 1 := by omega
        rw [hrw]
        omega
  have key : ∀ m n : ℕ, m ≤ n → treeDist (g m).1 (g n).1 = n - m := by
    intro m n hmn
    have h1 := treeDist_triangle (g 0).1 (g m).1 (g n).1
    rw [hbase m, hbase n] at h1
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have h2 := hle m d
    omega
  intro m n
  rw [wordGraph_dist hT]
  rcases le_total m n with h | h
  · rw [key m n h]
    unfold Nat.dist
    omega
  · rw [treeDist_comm, key n m h]
    unfold Nat.dist
    omega

/-! ### The three rays out of a split below a split -/

/-- The lower split: the vertex `u·2·1^k` of the paper's notation. -/
def splitV (u : Word) (k : ℕ) : Word := (u ++ [true]) ++ List.replicate k false

lemma splitV_length (u : Word) (k : ℕ) : (splitV u k).length = u.length + 1 + k := by
  simp only [splitV, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil]

/-- The three rays out of `splitV u k`: down its chain child, down its second
child, and up past `u` and down the other child of `u`. -/
def rayWord (u : Word) (k : ℕ) : Fin 3 → ℕ → Word
  | 0, n => splitV u k ++ List.replicate n false
  | 1, n => if n = 0 then splitV u k
            else (splitV u k ++ [true]) ++ List.replicate (n - 1) false
  | 2, n => if n ≤ k then (u ++ [true]) ++ List.replicate (k - n) false
            else u ++ List.replicate (n - k - 1) false

@[simp] lemma rayWord_zero (u : Word) (k : ℕ) (i : Fin 3) :
    rayWord u k i 0 = splitV u k := by
  fin_cases i <;> simp [rayWord, splitV]

/-! ### The three membership hypotheses -/

variable {u : Word} {k : ℕ}

/-- Every vertex of the three rays lies in the tree. -/
lemma rayWord_mem (hT : PrefixClosed T)
    (hu : ∀ j, T (u ++ List.replicate j false))
    (hv : ∀ j, T (splitV u k ++ List.replicate j false))
    (hvt : ∀ j, T ((splitV u k ++ [true]) ++ List.replicate j false))
    (i : Fin 3) (n : ℕ) : T (rayWord u k i n) := by
  fin_cases i
  · exact hv n
  · show T (if n = 0 then _ else _)
    split
    · simpa using hv 0
    · exact hvt (n - 1)
  · show T (if n ≤ k then _ else _)
    split
    · refine hT (append_replicate_prefix (u ++ [true]) false (Nat.sub_le k _)) ?_
      simpa [splitV] using hv 0
    · exact hu (n - k - 1)

/-! ### The two ray conditions -/

/-- Each ray recedes from `splitV u k` at unit speed. -/
lemma treeDist_rayWord_zero (i : Fin 3) (n : ℕ) :
    treeDist (splitV u k) (rayWord u k i n) = n := by
  fin_cases i
  · show treeDist (splitV u k) (splitV u k ++ List.replicate n false) = n
    rw [treeDist_of_prefix (List.prefix_append _ _)]
    simp
  · show treeDist (splitV u k) (if n = 0 then _ else _) = n
    split
    · next h => simp [h]
    · next h =>
        rw [treeDist_of_prefix
          ((List.prefix_append (splitV u k) [true]).trans (List.prefix_append _ _))]
        simp only [List.length_append, List.length_replicate, List.length_cons,
          List.length_nil]
        omega
  · show treeDist (splitV u k) (if n ≤ k then _ else _) = n
    split
    · next h =>
        have hpre : (u ++ [true]) ++ List.replicate (k - n) false <+: splitV u k :=
          append_replicate_prefix (u ++ [true]) false (Nat.sub_le k n)
        rw [treeDist_comm, treeDist_of_prefix hpre, splitV_length]
        simp only [List.length_append, List.length_replicate, List.length_cons,
          List.length_nil]
        omega
    · next h =>
        rcases Nat.eq_zero_or_pos (n - k - 1) with hj | hj
        · have hpre : u <+: splitV u k :=
            (List.prefix_append u [true]).trans (List.prefix_append _ _)
          rw [hj]
          simp only [List.replicate_zero, List.append_nil]
          rw [treeDist_comm, treeDist_of_prefix hpre, splitV_length]
          omega
        · have hfalse : ([false] : Word) <+: List.replicate (n - k - 1) false := by
            obtain ⟨d, hd⟩ : ∃ d, n - k - 1 = 1 + d := ⟨n - k - 2, by omega⟩
            rw [hd, List.replicate_add]
            exact List.prefix_append _ _
          have hw : wedge (splitV u k) (u ++ List.replicate (n - k - 1) false) = u :=
            wedge_of_diverge (a := true) (b := false) (by simp)
              (by rw [splitV]; exact List.prefix_append _ _)
              (List.prefix_self_append_iff.mpr hfalse)
          have h1 := treeDist_add_wedge_length (splitV u k) (u ++ List.replicate (n - k - 1) false)
          rw [hw, splitV_length] at h1
          simp only [List.length_append, List.length_replicate] at h1
          omega

/-- Consecutive vertices of each ray are adjacent. -/
lemma treeDist_rayWord_step (i : Fin 3) (n : ℕ) :
    treeDist (rayWord u k i n) (rayWord u k i (n + 1)) = 1 := by
  fin_cases i
  · show treeDist (splitV u k ++ List.replicate n false)
        (splitV u k ++ List.replicate (n + 1) false) = 1
    rw [treeDist_of_prefix (append_replicate_prefix _ _ (Nat.le_succ n))]
    simp only [List.length_append, List.length_replicate]
    omega
  · show treeDist
        (if n = 0 then splitV u k
          else (splitV u k ++ [true]) ++ List.replicate (n - 1) false)
        (if n + 1 = 0 then splitV u k
          else (splitV u k ++ [true]) ++ List.replicate (n + 1 - 1) false) = 1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [if_pos rfl, if_neg (by omega)]
      simp only [Nat.add_sub_cancel, List.replicate_zero, List.append_nil]
      rw [treeDist_of_prefix (List.prefix_append (splitV u k) [true])]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · rw [if_neg (by omega), if_neg (by omega)]
      rw [treeDist_of_prefix (append_replicate_prefix _ _ (by omega : n - 1 ≤ n + 1 - 1))]
      simp only [List.length_append, List.length_replicate]
      omega
  · show treeDist (if n ≤ k then _ else _) (if n + 1 ≤ k then _ else _) = 1
    rcases Nat.lt_or_ge n k with h | h
    · rw [if_pos (by omega), if_pos (by omega)]
      rw [treeDist_comm, treeDist_of_prefix
        (append_replicate_prefix (u ++ [true]) false (by omega : k - (n + 1) ≤ k - n))]
      simp only [List.length_append, List.length_replicate]
      omega
    · rcases Nat.eq_or_lt_of_le h with h' | h'
      · rw [if_pos (by omega), if_neg (by omega)]
        have e1 : k - n = 0 := by omega
        have e2 : n + 1 - k - 1 = 0 := by omega
        rw [e1, e2]
        simp only [List.replicate_zero, List.append_nil]
        rw [treeDist_comm, treeDist_of_prefix (List.prefix_append u [true])]
        simp
      · rw [if_neg (by omega), if_neg (by omega)]
        rw [treeDist_of_prefix (append_replicate_prefix u false (by omega))]
        simp only [List.length_append, List.length_replicate]
        omega

/-! ### The three rays meet only at their initial vertex -/

/-- Past its initial vertex the first ray keeps below the chain child. -/
lemma prefix_rayWord_zero {n : ℕ} (hn : n ≠ 0) :
    splitV u k ++ [false] <+: rayWord u k 0 n := by
  show splitV u k ++ [false] <+: splitV u k ++ List.replicate n false
  refine List.prefix_self_append_iff.mpr ?_
  obtain ⟨d, rfl⟩ : ∃ d, n = 1 + d := ⟨n - 1, by omega⟩
  rw [List.replicate_add]
  exact List.prefix_append _ _

/-- Past its initial vertex the second ray keeps below the second child. -/
lemma prefix_rayWord_one {n : ℕ} (hn : n ≠ 0) :
    splitV u k ++ [true] <+: rayWord u k 1 n := by
  show splitV u k ++ [true] <+: (if n = 0 then _ else _)
  rw [if_neg hn]
  exact List.prefix_append _ _

/-- Past its initial vertex the third ray leaves the subtree below the initial
vertex: its early stages are proper ancestors, and its later stages descend the
other child of `u`. -/
lemma not_prefix_rayWord_two {n : ℕ} (hn : n ≠ 0) :
    ¬ splitV u k <+: rayWord u k 2 n := by
  show ¬ splitV u k <+: (if n ≤ k then _ else _)
  split
  · next h =>
      intro hcon
      have := hcon.length_le
      rw [splitV_length] at this
      simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil] at this
      omega
  · next h =>
      intro hcon
      have h1 : u ++ [true] <+: u ++ List.replicate (n - k - 1) false :=
        (List.prefix_append _ _).trans hcon
      have h2 : ([true] : Word) <+: List.replicate (n - k - 1) false :=
        List.prefix_self_append_iff.mp h1
      rcases Nat.eq_zero_or_pos (n - k - 1) with hj | hj
      · rw [hj] at h2
        simp at h2
      · have hsplit : List.replicate (n - k - 1) false
            = false :: List.replicate (n - k - 2) false := by
          obtain ⟨d, hd⟩ : ∃ d, n - k - 1 = d + 1 := ⟨n - k - 2, by omega⟩
          have hd2 : d = n - k - 2 := by omega
          rw [hd, hd2, List.replicate_succ]
        rw [hsplit] at h2
        rw [show ([true] : Word) = true :: [] from rfl, List.cons_prefix_cons] at h2
        simp at h2

/-- The first two rays part at the initial vertex. -/
lemma rayWord_ne_zero_one {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    rayWord u k 0 m ≠ rayWord u k 1 n := by
  intro h
  have h0 := prefix_rayWord_zero (u := u) (k := k) hm
  have h1 := prefix_rayWord_one (u := u) (k := k) hn
  rw [← h] at h1
  have : (splitV u k ++ [false] : Word) = splitV u k ++ [true] :=
    (prefix_of_prefix_of_length_le h0 h1 (by simp)).eq_of_length (by simp)
  simp at this

/-- The first and the third ray part at the initial vertex. -/
lemma rayWord_ne_zero_two {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    rayWord u k 0 m ≠ rayWord u k 2 n := by
  intro h
  refine not_prefix_rayWord_two (u := u) (k := k) hn ?_
  rw [← h]
  exact (List.prefix_append (splitV u k) [false]).trans (prefix_rayWord_zero hm)

/-- The second and the third ray part at the initial vertex. -/
lemma rayWord_ne_one_two {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    rayWord u k 1 m ≠ rayWord u k 2 n := by
  intro h
  refine not_prefix_rayWord_two (u := u) (k := k) hn ?_
  rw [← h]
  exact (List.prefix_append (splitV u k) [true]).trans (prefix_rayWord_one hm)

/-- **The three rays meet only at their initial vertex.** -/
lemma rayWord_ne {i j : Fin 3} (hij : i ≠ j) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    rayWord u k i m ≠ rayWord u k j n := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact rayWord_ne_zero_one hm hn
  · exact rayWord_ne_zero_two hm hn
  · exact fun h => rayWord_ne_zero_one hn hm h.symm
  · exact absurd rfl hij
  · exact rayWord_ne_one_two hm hn
  · exact fun h => rayWord_ne_zero_two hn hm h.symm
  · exact fun h => rayWord_ne_one_two hn hm h.symm
  · exact absurd rfl hij

/-! ### The obstruction -/

/-- **`thm:three-rays` for a set of words.** A prefix-closed set containing a
split `u` and a further split `splitV u k` below its second child is not
quasi-isometric to the ray. -/
theorem not_quasiIsometric_rayGraph_of_splits (hT : PrefixClosed T)
    (hu : ∀ j, T (u ++ List.replicate j false))
    (hv : ∀ j, T (splitV u k ++ List.replicate j false))
    (hvt : ∀ j, T ((splitV u k ++ [true]) ++ List.replicate j false)) :
    ¬ QuasiIsometric (wordGraph T) rayGraph := by
  have hvT : T (splitV u k) := by simpa using hv 0
  have hne : Nonempty {w : Word // T w} := ⟨⟨splitV u k, hvT⟩⟩
  refine BranchingProcess.not_quasiIsometric_rayGraph
    (v := (⟨splitV u k, hvT⟩ : {w : Word // T w}))
    (ray := fun i n => ⟨rayWord u k i n, rayWord_mem hT hu hv hvt i n⟩)
    (wordGraph_isTree hT hne) (fun i => ?_) (fun i => ?_) (fun i j hij m n hmn => ?_)
  · refine isRay_of hT _ (fun n => treeDist_rayWord_step i n) (fun n => ?_)
    show treeDist (rayWord u k i 0) (rayWord u k i n) = n
    rw [rayWord_zero]
    exact treeDist_rayWord_zero i n
  · exact Subtype.ext (rayWord_zero u k i)
  · have heq : rayWord u k i m = rayWord u k j n := congrArg Subtype.val hmn
    by_cases hm : m = 0
    · subst hm
      exact Subtype.ext (rayWord_zero u k i)
    by_cases hn : n = 0
    · subst hn
      exact Subtype.ext (heq.trans (rayWord_zero u k j))
    exact absurd heq (rayWord_ne hij hm hn)

/-! ### The rays in the sample tree -/

variable {χ : Word → Bool}

/-- **`thm:three-rays` for the sample tree.**  On `Ω₀` every chain terminates,
so the leftmost chain reaches a split `u`, and the chain below the second child
of `u` reaches a further split.  The two children of that split carry two rays,
and the third climbs past `u` and descends its other child. -/
theorem not_quasiIsometric_rayGraph_inTree (hχ : Chains χ) :
    ¬ QuasiIsometric (wordGraph (InTree χ)) rayGraph := by
  set u : Word := List.replicate (kappa hχ [] - 1) false with hu_def
  have hu_split : χ u = true := by
    have h := kappa_spec hχ []
    rwa [List.nil_append] at h
  have hu_mem : InTree χ u := by
    have h := ray_mem_tree (InTree.root (χ := χ)) (kappa hχ [] - 1)
    rwa [List.nil_append] at h
  have hw_mem : InTree χ (u ++ [true]) := InTree.two hu_mem hu_split
  set k : ℕ := kappa hχ (u ++ [true]) - 1 with hk_def
  have hv_split : χ (splitV u k) = true := kappa_spec hχ (u ++ [true])
  have hv_mem : InTree χ (splitV u k) := ray_mem_tree hw_mem k
  exact not_quasiIsometric_rayGraph_of_splits (prefixClosed_inTree χ)
    (fun j => ray_mem_tree hu_mem j) (fun j => ray_mem_tree hv_mem j)
    (fun j => ray_mem_tree (InTree.two hv_mem hv_split) j)

/-! ### `thm:converse` -/

/-- **`thm:converse` on the constructed space.**  Almost surely the sample tree
of the chain regime is quasi-isometric neither to the binary tree nor to the
ray, both halves stated for the graph of `sec:words`. -/
theorem converse_ae {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∀ᵐ ω ∂(chainMeasure ht ht1.le),
      ¬ QuasiIsometric (wordGraph (InTree ω)) (wordGraph fun _ : Word => True)
        ∧ ¬ QuasiIsometric (wordGraph (InTree ω)) rayGraph := by
  have hchains : ∀ᵐ ω ∂(chainMeasure ht ht1.le), Chains ω := by
    rw [ae_iff]
    exact not_chains_null (chainMeasure ht ht1.le)
      (fun v : Word ↦ (BranchingProcess.coord v : (Word → Bool) → Bool)) t
      measurable_chainMeasure_coord (chainMeasure_iIndepFun ht ht1.le)
      (chainMeasure_coord_true ht ht1.le) ht
  filter_upwards [hchains, converse_binary_ae ht ht1] with ω hω hbin
  refine ⟨?_, not_quasiIsometric_rayGraph_inTree hω⟩
  refine not_quasiIsometric_of_not_isQIWith (prefixClosed_inTree ω) prefixClosed_true ?_
  rw [inTree_eq_inAssoc hω]
  exact hbin

end ChainClasses
