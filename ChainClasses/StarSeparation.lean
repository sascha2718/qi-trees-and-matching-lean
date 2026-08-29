/-
The deterministic core of `thm:chain-separation` (`prelims.tex`): a sample carrying an
`L`-star of excess `m` at a vertex far from the root is not the target of a
`D`-quasi-isometry from a sample all of whose sphere counts avoid `m`, once `L` is
large against `D` and `m`.  The probabilistic layer that supplies the stars and the
sphere hypotheses is `ChainSeparationProof.lean`.

The route is the prose's: quasi-geodesic stability enters only in the walk form
`BranchingProcess.exists_between_dist_le`, whose constant is `D` itself, and Step 1
counts the sphere just outside a ball, `|S(w, C₂+1)|`, twice, once as `m + 2` through
the gates of the star's ends and once as `2 + s` with `s` in the branching semigroup.

* `geoPt`, `geoPt_dist`, `geoPt_add`, `geoPt_unique`: the vertex at a prescribed
  distance on the geodesic between two words, with its characterisation by metric
  additivity.
* `med` with `med_add_left`, `med_add_right`, `med_add_outer`: the median of three
  words as the longest pairwise wedge, on all three geodesics.
-/
import ChainClasses.GeneralObstructions

namespace ChainClasses

open SimpleGraph
open BranchingProcess (sample Subtree)

variable {N : ℕ}

/-! ### Prefix and wedge helpers -/

/-- Mutual prefixes are equal. -/
lemma prefix_antisymm {u v : GWord N} (h1 : u <+: v) (h2 : v <+: u) : u = v :=
  h1.eq_of_length (le_antisymm h1.length_le h2.length_le)

/-- The wedge of `w` and `z` is a prefix of every prefix of `w` at least as long. -/
lemma wedge_prefix_take_left {w z : GWord N} {n : ℕ}
    (h : (BranchingProcess.wedge w z).length ≤ n) :
    BranchingProcess.wedge w z <+: w.take n :=
  List.prefix_of_prefix_length_le (BranchingProcess.wedge_prefix_left w z)
    (List.take_prefix n w)
    (by rw [List.length_take]
        exact le_min h (BranchingProcess.wedge_length_le_left w z))

/-- The wedge of `w` and `z` is a prefix of every prefix of `z` at least as long. -/
lemma wedge_prefix_take_right {w z : GWord N} {n : ℕ}
    (h : (BranchingProcess.wedge w z).length ≤ n) :
    BranchingProcess.wedge w z <+: z.take n := by
  rw [BranchingProcess.wedge_comm]
  exact wedge_prefix_take_left (by rwa [BranchingProcess.wedge_comm])

/-- Wedging `w` with a prefix of `z` extending the wedge changes nothing. -/
lemma wedge_take_right {w z : GWord N} {n : ℕ}
    (h : (BranchingProcess.wedge w z).length ≤ n) :
    BranchingProcess.wedge w (z.take n) = BranchingProcess.wedge w z := by
  refine prefix_antisymm ?_ ?_
  · exact BranchingProcess.prefix_wedge_of_prefix
      (BranchingProcess.wedge_prefix_left _ _)
      ((BranchingProcess.wedge_prefix_right w (z.take n)).trans (List.take_prefix n z))
  · exact BranchingProcess.prefix_wedge_of_prefix
      (BranchingProcess.wedge_prefix_left w z) (wedge_prefix_take_right h)

/-! ### The vertex at a prescribed distance on a geodesic -/

/-- The vertex at distance `k` from `w` on the geodesic from `w` to `z`: climb towards
the wedge for the first `|w| - |w ∧ z|` steps, then descend towards `z`. -/
def geoPt (w z : GWord N) (k : ℕ) : GWord N :=
  if k ≤ w.length - (BranchingProcess.wedge w z).length then w.take (w.length - k)
  else z.take ((BranchingProcess.wedge w z).length
    + (k - (w.length - (BranchingProcess.wedge w z).length)))

/-- The distance from `w` to the geodesic vertex is as prescribed. -/
lemma geoPt_dist (w z : GWord N) {k : ℕ} (hk : k ≤ BranchingProcess.treeDist w z) :
    BranchingProcess.treeDist w (geoPt w z k) = k := by
  have hql := BranchingProcess.wedge_length_le_left w z
  have hqr := BranchingProcess.wedge_length_le_right w z
  have hadd := BranchingProcess.treeDist_add w z
  rw [geoPt]
  split_ifs with h
  · rw [BranchingProcess.treeDist_comm,
      BranchingProcess.treeDist_of_prefix (List.take_prefix _ w), List.length_take]
    omega
  · have hwedge : BranchingProcess.wedge w (z.take ((BranchingProcess.wedge w z).length
        + (k - (w.length - (BranchingProcess.wedge w z).length))))
        = BranchingProcess.wedge w z := wedge_take_right (by omega)
    have := BranchingProcess.treeDist_add w
      (z.take ((BranchingProcess.wedge w z).length
        + (k - (w.length - (BranchingProcess.wedge w z).length))))
    rw [hwedge, List.length_take] at this
    omega

/-- The geodesic vertex splits the distance additively. -/
lemma geoPt_add (w z : GWord N) {k : ℕ} (hk : k ≤ BranchingProcess.treeDist w z) :
    BranchingProcess.treeDist w (geoPt w z k)
      + BranchingProcess.treeDist (geoPt w z k) z = BranchingProcess.treeDist w z := by
  have hql := BranchingProcess.wedge_length_le_left w z
  have hqr := BranchingProcess.wedge_length_le_right w z
  have hadd := BranchingProcess.treeDist_add w z
  rw [geoPt_dist w z hk, geoPt]
  split_ifs with h
  · have hpre : BranchingProcess.wedge w z <+: w.take (w.length - k) :=
      wedge_prefix_take_left (by omega)
    have hwedge : BranchingProcess.wedge (w.take (w.length - k)) z
        = BranchingProcess.wedge w z := by
      refine prefix_antisymm ?_ ?_
      · exact BranchingProcess.prefix_wedge_of_prefix
          ((BranchingProcess.wedge_prefix_left (w.take (w.length - k)) z).trans
            (List.take_prefix _ w))
          (BranchingProcess.wedge_prefix_right _ _)
      · exact BranchingProcess.prefix_wedge_of_prefix hpre
          (BranchingProcess.wedge_prefix_right w z)
    have := BranchingProcess.treeDist_add (w.take (w.length - k)) z
    rw [hwedge, List.length_take] at this
    omega
  · rw [BranchingProcess.treeDist_of_prefix (List.take_prefix _ z), List.length_take]
    omega

/-- The geodesic vertex is a prefix of one of the two endpoints. -/
lemma geoPt_prefix (w z : GWord N) (k : ℕ) :
    (∃ n, geoPt w z k = w.take n) ∨ ∃ n, geoPt w z k = z.take n := by
  rw [geoPt]
  split_ifs
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

/-- The geodesic vertex of two vertices of a prefix-closed set lies in the set. -/
lemma geoPt_mem {T : GWord N → Prop} (hT : PrefixClosedN T) {w z : GWord N}
    (hw : T w) (hz : T z) (k : ℕ) : T (geoPt w z k) := by
  rcases geoPt_prefix w z k with ⟨n, hn⟩ | ⟨n, hn⟩
  · rw [hn]; exact hT (List.take_prefix n w) hw
  · rw [hn]; exact hT (List.take_prefix n z) hz

/-- A vertex splitting the distance between `w` and `z` additively is a prefix of `w`
above the wedge or a prefix of `z` above the wedge. -/
lemma prefix_of_dist_add {w z x : GWord N}
    (h : BranchingProcess.treeDist w x + BranchingProcess.treeDist x z
      = BranchingProcess.treeDist w z) :
    (x <+: w ∧ BranchingProcess.wedge w z <+: x)
      ∨ (x <+: z ∧ BranchingProcess.wedge w z <+: x) := by
  have hwx := BranchingProcess.treeDist_add w x
  have hxz := BranchingProcess.treeDist_add x z
  have hwz := BranchingProcess.treeDist_add w z
  have hkey : x.length + (BranchingProcess.wedge w z).length
      = (BranchingProcess.wedge w x).length + (BranchingProcess.wedge x z).length := by
    omega
  rcases List.prefix_or_prefix_of_prefix (BranchingProcess.wedge_prefix_right w x)
    (BranchingProcess.wedge_prefix_left x z) with hp | hp
  · -- `w ∧ x` is the shorter wedge: `x ∧ z = x`, so `x <+: z`
    have h1 : BranchingProcess.wedge w x <+: BranchingProcess.wedge w z :=
      BranchingProcess.prefix_wedge_of_prefix (BranchingProcess.wedge_prefix_left w x)
        (hp.trans (BranchingProcess.wedge_prefix_right x z))
    have h2 : (BranchingProcess.wedge x z).length ≤ x.length :=
      BranchingProcess.wedge_length_le_left x z
    have h3 := h1.length_le
    have h6 : BranchingProcess.wedge x z = x :=
      (BranchingProcess.wedge_prefix_left x z).eq_of_length (by omega)
    have h4 : BranchingProcess.wedge w x = BranchingProcess.wedge w z :=
      h1.eq_of_length (by omega)
    refine Or.inr ⟨?_, ?_⟩
    · exact h6 ▸ BranchingProcess.wedge_prefix_right x z
    · exact h4 ▸ BranchingProcess.wedge_prefix_right w x
  · -- `x ∧ z` is the shorter wedge: `w ∧ x = x`, so `x <+: w`
    have h1 : BranchingProcess.wedge x z <+: BranchingProcess.wedge w z :=
      BranchingProcess.prefix_wedge_of_prefix
        (hp.trans (BranchingProcess.wedge_prefix_left w x))
        (BranchingProcess.wedge_prefix_right x z)
    have h2 : (BranchingProcess.wedge w x).length ≤ x.length :=
      BranchingProcess.wedge_length_le_right w x
    have h3 := h1.length_le
    have h6 : BranchingProcess.wedge w x = x :=
      (BranchingProcess.wedge_prefix_right w x).eq_of_length (by omega)
    have h7 : BranchingProcess.wedge x z = BranchingProcess.wedge w z :=
      h1.eq_of_length (by omega)
    refine Or.inl ⟨?_, ?_⟩
    · exact h6 ▸ BranchingProcess.wedge_prefix_left w x
    · exact h7 ▸ BranchingProcess.wedge_prefix_left x z

/-- **Uniqueness of the geodesic vertex**: a vertex splitting the distance between `w`
and `z` additively is the geodesic vertex at its distance from `w`. -/
theorem geoPt_unique {w z x : GWord N}
    (h : BranchingProcess.treeDist w x + BranchingProcess.treeDist x z
      = BranchingProcess.treeDist w z) :
    x = geoPt w z (BranchingProcess.treeDist w x) := by
  have hql := BranchingProcess.wedge_length_le_left w z
  have hqr := BranchingProcess.wedge_length_le_right w z
  rcases prefix_of_dist_add h with ⟨hxw, hqx⟩ | ⟨hxz', hqx⟩
  · -- `x` on the climbing part
    have hxle := hxw.length_le
    have hqle := hqx.length_le
    have hd : BranchingProcess.treeDist w x = w.length - x.length := by
      rw [BranchingProcess.treeDist_comm, BranchingProcess.treeDist_of_prefix hxw]
    rw [hd, geoPt, if_pos (by omega)]
    have hxx : w.length - (w.length - x.length) = x.length := by omega
    rw [hxx]
    exact List.prefix_iff_eq_take.mp hxw
  · -- `x` on the descending part
    have hxle := hxz'.length_le
    have hqle := hqx.length_le
    have hwx' : BranchingProcess.wedge w x = BranchingProcess.wedge w z := by
      refine prefix_antisymm ?_ ?_
      · exact BranchingProcess.prefix_wedge_of_prefix
          (BranchingProcess.wedge_prefix_left w x)
          ((BranchingProcess.wedge_prefix_right w x).trans hxz')
      · exact BranchingProcess.prefix_wedge_of_prefix
          (BranchingProcess.wedge_prefix_left w z) hqx
    have hd : BranchingProcess.treeDist w x
        = w.length + x.length - 2 * (BranchingProcess.wedge w z).length := by
      have := BranchingProcess.treeDist_add w x
      rw [hwx'] at this
      omega
    by_cases hcase : BranchingProcess.treeDist w x
        ≤ w.length - (BranchingProcess.wedge w z).length
    · -- forces `x = wedge w z`, which is also a climbing vertex
      have hxlen : x.length = (BranchingProcess.wedge w z).length := by omega
      have hxeq : x = BranchingProcess.wedge w z := (hqx.eq_of_length hxlen.symm).symm
      rw [geoPt, if_pos hcase, hd]
      have hxx : w.length - (w.length + x.length
          - 2 * (BranchingProcess.wedge w z).length) = x.length := by omega
      nth_rewrite 1 [hxeq]
      rw [hxx, hxeq]
      exact List.prefix_iff_eq_take.mp (BranchingProcess.wedge_prefix_left w z)
    · rw [geoPt, if_neg hcase]
      have hxx : (BranchingProcess.wedge w z).length + (BranchingProcess.treeDist w x
          - (w.length - (BranchingProcess.wedge w z).length)) = x.length := by omega
      rw [hxx]
      exact List.prefix_iff_eq_take.mp hxz'

/-- Geodesics compose: the vertex at distance `k` towards an intermediate vertex is
the vertex at distance `k` towards the far endpoint. -/
lemma geoPt_comp {w q z : GWord N}
    (hq : BranchingProcess.treeDist w q + BranchingProcess.treeDist q z
      = BranchingProcess.treeDist w z) {k : ℕ}
    (hk : k ≤ BranchingProcess.treeDist w q) :
    geoPt w z k = geoPt w q k := by
  have h1 := geoPt_dist w q hk
  have h2 := geoPt_add w q hk
  have h3 : BranchingProcess.treeDist w (geoPt w q k)
      + BranchingProcess.treeDist (geoPt w q k) z = BranchingProcess.treeDist w z := by
    have t1 := BranchingProcess.treeDist_triangle w (geoPt w q k) z
    have t2 := BranchingProcess.treeDist_triangle (geoPt w q k) q z
    omega
  have h4 := geoPt_unique h3
  rw [h1] at h4
  exact h4.symm

/-! ### The median of three words -/

/-- The median of three words: the longest of the three pairwise wedges. -/
def med (w a b : GWord N) : GWord N :=
  if (BranchingProcess.wedge w a).length < (BranchingProcess.wedge w b).length then
    BranchingProcess.wedge w b
  else if (BranchingProcess.wedge w b).length < (BranchingProcess.wedge w a).length then
    BranchingProcess.wedge w a
  else BranchingProcess.wedge a b

/-- The three additivities of the median in the asymmetric case `|w ∧ a| < |w ∧ b|`,
where the median is `w ∧ b`. -/
private lemma med_spec_aux {w a b : GWord N}
    (hlt : (BranchingProcess.wedge w a).length < (BranchingProcess.wedge w b).length) :
    (BranchingProcess.treeDist w (BranchingProcess.wedge w b)
        + BranchingProcess.treeDist (BranchingProcess.wedge w b) a
        = BranchingProcess.treeDist w a)
    ∧ (BranchingProcess.treeDist w (BranchingProcess.wedge w b)
        + BranchingProcess.treeDist (BranchingProcess.wedge w b) b
        = BranchingProcess.treeDist w b)
    ∧ (BranchingProcess.treeDist a (BranchingProcess.wedge w b)
        + BranchingProcess.treeDist (BranchingProcess.wedge w b) b
        = BranchingProcess.treeDist a b) := by
  -- `w ∧ a` is a proper prefix of `w ∧ b`
  have hqaqb : BranchingProcess.wedge w a <+: BranchingProcess.wedge w b := by
    rcases List.prefix_or_prefix_of_prefix (BranchingProcess.wedge_prefix_left w a)
      (BranchingProcess.wedge_prefix_left w b) with hp | hp
    · exact hp
    · exact absurd hp.length_le (by omega)
  -- the wedge of `a` and `b` is `w ∧ a`
  have hab : BranchingProcess.wedge a b = BranchingProcess.wedge w a := by
    refine prefix_antisymm ?_ ?_
    · rcases List.prefix_or_prefix_of_prefix (BranchingProcess.wedge_prefix_right a b)
        (BranchingProcess.wedge_prefix_right w b) with hp | hp
      · exact BranchingProcess.prefix_wedge_of_prefix
          (hp.trans (BranchingProcess.wedge_prefix_left w b))
          (BranchingProcess.wedge_prefix_left a b)
      · have hcon : BranchingProcess.wedge w b <+: BranchingProcess.wedge w a :=
          BranchingProcess.prefix_wedge_of_prefix
            (BranchingProcess.wedge_prefix_left w b)
            (hp.trans (BranchingProcess.wedge_prefix_left a b))
        exact absurd hcon.length_le (by omega)
    · exact BranchingProcess.prefix_wedge_of_prefix
        (BranchingProcess.wedge_prefix_right w a)
        (hqaqb.trans (BranchingProcess.wedge_prefix_right w b))
  -- the wedge of `w ∧ b` and `a` is `w ∧ a`
  have hqba : BranchingProcess.wedge (BranchingProcess.wedge w b) a
      = BranchingProcess.wedge w a := by
    refine prefix_antisymm ?_ ?_
    · exact BranchingProcess.prefix_wedge_of_prefix
        ((BranchingProcess.wedge_prefix_left (BranchingProcess.wedge w b) a).trans
          (BranchingProcess.wedge_prefix_left w b))
        (BranchingProcess.wedge_prefix_right (BranchingProcess.wedge w b) a)
    · exact BranchingProcess.prefix_wedge_of_prefix hqaqb
        (BranchingProcess.wedge_prefix_right w a)
  have hwa := BranchingProcess.treeDist_add w a
  have hwb := BranchingProcess.treeDist_add w b
  have hab' := BranchingProcess.treeDist_add a b
  have hablen : (BranchingProcess.wedge a b).length
      = (BranchingProcess.wedge w a).length := by rw [hab]
  have hqbw : BranchingProcess.treeDist w (BranchingProcess.wedge w b)
      = w.length - (BranchingProcess.wedge w b).length := by
    rw [BranchingProcess.treeDist_comm,
      BranchingProcess.treeDist_of_prefix (BranchingProcess.wedge_prefix_left w b)]
  have hqbb : BranchingProcess.treeDist (BranchingProcess.wedge w b) b
      = b.length - (BranchingProcess.wedge w b).length :=
    BranchingProcess.treeDist_of_prefix (BranchingProcess.wedge_prefix_right w b)
  have hqba' := BranchingProcess.treeDist_add (BranchingProcess.wedge w b) a
  rw [hqba] at hqba'
  have hqab := BranchingProcess.treeDist_comm a (BranchingProcess.wedge w b)
  have h1 := BranchingProcess.wedge_length_le_left w a
  have h2 := BranchingProcess.wedge_length_le_right w a
  have h3 := BranchingProcess.wedge_length_le_left w b
  have h4 := BranchingProcess.wedge_length_le_right w b
  have h5 := hqaqb.length_le
  refine ⟨by omega, by omega, by omega⟩

/-- The median splits the distance from `w` to `a`. -/
lemma med_add_left (w a b : GWord N) :
    BranchingProcess.treeDist w (med w a b) + BranchingProcess.treeDist (med w a b) a
      = BranchingProcess.treeDist w a := by
  rw [med]
  split_ifs with h1 h2
  · exact (med_spec_aux h1).1
  · exact (med_spec_aux h2).2.1
  · -- equal wedge lengths: the median is `a ∧ b`
    have heq : BranchingProcess.wedge w a = BranchingProcess.wedge w b := by
      rcases List.prefix_or_prefix_of_prefix (BranchingProcess.wedge_prefix_left w a)
        (BranchingProcess.wedge_prefix_left w b) with hp | hp
      · exact hp.eq_of_length (by omega)
      · exact (hp.eq_of_length (by omega)).symm
    have hq : BranchingProcess.wedge w a <+: BranchingProcess.wedge a b :=
      BranchingProcess.prefix_wedge_of_prefix (BranchingProcess.wedge_prefix_right w a)
        (heq ▸ BranchingProcess.wedge_prefix_right w b)
    have hwm : BranchingProcess.wedge w (BranchingProcess.wedge a b)
        = BranchingProcess.wedge w a := by
      refine prefix_antisymm ?_ ?_
      · exact BranchingProcess.prefix_wedge_of_prefix
          (BranchingProcess.wedge_prefix_left w (BranchingProcess.wedge a b))
          ((BranchingProcess.wedge_prefix_right w (BranchingProcess.wedge a b)).trans
            (BranchingProcess.wedge_prefix_left a b))
      · exact BranchingProcess.prefix_wedge_of_prefix
          (BranchingProcess.wedge_prefix_left w a) hq
    have hd1 := BranchingProcess.treeDist_add w (BranchingProcess.wedge a b)
    rw [hwm] at hd1
    have hd2 : BranchingProcess.treeDist (BranchingProcess.wedge a b) a
        = a.length - (BranchingProcess.wedge a b).length :=
      BranchingProcess.treeDist_of_prefix (BranchingProcess.wedge_prefix_left a b)
    have hwa := BranchingProcess.treeDist_add w a
    have h1' := BranchingProcess.wedge_length_le_left w a
    have h2' := BranchingProcess.wedge_length_le_right w a
    have h3' := hq.length_le
    have h4' := BranchingProcess.wedge_length_le_left a b
    omega

/-- The median splits the distance from `w` to `b`. -/
lemma med_add_right (w a b : GWord N) :
    BranchingProcess.treeDist w (med w a b) + BranchingProcess.treeDist (med w a b) b
      = BranchingProcess.treeDist w b := by
  rw [med]
  split_ifs with h1 h2
  · exact (med_spec_aux h1).2.1
  · exact (med_spec_aux h2).1
  · have heq : BranchingProcess.wedge w a = BranchingProcess.wedge w b := by
      rcases List.prefix_or_prefix_of_prefix (BranchingProcess.wedge_prefix_left w a)
        (BranchingProcess.wedge_prefix_left w b) with hp | hp
      · exact hp.eq_of_length (by omega)
      · exact (hp.eq_of_length (by omega)).symm
    have hq : BranchingProcess.wedge w b <+: BranchingProcess.wedge a b :=
      BranchingProcess.prefix_wedge_of_prefix
        (heq ▸ BranchingProcess.wedge_prefix_right w a)
        (BranchingProcess.wedge_prefix_right w b)
    have hwm : BranchingProcess.wedge w (BranchingProcess.wedge a b)
        = BranchingProcess.wedge w b := by
      refine prefix_antisymm ?_ ?_
      · exact BranchingProcess.prefix_wedge_of_prefix
          (BranchingProcess.wedge_prefix_left w (BranchingProcess.wedge a b))
          ((BranchingProcess.wedge_prefix_right w (BranchingProcess.wedge a b)).trans
            (BranchingProcess.wedge_prefix_right a b))
      · exact BranchingProcess.prefix_wedge_of_prefix
          (BranchingProcess.wedge_prefix_left w b) hq
    have hd1 := BranchingProcess.treeDist_add w (BranchingProcess.wedge a b)
    rw [hwm] at hd1
    have hd2 : BranchingProcess.treeDist (BranchingProcess.wedge a b) b
        = b.length - (BranchingProcess.wedge a b).length :=
      BranchingProcess.treeDist_of_prefix (BranchingProcess.wedge_prefix_right a b)
    have hwb := BranchingProcess.treeDist_add w b
    have h1' := BranchingProcess.wedge_length_le_left w b
    have h2' := BranchingProcess.wedge_length_le_right w b
    have h3' := hq.length_le
    have h4' := BranchingProcess.wedge_length_le_right a b
    omega

/-- The median splits the distance from `a` to `b`. -/
lemma med_add_outer (w a b : GWord N) :
    BranchingProcess.treeDist a (med w a b) + BranchingProcess.treeDist (med w a b) b
      = BranchingProcess.treeDist a b := by
  rw [med]
  split_ifs with h1 h2
  · exact (med_spec_aux h1).2.2
  · have h := (med_spec_aux h2).2.2
    have hc1 := BranchingProcess.treeDist_comm b (BranchingProcess.wedge w a)
    have hc2 := BranchingProcess.treeDist_comm a (BranchingProcess.wedge w a)
    have hc3 := BranchingProcess.treeDist_comm a b
    omega
  · have hd1 : BranchingProcess.treeDist a (BranchingProcess.wedge a b)
        = a.length - (BranchingProcess.wedge a b).length := by
      rw [BranchingProcess.treeDist_comm]
      exact BranchingProcess.treeDist_of_prefix (BranchingProcess.wedge_prefix_left a b)
    have hd2 : BranchingProcess.treeDist (BranchingProcess.wedge a b) b
        = b.length - (BranchingProcess.wedge a b).length :=
      BranchingProcess.treeDist_of_prefix (BranchingProcess.wedge_prefix_right a b)
    have hab := BranchingProcess.treeDist_add a b
    have h4' := BranchingProcess.wedge_length_le_left a b
    have h5' := BranchingProcess.wedge_length_le_right a b
    omega

/-- **The Gromov product bound for common geodesic vertices**: a vertex on the
geodesics from `w` to `a` and from `w` to `b` sits within the Gromov product. -/
lemma two_mul_dist_le_of_dist_add {w a b x : GWord N}
    (ha : BranchingProcess.treeDist w x + BranchingProcess.treeDist x a
      = BranchingProcess.treeDist w a)
    (hb : BranchingProcess.treeDist w x + BranchingProcess.treeDist x b
      = BranchingProcess.treeDist w b) :
    2 * BranchingProcess.treeDist w x + BranchingProcess.treeDist a b
      ≤ BranchingProcess.treeDist w a + BranchingProcess.treeDist w b := by
  have htri := BranchingProcess.treeDist_triangle a x b
  have hc := BranchingProcess.treeDist_comm a x
  omega

/-! ### Walks, betweenness and stability over `wordGraphN` -/

section Graph

variable {T : GWord N → Prop}

/-- Metric additivity produces betweenness in the graph of a prefix-closed set. -/
lemma betweenN (hT : PrefixClosedN T) {x y z : {w : GWord N // T w}}
    (h : BranchingProcess.treeDist x.1 y.1 + BranchingProcess.treeDist y.1 z.1
      = BranchingProcess.treeDist x.1 z.1) :
    BranchingProcess.Between (wordGraphN T) x y z := by
  rw [BranchingProcess.between_iff_dist_add (wordGraphN_isTree hT ⟨x⟩)]
  rw [wordGraphN_dist hT, wordGraphN_dist hT, wordGraphN_dist hT]
  exact h

/-- A vertex between `w` and `z` is between `w` and everything close to `z` but far
from the vertex. -/
lemma between_of_close {V : Type*} {G : SimpleGraph V} (hG : G.IsTree) {w g z x : V}
    {E : ℕ} (hb : BranchingProcess.Between G w g z) (hclose : G.dist z x ≤ E)
    (hfar : E < G.dist g z) : BranchingProcess.Between G w g x := by
  rcases BranchingProcess.between_or hG hb x with h | h
  · exact h
  · have hadd := h.dist_add hG.connected
    rw [SimpleGraph.dist_comm (u := x) (v := g)] at hadd
    have hxz : G.dist x z ≤ E := by rwa [SimpleGraph.dist_comm]
    omega

/-- Along any walk the distance from the start grows by at most one per step. -/
lemma treeDist_getVert_le {u v : {w : GWord N // T w}} (p : (wordGraphN T).Walk u v) :
    ∀ i, BranchingProcess.treeDist u.1 (p.getVert i).1 ≤ i := by
  induction p with
  | nil => intro i; simp
  | @cons a c d hac q ih =>
      intro i
      cases i with
      | zero => simp
      | succ i =>
          have h1 : BranchingProcess.treeDist a.1 c.1 = 1 := hac
          have h2 := ih i
          have htri := BranchingProcess.treeDist_triangle a.1 c.1 ((q.getVert i).1)
          rw [SimpleGraph.Walk.getVert_cons_succ]
          omega

/-- Along any walk the distance to the end is bounded by the remaining length. -/
lemma treeDist_getVert_le' {u v : {w : GWord N // T w}} (p : (wordGraphN T).Walk u v) :
    ∀ i, BranchingProcess.treeDist (p.getVert i).1 v.1 ≤ p.length - i := by
  induction p with
  | nil => intro i; simp
  | @cons a c d hac q ih =>
      intro i
      cases i with
      | zero =>
          simp only [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.length_cons]
          have h1 : BranchingProcess.treeDist a.1 c.1 = 1 := hac
          have h2 := treeDistN_le_walk_length q
          have htri := BranchingProcess.treeDist_triangle a.1 c.1 d.1
          omega
      | succ i =>
          have h2 := ih i
          rw [SimpleGraph.Walk.getVert_cons_succ]
          simp only [SimpleGraph.Walk.length_cons]
          omega

/-- **A vertex of a distance-realising walk is the geodesic vertex at its index.** -/
lemma getVert_eq_geoPt {u v : {w : GWord N // T w}} {p : (wordGraphN T).Walk u v}
    (hlen : p.length = BranchingProcess.treeDist u.1 v.1) {i : ℕ} (hi : i ≤ p.length) :
    (p.getVert i).1 = geoPt u.1 v.1 i
      ∧ BranchingProcess.treeDist u.1 (p.getVert i).1 = i
      ∧ BranchingProcess.treeDist u.1 (p.getVert i).1
          + BranchingProcess.treeDist (p.getVert i).1 v.1
          = BranchingProcess.treeDist u.1 v.1 := by
  have h1 := treeDist_getVert_le p i
  have h2 := treeDist_getVert_le' p i
  have htri := BranchingProcess.treeDist_triangle u.1 ((p.getVert i).1) v.1
  have hd : BranchingProcess.treeDist u.1 (p.getVert i).1 = i := by omega
  have hadd : BranchingProcess.treeDist u.1 (p.getVert i).1
      + BranchingProcess.treeDist (p.getVert i).1 v.1
      = BranchingProcess.treeDist u.1 v.1 := by omega
  refine ⟨?_, hd, hadd⟩
  have hu := geoPt_unique hadd
  rwa [hd] at hu

end Graph

/-! ### Extension beyond a vertex, away from a base point -/

/-- Wedging with an extension of `g` changes nothing when `g` does not sit above
`w`. -/
lemma wedge_append_of_not_prefix {w g : GWord N} (h : ¬ g <+: w) (e : GWord N) :
    BranchingProcess.wedge w (g ++ e) = BranchingProcess.wedge w g := by
  refine prefix_antisymm ?_ ?_
  · rcases List.prefix_or_prefix_of_prefix
      (BranchingProcess.wedge_prefix_right w (g ++ e)) (List.prefix_append g e)
      with hp | hp
    · exact BranchingProcess.prefix_wedge_of_prefix
        (BranchingProcess.wedge_prefix_left w (g ++ e)) hp
    · exact absurd (hp.trans (BranchingProcess.wedge_prefix_left w (g ++ e))) h
  · exact BranchingProcess.prefix_wedge_of_prefix
      (BranchingProcess.wedge_prefix_left w g)
      ((BranchingProcess.wedge_prefix_right w g).trans (List.prefix_append g e))

/-- In a sample all of whose offspring counts are positive, descending by first
children stays in the sample. -/
lemma append_replicate_mem_sample {N' : ℕ} {c : GWord N' → ℕ} (hN : 0 < N')
    (hpos : ∀ v, 1 ≤ c v) {g : GWord N'} (hg : g ∈ sample c) :
    ∀ k, g ++ List.replicate k (⟨0, hN⟩ : Fin N') ∈ sample c := by
  intro k
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      rw [List.replicate_succ', ← List.append_assoc]
      exact BranchingProcess.mem_sample_append_singleton.mpr ⟨ih, hpos _⟩

/-- **Extension beyond a sphere vertex.** In a sample without leaves, any vertex at
distance `ρ` from `w` has points behind it at every distance up to the depth of `w`
and beyond. -/
lemma exists_beyond {N' : ℕ} {c : GWord N' → ℕ} (hN : 0 < N') (hpos : ∀ v, 1 ≤ c v)
    {w g : GWord N'} (hw : w ∈ sample c) (hg : g ∈ sample c) {ρ ρ' : ℕ}
    (hd : BranchingProcess.treeDist w g = ρ) (hle : ρ ≤ ρ') (hdepth : ρ' ≤ w.length) :
    ∃ z ∈ sample c, BranchingProcess.treeDist w z = ρ'
      ∧ BranchingProcess.treeDist w g + BranchingProcess.treeDist g z
        = BranchingProcess.treeDist w z := by
  by_cases hcase : g <+: w
  · refine ⟨w.take (w.length - ρ'), ?_, ?_, ?_⟩
    · exact BranchingProcess.Subtree.mem_of_prefix (List.take_prefix _ w) hw
    · rw [BranchingProcess.treeDist_comm,
        BranchingProcess.treeDist_of_prefix (List.take_prefix _ w), List.length_take]
      omega
    · have hglen : g.length = w.length - ρ := by
        have := hcase.length_le
        rw [BranchingProcess.treeDist_comm, BranchingProcess.treeDist_of_prefix hcase]
          at hd
        omega
      have hzg : w.take (w.length - ρ') <+: g := by
        refine List.prefix_of_prefix_length_le (List.take_prefix _ w) hcase ?_
        rw [List.length_take]
        omega
      have h1 : BranchingProcess.treeDist g (w.take (w.length - ρ'))
          = g.length - (w.take (w.length - ρ')).length := by
        rw [BranchingProcess.treeDist_comm]
        exact BranchingProcess.treeDist_of_prefix hzg
      have h2 : BranchingProcess.treeDist w (w.take (w.length - ρ'))
          = w.length - (w.take (w.length - ρ')).length := by
        rw [BranchingProcess.treeDist_comm]
        exact BranchingProcess.treeDist_of_prefix (List.take_prefix _ w)
      rw [hd, h1, h2, List.length_take]
      omega
  · refine ⟨g ++ List.replicate (ρ' - ρ) (⟨0, hN⟩ : Fin N'),
      append_replicate_mem_sample hN hpos hg _, ?_, ?_⟩
    · have hwedge := wedge_append_of_not_prefix hcase
        (List.replicate (ρ' - ρ) (⟨0, hN⟩ : Fin N'))
      have h1 := BranchingProcess.treeDist_add w
        (g ++ List.replicate (ρ' - ρ) (⟨0, hN⟩ : Fin N'))
      have h2 := BranchingProcess.treeDist_add w g
      rw [hwedge] at h1
      rw [List.length_append, List.length_replicate] at h1
      omega
    · have hwedge := wedge_append_of_not_prefix hcase
        (List.replicate (ρ' - ρ) (⟨0, hN⟩ : Fin N'))
      have h1 := BranchingProcess.treeDist_add w
        (g ++ List.replicate (ρ' - ρ) (⟨0, hN⟩ : Fin N'))
      have h2 := BranchingProcess.treeDist_add w g
      have h3 : BranchingProcess.treeDist g
          (g ++ List.replicate (ρ' - ρ) (⟨0, hN⟩ : Fin N')) = ρ' - ρ := by
        rw [BranchingProcess.treeDist_of_prefix (List.prefix_append _ _)]
        rw [List.length_append, List.length_replicate]
        omega
      rw [hwedge] at h1
      rw [List.length_append, List.length_replicate] at h1
      omega

/-! ### Spheres of a sample as finite sets -/

section Sphere

variable {N' : ℕ} {c : GWord N' → ℕ}

/-- The words of length at most `n` over `Fin N'`, as a finite set. -/
def allWordsN (N' : ℕ) : ℕ → Finset (GWord N')
  | 0 => {[]}
  | n + 1 => allWordsN N' n ∪ (allWordsN N' n).biUnion
      (fun p => Finset.univ.image (fun j : Fin N' => p ++ [j]))

lemma mem_allWordsN {n : ℕ} {x : GWord N'} : x ∈ allWordsN N' n ↔ x.length ≤ n := by
  induction n generalizing x with
  | zero =>
      simp only [allWordsN, Finset.mem_singleton, Nat.le_zero, List.length_eq_zero_iff]
  | succ n ih =>
      simp only [allWordsN, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_univ, true_and, ih]
      constructor
      · rintro (h | ⟨p, hp, j, rfl⟩)
        · omega
        · simp only [List.length_append, List.length_singleton]
          omega
      · intro h
        by_cases hn : x.length ≤ n
        · exact Or.inl hn
        · rcases List.eq_nil_or_concat x with rfl | ⟨p, j, rfl⟩
          · simp at hn
          · refine Or.inr ⟨p, ?_, j, (List.concat_eq_append (as := p) (a := j)).symm⟩
            simp only [List.concat_eq_append, List.length_append,
              List.length_singleton] at h
            omega

/-- The sphere of radius `ρ` around `w` in the sample of `c`, as a finite set. -/
noncomputable def sphereFinset (c : GWord N' → ℕ) (w : GWord N') (ρ : ℕ) :
    Finset (GWord N') := by
  classical
  exact (allWordsN N' (w.length + ρ)).filter
    (fun x => x ∈ sample c ∧ BranchingProcess.treeDist w x = ρ)

lemma mem_sphereFinset {w x : GWord N'} {ρ : ℕ} :
    x ∈ sphereFinset c w ρ ↔ x ∈ sample c ∧ BranchingProcess.treeDist w x = ρ := by
  rw [sphereFinset]
  classical
  rw [Finset.mem_filter]
  constructor
  · tauto
  · rintro ⟨hx, hd⟩
    refine ⟨mem_allWordsN.mpr ?_, hx, hd⟩
    have h1 := BranchingProcess.treeDist_add w x
    have h2 := BranchingProcess.wedge_length_le_left w x
    omega

/-! #### Adjacency and the vertex towards the base point -/

/-- Appending a letter that does not run along `w` increases the distance to `w`. -/
lemma dist_append_of_not_prefix {w x : GWord N'} {j : Fin N'}
    (h : ¬ x ++ [j] <+: w) :
    BranchingProcess.treeDist w (x ++ [j]) = BranchingProcess.treeDist w x + 1 := by
  by_cases hx : x <+: w
  · -- the wedge with `x ++ [j]` is `x`
    have hwedge : BranchingProcess.wedge w (x ++ [j]) = x := by
      refine prefix_antisymm ?_ ?_
      · rcases List.prefix_or_prefix_of_prefix
          (BranchingProcess.wedge_prefix_right w (x ++ [j]))
          (List.prefix_append x [j]) with hp | hp
        · exact hp
        · have hle := (BranchingProcess.wedge_prefix_right w (x ++ [j])).length_le
          simp only [List.length_append, List.length_singleton] at hle
          rcases lt_or_eq_of_le hle with hlt | heq
          · have hplen := hp.length_le
            have hxe : x = BranchingProcess.wedge w (x ++ [j]) :=
              hp.eq_of_length (by omega)
            rw [← hxe]
          · have hfull : BranchingProcess.wedge w (x ++ [j]) = x ++ [j] :=
              (BranchingProcess.wedge_prefix_right w (x ++ [j])).eq_of_length
                (by simp [heq])
            exact absurd (hfull ▸ BranchingProcess.wedge_prefix_left w (x ++ [j])) h
      · exact BranchingProcess.prefix_wedge_of_prefix hx (List.prefix_append x [j])
    have h1 := BranchingProcess.treeDist_add w (x ++ [j])
    rw [hwedge] at h1
    have h2 : BranchingProcess.treeDist w x = w.length - x.length := by
      rw [BranchingProcess.treeDist_comm, BranchingProcess.treeDist_of_prefix hx]
    have h3 := hx.length_le
    simp only [List.length_append, List.length_singleton] at h1
    omega
  · have hwedge := wedge_append_of_not_prefix hx [j]
    have h1 := BranchingProcess.treeDist_add w (x ++ [j])
    have h2 := BranchingProcess.treeDist_add w x
    rw [hwedge] at h1
    simp only [List.length_append, List.length_singleton] at h1
    omega

/-- Appending a letter that runs along `w` decreases the distance to `w`. -/
lemma dist_append_of_prefix {w x : GWord N'} {j : Fin N'} (h : x ++ [j] <+: w) :
    BranchingProcess.treeDist w (x ++ [j]) + 1 = BranchingProcess.treeDist w x := by
  have hx : x <+: w := (List.prefix_append x [j]).trans h
  have h1 : BranchingProcess.treeDist w (x ++ [j]) = w.length - (x.length + 1) := by
    rw [BranchingProcess.treeDist_comm, BranchingProcess.treeDist_of_prefix h]
    simp
  have h2 : BranchingProcess.treeDist w x = w.length - x.length := by
    rw [BranchingProcess.treeDist_comm, BranchingProcess.treeDist_of_prefix hx]
  have h3 := h.length_le
  simp only [List.length_append, List.length_singleton] at h3
  omega

/-- The vertex adjacent to `x` in the direction of `w`: the next vertex along `w` when
`x` sits above `w`, the parent otherwise. -/
def twd (w x : GWord N') : GWord N' :=
  if x <+: w then w.take (x.length + 1) else x.dropLast

/-- The parent decomposition of a nonempty word. -/
lemma eq_dropLast_append {x : GWord N'} (hx : x ≠ []) :
    ∃ j : Fin N', x = x.dropLast ++ [j] := by
  rcases List.eq_nil_or_concat x with rfl | ⟨p, j, rfl⟩
  · exact absurd rfl hx
  · exact ⟨j, by simp⟩

/-- The toward vertex is adjacent and one step closer. -/
lemma twd_spec {w x : GWord N'} (hxw : x ≠ w) (hx : x ≠ [] ∨ x <+: w) :
    BranchingProcess.treeDist x (twd w x) = 1
      ∧ BranchingProcess.treeDist w (twd w x) + 1 = BranchingProcess.treeDist w x := by
  rw [twd]
  split_ifs with hp
  · -- along `w`
    have hlt : x.length < w.length := by
      rcases lt_or_eq_of_le hp.length_le with h | h
      · exact h
      · exact absurd (hp.eq_of_length h) hxw
    have hxx : x <+: w.take (x.length + 1) :=
      List.prefix_of_prefix_length_le hp (List.take_prefix _ w)
        (by rw [List.length_take]; omega)
    constructor
    · rw [BranchingProcess.treeDist_of_prefix hxx, List.length_take]
      omega
    · have h1 : BranchingProcess.treeDist w (w.take (x.length + 1))
          = w.length - (x.length + 1) := by
        rw [BranchingProcess.treeDist_comm,
          BranchingProcess.treeDist_of_prefix (List.take_prefix _ w), List.length_take]
        omega
      have h2 : BranchingProcess.treeDist w x = w.length - x.length := by
        rw [BranchingProcess.treeDist_comm, BranchingProcess.treeDist_of_prefix hp]
      omega
  · -- the parent
    have hne : x ≠ [] := by
      rcases hx with h | h
      · exact h
      · exact absurd h hp
    obtain ⟨j, hj⟩ := eq_dropLast_append hne
    constructor
    · rw [BranchingProcess.treeDist_comm]
      nth_rewrite 2 [hj]
      exact BranchingProcess.treeDist_append_singleton x.dropLast j
    · have h1 : ¬ x.dropLast ++ [j] <+: w := by rwa [← hj]
      have := dist_append_of_not_prefix h1
      rw [← hj] at this
      omega

/-- **Uniqueness of the toward vertex**: an adjacent vertex one step closer to `w` is
the toward vertex. -/
lemma eq_twd {w x y : GWord N'}
    (hadj : BranchingProcess.treeDist x y = 1)
    (hd : BranchingProcess.treeDist w y + 1 = BranchingProcess.treeDist w x) :
    y = twd w x := by
  rcases treeDistN_eq_one_iff.mp hadj with ⟨j, rfl⟩ | ⟨j, hj⟩
  · -- `y` is a child of `x`
    by_cases hp : x ++ [j] <+: w
    · have hxp : x <+: w := (List.prefix_append x [j]).trans hp
      rw [twd, if_pos hxp]
      have := List.prefix_iff_eq_take.mp hp
      rw [this]
      congr 1
      simp
    · have := dist_append_of_not_prefix hp
      omega
  · -- `x` is a child of `y`
    by_cases hp : x <+: w
    · have := dist_append_of_prefix (hj ▸ hp)
      rw [← hj] at this
      omega
    · rw [twd, if_neg hp, hj]
      simp
/-! #### Neighbour sets and the sphere recursion -/

/-- The children of `x` in the sample of `c`, as a finite set. -/
def childFinset (c : GWord N' → ℕ) (x : GWord N') : Finset (GWord N') :=
  ((Finset.univ : Finset (Fin N')).filter (fun j : Fin N' => (j : ℕ) < c x)).image
    (fun j : Fin N' => x ++ [j])

/-- The parent of `x`, as a finite set. -/
def parentFinset (x : GWord N') : Finset (GWord N') :=
  if x = [] then ∅ else {x.dropLast}

/-- The neighbours of `x` in the sample of `c`. -/
def nbrFinset (c : GWord N' → ℕ) (x : GWord N') : Finset (GWord N') :=
  childFinset c x ∪ parentFinset x

lemma mem_childFinset {x y : GWord N'} :
    y ∈ childFinset c x ↔ ∃ j : Fin N', (j : ℕ) < c x ∧ y = x ++ [j] := by
  simp only [childFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩

lemma mem_nbrFinset {x y : GWord N'} :
    y ∈ nbrFinset c x
      ↔ (∃ j : Fin N', (j : ℕ) < c x ∧ y = x ++ [j]) ∨ (x ≠ [] ∧ y = x.dropLast) := by
  simp only [nbrFinset, Finset.mem_union, mem_childFinset, parentFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · split_ifs at h with hx
      · simp at h
      · rw [Finset.mem_singleton] at h
        exact Or.inr ⟨hx, h⟩
  · rintro (h | ⟨hx, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ?_
      rw [if_neg hx, Finset.mem_singleton]

/-- The number of `j : Fin N'` below `k`. -/
lemma card_fin_filter_lt {k : ℕ} (hk : k ≤ N') :
    ((Finset.univ : Finset (Fin N')).filter (fun j : Fin N' => (j : ℕ) < k)).card
      = k := by
  have himg : ((Finset.univ : Finset (Fin N')).filter
      (fun j : Fin N' => (j : ℕ) < k)).image Fin.val = Finset.range k := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hn
      exact ⟨⟨n, lt_of_lt_of_le hn hk⟩, hn, rfl⟩
  have := Finset.card_image_of_injective
    ((Finset.univ : Finset (Fin N')).filter (fun j : Fin N' => (j : ℕ) < k))
    Fin.val_injective
  rw [himg, Finset.card_range] at this
  exact this.symm

lemma card_childFinset {x : GWord N'} (hbdd : c x ≤ N') :
    (childFinset c x).card = c x := by
  rw [childFinset, Finset.card_image_of_injective _ (fun j j' h => by
    simpa using List.append_cancel_left h), card_fin_filter_lt hbdd]

lemma card_nbrFinset {x : GWord N'} (hbdd : c x ≤ N') (hx : x ≠ []) :
    (nbrFinset c x).card = c x + 1 := by
  rw [nbrFinset, Finset.card_union_of_disjoint, card_childFinset hbdd, parentFinset,
    if_neg hx, Finset.card_singleton]
  refine Finset.disjoint_left.mpr fun y hy hy' => ?_
  rw [mem_childFinset] at hy
  obtain ⟨j, -, rfl⟩ := hy
  rw [parentFinset, if_neg hx, Finset.mem_singleton] at hy'
  have h1 : (x ++ [j]).length = x.length + 1 := by simp
  have h2 : x.dropLast.length = x.length - 1 := by simp
  have h3 : 1 ≤ x.length := by
    cases x
    · exact absurd rfl hx
    · simp
  rw [hy'] at h1
  omega

/-- A neighbour of a sample vertex in the sample is a member of `nbrFinset`, and
conversely. -/
lemma mem_nbrFinset_iff_dist_one {x y : GWord N'} (hx : x ∈ sample c) :
    y ∈ nbrFinset c x ↔ y ∈ sample c ∧ BranchingProcess.treeDist x y = 1 := by
  constructor
  · intro hy
    rcases mem_nbrFinset.mp hy with ⟨j, hj, rfl⟩ | ⟨hne, rfl⟩
    · exact ⟨BranchingProcess.mem_sample_append_singleton.mpr ⟨hx, hj⟩,
        BranchingProcess.treeDist_append_singleton x j⟩
    · obtain ⟨j, hj⟩ := eq_dropLast_append hne
      refine ⟨BranchingProcess.Subtree.mem_of_prefix ?_ hx, ?_⟩
      · nth_rewrite 2 [hj]
        exact List.prefix_append _ _
      · rw [BranchingProcess.treeDist_comm]
        nth_rewrite 2 [hj]
        exact BranchingProcess.treeDist_append_singleton x.dropLast j
  · rintro ⟨hy, hd⟩
    rcases treeDistN_eq_one_iff.mp hd with ⟨j, rfl⟩ | ⟨j, hj⟩
    · refine mem_nbrFinset.mpr (Or.inl ⟨j, ?_, rfl⟩)
      exact (BranchingProcess.mem_sample_append_singleton.mp hy).2
    · refine mem_nbrFinset.mpr (Or.inr ⟨?_, ?_⟩)
      · rw [hj]
        simp
      · rw [hj]
        simp

/-- Both adjacency cases move the distance to `w` by exactly one. -/
lemma dist_adj_dichotomy {w x y : GWord N'} (hadj : BranchingProcess.treeDist x y = 1) :
    BranchingProcess.treeDist w y + 1 = BranchingProcess.treeDist w x
      ∨ BranchingProcess.treeDist w x + 1 = BranchingProcess.treeDist w y := by
  rcases treeDistN_eq_one_iff.mp hadj with ⟨j, rfl⟩ | ⟨j, hj⟩
  · by_cases hp : x ++ [j] <+: w
    · exact Or.inl (dist_append_of_prefix hp)
    · exact Or.inr (dist_append_of_not_prefix hp).symm
  · by_cases hp : y ++ [j] <+: w
    · exact Or.inr (hj ▸ dist_append_of_prefix hp)
    · exact Or.inl ((hj ▸ dist_append_of_not_prefix hp : _ = _)).symm

/-- The toward vertex of a sample vertex lies in its neighbour set. -/
lemma twd_mem_nbrFinset {w x : GWord N'} (hw : w ∈ sample c)
    (hne : x ≠ []) (hxw : x ≠ w) : twd w x ∈ nbrFinset c x := by
  rw [twd]
  split_ifs with hp
  · -- the next vertex along `w` is a child carried by the sample
    have hlt : x.length < w.length := by
      rcases lt_or_eq_of_le hp.length_le with h | h
      · exact h
      · exact absurd (hp.eq_of_length h) hxw
    have htake : w.take (x.length + 1) = x ++ [w[x.length]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt,
        ← List.prefix_iff_eq_take.mp hp]
      rfl
    have hmem : w.take (x.length + 1) ∈ sample c :=
      BranchingProcess.Subtree.mem_of_prefix (List.take_prefix _ w) hw
    rw [htake] at hmem ⊢
    exact mem_nbrFinset.mpr
      (Or.inl ⟨_, (BranchingProcess.mem_sample_append_singleton.mp hmem).2, rfl⟩)
  · exact mem_nbrFinset.mpr (Or.inr ⟨hne, rfl⟩)

/-- The neighbours of `x` away from `w`. -/
def awayFinset (c : GWord N' → ℕ) (w x : GWord N') : Finset (GWord N') :=
  (nbrFinset c x).erase (twd w x)

lemma card_awayFinset {w x : GWord N'} (hw : w ∈ sample c)
    (hbdd : c x ≤ N') (hne : x ≠ []) (hxw : x ≠ w) :
    (awayFinset c w x).card = c x := by
  rw [awayFinset, Finset.card_erase_of_mem (twd_mem_nbrFinset hw hne hxw),
    card_nbrFinset hbdd hne]
  omega

/-- A member of the away set of a sphere vertex sits on the next sphere, with the
sphere vertex as its toward vertex. -/
lemma mem_awayFinset_spec {w p x : GWord N'} (hp : p ∈ sample c) {ρ : ℕ}
    (hd : BranchingProcess.treeDist w p = ρ) (hx : x ∈ awayFinset c w p) :
    x ∈ sample c ∧ BranchingProcess.treeDist w x = ρ + 1 ∧ p = twd w x := by
  rw [awayFinset, Finset.mem_erase] at hx
  obtain ⟨hxne, hxnbr⟩ := hx
  obtain ⟨hxs, hadj⟩ := (mem_nbrFinset_iff_dist_one hp).mp hxnbr
  rcases dist_adj_dichotomy (w := w) hadj with hcase | hcase
  · -- `x` one step towards `w` would be the toward vertex
    exact absurd (eq_twd hadj (by omega)) hxne
  · refine ⟨hxs, by omega, eq_twd ?_ (by omega)⟩
    rwa [BranchingProcess.treeDist_comm]

/-- **The sphere recursion**: the next sphere is the union of the away sets. -/
lemma sphereFinset_succ {w : GWord N'} (hw : w ∈ sample c) {ρ : ℕ} (h1 : 1 ≤ ρ) :
    sphereFinset c w (ρ + 1) = (sphereFinset c w ρ).biUnion (awayFinset c w) := by
  ext x
  rw [mem_sphereFinset, Finset.mem_biUnion]
  constructor
  · rintro ⟨hx, hd⟩
    have hxw : x ≠ w := by
      intro h
      rw [h, BranchingProcess.treeDist_self] at hd
      omega
    have hxne : x ≠ [] ∨ x <+: w := by
      by_cases hcase : x = []
      · exact Or.inr (hcase ▸ List.nil_prefix)
      · exact Or.inl hcase
    obtain ⟨hadj, hdd⟩ := twd_spec hxw hxne
    have htmem : twd w x ∈ sample c := by
      rw [twd]
      split_ifs with hcase
      · exact BranchingProcess.Subtree.mem_of_prefix (List.take_prefix _ w) hw
      · exact BranchingProcess.Subtree.mem_of_prefix
          (x.dropLast_prefix) hx
    refine ⟨twd w x, mem_sphereFinset.mpr ⟨htmem, by omega⟩, ?_⟩
    rw [awayFinset, Finset.mem_erase]
    constructor
    · -- `x` is not the toward vertex of its own toward vertex, by distances
      intro hcon
      have htww : twd w x ≠ w := by
        intro h
        rw [h, BranchingProcess.treeDist_self] at hdd
        omega
      have htwne : twd w x ≠ [] ∨ twd w x <+: w := by
        by_cases hcase : twd w x = []
        · exact Or.inr (hcase ▸ List.nil_prefix)
        · exact Or.inl hcase
      obtain ⟨-, hdd2⟩ := twd_spec htww htwne
      rw [← hcon] at hdd2
      omega
    · rw [mem_nbrFinset_iff_dist_one htmem]
      exact ⟨hx, by rwa [BranchingProcess.treeDist_comm]⟩
  · rintro ⟨p, hpmem, hpx⟩
    obtain ⟨hps, hpd⟩ := mem_sphereFinset.mp hpmem
    obtain ⟨hxs, hxd, -⟩ := mem_awayFinset_spec hps hpd hpx
    exact ⟨hxs, hxd⟩

/-- The first sphere is the neighbour set of the base point. -/
lemma sphereFinset_one {w : GWord N'} (hw : w ∈ sample c) :
    sphereFinset c w 1 = nbrFinset c w := by
  ext x
  rw [mem_sphereFinset, mem_nbrFinset_iff_dist_one hw]

/-- **The sphere count**: the cardinality of the next sphere is the sum of the
offspring counts over the current sphere. -/
lemma card_sphereFinset_succ {w : GWord N'} (hw : w ∈ sample c)
    (hbdd : ∀ v, c v ≤ N') {ρ : ℕ} (h1 : 1 ≤ ρ) (hρ : ρ < w.length) :
    (sphereFinset c w (ρ + 1)).card = ∑ p ∈ sphereFinset c w ρ, c p := by
  rw [sphereFinset_succ hw h1]
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hps, hpd⟩ := mem_sphereFinset.mp hp
    have hpne : p ≠ [] := by
      intro h
      rw [h] at hpd
      have : BranchingProcess.treeDist w ([] : GWord N') = w.length := by
        rw [BranchingProcess.treeDist_comm]
        exact BranchingProcess.treeDist_of_prefix (List.nil_prefix)
      omega
    have hpw : p ≠ w := by
      intro h
      rw [h, BranchingProcess.treeDist_self] at hpd
      omega
    exact card_awayFinset hw (hbdd p) hpne hpw
  · intro p hp q hq hpq
    obtain ⟨hps, hpd⟩ := mem_sphereFinset.mp hp
    obtain ⟨hqs, hqd⟩ := mem_sphereFinset.mp hq
    refine Finset.disjoint_left.mpr fun y hyp hyq => ?_
    obtain ⟨-, -, hyp'⟩ := mem_awayFinset_spec hps hpd hyp
    obtain ⟨-, -, hyq'⟩ := mem_awayFinset_spec hqs hqd hyq
    exact hpq (hyp'.trans hyq'.symm)

/-- **The sphere count lies in the semigroup**: `|S(w, ρ+1)| = 2 + s` with `s` a sum
of shifted offspring values. -/
lemma exists_sphereFinset_card {Λ : AddSubmonoid ℕ} (hsupp : ∀ v, c v - 1 ∈ Λ)
    (hpos : ∀ v, 1 ≤ c v) (hbdd : ∀ v, c v ≤ N') {w : GWord N'} (hw : w ∈ sample c) :
    ∀ {ρ : ℕ}, ρ < w.length → ∃ s ∈ Λ, (sphereFinset c w (ρ + 1)).card = 2 + s := by
  intro ρ
  induction ρ with
  | zero =>
      intro hρ
      have hne : w ≠ [] := by
        intro h
        rw [h] at hρ
        simp at hρ
      refine ⟨c w - 1, hsupp w, ?_⟩
      rw [sphereFinset_one hw, card_nbrFinset (hbdd w) hne]
      have := hpos w
      omega
  | succ ρ ih =>
      intro hρ
      obtain ⟨s, hs, hcard⟩ := ih (by omega)
      refine ⟨s + ∑ p ∈ sphereFinset c w (ρ + 1), (c p - 1),
        Λ.add_mem hs (AddSubmonoid.sum_mem Λ fun p _ => hsupp p), ?_⟩
      rw [card_sphereFinset_succ hw hbdd (by omega) hρ]
      have hsum : ∑ p ∈ sphereFinset c w (ρ + 1), c p
          = (∑ p ∈ sphereFinset c w (ρ + 1), (c p - 1))
            + (sphereFinset c w (ρ + 1)).card := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        have := hpos p
        omega
      omega

end Sphere

/-! ### The constants of the separation argument -/

/-- The stability constant of Step 3: images of star vertices near a median. -/
def sepC2 (D m : ℕ) : ℕ := D * (m + 3 * D * D + 1) + 2 * D

/-- The annulus depth: beyond-points of sphere vertices sit at this distance. -/
def sepC3 (D m : ℕ) : ℕ :=
  D * m + D * (D * (sepC2 D m + 3 * D) + D * D) + 3 * D + sepC2 D m + 2

/-- The reach of a coarse preimage of an annulus point. -/
def sepLb (D m : ℕ) : ℕ := D * (sepC3 D m + 1 + D) + D * D

/-- The line length of the star. -/
def sepL (D m : ℕ) : ℕ := sepLb D m + m + D * (sepC2 D m + 2) + D * D + 5

/-- The separation of the two star centres removing the root hypothesis. -/
def sepR (D m : ℕ) : ℕ := D * (2 * sepC3 D m + 4) + D * D + 1

lemma sepC2_le_sepC3 (D m : ℕ) : sepC2 D m + 1 ≤ sepC3 D m := by
  rw [sepC3]
  omega

/-! ### The star interface -/

/-- **An `L`-star of excess `m`** in a set of words: a centre, `m + 2` boundary ends,
and the lines towards them, with the geodesic classification, the pairwise divergence
of the lines, and the rigidity of the `L`-neighbourhood of the centre.  The
probabilistic layer constructs one from the coordinate pattern of
`thm:chain-separation` Step 2; the offsets record the distance from the centre to the
head of each line, at most `m` through the stack. -/
structure Star (N : ℕ) (T : GWord N → Prop) (m L : ℕ) : Type where
  /-- The centre. -/
  ctr : GWord N
  ctrMem : T ctr
  /-- The boundary ends, one per line. -/
  ends : Finset (GWord N)
  card_ends : ends.card = m + 2
  /-- The line towards an end, indexed by the distance along it. -/
  line : GWord N → ℕ → GWord N
  /-- The offset of a line: the distance from the centre to its head, less one. -/
  off : GWord N → ℕ
  off_le : ∀ e ∈ ends, off e ≤ m
  lineMem : ∀ e ∈ ends, ∀ t, t ≤ L - 1 → T (line e t)
  line_dist : ∀ e ∈ ends, ∀ t, t ≤ L - 1 →
    BranchingProcess.treeDist ctr (line e t) = off e + t + 1
  line_end : ∀ e ∈ ends, line e (L - 1) = e
  /-- Distinct lines diverge at the star. -/
  line_pair : ∀ e ∈ ends, ∀ e' ∈ ends, e ≠ e' → ∀ t, t ≤ L - 1 → ∀ t', t' ≤ L - 1 →
    t + t' + 2 ≤ BranchingProcess.treeDist (line e t) (line e' t')
  /-- A vertex on the geodesic from the centre to a line vertex is in the star or on
  that line. -/
  onGeo : ∀ e ∈ ends, ∀ t, t ≤ L - 1 → ∀ x, T x →
    BranchingProcess.treeDist ctr x + BranchingProcess.treeDist x (line e t)
      = BranchingProcess.treeDist ctr (line e t) →
    BranchingProcess.treeDist ctr x ≤ m ∨ ∃ t', t' ≤ t ∧ x = line e t'
  /-- The distance along a line. -/
  line_seg_dist : ∀ e ∈ ends, ∀ t t', t ≤ t' → t' ≤ L - 1 →
    BranchingProcess.treeDist (line e t) (line e t') = t' - t
  /-- A vertex on the geodesic between two vertices of a line is on the line. -/
  onGeoSeg : ∀ e ∈ ends, ∀ t t', t ≤ t' → t' ≤ L - 1 → ∀ x, T x →
    BranchingProcess.treeDist (line e t) x + BranchingProcess.treeDist x (line e t')
      = BranchingProcess.treeDist (line e t) (line e t') →
    ∃ τ, t ≤ τ ∧ τ ≤ t' ∧ x = line e τ
  /-- Rigidity: everything within `L - 1` of the centre is in the star or on a line. -/
  classify : ∀ x, T x → BranchingProcess.treeDist ctr x ≤ L - 1 →
    BranchingProcess.treeDist ctr x ≤ m
      ∨ ∃ e ∈ ends, ∃ t, t ≤ L - 1 ∧ x = line e t

/-! ### The core argument -/

namespace Star

variable {m L : ℕ} {T : GWord N → Prop}

/-- The ends of a star are vertices. -/
lemma end_mem (S : Star N T m L) {e : GWord N} (he : e ∈ S.ends) : T e := by
  have h := S.lineMem e he (L - 1) le_rfl
  rwa [S.line_end e he] at h

/-- The centre as a vertex. -/
def ctrVert (S : Star N T m L) : {w : GWord N // T w} := ⟨S.ctr, S.ctrMem⟩

/-- An end as a vertex. -/
def endVert (S : Star N T m L) {e : GWord N} (he : e ∈ S.ends) : {w : GWord N // T w} :=
  ⟨e, S.end_mem he⟩

/-- The distance from the centre to an end. -/
lemma dist_ctr_end (S : Star N T m L) {e : GWord N} (he : e ∈ S.ends) :
    BranchingProcess.treeDist S.ctr e = S.off e + (L - 1) + 1 := by
  have h := S.line_dist e he (L - 1) le_rfl
  rwa [S.line_end e he] at h

end Star

/-- The median of vertices of a prefix-closed set is a vertex. -/
lemma med_mem {T : GWord N → Prop} (hT : PrefixClosedN T) {w a b : GWord N}
    (hw : T w) (ha : T a) : T (med w a b) := by
  rw [med]
  split_ifs
  · exact hT (BranchingProcess.wedge_prefix_left w b) hw
  · exact hT (BranchingProcess.wedge_prefix_left w a) hw
  · exact hT (BranchingProcess.wedge_prefix_left a b) ha

section Core

variable {N N' m D : ℕ} {T : GWord N → Prop} {c' : GWord N' → ℕ}
variable {f : {w : GWord N // T w} → {w' : GWord N' // w' ∈ sample c'}}

/-- One stability step: a between-vertex of the images of the centre and an end is
within `D` of the image of a star vertex or a line vertex. -/
private lemma stab_step (hT : PrefixClosedN T)
    (S : Star N T m (sepL D m))
    (hf : BranchingProcess.IsQIWith D (wordGraphN T)
      (wordGraphN (fun w : GWord N' => w ∈ sample c')) f)
    {e₀ : GWord N} (he₀ : e₀ ∈ S.ends) {μ : GWord N'} (hμmem : μ ∈ sample c')
    (hadd : BranchingProcess.treeDist (f S.ctrVert).1 μ
        + BranchingProcess.treeDist μ (f (S.endVert he₀)).1
        = BranchingProcess.treeDist (f S.ctrVert).1 (f (S.endVert he₀)).1) :
    ∃ u : {w : GWord N // T w},
      BranchingProcess.treeDist (f u).1 μ ≤ D ∧
      (BranchingProcess.treeDist S.ctr u.1 ≤ m
        ∨ ∃ τ, τ ≤ sepL D m - 1 ∧ u.1 = S.line e₀ τ) := by
  have hT'c : PrefixClosedN (fun w : GWord N' => w ∈ sample c') := prefixClosedN_sample c'
  obtain ⟨p, -, hplen⟩ := (wordGraphN_connected hT ⟨S.ctrVert⟩).exists_path_of_dist
    S.ctrVert (S.endVert he₀)
  have hbet : BranchingProcess.Between
      (wordGraphN (fun w : GWord N' => w ∈ sample c')) (f S.ctrVert)
      ⟨μ, hμmem⟩ (f (S.endVert he₀)) := betweenN hT'c hadd
  obtain ⟨i, hi, hstab⟩ := BranchingProcess.exists_between_dist_le
    (wordGraphN_isTree hT'c ⟨f S.ctrVert⟩) hf p hbet
  have hplen' : p.length
      = BranchingProcess.treeDist S.ctrVert.1 (S.endVert he₀).1 := by
    rw [hplen, wordGraphN_dist hT]
  obtain ⟨-, -, haddu⟩ := getVert_eq_geoPt hplen' hi
  have hclass := S.onGeo e₀ he₀ (sepL D m - 1) le_rfl (p.getVert i).1 (p.getVert i).2 (by
    rw [S.line_end e₀ he₀]
    exact haddu)
  refine ⟨p.getVert i, ?_, hclass⟩
  have h := hstab
  rw [wordGraphN_dist hT'c] at h
  exact h

/-- The finishing bound: the image of a vertex near the star is near the base image,
so a between-vertex within `D` of it sits within `C₂` of the base image. -/
private lemma stab_finish (hT : PrefixClosedN T)
    (S : Star N T m (sepL D m))
    (hf : BranchingProcess.IsQIWith D (wordGraphN T)
      (wordGraphN (fun w : GWord N' => w ∈ sample c')) f)
    {μ : GWord N'} {u₀ : {w : GWord N // T w}}
    (hstab₀ : BranchingProcess.treeDist (f u₀).1 μ ≤ D)
    (hpos₀ : BranchingProcess.treeDist S.ctr u₀.1 ≤ m + 3 * D * D + 1) :
    BranchingProcess.treeDist (f S.ctrVert).1 μ ≤ sepC2 D m := by
  have hT'c : PrefixClosedN (fun w : GWord N' => w ∈ sample c') := prefixClosedN_sample c'
  have hupper := hf.upper S.ctrVert u₀
  rw [wordGraphN_dist hT, wordGraphN_dist hT'c] at hupper
  have hctr : S.ctrVert.1 = S.ctr := rfl
  rw [hctr] at hupper
  have hmul := Nat.mul_le_mul_left D hpos₀
  have htri := BranchingProcess.treeDist_triangle
    (f S.ctrVert).1 (f u₀).1 μ
  rw [sepC2]
  omega

/-- **Step 3, first part**: the images of the centre and two distinct ends satisfy the
Gromov product bound `(y ⋅ y')_w ≤ C₂`. -/
lemma star_gromov (hT : PrefixClosedN T)
    (S : Star N T m (sepL D m))
    (hf : BranchingProcess.IsQIWith D (wordGraphN T)
      (wordGraphN (fun w : GWord N' => w ∈ sample c')) f)
    {e e' : GWord N} (he : e ∈ S.ends) (he' : e' ∈ S.ends) (hne : e ≠ e') :
    BranchingProcess.treeDist (f S.ctrVert).1 (f (S.endVert he)).1
      + BranchingProcess.treeDist (f S.ctrVert).1 (f (S.endVert he')).1
      ≤ 2 * sepC2 D m
        + BranchingProcess.treeDist (f (S.endVert he)).1 (f (S.endVert he')).1 := by
  have hT'c : PrefixClosedN (fun w : GWord N' => w ∈ sample c') := prefixClosedN_sample c'
  have hμmem : (fun w : GWord N' => w ∈ sample c')
      (med (f S.ctrVert).1 (f (S.endVert he)).1 (f (S.endVert he')).1) :=
    med_mem hT'c (f S.ctrVert).2 (f (S.endVert he)).2
  have hml := med_add_left (f S.ctrVert).1 (f (S.endVert he)).1 (f (S.endVert he')).1
  have hmr := med_add_right (f S.ctrVert).1 (f (S.endVert he)).1 (f (S.endVert he')).1
  have hmo := med_add_outer (f S.ctrVert).1 (f (S.endVert he)).1 (f (S.endVert he')).1
  have hc1 := BranchingProcess.treeDist_comm (f (S.endVert he)).1
    (med (f S.ctrVert).1 (f (S.endVert he)).1 (f (S.endVert he')).1)
  suffices hsuff : BranchingProcess.treeDist (f S.ctrVert).1
      (med (f S.ctrVert).1 (f (S.endVert he)).1 (f (S.endVert he')).1) ≤ sepC2 D m by
    omega
  obtain ⟨u, hu1, hu2⟩ := stab_step hT S hf he hμmem (by omega)
  obtain ⟨u', hu1', hu2'⟩ := stab_step hT S hf he' hμmem (by omega)
  rcases hu2 with hK | ⟨τ, hτle, hτ⟩
  · exact stab_finish hT S hf hu1 (by omega)
  rcases hu2' with hK' | ⟨τ', hτle', hτ'⟩
  · exact stab_finish hT S hf hu1' (by omega)
  -- both stability vertices on their lines: the divergence bounds the positions
  have hpair := S.line_pair e he e' he' hne τ hτle τ' hτle'
  rw [← hτ, ← hτ'] at hpair
  have hlow := hf.lower u u'
  rw [wordGraphN_dist hT, wordGraphN_dist hT'c] at hlow
  have htri2 := BranchingProcess.treeDist_triangle (f u).1
    (med (f S.ctrVert).1 (f (S.endVert he)).1 (f (S.endVert he')).1) (f u').1
  have hc2 := BranchingProcess.treeDist_comm
    (med (f S.ctrVert).1 (f (S.endVert he)).1 (f (S.endVert he')).1) (f u').1
  have hffbound : BranchingProcess.treeDist (f u).1 (f u').1 ≤ 2 * D := by omega
  have hmul2 := Nat.mul_le_mul_left D hffbound
  have hDD : D * (2 * D) = 2 * (D * D) := by ring
  have hτbound : τ ≤ 3 * (D * D) := by omega
  have hoff := S.off_le e he
  have hdτ := S.line_dist e he τ hτle
  refine stab_finish hT S hf hu1 ?_
  rw [hτ, hdτ]
  have h3 : 3 * (D * D) = 3 * D * D := by ring
  omega

/-- The image of an end is well separated from the image of the centre. -/
lemma star_end_far (hT : PrefixClosedN T) (hD : 1 ≤ D)
    (S : Star N T m (sepL D m))
    (hf : BranchingProcess.IsQIWith D (wordGraphN T)
      (wordGraphN (fun w : GWord N' => w ∈ sample c')) f)
    {e : GWord N} (he : e ∈ S.ends) :
    sepC2 D m + 2
      ≤ BranchingProcess.treeDist (f S.ctrVert).1 (f (S.endVert he)).1 := by
  have hT'c : PrefixClosedN (fun w : GWord N' => w ∈ sample c') := prefixClosedN_sample c'
  have hlow := hf.lower S.ctrVert (S.endVert he)
  rw [wordGraphN_dist hT, wordGraphN_dist hT'c] at hlow
  have hdist : BranchingProcess.treeDist S.ctrVert.1 (S.endVert he).1
      = S.off e + (sepL D m - 1) + 1 := S.dist_ctr_end he
  by_contra hcon
  push Not at hcon
  have hle : BranchingProcess.treeDist (f S.ctrVert).1 (f (S.endVert he)).1
      ≤ sepC2 D m + 1 := by omega
  have hmul := Nat.mul_le_mul_left D hle
  have hexp : D * (sepC2 D m + 2) = D * (sepC2 D m + 1) + D := by ring
  have hL : sepL D m = sepLb D m + m + D * (sepC2 D m + 2) + D * D + 5 := rfl
  omega

/-- **The gates are distinct**: the geodesic vertices at depth `C₂ + 1` towards the
images of two distinct ends differ. -/
lemma star_gates_inj (hT : PrefixClosedN T) (hD : 1 ≤ D)
    (S : Star N T m (sepL D m))
    (hf : BranchingProcess.IsQIWith D (wordGraphN T)
      (wordGraphN (fun w : GWord N' => w ∈ sample c')) f)
    {e e' : GWord N} (he : e ∈ S.ends) (he' : e' ∈ S.ends) (hne : e ≠ e') :
    geoPt (f S.ctrVert).1 (f (S.endVert he)).1 (sepC2 D m + 1)
      ≠ geoPt (f S.ctrVert).1 (f (S.endVert he')).1 (sepC2 D m + 1) := by
  intro hcon
  have hfar := star_end_far hT hD S hf he
  have hfar' := star_end_far hT hD S hf he'
  have hd := geoPt_dist (f S.ctrVert).1 (f (S.endVert he)).1
    (k := sepC2 D m + 1) (by omega)
  have hadd := geoPt_add (f S.ctrVert).1 (f (S.endVert he)).1
    (k := sepC2 D m + 1) (by omega)
  have hadd' := geoPt_add (f S.ctrVert).1 (f (S.endVert he')).1
    (k := sepC2 D m + 1) (by omega)
  rw [← hcon] at hadd'
  have hgro := star_gromov hT S hf he he' hne
  have htwo := two_mul_dist_le_of_dist_add hadd hadd'
  omega

/-- The witness of a sphere vertex: an annulus point behind it, a coarse preimage,
and the line carrying that preimage. -/
def GateWit (S : Star N T m (sepL D m))
    (f : {w : GWord N // T w} → {w' : GWord N' // w' ∈ sample c'})
    (D : ℕ) (g : GWord N') (e : GWord N) : Prop :=
  ∃ (z : GWord N') (x : {w : GWord N // T w}) (t : ℕ),
    z ∈ sample c' ∧
    BranchingProcess.treeDist (f S.ctrVert).1 z = sepC3 D m + 1 ∧
    BranchingProcess.treeDist (f S.ctrVert).1 g + BranchingProcess.treeDist g z
      = BranchingProcess.treeDist (f S.ctrVert).1 z ∧
    BranchingProcess.treeDist (f x).1 z ≤ D ∧
    x.1 = S.line e t ∧ t ≤ sepL D m - 1

/-- **Every sphere vertex has a witness**: its annulus point pulls back to a line. -/
lemma star_gate_witness (hT : PrefixClosedN T)
    (S : Star N T m (sepL D m))
    (hf : BranchingProcess.IsQIWith D (wordGraphN T)
      (wordGraphN (fun w : GWord N' => w ∈ sample c')) f)
    (hroot : sepC3 D m + 1 ≤ (f S.ctrVert).1.length)
    (hN' : 0 < N') (hpos' : ∀ v, 1 ≤ c' v)
    {g : GWord N'} (hg : g ∈ sample c')
    (hgd : BranchingProcess.treeDist (f S.ctrVert).1 g = sepC2 D m + 1) :
    ∃ e ∈ S.ends, GateWit S f D g e := by
  have hT'c : PrefixClosedN (fun w : GWord N' => w ∈ sample c') := prefixClosedN_sample c'
  have hC23 := sepC2_le_sepC3 D m
  obtain ⟨z, hz, hzd, hzadd⟩ := exists_beyond hN' hpos' (f S.ctrVert).2 hg hgd
    (by omega) hroot
  obtain ⟨x, hx⟩ := hf.dense ⟨z, hz⟩
  rw [wordGraphN_dist hT'c] at hx
  replace hx : BranchingProcess.treeDist (f x).1 z ≤ D := hx
  -- the preimage lies within the rigid neighbourhood of the centre
  have hlow := hf.lower S.ctrVert x
  rw [wordGraphN_dist hT, wordGraphN_dist hT'c] at hlow
  have htri := BranchingProcess.treeDist_triangle (f S.ctrVert).1 z (f x).1
  have hcz := BranchingProcess.treeDist_comm z (f x).1
  have himg : BranchingProcess.treeDist (f S.ctrVert).1 (f x).1
      ≤ sepC3 D m + 1 + D := by omega
  have hmul := Nat.mul_le_mul_left D himg
  have hLb : sepLb D m = D * (sepC3 D m + 1 + D) + D * D := rfl
  have hL : sepL D m = sepLb D m + m + D * (sepC2 D m + 2) + D * D + 5 := rfl
  have hxle : BranchingProcess.treeDist S.ctr x.1 ≤ sepL D m - 1 := by
    have hctr : S.ctrVert.1 = S.ctr := rfl
    rw [hctr] at hlow
    omega
  rcases S.classify x.1 x.2 hxle with hK | ⟨e, he, t, ht, hx'⟩
  · -- a preimage in the star is too close to the image of the centre
    exfalso
    have hup := hf.upper S.ctrVert x
    rw [wordGraphN_dist hT, wordGraphN_dist hT'c] at hup
    have hctr : S.ctrVert.1 = S.ctr := rfl
    rw [hctr] at hup
    have hmul2 := Nat.mul_le_mul_left D hK
    have htri2 := BranchingProcess.treeDist_triangle (f S.ctrVert).1 (f x).1 z
    have hC3 : sepC3 D m = D * m
        + D * (D * (sepC2 D m + 3 * D) + D * D) + 3 * D + sepC2 D m + 2 := rfl
    omega
  · exact ⟨e, he, z, x, t, hz, hzd, hzadd, hx, hx', ht⟩

/-- **No two sphere vertices share a line**: the witnesses of distinct gates through
one line collide. -/
lemma star_no_two_gates (hT : PrefixClosedN T) (hD : 1 ≤ D)
    (S : Star N T m (sepL D m))
    (hf : BranchingProcess.IsQIWith D (wordGraphN T)
      (wordGraphN (fun w : GWord N' => w ∈ sample c')) f)
    {e : GWord N} (he : e ∈ S.ends) {g g' : GWord N'} (hgg : g ≠ g')
    (hgd : BranchingProcess.treeDist (f S.ctrVert).1 g = sepC2 D m + 1)
    (hgd' : BranchingProcess.treeDist (f S.ctrVert).1 g' = sepC2 D m + 1)
    {z z' : GWord N'} {x x' : {w : GWord N // T w}} {t t' : ℕ}
    (hzd : BranchingProcess.treeDist (f S.ctrVert).1 z = sepC3 D m + 1)
    (hzadd : BranchingProcess.treeDist (f S.ctrVert).1 g
      + BranchingProcess.treeDist g z = BranchingProcess.treeDist (f S.ctrVert).1 z)
    (hxz : BranchingProcess.treeDist (f x).1 z ≤ D)
    (hxl : x.1 = S.line e t) (htle : t ≤ sepL D m - 1)
    (hzd' : BranchingProcess.treeDist (f S.ctrVert).1 z' = sepC3 D m + 1)
    (hzadd' : BranchingProcess.treeDist (f S.ctrVert).1 g'
      + BranchingProcess.treeDist g' z' = BranchingProcess.treeDist (f S.ctrVert).1 z')
    (hxz' : BranchingProcess.treeDist (f x').1 z' ≤ D)
    (hxl' : x'.1 = S.line e t') (htle' : t' ≤ sepL D m - 1)
    (htt : t ≤ t') : False := by
  have hT'c : PrefixClosedN (fun w : GWord N' => w ∈ sample c') := prefixClosedN_sample c'
  have hC23 := sepC2_le_sepC3 D m
  -- the two annulus points diverge before depth `C₂`
  have hgeo : g = geoPt (f S.ctrVert).1 z (sepC2 D m + 1) := by
    have := geoPt_unique hzadd
    rwa [hgd] at this
  have hgeo' : g' = geoPt (f S.ctrVert).1 z' (sepC2 D m + 1) := by
    have := geoPt_unique hzadd'
    rwa [hgd'] at this
  have hql := med_add_left (f S.ctrVert).1 z z'
  have hqr := med_add_right (f S.ctrVert).1 z z'
  have hqo := med_add_outer (f S.ctrVert).1 z z'
  have hzz : 2 * (sepC3 D m + 1)
      ≤ BranchingProcess.treeDist z z' + 2 * sepC2 D m := by
    by_cases hqd : sepC2 D m + 1
        ≤ BranchingProcess.treeDist (f S.ctrVert).1 (med (f S.ctrVert).1 z z') 
    · exfalso
      refine hgg ?_
      rw [hgeo, hgeo', geoPt_comp hql hqd, geoPt_comp hqr hqd]
    · push Not at hqd
      have hcz := BranchingProcess.treeDist_comm z (med (f S.ctrVert).1 z z')
      omega
  -- so the images of the two witnesses are far apart
  have htr1 := BranchingProcess.treeDist_triangle z (f x).1 (f x').1
  have htr2 := BranchingProcess.treeDist_triangle (f x).1 (f x').1 z'
  have htr3 := BranchingProcess.treeDist_triangle z z' (f x').1
  have hcx := BranchingProcess.treeDist_comm z (f x).1
  have hcz' := BranchingProcess.treeDist_comm z' (f x').1
  have hff : BranchingProcess.treeDist z z'
      ≤ BranchingProcess.treeDist (f x).1 (f x').1 + 2 * D := by
    have h1 := BranchingProcess.treeDist_triangle z z' ((f x').1)
    have h2 := BranchingProcess.treeDist_triangle z (f x).1 (f x').1
    have h3 := BranchingProcess.treeDist_triangle (f x).1 (f x').1 z'
    have h4 := BranchingProcess.treeDist_triangle z (f x).1 z'
    have h5 := BranchingProcess.treeDist_triangle (f x).1 z' ((f x').1)
    have hc1 := BranchingProcess.treeDist_comm z' (f x').1
    have hc2 := BranchingProcess.treeDist_comm z (f x).1
    omega
  -- the median of the two images sits within `C₂ + 2D` of the base image
  have hml2 := med_add_left (f S.ctrVert).1 (f x).1 (f x').1
  have hmr2 := med_add_right (f S.ctrVert).1 (f x).1 (f x').1
  have hmo2 := med_add_outer (f S.ctrVert).1 (f x).1 (f x').1
  have himg1 : BranchingProcess.treeDist (f S.ctrVert).1 (f x).1
      ≤ sepC3 D m + 1 + D := by
    have := BranchingProcess.treeDist_triangle (f S.ctrVert).1 z (f x).1
    have hc := BranchingProcess.treeDist_comm z (f x).1
    omega
  have himg2 : BranchingProcess.treeDist (f S.ctrVert).1 (f x').1
      ≤ sepC3 D m + 1 + D := by
    have := BranchingProcess.treeDist_triangle (f S.ctrVert).1 z' (f x').1
    have hc := BranchingProcess.treeDist_comm z' (f x').1
    omega
  have hq2 : BranchingProcess.treeDist (f S.ctrVert).1
      (med (f S.ctrVert).1 (f x).1 (f x').1) ≤ sepC2 D m + 2 * D := by
    have hc := BranchingProcess.treeDist_comm (f x).1
      (med (f S.ctrVert).1 (f x).1 (f x').1)
    omega
  -- stability along the line segment between the two witnesses
  have hq2mem : (fun w : GWord N' => w ∈ sample c')
      (med (f S.ctrVert).1 (f x).1 (f x').1) :=
    med_mem hT'c (f S.ctrVert).2 (f x).2
  obtain ⟨p, -, hplen⟩ := (wordGraphN_connected hT ⟨x⟩).exists_path_of_dist x x'
  have hbet : BranchingProcess.Between
      (wordGraphN (fun w : GWord N' => w ∈ sample c')) (f x)
      ⟨med (f S.ctrVert).1 (f x).1 (f x').1, hq2mem⟩ (f x') := by
    refine betweenN hT'c ?_
    exact hmo2
  obtain ⟨i, hi, hstab⟩ := BranchingProcess.exists_between_dist_le
    (wordGraphN_isTree hT'c ⟨f x⟩) hf p hbet
  rw [wordGraphN_dist hT'c] at hstab
  replace hstab : BranchingProcess.treeDist (f (p.getVert i)).1
      (med (f S.ctrVert).1 (f x).1 (f x').1) ≤ D := hstab
  have hplen' : p.length = BranchingProcess.treeDist x.1 x'.1 := by
    rw [hplen, wordGraphN_dist hT]
  obtain ⟨-, -, haddu⟩ := getVert_eq_geoPt hplen' hi
  -- the stability vertex is a line vertex between the two witnesses
  obtain ⟨τ, hτ1, hτ2, hτeq⟩ := S.onGeoSeg e he t t' htt htle' (p.getVert i).1
    (p.getVert i).2 (by rw [← hxl, ← hxl']; exact haddu)
  -- its image is close to the base image, so its position is small
  have hnear : BranchingProcess.treeDist (f S.ctrVert).1 (f (p.getVert i)).1
      ≤ sepC2 D m + 3 * D := by
    have := BranchingProcess.treeDist_triangle (f S.ctrVert).1
      (med (f S.ctrVert).1 (f x).1 (f x').1) (f (p.getVert i)).1
    have hc := BranchingProcess.treeDist_comm (f (p.getVert i)).1
      (med (f S.ctrVert).1 (f x).1 (f x').1)
    omega
  have hlow2 := hf.lower S.ctrVert (p.getVert i)
  rw [wordGraphN_dist hT, wordGraphN_dist hT'c] at hlow2
  have hctr : S.ctrVert.1 = S.ctr := rfl
  rw [hctr] at hlow2
  have hτd := S.line_dist e he τ (le_trans hτ2 htle')
  rw [← hτeq] at hτd
  have hmulnear := Nat.mul_le_mul_left D hnear
  have hposbound : t + 1 ≤ D * (sepC2 D m + 3 * D) + D * D := by omega
  -- the position of the first witness is large
  have hup := hf.upper S.ctrVert x
  rw [wordGraphN_dist hT, wordGraphN_dist hT'c] at hup
  rw [hctr] at hup
  have htd := S.line_dist e he t htle
  rw [← hxl] at htd
  have hoff := S.off_le e he
  have himgfar : sepC3 D m + 1
      ≤ BranchingProcess.treeDist (f S.ctrVert).1 (f x).1 + D := by
    have := BranchingProcess.treeDist_triangle (f S.ctrVert).1 (f x).1 z
    omega
  have hmt : BranchingProcess.treeDist S.ctr x.1 ≤ m + t + 1 := by omega
  have hmulmt := Nat.mul_le_mul_left D hmt
  have hexp1 : D * (m + t + 1) = D * m + D * t + D := by ring
  -- the contradiction between the two bounds on `t`
  have hmulpos := Nat.mul_le_mul_left D hposbound
  have hexp2 : D * (t + 1) = D * t + D := by ring
  have hC3 : sepC3 D m = D * m
      + D * (D * (sepC2 D m + 3 * D) + D * D) + 3 * D + sepC2 D m + 2 := rfl
  omega

/-- **The core argument**: a `D`-quasi-isometry carrying the centre of a star deep
into the target sample forces the excess `m` into the submonoid of the sphere
counts. -/
theorem star_no_qi (hT : PrefixClosedN T) (hD : 1 ≤ D)
    (S : Star N T m (sepL D m)) {Λ' : AddSubmonoid ℕ} (hm : m ∉ Λ')
    (hN' : 0 < N') (hpos' : ∀ v, 1 ≤ c' v) (hbdd' : ∀ v, c' v ≤ N')
    (hsupp' : ∀ v, c' v - 1 ∈ Λ')
    (hf : BranchingProcess.IsQIWith D (wordGraphN T)
      (wordGraphN (fun w : GWord N' => w ∈ sample c')) f)
    (hroot : sepC3 D m + 1 ≤ (f S.ctrVert).1.length) : False := by
  classical
  have hT'c : PrefixClosedN (fun w : GWord N' => w ∈ sample c') := prefixClosedN_sample c'
  have hC23 := sepC2_le_sepC3 D m
  obtain ⟨s, hs, hcard⟩ := exists_sphereFinset_card hsupp' hpos' hbdd'
    (f S.ctrVert).2 (ρ := sepC2 D m) (by omega)
  -- the ends inject into the sphere through their gates
  have hend_inj : S.ends.card
      ≤ (sphereFinset c' (f S.ctrVert).1 (sepC2 D m + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun e => if h : e ∈ S.ends then
      geoPt (f S.ctrVert).1 (f (S.endVert h)).1 (sepC2 D m + 1) else []) ?_ ?_
    · intro e he
      simp only [Finset.mem_coe] at he
      dsimp only
      rw [dif_pos he, Finset.mem_coe, mem_sphereFinset]
      have hfar := star_end_far hT hD S hf he
      exact ⟨geoPt_mem hT'c (f S.ctrVert).2 (f (S.endVert he)).2 _,
        geoPt_dist _ _ (by omega)⟩
    · intro e he e' he' hee
      simp only [Finset.mem_coe] at he he'
      dsimp only at hee
      rw [dif_pos he, dif_pos he'] at hee
      by_contra hne
      exact star_gates_inj hT hD S hf he he' hne hee
  -- the sphere injects into the ends through the witnesses
  have hwit : ∀ g ∈ sphereFinset c' (f S.ctrVert).1 (sepC2 D m + 1),
      ∃ e, e ∈ S.ends ∧ GateWit S f D g e := by
    intro g hg
    obtain ⟨hgs, hgd⟩ := mem_sphereFinset.mp hg
    obtain ⟨e, he, hw⟩ := star_gate_witness hT S hf hroot hN' hpos' hgs hgd
    exact ⟨e, he, hw⟩
  have hsphere_inj : (sphereFinset c' (f S.ctrVert).1 (sepC2 D m + 1)).card
      ≤ S.ends.card := by
    refine Finset.card_le_card_of_injOn (fun g =>
      if h : ∃ e, e ∈ S.ends ∧ GateWit S f D g e then h.choose else S.ctr) ?_ ?_
    · intro g hg
      simp only [Finset.mem_coe] at hg
      dsimp only
      rw [dif_pos (hwit g hg), Finset.mem_coe]
      exact ((hwit g hg).choose_spec).1
    · intro g hg g' hg' hgg'
      simp only [Finset.mem_coe] at hg hg'
      by_contra hne
      have h1 := hwit g hg
      have h2 := hwit g' hg'
      dsimp only at hgg'
      rw [dif_pos h1, dif_pos h2] at hgg'
      obtain ⟨he1, hw1⟩ := h1.choose_spec
      obtain ⟨he2, hw2⟩ := h2.choose_spec
      rw [hgg'] at hw1
      obtain ⟨-, hgd⟩ := mem_sphereFinset.mp hg
      obtain ⟨-, hgd'⟩ := mem_sphereFinset.mp hg'
      obtain ⟨z, x, t, -, hzd, hzadd, hxz, hxl, htle⟩ := hw1
      obtain ⟨z', x', t', -, hzd', hzadd', hxz', hxl', htle'⟩ := hw2
      rcases le_total t t' with htt | htt
      · exact star_no_two_gates hT hD S hf he2 hne hgd hgd' hzd hzadd hxz hxl
          htle hzd' hzadd' hxz' hxl' htle' htt
      · exact star_no_two_gates hT hD S hf he2 (Ne.symm hne) hgd' hgd hzd' hzadd'
          hxz' hxl' htle' hzd hzadd hxz hxl htle htt
  have hcards : (sphereFinset c' (f S.ctrVert).1 (sepC2 D m + 1)).card = m + 2 := by
    have h := le_antisymm hsphere_inj hend_inj
    rw [h, S.card_ends]
  rw [hcards] at hcard
  have hsm : s = m := by omega
  exact hm (hsm ▸ hs)

/-- **Step 4**: two stars far apart remove the root hypothesis, so a `D`-quasi-isometry
into a sample with the sphere property cannot exist at all. -/
theorem star_pair_no_qi (hT : PrefixClosedN T) (hD : 1 ≤ D)
    (S S' : Star N T m (sepL D m))
    (hfar : sepR D m ≤ BranchingProcess.treeDist S.ctr S'.ctr)
    {Λ' : AddSubmonoid ℕ} (hm : m ∉ Λ')
    (hN' : 0 < N') (hpos' : ∀ v, 1 ≤ c' v) (hbdd' : ∀ v, c' v ≤ N')
    (hsupp' : ∀ v, c' v - 1 ∈ Λ')
    (hf : BranchingProcess.IsQIWith D (wordGraphN T)
      (wordGraphN (fun w : GWord N' => w ∈ sample c')) f) : False := by
  have hT'c : PrefixClosedN (fun w : GWord N' => w ∈ sample c') := prefixClosedN_sample c'
  have hlow := hf.lower S.ctrVert S'.ctrVert
  rw [wordGraphN_dist hT, wordGraphN_dist hT'c] at hlow
  have hc1 : S.ctrVert.1 = S.ctr := rfl
  have hc2 : S'.ctrVert.1 = S'.ctr := rfl
  rw [hc1, hc2] at hlow
  have himg : 2 * sepC3 D m + 4
      < BranchingProcess.treeDist (f S.ctrVert).1 (f S'.ctrVert).1 := by
    by_contra hcon
    push Not at hcon
    have hmul := Nat.mul_le_mul_left D hcon
    rw [sepR] at hfar
    omega
  have hdepth := BranchingProcess.treeDist_add (f S.ctrVert).1 (f S'.ctrVert).1
  by_cases hc : sepC3 D m + 1 ≤ (f S.ctrVert).1.length
  · exact star_no_qi hT hD S hm hN' hpos' hbdd' hsupp' hf hc
  · refine star_no_qi hT hD S' hm hN' hpos' hbdd' hsupp' hf ?_
    omega

end Core


/-! ### The star of the coordinate pattern -/

section Pattern

variable {a L m : ℕ}

/-- The word of `n` first letters. -/
def zw (hN : 0 < N) (n : ℕ) : GWord N := List.replicate n ⟨0, hN⟩

/-- A vertex of a leaving line: the stack vertex at depth `i`, the letter `j`, and
`t` further first letters. -/
def lineW (hN : 0 < N) (a L i : ℕ) (j : Fin N) (t : ℕ) : GWord N :=
  zw hN (a + L + i) ++ j :: List.replicate t ⟨0, hN⟩

@[simp] lemma zw_length (hN : 0 < N) (n : ℕ) : (zw hN n).length = n :=
  List.length_replicate

@[simp] lemma lineW_length (hN : 0 < N) (a L i : ℕ) (j : Fin N) (t : ℕ) :
    (lineW hN a L i j t).length = a + L + i + 1 + t := by
  simp only [lineW, zw, List.length_append, List.length_cons, List.length_replicate]
  omega

lemma zw_prefix (hN : 0 < N) {n n' : ℕ} (h : n ≤ n') : zw hN n <+: zw hN n' := by
  rw [List.prefix_iff_eq_take, zw_length, zw, zw, List.take_replicate]
  congr 1
  omega

/-- A prefix of a constant word is constant. -/
lemma eq_zw_of_prefix_zw (hN : 0 < N) {n : ℕ} {u : GWord N} (h : u <+: zw hN n) :
    u = zw hN (u.length) := by
  rw [zw, List.eq_replicate_iff]
  exact ⟨rfl, fun b hb => List.eq_of_mem_replicate (h.subset hb)⟩

lemma zw_prefix_lineW (hN : 0 < N) {n : ℕ} (hn : n ≤ a + L + i) (j : Fin N) (t : ℕ) :
    zw hN n <+: lineW hN a L i j t :=
  (zw_prefix hN hn).trans (List.prefix_append _ _)

/-- The initial segments of a line vertex. -/
lemma lineW_take (hN : 0 < N) (a L i : ℕ) (j : Fin N) {t t' : ℕ} (h : t' ≤ t) :
    (lineW hN a L i j t).take (a + L + i + 1 + t') = lineW hN a L i j t' := by
  have hassoc : lineW hN a L i j t
      = (zw hN (a + L + i) ++ [j]) ++ List.replicate t (⟨0, hN⟩ : Fin N) := by
    simp [lineW]
  rw [hassoc]
  have hlen : (zw hN (a + L + i) ++ [j]).length = a + L + i + 1 := by simp [zw]
  rw [List.take_append]
  rw [List.take_of_length_le (by rw [hlen]; omega), hlen,
    show a + L + i + 1 + t' - (a + L + i + 1) = t' from by omega,
    List.take_replicate, min_eq_left h]
  simp [lineW]

lemma lineW_prefix (hN : 0 < N) (a L i : ℕ) (j : Fin N) {t t' : ℕ} (h : t' ≤ t) :
    lineW hN a L i j t' <+: lineW hN a L i j t := by
  rw [← lineW_take hN a L i j h]
  exact List.take_prefix _ _

/-- Distance from the centre down a line. -/
lemma treeDist_ctr_lineW (hN : 0 < N) (a L i : ℕ) (j : Fin N) (t : ℕ) :
    BranchingProcess.treeDist (zw hN (a + L)) (lineW hN a L i j t) = i + 1 + t := by
  rw [BranchingProcess.treeDist_of_prefix (zw_prefix_lineW hN (by omega) j t),
    lineW_length, zw_length]
  omega

/-- Distance between vertices of a line. -/
lemma treeDist_lineW_lineW (hN : 0 < N) (a L i : ℕ) (j : Fin N) {t t' : ℕ}
    (h : t ≤ t') :
    BranchingProcess.treeDist (lineW hN a L i j t) (lineW hN a L i j t') = t' - t := by
  rw [BranchingProcess.treeDist_of_prefix (lineW_prefix hN a L i j h),
    lineW_length, lineW_length]
  omega

/-- Distance along the ray. -/
lemma treeDist_zw_zw (hN : 0 < N) {n n' : ℕ} (h : n ≤ n') :
    BranchingProcess.treeDist (zw hN n) (zw hN n') = n' - n := by
  rw [BranchingProcess.treeDist_of_prefix (zw_prefix hN h), zw_length, zw_length]

/-- Mismatched words diverge at the length of their wedge. -/
lemma getElem_ne_of_wedge {u v : GWord N}
    (hu : (BranchingProcess.wedge u v).length < u.length)
    (hv : (BranchingProcess.wedge u v).length < v.length) :
    u[(BranchingProcess.wedge u v).length]'hu ≠ v[(BranchingProcess.wedge u v).length]'hv := by
  induction u generalizing v with
  | nil => simp at hu
  | cons x u ih =>
      cases v with
      | nil => simp at hv
      | cons y v =>
          by_cases hxy : x = y
          · subst hxy
            have hw : BranchingProcess.wedge (x :: u) (x :: v)
                = x :: BranchingProcess.wedge u v := by
              rw [BranchingProcess.wedge_cons_cons, if_pos rfl]
            simp only [hw, List.length_cons, List.getElem_cons_succ] at hu hv ⊢
            exact ih (by omega) (by omega)
          · have hw : BranchingProcess.wedge (x :: u) (y :: v) = [] := by
              rw [BranchingProcess.wedge_cons_cons, if_neg hxy]
            simp only [hw, List.length_nil, List.getElem_cons_zero]
            exact hxy

/-- The wedge of two lines leaving the stack at the same vertex through different
letters is the stack vertex. -/
lemma wedge_lineW_ne (hN : 0 < N) (a L i : ℕ) {j j' : Fin N} (hjj : j ≠ j')
    (t t' : ℕ) :
    BranchingProcess.wedge (lineW hN a L i j t) (lineW hN a L i j' t')
      = zw hN (a + L + i) := by
  rw [lineW, lineW, BranchingProcess.wedge_append_append,
    BranchingProcess.wedge_cons_cons, if_neg hjj]
  simp

/-- The wedge of lines leaving at different stack depths, the lower one through a
positive letter. -/
lemma wedge_lineW_lt (hN : 0 < N) (a L : ℕ) {i i' : ℕ} (hii : i < i') {j j' : Fin N}
    (hj : 0 < (j : ℕ)) (t t' : ℕ) :
    BranchingProcess.wedge (lineW hN a L i j t) (lineW hN a L i' j' t')
      = zw hN (a + L + i) := by
  have hsplit : lineW hN a L i' j' t'
      = zw hN (a + L + i) ++ ((⟨0, hN⟩ : Fin N)
        :: (List.replicate (i' - i - 1) (⟨0, hN⟩ : Fin N) ++ j' :: List.replicate t' ⟨0, hN⟩)) := by
    rw [lineW]
    have hz : zw hN (a + L + i') = zw hN (a + L + i)
        ++ (⟨0, hN⟩ : Fin N) :: List.replicate (i' - i - 1) ⟨0, hN⟩ := by
      rw [zw, zw]
      rw [show (⟨0, hN⟩ : Fin N) :: List.replicate (i' - i - 1) (⟨0, hN⟩ : Fin N)
          = List.replicate (i' - i) ⟨0, hN⟩ from by
        rw [← List.replicate_succ]
        congr 1
        omega]
      rw [← List.replicate_add]
      congr 1
      omega
    rw [hz]
    simp
  rw [lineW, hsplit, BranchingProcess.wedge_append_append,
    BranchingProcess.wedge_cons_cons, if_neg (by
      intro hcon
      rw [hcon] at hj
      simp at hj)]
  simp

end Pattern

section Pattern

variable {a L m : ℕ}

/-- **The star pattern** of `thm:chain-separation` Step 2 at anchor `a`: `L` unary
ancestors, the stack of arities `ks`, and `L` unary vertices on every leaving line. -/
def PatternAt (hN : 0 < N) (c : GWord N → ℕ) (ks : List ℕ) (a L : ℕ) : Prop :=
  (∀ s, s < L → c (zw hN (a + s)) = 1) ∧
  (∀ i, i < ks.length → c (zw hN (a + L + i)) = ks.getD i 0) ∧
  (∀ i, i < ks.length → ∀ j : Fin N, (j : ℕ) < ks.getD i 0 →
    (0 < (j : ℕ) ∨ i + 1 = ks.length) → ∀ t, t < L →
      c (lineW hN a L i j t) = 1)

/-- The sum of a mapped list over its positions. -/
lemma list_map_sum_eq (f : ℕ → ℕ) (l : List ℕ) :
    (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i 0) := by
  induction l with
  | nil => simp
  | cons k tl ih =>
      rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      omega

/-- A list of positive shifts is no longer than its sum. -/
lemma length_le_sum {l : List ℕ} (h : ∀ k ∈ l, 1 ≤ k) : l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons k tl ih =>
      rw [List.length_cons, List.sum_cons]
      have h1 := h k List.mem_cons_self
      have h2 := ih fun k hk => h k (List.mem_cons_of_mem _ hk)
      omega

/-- The identifiers of the leaving lines: the stack depth and the letter. -/
def linePairs (N : ℕ) (ks : List ℕ) : Finset (ℕ × Fin N) :=
  (Finset.range ks.length).biUnion fun i =>
    ((Finset.univ : Finset (Fin N)).filter
      (fun j : Fin N => (j : ℕ) < ks.getD i 0 ∧ (0 < (j : ℕ) ∨ i + 1 = ks.length))).image
      (fun j => (i, j))

lemma mem_linePairs {ks : List ℕ} {p : ℕ × Fin N} :
    p ∈ linePairs N ks ↔ p.1 < ks.length ∧ (p.2 : ℕ) < ks.getD p.1 0
      ∧ (0 < (p.2 : ℕ) ∨ p.1 + 1 = ks.length) := by
  obtain ⟨i, j⟩ := p
  simp only [linePairs, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', j', ⟨hj1, hj2⟩, rfl, rfl⟩
    exact ⟨hi', hj1, hj2⟩
  · rintro ⟨hi, hj1, hj2⟩
    exact ⟨i, hi, j, ⟨hj1, hj2⟩, rfl, rfl⟩

/-- The number of positive letters below `k`. -/
lemma card_fin_filter_lt_pos {k : ℕ} (hk : k ≤ N) :
    ((Finset.univ : Finset (Fin N)).filter
      (fun j : Fin N => (j : ℕ) < k ∧ 0 < (j : ℕ))).card = k - 1 := by
  have himg : ((Finset.univ : Finset (Fin N)).filter
      (fun j : Fin N => (j : ℕ) < k ∧ 0 < (j : ℕ))).image Fin.val = Finset.Ico 1 k := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ico]
    constructor
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      omega
    · intro hn
      exact ⟨⟨n, by omega⟩, ⟨hn.2, hn.1⟩, rfl⟩
  have := Finset.card_image_of_injective ((Finset.univ : Finset (Fin N)).filter
    (fun j : Fin N => (j : ℕ) < k ∧ 0 < (j : ℕ))) Fin.val_injective
  rw [himg, Nat.card_Ico] at this
  exact this.symm

/-- **The line count**: there are `m + 1` leaving lines. -/
lemma card_linePairs {ks : List ℕ} (hks2 : ∀ k ∈ ks, 2 ≤ k) (hksN : ∀ k ∈ ks, k ≤ N)
    (hne : ks ≠ []) (hsum : (ks.map (fun k => k - 1)).sum = m) :
    (linePairs N ks).card = m + 1 := by
  have hr : 1 ≤ ks.length := by
    cases ks
    · exact absurd rfl hne
    · simp
  have hget : ∀ i, i < ks.length → ks.getD i 0 ∈ ks := fun i hi => by
    rw [List.getD_eq_getElem ks 0 hi]
    exact List.getElem_mem hi
  rw [linePairs, Finset.card_biUnion (by
    intro i hi i' hi' hii
    refine Finset.disjoint_left.mpr fun p hp hp' => ?_
    simp only [Finset.mem_image] at hp hp'
    obtain ⟨j, -, rfl⟩ := hp
    obtain ⟨j', -, hj'⟩ := hp'
    exact hii (congrArg Prod.fst hj').symm)]
  have hrow : ∀ i ∈ Finset.range ks.length,
      (((Finset.univ : Finset (Fin N)).filter
        (fun j : Fin N => (j : ℕ) < ks.getD i 0
          ∧ (0 < (j : ℕ) ∨ i + 1 = ks.length))).image (fun j => (i, j))).card
      = if i + 1 = ks.length then ks.getD i 0 else ks.getD i 0 - 1 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.card_image_of_injective _ (fun j j' h => (Prod.mk.injEq _ _ _ _).mp h |>.2)]
    split_ifs with hlast
    · have hfe : ((Finset.univ : Finset (Fin N)).filter
          (fun j : Fin N => (j : ℕ) < ks.getD i 0
            ∧ (0 < (j : ℕ) ∨ i + 1 = ks.length)))
          = (Finset.univ : Finset (Fin N)).filter
            (fun j : Fin N => (j : ℕ) < ks.getD i 0) := by
        ext j
        simp [hlast]
      rw [hfe]
      exact card_fin_filter_lt (hksN _ (hget i hi))
    · have hfe : ((Finset.univ : Finset (Fin N)).filter
          (fun j : Fin N => (j : ℕ) < ks.getD i 0
            ∧ (0 < (j : ℕ) ∨ i + 1 = ks.length)))
          = (Finset.univ : Finset (Fin N)).filter
            (fun j : Fin N => (j : ℕ) < ks.getD i 0 ∧ 0 < (j : ℕ)) := by
        ext j
        simp [hlast]
      rw [hfe]
      exact card_fin_filter_lt_pos (hksN _ (hget i hi))
  rw [Finset.sum_congr rfl hrow]
  have hsum' : ∑ i ∈ Finset.range ks.length, (ks.getD i 0 - 1) = m := by
    rw [← hsum, list_map_sum_eq]
  have hsplit : ∀ i ∈ Finset.range ks.length,
      (if i + 1 = ks.length then ks.getD i 0 else ks.getD i 0 - 1)
        = (ks.getD i 0 - 1) + (if i = ks.length - 1 then 1 else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h2 := hks2 _ (hget i hi)
    split_ifs <;> omega
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hsum',
    Finset.sum_ite_eq' (Finset.range ks.length) (ks.length - 1) (fun _ => 1),
    if_pos (Finset.mem_range.mpr (by omega))]

end Pattern

section Pattern

variable {a L m : ℕ} {c : GWord N → ℕ} {ks : List ℕ}

/-- The ray is in the sample. -/
lemma zw_mem_sample (hN : 0 < N) (hpos : ∀ v, 1 ≤ c v) (n : ℕ) :
    zw hN n ∈ sample c := by
  have h := append_replicate_mem_sample hN hpos (BranchingProcess.nil_mem_sample c) n
  simpa [zw] using h

/-- The line vertices are in the sample. -/
lemma lineW_mem_sample (hN : 0 < N) (hpos : ∀ v, 1 ≤ c v)
    (hpat : PatternAt hN c ks a L) {i : ℕ} (hi : i < ks.length) {j : Fin N}
    (hj : (j : ℕ) < ks.getD i 0) (t : ℕ) : lineW hN a L i j t ∈ sample c := by
  have h0 : zw hN (a + L + i) ++ [j] ∈ sample c :=
    BranchingProcess.mem_sample_append_singleton.mpr
      ⟨zw_mem_sample hN hpos _, by rw [hpat.2.1 i hi]; exact hj⟩
  have h := append_replicate_mem_sample hN hpos h0 t
  simpa [lineW] using h

/-- The zero letter. -/
lemma eq_zero_letter {hN : 0 < N} {j : Fin N} (h : (j : ℕ) = 0) : j = ⟨0, hN⟩ :=
  Fin.ext h

/-- **The descent**: a sample vertex below the centre within depth `L - 1` is a stack
vertex or a line vertex. -/
lemma pattern_descend (hN : 0 < N)
    (hpat : PatternAt hN c ks a L) (hL : 1 ≤ L) (hr1 : 1 ≤ ks.length) :
    ∀ x, x ∈ sample c → zw hN (a + L) <+: x → x.length ≤ a + L + (L - 1) →
    (∃ n, a + L ≤ n ∧ n ≤ a + L + (ks.length - 1) ∧ x = zw hN n)
      ∨ (∃ i j t, i < ks.length ∧ ((j : Fin N) : ℕ) < ks.getD i 0
        ∧ (0 < (j : ℕ) ∨ i + 1 = ks.length) ∧ t ≤ L - 1 ∧ x = lineW hN a L i j t) := by
  intro x
  induction x using List.reverseRecOn with
  | nil =>
      intro _ hpre _
      have h := hpre.length_le
      rw [zw_length] at h
      simp only [List.length_nil] at h
      omega
  | append_singleton x' jl ih =>
      intro hmem hpre hdep
      by_cases hshort : x'.length < a + L
      · -- the word is the centre itself
        have hlen : (x' ++ [jl]).length = x'.length + 1 := by simp
        have hle := hpre.length_le
        rw [zw_length] at hle
        have hexact : (x' ++ [jl]).length = a + L := by omega
        have hx : x' ++ [jl] = zw hN (a + L) :=
          (hpre.eq_of_length (by rw [zw_length, hexact])).symm
        exact Or.inl ⟨a + L, le_rfl, by omega, hx⟩
      · push Not at hshort
        have hpre' : zw hN (a + L) <+: x' :=
          List.prefix_of_prefix_length_le hpre (List.prefix_append x' [jl])
            (by rw [zw_length]; exact hshort)
        have hmem' : x' ∈ sample c :=
          BranchingProcess.Subtree.mem_of_prefix (List.prefix_append x' [jl]) hmem
        have hdep' : x'.length ≤ a + L + (L - 1) := by
          have : (x' ++ [jl]).length = x'.length + 1 := by simp
          omega
        have hjl : (jl : ℕ) < c x' :=
          (BranchingProcess.mem_sample_append_singleton.mp hmem).2
        rcases ih hmem' hpre' hdep' with ⟨n, hn1, hn2, rfl⟩ | ⟨i, j, t, hi, hj, hv, ht, rfl⟩
        · -- the parent is a stack vertex
          have hilt : n - (a + L) < ks.length := by omega
          have hcx : c (zw hN n) = ks.getD (n - (a + L)) 0 := by
            have := hpat.2.1 (n - (a + L)) hilt
            rwa [show a + L + (n - (a + L)) = n from by omega] at this
          rw [hcx] at hjl
          by_cases hzero : (jl : ℕ) = 0 ∧ n - (a + L) + 1 < ks.length
          · -- continue the stack
            refine Or.inl ⟨n + 1, by omega, by omega, ?_⟩
            rw [eq_zero_letter (hN := hN) hzero.1, zw, zw, ← List.replicate_succ']
          · -- start a line
            have hvalid : 0 < (jl : ℕ) ∨ (n - (a + L)) + 1 = ks.length := by
              rcases Nat.eq_zero_or_pos (jl : ℕ) with h0 | h0
              · refine Or.inr ?_
                rcases Classical.em ((n - (a + L)) + 1 < ks.length) with hlt | hge
                · exact absurd ⟨h0, hlt⟩ hzero
                · omega
              · exact Or.inl h0
            refine Or.inr ⟨n - (a + L), jl, 0, hilt, hjl, hvalid, by omega, ?_⟩
            rw [lineW, show a + L + (n - (a + L)) = n from by omega]
            simp
        · -- the parent is a line vertex
          have hcx : c (lineW hN a L i j t) = 1 := hpat.2.2 i hi j hj hv t (by omega)
          rw [hcx] at hjl
          have hjl0 : jl = ⟨0, hN⟩ := eq_zero_letter (by omega)
          refine Or.inr ⟨i, j, t + 1, hi, hj, hv, ?_, ?_⟩
          · have hlen : (lineW hN a L i j t ++ [jl]).length = a + L + i + 1 + t + 1 := by
              simp
            omega
          · rw [hjl0, lineW, lineW, List.replicate_succ']
            simp

/-- **The rigidity of the pattern**: everything in the sample within `L - 1` of the
centre is an ancestor, a stack vertex, or a line vertex. -/
lemma pattern_classify (hN : 0 < N)
    (hpat : PatternAt hN c ks a L) (hL : 1 ≤ L) (hr1 : 1 ≤ ks.length)
    {x : GWord N} (hmem : x ∈ sample c)
    (hdist : BranchingProcess.treeDist (zw hN (a + L)) x ≤ L - 1) :
    (∃ n, a + L ≤ n ∧ n ≤ a + L + (ks.length - 1) ∧ x = zw hN n)
      ∨ (∃ t, t ≤ L - 1 ∧ x = zw hN (a + L - 1 - t))
      ∨ (∃ i j t, i < ks.length ∧ ((j : Fin N) : ℕ) < ks.getD i 0
        ∧ (0 < (j : ℕ) ∨ i + 1 = ks.length) ∧ t ≤ L - 1 ∧ x = lineW hN a L i j t) := by
  have hadd := BranchingProcess.treeDist_add (zw hN (a + L)) x
  rw [zw_length] at hadd
  have hqx := BranchingProcess.wedge_prefix_right (zw hN (a + L)) x
  have hqc := BranchingProcess.wedge_prefix_left (zw hN (a + L)) x
  have hqz := eq_zw_of_prefix_zw hN hqc
  have hqlen := hqc.length_le
  rw [zw_length] at hqlen
  have hqa : a + 1 ≤ (BranchingProcess.wedge (zw hN (a + L)) x).length := by
    have := hqx.length_le
    omega
  by_cases hcase : (BranchingProcess.wedge (zw hN (a + L)) x).length = a + L
  · -- the centre is a prefix of `x`
    have hctr : zw hN (a + L) <+: x := by
      have : BranchingProcess.wedge (zw hN (a + L)) x = zw hN (a + L) := by
        rw [hqz, hcase]
      rw [← this]
      exact hqx
    have hxlen : x.length ≤ a + L + (L - 1) := by omega
    rcases pattern_descend hN hpat hL hr1 x hmem hctr hxlen with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · -- `x` hangs off a strict ancestor of the centre, which is unary: `x` is on the ray
    have hqlt : (BranchingProcess.wedge (zw hN (a + L)) x).length < a + L := by omega
    have hxq : x = BranchingProcess.wedge (zw hN (a + L)) x := by
      by_contra hne
      have hxlt : (BranchingProcess.wedge (zw hN (a + L)) x).length < x.length :=
        BranchingProcess.length_lt_of_prefix_ne hqx fun h => hne h.symm
      have hclt : (BranchingProcess.wedge (zw hN (a + L)) x).length < (zw hN (a + L)).length := by
        rw [zw_length]
        omega
      have hmismatch := getElem_ne_of_wedge (u := zw hN (a + L)) (v := x) hclt hxlt
      have hctr0 : (zw hN (a + L))[(BranchingProcess.wedge (zw hN (a + L)) x).length]'hclt
          = ⟨0, hN⟩ := List.getElem_replicate ..
      have htake : x.take ((BranchingProcess.wedge (zw hN (a + L)) x).length + 1)
          = BranchingProcess.wedge (zw hN (a + L)) x
            ++ [x[(BranchingProcess.wedge (zw hN (a + L)) x).length]'hxlt] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hxlt,
          ← List.prefix_iff_eq_take.mp hqx]
        rfl
      have hmemq : BranchingProcess.wedge (zw hN (a + L)) x
          ++ [x[(BranchingProcess.wedge (zw hN (a + L)) x).length]'hxlt] ∈ sample c := by
        rw [← htake]
        exact BranchingProcess.Subtree.mem_of_prefix (List.take_prefix _ x) hmem
      have hlt1 := (BranchingProcess.mem_sample_append_singleton.mp hmemq).2
      have hcq : c (BranchingProcess.wedge (zw hN (a + L)) x) = 1 := by
        have hs := hpat.1 ((BranchingProcess.wedge (zw hN (a + L)) x).length - a) (by omega)
        rw [show a + ((BranchingProcess.wedge (zw hN (a + L)) x).length - a)
            = (BranchingProcess.wedge (zw hN (a + L)) x).length from by omega] at hs
        rwa [← hqz] at hs
      rw [hcq] at hlt1
      exact hmismatch (by
        rw [hctr0]
        exact (eq_zero_letter (hN := hN) (by omega)).symm)
    refine Or.inr (Or.inl ⟨a + L - 1 - (BranchingProcess.wedge (zw hN (a + L)) x).length,
      by omega, ?_⟩)
    have hidx : (BranchingProcess.wedge (zw hN (a + L)) x).length
        = a + L - 1 - (a + L - 1
          - (BranchingProcess.wedge (zw hN (a + L)) x).length) := by omega
    exact hxq.trans (hqz.trans (congrArg (zw hN) hidx))

end Pattern

section Pattern

variable {a L m : ℕ} {c : GWord N → ℕ} {ks : List ℕ}

/-- The line function of the pattern star: the ray towards the root for the arriving
end, the initial segments for a leaving end. -/
def pLine (hN : 0 < N) (a L : ℕ) (e : GWord N) (t : ℕ) : GWord N :=
  if e.length = a then zw hN (a + L - 1 - t) else e.take (e.length - (L - 1) + t)

/-- The offset of a line: zero for the arriving end, the stack depth otherwise. -/
def pOff (a L : ℕ) (e : GWord N) : ℕ :=
  if e.length = a then 0 else e.length - (a + 2 * L)

/-- The boundary ends of the pattern star. -/
def pEnds (hN : 0 < N) (a L : ℕ) (ks : List ℕ) : Finset (GWord N) :=
  insert (zw hN a) ((linePairs N ks).image (fun p => lineW hN a L p.1 p.2 (L - 1)))

lemma pLine_arr (hN : 0 < N) (t : ℕ) :
    pLine hN a L (zw hN a) t = zw hN (a + L - 1 - t) := by
  rw [pLine, if_pos (zw_length hN a)]

lemma pOff_arr (hN : 0 < N) : pOff a L (zw hN a) = 0 := by
  rw [pOff, if_pos (zw_length hN a)]

lemma pLine_leaving (hN : 0 < N) (hL : 1 ≤ L) (i : ℕ) (j : Fin N) {t : ℕ}
    (ht : t ≤ L - 1) :
    pLine hN a L (lineW hN a L i j (L - 1)) t = lineW hN a L i j t := by
  rw [pLine, if_neg (by rw [lineW_length]; omega), lineW_length,
    show a + L + i + 1 + (L - 1) - (L - 1) + t = a + L + i + 1 + t from by omega,
    lineW_take hN a L i j ht]

lemma pOff_leaving (hN : 0 < N) (hL : 1 ≤ L) (i : ℕ) (j : Fin N) :
    pOff a L (lineW hN a L i j (L - 1)) = i := by
  rw [pOff, if_neg (by rw [lineW_length]; omega), lineW_length]
  omega

lemma mem_pEnds {hN : 0 < N} {e : GWord N} :
    e ∈ pEnds hN a L ks ↔ e = zw hN a
      ∨ ∃ i j, (i, j) ∈ linePairs N ks ∧ e = lineW hN a L i j (L - 1) := by
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact Or.inl rfl
    · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨p.1, p.2, hp, hpe.symm⟩
  · rintro (rfl | ⟨i, j, hp, rfl⟩)
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(i, j), hp, rfl⟩)

/-- Distinct pairs give distinct ends. -/
lemma lineW_inj (hN : 0 < N) {i i' t : ℕ} {j j' : Fin N}
    (h : lineW hN a L i j t = lineW hN a L i' j' t) : i = i' ∧ j = j' := by
  have hlen := congrArg List.length h
  rw [lineW_length, lineW_length] at hlen
  have hii : i = i' := by omega
  subst hii
  rw [lineW, lineW] at h
  have := List.append_cancel_left h
  rw [List.cons.injEq] at this
  exact ⟨rfl, this.1⟩

/-- **The end count**: the star has `m + 2` boundary ends. -/
lemma card_pEnds (hN : 0 < N) (hks2 : ∀ k ∈ ks, 2 ≤ k) (hksN : ∀ k ∈ ks, k ≤ N)
    (hne : ks ≠ []) (hsum : (ks.map (fun k => k - 1)).sum = m) (hL : 1 ≤ L) :
    (pEnds hN a L ks).card = m + 2 := by
  rw [pEnds, Finset.card_insert_of_notMem (by
    intro hcon
    rw [Finset.mem_image] at hcon
    obtain ⟨p, -, hp⟩ := hcon
    have := congrArg List.length hp
    rw [lineW_length, zw_length] at this
    omega)]
  rw [Finset.card_image_of_injOn (fun p _ q _ hpq => by
    obtain ⟨h1, h2⟩ := lineW_inj hN hpq
    exact Prod.ext h1 h2)]
  rw [card_linePairs hks2 hksN hne hsum]

end Pattern

section Pattern

variable {a L m : ℕ} {c : GWord N → ℕ} {ks : List ℕ}

/-- **The star of the coordinate pattern**: the pattern of `thm:chain-separation`
Step 2 realises an `L`-star of excess `m` at the vertex `0^(a+L)` of the sample. -/
def patternStar (hN : 0 < N) (hpos : ∀ v, 1 ≤ c v) (hpat : PatternAt hN c ks a L)
    (hks2 : ∀ k ∈ ks, 2 ≤ k) (hksN : ∀ k ∈ ks, k ≤ N) (hne : ks ≠ [])
    (hsum : (ks.map (fun k => k - 1)).sum = m) (hL : 1 ≤ L) :
    Star N (fun w : GWord N => w ∈ sample c) m L := by
  have hr1 : 1 ≤ ks.length := by
    cases ks
    · exact absurd rfl hne
    · simp
  have hrm : ks.length ≤ m := by
    have h1 : (ks.map (fun k => k - 1)).length ≤ (ks.map (fun k => k - 1)).sum :=
      length_le_sum (by
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨k, hk, rfl⟩ := hy
        have := hks2 k hk
        omega)
    rw [List.length_map, hsum] at h1
    exact h1
  have hget : ∀ i, i < ks.length → ks.getD i 0 ∈ ks := fun i hi => by
    rw [List.getD_eq_getElem ks 0 hi]
    exact List.getElem_mem hi
  refine
  { ctr := zw hN (a + L)
    ctrMem := zw_mem_sample hN hpos _
    ends := pEnds hN a L ks
    card_ends := card_pEnds hN hks2 hksN hne hsum hL
    line := pLine hN a L
    off := pOff a L
    off_le := ?_
    lineMem := ?_
    line_dist := ?_
    line_end := ?_
    line_pair := ?_
    onGeo := ?_
    line_seg_dist := ?_
    onGeoSeg := ?_
    classify := ?_ }
  · -- off_le
    intro e he
    rcases mem_pEnds.mp he with rfl | ⟨i, j, hp, rfl⟩
    · rw [pOff_arr]
      omega
    · rw [pOff_leaving hN hL]
      have := (mem_linePairs.mp hp).1
      omega
  · -- lineMem
    intro e he t ht
    rcases mem_pEnds.mp he with rfl | ⟨i, j, hp, rfl⟩
    · rw [pLine_arr]
      exact zw_mem_sample hN hpos _
    · rw [pLine_leaving hN hL i j ht]
      obtain ⟨hi, hj, -⟩ := mem_linePairs.mp hp
      exact lineW_mem_sample hN hpos hpat hi hj t
  · -- line_dist
    intro e he t ht
    rcases mem_pEnds.mp he with rfl | ⟨i, j, hp, rfl⟩
    · rw [pLine_arr, pOff_arr, BranchingProcess.treeDist_comm,
        treeDist_zw_zw hN (by omega : a + L - 1 - t ≤ a + L)]
      omega
    · rw [pLine_leaving hN hL i j ht, pOff_leaving hN hL, treeDist_ctr_lineW]
      omega
  · -- line_end
    intro e he
    rcases mem_pEnds.mp he with rfl | ⟨i, j, hp, rfl⟩
    · rw [pLine_arr]
      congr 1
      omega
    · rw [pLine_leaving hN hL i j le_rfl]
  · -- line_pair
    intro e he e' he' hnee t ht t' ht'
    rcases mem_pEnds.mp he with rfl | ⟨i, j, hp, rfl⟩ <;>
      rcases mem_pEnds.mp he' with heq | ⟨i', j', hp', heq⟩
    · exact absurd heq.symm hnee
    · subst heq
      rw [pLine_arr, pLine_leaving hN hL i' j' ht',
        BranchingProcess.treeDist_of_prefix (zw_prefix_lineW hN (by omega) j' t'),
        lineW_length, zw_length]
      omega
    · subst heq
      rw [pLine_leaving hN hL i j ht, pLine_arr, BranchingProcess.treeDist_comm,
        BranchingProcess.treeDist_of_prefix (zw_prefix_lineW hN (by omega) j t),
        lineW_length, zw_length]
      omega
    · subst heq
      obtain ⟨hi, hj, hv⟩ := mem_linePairs.mp hp
      obtain ⟨hi', hj', hv'⟩ := mem_linePairs.mp hp'
      rw [pLine_leaving hN hL i j ht, pLine_leaving hN hL i' j' ht']
      rcases Nat.lt_trichotomy i i' with hii | hii | hii
      · have hjpos : 0 < (j : ℕ) := by
          rcases hv with h | h
          · exact h
          · omega
        have hadd := BranchingProcess.treeDist_add (lineW hN a L i j t)
          (lineW hN a L i' j' t')
        rw [wedge_lineW_lt hN a L hii hjpos, lineW_length, lineW_length,
          zw_length] at hadd
        omega
      · subst hii
        have hjj : j ≠ j' := by
          intro hcon
          exact hnee (by rw [hcon])
        have hadd := BranchingProcess.treeDist_add (lineW hN a L i j t)
          (lineW hN a L i j' t')
        rw [wedge_lineW_ne hN a L i hjj, lineW_length, lineW_length,
          zw_length] at hadd
        omega
      · have hjpos : 0 < (j' : ℕ) := by
          rcases hv' with h | h
          · exact h
          · omega
        have hadd := BranchingProcess.treeDist_add (lineW hN a L i' j' t')
          (lineW hN a L i j t)
        rw [wedge_lineW_lt hN a L hii hjpos, lineW_length, lineW_length,
          zw_length] at hadd
        rw [BranchingProcess.treeDist_comm]
        omega
  · -- onGeo
    intro e he t ht x hx hadd
    rcases mem_pEnds.mp he with rfl | ⟨i, j, hp, rfl⟩
    · rw [pLine_arr] at hadd
      have hzc : zw hN (a + L - 1 - t) <+: zw hN (a + L) := zw_prefix hN (by omega)
      have hwedge : BranchingProcess.wedge (zw hN (a + L)) (zw hN (a + L - 1 - t))
          = zw hN (a + L - 1 - t) := by
        rw [BranchingProcess.wedge_comm]
        exact BranchingProcess.wedge_of_prefix hzc
      rcases prefix_of_dist_add hadd with ⟨hxc, hqx⟩ | ⟨hxz, hqx⟩
      · rw [hwedge] at hqx
        have hxz : x = zw hN x.length := eq_zw_of_prefix_zw hN hxc
        have h1 := hqx.length_le
        have h2 := hxc.length_le
        rw [zw_length] at h1
        rw [zw_length] at h2
        by_cases hfull : x.length = a + L
        · refine Or.inl ?_
          have : x = zw hN (a + L) := by rw [hxz, hfull]
          rw [this, BranchingProcess.treeDist_self]
          omega
        · refine Or.inr ⟨a + L - 1 - x.length, by omega, ?_⟩
          rw [pLine_arr]
          exact hxz.trans (congrArg (zw hN) (by omega))
      · rw [hwedge] at hqx
        refine Or.inr ⟨t, le_rfl, ?_⟩
        rw [pLine_arr]
        exact prefix_antisymm hxz hqx
    · obtain ⟨hi, hj, hv⟩ := mem_linePairs.mp hp
      rw [pLine_leaving hN hL i j ht] at hadd
      have hcz : zw hN (a + L) <+: lineW hN a L i j t := zw_prefix_lineW hN (by omega) j t
      have hwedge : BranchingProcess.wedge (zw hN (a + L)) (lineW hN a L i j t)
          = zw hN (a + L) := BranchingProcess.wedge_of_prefix hcz
      rcases prefix_of_dist_add hadd with ⟨hxc, hqx⟩ | ⟨hxz, hqx⟩
      · rw [hwedge] at hqx
        refine Or.inl ?_
        have : x = zw hN (a + L) := prefix_antisymm hqx hxc |>.symm
        rw [this, BranchingProcess.treeDist_self]
        omega
      · rw [hwedge] at hqx
        have h1 := hqx.length_le
        have h2 := hxz.length_le
        rw [zw_length] at h1
        rw [lineW_length] at h2
        have hxt : x = (lineW hN a L i j t).take x.length :=
          List.prefix_iff_eq_take.mp hxz
        by_cases hcase : x.length ≤ a + L + i
        · refine Or.inl ?_
          have hxz2 : x = zw hN x.length := by
            conv_lhs => rw [hxt]
            rw [lineW, List.take_append_of_le_length (by rw [zw_length]; omega),
              zw, List.take_replicate, min_eq_left (by omega : x.length ≤ a + L + i),
              ← zw]
          rw [hxz2, treeDist_zw_zw hN (by omega : a + L ≤ x.length)]
          omega
        · refine Or.inr ⟨x.length - (a + L + i + 1), by omega, ?_⟩
          rw [pLine_leaving hN hL i j (by omega : x.length - (a + L + i + 1) ≤ L - 1)]
          conv_lhs => rw [hxt, show x.length
            = a + L + i + 1 + (x.length - (a + L + i + 1)) from by omega]
          rw [lineW_take hN a L i j (by omega)]
  · -- line_seg_dist
    intro e he t t' htt ht'
    rcases mem_pEnds.mp he with rfl | ⟨i, j, hp, rfl⟩
    · rw [pLine_arr, pLine_arr, BranchingProcess.treeDist_comm,
        treeDist_zw_zw hN (by omega : a + L - 1 - t' ≤ a + L - 1 - t)]
      omega
    · rw [pLine_leaving hN hL i j (le_trans htt ht'), pLine_leaving hN hL i j ht',
        treeDist_lineW_lineW hN a L i j htt]
  · -- onGeoSeg
    intro e he t t' htt ht' x hx hadd
    rcases mem_pEnds.mp he with rfl | ⟨i, j, hp, rfl⟩
    · rw [pLine_arr, pLine_arr] at hadd
      have hvu : zw hN (a + L - 1 - t') <+: zw hN (a + L - 1 - t) :=
        zw_prefix hN (by omega)
      have hwedge : BranchingProcess.wedge (zw hN (a + L - 1 - t))
          (zw hN (a + L - 1 - t')) = zw hN (a + L - 1 - t') := by
        rw [BranchingProcess.wedge_comm]
        exact BranchingProcess.wedge_of_prefix hvu
      rcases prefix_of_dist_add hadd with ⟨hxu, hqx⟩ | ⟨hxv, hqx⟩
      · rw [hwedge] at hqx
        have hxz : x = zw hN x.length := eq_zw_of_prefix_zw hN hxu
        have h1 := hqx.length_le
        have h2 := hxu.length_le
        rw [zw_length] at h1
        rw [zw_length] at h2
        refine ⟨a + L - 1 - x.length, by omega, by omega, ?_⟩
        rw [pLine_arr]
        exact hxz.trans (congrArg (zw hN) (by omega))
      · rw [hwedge] at hqx
        refine ⟨t', htt, le_rfl, ?_⟩
        rw [pLine_arr]
        exact prefix_antisymm hxv hqx
    · rw [pLine_leaving hN hL i j (le_trans htt ht'), pLine_leaving hN hL i j ht']
        at hadd
      have huv : lineW hN a L i j t <+: lineW hN a L i j t' :=
        lineW_prefix hN a L i j htt
      have hwedge : BranchingProcess.wedge (lineW hN a L i j t)
          (lineW hN a L i j t') = lineW hN a L i j t :=
        BranchingProcess.wedge_of_prefix huv
      rcases prefix_of_dist_add hadd with ⟨hxu, hqx⟩ | ⟨hxv, hqx⟩
      · rw [hwedge] at hqx
        refine ⟨t, le_rfl, htt, ?_⟩
        rw [pLine_leaving hN hL i j (le_trans htt ht')]
        exact prefix_antisymm hxu hqx
      · rw [hwedge] at hqx
        have h1 := hqx.length_le
        have h2 := hxv.length_le
        rw [lineW_length] at h1
        rw [lineW_length] at h2
        refine ⟨x.length - (a + L + i + 1), by omega, by omega, ?_⟩
        rw [pLine_leaving hN hL i j (by omega : x.length - (a + L + i + 1) ≤ L - 1)]
        conv_lhs => rw [List.prefix_iff_eq_take.mp hxv, show x.length
          = a + L + i + 1 + (x.length - (a + L + i + 1)) from by omega]
        rw [lineW_take hN a L i j (by omega)]
  · -- classify
    intro x hx hdist
    rcases pattern_classify hN hpat hL hr1 hx hdist with
      ⟨n, hn1, hn2, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨i, j, t, hi, hj, hv, ht, rfl⟩
    · refine Or.inl ?_
      rw [treeDist_zw_zw hN hn1]
      omega
    · refine Or.inr ⟨zw hN a, mem_pEnds.mpr (Or.inl rfl), t, ht, ?_⟩
      rw [pLine_arr]
    · refine Or.inr ⟨lineW hN a L i j (L - 1),
        mem_pEnds.mpr (Or.inr ⟨i, j, mem_linePairs.mpr ⟨hi, hj, hv⟩, rfl⟩), t, ht, ?_⟩
      rw [pLine_leaving hN hL i j ht]

end Pattern

end ChainClasses
