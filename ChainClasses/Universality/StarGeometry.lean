import ChainClasses.Universality.GeneralObstructions

/-!
The geometry behind `thm:chain-separation` (`prelims.tex`): prefix and wedge helpers, the
vertex at a prescribed distance on a geodesic, the median of three words, walks,
betweenness and stability over `wordGraphN`, extension beyond a vertex away from a base
point, and the spheres of a sample as finite sets with their recursion.  The separation
argument itself is `StarSeparation`.
-/

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

end ChainClasses
