import ChainClasses.General.GeneralCascade
import ChainClasses.General.GeneralShapeIID
import ChainClasses.General.GeneralNeck
import ChainClasses.Bushy.Trichotomy
import BranchingProcess.Geometry
import BranchingProcess.Harris
import Mathlib.Data.Set.Finite.List

/-!
`thm:regime-obstructions-general` of `trichotomy.tex`: the regimes of an offspring
law of bounded support against the obstructions, on the graph footing of
`BranchingProcess.Geometry`.

Everything is stated for the graph `gSampleGraph c = wordGraphN (· ∈ sample c)` of
the sample tree of an offspring field `c : GWord N → ℕ`, almost surely under the
conditioned law `survivalMeasure θ`.  The deterministic layer mirrors
`Trichotomy.lean`, `Hairs.lean`, `ThreeRays.lean` and `Converse.lean` over words in
`Fin N`, the rays being chains of children rather than the chain-letter descents of
the binary case.  The probabilistic layer reads the skeleton through the rank-indexed
subfields `bushAt` and `neckIter` of the Harris decomposition, which `neckVertex`
places at ambient skeleton vertices, and runs every clause through one scheme: a
law-preserving step of the sample space and a root event of positive mass independent
of the stepped field fail along the first `k + 1` iterates with probability at most
`(1 - p)^(k + 1)`, so some iterate realises the event almost surely.

* `wordGraphN_connected`, `wordGraphN_isBridge`, `wordGraphN_isTree`: the graph of a
  nonempty prefix-closed set of words over `Fin N` is a tree.
* `HasThreeRaysN`, `not_quasiIsometric_rayGraph_of_threeRaysN`, `NearLineN`,
  `UnboundedHairsN`, `not_quasiIsometric_of_hairsN_of_nearLineN`, `HasThinBallsG`,
  `not_quasiIsometric_binary_of_thinBalls`, `HasThinBallsN`,
  `not_quasiIsometric_binary_of_thinBallsN`, `not_quasiIsometric_of_thinBallsN_of_binary`:
  **the obstructions of `thm:three-rays`, `thm:hair-separation` and
  `thm:bottleneck`** in the forms the general assembly consumes.
* `IsChain`, `exists_chain_of_forall_child`, `isRayN_of_chain`, `chainFrom`, `upChain`,
  `treeDist_chain_upChain`: chains of children as rays, the ray climbing to a split and
  descending a chain out of its other child, and the distances between them.
* `hasThreeRaysN_of_splits`: **`thm:regime-obstructions-general`
  (`it:gen-obstr-rays`), the deterministic form**: three rays out of a split
  below a split.
* `exists_isLine_throughN`, `exists_divergeFin`, `nearLineN_of_split`:
  **`thm:regime-obstructions-general` (`it:gen-obstr-lines`), the deterministic
  form**: in a tree without leaves every vertex lies within the depth of a split of a
  line.
* `exists_componentCompl_coneN`, `exists_isHair_coneN`, `unboundedHairsN_of_deep_cones`:
  **`thm:regime-obstructions-general` (`it:gen-obstr-hair`), the deterministic
  form**: a finite cone above a child is a hair.
* `ball_subset_neck`, `hasThinBallsN_of_necks`: **`thm:regime-obstructions-general`
  (`it:gen-obstr-thin`), the deterministic form**: the midpoint of a neck of
  length `2ℓ` has a thin ball.
* `iterFail`, `measure_iterFail_le`, `ae_exists_iterate_mem`: the iteration scheme.
* `mem_skeleton_ambSub_iff`, `gSampleGraph`, `exists_two_skeleton_children`, `firstSurvivor`, `neckVertex`, `neckVertex_spec`,
  `isChain_neckVertex`, `exists_dyingAt_zero_eq_ambSub`: the rank-indexed subfields of
  the Harris decomposition at ambient skeleton vertices.
* `skeletonWeight_top_pos`, `skeletonWeight_one_pos`, `skeletonWeight_one_lt_one_of_top`,
  `sum_ofReal_skeletonWeight`: `θ̃_J > 0`, `θ̃₁ > 0` and `θ̃₁ < 1` at every extinction
  probability once `θ_J > 0`, `θ₁ > 0` and `J ≥ 2`, and the weights sum to one.
* `ae_survives`, `survivalMeasure_bushAt_zero_preimage`,
  `survivalMeasure_neckIter_preimage`: the neck descent preserves the conditioned law.
* `ae_gArity_ge_two`, `ae_gArity_gSplitBush_ge_two`, `hasThreeRaysN_sample`,
  `threeRays_ae`, `threeRays_ae_of_top`:
  **`thm:regime-obstructions-general` (`it:gen-obstr-rays`)**.
* `ae_forall_pos_of_zero`, `nearLineN_sample`, `nearLine_gSample_ae`:
  **`thm:regime-obstructions-general` (`it:gen-obstr-lines`)**.
* `ae_exists_neck`, `hasThinBallsN_sample`, `thinBalls_gSample_ae`:
  **`thm:regime-obstructions-general` (`it:gen-obstr-thin`)**.
* `deepEvent`, `bushMeasure_deepEvent_pos`, `hairEvent`, `hairMass_ne_zero`,
  `survivalMeasure_hairEvent_inter`, `unboundedHairsN_sample`,
  `unbounded_hairs_gSample_ae`:
  **`thm:regime-obstructions-general` (`it:gen-obstr-hair`)**.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped ENNReal
open BranchingProcess (Offspring QuasiIsometric IsRay IsLine IsHair rayGraph sample
  survivalMeasure Survives survivors skeletonDegree skeleton bushAt skelSub bushMeasure
  decorationEvent decorationMass dyingAt)

variable {J N : ℕ}

/-! ### The graph of a set of words over `Fin N` is a tree -/

section TreeN

variable {T : BranchingProcess.Word N → Prop}

/-- `BranchingProcess.treeDist` is the graph metric of the parent-child adjacency: the
words at distance one are exactly a word and one of its children. -/
lemma treeDistN_eq_one_iff {u v : BranchingProcess.Word N} :
    BranchingProcess.treeDist u v = 1 ↔ (∃ j, v = u ++ [j]) ∨ (∃ j, u = v ++ [j]) := by
  constructor
  · intro h
    have h1 := BranchingProcess.treeDist_add u v
    have h2 := BranchingProcess.wedge_length_le_left u v
    have h3 := BranchingProcess.wedge_length_le_right u v
    rcases Nat.lt_or_ge (BranchingProcess.wedge u v).length u.length with hlt | hge
    · have hv : BranchingProcess.wedge u v = v :=
        (BranchingProcess.wedge_prefix_right u v).eq_of_length (by omega)
      obtain ⟨s, hs⟩ : v <+: u := hv ▸ BranchingProcess.wedge_prefix_left u v
      have hlen : s.length = 1 := by
        have := congrArg List.length hs
        simp only [List.length_append] at this
        omega
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
      exact Or.inr ⟨b, hs.symm⟩
    · have hu : BranchingProcess.wedge u v = u :=
        (BranchingProcess.wedge_prefix_left u v).eq_of_length (by omega)
      obtain ⟨s, hs⟩ : u <+: v := hu ▸ BranchingProcess.wedge_prefix_right u v
      have hlen : s.length = 1 := by
        have := congrArg List.length hs
        simp only [List.length_append] at this
        omega
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
      exact Or.inl ⟨b, hs.symm⟩
  · rintro (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact BranchingProcess.treeDist_append_singleton u b
    · rw [BranchingProcess.treeDist_comm]
      exact BranchingProcess.treeDist_append_singleton v b

/-- The wedge of a vertex of a prefix-closed set with any word is one of its vertices. -/
lemma wedgeN_mem (hT : PrefixClosedN T) {u v : BranchingProcess.Word N} (hu : T u) :
    T (BranchingProcess.wedge u v) :=
  hT (BranchingProcess.wedge_prefix_left u v) hu

/-- **The graph of a nonempty prefix-closed set is connected.** -/
theorem wordGraphN_connected (hT : PrefixClosedN T)
    (hne : Nonempty {w : BranchingProcess.Word N // T w}) : (wordGraphN T).Connected := by
  obtain ⟨v0⟩ := hne
  haveI : Nonempty {w : BranchingProcess.Word N // T w} := ⟨v0⟩
  refine ⟨fun u v => ?_⟩
  have hw : T (BranchingProcess.wedge u.1 v.1) := wedgeN_mem hT u.2
  obtain ⟨p, -⟩ := exists_walkN_of_prefix hT
    (u.1.length - (BranchingProcess.wedge u.1 v.1).length)
    ⟨BranchingProcess.wedge u.1 v.1, hw⟩ u (BranchingProcess.wedge_prefix_left u.1 v.1) rfl
  obtain ⟨q, -⟩ := exists_walkN_of_prefix hT
    (v.1.length - (BranchingProcess.wedge u.1 v.1).length)
    ⟨BranchingProcess.wedge u.1 v.1, hw⟩ v (BranchingProcess.wedge_prefix_right u.1 v.1) rfl
  exact ⟨p.reverse.append q⟩

/-- The descendants of a vertex are separated from the rest by the edge above it. -/
lemma eq_of_adjN_of_prefix {x y z z' : {w : BranchingProcess.Word N // T w}} {b : Fin N}
    (hxy : y.1 = x.1 ++ [b]) (hz : y.1 <+: z.1) (hz' : ¬ y.1 <+: z'.1)
    (hadj : (wordGraphN T).Adj z z') : z = y ∧ z' = x := by
  rcases treeDistN_eq_one_iff.mp hadj with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact absurd (hc ▸ hz.trans (List.prefix_append z.1 [c])) hz'
  · have hz'p : z'.1 <+: z.1 := hc ▸ List.prefix_append z'.1 [c]
    have hlen : z.1.length = z'.1.length + 1 := by rw [hc]; simp
    have hylen : z'.1.length < y.1.length := by
      by_contra hcon
      exact hz' (List.prefix_of_prefix_length_le hz hz'p (by omega))
    have hyz : y.1.length = z.1.length := by have := hz.length_le; omega
    have hzy : z.1 = y.1 := (hz.eq_of_length hyz).symm
    have hzx : z'.1 = x.1 := by
      have : z'.1 ++ [c] = x.1 ++ [b] := by rw [← hc, hzy, hxy]
      exact (List.append_inj this (by
        have hxlen : x.1.length + 1 = y.1.length := by rw [hxy]; simp
        omega)).1
    exact ⟨Subtype.ext hzy, Subtype.ext hzx⟩

/-- Walks in the graph with the edge above `y` removed stay among the descendants of
`y` once they start there. -/
lemma prefix_of_walkN_deleteEdges {x y : {w : BranchingProcess.Word N // T w}} {b : Fin N}
    (hxy : y.1 = x.1 ++ [b]) {z z' : {w : BranchingProcess.Word N // T w}}
    (p : ((wordGraphN T).deleteEdges {s(x, y)}).Walk z z') (hz : y.1 <+: z.1) :
    y.1 <+: z'.1 := by
  induction p with
  | nil => exact hz
  | @cons a c d hac _ ih =>
      refine ih ?_
      by_contra hcon
      rw [deleteEdges_adj] at hac
      obtain ⟨rfl, rfl⟩ := eq_of_adjN_of_prefix hxy hz hcon hac.1
      exact hac.2 (by simp [Sym2.eq_swap])

/-- **Every edge is a bridge.** -/
theorem wordGraphN_isBridge {u v : {w : BranchingProcess.Word N // T w}}
    (h : (wordGraphN T).Adj u v) : (wordGraphN T).IsBridge s(u, v) := by
  suffices hkey : ∀ x y : {w : BranchingProcess.Word N // T w}, (∃ b, y.1 = x.1 ++ [b]) →
      (wordGraphN T).IsBridge s(x, y) by
    rcases treeDistN_eq_one_iff.mp h with hb | hb
    · exact hkey u v hb
    · rw [Sym2.eq_swap]
      exact hkey v u hb
  rintro x y ⟨b, hxy⟩
  rw [isBridge_iff]
  rintro ⟨p⟩
  have hx : ¬ y.1 <+: x.1 := by
    intro hcon
    have := hcon.length_le
    rw [hxy] at this
    simp at this
  exact hx (prefix_of_walkN_deleteEdges hxy p.reverse (List.prefix_refl _))

/-- **The graph of a nonempty prefix-closed set of words over `Fin N` is a tree.** -/
theorem wordGraphN_isTree (hT : PrefixClosedN T)
    (hne : Nonempty {w : BranchingProcess.Word N // T w}) : (wordGraphN T).IsTree where
  connected := wordGraphN_connected hT hne
  isAcyclic := isAcyclic_iff_forall_adj_isBridge.mpr fun _ _ h => wordGraphN_isBridge h

end TreeN

/-! ### The three obstructions for sets of words over `Fin N` -/

section Obstructions

variable {T : BranchingProcess.Word N → Prop}

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-rays`)**, in the form
`thm:three-rays` consumes: three rays out of one vertex, pairwise meeting only there. -/
def HasThreeRaysN (T : BranchingProcess.Word N → Prop) : Prop :=
  ∃ (v : {w : BranchingProcess.Word N // T w})
    (ray : Fin 3 → ℕ → {w : BranchingProcess.Word N // T w}),
    (∀ i, IsRay (wordGraphN T) (ray i)) ∧ (∀ i, ray i 0 = v) ∧
      ∀ i j, i ≠ j → ∀ m n, ray i m = ray j n → ray i m = v

/-- **`thm:three-rays` for a set of words over `Fin N`.** -/
theorem not_quasiIsometric_rayGraph_of_threeRaysN (hT : PrefixClosedN T)
    (h : HasThreeRaysN T) : ¬ QuasiIsometric (wordGraphN T) rayGraph := by
  obtain ⟨v, ray, hray, hbase, hmeet⟩ := h
  exact BranchingProcess.not_quasiIsometric_rayGraph (wordGraphN_isTree hT ⟨v⟩) hray hbase hmeet

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-lines`)**, in the form
`thm:hair-separation` consumes: every vertex lies within a bounded distance of a
line. -/
def NearLineN (T : BranchingProcess.Word N → Prop) : Prop :=
  ∃ R : ℕ, ∀ u : {w : BranchingProcess.Word N // T w},
    ∃ (l : ℤ → {w : BranchingProcess.Word N // T w}) (k : ℤ),
      IsLine (wordGraphN T) l ∧ (wordGraphN T).dist u (l k) ≤ R

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-hair`)**, in the form
`thm:hair-separation` consumes: hairs of unbounded depth. -/
def UnboundedHairsN (T : BranchingProcess.Word N → Prop) : Prop :=
  ∀ n : ℕ, ∃ (c : {w : BranchingProcess.Word N // T w})
    (P : Set {w : BranchingProcess.Word N // T w}) (h : ℕ),
    n < h ∧ IsHair (wordGraphN T) c P h

/-- **`thm:hair-separation` for two sets of words over `Fin N`.** -/
theorem not_quasiIsometric_of_hairsN_of_nearLineN {N' : ℕ}
    {T' : BranchingProcess.Word N' → Prop} (hT : PrefixClosedN T) (hT' : PrefixClosedN T')
    (hne : T []) (hne' : T' []) (hhair : UnboundedHairsN T) (hline : NearLineN T') :
    ¬ QuasiIsometric (wordGraphN T) (wordGraphN T') := by
  obtain ⟨R, hR⟩ := hline
  exact BranchingProcess.not_quasiIsometric_of_hair_of_line (R := R)
    (wordGraphN_isTree hT ⟨⟨[], hne⟩⟩) (wordGraphN_isTree hT' ⟨⟨[], hne'⟩⟩) hhair hR

/-- The hypothesis of `thm:bottleneck` for a graph: at every radius `ℓ` some ball of
radius `ℓ` is covered by `2ℓ + 1` vertices, as it is when the ball is a segment of
`ℤ`. -/
def HasThinBallsG {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ℓ : ℕ, ∃ (v : V) (S : Finset V), S.card ≤ 2 * ℓ + 1 ∧ ∀ x, G.dist x v ≤ ℓ → x ∈ S

/-- The binary tree `𝔹` as a graph. -/
abbrev binaryGraph : SimpleGraph {w : Word // (fun _ : Word ↦ True) w} :=
  wordGraph (fun _ : Word ↦ True)

/-- **`thm:bottleneck` on the graph footing**: a graph with a thin ball at every radius
is not quasi-isometric to the binary tree.  The count runs on the sphere of radius `R`
around the image of the thin centre: coarse density picks a preimage for each of its
`2^R` vertices, the lower quasi-isometry bound confines those preimages to the thin
ball, and two vertices of the sphere sharing a preimage agree off their last `K`
letters, so a fibre has at most `2^K` elements. -/
theorem not_quasiIsometric_binary_of_thinBalls {V : Type*} {G : SimpleGraph V}
    (hG : HasThinBallsG G) : ¬ QuasiIsometric G binaryGraph := by
  classical
  rintro ⟨K₀, f, hqi₀⟩
  have hmono : ∀ {K K' : ℕ}, K ≤ K' → BranchingProcess.IsQIWith K G binaryGraph f →
      BranchingProcess.IsQIWith K' G binaryGraph f := by
    intro K K' h hf
    refine ⟨fun x y ↦ ?_, fun x y ↦ ?_, fun y ↦ ?_⟩
    · exact le_trans (hf.upper x y) (Nat.add_le_add (Nat.mul_le_mul_right _ h) h)
    · exact le_trans (hf.lower x y) (Nat.add_le_add (Nat.mul_le_mul_right _ h) (Nat.mul_le_mul h h))
    · obtain ⟨x, hx⟩ := hf.dense y
      exact ⟨x, le_trans hx h⟩
  obtain ⟨K, -, hqi⟩ : ∃ K, 1 ≤ K ∧ BranchingProcess.IsQIWith K G binaryGraph f :=
    ⟨K₀ + 1, Nat.le_add_left 1 K₀, hmono (Nat.le_succ K₀) hqi₀⟩
  obtain ⟨R', hR'⟩ := exists_two_pow_gt (2 * K) (6 * K * K + 1)
  set R := K + R' with hR
  set ℓ := K * R + 2 * K * K with hℓ
  obtain ⟨v, S, hScard, hSmem⟩ := hG ℓ
  have hdist : ∀ a b : {w : Word // (fun _ : Word ↦ True) w},
      binaryGraph.dist a b = treeDist a.1 b.1 := fun a b ↦ wordGraph_dist prefixClosed_true a b
  have hdense : ∀ u : Word, ∃ x, treeDist (f x).1 ((f v).1 ++ u) ≤ K := by
    intro u
    obtain ⟨x, hx⟩ := hqi.dense ⟨(f v).1 ++ u, trivial⟩
    exact ⟨x, by rw [hdist] at hx; exact hx⟩
  choose g hg using hdense
  have hdv : ∀ u : Word, treeDist ((f v).1 ++ u) (f v).1 = u.length := by
    intro u
    rw [treeDist_comm, treeDist_of_prefix (List.prefix_append (f v).1 u)]
    simp
  have hgS : ∀ u : Word, u.length = R → g u ∈ S := by
    intro u hu
    refine hSmem _ ?_
    have h1 : treeDist (f (g u)).1 (f v).1 ≤ K + R := by
      have h := treeDist_triangle (f (g u)).1 ((f v).1 ++ u) (f v).1
      have h2 := hg u
      rw [hdv u, hu] at h
      omega
    calc G.dist (g u) v ≤ K * binaryGraph.dist (f (g u)) (f v) + K * K := hqi.lower (g u) v
      _ = K * treeDist (f (g u)).1 (f v).1 + K * K := by rw [hdist]
      _ ≤ K * (K + R) + K * K := Nat.add_le_add_right (Nat.mul_le_mul_left K h1) _
      _ = K * R + 2 * K * K := by ring
      _ = ℓ := hℓ.symm
  have hcount : (wordsOf R).card ≤ (S ×ˢ wordsOf K).card := by
    refine Finset.card_le_card_of_injOn (fun u ↦ (g u, u.drop R')) ?_ ?_
    · intro u hu
      rw [Finset.mem_coe, mem_wordsOf] at hu
      refine Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hgS u hu, ?_⟩)
      rw [mem_wordsOf, List.length_drop, hu]
      omega
    · intro u hu u' hu' heq
      rw [Finset.mem_coe, mem_wordsOf] at hu hu'
      have hgg : g u = g u' := congrArg Prod.fst heq
      have hdrop : u.drop R' = u'.drop R' := congrArg Prod.snd heq
      have h1 : treeDist ((f v).1 ++ u) (f (g u')).1 ≤ K := by
        rw [treeDist_comm, ← hgg]
        exact hg u
      have h2 : treeDist (f (g u')).1 ((f v).1 ++ u') ≤ K := hg u'
      have h3 := treeDist_triangle ((f v).1 ++ u) (f (g u')).1 ((f v).1 ++ u')
      rw [treeDist_append_left] at h3
      have hadd := treeDist_add_wedge_length u u'
      rw [hu, hu'] at hadd
      have hge : R' ≤ (wedge u u').length := by omega
      have hqu : (wedge u u').take R' <+: u :=
        (List.take_prefix R' _).trans (wedge_prefix_left u u')
      have hqu' : (wedge u u').take R' <+: u' :=
        (List.take_prefix R' _).trans (wedge_prefix_right u u')
      have hql : ((wedge u u').take R').length = R' := by
        rw [List.length_take]; omega
      have e1 : (wedge u u').take R' = u.take R' := by
        have h := List.prefix_iff_eq_take.mp hqu
        rwa [hql] at h
      have e2 : (wedge u u').take R' = u'.take R' := by
        have h := List.prefix_iff_eq_take.mp hqu'
        rwa [hql] at h
      have hu1 : u = (wedge u u').take R' ++ u.drop R' := by
        rw [e1]; exact (List.take_append_drop R' u).symm
      have hu2 : u' = (wedge u u').take R' ++ u'.drop R' := by
        rw [e2]; exact (List.take_append_drop R' u').symm
      calc u = (wedge u u').take R' ++ u.drop R' := hu1
        _ = (wedge u u').take R' ++ u'.drop R' := by rw [hdrop]
        _ = u' := hu2.symm
  have hfin : 2 ^ R ≤ (2 * ℓ + 1) * 2 ^ K :=
    calc 2 ^ R = (wordsOf R).card := (card_wordsOf R).symm
      _ ≤ (S ×ˢ wordsOf K).card := hcount
      _ = S.card * 2 ^ K := by rw [Finset.card_product, card_wordsOf]
      _ ≤ (2 * ℓ + 1) * 2 ^ K := Nat.mul_le_mul_right _ hScard
  have hnum : (2 * ℓ + 1) * 2 ^ K < 2 ^ R := by
    have hp : 0 < 2 ^ K := pow_pos (by norm_num) K
    have he : 2 * ℓ + 1 = 2 * K * R' + (6 * K * K + 1) := by rw [hℓ, hR]; ring
    calc (2 * ℓ + 1) * 2 ^ K = (2 * K * R' + (6 * K * K + 1)) * 2 ^ K := by rw [he]
      _ < 2 ^ R' * 2 ^ K := mul_lt_mul_of_pos_right hR' hp
      _ = 2 ^ R := by rw [← pow_add]; congr 1; omega
  exact absurd hfin (Nat.not_le.mpr hnum)

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-thin`)**, in the form
`thm:bottleneck` consumes: at every radius `ℓ` a vertex whose ball of radius `ℓ` is
covered by `2ℓ + 1` vertices. -/
def HasThinBallsN (T : BranchingProcess.Word N → Prop) : Prop :=
  ∀ ℓ : ℕ, ∃ v : BranchingProcess.Word N, T v ∧ ∃ S : Finset (BranchingProcess.Word N),
    S.card ≤ 2 * ℓ + 1 ∧ ∀ x, T x → BranchingProcess.treeDist x v ≤ ℓ → x ∈ S

/-- Thin balls of the word set are thin balls of its graph. -/
lemma hasThinBallsG_of_hasThinBallsN (hT : PrefixClosedN T) (h : HasThinBallsN T) :
    HasThinBallsG (wordGraphN T) := by
  classical
  intro ℓ
  obtain ⟨v, hv, S, hS, hmem⟩ := h ℓ
  refine ⟨⟨v, hv⟩, S.subtype T, ?_, fun x hx ↦ ?_⟩
  · exact (Finset.card_subtype T S).trans_le ((Finset.card_filter_le _ _).trans hS)
  · rw [Finset.mem_subtype]
    rw [wordGraphN_dist hT] at hx
    exact hmem x.1 x.2 hx

/-- **`thm:bottleneck` for a set of words over `Fin N`.** -/
theorem not_quasiIsometric_binary_of_thinBallsN (hT : PrefixClosedN T)
    (h : HasThinBallsN T) : ¬ QuasiIsometric (wordGraphN T) binaryGraph :=
  not_quasiIsometric_binary_of_thinBalls (hasThinBallsG_of_hasThinBallsN hT h)

/-- **`thm:bottleneck` against a graph quasi-isometric to the binary tree**: thin balls
separate from anything the full tree regime produces. -/
theorem not_quasiIsometric_of_thinBallsN_of_binary {V : Type*} {G : SimpleGraph V}
    (hT : PrefixClosedN T) (h : HasThinBallsN T) (hG : QuasiIsometric G binaryGraph) :
    ¬ QuasiIsometric (wordGraphN T) G := fun hqi ↦
  not_quasiIsometric_binary_of_thinBallsN hT h
    (QuasiIsometric.trans (wordGraph_connected prefixClosed_true ⟨⟨[], trivial⟩⟩) hqi hG)

end Obstructions

/-! ### Chains of children as rays -/

section Chains

variable {T : GWord N → Prop}

/-- A chain of children: each term is a child of the previous one. -/
def IsChain (r : ℕ → GWord N) : Prop :=
  ∀ n, r (n + 1) ∈ BranchingProcess.Word.children (r n)

lemma IsChain.prefix {r : ℕ → GWord N} (hr : IsChain r) {m n : ℕ} (h : m ≤ n) :
    r m <+: r n :=
  BranchingProcess.prefix_of_chain hr h

lemma IsChain.length {r : ℕ → GWord N} (hr : IsChain r) (n : ℕ) :
    (r n).length = (r 0).length + n :=
  BranchingProcess.length_of_chain hr n

lemma IsChain.treeDist {r : ℕ → GWord N} (hr : IsChain r) (m n : ℕ) :
    BranchingProcess.treeDist (r m) (r n) = Nat.dist m n :=
  BranchingProcess.treeDist_of_chain hr m n

/-- **In a tree without leaves every vertex starts a chain of children.** -/
lemma exists_chain_of_forall_child (hchild : ∀ u, T u → ∃ j : Fin N, T (u ++ [j]))
    {v : GWord N} (hv : T v) : ∃ r : ℕ → GWord N, r 0 = v ∧ (∀ n, T (r n)) ∧ IsChain r := by
  classical
  choose f hf using fun w : {w : GWord N // T w} ↦ hchild w.1 w.2
  let ρ : ℕ → {w : GWord N // T w} :=
    fun n ↦ Nat.rec (⟨v, hv⟩ : {w : GWord N // T w}) (fun _ w ↦ ⟨w.1 ++ [f w], hf w⟩) n
  exact ⟨fun n ↦ (ρ n).1, rfl, fun n ↦ (ρ n).2, fun n ↦ ⟨f (ρ n), rfl⟩⟩

/-- A sequence of vertices stepping one edge at a time and receding from its start at
unit speed is an isometric ray. -/
lemma isRayN_of (hT : PrefixClosedN T) (g : ℕ → {w : GWord N // T w})
    (hstep : ∀ n, BranchingProcess.treeDist (g n).1 (g (n + 1)).1 = 1)
    (hbase : ∀ n, BranchingProcess.treeDist (g 0).1 (g n).1 = n) :
    IsRay (wordGraphN T) g := by
  have hle : ∀ m d : ℕ, BranchingProcess.treeDist (g m).1 (g (m + d)).1 ≤ d := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
        have h1 := BranchingProcess.treeDist_triangle (g m).1 (g (m + d)).1 (g (m + d + 1)).1
        have h2 := hstep (m + d)
        have hrw : m + (d + 1) = m + d + 1 := by omega
        rw [hrw]
        omega
  have key : ∀ m n : ℕ, m ≤ n → BranchingProcess.treeDist (g m).1 (g n).1 = n - m := by
    intro m n hmn
    have h1 := BranchingProcess.treeDist_triangle (g 0).1 (g m).1 (g n).1
    rw [hbase m, hbase n] at h1
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have h2 := hle m d
    omega
  intro m n
  rw [wordGraphN_dist hT]
  rcases le_total m n with h | h
  · rw [key m n h]
    unfold Nat.dist
    omega
  · rw [BranchingProcess.treeDist_comm, key n m h]
    unfold Nat.dist
    omega

/-- A chain of vertices of `T` is a ray of its graph. -/
lemma isRayN_of_chain (hT : PrefixClosedN T) {r : ℕ → GWord N} (hr : IsChain r)
    (hmem : ∀ n, T (r n)) : IsRay (wordGraphN T) (fun n ↦ ⟨r n, hmem n⟩) := by
  intro m n
  rw [wordGraphN_dist hT]
  exact hr.treeDist m n

/-- The chain out of `v` continuing along a chain out of one of its children. -/
def chainFrom (v : GWord N) (r : ℕ → GWord N) (n : ℕ) : GWord N :=
  if n = 0 then v else r (n - 1)

@[simp] lemma chainFrom_zero (v : GWord N) (r : ℕ → GWord N) : chainFrom v r 0 = v := rfl

lemma chainFrom_succ (v : GWord N) (r : ℕ → GWord N) (n : ℕ) :
    chainFrom v r (n + 1) = r n := by simp [chainFrom]

lemma isChain_chainFrom {v : GWord N} {r : ℕ → GWord N} (hr : IsChain r)
    (hr0 : r 0 ∈ BranchingProcess.Word.children v) : IsChain (chainFrom v r) := by
  intro n
  cases n with
  | zero => rw [chainFrom_succ, chainFrom_zero]; exact hr0
  | succ m => rw [chainFrom_succ, chainFrom_succ]; exact hr m

lemma chainFrom_mem {v : GWord N} {r : ℕ → GWord N} (hv : T v) (hr : ∀ n, T (r n)) (n : ℕ) :
    T (chainFrom v r n) := by
  cases n with
  | zero => exact hv
  | succ m => rw [chainFrom_succ]; exact hr m

/-- Past its initial vertex the chain stays below the child it descends. -/
lemma prefix_chainFrom {v : GWord N} {r : ℕ → GWord N} (hr : IsChain r) {n : ℕ} (hn : n ≠ 0) :
    r 0 <+: chainFrom v r n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [chainFrom_succ]
  exact hr.prefix (Nat.zero_le m)

/-! #### The ray climbing to a split and descending a chain out of its other child -/

/-- The ray climbing from `w` to the split `p` above it and descending the chain `r`
out of the child of `p` that `w` does not lie below. -/
def upChain (w p : GWord N) (r : ℕ → GWord N) (n : ℕ) : GWord N :=
  if n ≤ w.length - p.length then w.take (w.length - n)
  else r (n - (w.length - p.length) - 1)

section UpChain

variable {w p : GWord N} {r : ℕ → GWord N} {x y : Fin N}

lemma upChain_le {n : ℕ} (hn : n ≤ w.length - p.length) :
    upChain w p r n = w.take (w.length - n) := if_pos hn

lemma upChain_gt {n : ℕ} (hn : ¬ n ≤ w.length - p.length) :
    upChain w p r n = r (n - (w.length - p.length) - 1) := if_neg hn

@[simp] lemma upChain_zero : upChain w p r 0 = w := by
  rw [upChain_le (Nat.zero_le _)]
  simp

lemma upChain_prefix {n : ℕ} (hn : n ≤ w.length - p.length) : upChain w p r n <+: w := by
  rw [upChain_le hn]
  exact List.take_prefix _ _

lemma upChain_length {n : ℕ} (hn : n ≤ w.length - p.length) :
    (upChain w p r n).length = w.length - n := by
  rw [upChain_le hn, List.length_take]
  omega

variable (hpw : p ++ [x] <+: w) (hr : IsChain r) (hr0 : r 0 = p ++ [y]) (hxy : x ≠ y)
include hpw

lemma le_length_of_splitN : p.length + 1 ≤ w.length := by
  have := hpw.length_le
  simp only [List.length_append, List.length_singleton] at this
  omega

lemma upChain_split : upChain w p r (w.length - p.length) = p := by
  have hlen := le_length_of_splitN hpw
  rw [upChain_le le_rfl, show w.length - (w.length - p.length) = p.length by omega]
  exact (List.prefix_iff_eq_take.mp ((List.prefix_append p [x]).trans hpw)).symm

include hr hr0 hxy in
/-- The wedge of the far part of the climbing ray with anything below `w` is the
split: the two leave `p` by different letters. -/
lemma wedge_upChain {n : ℕ} (hn : ¬ n ≤ w.length - p.length) {z : GWord N}
    (hz : w <+: z) : BranchingProcess.wedge z (upChain w p r n) = p := by
  rw [upChain_gt hn]
  obtain ⟨t, ht⟩ := hpw.trans hz
  obtain ⟨t', ht'⟩ := hr.prefix (Nat.zero_le (n - (w.length - p.length) - 1))
  rw [hr0] at ht'
  rw [← ht, ← ht', List.append_assoc, List.append_assoc, List.singleton_append,
    List.singleton_append]
  exact wedgeN_diverge hxy

include hr hr0 hxy in
lemma treeDist_upChain (n : ℕ) : BranchingProcess.treeDist w (upChain w p r n) = n := by
  have hlen := le_length_of_splitN hpw
  by_cases hn : n ≤ w.length - p.length
  · rw [BranchingProcess.treeDist_comm, BranchingProcess.treeDist_of_prefix (upChain_prefix hn),
      upChain_length hn]
    omega
  · have hw := BranchingProcess.treeDist_add w (upChain w p r n)
    rw [wedge_upChain hpw hr hr0 hxy hn (List.prefix_refl w)] at hw
    have hlen2 : (upChain w p r n).length = p.length + 1 + (n - (w.length - p.length) - 1) := by
      rw [upChain_gt hn, hr.length, hr0]
      simp only [List.length_append, List.length_singleton]
    omega

include hr hr0 hxy in
/-- The two rays out of `w` are at distance the sum of their parameters. -/
lemma treeDist_chain_upChain {s : ℕ → GWord N} (hs : IsChain s) (hs0 : s 0 = w) (m n : ℕ) :
    BranchingProcess.treeDist (s m) (upChain w p r n) = m + n := by
  have hlen := le_length_of_splitN hpw
  have hsm : w <+: s m := hs0 ▸ hs.prefix (Nat.zero_le m)
  have hslen : (s m).length = w.length + m := by rw [hs.length, hs0]
  by_cases hn : n ≤ w.length - p.length
  · have hpre : upChain w p r n <+: s m := (upChain_prefix hn).trans hsm
    rw [BranchingProcess.treeDist_comm, BranchingProcess.treeDist_of_prefix hpre,
      upChain_length hn]
    omega
  · have hw := BranchingProcess.treeDist_add (s m) (upChain w p r n)
    rw [wedge_upChain hpw hr hr0 hxy hn hsm] at hw
    have hlen2 : (upChain w p r n).length = p.length + 1 + (n - (w.length - p.length) - 1) := by
      rw [upChain_gt hn, hr.length, hr0]
      simp only [List.length_append, List.length_singleton]
    omega

include hr hr0 in
lemma treeDist_upChain_step (n : ℕ) :
    BranchingProcess.treeDist (upChain w p r n) (upChain w p r (n + 1)) = 1 := by
  have hlen := le_length_of_splitN hpw
  by_cases hn : n + 1 ≤ w.length - p.length
  · have hn' : n ≤ w.length - p.length := by omega
    have hpre : upChain w p r (n + 1) <+: upChain w p r n := by
      rw [upChain_le hn, upChain_le hn']
      exact List.prefix_take_iff.mpr ⟨List.take_prefix _ _, by simp; omega⟩
    rw [BranchingProcess.treeDist_comm, BranchingProcess.treeDist_of_prefix hpre,
      upChain_length hn, upChain_length hn']
    omega
  · by_cases hn' : n ≤ w.length - p.length
    · have hnv : n = w.length - p.length := by omega
      rw [hnv, upChain_split hpw, upChain_gt (by omega),
        show w.length - p.length + 1 - (w.length - p.length) - 1 = 0 by omega, hr0]
      exact BranchingProcess.treeDist_append_singleton p y
    · rw [upChain_gt hn, upChain_gt hn',
        show n + 1 - (w.length - p.length) - 1 = (n - (w.length - p.length) - 1) + 1 by omega]
      exact BranchingProcess.treeDist_of_mem_children (hr _)

omit hpw in
lemma upChain_mem (hT : PrefixClosedN T) (hw : T w) (hrT : ∀ n, T (r n)) (n : ℕ) :
    T (upChain w p r n) := by
  by_cases hn : n ≤ w.length - p.length
  · exact hT (upChain_prefix hn) hw
  · rw [upChain_gt hn]
    exact hrT _

omit hpw in
include hr hr0 in
/-- Past its initial vertex the climbing ray is either shorter than `w` or descends
the other child of `p`. -/
lemma upChain_cases {n : ℕ} (hn : n ≠ 0) :
    (upChain w p r n).length < w.length ∨ p ++ [y] <+: upChain w p r n := by
  by_cases hnk : n ≤ w.length - p.length
  · refine Or.inl ?_
    rw [upChain_length hnk]
    omega
  · refine Or.inr ?_
    rw [upChain_gt hnk, ← hr0]
    exact hr.prefix (Nat.zero_le _)

end UpChain

/-! ### Three rays out of a split below a split -/

/-- **Three rays out of one vertex**, pairwise meeting only there. -/
lemma hasThreeRaysN_of {v : {w : GWord N // T w}} {r s t : ℕ → {w : GWord N // T w}}
    (hr : IsRay (wordGraphN T) r) (hs : IsRay (wordGraphN T) s) (ht : IsRay (wordGraphN T) t)
    (hr0 : r 0 = v) (hs0 : s 0 = v) (ht0 : t 0 = v)
    (hrs : ∀ m n, m ≠ 0 → n ≠ 0 → r m ≠ s n)
    (hrt : ∀ m n, m ≠ 0 → n ≠ 0 → r m ≠ t n)
    (hst : ∀ m n, m ≠ 0 → n ≠ 0 → s m ≠ t n) : HasThreeRaysN T := by
  refine ⟨v, ![r, s, t], fun i ↦ ?_, fun i ↦ ?_, fun i j hij m n hmn ↦ ?_⟩
  · fin_cases i
    exacts [hr, hs, ht]
  · fin_cases i
    exacts [hr0, hs0, ht0]
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · fin_cases i
      exacts [hr0, hs0, ht0]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hmn]
      fin_cases j
      exacts [hr0, hs0, ht0]
    fin_cases i
    · fin_cases j
      · exact absurd rfl hij
      · exact absurd hmn (hrs m n hm.ne' hn.ne')
      · exact absurd hmn (hrt m n hm.ne' hn.ne')
    · fin_cases j
      · exact absurd hmn fun h ↦ hrs n m hn.ne' hm.ne' h.symm
      · exact absurd rfl hij
      · exact absurd hmn (hst m n hm.ne' hn.ne')
    · fin_cases j
      · exact absurd hmn fun h ↦ hrt n m hn.ne' hm.ne' h.symm
      · exact absurd hmn fun h ↦ hst n m hn.ne' hm.ne' h.symm
      · exact absurd rfl hij

/-- Two prefixes of one word of the same length agree. -/
lemma eq_of_prefixN_of_length {x y w : GWord N} (hx : x <+: w) (hy : y <+: w)
    (h : x.length = y.length) : x = y := by
  rw [List.prefix_iff_eq_take.mp hx, List.prefix_iff_eq_take.mp hy, h]

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-rays`), the
deterministic form.**  A split `u` with children `u ++ [a]` and `u ++ [b]`, a further
split `v` below `u ++ [b]` with children `v ++ [a']` and `v ++ [b']`, and chains of
vertices of `T` descending from `v ++ [a']`, `v ++ [b']` and `u ++ [a]` give three
rays out of `v` pairwise meeting only there. -/
theorem hasThreeRaysN_of_splits (hT : PrefixClosedN T) {u v : GWord N} {a b a' b' : Fin N}
    (hab : a ≠ b) (hab' : a' ≠ b') (hv : T v) (huv : u ++ [b] <+: v)
    {r₁ r₂ r₃ : ℕ → GWord N} (h₁ : IsChain r₁) (h₁0 : r₁ 0 = v ++ [a']) (h₁T : ∀ n, T (r₁ n))
    (h₂ : IsChain r₂) (h₂0 : r₂ 0 = v ++ [b']) (h₂T : ∀ n, T (r₂ n))
    (h₃ : IsChain r₃) (h₃0 : r₃ 0 = u ++ [a]) (h₃T : ∀ n, T (r₃ n)) : HasThreeRaysN T := by
  have hc₁ : IsChain (chainFrom v r₁) := isChain_chainFrom h₁ ⟨a', h₁0⟩
  have hc₂ : IsChain (chainFrom v r₂) := isChain_chainFrom h₂ ⟨b', h₂0⟩
  have hba : b ≠ a := Ne.symm hab
  set R₁ : ℕ → {w : GWord N // T w} := fun n ↦ ⟨chainFrom v r₁ n, chainFrom_mem hv h₁T n⟩
  set R₂ : ℕ → {w : GWord N // T w} := fun n ↦ ⟨chainFrom v r₂ n, chainFrom_mem hv h₂T n⟩
  set S : ℕ → {w : GWord N // T w} := fun n ↦ ⟨upChain v u r₃ n, upChain_mem hT hv h₃T n⟩
  have hrayS : IsRay (wordGraphN T) S := by
    refine isRayN_of hT S (fun n ↦ treeDist_upChain_step huv h₃ h₃0 n) (fun n ↦ ?_)
    show BranchingProcess.treeDist (upChain v u r₃ 0) (upChain v u r₃ n) = n
    rw [upChain_zero]
    exact treeDist_upChain huv h₃ h₃0 hba n
  -- the descending rays stay below the two children of `v`, the climbing ray does not
  have hsep : ∀ m n, m ≠ 0 → n ≠ 0 → chainFrom v r₁ m ≠ chainFrom v r₂ n := by
    intro m n hm hn heq
    have h1 := prefix_chainFrom (v := v) h₁ hm
    have h2 := prefix_chainFrom (v := v) h₂ hn
    rw [← heq] at h2
    have h3 := eq_of_prefixN_of_length h1 h2 (by rw [h₁0, h₂0]; simp)
    rw [h₁0, h₂0] at h3
    exact hab' (by simpa using h3)
  have hsepU : ∀ (r : ℕ → GWord N) (a'' : Fin N), IsChain r → r 0 = v ++ [a''] →
      ∀ m n, m ≠ 0 → n ≠ 0 → chainFrom v r m ≠ upChain v u r₃ n := by
    intro r a'' hr hr0 m n hm hn heq
    rcases upChain_cases (w := v) (p := u) h₃ h₃0 hn with hshort | hlong
    · rw [← heq] at hshort
      have h1 := (prefix_chainFrom (v := v) hr hm).length_le
      rw [hr0] at h1
      simp only [List.length_append, List.length_singleton] at h1
      omega
    · rw [← heq] at hlong
      have h1 : u ++ [b] <+: chainFrom v r m :=
        huv.trans ((List.prefix_append v [a'']).trans (hr0 ▸ prefix_chainFrom (v := v) hr hm))
      have h3 := eq_of_prefixN_of_length hlong h1 (by simp)
      exact hab (by simpa using h3)
  exact hasThreeRaysN_of (v := ⟨v, hv⟩) (isRayN_of_chain hT hc₁ (chainFrom_mem hv h₁T))
    (isRayN_of_chain hT hc₂ (chainFrom_mem hv h₂T)) hrayS rfl rfl
    (Subtype.ext (upChain_zero (p := u) (r := r₃)))
    (fun m n hm hn h ↦ hsep m n hm hn (congrArg Subtype.val h))
    (fun m n hm hn h ↦ hsepU r₁ a' h₁ h₁0 m n hm hn (congrArg Subtype.val h))
    (fun m n hm hn h ↦ hsepU r₂ b' h₂ h₂0 m n hm hn (congrArg Subtype.val h))

/-! ### Lines in a tree without leaves -/

/-- **A line through a vertex below a split.**  A chain descending from `w` carries
one ray, and the climb to the split `p` followed by a chain out of its other child
`p ++ [y]` carries the other. -/
theorem exists_isLine_throughN (hT : PrefixClosedN T)
    (hchild : ∀ u, T u → ∃ j : Fin N, T (u ++ [j])) {p w : GWord N} {x y : Fin N}
    (hxy : x ≠ y) (hpy : T (p ++ [y])) (hpw : p ++ [x] <+: w) (hw : T w) :
    ∃ l : ℤ → {v : GWord N // T v}, IsLine (wordGraphN T) l ∧ (l 0).1 = w := by
  obtain ⟨s, hs0, hsT, hs⟩ := exists_chain_of_forall_child hchild hw
  obtain ⟨r, hr0, hrT, hr⟩ := exists_chain_of_forall_child hchild hpy
  set R : ℕ → {v : GWord N // T v} := fun n ↦ ⟨s n, hsT n⟩ with hR
  set S : ℕ → {v : GWord N // T v} := fun n ↦ ⟨upChain w p r n, upChain_mem hT hw hrT n⟩
  have hrayR : IsRay (wordGraphN T) R := isRayN_of_chain hT hs hsT
  have hrayS : IsRay (wordGraphN T) S := by
    refine isRayN_of hT S (fun n ↦ treeDist_upChain_step hpw hr hr0 n) (fun n ↦ ?_)
    show BranchingProcess.treeDist (upChain w p r 0) (upChain w p r n) = n
    rw [upChain_zero]
    exact treeDist_upChain hpw hr hr0 hxy n
  refine ⟨fun k : ℤ ↦ if 0 ≤ k then R k.toNat else S (-k).toNat,
    isLine_of hrayR hrayS (fun m n ↦ ?_), by simp [hR, hs0]⟩
  rw [wordGraphN_dist hT]
  exact treeDist_chain_upChain hpw hr hr0 hxy hs hs0 m n

/-- Two words neither of which is a prefix of the other diverge at a common prefix. -/
lemma exists_divergeFin : ∀ {u b : GWord N}, ¬ u <+: b → ¬ b <+: u →
    ∃ (q : GWord N) (x y : Fin N), x ≠ y ∧ q ++ [x] <+: u ∧ q ++ [y] <+: b
  | [], _, h1, _ => absurd List.nil_prefix h1
  | _ :: _, [], _, h2 => absurd List.nil_prefix h2
  | c :: u, d :: b, h1, h2 => by
      by_cases hcd : c = d
      · subst hcd
        have h1' : ¬ u <+: b := fun h ↦ h1 (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
        have h2' : ¬ b <+: u := fun h ↦ h2 (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
        obtain ⟨q, x, y, hxy, hx, hy⟩ := exists_divergeFin h1' h2'
        exact ⟨c :: q, x, y, hxy, List.cons_prefix_cons.mpr ⟨rfl, hx⟩,
          List.cons_prefix_cons.mpr ⟨rfl, hy⟩⟩
      · exact ⟨[], c, d, hcd, by simp, by simp⟩

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-lines`), the
deterministic form.**  In a tree without leaves carrying a split at `b`, every vertex
lies within `|b| + 1` of a line: the vertices above `b` use the line through its child,
and every other vertex lies below a split and on a line through it. -/
theorem nearLineN_of_split (hT : PrefixClosedN T)
    (hchild : ∀ u, T u → ∃ j : Fin N, T (u ++ [j])) {b : GWord N} {a a' : Fin N}
    (haa : a ≠ a') (hba : T (b ++ [a])) (hba' : T (b ++ [a'])) : NearLineN T := by
  refine ⟨b.length + 1, fun u ↦ ?_⟩
  -- the line through `u` when `u` lies below a split `p` by the letter `x`
  have hline : ∀ (p : GWord N) (x y : Fin N), x ≠ y → T (p ++ [y]) → p ++ [x] <+: u.1 →
      ∃ (l : ℤ → {w : GWord N // T w}) (k : ℤ),
        IsLine (wordGraphN T) l ∧ (wordGraphN T).dist u (l k) ≤ b.length + 1 := by
    intro p x y hxy hpy hpu
    obtain ⟨l, hl, hl0⟩ := exists_isLine_throughN hT hchild hxy hpy hpu u.2
    refine ⟨l, 0, hl, ?_⟩
    rw [wordGraphN_dist hT, hl0, BranchingProcess.treeDist_self]
    omega
  by_cases hub : u.1 <+: b
  · -- above the split: the line through `b ++ [a]`
    obtain ⟨l, hl, hl0⟩ := exists_isLine_throughN hT hchild haa hba' (List.prefix_refl _) hba
    refine ⟨l, 0, hl, ?_⟩
    rw [wordGraphN_dist hT, hl0,
      BranchingProcess.treeDist_of_prefix (hub.trans (List.prefix_append b [a]))]
    simp
  by_cases hbu : b <+: u.1
  · obtain ⟨t, ht⟩ := hbu
    obtain ⟨x, t', rfl⟩ : ∃ (x : Fin N) (t' : GWord N), t = x :: t' := by
      cases t with
      | nil => exact absurd (by rw [← ht, List.append_nil]) hub
      | cons x t' => exact ⟨x, t', rfl⟩
    have hbx : b ++ [x] <+: u.1 := ⟨t', by rw [← ht]; simp⟩
    by_cases hxa : x = a
    · exact hline b x a' (hxa ▸ haa) hba' hbx
    · exact hline b x a hxa hba hbx
  · obtain ⟨q, x, y, hxy, hqu, hqb⟩ := exists_divergeFin hub hbu
    exact hline q x y hxy (hT hqb (hT (List.prefix_append b [a]) hba)) hqu

/-! ### The cone above a child is a hair -/

/-- One step of the tree metric keeps the cone: a neighbour of a vertex extending
`x ++ [j]`, other than `x` itself, extends `x ++ [j]` too. -/
lemma prefix_of_adjN {x : GWord N} {j : Fin N} {p q : {w : GWord N // T w}}
    (hadj : (wordGraphN T).Adj p q) (hqx : q.1 ≠ x) (hp : x ++ [j] <+: p.1) :
    x ++ [j] <+: q.1 := by
  rcases treeDistN_eq_one_iff.mp (wordGraphN_adj.mp hadj) with ⟨b', hb'⟩ | ⟨b', hb'⟩
  · exact hp.trans (by rw [hb']; exact List.prefix_append _ _)
  · rcases eq_or_ne (x ++ [j]) p.1 with heq | hne
    · exact absurd ((List.append_inj' (heq.trans hb') rfl).1).symm hqx
    · have hq1 : q.1 <+: p.1 := by rw [hb']; exact List.prefix_append _ _
      refine List.prefix_of_prefix_length_le hp hq1 ?_
      have hlt : (x ++ [j]).length < p.1.length :=
        lt_of_le_of_ne hp.length_le fun h ↦ hne (hp.eq_of_length h)
      rw [hb'] at hlt
      simp only [List.length_append, List.length_singleton] at hlt ⊢
      omega

/-- **The cone above a child is a component.**  In the graph of a prefix-closed set
the vertices extending `x ++ [j]` are the component of the complement of `x`
containing `x ++ [j]`. -/
theorem exists_componentCompl_coneN (hT : PrefixClosedN T) {x : GWord N} {j : Fin N}
    (hx : T x) (hy : T (x ++ [j])) :
    ∃ C : (wordGraphN T).ComponentCompl
      ({(⟨x, hx⟩ : {w : GWord N // T w})} : Set {w : GWord N // T w}),
      (C : Set {w : GWord N // T w}) = {w : {w : GWord N // T w} | x ++ [j] <+: w.1} := by
  have hyx : (⟨x ++ [j], hy⟩ : {w : GWord N // T w})
      ∉ ({(⟨x, hx⟩ : {w : GWord N // T w})} : Set {w : GWord N // T w}) := by
    simp only [Set.mem_singleton_iff]
    intro h
    have := congrArg (fun w : {w : GWord N // T w} ↦ w.1.length) h
    simp at this
  refine ⟨(wordGraphN T).componentComplMk hyx, Set.eq_of_subset_of_subset ?_ ?_⟩
  · intro z hz
    rw [SetLike.mem_coe, SimpleGraph.ComponentCompl.mem_supp_iff] at hz
    obtain ⟨hzK, hzC⟩ := hz
    obtain ⟨W⟩ := (SimpleGraph.ConnectedComponent.exact hzC).symm
    show x ++ [j] <+: z.1
    have hwalk : ∀ {p q : ↥(({(⟨x, hx⟩ : {w : GWord N // T w})} : Set {w : GWord N // T w})ᶜ)}
        (_ : ((wordGraphN T).induce
          (({(⟨x, hx⟩ : {w : GWord N // T w})} : Set {w : GWord N // T w})ᶜ)).Walk p q),
        x ++ [j] <+: p.1.1 → x ++ [j] <+: q.1.1 := by
      intro p q W
      induction W with
      | nil => exact id
      | @cons p' v' q' hadj W ih =>
          intro hp
          exact ih (prefix_of_adjN (SimpleGraph.induce_adj.mp hadj)
            (fun h ↦ v'.2 (Set.mem_singleton_iff.mpr (Subtype.ext h))) hp)
    exact hwalk W List.prefix_rfl
  · have key : ∀ (t : GWord N) (hzv : T (x ++ [j] ++ t)),
        (⟨x ++ [j] ++ t, hzv⟩ : {w : GWord N // T w}) ∈ (wordGraphN T).componentComplMk hyx := by
      intro t
      induction t using List.reverseRecOn with
      | nil =>
          intro hzv
          have he : (⟨x ++ [j] ++ [], hzv⟩ : {w : GWord N // T w}) = ⟨x ++ [j], hy⟩ :=
            Subtype.ext (List.append_nil _)
          rw [he]
          exact SimpleGraph.componentComplMk_mem _ hyx
      | append_singleton t a ih =>
          intro hzv
          have hTt : T (x ++ [j] ++ t) :=
            hT (by rw [← List.append_assoc]; exact List.prefix_append _ _) hzv
          refine SimpleGraph.ComponentCompl.mem_of_adj ⟨x ++ [j] ++ t, hTt⟩ _ (ih hTt) ?_ ?_
          · simp only [Set.mem_singleton_iff]
            intro h
            have hlen := congrArg (fun w : {w : GWord N // T w} ↦ w.1.length) h
            simp only [List.length_append, List.length_singleton] at hlen
            omega
          · rw [wordGraphN_adj]
            show BranchingProcess.treeDist (x ++ [j] ++ t) (x ++ [j] ++ (t ++ [a])) = 1
            rw [← List.append_assoc]
            exact BranchingProcess.treeDist_append_singleton _ a
    rintro ⟨zv, hzv⟩ hz
    rw [SetLike.mem_coe]
    obtain ⟨t, rfl⟩ := hz
    exact key t hzv

/-- **A finite cone is a hair**, of depth the largest distance to the puncture,
realised by a deepest cone vertex. -/
theorem exists_isHair_coneN (hT : PrefixClosedN T) {x : GWord N} {j : Fin N}
    (hx : T x) (hy : T (x ++ [j])) (hfin : {w : GWord N | T w ∧ x ++ [j] <+: w}.Finite) :
    ∃ h : ℕ, IsHair (wordGraphN T) ⟨x, hx⟩ {w : {w : GWord N // T w} | x ++ [j] <+: w.1} h ∧
      ∀ z : GWord N, (hz : T z) → x ++ [j] <+: z →
        (wordGraphN T).dist ⟨z, hz⟩ ⟨x, hx⟩ ≤ h := by
  classical
  have hfin' : {w : {w : GWord N // T w} | x ++ [j] <+: w.1}.Finite := by
    have he : {w : {w : GWord N // T w} | x ++ [j] <+: w.1}
        = Subtype.val ⁻¹' {w : GWord N | T w ∧ x ++ [j] <+: w} := by
      ext w
      simp [w.2]
    rw [he]
    exact Set.Finite.preimage Subtype.val_injective.injOn hfin
  have hFne : hfin'.toFinset.Nonempty :=
    ⟨⟨x ++ [j], hy⟩, hfin'.mem_toFinset.mpr List.prefix_rfl⟩
  obtain ⟨w0, hw0F, hw0⟩ :=
    hfin'.toFinset.exists_mem_eq_sup hFne fun w ↦ (wordGraphN T).dist w ⟨x, hx⟩
  refine ⟨hfin'.toFinset.sup fun w ↦ (wordGraphN T).dist w ⟨x, hx⟩,
    ⟨exists_componentCompl_coneN hT hx hy, fun v hv ↦ ?_, ⟨w0, ?_, hw0.symm⟩⟩, fun z hz hpre ↦ ?_⟩
  · exact Finset.le_sup (f := fun w ↦ (wordGraphN T).dist w ⟨x, hx⟩)
      (hfin'.mem_toFinset.mpr hv)
  · exact hfin'.mem_toFinset.mp hw0F
  · exact Finset.le_sup (f := fun w ↦ (wordGraphN T).dist w ⟨x, hx⟩)
      (hfin'.mem_toFinset.mpr hpre)

/-- A finite cone with a deep vertex for every depth gives hairs of unbounded depth. -/
theorem unboundedHairsN_of_deep_cones (hT : PrefixClosedN T)
    (hdeep : ∀ n : ℕ, ∃ (x : GWord N) (j : Fin N) (z : GWord N), T (x ++ [j]) ∧
      {w : GWord N | T w ∧ x ++ [j] <+: w}.Finite ∧ T z ∧ x ++ [j] <+: z ∧
        n < BranchingProcess.treeDist z x) :
    UnboundedHairsN T := by
  intro n
  obtain ⟨x, j, z, hy, hfin, hz, hyz, hn⟩ := hdeep n
  have hx : T x := hT (List.prefix_append x [j]) hy
  obtain ⟨h, hhair, hle⟩ := exists_isHair_coneN hT hx hy hfin
  refine ⟨⟨x, hx⟩, _, h, ?_, hhair⟩
  have hd : BranchingProcess.treeDist z x ≤ h := by
    have h0 := hle z hz hyz
    rwa [wordGraphN_dist hT] at h0
  omega

/-! ### Thin balls in the middle of a neck -/

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-thin`), the
deterministic form.**  Along a chain `r` whose first `2ℓ` vertices have no child in
`T` besides the next vertex of the chain, the ball of radius `ℓ` around `r ℓ` is
covered by the first `2ℓ + 1` vertices of the chain. -/
theorem ball_subset_neck (hT : PrefixClosedN T) {r : ℕ → GWord N} (hr : IsChain r)
    {ℓ : ℕ} (hneck : ∀ i, i < 2 * ℓ → ∀ j : Fin N, T (r i ++ [j]) → r i ++ [j] = r (i + 1))
    {z : GWord N} (hz : T z) (hd : BranchingProcess.treeDist z (r ℓ) ≤ ℓ) :
    ∃ i ≤ 2 * ℓ, z = r i := by
  by_cases hvz : r ℓ <+: z
  · -- below the midpoint: the chain is the only way down
    obtain ⟨t, ht⟩ := hvz
    have htlen : t.length ≤ ℓ := by
      rw [← ht, BranchingProcess.treeDist_comm,
        BranchingProcess.treeDist_of_prefix (List.prefix_append _ _)] at hd
      simp only [List.length_append] at hd
      omega
    have key : ∀ s : GWord N, s.length ≤ ℓ → T (r ℓ ++ s) → r ℓ ++ s = r (ℓ + s.length) := by
      intro s
      induction s using List.reverseRecOn with
      | nil => intro _ _; simp
      | append_singleton s a ih =>
          intro hs hTs
          have hTs' : T (r ℓ ++ s) :=
            hT (by rw [← List.append_assoc]; exact List.prefix_append _ _) hTs
          have hslen : s.length ≤ ℓ := by simp at hs; omega
          have h1 := ih hslen hTs'
          rw [← List.append_assoc, h1] at hTs ⊢
          rw [hneck _ (by simp at hs; omega) a hTs]
          simp only [List.length_append, List.length_singleton, Nat.add_assoc]
    refine ⟨ℓ + t.length, by omega, ?_⟩
    rw [← ht]
    exact key t htlen (ht ▸ hz)
  · -- off the midpoint: the wedge is a chain vertex above it, and `z` is that vertex
    set q := BranchingProcess.wedge z (r ℓ) with hq
    have hqz : q <+: z := BranchingProcess.wedge_prefix_left _ _
    have hqv : q <+: r ℓ := BranchingProcess.wedge_prefix_right _ _
    have hadd := BranchingProcess.treeDist_add z (r ℓ)
    rw [← hq] at hadd
    have hqne : q ≠ r ℓ := fun h ↦ hvz (h ▸ hqz)
    have hqlt : q.length < (r ℓ).length := BranchingProcess.length_lt_of_prefix_ne hqv hqne
    have hrℓ : (r ℓ).length = (r 0).length + ℓ := hr.length ℓ
    have hqzlen := hqz.length_le
    have hq0 : (r 0).length ≤ q.length := by omega
    set i := q.length - (r 0).length with hi
    have hiℓ : i < ℓ := by omega
    have hqi : q = r i := by
      refine eq_of_prefixN_of_length hqv (hr.prefix (by omega)) ?_
      rw [hr.length i]
      omega
    refine ⟨i, by omega, ?_⟩
    by_contra hzq
    have hzq' : z ≠ q := fun h ↦ hzq (h.trans hqi)
    obtain ⟨t, ht⟩ := hqz
    obtain ⟨j, t', rfl⟩ : ∃ (j : Fin N) (t' : GWord N), t = j :: t' := by
      cases t with
      | nil => exact absurd (by rw [← ht, List.append_nil]) hzq'
      | cons j t' => exact ⟨j, t', rfl⟩
    have hqj : q ++ [j] <+: z := ⟨t', by rw [← ht]; simp⟩
    have hTqj : T (q ++ [j]) := hT hqj hz
    rw [hqi] at hTqj hqj
    have hstep := hneck i (by omega) j hTqj
    rw [hstep] at hqj
    have hqjv : r (i + 1) <+: r ℓ := hr.prefix (by omega)
    have hwed : r (i + 1) <+: q := BranchingProcess.prefix_wedge_of_prefix hqj hqjv
    have hlen := hwed.length_le
    rw [hr.length (i + 1), hqi, hr.length i] at hlen
    omega

/-- **Thin balls from necks of every length.** -/
theorem hasThinBallsN_of_necks (hT : PrefixClosedN T)
    (hneck : ∀ ℓ : ℕ, ∃ r : ℕ → GWord N, IsChain r ∧ T (r ℓ) ∧
      ∀ i, i < 2 * ℓ → ∀ j : Fin N, T (r i ++ [j]) → r i ++ [j] = r (i + 1)) :
    HasThinBallsN T := by
  classical
  intro ℓ
  obtain ⟨r, hr, hv, hn⟩ := hneck ℓ
  refine ⟨r ℓ, hv, (Finset.range (2 * ℓ + 1)).image r, le_trans Finset.card_image_le (by simp),
    fun z hz hd ↦ ?_⟩
  obtain ⟨i, hi, rfl⟩ := ball_subset_neck hT hr hn hz hd
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

end Chains

/-! ### A root event along a law-preserving descent

The probabilistic arguments of the four clauses share one scheme: a step `Φ` of the
sample space preserving the law (one step down the neck, or `n` of them), and a root
event `D` of mass `p` whose intersection with any event of the stepped field carries
the product mass.  The event that `D` fails at the first `k + 1` iterates then has mass
at most `(1 - p)^(k + 1)`, so almost surely some iterate lies in `D`. -/

section Iterate

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Φ : Ω → Ω} {D : Set Ω}

/-- The event that `D` fails at the first `k + 1` iterates of `Φ`. -/
def iterFail (Φ : Ω → Ω) (D : Set Ω) : ℕ → Set Ω
  | 0 => Dᶜ
  | k + 1 => Dᶜ ∩ Φ ⁻¹' iterFail Φ D k

lemma measurableSet_iterFail (hΦ : Measurable Φ) (hD : MeasurableSet D) :
    ∀ k, MeasurableSet (iterFail Φ D k)
  | 0 => hD.compl
  | k + 1 => hD.compl.inter (hΦ (measurableSet_iterFail hΦ hD k))

omit [MeasurableSpace Ω] in
/-- Off the failure event some iterate lies in `D`. -/
lemma exists_iterate_mem_of_notMem_iterFail :
    ∀ (k : ℕ) {ω : Ω}, ω ∉ iterFail Φ D k → ∃ i, i ≤ k ∧ Φ^[i] ω ∈ D
  | 0, ω, h => ⟨0, le_rfl, by simpa [iterFail] using h⟩
  | k + 1, ω, h => by
      simp only [iterFail, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage,
        not_and] at h
      by_cases hD : ω ∈ D
      · exact ⟨0, Nat.zero_le _, hD⟩
      · obtain ⟨i, hi, hmem⟩ := exists_iterate_mem_of_notMem_iterFail k (h hD)
        exact ⟨i + 1, by omega, by rw [Function.iterate_succ_apply]; exact hmem⟩

/-- **The failure event decays geometrically.** -/
lemma measure_iterFail_le [IsProbabilityMeasure μ] (hΦ : Measurable Φ)
    (hpres : ∀ A, MeasurableSet A → μ (Φ ⁻¹' A) = μ A) (hD : MeasurableSet D) {p : ℝ≥0∞}
    (hind : ∀ A, MeasurableSet A → μ (D ∩ Φ ⁻¹' A) = p * μ A) :
    ∀ k, μ (iterFail Φ D k) ≤ (1 - p) ^ (k + 1) := by
  have hpD : μ D = p := by
    have h := hind Set.univ MeasurableSet.univ
    rwa [Set.preimage_univ, Set.inter_univ, measure_univ, mul_one] at h
  intro k
  induction k with
  | zero =>
      show μ Dᶜ ≤ (1 - p) ^ 1
      rw [pow_one, prob_compl_eq_one_sub hD, hpD]
  | succ k ih =>
      have hF := measurableSet_iterFail hΦ hD k
      have hsplit := measure_inter_add_sdiff (μ := μ) (Φ ⁻¹' iterFail Φ D k) hD
      rw [Set.sdiff_eq, Set.inter_comm (Φ ⁻¹' iterFail Φ D k) D, hind _ hF,
        hpres _ hF, Set.inter_comm] at hsplit
      have hpne : p ≠ ⊤ := hpD ▸ measure_ne_top μ D
      have heq : μ (iterFail Φ D (k + 1)) = μ (iterFail Φ D k) - p * μ (iterFail Φ D k) := by
        show μ (Dᶜ ∩ Φ ⁻¹' iterFail Φ D k) = _
        exact ENNReal.eq_sub_of_add_eq (ENNReal.mul_ne_top hpne (measure_ne_top _ _))
          (by rw [add_comm]; exact hsplit)
      calc μ (iterFail Φ D (k + 1)) = (1 - p) * μ (iterFail Φ D k) := by
            rw [heq, ENNReal.sub_mul (fun _ _ ↦ measure_ne_top _ _), one_mul]
        _ ≤ (1 - p) * (1 - p) ^ (k + 1) := by gcongr
        _ = (1 - p) ^ (k + 1 + 1) := by ring

/-- **Some iterate lies in a root event of positive mass**, almost surely. -/
theorem ae_exists_iterate_mem [IsProbabilityMeasure μ] (hΦ : Measurable Φ)
    (hpres : ∀ A, MeasurableSet A → μ (Φ ⁻¹' A) = μ A) (hD : MeasurableSet D) {p : ℝ≥0∞}
    (hind : ∀ A, MeasurableSet A → μ (D ∩ Φ ⁻¹' A) = p * μ A) (hp : p ≠ 0) :
    ∀ᵐ ω ∂μ, ∃ k, Φ^[k] ω ∈ D := by
  rw [ae_iff]
  have hsub : {ω | ¬ ∃ k, Φ^[k] ω ∈ D} ⊆ ⋂ k, iterFail Φ D k := by
    intro ω hω
    simp only [Set.mem_setOf_eq, not_exists] at hω
    refine Set.mem_iInter.mpr fun k ↦ ?_
    by_contra hk
    obtain ⟨i, -, hi⟩ := exists_iterate_mem_of_notMem_iterFail k hk
    exact hω i hi
  have hle : ∀ k, μ (⋂ k, iterFail Φ D k) ≤ (1 - p) ^ (k + 1) := fun k ↦
    (measure_mono (Set.iInter_subset _ k)).trans (measure_iterFail_le hΦ hpres hD hind k)
  have hlt : (1 : ℝ≥0∞) - p < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp
  have htend := (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt).comp
    (Filter.tendsto_add_atTop_nat 1)
  exact nonpos_iff_eq_zero.mp (measure_mono hsub |>.trans
    (nonpos_iff_eq_zero.mp (ge_of_tendsto' htend hle)).le)

end Iterate

/-! ### The rank-indexed subfields at ambient vertices -/

section Bridge

variable {c d : GWord N → ℕ}

/-- The sample of a residual field, read in the sample. -/
lemma mem_sample_ambSub_iff {x w : GWord N} (hx : x ∈ sample c) :
    w ∈ sample (ambSub c x) ↔ x ++ w ∈ sample c := by
  rw [BranchingProcess.append_mem_sample_iff]
  exact ⟨fun h ↦ ⟨hx, h⟩, fun h ↦ h.2⟩

/-- A vertex of the sample lies in the skeleton exactly when its residual field
survives. -/
lemma mem_skeleton_iff_survives_ambSub {x : GWord N} (hx : x ∈ sample c) :
    x ∈ skeleton c ↔ Survives (ambSub c x) := by
  rw [BranchingProcess.mem_skeleton_iff, BranchingProcess.subAt_sample hx]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hx, h⟩⟩

/-- The skeleton of a residual field, read in the skeleton. -/
lemma mem_skeleton_ambSub_iff {x y : GWord N} (hx : x ∈ sample c) :
    y ∈ skeleton (ambSub c x) ↔ x ++ y ∈ skeleton c := by
  constructor
  · intro hy
    have hys : y ∈ sample (ambSub c x) := BranchingProcess.skeleton_subset_sample _ hy
    have hxy : x ++ y ∈ sample c := (mem_sample_ambSub_iff hx).mp hys
    rw [mem_skeleton_iff_survives_ambSub hys] at hy
    rw [mem_skeleton_iff_survives_ambSub hxy, ← ambSub_ambSub]
    exact hy
  · intro hxy
    have hxys : x ++ y ∈ sample c := BranchingProcess.skeleton_subset_sample _ hxy
    have hys : y ∈ sample (ambSub c x) := (mem_sample_ambSub_iff hx).mpr hxys
    rw [mem_skeleton_iff_survives_ambSub hxys, ← ambSub_ambSub] at hxy
    rw [mem_skeleton_iff_survives_ambSub hys]
    exact hxy

/-- The sample tree is prefix-closed. -/
lemma prefixClosedN_sample (c : GWord N → ℕ) : PrefixClosedN (fun w ↦ w ∈ sample c) :=
  fun _ _ huv hv ↦ BranchingProcess.Subtree.mem_of_prefix huv hv

/-- **The graph of the sample tree** of an offspring field, the graph the four clauses
of `thm:regime-obstructions-general` speak of. -/
abbrev gSampleGraph (c : GWord N → ℕ) : SimpleGraph {w : GWord N // w ∈ sample c} :=
  wordGraphN (fun w : GWord N ↦ w ∈ sample c)

/-- **Two surviving children of a split**, the first two in letter order. -/
lemma exists_two_skeleton_children (h2 : 2 ≤ skeletonDegree d) :
    ∃ i₀ i₁ : Fin N, i₀ ≠ i₁ ∧ [i₀] ∈ skeleton d ∧ [i₁] ∈ skeleton d ∧
      bushAt d 0 = ambSub d [i₀] ∧ bushAt d 1 = ambSub d [i₁] := by
  have h0 : 0 < skeletonDegree d := by omega
  have h1 : 1 < skeletonDegree d := by omega
  refine ⟨(survivors d).orderEmbOfFin rfl ⟨0, h0⟩, (survivors d).orderEmbOfFin rfl ⟨1, h1⟩,
    fun h ↦ ?_, BranchingProcess.mem_survivors_iff_mem_skeleton.mp
      (BranchingProcess.orderEmbOfFin_mem_survivors h0),
    BranchingProcess.mem_survivors_iff_mem_skeleton.mp
      (BranchingProcess.orderEmbOfFin_mem_survivors h1),
    BranchingProcess.bushAt_of_lt h0, BranchingProcess.bushAt_of_lt h1⟩
  have := ((survivors d).orderEmbOfFin rfl).injective h
  simp at this

/-- The letter of the first surviving child as a one-letter word, empty when no child
survives. -/
noncomputable def firstSurvivor (d : GWord N → ℕ) : GWord N :=
  if h : 0 < (survivors d).card then [(survivors d).orderEmbOfFin rfl ⟨0, h⟩] else []

lemma firstSurvivor_spec (hd : Survives d) :
    firstSurvivor d ∈ skeleton d ∧ (firstSurvivor d).length = 1 ∧
      bushAt d 0 = ambSub d (firstSurvivor d) := by
  have h0 : 0 < (survivors d).card :=
    Nat.pos_of_ne_zero (BranchingProcess.survives_iff_skeletonDegree_ne_zero.mp hd)
  rw [firstSurvivor, dif_pos h0]
  exact ⟨BranchingProcess.mem_survivors_iff_mem_skeleton.mp
    (BranchingProcess.orderEmbOfFin_mem_survivors h0), rfl, BranchingProcess.bushAt_of_lt h0⟩

/-- **The ambient vertex reached by `n` steps of the neck descent** `neckIter`. -/
noncomputable def neckVertex (c : GWord N → ℕ) : ℕ → GWord N
  | 0 => []
  | n + 1 => neckVertex c n ++ firstSurvivor (neckIter c n)

@[simp] lemma neckVertex_zero (c : GWord N → ℕ) : neckVertex c 0 = [] := rfl

lemma neckVertex_succ (c : GWord N → ℕ) (n : ℕ) :
    neckVertex c (n + 1) = neckVertex c n ++ firstSurvivor (neckIter c n) := rfl

/-- **The neck descent at ambient vertices**: on survival the `n`-th step of `neckIter`
is the residual field at a skeleton vertex of depth `n`. -/
lemma neckVertex_spec (hc : Survives c) : ∀ n,
    neckVertex c n ∈ skeleton c ∧ (neckVertex c n).length = n ∧
      neckIter c n = ambSub c (neckVertex c n)
  | 0 => ⟨BranchingProcess.nil_mem_skeleton_iff.mpr hc, rfl, by simp⟩
  | n + 1 => by
      obtain ⟨hmem, hlen, heq⟩ := neckVertex_spec hc n
      have hsamp : neckVertex c n ∈ sample c := BranchingProcess.skeleton_subset_sample _ hmem
      have hsurv : Survives (ambSub c (neckVertex c n)) :=
        (mem_skeleton_iff_survives_ambSub hsamp).mp hmem
      obtain ⟨hfs, hfl, hfb⟩ := firstSurvivor_spec hsurv
      rw [neckVertex_succ, heq]
      refine ⟨(mem_skeleton_ambSub_iff hsamp).mp hfs, ?_, ?_⟩
      · rw [List.length_append, hlen, hfl]
      · rw [neckIter_succ_right, heq, hfb, ambSub_ambSub]

/-- The neck descent is a chain of children. -/
lemma isChain_neckVertex (hc : Survives c) : IsChain (neckVertex c) := by
  intro n
  obtain ⟨hmem, -, heq⟩ := neckVertex_spec hc n
  have hsurv : Survives (ambSub c (neckVertex c n)) :=
    (mem_skeleton_iff_survives_ambSub (BranchingProcess.skeleton_subset_sample _ hmem)).mp hmem
  obtain ⟨-, hfl, -⟩ := firstSurvivor_spec hsurv
  rw [neckVertex_succ, heq]
  obtain ⟨j, hj⟩ := List.length_eq_one_iff.mp hfl
  exact ⟨j, by rw [hj]⟩

/-- Iterating the descent adds the step counts. -/
lemma neckIter_add (c : GWord N → ℕ) : ∀ a b, neckIter (neckIter c a) b = neckIter c (a + b)
  | 0, _ => by rw [neckIter_zero, Nat.zero_add]
  | a + 1, b => by
      rw [neckIter_succ, neckIter_add (bushAt c 0) a b, ← neckIter_succ]
      congr 1
      omega

/-- The iterates of one neck step are the neck descent. -/
lemma iterate_bushAt_zero (c : GWord N → ℕ) :
    ∀ n, (fun d : GWord N → ℕ ↦ bushAt d 0)^[n] c = neckIter c n
  | 0 => rfl
  | n + 1 => by
      rw [Function.iterate_succ_apply', iterate_bushAt_zero c n, neckIter_succ_right]

/-- The iterates of `n` neck steps are the neck descent at multiples of `n`. -/
lemma iterate_neckIter (c : GWord N → ℕ) (n : ℕ) :
    ∀ k, (fun d : GWord N → ℕ ↦ neckIter d n)^[k] c = neckIter c (k * n)
  | 0 => by simp
  | k + 1 => by
      rw [Function.iterate_succ_apply', iterate_neckIter c n k, neckIter_add]
      congr 1
      ring

/-- **The first dying subtree is the residual field at a dying child.** -/
lemma exists_dyingAt_zero_eq_ambSub (hdN : d [] ≤ N) (hlt : skeletonDegree d < d []) :
    ∃ i : Fin N, (i : ℕ) < d [] ∧ ¬ Survives (ambSub d [i]) ∧ dyingAt d 0 = ambSub d [i] := by
  classical
  set S := BranchingProcess.childSet N (d []) \ survivors d with hS
  have hsub := BranchingProcess.survivors_subset d
  have hcard : S.card = d [] - skeletonDegree d := by
    rw [hS, Finset.card_sdiff_of_subset hsub, BranchingProcess.card_childSet hdN]
    rfl
  have hpos : 0 < S.card := by omega
  have hmem : S.orderEmbOfFin rfl ⟨0, hpos⟩
      ∈ BranchingProcess.childSet N (d []) \ survivors d := Finset.orderEmbOfFin_mem _ _ _
  rw [Finset.mem_sdiff] at hmem
  refine ⟨S.orderEmbOfFin rfl ⟨0, hpos⟩, BranchingProcess.mem_childSet.mp hmem.1, ?_, ?_⟩
  · intro hsurv
    exact hmem.2 (BranchingProcess.mem_survivors.mpr
      ⟨BranchingProcess.mem_childSet.mp hmem.1, hsurv⟩)
  · rw [dyingAt, BranchingProcess.bushOf, dif_pos hpos]
    rfl

/-- In a sample all of whose vertices have children, every residual field survives. -/
lemma survives_ambSub_of_forall_pos (hN : 0 < N) (hpos : ∀ v, 1 ≤ c v) {v : GWord N}
    (hv : v ∈ sample c) : Survives (ambSub c v) := by
  have hmem : ∀ k, v ++ List.replicate k ⟨0, hN⟩ ∈ sample c := by
    intro k
    induction k with
    | zero => simpa using hv
    | succ k ih =>
        rw [List.replicate_succ', ← List.append_assoc]
        exact BranchingProcess.mem_sample_append_singleton.mpr ⟨ih, hpos _⟩
  have hinj : Function.Injective fun k : ℕ ↦ (List.replicate k (⟨0, hN⟩ : Fin N) : GWord N) :=
    fun k l h ↦ by simpa using congrArg List.length h
  exact Set.infinite_of_injective_forall_mem hinj fun k ↦ (mem_sample_ambSub_iff hv).mpr (hmem k)

end Bridge

/-! ### The skeleton weights at the ends of the support -/

section Weights

variable (θ : Offspring J)

/-- The largest arity keeps positive skeleton weight at every extinction probability. -/
lemma skeletonWeight_top_pos (hq : θ.extinction < 1) (hJ1 : 1 ≤ J) (hθJ : 0 < θ J) :
    0 < θ.skeletonWeight J := by
  have h1q : (0 : ℝ) < 1 - θ.extinction := by linarith
  have hterm : (0 : ℝ) < θ J * (J.choose J : ℝ) * (1 - θ.extinction) ^ J
      * θ.extinction ^ (J - J) := by
    rw [Nat.choose_self, Nat.sub_self, pow_zero]
    simp only [Nat.cast_one, mul_one]
    positivity
  have hnonneg : ∀ j ∈ Finset.range (J + 1),
      (0 : ℝ) ≤ θ j * (j.choose J : ℝ) * (1 - θ.extinction) ^ J * θ.extinction ^ (j - J) := by
    intro j _
    have h1 := θ.nonneg j
    have h2 := θ.extinction_nonneg
    positivity
  have hsum : θ J * (J.choose J : ℝ) * (1 - θ.extinction) ^ J * θ.extinction ^ (J - J)
      ≤ θ.surviveWeight J := by
    rw [BranchingProcess.Offspring.surviveWeight]
    exact Finset.single_le_sum hnonneg (Finset.self_mem_range_succ J)
  rw [BranchingProcess.Offspring.skeletonWeight_of_ne_zero θ (by omega)]
  exact div_pos (lt_of_lt_of_le hterm hsum) h1q

/-- Arity one keeps positive skeleton weight once `θ₁ > 0`. -/
lemma skeletonWeight_one_pos (hq : θ.extinction < 1) (hJ1 : 1 ≤ J) (h1 : 0 < θ 1) :
    0 < θ.skeletonWeight 1 := by
  have h1q : (0 : ℝ) < 1 - θ.extinction := by linarith
  have hterm : (0 : ℝ) < θ 1 * ((1 : ℕ).choose 1 : ℝ) * (1 - θ.extinction) ^ 1
      * θ.extinction ^ (1 - 1) := by
    simp only [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, mul_one, pow_one]
    positivity
  have hnonneg : ∀ j ∈ Finset.range (J + 1),
      (0 : ℝ) ≤ θ j * (j.choose 1 : ℝ) * (1 - θ.extinction) ^ 1 * θ.extinction ^ (j - 1) := by
    intro j _
    have h1 := θ.nonneg j
    have h2 := θ.extinction_nonneg
    positivity
  have hsum : θ 1 * ((1 : ℕ).choose 1 : ℝ) * (1 - θ.extinction) ^ 1 * θ.extinction ^ (1 - 1)
      ≤ θ.surviveWeight 1 := by
    rw [BranchingProcess.Offspring.surviveWeight]
    exact Finset.single_le_sum hnonneg (Finset.mem_range.mpr (by omega))
  rw [BranchingProcess.Offspring.skeletonWeight_of_ne_zero θ one_ne_zero]
  exact div_pos (lt_of_lt_of_le hterm hsum) h1q

/-- **The neck weight is below one** once the law charges an arity of at least two:
`θ̃₁ + θ̃_J ≤ 1` with `θ̃_J > 0`. -/
lemma skeletonWeight_one_lt_one_of_top (hq : θ.extinction < 1) (hJ2 : 2 ≤ J)
    (hθJ : 0 < θ J) : θ.skeletonWeight 1 < 1 := by
  have hsum := BranchingProcess.Offspring.sum_skeletonWeight θ hq
  have hJpos := skeletonWeight_top_pos θ hq (by omega) hθJ
  have hnonneg : ∀ j ∈ Finset.range (J + 1), 0 ≤ θ.skeletonWeight j := fun j _ ↦
    θ.skeletonWeight_nonneg hq j
  have hsub : ({1, J} : Finset ℕ) ⊆ Finset.range (J + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ ↦ hnonneg j hj)
  rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ J)] at hle
  linarith

/-- The skeleton weights sum to one over the alphabet. -/
lemma sum_ofReal_skeletonWeight (hJN : J ≤ N) (hq : θ.extinction < 1) :
    ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (θ.skeletonWeight k) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ θ.skeletonWeight_nonneg hq k),
    ← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : J + 1 ≤ N + 1))
      (fun k _ hk ↦ θ.skeletonWeight_vanishing (by simp only [Finset.mem_range] at hk; omega)),
    θ.sum_skeletonWeight hq, ENNReal.ofReal_one]

end Weights

/-! ### The neck descent preserves the conditioned law -/

section LawPreserving

variable (θ : Offspring J)

/-- Survival is almost sure under the conditioned law. -/
lemma ae_survives (hJN : J ≤ N) (hq : θ.extinction < 1) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, Survives c := by
  rw [ae_iff]
  exact survivalMeasure_compl_survives θ hJN hq

/-- The skeleton degree is bounded by the alphabet. -/
lemma skeletonDegree_le_alphabet (c : GWord N → ℕ) : skeletonDegree c ≤ N := by
  rw [BranchingProcess.skeletonDegree]
  exact (Finset.card_le_univ _).trans (by simp)

/-- **One neck step preserves the law**: the first surviving subtree of the root is
again a conditioned sample, the skeleton weights summing to one. -/
theorem survivalMeasure_bushAt_zero_preimage (hJN : J ≤ N) (hq : θ.extinction < 1)
    {A : Set (GWord N → ℕ)} (hA : MeasurableSet A) :
    survivalMeasure (N := N) θ ((fun c ↦ bushAt c 0) ⁻¹' A) = survivalMeasure (N := N) θ A := by
  classical
  haveI := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  set A' : ℕ → Set (GWord N → ℕ) := fun m ↦ if m = 0 then A else Set.univ with hA'
  have hA'meas : ∀ m, MeasurableSet (A' m) := by
    intro m
    simp only [hA']
    split
    · exact hA
    · exact MeasurableSet.univ
  have hcover : (fun c ↦ bushAt c 0) ⁻¹' A ∪ {c : GWord N → ℕ | skeletonDegree c = 0}
      = ⋃ k ∈ Finset.range (N + 1), ({c : GWord N → ℕ | skeletonDegree c = k}
          ∩ {c : GWord N → ℕ | ∀ m, m < k → bushAt c m ∈ A' m}) := by
    ext c
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_inter_iff, Finset.mem_range, exists_prop]
    constructor
    · rintro (h | h)
      · refine ⟨skeletonDegree c, by have := skeletonDegree_le_alphabet c; omega, rfl,
          fun m _ ↦ ?_⟩
        simp only [hA']
        split
        · next hm => rw [hm]; exact h
        · trivial
      · exact ⟨0, by omega, h, fun m hm ↦ absurd hm (Nat.not_lt_zero m)⟩
    · rintro ⟨k, -, hdeg, hm⟩
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · exact Or.inr hdeg
      · left
        have := hm 0 hkpos
        simpa [hA'] using this
  have hnull : survivalMeasure (N := N) θ {c : GWord N → ℕ | skeletonDegree c = 0} = 0 := by
    rw [BranchingProcess.survivalMeasure_skeletonDegree θ hJN hq 0,
      BranchingProcess.Offspring.skeletonWeight_zero, ENNReal.ofReal_zero]
  have h1 : survivalMeasure (N := N) θ ((fun c ↦ bushAt c 0) ⁻¹' A)
      = survivalMeasure (N := N) θ
        ((fun c ↦ bushAt c 0) ⁻¹' A ∪ {c : GWord N → ℕ | skeletonDegree c = 0}) :=
    le_antisymm (measure_mono Set.subset_union_left)
      ((measure_union_le _ _).trans (by rw [hnull, add_zero]))
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (N + 1)) : Set ℕ)
      fun k ↦ ({c : GWord N → ℕ | skeletonDegree c = k}
        ∩ {c : GWord N → ℕ | ∀ m, m < k → bushAt c m ∈ A' m}) := by
    intro k _ k' _ hkk
    refine Set.disjoint_left.mpr fun c hc hc' ↦ hkk ?_
    rw [← hc.1, ← hc'.1]
  have hmeas : ∀ k ∈ Finset.range (N + 1), MeasurableSet
      ({c : GWord N → ℕ | skeletonDegree c = k}
        ∩ {c : GWord N → ℕ | ∀ m, m < k → bushAt c m ∈ A' m}) := by
    intro k _
    refine (BranchingProcess.measurableSet_skeletonDegree_eq k).inter ?_
    have he : {c : GWord N → ℕ | ∀ m, m < k → bushAt c m ∈ A' m}
        = ⋂ m ∈ Finset.range k, (fun c : GWord N → ℕ ↦ bushAt c m) ⁻¹' (A' m) := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
    rw [he]
    exact MeasurableSet.biInter (Set.to_countable _) fun m _ ↦
      BranchingProcess.measurable_bushAt m (hA'meas m)
  have hterm : ∀ k, ENNReal.ofReal (θ.skeletonWeight k)
      * ∏ m ∈ Finset.range k, survivalMeasure (N := N) θ (A' m)
      = ENNReal.ofReal (θ.skeletonWeight k) * survivalMeasure (N := N) θ A := by
    intro k
    cases k with
    | zero => simp
    | succ k =>
        rw [Finset.prod_range_succ']
        have hone : ∀ m ∈ Finset.range k, survivalMeasure (N := N) θ (A' (m + 1)) = 1 := by
          intro m _
          simp [hA']
        rw [Finset.prod_congr rfl hone, Finset.prod_const_one, one_mul]
        simp [hA']
  rw [h1, hcover, measure_biUnion_finset hdisj hmeas]
  simp_rw [BranchingProcess.survivalMeasure_skeletonDegree_bushes θ hJN hq _ hA'meas, hterm]
  rw [← Finset.sum_mul, sum_ofReal_skeletonWeight θ hJN hq, one_mul]

/-- **The neck descent preserves the law**, at any number of steps. -/
theorem survivalMeasure_neckIter_preimage (hJN : J ≤ N) (hq : θ.extinction < 1) (n : ℕ) :
    ∀ {A : Set (GWord N → ℕ)}, MeasurableSet A →
      survivalMeasure (N := N) θ ((fun c ↦ neckIter c n) ⁻¹' A)
        = survivalMeasure (N := N) θ A := by
  induction n with
  | zero => intro A _; simp
  | succ n ih =>
      intro A hA
      have he : (fun c : GWord N → ℕ ↦ neckIter c (n + 1)) ⁻¹' A
          = (fun c ↦ neckIter c n) ⁻¹' ((fun d ↦ bushAt d 0) ⁻¹' A) := by
        ext c
        simp [neckIter_succ_right]
      rw [he, ih (BranchingProcess.measurable_bushAt 0 hA),
        survivalMeasure_bushAt_zero_preimage θ hJN hq hA]

end LawPreserving

/-! ### Splits below splits -/

section Splits

variable (θ : Offspring J)

/-- **The descent from the root splits**, almost surely. -/
theorem ae_gArity_ge_two (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) : ∀ᵐ c ∂survivalMeasure (N := N) θ, 2 ≤ gArity c := by
  rw [ae_iff]
  refine measure_mono_null (fun c hc ↦ ?_)
    (measure_union_null (survivalMeasure_gArity_eq_one θ hJN hq hs1)
      (survivalMeasure_compl_survives θ hJN hq))
  simp only [Set.mem_setOf_eq, not_le] at hc
  by_cases hs : Survives c
  · left
    have := one_le_gArity_of_survives hs
    show gArity c = 1
    omega
  · exact Or.inr hs

/-- **The descent from the second child of the first split splits**, almost surely:
the subtrees below the split are independent conditioned samples. -/
theorem ae_gArity_gSplitBush_ge_two (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1 : θ.skeletonWeight 1 < 1) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, 2 ≤ gArity (gSplitBush c 1) := by
  classical
  set A : ℕ → Set (GWord N → ℕ) :=
    fun m ↦ if m = 1 then {d : GWord N → ℕ | gArity d = 1} else Set.univ with hA
  have hAmeas : ∀ m, MeasurableSet (A m) := by
    intro m
    simp only [hA]
    split
    · exact fibreMeasurableG_gArity 1
    · exact MeasurableSet.univ
  have hnull : ∀ κ : ℕ, 2 ≤ κ → survivalMeasure (N := N) θ
      ({c : GWord N → ℕ | gArity c = κ}
        ∩ {c : GWord N → ℕ | ∀ m, m < κ → gSplitBush c m ∈ A m}) = 0 := by
    intro κ hκ
    rw [survivalMeasure_gArityPair θ hJN hq hs1 hκ hAmeas,
      Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : 1 < κ)), mul_zero]
    simp only [hA, if_pos rfl]
    exact survivalMeasure_gArity_eq_one θ hJN hq hs1
  rw [ae_iff]
  refine measure_mono_null (fun c hc ↦ ?_)
    (measure_union_null (ae_iff.mp (ae_gArity_ge_two θ hJN hq hs1))
      (measure_iUnion_null fun κ ↦ measure_iUnion_null fun hκ ↦ hnull κ hκ))
  simp only [Set.mem_setOf_eq, not_le] at hc
  by_cases h2 : 2 ≤ gArity c
  · right
    have hsurv : Survives (gSplitBush c 1) := survives_gSplitBush (by omega)
    have hone := one_le_gArity_of_survives hsurv
    refine Set.mem_iUnion.mpr ⟨gArity c, Set.mem_iUnion.mpr ⟨h2, rfl, fun m _ ↦ ?_⟩⟩
    simp only [hA]
    split
    · next hm => rw [hm]; show gArity (gSplitBush c 1) = 1; omega
    · trivial
  · left
    exact h2

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-rays`), read in the
sample.**  The descent from the root ends at a split `u`; the descent from its second
surviving child ends at a split `v`; two skeleton rays out of two children of `v` and
the climb from `v` to `u` followed by a skeleton ray out of the first child of `u` are
three rays out of `v`, pairwise meeting only there. -/
theorem hasThreeRaysN_sample {c : GWord N → ℕ} (hsurv : Survives c) (h2 : 2 ≤ gArity c)
    (h2' : 2 ≤ gArity (gSplitBush c 1)) : HasThreeRaysN (fun w : GWord N ↦ w ∈ sample c) := by
  -- the first split
  obtain ⟨hu, -, hueq⟩ := neckVertex_spec hsurv (gSplitDepth c)
  set u := neckVertex c (gSplitDepth c)
  have husamp : u ∈ sample c := BranchingProcess.skeleton_subset_sample _ hu
  have hfield : gSplitField c = ambSub c u := hueq
  have hdeg : 2 ≤ skeletonDegree (ambSub c u) := by
    rw [← hfield]
    exact h2
  obtain ⟨i₀, i₁, hi, hi₀, hi₁, -, hb₁⟩ := exists_two_skeleton_children hdeg
  have hui₀ : u ++ [i₀] ∈ skeleton c := (mem_skeleton_ambSub_iff husamp).mp hi₀
  have hui₁ : u ++ [i₁] ∈ skeleton c := (mem_skeleton_ambSub_iff husamp).mp hi₁
  have hui₁s : u ++ [i₁] ∈ sample c := BranchingProcess.skeleton_subset_sample _ hui₁
  have hd : gSplitBush c 1 = ambSub c (u ++ [i₁]) := by
    rw [gSplitBush, hfield, hb₁, ambSub_ambSub]
  -- the second split, below the second child of the first
  have hdsurv : Survives (ambSub c (u ++ [i₁])) :=
    (mem_skeleton_iff_survives_ambSub hui₁s).mp hui₁
  rw [hd] at h2'
  obtain ⟨hv', -, hveq⟩ := neckVertex_spec hdsurv (gSplitDepth (ambSub c (u ++ [i₁])))
  set v' := neckVertex (ambSub c (u ++ [i₁])) (gSplitDepth (ambSub c (u ++ [i₁])))
  have hv : u ++ [i₁] ++ v' ∈ skeleton c := (mem_skeleton_ambSub_iff hui₁s).mp hv'
  have hvsamp : u ++ [i₁] ++ v' ∈ sample c := BranchingProcess.skeleton_subset_sample _ hv
  have hdeg' : 2 ≤ skeletonDegree (ambSub c (u ++ [i₁] ++ v')) := by
    have : gArity (ambSub c (u ++ [i₁]))
        = skeletonDegree (ambSub c (u ++ [i₁] ++ v')) := by
      rw [gArity, gSplitField, hveq, ambSub_ambSub]
    rw [← this]
    exact h2'
  obtain ⟨j₀, j₁, hj, hj₀, hj₁, -, -⟩ := exists_two_skeleton_children hdeg'
  have hvj₀ := (mem_skeleton_ambSub_iff hvsamp).mp hj₀
  have hvj₁ := (mem_skeleton_ambSub_iff hvsamp).mp hj₁
  -- the three skeleton rays
  obtain ⟨r₁, hr₁0, hr₁mem, hr₁⟩ := BranchingProcess.exists_skeleton_ray hvj₀
  obtain ⟨r₂, hr₂0, hr₂mem, hr₂⟩ := BranchingProcess.exists_skeleton_ray hvj₁
  obtain ⟨r₃, hr₃0, hr₃mem, hr₃⟩ := BranchingProcess.exists_skeleton_ray hui₀
  exact hasThreeRaysN_of_splits (prefixClosedN_sample c) hi hj hvsamp (List.prefix_append _ _)
    hr₁ hr₁0 (fun n ↦ BranchingProcess.skeleton_subset_sample _ (hr₁mem n))
    hr₂ hr₂0 (fun n ↦ BranchingProcess.skeleton_subset_sample _ (hr₂mem n))
    hr₃ hr₃0 (fun n ↦ BranchingProcess.skeleton_subset_sample _ (hr₃mem n))

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-rays`)**: almost surely
the sample carries three rays pairwise meeting only in their common initial vertex. -/
theorem threeRays_ae (hJN : J ≤ N) (hq : θ.extinction < 1) (hs1 : θ.skeletonWeight 1 < 1) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, HasThreeRaysN (fun w : GWord N ↦ w ∈ sample c) := by
  filter_upwards [ae_survives θ hJN hq, ae_gArity_ge_two θ hJN hq hs1,
    ae_gArity_gSplitBush_ge_two θ hJN hq hs1] with c hsurv h2 h2'
  exact hasThreeRaysN_sample hsurv h2 h2'

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-rays`)** under the
support hypotheses of the paper, `J ≥ 2` and `θ_J > 0`. -/
theorem threeRays_ae_of_top (hJN : J ≤ N) (hq : θ.extinction < 1) (hJ2 : 2 ≤ J)
    (hθJ : 0 < θ J) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, HasThreeRaysN (fun w : GWord N ↦ w ∈ sample c) :=
  threeRays_ae θ hJN hq (skeletonWeight_one_lt_one_of_top θ hq hJ2 hθJ)

end Splits

/-! ### Near a line at `θ₀ = 0` -/

section Lines

variable (θ : Offspring J)

/-- At `θ₀ = 0` every vertex has a child, almost surely. -/
lemma ae_forall_pos_of_zero (h0 : θ 0 = 0) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, ∀ v : GWord N, 1 ≤ c v := by
  refine ae_all_iff.mpr fun v ↦ ?_
  rw [ae_iff]
  have hs : BranchingProcess.sampleMeasure (N := N) θ {c : GWord N → ℕ | ¬ 1 ≤ c v} = 0 := by
    have he : {c : GWord N → ℕ | ¬ 1 ≤ c v} = {c : GWord N → ℕ | c v = 0} := by
      ext c
      simp
    rw [he, BranchingProcess.sampleMeasure_coord θ v 0, h0, ENNReal.ofReal_zero]
  rw [BranchingProcess.survivalMeasure_apply]
  exact mul_eq_zero.mpr (Or.inr (measure_mono_null Set.inter_subset_right hs))

/-- The alphabet is nonempty once the law has no mass at zero. -/
lemma pos_of_zero (hJN : J ≤ N) (h0 : θ 0 = 0) : 0 < N := by
  by_contra hN
  have hJ : J = 0 := Nat.eq_zero_of_le_zero (hJN.trans (Nat.le_of_not_lt hN))
  subst hJ
  have htot := θ.total
  rw [Finset.sum_range_one, h0] at htot
  exact zero_ne_one htot

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-lines`), read in the
sample**: with every vertex carrying a child and the descent from the root ending at a
split, every vertex lies within the depth of that split of a line. -/
theorem nearLineN_sample (hN : 0 < N) {c : GWord N → ℕ} (hsurv : Survives c)
    (h2 : 2 ≤ gArity c) (hpos : ∀ v : GWord N, 1 ≤ c v) :
    NearLineN (fun w : GWord N ↦ w ∈ sample c) := by
  have hchild : ∀ w : GWord N, w ∈ sample c → ∃ j : Fin N, w ++ [j] ∈ sample c := fun w hw ↦
    ⟨⟨0, hN⟩, BranchingProcess.mem_sample_append_singleton.mpr ⟨hw, by
      have := hpos w
      show 0 < c w
      omega⟩⟩
  obtain ⟨hu, -, hueq⟩ := neckVertex_spec hsurv (gSplitDepth c)
  set u := neckVertex c (gSplitDepth c)
  have husamp : u ∈ sample c := BranchingProcess.skeleton_subset_sample _ hu
  have hdeg : 2 ≤ skeletonDegree (ambSub c u) := by
    have hfield : gSplitField c = ambSub c u := hueq
    rw [← hfield]
    exact h2
  obtain ⟨i₀, i₁, hi, hi₀, hi₁, -, -⟩ := exists_two_skeleton_children hdeg
  exact nearLineN_of_split (prefixClosedN_sample c) hchild hi
    (BranchingProcess.skeleton_subset_sample _ ((mem_skeleton_ambSub_iff husamp).mp hi₀))
    (BranchingProcess.skeleton_subset_sample _ ((mem_skeleton_ambSub_iff husamp).mp hi₁))

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-lines`)**: at `θ₀ = 0`,
almost surely every vertex of the sample lies within a bounded distance of a line. -/
theorem nearLine_gSample_ae (hJN : J ≤ N) (hq : θ.extinction < 1) (h0 : θ 0 = 0)
    (hs1 : θ.skeletonWeight 1 < 1) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, NearLineN (fun w : GWord N ↦ w ∈ sample c) := by
  filter_upwards [ae_survives θ hJN hq, ae_gArity_ge_two θ hJN hq hs1,
    ae_forall_pos_of_zero θ h0] with c hsurv h2 hpos
  exact nearLineN_sample (pos_of_zero θ hJN h0) hsurv h2 hpos

end Lines

/-! ### Thin balls at `θ₀ = 0 < θ₁` -/

section ThinBalls

variable (θ : Offspring J)

/-- The memorylessness of the neck, in the form the iteration scheme consumes. -/
lemma survivalMeasure_missEvent_inter (hJN : J ≤ N) (hq : θ.extinction < 1) (n : ℕ)
    {A : Set (GWord N → ℕ)} (hA : MeasurableSet A) :
    survivalMeasure (N := N) θ
        (missEvent (N := N) n Set.univ ∩ (fun c ↦ neckIter c n) ⁻¹' A)
      = ENNReal.ofReal (θ.skeletonWeight 1) ^ n * survivalMeasure (N := N) θ A := by
  have he : missEvent (N := N) n Set.univ ∩ (fun c ↦ neckIter c n) ⁻¹' A
      = missEvent (N := N) n A := by
    ext c
    simp [missEvent]
  rw [he, survivalMeasure_missEvent θ hJN hq n hA]

/-- **Necks of every length**, almost surely: the neck descent carries a run of `n`
neck vertices somewhere. -/
theorem ae_exists_neck (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hs1pos : 0 < θ.skeletonWeight 1) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, ∀ n : ℕ, ∃ k : ℕ,
      ∀ i, i < n → skeletonDegree (neckIter c (k * n + i)) = 1 := by
  haveI := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  refine ae_all_iff.mpr fun n ↦ ?_
  have hp : ENNReal.ofReal (θ.skeletonWeight 1) ^ n ≠ 0 :=
    pow_ne_zero n (ENNReal.ofReal_pos.mpr hs1pos).ne'
  filter_upwards [ae_exists_iterate_mem (μ := survivalMeasure (N := N) θ)
    (Φ := fun c ↦ neckIter c n) (D := missEvent (N := N) n Set.univ) (measurable_neckIter n)
    (fun A hA ↦ survivalMeasure_neckIter_preimage θ hJN hq n hA)
    (measurableSet_missEvent n MeasurableSet.univ)
    (fun A hA ↦ survivalMeasure_missEvent_inter θ hJN hq n hA) hp] with c hc
  obtain ⟨k, hk⟩ := hc
  rw [iterate_neckIter] at hk
  refine ⟨k, fun i hi ↦ ?_⟩
  have := hk.1 i hi
  rwa [neckIter_add] at this

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-thin`), read in the
sample**: a run of `2ℓ` neck vertices along the neck descent, in a sample all of whose
vertices have children, is a chain whose vertices have no other child, and its
midpoint has a thin ball. -/
theorem hasThinBallsN_sample (hN : 0 < N) {c : GWord N → ℕ} (hsurv : Survives c)
    (hpos : ∀ v : GWord N, 1 ≤ c v)
    (hneck : ∀ n : ℕ, ∃ k : ℕ, ∀ i, i < n → skeletonDegree (neckIter c (k * n + i)) = 1) :
    HasThinBallsN (fun w : GWord N ↦ w ∈ sample c) := by
  refine hasThinBallsN_of_necks (prefixClosedN_sample c) fun ℓ ↦ ?_
  obtain ⟨k, hk⟩ := hneck (2 * ℓ)
  refine ⟨fun i ↦ neckVertex c (k * (2 * ℓ) + i), fun i ↦ isChain_neckVertex hsurv _,
    BranchingProcess.skeleton_subset_sample _ (neckVertex_spec hsurv _).1, fun i hi j hTj ↦ ?_⟩
  obtain ⟨hx, -, hxeq⟩ := neckVertex_spec hsurv (k * (2 * ℓ) + i)
  set x := neckVertex c (k * (2 * ℓ) + i)
  have hxs : x ∈ sample c := BranchingProcess.skeleton_subset_sample _ hx
  have hdeg1 : skeletonDegree (ambSub c x) = 1 := by
    rw [← hxeq]
    exact hk i hi
  have hxsurv : Survives (ambSub c x) := (mem_skeleton_iff_survives_ambSub hxs).mp hx
  -- the child `j` survives, so it is the unique survivor
  have hj : j ∈ survivors (ambSub c x) := by
    refine BranchingProcess.mem_survivors.mpr ⟨?_, ?_⟩
    · have := (BranchingProcess.mem_sample_append_singleton.mp hTj).2
      simpa [ambSub] using this
    · have := survives_ambSub_of_forall_pos hN hpos hTj
      rwa [← ambSub_ambSub] at this
  obtain ⟨j', hj'⟩ := Finset.card_eq_one.mp hdeg1
  rw [hj', Finset.mem_singleton] at hj
  -- the neck descent continues through that survivor
  obtain ⟨hfs, hfl, -⟩ := firstSurvivor_spec hxsurv
  obtain ⟨e, he⟩ := List.length_eq_one_iff.mp hfl
  rw [he] at hfs
  have hes : e ∈ survivors (ambSub c x) :=
    BranchingProcess.mem_survivors_iff_mem_skeleton.mpr hfs
  rw [hj', Finset.mem_singleton] at hes
  show x ++ [j] = neckVertex c (k * (2 * ℓ) + i + 1)
  rw [neckVertex_succ, hxeq, he, hj, hes]

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-thin`)**: at
`θ₀ = 0 < θ₁`, almost surely the sample has a thin ball at every radius. -/
theorem thinBalls_gSample_ae (hJN : J ≤ N) (hq : θ.extinction < 1) (h0 : θ 0 = 0)
    (h1 : 0 < θ 1) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, HasThinBallsN (fun w : GWord N ↦ w ∈ sample c) := by
  have hJ1 : 1 ≤ J := by
    by_contra hJ
    rw [θ.vanishing 1 (by omega)] at h1
    exact lt_irrefl 0 h1
  filter_upwards [ae_survives θ hJN hq, ae_forall_pos_of_zero θ h0,
    ae_exists_neck θ hJN hq (skeletonWeight_one_pos θ hq hJ1 h1)] with c hsurv hpos hneck
  exact hasThinBallsN_sample (pos_of_zero θ hJN h0) hsurv hpos hneck

end ThinBalls

/-! ### Hairs of unbounded depth at `θ₀ > 0` -/

section Hairs

variable (θ : Offspring J)

/-- The event that a field has a vertex at depth `n`. -/
def deepEvent (n : ℕ) : Set (GWord N → ℕ) :=
  {d | ∃ w : GWord N, w.length = n ∧ w ∈ sample d}

lemma measurableSet_deepEvent (n : ℕ) : MeasurableSet (deepEvent (N := N) n) := by
  have he : deepEvent (N := N) n
      = ⋃ w ∈ {w : GWord N | w.length = n}, {d : GWord N → ℕ | w ∈ sample d} := by
    ext d
    simp [deepEvent]
  rw [he]
  exact MeasurableSet.biUnion (Set.to_countable _) fun w _ ↦
    BranchingProcess.measurableSet_mem_sample w

/-- **A deep bush has positive conjugate mass**: the complete `J`-ary tree of height
`n` is charged, since `θ_J > 0` and `θ₀ > 0`. -/
theorem bushMeasure_deepEvent_pos (hJN : J ≤ N) (hq0 : 0 < θ.extinction) (hJ1 : 1 ≤ J)
    (hθJ : 0 < θ J) (n : ℕ) : 0 < bushMeasure (N := N) θ (deepEvent n) := by
  have hN : 0 < N := by omega
  have hθ0 : 0 < θ 0 := by
    refine lt_of_le_of_ne (θ.nonneg 0) fun h ↦ ?_
    exact hq0.ne' (θ.extinction_eq_zero_iff.mpr h.symm)
  set e : GWord N → ℕ := fun v ↦ if v.length < n then J else 0 with he
  have hbound : ∀ v ∈ sample e, v.length ≤ n := by
    intro v hv
    by_contra hlt
    push Not at hlt
    have h := (BranchingProcess.mem_sample_iff'.mp hv) n hlt
    have h0 : e (v.take n) = 0 := by
      simp only [he, List.length_take]
      rw [if_neg (by omega)]
    rw [h0] at h
    exact absurd h (Nat.not_lt_zero _)
  have hfin : (sample e : Set (GWord N)).Finite :=
    (List.finite_length_le (Fin N) n).subset hbound
  have hmass : ∀ v ∈ sample e, min (θ J) (θ 0) ≤ θ (e v) := by
    intro v _
    simp only [he]
    split
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hpoint := BranchingProcess.ofReal_pow_le_bushMeasure_sample_eq θ hfin hmass
  have hdeep : List.replicate n (⟨0, hN⟩ : Fin N) ∈ sample e := by
    rw [BranchingProcess.mem_sample_iff']
    intro i hi
    rw [List.length_replicate] at hi
    simp only [List.getElem_replicate, List.take_replicate, he, List.length_replicate]
    rw [if_pos (by omega)]
    exact hJ1
  have hsub : {c : GWord N → ℕ | (sample c : Set (GWord N)) = (sample e : Set (GWord N))}
      ⊆ deepEvent n := by
    intro c hc
    refine ⟨List.replicate n ⟨0, hN⟩, List.length_replicate .., ?_⟩
    show List.replicate n (⟨0, hN⟩ : Fin N) ∈ (sample c : Set (GWord N))
    rw [hc]
    exact hdeep
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (min (θ J) (θ 0)) ^ (sample e : Set (GWord N)).ncard :=
        ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (lt_min hθJ hθ0)) _
    _ ≤ bushMeasure (N := N) θ
        {c : GWord N → ℕ | (sample c : Set (GWord N)) = (sample e : Set (GWord N))} := hpoint
    _ ≤ bushMeasure (N := N) θ (deepEvent n) := measure_mono hsub

/-- The constraint sets of the witness decoration: the first dying subtree is deep. -/
def hairSets (n : ℕ) : ℕ → Set (GWord N → ℕ) :=
  fun m ↦ if m = 0 then deepEvent n else Set.univ

lemma measurableSet_hairSets (n m : ℕ) : MeasurableSet (hairSets (N := N) n m) := by
  rw [hairSets]
  split
  · exact measurableSet_deepEvent n
  · exact MeasurableSet.univ

/-- **The witness decoration**: a neck vertex of full offspring whose first dying
subtree reaches depth `n`. -/
def hairEvent (J : ℕ) (n : ℕ) : Set (GWord N → ℕ) := decorationEvent J 1 (hairSets n)

lemma measurableSet_hairEvent (n : ℕ) : MeasurableSet (hairEvent (N := N) J n) :=
  BranchingProcess.measurableSet_decorationEvent J 1 (measurableSet_hairSets n)

/-- The mass of the witness decoration. -/
noncomputable def hairMass (n : ℕ) : ℝ≥0∞ := decorationMass (N := N) θ J 1 (hairSets n)

/-- **The witness decoration has positive mass.** -/
lemma hairMass_ne_zero (hJN : J ≤ N) (hq : θ.extinction < 1) (hq0 : 0 < θ.extinction)
    (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) (n : ℕ) : hairMass (N := N) θ n ≠ 0 := by
  haveI := BranchingProcess.isProbabilityMeasure_bushMeasure (N := N) θ hJN hq0
  rw [hairMass, decorationMass]
  refine mul_ne_zero ?_ ?_
  · have h1q : (0 : ℝ) < 1 - θ.extinction := by linarith
    have hJpos : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
    rw [Nat.choose_one_right]
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    have := θ.extinction_nonneg
    positivity
  · refine Finset.prod_ne_zero_iff.mpr fun m _ ↦ ?_
    rw [hairSets]
    split
    · exact (bushMeasure_deepEvent_pos θ hJN hq0 (by omega) hθJ n).ne'
    · rw [measure_univ]
      exact one_ne_zero

/-- The witness decoration at the root is independent of the subtree below its
surviving child, with the product mass. -/
lemma survivalMeasure_hairEvent_inter (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (n : ℕ) {A : Set (GWord N → ℕ)} (hA : MeasurableSet A) :
    survivalMeasure (N := N) θ (hairEvent J n ∩ (fun c ↦ bushAt c 0) ⁻¹' A)
      = hairMass (N := N) θ n * survivalMeasure (N := N) θ A := by
  classical
  set A' : ℕ → Set (GWord N → ℕ) := fun m ↦ if m = 0 then A else Set.univ with hA'
  have hA'meas : ∀ m, MeasurableSet (A' m) := by
    intro m
    simp only [hA']
    split
    · exact hA
    · exact MeasurableSet.univ
  have he : hairEvent J n ∩ (fun c ↦ bushAt c 0) ⁻¹' A
      = decorationEvent J 1 (hairSets n)
        ∩ {c : GWord N → ℕ | ∀ m, m < 1 → bushAt c m ∈ A' m} := by
    ext c
    simp [hairEvent, hA']
  rw [he, BranchingProcess.survivalMeasure_root_decorated θ hJN hq hq0 hJN one_ne_zero hA'meas
    (measurableSet_hairSets n), Finset.prod_range_one, hairMass]
  simp [hA']

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-hair`), read in the
sample**: a witness decoration along the neck descent is a neck vertex with a dying
child whose subtree reaches depth `n`, and the cone above that child is a finite
component of the punctured sample, a hair of depth exceeding `n`. -/
theorem unboundedHairsN_sample (hJN : J ≤ N) (hJ2 : 2 ≤ J) {c : GWord N → ℕ}
    (hsurv : Survives c) (hdeep : ∀ n, ∃ k, neckIter c k ∈ hairEvent (N := N) J n) :
    UnboundedHairsN (fun w : GWord N ↦ w ∈ sample c) := by
  refine unboundedHairsN_of_deep_cones (prefixClosedN_sample c) fun n ↦ ?_
  obtain ⟨k, hk⟩ := hdeep n
  obtain ⟨hx, -, hxeq⟩ := neckVertex_spec hsurv k
  set x := neckVertex c k
  have hxs : x ∈ sample c := BranchingProcess.skeleton_subset_sample _ hx
  rw [hxeq] at hk
  obtain ⟨⟨hroot, hdeg⟩, hdying⟩ := hk
  have hroot' : c x = J := by
    have h : ambSub c x [] = J := hroot
    rwa [ambSub_apply, List.append_nil] at h
  have hdeepdying : dyingAt (ambSub c x) 0 ∈ deepEvent n := by
    have h := hdying 0 (by show 0 < J - 1; omega)
    rwa [hairSets, if_pos rfl] at h
  obtain ⟨i, hi, hns, hieq⟩ := exists_dyingAt_zero_eq_ambSub
    (d := ambSub c x) (by show ambSub c x [] ≤ N; rw [hroot]; exact hJN)
    (by show skeletonDegree (ambSub c x) < ambSub c x []; rw [hroot, hdeg]; omega)
  rw [hieq, ambSub_ambSub] at hdeepdying
  rw [ambSub_ambSub] at hns
  have hi' : (i : ℕ) < c x := by
    have h : (i : ℕ) < ambSub c x [] := hi
    rwa [ambSub_apply, List.append_nil] at h
  have hxi : x ++ [i] ∈ sample c := BranchingProcess.mem_sample_append_singleton.mpr ⟨hxs, hi'⟩
  obtain ⟨w, hwlen, hw⟩ := hdeepdying
  have hz : x ++ [i] ++ w ∈ sample c := (mem_sample_ambSub_iff hxi).mp hw
  have hfin : {v : GWord N | v ∈ sample c ∧ x ++ [i] <+: v}.Finite := by
    have he : {v : GWord N | v ∈ sample c ∧ x ++ [i] <+: v}
        = (fun t ↦ x ++ [i] ++ t) '' (sample (ambSub c (x ++ [i])) : Set (GWord N)) := by
      ext v
      constructor
      · rintro ⟨hv, t, rfl⟩
        exact ⟨t, (mem_sample_ambSub_iff hxi).mpr hv, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨(mem_sample_ambSub_iff hxi).mp ht, List.prefix_append _ _⟩
    rw [he]
    exact (Set.not_infinite.mp hns).image _
  refine ⟨x, i, x ++ [i] ++ w, hxi, hfin, hz, List.prefix_append _ _, ?_⟩
  rw [BranchingProcess.treeDist_comm, BranchingProcess.treeDist_of_prefix
    ((List.prefix_append x [i]).trans (List.prefix_append _ _))]
  simp only [List.length_append, List.length_singleton, hwlen]
  omega

/-- **`thm:regime-obstructions-general` (`it:gen-obstr-hair`)**: at `θ₀ > 0`,
almost surely the sample has hairs of unbounded depth. -/
theorem unbounded_hairs_gSample_ae (hJN : J ≤ N) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (hJ2 : 2 ≤ J) (hθJ : 0 < θ J) :
    ∀ᵐ c ∂survivalMeasure (N := N) θ, UnboundedHairsN (fun w : GWord N ↦ w ∈ sample c) := by
  haveI := BranchingProcess.isProbabilityMeasure_survivalMeasure (N := N) θ hJN hq
  have hae : ∀ᵐ c ∂survivalMeasure (N := N) θ, ∀ n, ∃ k, neckIter c k ∈ hairEvent (N := N) J n := by
    refine ae_all_iff.mpr fun n ↦ ?_
    filter_upwards [ae_exists_iterate_mem (μ := survivalMeasure (N := N) θ)
      (Φ := fun d ↦ bushAt d 0) (D := hairEvent (N := N) J n)
      (BranchingProcess.measurable_bushAt 0)
      (fun A hA ↦ survivalMeasure_bushAt_zero_preimage θ hJN hq hA)
      (measurableSet_hairEvent n)
      (fun A hA ↦ survivalMeasure_hairEvent_inter θ hJN hq hq0 n hA)
      (hairMass_ne_zero θ hJN hq hq0 hJ2 hθJ n)] with c hc
    obtain ⟨k, hk⟩ := hc
    rw [iterate_bushAt_zero] at hk
    exact ⟨k, hk⟩
  filter_upwards [hae, ae_survives θ hJN hq] with c hdeep hsurv
  exact unboundedHairsN_sample hJN hJ2 hsurv hdeep

end Hairs


end ChainClasses
