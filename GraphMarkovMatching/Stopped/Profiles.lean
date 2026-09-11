/-
Binary profiles and their composites (`markov_matching_new_proof.tex`,
`sec:common-presentations`): full binary trees with marked graft roots.

* `MTree`: `leaf` is a fresh continuation, `node` a forced vertex, `gnode` a forced vertex
  that is the root of a grafted core profile;
* `leaves`, `height`, `leafDepths`, `minLeafDepth`, `subtrees`: the combinatorial data;
* `flatten` erases the grafts (a graft root becomes a fresh leaf), `erase` forgets the
  markers, `NoGraft` says no graft occurs;
* `AllComp S D t`: every graft root of `t` carries a core profile `D a`, `a ∈ S`, at its
  core block `node l.flatten r.flatten` (`sec:common-presentations`: a composite profile is
  a core profile with composite profiles at some of its leaves);
* `graftAt`, `graftShallowest`: replacing a leaf by a core profile, at a shallowest leaf;
* the height bounds `thm:shallow-grafting`, the optimal height recursion
  `eq:optimal-profile-height`, and the Kraft bound behind them.

The Markov model built from these profiles is in `Presentation.lean`.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace GraphMarkovMatching.Stopped

/-- Marked full binary trees: fresh leaves, forced vertices, and graft roots. -/
inductive MTree
  | leaf : MTree
  | node (l r : MTree) : MTree
  | gnode (l r : MTree) : MTree
  deriving DecidableEq, Repr

namespace MTree

/-- The number of leaves. -/
def leaves : MTree → ℕ
  | leaf => 1
  | node l r => l.leaves + r.leaves
  | gnode l r => l.leaves + r.leaves

/-- The height (a leaf has height `0`). -/
def height : MTree → ℕ
  | leaf => 0
  | node l r => max l.height r.height + 1
  | gnode l r => max l.height r.height + 1

/-- The leaf paths of a tree. -/
def leafPaths : MTree → Finset (List Bool)
  | leaf => {[]}
  | node l r => l.leafPaths.image (false :: ·) ∪ r.leafPaths.image (true :: ·)
  | gnode l r => l.leafPaths.image (false :: ·) ∪ r.leafPaths.image (true :: ·)

/-- The set of leaf depths. -/
def leafDepths : MTree → Finset ℕ
  | leaf => {0}
  | node l r => (l.leafDepths ∪ r.leafDepths).image (· + 1)
  | gnode l r => (l.leafDepths ∪ r.leafDepths).image (· + 1)

/-- The least leaf depth. -/
def minLeafDepth : MTree → ℕ
  | leaf => 0
  | node l r => min l.minLeafDepth r.minLeafDepth + 1
  | gnode l r => min l.minLeafDepth r.minLeafDepth + 1

/-- Erase the grafts: a graft root becomes a fresh leaf. -/
def flatten : MTree → MTree
  | leaf => leaf
  | node l r => node l.flatten r.flatten
  | gnode _ _ => leaf

/-- Forget the markers. -/
def erase : MTree → MTree
  | leaf => leaf
  | node l r => node l.erase r.erase
  | gnode l r => node l.erase r.erase

/-- No graft root occurs. -/
def NoGraft : MTree → Prop
  | leaf => True
  | node l r => NoGraft l ∧ NoGraft r
  | gnode _ _ => False

/-- The immediate graft roots (the grafted subtrees, not descending into them). -/
def grafts : MTree → List MTree
  | leaf => []
  | node l r => l.grafts ++ r.grafts
  | gnode l r => [gnode l r]

/-- All subtrees, including the tree itself. -/
def subtrees : MTree → Finset MTree
  | leaf => {leaf}
  | node l r => insert (node l r) (l.subtrees ∪ r.subtrees)
  | gnode l r => insert (gnode l r) (l.subtrees ∪ r.subtrees)

/-- `AllComp S D t`: every graft root of `t` (including `t` itself when it is a graft root)
carries a core profile `D a` with `a ∈ S` at its core block, and the same holds inside. -/
def AllComp (S : Finset ℕ) (D : ℕ → MTree) : MTree → Prop
  | leaf => True
  | node l r => AllComp S D l ∧ AllComp S D r
  | gnode l r => (∃ a ∈ S, node l.flatten r.flatten = D a) ∧ AllComp S D l ∧ AllComp S D r

/-- The core block of a graft root: `node l.flatten r.flatten`. -/
def coreBlock : MTree → MTree
  | gnode l r => node l.flatten r.flatten
  | t => t.flatten

/-- Replace the leaf at the given path (a list of directions, `true` = right) by `g`,
marked as a graft root; paths not ending at a leaf leave the tree unchanged. -/
def graftAt (g : MTree) : List Bool → MTree → MTree
  | [], leaf => g
  | _ :: _, leaf => leaf
  | [], t => t
  | false :: p, node l r => node (graftAt g p l) r
  | true :: p, node l r => node l (graftAt g p r)
  | false :: p, gnode l r => gnode (graftAt g p l) r
  | true :: p, gnode l r => gnode l (graftAt g p r)

/-- The path to a shallowest leaf (leftmost among the shallowest). -/
def shallowestPath : MTree → List Bool
  | leaf => []
  | node l r => if l.minLeafDepth ≤ r.minLeafDepth then false :: shallowestPath l
      else true :: shallowestPath r
  | gnode l r => if l.minLeafDepth ≤ r.minLeafDepth then false :: shallowestPath l
      else true :: shallowestPath r

/-- Graft `g` at a shallowest leaf. -/
def graftShallowest (g : MTree) (t : MTree) : MTree := graftAt g (shallowestPath t) t

/-- Mark a core profile as a graft root: `node l r ↦ gnode l r`. -/
def markRoot : MTree → MTree
  | node l r => gnode l r
  | t => t

/-- The composite profile of an expression `a_1 + ⋯ + a_n`: start from a single leaf,
successively graft the marked core profiles `D a_i` at a shallowest current leaf
(`sec:common-generators`). -/
def composite (D : ℕ → MTree) : List ℕ → MTree
  | [] => leaf
  | a :: as => graftShallowest (markRoot (D a)) (composite D as)

/-! ### Basic facts -/

lemma leaves_pos (t : MTree) : 0 < t.leaves := by
  induction t with
  | leaf => simp [leaves]
  | node l r ihl ihr => simp only [leaves]; omega
  | gnode l r ihl ihr => simp only [leaves]; omega

lemma leaves_flatten_le (t : MTree) : t.flatten.leaves ≤ t.leaves := by
  induction t with
  | leaf => simp [flatten]
  | node l r ihl ihr => simp only [flatten, leaves]; omega
  | gnode l r _ _ =>
    have := leaves_pos l
    have := leaves_pos r
    simp only [flatten, leaves]; omega

lemma flatten_noGraft (t : MTree) : t.flatten.NoGraft := by
  induction t with
  | leaf => simp [flatten, NoGraft]
  | node l r ihl ihr => exact ⟨ihl, ihr⟩
  | gnode l r _ _ => simp [flatten, NoGraft]

lemma flatten_eq_self_of_noGraft {t : MTree} (h : t.NoGraft) : t.flatten = t := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr => simp only [flatten]; rw [ihl h.1, ihr h.2]
  | gnode l r _ _ => exact absurd h id

lemma height_flatten_le (t : MTree) : t.flatten.height ≤ t.height := by
  induction t with
  | leaf => simp [flatten]
  | node l r ihl ihr => simp only [flatten, height]; omega
  | gnode l r _ _ => simp [flatten, height]

lemma minLeafDepth_le_height (t : MTree) : t.minLeafDepth ≤ t.height := by
  induction t with
  | leaf => simp [minLeafDepth, height]
  | node l r ihl ihr => simp only [minLeafDepth, height]; omega
  | gnode l r ihl ihr => simp only [minLeafDepth, height]; omega

lemma minLeafDepth_mem_leafDepths (t : MTree) : t.minLeafDepth ∈ t.leafDepths := by
  induction t with
  | leaf => simp [minLeafDepth, leafDepths]
  | node l r ihl ihr =>
    simp only [minLeafDepth, leafDepths, Finset.mem_image, Finset.mem_union]
    rcases le_total l.minLeafDepth r.minLeafDepth with h | h
    · exact ⟨l.minLeafDepth, Or.inl ihl, by rw [min_eq_left h]⟩
    · exact ⟨r.minLeafDepth, Or.inr ihr, by rw [min_eq_right h]⟩
  | gnode l r ihl ihr =>
    simp only [minLeafDepth, leafDepths, Finset.mem_image, Finset.mem_union]
    rcases le_total l.minLeafDepth r.minLeafDepth with h | h
    · exact ⟨l.minLeafDepth, Or.inl ihl, by rw [min_eq_left h]⟩
    · exact ⟨r.minLeafDepth, Or.inr ihr, by rw [min_eq_right h]⟩

lemma le_of_mem_leafDepths {t : MTree} {d : ℕ} (hd : d ∈ t.leafDepths) : d ≤ t.height := by
  induction t generalizing d with
  | leaf => simp [leafDepths] at hd; omega
  | node l r ihl ihr =>
    simp only [leafDepths, Finset.mem_image, Finset.mem_union] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    simp only [height]
    rcases hd' with h | h
    · have := ihl h; omega
    · have := ihr h; omega
  | gnode l r ihl ihr =>
    simp only [leafDepths, Finset.mem_image, Finset.mem_union] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    simp only [height]
    rcases hd' with h | h
    · have := ihl h; omega
    · have := ihr h; omega

lemma minLeafDepth_le_of_mem {t : MTree} {d : ℕ} (hd : d ∈ t.leafDepths) :
    t.minLeafDepth ≤ d := by
  induction t generalizing d with
  | leaf => simp [minLeafDepth]
  | node l r ihl ihr =>
    simp only [leafDepths, Finset.mem_image, Finset.mem_union] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    simp only [minLeafDepth]
    rcases hd' with h | h
    · have := ihl h; omega
    · have := ihr h; omega
  | gnode l r ihl ihr =>
    simp only [leafDepths, Finset.mem_image, Finset.mem_union] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    simp only [minLeafDepth]
    rcases hd' with h | h
    · have := ihl h; omega
    · have := ihr h; omega

lemma mem_subtrees_self (t : MTree) : t ∈ t.subtrees := by
  cases t <;> simp [subtrees]

lemma subtrees_node_left (l r : MTree) : l ∈ (node l r).subtrees := by
  simp [subtrees, mem_subtrees_self]

lemma subtrees_node_right (l r : MTree) : r ∈ (node l r).subtrees := by
  simp [subtrees, mem_subtrees_self]

lemma subtrees_gnode_left (l r : MTree) : l ∈ (gnode l r).subtrees := by
  simp [subtrees, mem_subtrees_self]

lemma subtrees_gnode_right (l r : MTree) : r ∈ (gnode l r).subtrees := by
  simp [subtrees, mem_subtrees_self]

lemma subtrees_trans {a b c : MTree} (hab : a ∈ b.subtrees) (hbc : b ∈ c.subtrees) :
    a ∈ c.subtrees := by
  induction c with
  | leaf =>
    simp only [subtrees, Finset.mem_singleton] at hbc
    subst hbc; exact hab
  | node l r ihl ihr =>
    simp only [subtrees, Finset.mem_insert, Finset.mem_union] at hbc
    rcases hbc with rfl | h | h
    · exact hab
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (ihl h))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ihr h))
  | gnode l r ihl ihr =>
    simp only [subtrees, Finset.mem_insert, Finset.mem_union] at hbc
    rcases hbc with rfl | h | h
    · exact hab
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (ihl h))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ihr h))

lemma height_le_of_mem_subtrees {a b : MTree} (h : a ∈ b.subtrees) : a.height ≤ b.height := by
  induction b with
  | leaf =>
    simp only [subtrees, Finset.mem_singleton] at h
    subst h; exact le_rfl
  | node l r ihl ihr =>
    simp only [subtrees, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact le_rfl
    · have := ihl h; simp only [height]; omega
    · have := ihr h; simp only [height]; omega
  | gnode l r ihl ihr =>
    simp only [subtrees, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact le_rfl
    · have := ihl h; simp only [height]; omega
    · have := ihr h; simp only [height]; omega

lemma allComp_of_mem_subtrees {S : Finset ℕ} {D : ℕ → MTree} {a b : MTree}
    (hb : AllComp S D b) (h : a ∈ b.subtrees) : AllComp S D a := by
  induction b with
  | leaf =>
    simp only [subtrees, Finset.mem_singleton] at h
    subst h; exact hb
  | node l r ihl ihr =>
    simp only [subtrees, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact hb
    · exact ihl hb.1 h
    · exact ihr hb.2 h
  | gnode l r ihl ihr =>
    simp only [subtrees, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact hb
    · exact ihl hb.2.1 h
    · exact ihr hb.2.2 h

/-- The Kraft inequality in integer form: `2 ^ minLeafDepth ≤ leaves`
(`thm:shallow-grafting`). -/
lemma two_pow_minLeafDepth_le (t : MTree) : 2 ^ t.minLeafDepth ≤ t.leaves := by
  induction t with
  | leaf => simp [minLeafDepth, leaves]
  | node l r ihl ihr =>
    simp only [minLeafDepth, leaves, pow_succ]
    have h1 : 2 ^ min l.minLeafDepth r.minLeafDepth ≤ 2 ^ l.minLeafDepth :=
      Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
    have h2 : 2 ^ min l.minLeafDepth r.minLeafDepth ≤ 2 ^ r.minLeafDepth :=
      Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)
    omega
  | gnode l r ihl ihr =>
    simp only [minLeafDepth, leaves, pow_succ]
    have h1 : 2 ^ min l.minLeafDepth r.minLeafDepth ≤ 2 ^ l.minLeafDepth :=
      Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
    have h2 : 2 ^ min l.minLeafDepth r.minLeafDepth ≤ 2 ^ r.minLeafDepth :=
      Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)
    omega

/-- **The Kraft bound**: a full binary tree with `n` leaves has a leaf of depth at most
`⌊log₂ n⌋` (`thm:shallow-grafting`: `∑_u 2^{-|u|} = 1` over the leaves). -/
lemma minLeafDepth_le_log (t : MTree) : t.minLeafDepth ≤ Nat.log 2 t.leaves :=
  Nat.le_log_of_pow_le (by norm_num) (two_pow_minLeafDepth_le t)

/-- A binary tree of height `h` has at most `2^h` leaves, so the height is at least
`⌈log₂ k⌉`. -/
lemma leaves_le_two_pow_height (t : MTree) : t.leaves ≤ 2 ^ t.height := by
  induction t with
  | leaf => simp [leaves, height]
  | node l r ihl ihr =>
    simp only [leaves, height, pow_succ]
    have h1 : 2 ^ l.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2 : 2 ^ r.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    omega
  | gnode l r ihl ihr =>
    simp only [leaves, height, pow_succ]
    have h1 : 2 ^ l.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2 : 2 ^ r.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    omega

lemma clog_leaves_le_height (t : MTree) : Nat.clog 2 t.leaves ≤ t.height :=
  Nat.clog_le_of_le_pow (leaves_le_two_pow_height t)

/-! ### Grafting -/

lemma leaves_graftAt_of_leaf (g t : MTree) (p : List Bool) (hp : p ∈ t.leafPaths) :
    (graftAt g p t).leaves = t.leaves + g.leaves - 1 := by
  have hg := leaves_pos g
  induction t generalizing p with
  | leaf =>
    simp only [leafPaths, Finset.mem_singleton] at hp
    subst hp
    simp only [graftAt, leaves]; omega
  | node l r ihl ihr =>
    simp only [leafPaths, Finset.mem_union, Finset.mem_image] at hp
    have hl := leaves_pos l
    have hr := leaves_pos r
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have := ihl q hq
      simp only [graftAt, leaves]; omega
    · have := ihr q hq
      simp only [graftAt, leaves]; omega
  | gnode l r ihl ihr =>
    simp only [leafPaths, Finset.mem_union, Finset.mem_image] at hp
    have hl := leaves_pos l
    have hr := leaves_pos r
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have := ihl q hq
      simp only [graftAt, leaves]; omega
    · have := ihr q hq
      simp only [graftAt, leaves]; omega

lemma shallowestPath_mem (t : MTree) : t.shallowestPath ∈ t.leafPaths := by
  induction t with
  | leaf => simp [shallowestPath, leafPaths]
  | node l r ihl ihr =>
    simp only [shallowestPath, leafPaths]
    split_ifs
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ ihl)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ ihr)
  | gnode l r ihl ihr =>
    simp only [shallowestPath, leafPaths]
    split_ifs
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ ihl)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ ihr)

lemma length_shallowestPath (t : MTree) : t.shallowestPath.length = t.minLeafDepth := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
    simp only [shallowestPath, minLeafDepth]
    split_ifs with h
    · rw [List.length_cons, ihl]; omega
    · rw [List.length_cons, ihr]; omega
  | gnode l r ihl ihr =>
    simp only [shallowestPath, minLeafDepth]
    split_ifs with h
    · rw [List.length_cons, ihl]; omega
    · rw [List.length_cons, ihr]; omega

/-- Grafting at a shallowest leaf adds `g.leaves - 1` leaves. -/
lemma leaves_graftShallowest (g t : MTree) :
    (graftShallowest g t).leaves = t.leaves + g.leaves - 1 :=
  leaves_graftAt_of_leaf g t _ (shallowestPath_mem t)

/-- The height after grafting at a leaf of depth `|p|` is at most
`max (t.height) (|p| + g.height)` (`thm:shallow-grafting`: the new leaves have depth at most
`g.height` larger than the chosen leaf). -/
lemma height_graftAt_le (g t : MTree) (p : List Bool) (hp : p ∈ t.leafPaths) :
    (graftAt g p t).height ≤ max t.height (p.length + g.height) := by
  induction t generalizing p with
  | leaf =>
    simp only [leafPaths, Finset.mem_singleton] at hp
    subst hp
    simp [graftAt, height]
  | node l r ihl ihr =>
    simp only [leafPaths, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have := ihl q hq
      simp only [graftAt, height, List.length_cons]; omega
    · have := ihr q hq
      simp only [graftAt, height, List.length_cons]; omega
  | gnode l r ihl ihr =>
    simp only [leafPaths, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have := ihl q hq
      simp only [graftAt, height, List.length_cons]; omega
    · have := ihr q hq
      simp only [graftAt, height, List.length_cons]; omega

/-- The height after grafting at a shallowest leaf is at most
`max (t.height) (t.minLeafDepth + g.height)`. -/
lemma height_graftShallowest_le (g t : MTree) :
    (graftShallowest g t).height ≤ max t.height (t.minLeafDepth + g.height) := by
  have := height_graftAt_le g t _ (shallowestPath_mem t)
  rwa [length_shallowestPath] at this

lemma leaves_markRoot (t : MTree) : (markRoot t).leaves = t.leaves := by
  cases t <;> rfl

lemma height_markRoot (t : MTree) : (markRoot t).height = t.height := by
  cases t <;> rfl

/-- The composite of an expression has `1 + ∑ a_i` leaves when every `D a_i` has `a_i + 1`
leaves. -/
lemma leaves_composite (D : ℕ → MTree) (as : List ℕ) (hD : ∀ a ∈ as, (D a).leaves = a + 1) :
    (composite D as).leaves = 1 + as.sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ih' := ih (fun b hb => hD b (by simp [hb]))
    simp only [composite, List.sum_cons]
    rw [leaves_graftShallowest, ih', leaves_markRoot, hD a (by simp)]
    omega

/-- **`thm:shallow-grafting`**: if every `D a` has height at most `L` and the expression has
summands at least `s₀ ≥ 1`, the composite of `k - 1 = ∑ a_i` has height at most
`L + ⌊log₂(k - s₀)⌋`. -/
theorem height_composite_le (D : ℕ → MTree) (as : List ℕ) (L s₀ : ℕ) (hs₀ : 1 ≤ s₀)
    (hne : as ≠ []) (hD : ∀ a ∈ as, (D a).leaves = a + 1) (hL : ∀ a ∈ as, (D a).height ≤ L)
    (hs : ∀ a ∈ as, s₀ ≤ a) :
    (composite D as).height ≤ L + Nat.log 2 (1 + as.sum - s₀) := by
  have key : ∀ bs : List ℕ, (∀ a ∈ bs, (D a).leaves = a + 1) → (∀ a ∈ bs, (D a).height ≤ L) →
      (∀ a ∈ bs, s₀ ≤ a) → (composite D bs).height ≤ L + Nat.log 2 (1 + bs.sum - s₀) := by
    intro bs
    induction bs with
    | nil => intros; simp [composite, height]
    | cons a bs ih =>
      intro hD hL hs
      have ih' := ih (fun b hb => hD b (by simp [hb])) (fun b hb => hL b (by simp [hb]))
        (fun b hb => hs b (by simp [hb]))
      have ha := hs a (by simp)
      have hLa := hL a (by simp)
      simp only [composite, List.sum_cons]
      refine (height_graftShallowest_le _ _).trans ?_
      have h1 := minLeafDepth_le_log (composite D bs)
      rw [leaves_composite D bs (fun b hb => hD b (by simp [hb]))] at h1
      rw [height_markRoot]
      have hmono1 : Nat.log 2 (1 + bs.sum - s₀) ≤ Nat.log 2 (1 + (a + bs.sum) - s₀) :=
        Nat.log_mono_right (by omega)
      have hmono2 : Nat.log 2 (1 + bs.sum) ≤ Nat.log 2 (1 + (a + bs.sum) - s₀) :=
        Nat.log_mono_right (by omega)
      omega
  cases as with
  | nil => exact absurd rfl hne
  | cons a as => exact key (a :: as) hD hL hs

/-- A graft-free tree satisfies `AllComp` vacuously. -/
lemma allComp_of_noGraft {S : Finset ℕ} {D : ℕ → MTree} {t : MTree} (h : t.NoGraft) :
    AllComp S D t := by
  induction t with
  | leaf => trivial
  | node l r ihl ihr => exact ⟨ihl h.1, ihr h.2⟩
  | gnode l r _ _ => exact absurd h id

/-- A marked tree flattens to a leaf. -/
lemma flatten_markRoot (t : MTree) : (markRoot t).flatten = leaf := by
  cases t <;> rfl

/-- Grafting a tree that flattens to a leaf does not change the flattening
(`sec:common-presentations`: the core block of a graft root is unchanged by further grafts). -/
lemma flatten_graftAt {g : MTree} (hg : g.flatten = leaf) (p : List Bool) (t : MTree) :
    (graftAt g p t).flatten = t.flatten := by
  induction t generalizing p with
  | leaf =>
    cases p with
    | nil => simpa [graftAt, flatten] using hg
    | cons b p => simp [graftAt]
  | node l r ihl ihr =>
    cases p with
    | nil => simp [graftAt]
    | cons b p => cases b <;> simp [graftAt, flatten, ihl, ihr]
  | gnode l r _ _ =>
    cases p with
    | nil => simp [graftAt]
    | cons b p => cases b <;> simp [graftAt, flatten]

/-- Grafting a composite graft root at any path preserves `AllComp`. -/
lemma allComp_graftAt {S : Finset ℕ} {D : ℕ → MTree} {g : MTree} (hg : AllComp S D g)
    (hg' : g.flatten = leaf) (p : List Bool) {t : MTree} (ht : AllComp S D t) :
    AllComp S D (graftAt g p t) := by
  induction t generalizing p with
  | leaf =>
    cases p with
    | nil => simpa [graftAt] using hg
    | cons b p => simp [graftAt, AllComp]
  | node l r ihl ihr =>
    cases p with
    | nil => simpa [graftAt] using ht
    | cons b p =>
      cases b
      · simp only [graftAt, AllComp]
        exact ⟨ihl p ht.1, ht.2⟩
      · simp only [graftAt, AllComp]
        exact ⟨ht.1, ihr p ht.2⟩
  | gnode l r ihl ihr =>
    cases p with
    | nil => simpa [graftAt] using ht
    | cons b p =>
      cases b
      · simp only [graftAt, AllComp]
        refine ⟨?_, ihl p ht.2.1, ht.2.2⟩
        rw [flatten_graftAt hg']; exact ht.1
      · simp only [graftAt, AllComp]
        refine ⟨?_, ht.2.1, ihr p ht.2.2⟩
        rw [flatten_graftAt hg']; exact ht.1

/-- The composite of an expression over core arities is a composite profile: every graft
root carries a core profile, provided each `D a` is a graft-free `node`. -/
theorem allComp_composite (S : Finset ℕ) (D : ℕ → MTree) (as : List ℕ)
    (hD : ∀ a ∈ as, (D a).NoGraft ∧ ∃ l r, D a = node l r) (hS : ∀ a ∈ as, a ∈ S) :
    AllComp S D (composite D as) := by
  induction as with
  | nil => trivial
  | cons a as ih =>
    have ih' := ih (fun b hb => hD b (by simp [hb])) (fun b hb => hS b (by simp [hb]))
    obtain ⟨hng, l, r, hDa⟩ := hD a (by simp)
    have haS := hS a (by simp)
    simp only [composite, graftShallowest]
    refine allComp_graftAt ?_ (flatten_markRoot _) _ ih'
    rw [hDa] at hng ⊢
    simp only [markRoot, AllComp]
    refine ⟨⟨a, haS, ?_⟩, allComp_of_noGraft hng.1, allComp_of_noGraft hng.2⟩
    rw [flatten_eq_self_of_noGraft hng.1, flatten_eq_self_of_noGraft hng.2, hDa]

/-- Grafting into a graft root keeps a graft root. -/
lemma graftAt_gnode (g l r : MTree) (p : List Bool) :
    ∃ l' r', graftAt g p (gnode l r) = gnode l' r' := by
  cases p with
  | nil => exact ⟨l, r, by simp [graftAt]⟩
  | cons b p => cases b <;> exact ⟨_, _, rfl⟩

/-- A nonempty composite is a graft root. -/
theorem composite_cons (D : ℕ → MTree) (a : ℕ) (as : List ℕ)
    (hD : ∀ b ∈ a :: as, ∃ l r, D b = node l r) :
    ∃ l r, composite D (a :: as) = gnode l r := by
  induction as generalizing a with
  | nil =>
    obtain ⟨l, r, h⟩ := hD a (by simp)
    exact ⟨l, r, by simp [composite, graftShallowest, shallowestPath, graftAt, h, markRoot]⟩
  | cons b bs ih =>
    obtain ⟨l, r, h⟩ := ih b (fun c hc => hD c (by simp at hc ⊢; tauto))
    have e : composite D (a :: b :: bs) = graftShallowest (markRoot (D a)) (gnode l r) := by
      rw [← h]; rfl
    rw [e, graftShallowest]
    exact graftAt_gnode _ _ _ _

/-- The one-term composite is the marked core profile. -/
lemma composite_singleton (D : ℕ → MTree) (a : ℕ) : composite D [a] = markRoot (D a) := by
  simp [composite, graftShallowest, shallowestPath, graftAt]

/-! ### The optimal height recursion (`eq:optimal-profile-height`) -/

/-- Graft, at every leaf of `t` reached by the path `p`, the tree `f p` (marked as a graft
root when it is not a leaf). -/
def graftLeaves (f : List Bool → MTree) : List Bool → MTree → MTree
  | p, leaf => markRoot (f p)
  | p, node l r => node (graftLeaves f (p ++ [false]) l) (graftLeaves f (p ++ [true]) r)
  | p, gnode l r => gnode (graftLeaves f (p ++ [false]) l) (graftLeaves f (p ++ [true]) r)

/-- A composite profile: a graft root whose grafts all carry core profiles, or a single
leaf (`sec:common-presentations`, the case `s_i = 0`). -/
def IsCompositeProfile (S : Finset ℕ) (D : ℕ → MTree) (t : MTree) : Prop :=
  AllComp S D t ∧ ((∃ l r, t = gnode l r) ∨ t = leaf)

/-- The least height of a composite profile with `s + 1` leaves (`h(s)` of
`eq:optimal-profile-height`), as an infimum over the (finite) set of realisable heights. -/
noncomputable def optHeight (S : Finset ℕ) (D : ℕ → MTree) (s : ℕ) : ℕ :=
  sInf {h | ∃ t, IsCompositeProfile S D t ∧ t.leaves = s + 1 ∧ t.height = h}

/-- The two halves of the leaf paths of a node are disjoint. -/
private lemma disjoint_leafPaths_images (l r : Finset (List Bool)) :
    Disjoint (l.image (false :: ·)) (r.image (true :: ·)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_image] at hx hx'
  obtain ⟨q, _, rfl⟩ := hx
  obtain ⟨q', _, h⟩ := hx'
  simp at h

/-- A tree has as many leaf paths as leaves. -/
lemma card_leafPaths (t : MTree) : t.leafPaths.card = t.leaves := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
    simp only [leafPaths, leaves]
    rw [Finset.card_union_of_disjoint (disjoint_leafPaths_images _ _),
      Finset.card_image_of_injective _ List.cons_injective,
      Finset.card_image_of_injective _ List.cons_injective, ihl, ihr]
  | gnode l r ihl ihr =>
    simp only [leafPaths, leaves]
    rw [Finset.card_union_of_disjoint (disjoint_leafPaths_images _ _),
      Finset.card_image_of_injective _ List.cons_injective,
      Finset.card_image_of_injective _ List.cons_injective, ihl, ihr]

/-- Every tree has a leaf path. -/
lemma leafPaths_nonempty (t : MTree) : t.leafPaths.Nonempty :=
  Finset.card_pos.1 (by rw [card_leafPaths]; exact leaves_pos t)

/-- A constant shift commutes with the supremum over a nonempty finset. -/
private lemma sup_add_const {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (g : ι → ℕ) (c : ℕ) :
    (s.sup fun q => g q + c) = s.sup g + c := by
  apply le_antisymm
  · exact Finset.sup_le fun q hq => Nat.add_le_add_right (Finset.le_sup (f := g) hq) c
  · obtain ⟨q₀, hq₀, hsup⟩ := Finset.exists_mem_eq_sup s hs g
    rw [hsup]
    exact Finset.le_sup (f := fun q => g q + c) hq₀

/-- The height of a leaf-grafted tree is the largest `|p| + height (f p)` over the leaf
paths. -/
lemma height_graftLeaves (f : List Bool → MTree) (p : List Bool) (t : MTree) :
    (graftLeaves f p t).height
      = (t.leafPaths.sup fun q => q.length + (f (p ++ q)).height) := by
  induction t generalizing p with
  | leaf => simp [graftLeaves, leafPaths, height_markRoot]
  | node l r ihl ihr =>
    simp only [graftLeaves, height, leafPaths, Finset.sup_union, Finset.sup_image, ihl, ihr,
      Function.comp_def, List.length_cons, List.append_assoc, List.singleton_append]
    have e1 : (l.leafPaths.sup fun q => q.length + 1 + (f (p ++ false :: q)).height)
        = (l.leafPaths.sup fun q => q.length + (f (p ++ false :: q)).height) + 1 := by
      rw [← sup_add_const _ (leafPaths_nonempty l)]
      congr 1; funext q; omega
    have e2 : (r.leafPaths.sup fun q => q.length + 1 + (f (p ++ true :: q)).height)
        = (r.leafPaths.sup fun q => q.length + (f (p ++ true :: q)).height) + 1 := by
      rw [← sup_add_const _ (leafPaths_nonempty r)]
      congr 1; funext q; omega
    rw [e1, e2]; omega
  | gnode l r ihl ihr =>
    simp only [graftLeaves, height, leafPaths, Finset.sup_union, Finset.sup_image, ihl, ihr,
      Function.comp_def, List.length_cons, List.append_assoc, List.singleton_append]
    have e1 : (l.leafPaths.sup fun q => q.length + 1 + (f (p ++ false :: q)).height)
        = (l.leafPaths.sup fun q => q.length + (f (p ++ false :: q)).height) + 1 := by
      rw [← sup_add_const _ (leafPaths_nonempty l)]
      congr 1; funext q; omega
    have e2 : (r.leafPaths.sup fun q => q.length + 1 + (f (p ++ true :: q)).height)
        = (r.leafPaths.sup fun q => q.length + (f (p ++ true :: q)).height) + 1 := by
      rw [← sup_add_const _ (leafPaths_nonempty r)]
      congr 1; funext q; omega
    rw [e1, e2]; omega

/-- The leaf count of a leaf-grafted tree is the sum of the leaf counts of the grafts. -/
lemma leaves_graftLeaves (f : List Bool → MTree) (p : List Bool) (t : MTree) :
    (graftLeaves f p t).leaves = t.leafPaths.sum fun q => (f (p ++ q)).leaves := by
  induction t generalizing p with
  | leaf => simp [graftLeaves, leafPaths, leaves_markRoot]
  | node l r ihl ihr =>
    simp only [graftLeaves, leaves, leafPaths, ihl, ihr]
    rw [Finset.sum_union (disjoint_leafPaths_images _ _),
      Finset.sum_image (fun _ _ _ _ h => List.cons_injective h),
      Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
    simp [List.append_assoc]
  | gnode l r ihl ihr =>
    simp only [graftLeaves, leaves, leafPaths, ihl, ihr]
    rw [Finset.sum_union (disjoint_leafPaths_images _ _),
      Finset.sum_image (fun _ _ _ _ h => List.cons_injective h),
      Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
    simp [List.append_assoc]

/-- The subtree at a path (`leaf` when the path leaves the tree). -/
def subtreeAt : List Bool → MTree → MTree
  | [], t => t
  | _ :: _, leaf => leaf
  | false :: p, node l _ => subtreeAt p l
  | true :: p, node _ r => subtreeAt p r
  | false :: p, gnode l _ => subtreeAt p l
  | true :: p, gnode _ r => subtreeAt p r

/-- Every subtree of a leaf is the leaf. -/
lemma subtreeAt_leaf (p : List Bool) : subtreeAt p leaf = leaf := by
  cases p <;> rfl

/-- Following a concatenated path follows the two paths in turn. -/
lemma subtreeAt_append (p q : List Bool) (t : MTree) :
    subtreeAt (p ++ q) t = subtreeAt q (subtreeAt p t) := by
  induction p generalizing t with
  | nil => rfl
  | cons b p ih =>
    cases t with
    | leaf => simp [subtreeAt, subtreeAt_leaf]
    | node l r => cases b <;> simp [subtreeAt, ih]
    | gnode l r => cases b <;> simp [subtreeAt, ih]

/-- A composite profile is unchanged by marking (it is a graft root or a leaf). -/
lemma markRoot_eq_self_of_isCompositeProfile {S : Finset ℕ} {D : ℕ → MTree} {t : MTree}
    (h : IsCompositeProfile S D t) : markRoot t = t := by
  rcases h.2 with ⟨l, r, rfl⟩ | rfl <;> rfl

/-- Regrafting the subtrees of `t` at the leaves of a flattened subtree recovers it. -/
lemma graftLeaves_subtreeAt (t : MTree) : ∀ (u : MTree) (p : List Bool), subtreeAt p t = u →
    graftLeaves (fun q => subtreeAt q t) p u.flatten = u := by
  intro u
  induction u with
  | leaf => intro p hp; simp [flatten, graftLeaves, hp, markRoot]
  | node l r ihl ihr =>
    intro p hp
    simp only [flatten, graftLeaves]
    rw [ihl _ (by rw [subtreeAt_append, hp]; rfl), ihr _ (by rw [subtreeAt_append, hp]; rfl)]
  | gnode l r _ _ => intro p hp; simp [flatten, graftLeaves, hp, markRoot]

/-- The subtree at a leaf path of the flattening is a composite profile. -/
lemma isCompositeProfile_subtreeAt {S : Finset ℕ} {D : ℕ → MTree} : ∀ (u : MTree),
    AllComp S D u → ∀ q ∈ u.flatten.leafPaths, IsCompositeProfile S D (subtreeAt q u) := by
  intro u
  induction u with
  | leaf =>
    intro _ q hq
    simp only [flatten, leafPaths, Finset.mem_singleton] at hq
    subst hq
    exact ⟨trivial, Or.inr rfl⟩
  | node l r ihl ihr =>
    intro hu q hq
    simp only [flatten, leafPaths, Finset.mem_union, Finset.mem_image] at hq
    rcases hq with ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
    · exact ihl hu.1 q' hq'
    · exact ihr hu.2 q' hq'
  | gnode l r _ _ =>
    intro hu q hq
    simp only [flatten, leafPaths, Finset.mem_singleton] at hq
    subst hq
    exact ⟨hu, Or.inl ⟨l, r, rfl⟩⟩

/-- Leaf-grafting a graft-free tree flattens back to the tree. -/
lemma flatten_graftLeaves (f : List Bool → MTree) (p : List Bool) {u : MTree}
    (hu : u.NoGraft) : (graftLeaves f p u).flatten = u := by
  induction u generalizing p with
  | leaf => simp [graftLeaves, flatten_markRoot]
  | node l r ihl ihr => simp [graftLeaves, flatten, ihl _ hu.1, ihr _ hu.2]
  | gnode l r _ _ => exact absurd hu id

/-- Leaf-grafting composite profiles onto a graft-free tree satisfies `AllComp`. -/
lemma allComp_graftLeaves {S : Finset ℕ} {D : ℕ → MTree} (f : List Bool → MTree)
    (p : List Bool) {u : MTree} (hu : u.NoGraft)
    (hf : ∀ q ∈ u.leafPaths, IsCompositeProfile S D (f (p ++ q))) :
    AllComp S D (graftLeaves f p u) := by
  induction u generalizing p with
  | leaf =>
    have := hf [] (by simp [leafPaths])
    rw [List.append_nil] at this
    simp only [graftLeaves]
    rw [markRoot_eq_self_of_isCompositeProfile this]
    exact this.1
  | node l r ihl ihr =>
    refine ⟨ihl _ hu.1 (fun q hq => ?_), ihr _ hu.2 (fun q hq => ?_)⟩
    · have := hf (false :: q) (by simp [leafPaths, hq])
      simpa [List.append_assoc] using this
    · have := hf (true :: q) (by simp [leafPaths, hq])
      simpa [List.append_assoc] using this
  | gnode l r _ _ => exact absurd hu id

/-- **The structure of composite profiles**: every composite profile other than a leaf is a
core profile `D a` with a composite profile (possibly a leaf) grafted at each of its leaves,
and conversely. -/
theorem isCompositeProfile_iff (S : Finset ℕ) (D : ℕ → MTree)
    (hD : ∀ a ∈ S, (D a).NoGraft ∧ ∃ l r, D a = node l r) (t : MTree) (ht : t ≠ leaf) :
    IsCompositeProfile S D t
      ↔ ∃ a ∈ S, ∃ f : List Bool → MTree, (∀ q ∈ (D a).leafPaths, IsCompositeProfile S D (f q))
          ∧ t = markRoot (graftLeaves f [] (D a)) := by
  constructor
  · rintro ⟨hall, hshape⟩
    rcases hshape with ⟨l, r, rfl⟩ | rfl
    · obtain ⟨⟨a, haS, hDa⟩, hl, hr⟩ := hall
      refine ⟨a, haS, fun q => subtreeAt q (gnode l r), ?_, ?_⟩
      · intro q hq
        rw [← hDa] at hq
        simp only [leafPaths, Finset.mem_union, Finset.mem_image] at hq
        rcases hq with ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
        · exact isCompositeProfile_subtreeAt l hl q' hq'
        · exact isCompositeProfile_subtreeAt r hr q' hq'
      · rw [← hDa]
        simp only [graftLeaves, List.nil_append]
        rw [graftLeaves_subtreeAt (gnode l r) l [false] rfl,
          graftLeaves_subtreeAt (gnode l r) r [true] rfl]
        rfl
    · exact absurd rfl ht
  · rintro ⟨a, haS, f, hf, rfl⟩
    obtain ⟨hng, l, r, hDa⟩ := hD a haS
    rw [hDa] at hng hf ⊢
    simp only [graftLeaves, List.nil_append, markRoot]
    refine ⟨?_, Or.inl ⟨_, _, rfl⟩⟩
    refine ⟨⟨a, haS, ?_⟩, allComp_graftLeaves f _ hng.1 (fun q hq => ?_),
      allComp_graftLeaves f _ hng.2 (fun q hq => ?_)⟩
    · rw [flatten_graftLeaves _ _ hng.1, flatten_graftLeaves _ _ hng.2, hDa]
    · exact hf (false :: q) (by simp [leafPaths, hq])
    · exact hf (true :: q) (by simp [leafPaths, hq])

/-- **`eq:optimal-profile-height`**: the least height `h(s)` of a composite profile with
`s + 1` leaves is the minimum over the root core profile `D a` and the sizes `s_q` at its
leaves with `a + ∑ s_q = s` of `max_q (|q| + h(s_q))`; `h(0) = 0`. -/
theorem optHeight_eq (S : Finset ℕ) (D : ℕ → MTree)
    (hD : ∀ a ∈ S, (D a).NoGraft ∧ (D a).leaves = a + 1 ∧ ∃ l r, D a = node l r)
    (s : ℕ) (hs : 0 < s)
    (hex : ∃ t, IsCompositeProfile S D t ∧ t.leaves = s + 1) :
    optHeight S D s
      = sInf {h | ∃ a ∈ S, ∃ σ : List Bool → ℕ,
          (a + (D a).leafPaths.sum σ = s) ∧ (∀ q ∈ (D a).leafPaths,
            ∃ t, IsCompositeProfile S D t ∧ t.leaves = σ q + 1)
          ∧ h = (D a).leafPaths.sup fun q => q.length + optHeight S D (σ q)} := by
  classical
  have hD' : ∀ a ∈ S, (D a).NoGraft ∧ ∃ l r, D a = node l r :=
    fun a ha => ⟨(hD a ha).1, (hD a ha).2.2⟩
  -- every element of the recursion set is the height of a composite profile
  have hBA : ∀ h ∈ {h | ∃ a ∈ S, ∃ σ : List Bool → ℕ,
          (a + (D a).leafPaths.sum σ = s) ∧ (∀ q ∈ (D a).leafPaths,
            ∃ t, IsCompositeProfile S D t ∧ t.leaves = σ q + 1)
          ∧ h = (D a).leafPaths.sup fun q => q.length + optHeight S D (σ q)},
      h ∈ {h | ∃ t, IsCompositeProfile S D t ∧ t.leaves = s + 1 ∧ t.height = h} := by
    rintro h ⟨a, haS, σ, hsum, hσ, rfl⟩
    have hmin : ∀ q ∈ (D a).leafPaths, ∃ t, IsCompositeProfile S D t ∧ t.leaves = σ q + 1
        ∧ t.height = optHeight S D (σ q) := by
      intro q hq
      obtain ⟨t, ht, hl⟩ := hσ q hq
      exact Nat.sInf_mem (s := {h | ∃ t, IsCompositeProfile S D t ∧ t.leaves = σ q + 1
        ∧ t.height = h}) ⟨t.height, t, ht, hl, rfl⟩
    haveI : Inhabited MTree := ⟨leaf⟩
    choose! f hf using hmin
    obtain ⟨_, hleaves, l, r, hDa⟩ := hD a haS
    have hne' : markRoot (graftLeaves f [] (D a)) ≠ leaf := by
      rw [hDa]; simp [graftLeaves, markRoot]
    refine ⟨markRoot (graftLeaves f [] (D a)), ?_, ?_, ?_⟩
    · exact (isCompositeProfile_iff S D hD' _ hne').2
        ⟨a, haS, f, fun q hq => (hf q hq).1, rfl⟩
    · rw [leaves_markRoot, leaves_graftLeaves]
      simp only [List.nil_append]
      rw [Finset.sum_congr rfl (fun q hq => (hf q hq).2.1), Finset.sum_add_distrib,
        Finset.sum_const, smul_eq_mul, mul_one, card_leafPaths, hleaves]
      have hsum' : ∑ x ∈ (D a).leafPaths, σ x = (D a).leafPaths.sum σ := rfl
      omega
    · rw [height_markRoot, height_graftLeaves]
      simp only [List.nil_append]
      exact Finset.sup_congr rfl (fun q hq => by rw [(hf q hq).2.2])
  -- the minimiser of the height set yields an element of the recursion set
  have hAne : {h | ∃ t, IsCompositeProfile S D t ∧ t.leaves = s + 1 ∧ t.height = h}.Nonempty := by
    obtain ⟨t, ht, hl⟩ := hex
    exact ⟨t.height, t, ht, hl, rfl⟩
  obtain ⟨t, ht, hlt, hht⟩ := Nat.sInf_mem hAne
  have htne : t ≠ leaf := by
    rintro rfl
    simp [leaves] at hlt
    omega
  obtain ⟨a, haS, f, hf, rfl⟩ := (isCompositeProfile_iff S D hD' t htne).1 ht
  obtain ⟨_, hleaves, _⟩ := hD a haS
  have hB' : ((D a).leafPaths.sup fun q => q.length + optHeight S D ((f q).leaves - 1))
      ∈ {h | ∃ a ∈ S, ∃ σ : List Bool → ℕ,
          (a + (D a).leafPaths.sum σ = s) ∧ (∀ q ∈ (D a).leafPaths,
            ∃ t, IsCompositeProfile S D t ∧ t.leaves = σ q + 1)
          ∧ h = (D a).leafPaths.sup fun q => q.length + optHeight S D (σ q)} := by
    refine ⟨a, haS, fun q => (f q).leaves - 1, ?_, ?_, rfl⟩
    · rw [leaves_markRoot, leaves_graftLeaves] at hlt
      simp only [List.nil_append] at hlt
      have hsum : ((D a).leafPaths.sum fun q => (f q).leaves)
          = ((D a).leafPaths.sum fun q => (f q).leaves - 1) + (D a).leafPaths.card := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun q _ => by have := leaves_pos (f q); omega)
      rw [hsum, card_leafPaths, hleaves] at hlt
      omega
    · intro q hq
      refine ⟨f q, hf q hq, ?_⟩
      have := leaves_pos (f q)
      show (f q).leaves = (f q).leaves - 1 + 1
      omega
  have hle : ((D a).leafPaths.sup fun q => q.length + optHeight S D ((f q).leaves - 1))
      ≤ optHeight S D s := by
    have hht' : (markRoot (graftLeaves f [] (D a))).height = optHeight S D s := hht
    rw [← hht', height_markRoot, height_graftLeaves]
    simp only [List.nil_append]
    apply Finset.sup_mono_fun
    intro q hq
    have : optHeight S D ((f q).leaves - 1) ≤ (f q).height :=
      Nat.sInf_le ⟨f q, hf q hq, by have := leaves_pos (f q); omega, rfl⟩
    omega
  apply le_antisymm
  · exact le_csInf ⟨_, hB'⟩ (fun h hh => Nat.sInf_le (hBA h hh))
  · exact (Nat.sInf_le hB').trans hle

lemma optHeight_zero (S : Finset ℕ) (D : ℕ → MTree) : optHeight S D 0 = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨leaf, ⟨trivial, Or.inr rfl⟩, rfl, rfl⟩)

end MTree

end GraphMarkovMatching.Stopped
