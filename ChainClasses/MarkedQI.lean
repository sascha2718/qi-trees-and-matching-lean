/-
`sec:shape-net` of `matching_classes_simple.tex`: the abstract content of
`thm:shape-net` (basic net properties).

Two conventions fix the tex correspondence.  The shapes `𝒮` with their size
enumeration are abstracted to a `ℕ`-indexed family `S` of marked metric
spaces, the index order standing for the enumeration by size; a size function
enters only through a monotone `sz` in `sz_repIdx_le`.  Comparability is used
in the directed form: a shape reaches its representative by a marked
quasi-isometry `σ → rep`, the direction the constant bookkeeping of the tex
proof uses.

* `MarkedSpace`, `IsMarkedQI`, `MarkedQI`: `def:qi` of `prelims.tex` with all
  three constants equal to `K`, plus entry and exit marks moved by at most
  `K`; the lower bound `K⁻¹ d - K ≤ d'` is carried division-free as
  `d ≤ K d' + K²`.
* `markedQI_comp` and `markedQI_symm`: the two constants of `thm:shape-net`,
  composition at `3KK'` and quasi-inverse at `3K²`.
* `netMem`, `repIdx`: the net `ℛ_D` and the representative map `rep_D` of
  `def:shape-net`.
* `NetAdj`, `NetLink`: the edge of the label graph `G_D` of `def:shape-net`
  and its symmetrisation.  `netAdj_reach_zero` and `netLink_connected` are
  `thm:shape-connected`, the descent on the size, with the shrinking step and
  the base case as hypotheses: on shapes they are `Shape.exists_shrink` and
  `Shape.eq_of_size_le_one` once the deletion map is read as a `1`-marked
  quasi-isometry.
* The consequence list of `thm:shape-net`: existence `exists_rep` with
  `netMem_repIdx` and `markedQI_repIdx`, position `repIdx_le` and size
  `sz_repIdx_le` (the tex `|rep_D(σ)| ≤ |σ|`), idempotence `repIdx_of_netMem`,
  one class `markedQI_of_repIdx_eq` (`9D³`), and adjacent classes
  `markedQI_of_repIdx_adjacent` (`729D⁷`).
-/
import Mathlib.Tactic

namespace ChainClasses

/-- A metric space with two marked points, the abstract stand-in for a shape
realisation with its entry and exit. -/
structure MarkedSpace where
  carrier : Type
  [str : MetricSpace carrier]
  entry : carrier
  exit : carrier

attribute [instance] MarkedSpace.str

/-- `f` is a `K`-marked quasi-isometry: a `K`-quasi-isometry (`def:qi` with
all three constants equal, the lower bound in division-free form) moving each
mark by at most `K`. -/
structure IsMarkedQI (K : ℝ) (X Y : MarkedSpace) (f : X.carrier → Y.carrier) : Prop where
  upper : ∀ a b, dist (f a) (f b) ≤ K * dist a b + K
  lower : ∀ a b, dist a b ≤ K * dist (f a) (f b) + K * K
  dense : ∀ y, ∃ a, dist (f a) y ≤ K
  entry : dist (f X.entry) Y.entry ≤ K
  exit : dist (f X.exit) Y.exit ≤ K

/-- `X` and `Y` are `K`-comparable: some `K`-marked quasi-isometry `X → Y`. -/
def MarkedQI (K : ℝ) (X Y : MarkedSpace) : Prop :=
  ∃ f, IsMarkedQI K X Y f

/-- Comparability weakens as the constant grows. -/
lemma MarkedQI.mono {K K' : ℝ} {X Y : MarkedSpace} (hK : 0 ≤ K) (hKK' : K ≤ K')
    (h : MarkedQI K X Y) : MarkedQI K' X Y := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, fun a b => ?_, fun a b => ?_, fun y => ?_,
    hf.entry.trans hKK', hf.exit.trans hKK'⟩
  · have h1 := hf.upper a b
    have h2 : K * dist a b ≤ K' * dist a b :=
      mul_le_mul_of_nonneg_right hKK' dist_nonneg
    linarith
  · have h1 := hf.lower a b
    have h2 : K * dist (f a) (f b) ≤ K' * dist (f a) (f b) :=
      mul_le_mul_of_nonneg_right hKK' dist_nonneg
    have h3 : K * K ≤ K' * K' := mul_le_mul hKK' hKK' hK (hK.trans hKK')
    linarith
  · obtain ⟨a, ha⟩ := hf.dense y
    exact ⟨a, ha.trans hKK'⟩

/-- The identity is a `K`-marked quasi-isometry for every `K ≥ 1`. -/
lemma markedQI_id {K : ℝ} (hK : 1 ≤ K) (X : MarkedSpace) : MarkedQI K X X := by
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  refine ⟨fun x => x, fun a b => ?_, fun a b => ?_, fun y => ⟨y, by simpa using hK0⟩,
    by simpa using hK0, by simpa using hK0⟩
  · show dist a b ≤ K * dist a b + K
    nlinarith [dist_nonneg (x := a) (y := b),
      mul_nonneg (sub_nonneg.mpr hK) (dist_nonneg (x := a) (y := b))]
  · show dist a b ≤ K * dist a b + K * K
    nlinarith [dist_nonneg (x := a) (y := b),
      mul_nonneg (sub_nonneg.mpr hK) (dist_nonneg (x := a) (y := b))]

/-- **The collapse of a space of small diameter.**  A space whose diameter is
at most `K²` is `K`-comparable to a point: the constant map has nothing to
prove but the lower bound, and both marks of the target are that point. -/
lemma markedQI_of_subsingleton {K : ℝ} (hK : 1 ≤ K) {X Y : MarkedSpace}
    [Subsingleton Y.carrier] (hdiam : ∀ a b : X.carrier, dist a b ≤ K * K) :
    MarkedQI K X Y := by
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  have hzero : ∀ a b : Y.carrier, dist a b = 0 := fun a b => by
    rw [Subsingleton.elim a b, dist_self]
  refine ⟨fun _ => Y.entry, fun a b => ?_, fun a b => ?_, fun y => ⟨X.entry, ?_⟩, ?_, ?_⟩
  · rw [hzero]
    nlinarith [dist_nonneg (x := a) (y := b)]
  · rw [hzero, mul_zero, zero_add]
    exact hdiam a b
  · rw [hzero]
    exact hK0
  · rw [hzero]
    exact hK0
  · rw [hzero]
    exact hK0

/-- `thm:shape-net`, first constant: the composition of a `K`-marked and a
`K'`-marked quasi-isometry is `3KK'`-marked. -/
lemma markedQI_comp {K K' : ℝ} {X Y Z : MarkedSpace} (hK : 1 ≤ K) (hK' : 1 ≤ K')
    (h : MarkedQI K X Y) (h' : MarkedQI K' Y Z) : MarkedQI (3 * K * K') X Z := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  have hK'0 : (0 : ℝ) ≤ K' := zero_le_one.trans hK'
  refine ⟨fun x => g (f x), fun a b => ?_, fun a b => ?_, fun z => ?_, ?_, ?_⟩
  · -- distortion `KK'` with additive error `KK' + K' ≤ 3KK'`
    have h1 := hg.upper (f a) (f b)
    have h2 : K' * dist (f a) (f b) ≤ K' * (K * dist a b + K) :=
      mul_le_mul_of_nonneg_left (hf.upper a b) hK'0
    show dist (g (f a)) (g (f b)) ≤ 3 * K * K' * dist a b + 3 * K * K'
    nlinarith [mul_nonneg (mul_nonneg hK0 hK'0) (dist_nonneg (x := a) (y := b))]
  · -- `d ≤ KK' d'' + KK'² + K²` and `KK'² + K² ≤ 2K²K'² ≤ (3KK')²`
    have h1 := hf.lower a b
    have h2 : K * dist (f a) (f b) ≤ K * (K' * dist (g (f a)) (g (f b)) + K' * K') :=
      mul_le_mul_of_nonneg_left (hg.lower (f a) (f b)) hK0
    have hK'2 : (1 : ℝ) ≤ K' * K' := by nlinarith
    have e1 : K * (K' * K') ≤ K * K' * (K * K') := by
      nlinarith [mul_nonneg (mul_nonneg hK'0 hK'0) hK0]
    have e2 : K * K ≤ K * K' * (K * K') := by nlinarith [mul_nonneg hK0 hK0]
    show dist a b ≤ 3 * K * K' * dist (g (f a)) (g (f b)) + 3 * K * K' * (3 * K * K')
    nlinarith [mul_nonneg (mul_nonneg hK0 hK'0) (dist_nonneg (x := g (f a)) (y := g (f b))),
      mul_nonneg (mul_nonneg hK0 hK'0) (mul_nonneg hK0 hK'0)]
  · -- density `KK' + 2K' ≤ 3KK'`
    obtain ⟨y, hy⟩ := hg.dense z
    obtain ⟨a, ha⟩ := hf.dense y
    refine ⟨a, ?_⟩
    have htri : dist (g (f a)) z ≤ dist (g (f a)) (g y) + dist (g y) z := dist_triangle _ _ _
    have h1 := hg.upper (f a) y
    have h2 : K' * dist (f a) y ≤ K' * K := mul_le_mul_of_nonneg_left ha hK'0
    show dist (g (f a)) z ≤ 3 * K * K'
    nlinarith
  · -- the entry mark moves by at most `KK' + 2K' ≤ 3KK'`
    have htri : dist (g (f X.entry)) Z.entry
        ≤ dist (g (f X.entry)) (g Y.entry) + dist (g Y.entry) Z.entry := dist_triangle _ _ _
    have h1 := hg.upper (f X.entry) Y.entry
    have h2 : K' * dist (f X.entry) Y.entry ≤ K' * K :=
      mul_le_mul_of_nonneg_left hf.entry hK'0
    have h3 := hg.entry
    show dist (g (f X.entry)) Z.entry ≤ 3 * K * K'
    nlinarith
  · have htri : dist (g (f X.exit)) Z.exit
        ≤ dist (g (f X.exit)) (g Y.exit) + dist (g Y.exit) Z.exit := dist_triangle _ _ _
    have h1 := hg.upper (f X.exit) Y.exit
    have h2 : K' * dist (f X.exit) Y.exit ≤ K' * K :=
      mul_le_mul_of_nonneg_left hf.exit hK'0
    have h3 := hg.exit
    show dist (g (f X.exit)) Z.exit ≤ 3 * K * K'
    nlinarith

/-- `thm:shape-net`, second constant: a `K`-marked quasi-isometry has a
`3K²`-marked quasi-inverse. -/
lemma markedQI_symm {K : ℝ} {X Y : MarkedSpace} (hK : 1 ≤ K) (h : MarkedQI K X Y) :
    MarkedQI (3 * K ^ 2) Y X := by
  obtain ⟨f, hf⟩ := h
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  choose g hg using hf.dense
  refine ⟨g, fun a b => ?_, fun a b => ?_, fun x => ?_, ?_, ?_⟩
  · -- distortion factor `K` with additive error `3K²`
    have h1 := hf.lower (g a) (g b)
    have h2 : dist (f (g a)) (f (g b)) ≤ dist (f (g a)) a + dist a b + dist b (f (g b)) :=
      dist_triangle4 _ _ _ _
    have h3 : dist b (f (g b)) ≤ K := by rw [dist_comm]; exact hg b
    have h4 : K * dist (f (g a)) (f (g b))
        ≤ K * (dist (f (g a)) a + dist a b + dist b (f (g b))) :=
      mul_le_mul_of_nonneg_left h2 hK0
    have h5 : K * dist (f (g a)) a ≤ K * K := mul_le_mul_of_nonneg_left (hg a) hK0
    have h6 : K * dist b (f (g b)) ≤ K * K := mul_le_mul_of_nonneg_left h3 hK0
    nlinarith [mul_nonneg (mul_nonneg hK0 (sub_nonneg.mpr hK)) (dist_nonneg (x := a) (y := b)),
      mul_nonneg (mul_nonneg hK0 hK0) (dist_nonneg (x := a) (y := b))]
  · -- `d ≤ K d' + 3K ≤ 3K² d' + (3K²)²`
    have h2 : dist a b ≤ dist a (f (g a)) + dist (f (g a)) (f (g b)) + dist (f (g b)) b :=
      dist_triangle4 _ _ _ _
    have h3 : dist a (f (g a)) ≤ K := by rw [dist_comm]; exact hg a
    have h4 := hf.upper (g a) (g b)
    nlinarith [hg b,
      mul_nonneg (mul_nonneg hK0 (sub_nonneg.mpr hK)) (dist_nonneg (x := g a) (y := g b)),
      mul_nonneg (mul_nonneg hK0 hK0) (dist_nonneg (x := g a) (y := g b)),
      mul_nonneg hK0 (sub_nonneg.mpr (one_le_pow₀ hK (n := 3))), pow_nonneg hK0 4]
  · -- `2K²`-dense image
    refine ⟨f x, ?_⟩
    have h1 := hf.lower (g (f x)) x
    have h2 : K * dist (f (g (f x))) (f x) ≤ K * K :=
      mul_le_mul_of_nonneg_left (hg (f x)) hK0
    nlinarith [sq_nonneg K]
  · -- the entry mark moves by at most `3K²`
    have h1 := hf.lower (g Y.entry) X.entry
    have h2 : dist (f (g Y.entry)) (f X.entry)
        ≤ dist (f (g Y.entry)) Y.entry + dist Y.entry (f X.entry) := dist_triangle _ _ _
    have h3 : dist Y.entry (f X.entry) ≤ K := by rw [dist_comm]; exact hf.entry
    have h4 : K * dist (f (g Y.entry)) (f X.entry)
        ≤ K * (dist (f (g Y.entry)) Y.entry + dist Y.entry (f X.entry)) :=
      mul_le_mul_of_nonneg_left h2 hK0
    have h5 : K * dist (f (g Y.entry)) Y.entry ≤ K * K :=
      mul_le_mul_of_nonneg_left (hg Y.entry) hK0
    have h6 : K * dist Y.entry (f X.entry) ≤ K * K := mul_le_mul_of_nonneg_left h3 hK0
    nlinarith
  · have h1 := hf.lower (g Y.exit) X.exit
    have h2 : dist (f (g Y.exit)) (f X.exit)
        ≤ dist (f (g Y.exit)) Y.exit + dist Y.exit (f X.exit) := dist_triangle _ _ _
    have h3 : dist Y.exit (f X.exit) ≤ K := by rw [dist_comm]; exact hf.exit
    have h4 : K * dist (f (g Y.exit)) (f X.exit)
        ≤ K * (dist (f (g Y.exit)) Y.exit + dist Y.exit (f X.exit)) :=
      mul_le_mul_of_nonneg_left h2 hK0
    have h5 : K * dist (f (g Y.exit)) Y.exit ≤ K * K :=
      mul_le_mul_of_nonneg_left (hg Y.exit) hK0
    have h6 : K * dist Y.exit (f X.exit) ≤ K * K := mul_le_mul_of_nonneg_left h3 hK0
    nlinarith

/-! ### The net and the representatives, `def:shape-net` -/

variable (S : ℕ → MarkedSpace) (Dq : ℝ)

/-- Membership in the net `ℛ_D`: `S n` admits no `Dq`-marked quasi-isometry
to an earlier net member. -/
def netMem (n : ℕ) : Prop :=
  ∀ m, m < n → netMem m → ¬ MarkedQI Dq (S n) (S m)
termination_by n

/-- The defining recursion of `netMem`, unfolded once. -/
lemma netMem_iff (n : ℕ) :
    netMem S Dq n ↔ ∀ m, m < n → netMem S Dq m → ¬ MarkedQI Dq (S n) (S m) := by
  rw [netMem]

/-- `thm:shape-net`, existence: some net index is reached from `S n`. -/
lemma exists_rep (hD : 1 ≤ Dq) (n : ℕ) :
    ∃ m, netMem S Dq m ∧ MarkedQI Dq (S n) (S m) := by
  by_cases h : netMem S Dq n
  · exact ⟨n, h, markedQI_id hD (S n)⟩
  · rw [netMem_iff] at h
    push Not at h
    obtain ⟨m, _, hm, hqi⟩ := h
    exact ⟨m, hm, hqi⟩

/-- `rep_D`: the earliest net index reached from `S n` at scale `Dq`. -/
noncomputable def repIdx (n : ℕ) : ℕ :=
  sInf {m | netMem S Dq m ∧ MarkedQI Dq (S n) (S m)}

/-- The representative lies in the net and is reached from `S n`. -/
lemma repIdx_mem (hD : 1 ≤ Dq) (n : ℕ) :
    netMem S Dq (repIdx S Dq n) ∧ MarkedQI Dq (S n) (S (repIdx S Dq n)) :=
  Nat.sInf_mem (exists_rep S Dq hD n)

lemma netMem_repIdx (hD : 1 ≤ Dq) (n : ℕ) : netMem S Dq (repIdx S Dq n) :=
  (repIdx_mem S Dq hD n).1

lemma markedQI_repIdx (hD : 1 ≤ Dq) (n : ℕ) :
    MarkedQI Dq (S n) (S (repIdx S Dq n)) :=
  (repIdx_mem S Dq hD n).2

/-- `thm:shape-net`: the representative occurs no later than `n`. -/
lemma repIdx_le (hD : 1 ≤ Dq) (n : ℕ) : repIdx S Dq n ≤ n := by
  by_cases h : netMem S Dq n
  · exact Nat.sInf_le ⟨h, markedQI_id hD (S n)⟩
  · rw [netMem_iff] at h
    push Not at h
    obtain ⟨m, hmn, hm, hqi⟩ := h
    have hle : repIdx S Dq n ≤ m := Nat.sInf_le ⟨hm, hqi⟩
    exact hle.trans hmn.le

/-- `thm:shape-net`: `|rep_D(σ)| ≤ |σ|` for any size monotone along the
enumeration. -/
lemma sz_repIdx_le (hD : 1 ≤ Dq) {sz : ℕ → ℕ} (hsz : Monotone sz) (n : ℕ) :
    sz (repIdx S Dq n) ≤ sz n :=
  hsz (repIdx_le S Dq hD n)

/-- `thm:shape-net`, idempotence: each net member represents itself, so every
class contains its representative. -/
lemma repIdx_of_netMem (hD : 1 ≤ Dq) {n : ℕ} (hn : netMem S Dq n) :
    repIdx S Dq n = n := by
  refine le_antisymm (Nat.sInf_le ⟨hn, markedQI_id hD (S n)⟩) (not_lt.mp fun hlt => ?_)
  obtain ⟨hmem, hqi⟩ := repIdx_mem S Dq hD n
  exact (netMem_iff S Dq n).mp hn _ hlt hmem hqi

/-- The first member of the enumeration lies in the net: it has no earlier
member to be comparable to. -/
lemma netMem_zero : netMem S Dq 0 := by
  rw [netMem_iff]
  intro m hm
  exact absurd hm (Nat.not_lt_zero m)

/-- **The class of the first member.**  A space comparable to the first member
of the enumeration is represented by it, so the classes other than that one
carry no such space. -/
lemma repIdx_eq_zero {n : ℕ} (h : MarkedQI Dq (S n) (S 0)) : repIdx S Dq n = 0 :=
  Nat.le_zero.mp (Nat.sInf_le ⟨netMem_zero S Dq, h⟩)

/-- `thm:shape-net`: two members of one class are `9D³`-comparable, through
the representative. -/
theorem markedQI_of_repIdx_eq (hD : 1 ≤ Dq) {n n' : ℕ}
    (h : repIdx S Dq n = repIdx S Dq n') :
    MarkedQI (9 * Dq ^ 3) (S n) (S n') := by
  have hD2 : (1 : ℝ) ≤ 3 * Dq ^ 2 := by nlinarith
  have h1 := markedQI_repIdx S Dq hD n
  rw [h] at h1
  have h2 := markedQI_symm hD (markedQI_repIdx S Dq hD n')
  have h3 := markedQI_comp hD hD2 h1 h2
  have e : 3 * Dq * (3 * Dq ^ 2) = 9 * Dq ^ 3 := by ring
  rwa [e] at h3

/-- `thm:shape-net`: members of equal or adjacent classes, the representatives
being `27D⁴`-comparable, are `729D⁷`-comparable. -/
theorem markedQI_of_repIdx_adjacent (hD : 1 ≤ Dq) {n n' : ℕ}
    (h : MarkedQI (27 * Dq ^ 4) (S (repIdx S Dq n)) (S (repIdx S Dq n'))) :
    MarkedQI (729 * Dq ^ 7) (S n) (S n') := by
  have h4 : (1 : ℝ) ≤ Dq ^ 4 := one_le_pow₀ hD
  have hD2 : (1 : ℝ) ≤ 3 * Dq ^ 2 := by nlinarith
  have ha : (1 : ℝ) ≤ 27 * Dq ^ 4 := by linarith
  have h1 := markedQI_comp hD ha (markedQI_repIdx S Dq hD n) h
  have hc : (1 : ℝ) ≤ 3 * Dq * (27 * Dq ^ 4) := by nlinarith [one_le_pow₀ hD (n := 5)]
  have h2 := markedQI_symm hD (markedQI_repIdx S Dq hD n')
  have h3 := markedQI_comp hc hD2 h1 h2
  have e : 3 * (3 * Dq * (27 * Dq ^ 4)) * (3 * Dq ^ 2) = 729 * Dq ^ 7 := by ring
  rwa [e] at h3

/-! ### Connectivity, `thm:shape-connected` -/

/-- The edge of `G_D`: distinct net members that are `27D⁴`-comparable. -/
def NetAdj (a b : ℕ) : Prop :=
  a ≠ b ∧ netMem S Dq a ∧ netMem S Dq b ∧ MarkedQI (27 * Dq ^ 4) (S a) (S b)

/-- The undirected edge, comparability being carried in the directed form. -/
def NetLink (a b : ℕ) : Prop := NetAdj S Dq a b ∨ NetAdj S Dq b a

lemma netLink_symm {a b : ℕ} (h : NetLink S Dq a b) : NetLink S Dq b a := by
  simp only [NetLink] at h ⊢; tauto

lemma reflTransGen_netLink_symm {a b : ℕ}
    (h : Relation.ReflTransGen (NetLink S Dq) a b) :
    Relation.ReflTransGen (NetLink S Dq) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (netLink_symm S Dq hbc) ih

lemma reflTransGen_netAdj_netLink {a b : ℕ}
    (h : Relation.ReflTransGen (NetAdj S Dq) a b) :
    Relation.ReflTransGen (NetLink S Dq) a b := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (Or.inl hbc)

/-- `thm:shape-connected`, the descent on the size: deleting a leaf shrinks a
shape by a `1`-marked quasi-isometry, and the shrunk shape reaches its
representative, so every net member is joined to the first index. -/
theorem netAdj_reach_zero (hD : 1 ≤ Dq) {sz : ℕ → ℕ} (hsz : Monotone sz)
    (hbase : ∀ n, sz n ≤ 1 → n = 0)
    (hshrink : ∀ n, 2 ≤ sz n → ∃ m, sz m < sz n ∧ MarkedQI 1 (S n) (S m)) :
    ∀ n, netMem S Dq n → Relation.ReflTransGen (NetAdj S Dq) n 0 := by
  have hD0 : (0 : ℝ) ≤ Dq := zero_le_one.trans hD
  have hcube : (1 : ℝ) ≤ Dq ^ 3 := one_le_pow₀ hD
  have hle : 3 * 1 * Dq ≤ 27 * Dq ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hcube hD0]
  have key : ∀ k n, sz n ≤ k → netMem S Dq n →
      Relation.ReflTransGen (NetAdj S Dq) n 0 := by
    intro k
    induction k with
    | zero =>
        intro n hk _
        have hn0 : n = 0 := hbase n (by omega)
        subst hn0
        exact Relation.ReflTransGen.refl
    | succ k ih =>
        intro n hk hn
        by_cases h1 : sz n ≤ 1
        · have hn0 : n = 0 := hbase n h1
          subst hn0
          exact Relation.ReflTransGen.refl
        · obtain ⟨m, hm, hqi⟩ := hshrink n (by omega)
          have hrmem : netMem S Dq (repIdx S Dq m) := netMem_repIdx S Dq hD m
          have hlt : sz (repIdx S Dq m) < sz n :=
            lt_of_le_of_lt (sz_repIdx_le S Dq hD hsz m) hm
          have hcomp : MarkedQI (3 * 1 * Dq) (S n) (S (repIdx S Dq m)) :=
            markedQI_comp le_rfl hD hqi (markedQI_repIdx S Dq hD m)
          have hne : n ≠ repIdx S Dq m := by
            intro h; rw [h] at hlt; exact lt_irrefl _ hlt
          exact Relation.ReflTransGen.head
            ⟨hne, hn, hrmem, hcomp.mono (by linarith) hle⟩ (ih _ (by omega) hrmem)
  exact fun n hn => key (sz n) n le_rfl hn

/-- **`thm:shape-connected`**: `G_D` is connected, any two net members being
joined by a path of edges. -/
theorem netLink_connected (hD : 1 ≤ Dq) {sz : ℕ → ℕ} (hsz : Monotone sz)
    (hbase : ∀ n, sz n ≤ 1 → n = 0)
    (hshrink : ∀ n, 2 ≤ sz n → ∃ m, sz m < sz n ∧ MarkedQI 1 (S n) (S m))
    {a b : ℕ} (ha : netMem S Dq a) (hb : netMem S Dq b) :
    Relation.ReflTransGen (NetLink S Dq) a b := by
  have h : ∀ n, netMem S Dq n → Relation.ReflTransGen (NetLink S Dq) n 0 := fun n hn =>
    reflTransGen_netAdj_netLink S Dq (netAdj_reach_zero S Dq hD hsz hbase hshrink n hn)
  exact (h a ha).trans (reflTransGen_netLink_symm S Dq (h b hb))

end ChainClasses
