import ChainClasses.General.GeneralAssembly
import ChainClasses.Regime.BlobField
import ChainClasses.Universality.GeneralObstructions
import ChainClasses.Bushy.AssemblyRelabel
import ChainClasses.General.GeneralCascade
import ChainClasses.Universality.BAssembly

/-!
`thm:chain-general` of `trichotomy.tex`, the deterministic core, first part: pieces, finite
trees with an entry and a list of ports; multi-marked spaces and port quasi-isometries;
the assembly `PAssembly` of a family of pieces with its distance formulas, as a metric
space; the glued transfer over pieces; the flat configuration; and words over `Fin N` read
over `ℕ`.  The chain regime and the blobs follow in `ChainBlob`, `BlobPiece` and
`BlobPresented`, and `BlobAssembly` concludes.
-/

namespace ChainClasses

/-! ### Pieces: finite trees with an entry and a list of ports -/

/-- **A piece**: a prefix-closed set of addresses, read as a rooted tree with the root as
its entry, together with a list of ports, each an address of the piece paired with a free
child index at which a copy is planted; the planted child is no address of the piece, and
distinct ports plant at distinct children. -/
structure Piece where
  /-- The addresses of the piece. -/
  mem : List ℕ → Prop
  /-- The root is an address. -/
  nil_mem : mem []
  /-- The address set is closed under prefixes. -/
  mem_of_prefix : ∀ {p q : List ℕ}, p <+: q → mem q → mem p
  /-- The ports, each with the free child index at which a copy is planted. -/
  ports : List (List ℕ × ℕ)
  /-- Every port is an address. -/
  port_mem : ∀ x ∈ ports, mem x.1
  /-- The child at which a copy is planted is no address of the piece. -/
  slot_free : ∀ x ∈ ports, ¬ mem (x.1 ++ [x.2])
  /-- Distinct ports plant at distinct children. -/
  ports_nodup : ports.Nodup

namespace Piece

/-- The vertices of a piece. -/
def carrier (X : Piece) : Type := {p : List ℕ // X.mem p}

/-- The number of ports. -/
def nports (X : Piece) : ℕ := X.ports.length

/-- The `j`-th port with its slot, the root with slot `0` past the last port. -/
def portSlot (X : Piece) (j : ℕ) : List ℕ × ℕ := X.ports.getD j ([], 0)

/-- The address of the `j`-th port. -/
def port (X : Piece) (j : ℕ) : List ℕ := (X.portSlot j).1

/-- The slot of the `j`-th port. -/
def slot (X : Piece) (j : ℕ) : ℕ := (X.portSlot j).2

/-- The address at which the copy planted at the `j`-th port sits: the port followed by
its slot. -/
def root (X : Piece) (j : ℕ) : List ℕ := X.port j ++ [X.slot j]

lemma portSlot_mem {X : Piece} {j : ℕ} (hj : j < X.nports) : X.portSlot j ∈ X.ports := by
  rw [portSlot, List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma portSlot_of_le {X : Piece} {j : ℕ} (hj : X.nports ≤ j) : X.portSlot j = ([], 0) :=
  List.getD_eq_default _ _ hj

/-- Every port, the junk ports included, is an address. -/
lemma port_mem' (X : Piece) (j : ℕ) : X.mem (X.port j) := by
  rcases lt_or_ge j X.nports with hj | hj
  · exact X.port_mem _ (portSlot_mem hj)
  · rw [port, portSlot_of_le hj]
    exact X.nil_mem

/-- Below the port count the planted child is no address. -/
lemma root_not_mem {X : Piece} {j : ℕ} (hj : j < X.nports) : ¬ X.mem (X.root j) :=
  X.slot_free _ (portSlot_mem hj)

/-- Distinct ports below the port count plant at distinct children. -/
lemma root_ne {X : Piece} {a b : ℕ} (ha : a < X.nports) (hb : b < X.nports) (hab : a ≠ b) :
    X.root a ≠ X.root b := by
  intro h
  have h1 : X.portSlot a = X.portSlot b := by
    have hp : X.port a = X.port b := by
      have := congrArg List.dropLast h
      simpa [root] using this
    have hs : X.slot a = X.slot b := by
      have := congrArg (fun l => l.getLast?) h
      simpa [root] using this
    exact Prod.ext hp hs
  rw [portSlot, portSlot, List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb] at h1
  exact hab (List.Nodup.getElem_inj_iff X.ports_nodup |>.mp h1)

/-- **The wedge through a port**: the wedge of an address of the piece with an address
reaching past a port into the planted child is its wedge with the port. -/
lemma wedgeN_eq_wedgeN_port (X : Piece) {p r : List ℕ} {j : ℕ} (hj : j < X.nports)
    (hp : X.mem p) (hr : X.root j <+: r) :
    wedgeN p r = wedgeN p (X.port j) := by
  have hnr : X.port j <+: r := (List.prefix_append _ _).trans hr
  have hg1 : wedgeN p (X.port j) <+: p := wedgeN_prefix_left _ _
  have hg2 : wedgeN p (X.port j) <+: X.port j := wedgeN_prefix_right _ _
  have hle : wedgeN p (X.port j) <+: wedgeN p r := prefix_wedgeN hg1 (hg2.trans hnr)
  rcases List.prefix_or_prefix_of_prefix (wedgeN_prefix_right p r) hnr with h | h
  · have h2 : wedgeN p r <+: wedgeN p (X.port j) := prefix_wedgeN (wedgeN_prefix_left p r) h
    exact h2.eq_of_length (le_antisymm h2.length_le hle.length_le)
  · have hnp : X.port j <+: p := h.trans (wedgeN_prefix_left p r)
    obtain ⟨v, rfl⟩ := hnp
    cases v with
    | nil =>
        rw [List.append_nil, wedgeN_of_prefix hnr, wedgeN_self]
    | cons i v =>
        have hne : i ≠ X.slot j := by
          intro hi
          subst hi
          exact root_not_mem hj (X.mem_of_prefix ⟨v, by simp [root]⟩ hp)
        rw [wedgeN_of_diverge hne ⟨v, by simp⟩ hr, wedgeN_comm,
          wedgeN_of_prefix (List.prefix_append _ _)]

/-- **The wedge of two planted children**: two addresses reaching past distinct ports into
their planted children meet at the wedge of the two ports. -/
lemma wedgeN_root_root (X : Piece) {a b : ℕ} (ha : a < X.nports) (hb : b < X.nports)
    (hab : a ≠ b) {r r' : List ℕ} (hr : X.root a <+: r) (hr' : X.root b <+: r') :
    wedgeN r r' = wedgeN (X.port a) (X.port b) := by
  have hpa : X.port a <+: r := (List.prefix_append _ _).trans hr
  have hpb : X.port b <+: r' := (List.prefix_append _ _).trans hr'
  by_cases h1 : X.port a <+: X.port b
  · rw [wedgeN_of_prefix h1]
    obtain ⟨v, hv⟩ := h1
    cases v with
    | nil =>
        rw [List.append_nil] at hv
        have hs : X.slot a ≠ X.slot b := by
          intro hs
          exact root_ne ha hb hab (by rw [root, root, hv, hs])
        exact wedgeN_of_diverge hs hr (hv ▸ hr')
    | cons i v =>
        have hne : X.slot a ≠ i := by
          intro hi
          subst hi
          exact root_not_mem ha (X.mem_of_prefix ⟨v, by rw [root, ← hv]; simp⟩
            (X.port_mem' b))
        exact wedgeN_of_diverge hne hr ((show X.port a ++ [i] <+: X.port b from
          ⟨v, by rw [← hv]; simp⟩).trans hpb)
  · by_cases h2 : X.port b <+: X.port a
    · rw [wedgeN_comm (X.port a), wedgeN_of_prefix h2]
      obtain ⟨v, hv⟩ := h2
      cases v with
      | nil =>
          rw [List.append_nil] at hv
          exact absurd (hv ▸ List.prefix_refl _) h1
      | cons i v =>
          have hne : X.slot b ≠ i := by
            intro hi
            subst hi
            exact root_not_mem hb (X.mem_of_prefix ⟨v, by rw [root, ← hv]; simp⟩
              (X.port_mem' a))
          rw [wedgeN_comm]
          exact wedgeN_of_diverge hne hr' ((show X.port b ++ [i] <+: X.port a from
            ⟨v, by rw [← hv]; simp⟩).trans hpa)
    · obtain ⟨z, i, i', hii', hzi, hzi'⟩ := exists_divergeN h1 h2
      rw [wedgeN_of_diverge hii' hzi hzi', wedgeN_of_diverge hii' (hzi.trans hpa) (hzi'.trans hpb)]

/-- The metric of a piece: the address metric. -/
noncomputable instance instMetricSpace (X : Piece) : MetricSpace X.carrier where
  dist x y := (addrDist x.1 y.1 : ℝ)
  dist_self x := by simp
  dist_comm x y := by simp only [addrDist_comm x.1 y.1]
  dist_triangle x y z := by
    have := addrDist_triangle x.1 y.1 z.1
    exact_mod_cast this
  eq_of_dist_eq_zero {x y} h := by
    have h0 : addrDist x.1 y.1 = 0 := by exact_mod_cast h
    exact Subtype.ext (addrDist_eq_zero_iff.mp h0)

@[simp] lemma dist_carrier {X : Piece} (x y : X.carrier) :
    dist x y = (addrDist x.1 y.1 : ℝ) := rfl

/-- The entry of a piece: its root. -/
def entry (X : Piece) : X.carrier := ⟨[], X.nil_mem⟩

/-- The `j`-th port of a piece as a vertex. -/
def portVert (X : Piece) (j : ℕ) : X.carrier := ⟨X.port j, X.port_mem' j⟩

@[simp] lemma entry_val (X : Piece) : (X.entry).1 = [] := rfl

@[simp] lemma portVert_val (X : Piece) (j : ℕ) : (X.portVert j).1 = X.port j := rfl

end Piece

/-! ### Multi-marked spaces and port quasi-isometries -/

/-- A metric space with an entry and a sequence of ports, the abstract stand-in for a piece
with its entry and its ports; the ports past the port count of a piece are its entry. -/
structure PortSpace where
  carrier : Type
  [str : MetricSpace carrier]
  entry : carrier
  port : ℕ → carrier

attribute [instance] PortSpace.str

/-- The port space of a piece. -/
noncomputable def Piece.space (X : Piece) : PortSpace where
  carrier := X.carrier
  entry := X.entry
  port := X.portVert

@[simp] lemma Piece.space_entry (X : Piece) : X.space.entry = X.entry := rfl

@[simp] lemma Piece.space_port (X : Piece) (j : ℕ) : X.space.port j = X.portVert j := rfl

/-- `f` is a `K`-port quasi-isometry: a `K`-quasi-isometry moving the entry and every port
by at most `K`. -/
structure IsPortQI (K : ℝ) (X Y : PortSpace) (f : X.carrier → Y.carrier) : Prop where
  upper : ∀ a b, dist (f a) (f b) ≤ K * dist a b + K
  lower : ∀ a b, dist a b ≤ K * dist (f a) (f b) + K * K
  dense : ∀ y, ∃ a, dist (f a) y ≤ K
  entry : dist (f X.entry) Y.entry ≤ K
  port : ∀ j, dist (f (X.port j)) (Y.port j) ≤ K

/-- A port space read as a marked space with the `j`-th port as its exit. -/
def PortSpace.toMarked (X : PortSpace) (j : ℕ) : MarkedSpace :=
  ⟨X.carrier, X.entry, X.port j⟩

/-- A port quasi-isometry is a marked quasi-isometry for every port. -/
lemma IsPortQI.toMarked {K : ℝ} {X Y : PortSpace} {f : X.carrier → Y.carrier}
    (hf : IsPortQI K X Y f) (j : ℕ) : IsMarkedQI K (X.toMarked j) (Y.toMarked j) f :=
  ⟨hf.upper, hf.lower, hf.dense, hf.entry, hf.port j⟩

/-- The composition of a `K`-port and a `K'`-port quasi-isometry is `3KK'`-port. -/
lemma IsPortQI.comp {K K' : ℝ} {X Y Z : PortSpace} (hK : 1 ≤ K) (hK' : 1 ≤ K')
    {f : X.carrier → Y.carrier} {g : Y.carrier → Z.carrier}
    (hf : IsPortQI K X Y f) (hg : IsPortQI K' Y Z g) :
    IsPortQI (3 * K * K') X Z (fun x => g (f x)) := by
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  have hK'0 : (0 : ℝ) ≤ K' := zero_le_one.trans hK'
  refine ⟨fun a b => ?_, fun a b => ?_, fun z => ?_, ?_, fun j => ?_⟩
  · have h1 := hg.upper (f a) (f b)
    have h2 : K' * dist (f a) (f b) ≤ K' * (K * dist a b + K) :=
      mul_le_mul_of_nonneg_left (hf.upper a b) hK'0
    nlinarith [mul_nonneg (mul_nonneg hK0 hK'0) (dist_nonneg (x := a) (y := b))]
  · have h1 := hf.lower a b
    have h2 : K * dist (f a) (f b) ≤ K * (K' * dist (g (f a)) (g (f b)) + K' * K') :=
      mul_le_mul_of_nonneg_left (hg.lower (f a) (f b)) hK0
    have hK'2 : (1 : ℝ) ≤ K' * K' := by nlinarith
    have e1 : K * (K' * K') ≤ K * K' * (K * K') := by
      nlinarith [mul_nonneg (mul_nonneg hK'0 hK'0) hK0]
    have e2 : K * K ≤ K * K' * (K * K') := by nlinarith [mul_nonneg hK0 hK0]
    nlinarith [mul_nonneg (mul_nonneg hK0 hK'0) (dist_nonneg (x := g (f a)) (y := g (f b))),
      mul_nonneg (mul_nonneg hK0 hK'0) (mul_nonneg hK0 hK'0)]
  · obtain ⟨y, hy⟩ := hg.dense z
    obtain ⟨a, ha⟩ := hf.dense y
    refine ⟨a, ?_⟩
    have htri : dist (g (f a)) z ≤ dist (g (f a)) (g y) + dist (g y) z := dist_triangle _ _ _
    have h1 := hg.upper (f a) y
    have h2 : K' * dist (f a) y ≤ K' * K := mul_le_mul_of_nonneg_left ha hK'0
    nlinarith
  · have htri : dist (g (f X.entry)) Z.entry
        ≤ dist (g (f X.entry)) (g Y.entry) + dist (g Y.entry) Z.entry := dist_triangle _ _ _
    have h1 := hg.upper (f X.entry) Y.entry
    have h2 : K' * dist (f X.entry) Y.entry ≤ K' * K :=
      mul_le_mul_of_nonneg_left hf.entry hK'0
    have h3 := hg.entry
    nlinarith
  · have htri : dist (g (f (X.port j))) (Z.port j)
        ≤ dist (g (f (X.port j))) (g (Y.port j)) + dist (g (Y.port j)) (Z.port j) :=
      dist_triangle _ _ _
    have h1 := hg.upper (f (X.port j)) (Y.port j)
    have h2 : K' * dist (f (X.port j)) (Y.port j) ≤ K' * K :=
      mul_le_mul_of_nonneg_left (hf.port j) hK'0
    have h3 := hg.port j
    nlinarith

/-- A `K`-port quasi-isometry has a `3K²`-port quasi-inverse. -/
lemma IsPortQI.symm {K : ℝ} {X Y : PortSpace} (hK : 1 ≤ K) {f : X.carrier → Y.carrier}
    (hf : IsPortQI K X Y f) : ∃ g : Y.carrier → X.carrier, IsPortQI (3 * K ^ 2) Y X g := by
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  choose g hg using hf.dense
  have hmark : ∀ (mX : X.carrier) (mY : Y.carrier), dist (f mX) mY ≤ K →
      dist (g mY) mX ≤ 3 * K ^ 2 := by
    intro mX mY hm
    have h1 := hf.lower (g mY) mX
    have h2 : dist (f (g mY)) (f mX) ≤ dist (f (g mY)) mY + dist mY (f mX) := dist_triangle _ _ _
    have h3 : dist mY (f mX) ≤ K := by rw [dist_comm]; exact hm
    have h4 : K * dist (f (g mY)) (f mX) ≤ K * (dist (f (g mY)) mY + dist mY (f mX)) :=
      mul_le_mul_of_nonneg_left h2 hK0
    have h5 : K * dist (f (g mY)) mY ≤ K * K := mul_le_mul_of_nonneg_left (hg mY) hK0
    have h6 : K * dist mY (f mX) ≤ K * K := mul_le_mul_of_nonneg_left h3 hK0
    nlinarith
  refine ⟨g, fun a b => ?_, fun a b => ?_, fun x => ?_, hmark _ _ hf.entry,
    fun j => hmark _ _ (hf.port j)⟩
  · have h1 := hf.lower (g a) (g b)
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
  · have h2 : dist a b ≤ dist a (f (g a)) + dist (f (g a)) (f (g b)) + dist (f (g b)) b :=
      dist_triangle4 _ _ _ _
    have h3 : dist a (f (g a)) ≤ K := by rw [dist_comm]; exact hg a
    have h4 := hf.upper (g a) (g b)
    nlinarith [hg b,
      mul_nonneg (mul_nonneg hK0 (sub_nonneg.mpr hK)) (dist_nonneg (x := g a) (y := g b)),
      mul_nonneg (mul_nonneg hK0 hK0) (dist_nonneg (x := g a) (y := g b)),
      mul_nonneg hK0 (sub_nonneg.mpr (one_le_pow₀ hK (n := 3))), pow_nonneg hK0 4]
  · refine ⟨f x, ?_⟩
    have h1 := hf.lower (g (f x)) x
    have h2 : K * dist (f (g (f x))) (f x) ≤ K * K :=
      mul_le_mul_of_nonneg_left (hg (f x)) hK0
    nlinarith [sq_nonneg K]

/-! ### The assembly of a family of pieces -/

/-- The letter of an index word at a position, `0` past its end. -/
def letterAt (v : List ℕ) (i : ℕ) : ℕ := v.getD i 0

lemma letterAt_append_left {u : List ℕ} (t : List ℕ) {i : ℕ} (hi : i < u.length) :
    letterAt (u ++ t) i = letterAt u i := by
  rw [letterAt, letterAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi]

lemma letterAt_append_cons (u : List ℕ) (a : ℕ) (t : List ℕ) :
    letterAt (u ++ a :: t) u.length = a := by
  rw [letterAt, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

lemma letterAt_take {v : List ℕ} {i n : ℕ} (hi : i < n) : letterAt (v.take n) i = letterAt v i := by
  rw [letterAt, letterAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hi]

/-- The address at which the copy at `w` is planted: the copy at `w ++ [j]` hangs at the
root planted at the `j`-th port of the copy at `w`. -/
def pCopyAddr (σ : List ℕ → Piece) (w : List ℕ) : List ℕ :=
  (w.foldl (fun p j => (p.1 ++ [j], p.2 ++ (σ p.1).root j)) (([] : List ℕ), ([] : List ℕ))).2

lemma pCopyAddr_foldl_fst (σ : List ℕ → Piece) (w a b : List ℕ) :
    (w.foldl (fun p j => (p.1 ++ [j], p.2 ++ (σ p.1).root j)) (a, b)).1 = a ++ w := by
  induction w generalizing a b with
  | nil => simp
  | cons j t ih => simpa using ih (a ++ [j]) (b ++ (σ a).root j)

@[simp] lemma pCopyAddr_nil (σ : List ℕ → Piece) : pCopyAddr σ [] = [] := rfl

/-- The recursion of the assembly. -/
lemma pCopyAddr_concat (σ : List ℕ → Piece) (w : List ℕ) (j : ℕ) :
    pCopyAddr σ (w ++ [j]) = pCopyAddr σ w ++ (σ w).root j := by
  have h := pCopyAddr_foldl_fst σ w [] []
  rw [List.nil_append] at h
  simp only [pCopyAddr, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [h]

lemma pCopyAddr_prefix (σ : List ℕ → Piece) {w w' : List ℕ} (h : w <+: w') :
    pCopyAddr σ w <+: pCopyAddr σ w' := by
  obtain ⟨u, rfl⟩ := h
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j ih =>
      rw [← List.append_assoc]
      calc pCopyAddr σ w <+: pCopyAddr σ (w ++ u) := ih
        _ <+: pCopyAddr σ (w ++ u ++ [j]) := by
            rw [pCopyAddr_concat]
            exact List.prefix_append _ _

/-- **The neck length of a copy toward a letter**: the depth of the port the letter uses,
plus one for the edge into the planted child. -/
def pNeck (σ : List ℕ → Piece) (t : List ℕ) (a : ℕ) : ℕ := ((σ t).port a).length + 1

lemma one_le_pNeck (σ : List ℕ → Piece) (t : List ℕ) (a : ℕ) :
    (1 : ℝ) ≤ (pNeck σ t a : ℝ) := by
  rw [pNeck]; push_cast; linarith [(Nat.cast_nonneg ((σ t).port a).length : (0 : ℝ) ≤ _)]

/-- The depth of a copy is the total neck length of the copies above it, each toward the
letter the index word uses there. -/
lemma pCopyAddr_length (σ : List ℕ → Piece) (w : List ℕ) :
    (pCopyAddr σ w).length
      = ∑ i ∈ Finset.range w.length, pNeck σ (w.take i) (letterAt w i) := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w j ih =>
      have hcong : ∀ i ∈ Finset.range w.length,
          pNeck σ ((w ++ [j]).take i) (letterAt (w ++ [j]) i) = pNeck σ (w.take i) (letterAt w i) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [List.take_append_of_le_length (by omega), letterAt_append_left _ hi]
      rw [pCopyAddr_concat]
      simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
      rw [Finset.sum_congr rfl hcong, List.take_left, ← ih, letterAt_append_cons, Piece.root,
        List.length_append, List.length_singleton, pNeck]

/-- **The neck sum**: the total neck length of the copies strictly between `u` and `v`,
each toward the letter `v` uses there. -/
def pNeckSum (σ : List ℕ → Piece) (u v : List ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico (u.length + 1) v.length, pNeck σ (v.take i) (letterAt v i)

/-- The depth increment from a copy to a copy below it. -/
lemma pCopyAddr_length_of_prefix (σ : List ℕ → Piece) {u v : List ℕ} (huv : u <+: v)
    (hne : u ≠ v) :
    (pCopyAddr σ v).length
      = (pCopyAddr σ u).length + pNeck σ u (letterAt v u.length) + pNeckSum σ u v := by
  have hlt : u.length < v.length := by
    rcases huv.length_le.lt_or_eq with h | h
    · exact h
    · exact absurd (huv.eq_of_length h) hne
  have hu : u = v.take u.length := List.prefix_iff_eq_take.mp huv
  have hlow : ∀ i ∈ Finset.range u.length,
      pNeck σ (v.take i) (letterAt v i) = pNeck σ (u.take i) (letterAt u i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hu, List.take_take, Nat.min_eq_left hi.le, letterAt_take hi]
  have hsplit : ∑ i ∈ Finset.range v.length, pNeck σ (v.take i) (letterAt v i)
      = (∑ i ∈ Finset.range u.length, pNeck σ (v.take i) (letterAt v i))
        + ∑ i ∈ Finset.Ico u.length v.length, pNeck σ (v.take i) (letterAt v i) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) hlt.le]
  have hbot : ∑ i ∈ Finset.Ico u.length v.length, pNeck σ (v.take i) (letterAt v i)
      = pNeck σ u (letterAt v u.length) + pNeckSum σ u v := by
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt, ← hu]
    rfl
  rw [pCopyAddr_length, pCopyAddr_length, hsplit, hbot, Finset.sum_congr rfl hlow]
  omega

/-! ### The distance formulas at the level of addresses -/

/-- **The ancestor formula**, at the level of addresses: from an address of the copy at `u`
to an address of a copy strictly below it, through the port the index word uses at `u`. -/
lemma addrDist_pCopyAddr_anc (σ : List ℕ → Piece) {u : List ℕ} {a : ℕ} {t : List ℕ}
    (ha : a < (σ u).nports) {p : List ℕ} (hp : (σ u).mem p) (q : List ℕ) :
    addrDist (pCopyAddr σ u ++ p) (pCopyAddr σ (u ++ a :: t) ++ q)
      = addrDist p ((σ u).port a) + 1 + pNeckSum σ u (u ++ a :: t) + q.length := by
  have hne : u ≠ u ++ a :: t := by simp
  have hstep : pCopyAddr σ u ++ (σ u).root a <+: pCopyAddr σ (u ++ a :: t) := by
    rw [← pCopyAddr_concat]
    exact pCopyAddr_prefix σ ⟨t, by simp⟩
  obtain ⟨r, hr⟩ := hstep
  have hcode : pCopyAddr σ (u ++ a :: t) ++ q
      = pCopyAddr σ u ++ ((σ u).root a ++ (r ++ q)) := by
    rw [← hr]; simp only [List.append_assoc]
  have hw : wedgeN (pCopyAddr σ u ++ p) (pCopyAddr σ u ++ ((σ u).root a ++ (r ++ q)))
      = pCopyAddr σ u ++ wedgeN p ((σ u).port a) := by
    rw [wedgeN_append_append, (σ u).wedgeN_eq_wedgeN_port ha hp (List.prefix_append _ _)]
  have h1 := addrDist_add_wedgeN_length (pCopyAddr σ u ++ p)
    (pCopyAddr σ u ++ ((σ u).root a ++ (r ++ q)))
  rw [hw] at h1
  have h2 := addrDist_add_wedgeN_length p ((σ u).port a)
  have hrlen := congrArg List.length hr
  have hroot : ((σ u).root a).length = ((σ u).port a).length + 1 := by
    simp [Piece.root]
  simp only [List.length_append] at hrlen
  have hlen := pCopyAddr_length_of_prefix σ (u := u) (v := u ++ a :: t) ⟨a :: t, rfl⟩ hne
  rw [letterAt_append_cons, pNeck] at hlen
  rw [hcode]
  simp only [List.length_append] at h1
  omega

/-- **The divergent formula**, at the level of addresses: from an address of the copy at
`z ++ a :: s` to one of the copy at `z ++ b :: t`, `a ≠ b`, the two branches climb to the
entries of their copies, traverse the intermediate copies, and meet in the copy at `z`,
between the two ports the letters `a` and `b` use. -/
lemma addrDist_pCopyAddr_div (σ : List ℕ → Piece) {z : List ℕ} {a b : ℕ} {s t : List ℕ}
    (hab : a ≠ b) (ha : a < (σ z).nports) (hb : b < (σ z).nports) (p q : List ℕ) :
    addrDist (pCopyAddr σ (z ++ a :: s) ++ p) (pCopyAddr σ (z ++ b :: t) ++ q)
      = p.length + q.length + 2 + pNeckSum σ z (z ++ a :: s) + pNeckSum σ z (z ++ b :: t)
        + addrDist ((σ z).port a) ((σ z).port b) := by
  have hzu : z <+: z ++ a :: s := ⟨a :: s, rfl⟩
  have hzv : z <+: z ++ b :: t := ⟨b :: t, rfl⟩
  have hzune : z ≠ z ++ a :: s := by simp
  have hzvne : z ≠ z ++ b :: t := by simp
  have hpu : pCopyAddr σ z ++ (σ z).root a <+: pCopyAddr σ (z ++ a :: s) := by
    rw [← pCopyAddr_concat]
    exact pCopyAddr_prefix σ ⟨s, by simp⟩
  have hpv : pCopyAddr σ z ++ (σ z).root b <+: pCopyAddr σ (z ++ b :: t) := by
    rw [← pCopyAddr_concat]
    exact pCopyAddr_prefix σ ⟨t, by simp⟩
  obtain ⟨r, hr⟩ := hpu
  obtain ⟨r', hr'⟩ := hpv
  have hcu : pCopyAddr σ (z ++ a :: s) ++ p = pCopyAddr σ z ++ ((σ z).root a ++ (r ++ p)) := by
    rw [← hr]; simp only [List.append_assoc]
  have hcv : pCopyAddr σ (z ++ b :: t) ++ q = pCopyAddr σ z ++ ((σ z).root b ++ (r' ++ q)) := by
    rw [← hr']; simp only [List.append_assoc]
  have hw : wedgeN (pCopyAddr σ (z ++ a :: s) ++ p) (pCopyAddr σ (z ++ b :: t) ++ q)
      = pCopyAddr σ z ++ wedgeN ((σ z).port a) ((σ z).port b) := by
    rw [hcu, hcv, wedgeN_append_append,
      (σ z).wedgeN_root_root ha hb hab (List.prefix_append _ _) (List.prefix_append _ _)]
  have h1 := addrDist_add_wedgeN_length (pCopyAddr σ (z ++ a :: s) ++ p)
    (pCopyAddr σ (z ++ b :: t) ++ q)
  rw [hw] at h1
  have h2 := addrDist_add_wedgeN_length ((σ z).port a) ((σ z).port b)
  have hlenu := pCopyAddr_length_of_prefix σ hzu hzune
  have hlenv := pCopyAddr_length_of_prefix σ hzv hzvne
  rw [letterAt_append_cons, pNeck] at hlenu hlenv
  simp only [List.length_append] at h1
  omega

/-! ### The assembly as a metric space -/

/-- **An index set for a family of pieces**: a set of index words in which the child
`w ++ [j]` is indexed only when `w` is and `j` is below the port count of the piece at
`w`. -/
def PIdx (σ : List ℕ → Piece) (Idx : List ℕ → Prop) : Prop :=
  ∀ w j, Idx (w ++ [j]) → Idx w ∧ j < (σ w).nports

lemma PIdx.of_prefix {σ : List ℕ → Piece} {Idx : List ℕ → Prop} (hI : PIdx σ Idx) :
    ∀ {u v : List ℕ}, u <+: v → Idx v → Idx u := by
  intro u v huv hv
  obtain ⟨s, rfl⟩ := huv
  induction s using List.reverseRecOn with
  | nil => simpa using hv
  | append_singleton s j ih =>
      rw [← List.append_assoc] at hv
      exact ih (hI _ _ hv).1

lemma PIdx.letter_lt {σ : List ℕ → Piece} {Idx : List ℕ → Prop} (hI : PIdx σ Idx)
    {u : List ℕ} {a : ℕ} {t : List ℕ} (hv : Idx (u ++ a :: t)) : a < (σ u).nports :=
  (hI u a (hI.of_prefix ⟨t, by simp⟩ hv)).2

/-- **The assembly of a family of pieces over an index set**: a vertex is an address of the
piece at an index word `w`, tagged by `w`. -/
structure PAssembly (σ : List ℕ → Piece) (Idx : List ℕ → Prop) (hI : PIdx σ Idx) where
  /-- The word naming the copy. -/
  copy : List ℕ
  /-- The word is indexed. -/
  idx : Idx copy
  /-- The address inside the piece at that copy. -/
  vert : (σ copy).carrier

namespace PAssembly

variable {σ : List ℕ → Piece} {Idx : List ℕ → Prop} {hI : PIdx σ Idx}

/-- The address of a vertex of the assembly in the ambient tree. -/
def code (x : PAssembly σ Idx hI) : List ℕ := pCopyAddr σ x.copy ++ x.vert.1

lemma vert_eq : ∀ {x y : PAssembly σ Idx hI}, x.copy = y.copy → x.vert.1 = y.vert.1 → x = y := by
  rintro ⟨u, hu, p, hp⟩ ⟨v, hv, q, hq⟩ h1 h2
  simp only at h1 h2
  subst h1
  subst h2
  rfl

/-- The three relative positions of two index words, the divergent one with its first
divergence. -/
lemma copy_cases (u v : List ℕ) :
    u = v ∨ (∃ a t, v = u ++ a :: t) ∨ (∃ a t, u = v ++ a :: t)
      ∨ ∃ z a b s t, a ≠ b ∧ u = z ++ a :: s ∧ v = z ++ b :: t := by
  by_cases h1 : u <+: v
  · obtain ⟨s, rfl⟩ := h1
    cases s with
    | nil => exact Or.inl (by simp)
    | cons a t => exact Or.inr (Or.inl ⟨a, t, rfl⟩)
  · by_cases h2 : v <+: u
    · obtain ⟨s, rfl⟩ := h2
      cases s with
      | nil => exact absurd (by simp) h1
      | cons a t => exact Or.inr (Or.inr (Or.inl ⟨a, t, rfl⟩))
    · obtain ⟨z, a, b, hab, ⟨s, rfl⟩, ⟨t, rfl⟩⟩ := exists_divergeN h1 h2
      exact Or.inr (Or.inr (Or.inr ⟨z, a, b, s, t, hab, by simp, by simp⟩))

/-- Distinct vertices carry distinct addresses. -/
lemma code_injective : Function.Injective (code (σ := σ) (Idx := Idx) (hI := hI)) := by
  rintro ⟨u, hu, p⟩ ⟨v, hv, q⟩ h
  simp only [code] at h
  have h0 : addrDist (pCopyAddr σ u ++ p.1) (pCopyAddr σ v ++ q.1) = 0 :=
    addrDist_eq_zero_iff.mpr h
  rcases copy_cases u v with rfl | ⟨a, t, rfl⟩ | ⟨a, t, rfl⟩ | ⟨z, a, b, s, t, hab, rfl, rfl⟩
  · refine vert_eq rfl ?_
    rw [addrDist_append_append] at h0
    exact addrDist_eq_zero_iff.mp h0
  · rw [addrDist_pCopyAddr_anc σ (hI.letter_lt hv) p.2] at h0
    omega
  · rw [addrDist_comm, addrDist_pCopyAddr_anc σ (hI.letter_lt hu) q.2] at h0
    omega
  · rw [addrDist_pCopyAddr_div σ hab (hI.letter_lt hu) (hI.letter_lt hv)] at h0
    omega

/-- The metric of the assembly, the address metric through the codes. -/
noncomputable instance instMetricSpace (σ : List ℕ → Piece) (Idx : List ℕ → Prop)
    (hI : PIdx σ Idx) : MetricSpace (PAssembly σ Idx hI) where
  dist x y := (addrDist (code x) (code y) : ℝ)
  dist_self x := by simp
  dist_comm x y := by simp only [addrDist_comm (code x) (code y)]
  dist_triangle x y z := by
    have := addrDist_triangle (code x) (code y) (code z)
    exact_mod_cast this
  eq_of_dist_eq_zero {x y} h := by
    have h0 : ((addrDist (code x) (code y) : ℕ) : ℝ) = 0 := h
    exact code_injective (addrDist_eq_zero_iff.mp (Nat.cast_eq_zero.mp h0))

@[simp] lemma dist_code (x y : PAssembly σ Idx hI) :
    dist x y = (addrDist (code x) (code y) : ℝ) := rfl

/-! ### The distance formulas -/

/-- The entry-to-port distance of a piece is the depth of the port. -/
lemma dist_entry_port (X : Piece) (j : ℕ) :
    dist X.entry (X.portVert j) = ((X.port j).length : ℝ) := by
  rw [Piece.dist_carrier, Piece.entry_val, Piece.portVert_val, addrDist_nil_left]

/-- The neck length toward a letter, read in the piece. -/
lemma pNeck_eq (σ : List ℕ → Piece) (t : List ℕ) (a : ℕ) :
    (pNeck σ t a : ℝ) = dist (σ t).entry ((σ t).portVert a) + 1 := by
  rw [pNeck, dist_entry_port]; push_cast; ring

/-- **Inside one copy** the distance is the distance of the piece. -/
theorem dist_same (u : List ℕ) (hu : Idx u) (p q : (σ u).carrier) :
    dist (⟨u, hu, p⟩ : PAssembly σ Idx hI) ⟨u, hu, q⟩ = dist p q := by
  simp only [dist_code, code, Piece.dist_carrier, addrDist_append_append]

/-- **The ancestor formula**: for `x` in the copy at `u` and `y` in the copy at
`u ++ a :: t`, the distance is the distance of `x` to the `a`-th port of its copy, plus
the distance of `y` to the entry of its copy, plus one, plus the neck sum of the copies
strictly between. -/
theorem dist_anc {u : List ℕ} {a : ℕ} {t : List ℕ} (hu : Idx u)
    (hv : Idx (u ++ a :: t)) (p : (σ u).carrier) (q : (σ (u ++ a :: t)).carrier) :
    dist (⟨u, hu, p⟩ : PAssembly σ Idx hI) ⟨u ++ a :: t, hv, q⟩
      = dist p ((σ u).portVert a) + dist q (σ (u ++ a :: t)).entry + 1
        + ∑ i ∈ Finset.Ico (u.length + 1) (u ++ a :: t).length,
            (pNeck σ ((u ++ a :: t).take i) (letterAt (u ++ a :: t) i) : ℝ) := by
  simp only [dist_code, code, Piece.dist_carrier, Piece.entry_val, Piece.portVert_val]
  rw [addrDist_pCopyAddr_anc σ (hI.letter_lt hv) p.2]
  simp only [pNeckSum, addrDist_nil_right]
  push_cast
  ring

/-- **The divergent formula**: for `x` in the copy at `z ++ a :: s` and `y` in the copy
at `z ++ b :: t`, `a ≠ b`, the distance is the two distances to the entries, plus two,
plus the two neck sums, plus the distance between the two ports of the copy at `z` the
branches leave through. -/
theorem dist_div {z : List ℕ} {a b : ℕ} {s t : List ℕ} (hab : a ≠ b)
    (hu : Idx (z ++ a :: s)) (hv : Idx (z ++ b :: t))
    (p : (σ (z ++ a :: s)).carrier) (q : (σ (z ++ b :: t)).carrier) :
    dist (⟨z ++ a :: s, hu, p⟩ : PAssembly σ Idx hI) ⟨z ++ b :: t, hv, q⟩
      = dist p (σ (z ++ a :: s)).entry + dist q (σ (z ++ b :: t)).entry + 2
        + (∑ i ∈ Finset.Ico (z.length + 1) (z ++ a :: s).length,
              (pNeck σ ((z ++ a :: s).take i) (letterAt (z ++ a :: s) i) : ℝ)
          + ∑ i ∈ Finset.Ico (z.length + 1) (z ++ b :: t).length,
              (pNeck σ ((z ++ b :: t).take i) (letterAt (z ++ b :: t) i) : ℝ))
        + dist ((σ z).portVert a) ((σ z).portVert b) := by
  simp only [dist_code, code, Piece.dist_carrier, Piece.entry_val, Piece.portVert_val]
  rw [addrDist_pCopyAddr_div σ hab (hI.letter_lt hu) (hI.letter_lt hv)]
  simp only [pNeckSum, addrDist_nil_right]
  push_cast
  ring

end PAssembly

/-! ### The glued transfer over pieces -/

/-- **The comparison off one copy, with the port term.**  Both distance formulas of the
assembly of pieces decompose the distance into two mark distances, a constant, a neck sum
and a port distance; the glued map transfers each group, and all constants fit `8K²`. -/
theorem blob_glued_dist_bounds {K A B N P A' B' N' P' e d d' : ℝ} (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 ≤ N) (hP : 0 ≤ P) (hA' : 0 ≤ A') (hB' : 0 ≤ B')
    (_hN' : 0 ≤ N') (hP' : 0 ≤ P') (he : 0 ≤ e)
    (hAup : A' ≤ K * A + 2 * K) (hAlo : A ≤ K * A' + 2 * K ^ 2)
    (hBup : B' ≤ K * B + 2 * K) (hBlo : B ≤ K * B' + 2 * K ^ 2)
    (hNup : N' ≤ 4 * K * N) (hNlo : N ≤ 8 * K ^ 2 * N')
    (hPup : P' ≤ K * P + 3 * K) (hPlo : P ≤ K * P' + 3 * K ^ 2)
    (hd : d = A + B + e + N + P) (hd' : d' = A' + B' + e + N' + P') :
    d' ≤ 8 * K ^ 2 * d + 8 * K ^ 2 ∧ d ≤ 8 * K ^ 2 * d' + (8 * K ^ 2) ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := zero_le_one.trans hK
  have hKL : K ≤ 8 * K ^ 2 := by nlinarith
  have h4KL : 4 * K ≤ 8 * K ^ 2 := by nlinarith
  have h1L : (1 : ℝ) ≤ 8 * K ^ 2 := by nlinarith
  subst hd hd'
  constructor
  · have e1 : K * A ≤ 8 * K ^ 2 * A := mul_le_mul_of_nonneg_right hKL hA
    have e2 : K * B ≤ 8 * K ^ 2 * B := mul_le_mul_of_nonneg_right hKL hB
    have e3 : 4 * K * N ≤ 8 * K ^ 2 * N := mul_le_mul_of_nonneg_right h4KL hN
    have e5 : K * P ≤ 8 * K ^ 2 * P := mul_le_mul_of_nonneg_right hKL hP
    have e4 : e ≤ 8 * K ^ 2 * e := by nlinarith
    nlinarith
  · have e1 : K * A' ≤ 8 * K ^ 2 * A' := mul_le_mul_of_nonneg_right hKL hA'
    have e2 : K * B' ≤ 8 * K ^ 2 * B' := mul_le_mul_of_nonneg_right hKL hB'
    have e5 : K * P' ≤ 8 * K ^ 2 * P' := mul_le_mul_of_nonneg_right hKL hP'
    have e4 : e ≤ 8 * K ^ 2 * e := by nlinarith
    have e6 : 7 * K ^ 2 ≤ (8 * K ^ 2) ^ 2 := by nlinarith
    nlinarith

/-- The port comparison of a port quasi-isometry: the distance between two ports of the
target is controlled by the distance between the corresponding ports of the source. -/
lemma port_dist_bounds {K : ℝ} (hK : 0 ≤ K) {X Y : PortSpace} {f : X.carrier → Y.carrier}
    (hf : IsPortQI K X Y f) (a b : ℕ) :
    dist (Y.port a) (Y.port b) ≤ K * dist (X.port a) (X.port b) + 3 * K
      ∧ dist (X.port a) (X.port b) ≤ K * dist (Y.port a) (Y.port b) + 3 * K ^ 2 := by
  have ha : dist (Y.port a) (f (X.port a)) ≤ K := by rw [dist_comm]; exact hf.port a
  have hb : dist (f (X.port b)) (Y.port b) ≤ K := hf.port b
  constructor
  · have htri : dist (Y.port a) (Y.port b)
        ≤ dist (Y.port a) (f (X.port a)) + dist (f (X.port a)) (f (X.port b))
          + dist (f (X.port b)) (Y.port b) := dist_triangle4 _ _ _ _
    have hmid := hf.upper (X.port a) (X.port b)
    linarith
  · have htri : dist (f (X.port a)) (f (X.port b))
        ≤ dist (f (X.port a)) (Y.port a) + dist (Y.port a) (Y.port b)
          + dist (Y.port b) (f (X.port b)) := dist_triangle4 _ _ _ _
    have h1 : dist (f (X.port a)) (Y.port a) ≤ K := hf.port a
    have h2 : dist (Y.port b) (f (X.port b)) ≤ K := by rw [dist_comm]; exact hf.port b
    have hlow := hf.lower (X.port a) (X.port b)
    have hmul : K * dist (f (X.port a)) (f (X.port b))
        ≤ K * (dist (Y.port a) (Y.port b) + 2 * K) := by
      refine mul_le_mul_of_nonneg_left ?_ hK
      linarith
    nlinarith

namespace PAssembly

variable {σ σ' : List ℕ → Piece} {Idx : List ℕ → Prop} {hI : PIdx σ Idx} {hI' : PIdx σ' Idx}

/-- **The glued map**: the per-piece maps, copy by copy. -/
def glue (φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier) (x : PAssembly σ Idx hI) :
    PAssembly σ' Idx hI' := ⟨x.copy, x.idx, φ x.copy x.vert⟩

/-- The neck sums compare termwise through the port quasi-isometries, the neck of an
intermediate copy being read toward the port the index word uses there. -/
lemma neckSum_bounds (hI : PIdx σ Idx) {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier}
    (hφ : ∀ w, Idx w → IsPortQI K (σ w).space (σ' w).space (φ w)) (a b : ℕ) {v : List ℕ}
    (hv : Idx v) :
    (∑ i ∈ Finset.Ico a b, (pNeck σ (v.take i) (letterAt v i) : ℝ))
        ≤ 8 * K ^ 2 * ∑ i ∈ Finset.Ico a b, (pNeck σ' (v.take i) (letterAt v i) : ℝ)
      ∧ (∑ i ∈ Finset.Ico a b, (pNeck σ' (v.take i) (letterAt v i) : ℝ))
        ≤ 4 * K * ∑ i ∈ Finset.Ico a b, (pNeck σ (v.take i) (letterAt v i) : ℝ) := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hidx : ∀ i, Idx (v.take i) := fun i => hI.of_prefix (List.take_prefix i v) hv
  refine neck_sum_bounds _ hK (fun i _ => ?_) (fun i _ => ?_) (fun i _ => ?_) (fun i _ => ?_)
  · exact one_le_pNeck _ _ _
  · exact one_le_pNeck _ _ _
  · have h := (neck_le_of_markedQI hK0 ((hφ _ (hidx i)).toMarked (letterAt v i))).1
    rw [pNeck_eq, pNeck_eq]
    change dist (σ' (v.take i)).entry ((σ' (v.take i)).portVert (letterAt v i))
      ≤ K * dist (σ (v.take i)).entry ((σ (v.take i)).portVert (letterAt v i)) + 3 * K at h
    linarith
  · have h := (neck_le_of_markedQI hK0 ((hφ _ (hidx i)).toMarked (letterAt v i))).2
    rw [pNeck_eq, pNeck_eq]
    change dist (σ (v.take i)).entry ((σ (v.take i)).portVert (letterAt v i))
      ≤ K * dist (σ' (v.take i)).entry ((σ' (v.take i)).portVert (letterAt v i)) + 3 * K ^ 2 at h
    linarith

/-- The glued transfer in the ancestor position. -/
theorem glue_dist_bounds_anc {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier}
    (hφ : ∀ w, Idx w → IsPortQI K (σ w).space (σ' w).space (φ w))
    {u : List ℕ} {a : ℕ} {t : List ℕ} (hu : Idx u) (hv : Idx (u ++ a :: t))
    (p : (σ u).carrier) (q : (σ (u ++ a :: t)).carrier) :
    dist (glue (hI := hI) (hI' := hI') φ (⟨u, hu, p⟩ : PAssembly σ Idx hI)) (glue (hI := hI) (hI' := hI') φ ⟨u ++ a :: t, hv, q⟩)
          ≤ 8 * K ^ 2 * dist (⟨u, hu, p⟩ : PAssembly σ Idx hI) ⟨u ++ a :: t, hv, q⟩ + 8 * K ^ 2
      ∧ dist (⟨u, hu, p⟩ : PAssembly σ Idx hI) ⟨u ++ a :: t, hv, q⟩
          ≤ 8 * K ^ 2 * dist (glue (hI := hI) (hI' := hI') φ (⟨u, hu, p⟩ : PAssembly σ Idx hI))
              (glue (hI := hI) (hI' := hI') φ ⟨u ++ a :: t, hv, q⟩) + (8 * K ^ 2) ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hA : dist (φ u p) ((σ' u).portVert a) ≤ K * dist p ((σ u).portVert a) + 2 * K
      ∧ dist p ((σ u).portVert a) ≤ K * dist (φ u p) ((σ' u).portVert a) + 2 * K ^ 2 :=
    dist_mark_bounds hK0 ((hφ u hu).toMarked a) ((hφ u hu).port a) p
  have hB : dist (φ _ q) (σ' (u ++ a :: t)).entry ≤ K * dist q (σ (u ++ a :: t)).entry + 2 * K
      ∧ dist q (σ (u ++ a :: t)).entry
        ≤ K * dist (φ _ q) (σ' (u ++ a :: t)).entry + 2 * K ^ 2 :=
    dist_mark_bounds hK0 ((hφ _ hv).toMarked 0) (hφ _ hv).entry q
  have hN := neckSum_bounds hI hK hφ (u.length + 1) (u ++ a :: t).length hv
  exact blob_glued_dist_bounds hK dist_nonneg dist_nonneg
    (Finset.sum_nonneg fun i _ => by positivity) le_rfl dist_nonneg dist_nonneg
    (Finset.sum_nonneg fun i _ => by positivity) le_rfl zero_le_one
    hA.1 hA.2 hB.1 hB.2 hN.2 hN.1 (by linarith) (by nlinarith)
    (by rw [dist_anc hu hv p q]; ring)
    (by rw [glue, glue, dist_anc hu hv (φ u p) (φ _ q)]; ring)

/-- The glued transfer in the divergent position. -/
theorem glue_dist_bounds_div {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier}
    (hφ : ∀ w, Idx w → IsPortQI K (σ w).space (σ' w).space (φ w))
    {z : List ℕ} {a b : ℕ} {s t : List ℕ} (hab : a ≠ b) (hu : Idx (z ++ a :: s))
    (hv : Idx (z ++ b :: t)) (p : (σ (z ++ a :: s)).carrier) (q : (σ (z ++ b :: t)).carrier) :
    dist (glue (hI := hI) (hI' := hI') φ (⟨z ++ a :: s, hu, p⟩ : PAssembly σ Idx hI))
        (glue (hI := hI) (hI' := hI') φ ⟨z ++ b :: t, hv, q⟩)
          ≤ 8 * K ^ 2 * dist (⟨z ++ a :: s, hu, p⟩ : PAssembly σ Idx hI) ⟨z ++ b :: t, hv, q⟩
            + 8 * K ^ 2
      ∧ dist (⟨z ++ a :: s, hu, p⟩ : PAssembly σ Idx hI) ⟨z ++ b :: t, hv, q⟩
          ≤ 8 * K ^ 2 * dist (glue (hI := hI) (hI' := hI') φ (⟨z ++ a :: s, hu, p⟩ : PAssembly σ Idx hI))
              (glue (hI := hI) (hI' := hI') φ ⟨z ++ b :: t, hv, q⟩) + (8 * K ^ 2) ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hz : Idx z := hI.of_prefix ⟨a :: s, rfl⟩ hu
  have hA : dist (φ _ p) (σ' (z ++ a :: s)).entry ≤ K * dist p (σ (z ++ a :: s)).entry + 2 * K
      ∧ dist p (σ (z ++ a :: s)).entry
        ≤ K * dist (φ _ p) (σ' (z ++ a :: s)).entry + 2 * K ^ 2 :=
    dist_mark_bounds hK0 ((hφ _ hu).toMarked 0) (hφ _ hu).entry p
  have hB : dist (φ _ q) (σ' (z ++ b :: t)).entry ≤ K * dist q (σ (z ++ b :: t)).entry + 2 * K
      ∧ dist q (σ (z ++ b :: t)).entry
        ≤ K * dist (φ _ q) (σ' (z ++ b :: t)).entry + 2 * K ^ 2 :=
    dist_mark_bounds hK0 ((hφ _ hv).toMarked 0) (hφ _ hv).entry q
  have hNu := neckSum_bounds hI hK hφ (z.length + 1) (z ++ a :: s).length hu
  have hNv := neckSum_bounds hI hK hφ (z.length + 1) (z ++ b :: t).length hv
  have hP : dist ((σ' z).portVert a) ((σ' z).portVert b)
        ≤ K * dist ((σ z).portVert a) ((σ z).portVert b) + 3 * K
      ∧ dist ((σ z).portVert a) ((σ z).portVert b)
        ≤ K * dist ((σ' z).portVert a) ((σ' z).portVert b) + 3 * K ^ 2 :=
    port_dist_bounds hK0 (hφ z hz) a b
  have hdu := dist_div (hI := hI) hab hu hv p q
  have hdu' := dist_div (hI := hI') hab hu hv (φ _ p) (φ _ q)
  refine blob_glued_dist_bounds hK dist_nonneg dist_nonneg ?_ dist_nonneg
    dist_nonneg dist_nonneg ?_ dist_nonneg (by norm_num)
    hA.1 hA.2 hB.1 hB.2 ?_ ?_ hP.1 hP.2 hdu hdu'
  · positivity
  · positivity
  · have h1 := hNu.2
    have h2 := hNv.2
    linarith
  · have h1 := hNu.1
    have h2 := hNv.1
    linarith

/-- Coarse density of the glued map, copy by copy. -/
lemma glue_dense {K : ℝ} {φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier}
    (hφ : ∀ w, Idx w → IsPortQI K (σ w).space (σ' w).space (φ w)) (y : PAssembly σ' Idx hI') :
    ∃ x : PAssembly σ Idx hI, dist (glue φ x) y ≤ K := by
  obtain ⟨w, hw, r⟩ := y
  obtain ⟨a, ha⟩ := (hφ w hw).dense r
  refine ⟨⟨w, hw, a⟩, ?_⟩
  have h : dist (glue φ (⟨w, hw, a⟩ : PAssembly σ Idx hI)) (⟨w, hw, r⟩ : PAssembly σ' Idx hI')
      = dist (φ w a) r := dist_same w hw _ _
  rw [h]
  exact ha

/-- **The glued transfer over pieces** (**`it:general-glued`** with several ports): two
families of pieces that are `K`-port comparable copy by copy over a common index set
have `8K²`-quasi-isometric assemblies, the glued map being the per-piece maps read copy by
copy. -/
theorem glued_transfer (hI : PIdx σ Idx) (hI' : PIdx σ' Idx) {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier}
    (hφ : ∀ w, Idx w → IsPortQI K (σ w).space (σ' w).space (φ w)) :
    (∀ x y : PAssembly σ Idx hI,
        dist (glue (hI := hI) (hI' := hI') φ x) (glue φ y) ≤ 8 * K ^ 2 * dist x y + 8 * K ^ 2)
      ∧ (∀ x y : PAssembly σ Idx hI, dist x y
          ≤ 8 * K ^ 2 * dist (glue (hI := hI) (hI' := hI') φ x) (glue φ y) + (8 * K ^ 2) ^ 2)
      ∧ ∀ y : PAssembly σ' Idx hI', ∃ x : PAssembly σ Idx hI, dist (glue φ x) y ≤ 8 * K ^ 2 := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have key : ∀ x y : PAssembly σ Idx hI,
      dist (glue (hI := hI) (hI' := hI') φ x) (glue φ y) ≤ 8 * K ^ 2 * dist x y + 8 * K ^ 2
        ∧ dist x y ≤ 8 * K ^ 2 * dist (glue (hI := hI) (hI' := hI') φ x) (glue φ y) + (8 * K ^ 2) ^ 2 := by
    rintro ⟨u, hu, p⟩ ⟨v, hv, q⟩
    rcases copy_cases u v with rfl | ⟨a, t, rfl⟩ | ⟨a, t, rfl⟩ | ⟨z, a, b, s, t, hab, rfl, rfl⟩
    · have e1 : dist (glue (hI := hI) (hI' := hI') φ (⟨u, hu, p⟩ : PAssembly σ Idx hI)) (glue (hI := hI) (hI' := hI') φ ⟨u, hv, q⟩)
          = dist (φ u p) (φ u q) := dist_same u hu _ _
      have e2 : dist (⟨u, hu, p⟩ : PAssembly σ Idx hI) ⟨u, hv, q⟩ = dist p q :=
        dist_same u hu p q
      rw [e1, e2]
      refine glued_dist_same hK dist_nonneg dist_nonneg ((hφ u hu).upper p q) ?_
      rw [pow_two]
      exact (hφ u hu).lower p q
    · exact glue_dist_bounds_anc hK hφ hu hv p q
    · obtain ⟨h1, h2⟩ := glue_dist_bounds_anc (hI' := hI') hK hφ hv hu q p
      rw [dist_comm (glue (hI := hI) (hI' := hI') φ (⟨v ++ a :: t, hu, p⟩ : PAssembly σ Idx hI)),
        dist_comm (⟨v ++ a :: t, hu, p⟩ : PAssembly σ Idx hI)]
      exact ⟨h1, h2⟩
    · exact glue_dist_bounds_div hK hφ hab hu hv p q
  refine ⟨fun x y => (key x y).1, fun x y => (key x y).2, fun y => ?_⟩
  obtain ⟨x, hx⟩ := glue_dense hφ y
  exact ⟨x, hx.trans (by nlinarith)⟩

/-- The glued transfer as a quasi-isometry in the sense of `IsQIMap`. -/
theorem glue_isQIMap (hI : PIdx σ Idx) (hI' : PIdx σ' Idx) {K : ℝ} (hK : 1 ≤ K)
    {φ : ∀ w : List ℕ, (σ w).carrier → (σ' w).carrier}
    (hφ : ∀ w, Idx w → IsPortQI K (σ w).space (σ' w).space (φ w)) :
    IsQIMap (8 * K ^ 2) (glue (hI := hI) (hI' := hI') φ) :=
  ⟨(glued_transfer hI hI' hK hφ).1, (glued_transfer hI hI' hK hφ).2.1,
    (glued_transfer hI hI' hK hφ).2.2⟩

end PAssembly

/-! ### The flat configuration -/

/-- The address `n` steps down the neck: `n` zeros. -/
def pRep (n : ℕ) : List ℕ := List.replicate n 0

@[simp] lemma pRep_zero : pRep 0 = [] := rfl

@[simp] lemma pRep_length (n : ℕ) : (pRep n).length = n := by simp [pRep]

lemma pRep_prefix_pRep {i n : ℕ} (h : i ≤ n) : pRep i <+: pRep n := by
  rw [pRep, pRep, List.prefix_replicate_iff]
  simp [h]

/-- A prefix of the neck is a neck vertex. -/
lemma eq_pRep_of_prefix {p : List ℕ} {n : ℕ} (h : p <+: pRep n) : p = pRep p.length := by
  rw [pRep, List.prefix_replicate_iff] at h
  exact h.2

/-- **The flat configuration**: a bare neck of `n` edges with `k` ports at its far end,
the `j`-th port planting at the child `j` of the far end. -/
def flatPiece (n k : ℕ) : Piece where
  mem p := p <+: pRep n
  nil_mem := List.nil_prefix
  mem_of_prefix := fun h1 h2 => h1.trans h2
  ports := (List.range k).map fun j => (pRep n, j)
  port_mem := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact List.prefix_refl _
  slot_free := by
    intro x hx h
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    have := h.length_le
    simp at this
  ports_nodup := by
    refine List.Nodup.map_on (fun a _ b _ h => ?_) List.nodup_range
    simpa using h

@[simp] lemma flatPiece_mem (n k : ℕ) (p : List ℕ) : (flatPiece n k).mem p ↔ p <+: pRep n :=
  Iff.rfl

@[simp] lemma flatPiece_nports (n k : ℕ) : (flatPiece n k).nports = k := by
  simp [Piece.nports, flatPiece]

lemma flatPiece_portSlot_of_lt {n k j : ℕ} (hj : j < k) :
    (flatPiece n k).portSlot j = (pRep n, j) := by
  rw [Piece.portSlot, List.getD_eq_getElem _ _ (by simp [flatPiece, hj])]
  simp [flatPiece]

lemma flatPiece_port_of_lt {n k j : ℕ} (hj : j < k) : (flatPiece n k).port j = pRep n := by
  rw [Piece.port, flatPiece_portSlot_of_lt hj]

lemma flatPiece_slot_of_lt {n k j : ℕ} (hj : j < k) : (flatPiece n k).slot j = j := by
  rw [Piece.slot, flatPiece_portSlot_of_lt hj]

lemma flatPiece_port_of_le {n k j : ℕ} (hj : k ≤ j) : (flatPiece n k).port j = [] := by
  rw [Piece.port, Piece.portSlot_of_le (by simpa using hj)]

lemma flatPiece_root_of_lt {n k j : ℕ} (hj : j < k) :
    (flatPiece n k).root j = pRep n ++ [j] := by
  rw [Piece.root, flatPiece_port_of_lt hj, flatPiece_slot_of_lt hj]

/-- The collapse onto the far end of the neck, on addresses. -/
def collapseAddr (n : ℕ) (p : List ℕ) : List ℕ := if pRep n <+: p then pRep n else p

lemma collapseAddr_of_prefix {n : ℕ} {p : List ℕ} (h : pRep n <+: p) :
    collapseAddr n p = pRep n := if_pos h

lemma collapseAddr_of_not_prefix {n : ℕ} {p : List ℕ} (h : ¬ pRep n <+: p) :
    collapseAddr n p = p := if_neg h

/-- The collapse does not increase distances. -/
lemma addrDist_collapseAddr_le {n : ℕ} {p q : List ℕ} (hp : p <+: pRep n ∨ pRep n <+: p)
    (hq : q <+: pRep n ∨ pRep n <+: q) :
    addrDist (collapseAddr n p) (collapseAddr n q) ≤ addrDist p q := by
  by_cases h1 : pRep n <+: p
  · by_cases h2 : pRep n <+: q
    · rw [collapseAddr_of_prefix h1, collapseAddr_of_prefix h2, addrDist_self]
      exact Nat.zero_le _
    · have hq' : q <+: pRep n := hq.resolve_right h2
      have e1 : addrDist (pRep n) q = n - q.length := by
        rw [addrDist_comm, addrDist_of_prefix hq', pRep_length]
      have e2 : addrDist p q = p.length - q.length := by
        rw [addrDist_comm, addrDist_of_prefix (hq'.trans h1)]
      have := h1.length_le
      rw [collapseAddr_of_prefix h1, collapseAddr_of_not_prefix h2, e1, e2]
      simp only [pRep_length] at this
      omega
  · by_cases h2 : pRep n <+: q
    · have hp' : p <+: pRep n := hp.resolve_right h1
      have e1 : addrDist p (pRep n) = n - p.length := by
        rw [addrDist_of_prefix hp', pRep_length]
      have e2 : addrDist p q = q.length - p.length := by
        rw [addrDist_of_prefix (hp'.trans h2)]
      have := h2.length_le
      rw [collapseAddr_of_not_prefix h1, collapseAddr_of_prefix h2, e1, e2]
      simp only [pRep_length] at this
      omega
    · rw [collapseAddr_of_not_prefix h1, collapseAddr_of_not_prefix h2]

/-- The collapse loses at most twice the depth below the far end. -/
lemma addrDist_le_collapseAddr {n Δ : ℕ} {p q : List ℕ} (hp : p <+: pRep n ∨ pRep n <+: p)
    (hq : q <+: pRep n ∨ pRep n <+: q) (hpd : pRep n <+: p → p.length ≤ n + Δ)
    (hqd : pRep n <+: q → q.length ≤ n + Δ) :
    addrDist p q ≤ addrDist (collapseAddr n p) (collapseAddr n q) + 2 * Δ := by
  by_cases h1 : pRep n <+: p
  · by_cases h2 : pRep n <+: q
    · rw [collapseAddr_of_prefix h1, collapseAddr_of_prefix h2, addrDist_self]
      have ht := addrDist_triangle p (pRep n) q
      have e1 : addrDist p (pRep n) = p.length - n := by
        rw [addrDist_comm, addrDist_of_prefix h1, pRep_length]
      have e2 : addrDist (pRep n) q = q.length - n := by
        rw [addrDist_of_prefix h2, pRep_length]
      have := hpd h1
      have := hqd h2
      omega
    · have hq' : q <+: pRep n := hq.resolve_right h2
      have e1 : addrDist (pRep n) q = n - q.length := by
        rw [addrDist_comm, addrDist_of_prefix hq', pRep_length]
      have e2 : addrDist p q = p.length - q.length := by
        rw [addrDist_comm, addrDist_of_prefix (hq'.trans h1)]
      have := hpd h1
      have := h1.length_le
      rw [collapseAddr_of_prefix h1, collapseAddr_of_not_prefix h2, e1, e2]
      simp only [pRep_length] at this
      omega
  · by_cases h2 : pRep n <+: q
    · have hp' : p <+: pRep n := hp.resolve_right h1
      have e1 : addrDist p (pRep n) = n - p.length := by
        rw [addrDist_of_prefix hp', pRep_length]
      have e2 : addrDist p q = q.length - p.length := by
        rw [addrDist_of_prefix (hp'.trans h2)]
      have := hqd h2
      have := h2.length_le
      rw [collapseAddr_of_not_prefix h1, collapseAddr_of_prefix h2, e1, e2]
      simp only [pRep_length] at this
      omega
    · rw [collapseAddr_of_not_prefix h1, collapseAddr_of_not_prefix h2]
      omega

/-- **A piece is a neck with everything else beyond its far end**: every address is a
neck vertex or extends the far end, the addresses beyond the far end reach at most `Δ`
deeper, and the ports all lie beyond the far end. -/
structure IsNeckPiece (X : Piece) (n Δ : ℕ) : Prop where
  neck : X.mem (pRep n)
  cases : ∀ p, X.mem p → p <+: pRep n ∨ pRep n <+: p
  depth : ∀ p, X.mem p → pRep n <+: p → p.length ≤ n + Δ
  port : ∀ j, j < X.nports → pRep n <+: X.port j

/-- The collapse of a neck piece onto its flat configuration, as a map of vertices. -/
def collapse (X : Piece) {n Δ : ℕ} (h : IsNeckPiece X n Δ) (x : X.carrier) :
    (flatPiece n X.nports).carrier :=
  ⟨collapseAddr n x.1, by
    rw [flatPiece_mem, collapseAddr]
    split
    · exact List.prefix_refl _
    · next hn => exact (h.cases x.1 x.2).resolve_right hn⟩

/-- **`thm:matched-presentation` (`it:matched-flat`), abstractly**: a neck piece
of depth `Δ` beyond its far end admits a `(2Δ + 1)`-port quasi-isometry onto its flat
configuration, the collapse of everything beyond the far end onto the far end. -/
theorem isPortQI_collapse (X : Piece) {n Δ : ℕ} (h : IsNeckPiece X n Δ) :
    IsPortQI (2 * Δ + 1) X.space (flatPiece n X.nports).space (collapse X h) := by
  have hL : (1 : ℝ) ≤ 2 * Δ + 1 := by
    have : (0 : ℝ) ≤ Δ := Nat.cast_nonneg Δ
    linarith
  have hup : ∀ a b : X.space.carrier,
      dist (collapse X h a : (flatPiece n X.nports).space.carrier) (collapse X h b)
        ≤ dist a b := by
    intro a b
    change ((addrDist (collapseAddr n a.1) (collapseAddr n b.1) : ℕ) : ℝ)
      ≤ ((addrDist a.1 b.1 : ℕ) : ℝ)
    exact_mod_cast addrDist_collapseAddr_le (h.cases a.1 a.2) (h.cases b.1 b.2)
  have hlo : ∀ a b : X.space.carrier, dist a b
      ≤ dist (collapse X h a : (flatPiece n X.nports).space.carrier) (collapse X h b)
        + 2 * Δ := by
    intro a b
    change ((addrDist a.1 b.1 : ℕ) : ℝ)
      ≤ ((addrDist (collapseAddr n a.1) (collapseAddr n b.1) : ℕ) : ℝ) + 2 * (Δ : ℝ)
    exact_mod_cast addrDist_le_collapseAddr (h.cases a.1 a.2) (h.cases b.1 b.2)
      (h.depth a.1 a.2) (h.depth b.1 b.2)
  have hfix : ∀ p : List ℕ, p <+: pRep n → collapseAddr n p = p := by
    intro p hp
    by_cases hn : pRep n <+: p
    · rw [collapseAddr_of_prefix hn]
      exact hn.eq_of_length (le_antisymm hn.length_le hp.length_le)
    · exact collapseAddr_of_not_prefix hn
  refine ⟨fun a b => ?_, fun a b => ?_, fun y => ?_, ?_, fun j => ?_⟩
  · have h2 : dist a b ≤ (2 * Δ + 1) * dist a b + (2 * Δ + 1) := by
      nlinarith [dist_nonneg (x := a) (y := b)]
    exact (hup a b).trans h2
  · have h2 : dist (collapse X h a : (flatPiece n X.nports).space.carrier) (collapse X h b)
        + 2 * Δ
        ≤ (2 * Δ + 1) * dist (collapse X h a : (flatPiece n X.nports).space.carrier)
            (collapse X h b) + (2 * Δ + 1) * (2 * Δ + 1) := by
      nlinarith [dist_nonneg (x := (collapse X h a : (flatPiece n X.nports).space.carrier))
        (y := collapse X h b)]
    exact (hlo a b).trans h2
  · obtain ⟨q, hq⟩ := y
    refine ⟨⟨q, X.mem_of_prefix hq h.neck⟩, ?_⟩
    have : collapse X h ⟨q, X.mem_of_prefix hq h.neck⟩ = ⟨q, hq⟩ :=
      Subtype.ext (hfix q hq)
    rw [this, dist_self]
    linarith
  · change dist (collapse X h X.entry) (flatPiece n X.nports).entry ≤ _
    have : collapse X h X.entry = (flatPiece n X.nports).entry :=
      Subtype.ext (hfix [] List.nil_prefix)
    rw [this, dist_self]
    linarith
  · change dist (collapse X h (X.portVert j)) ((flatPiece n X.nports).portVert j) ≤ _
    rcases lt_or_ge j X.nports with hj | hj
    · have : collapse X h (X.portVert j) = (flatPiece n X.nports).portVert j := by
        refine Subtype.ext ?_
        show collapseAddr n (X.port j) = (flatPiece n X.nports).port j
        rw [collapseAddr_of_prefix (h.port j hj), flatPiece_port_of_lt hj]
      rw [this, dist_self]
      linarith
    · have : collapse X h (X.portVert j) = (flatPiece n X.nports).portVert j := by
        refine Subtype.ext ?_
        show collapseAddr n (X.port j) = (flatPiece n X.nports).port j
        rw [Piece.port, Piece.portSlot_of_le hj, flatPiece_port_of_le hj]
        exact hfix [] List.nil_prefix
      rw [this, dist_self]
      linarith

/-! ### Words over `Fin N` read over `ℕ` -/

open BranchingProcess (sample Survives skeleton survivors skeletonDegree bushAt childSet)

variable {N : ℕ}

/-- A word over `Fin N` read as a word over `ℕ`. -/
def pvals (u : GWord N) : List ℕ := u.map Fin.val

@[simp] lemma pvals_nil : pvals ([] : GWord N) = [] := rfl

@[simp] lemma pvals_cons (i : Fin N) (u : GWord N) : pvals (i :: u) = (i : ℕ) :: pvals u := rfl

@[simp] lemma pvals_append (u v : GWord N) : pvals (u ++ v) = pvals u ++ pvals v := by
  simp [pvals]

@[simp] lemma pvals_length (u : GWord N) : (pvals u).length = u.length := by simp [pvals]

lemma pvals_injective : Function.Injective (pvals (N := N)) :=
  List.map_injective_iff.mpr Fin.val_injective

lemma wedgeN_pvals (u v : GWord N) :
    wedgeN (pvals u) (pvals v) = pvals (BranchingProcess.wedge u v) := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
      cases v with
      | nil => simp
      | cons b v =>
          rw [pvals_cons, pvals_cons, wedgeN_cons_cons, BranchingProcess.wedge_cons_cons]
          by_cases hab : a = b
          · subst hab
            simp [ih]
          · rw [if_neg (fun h => hab (Fin.ext h)), if_neg hab]
            rfl

/-- The tree metric of the ambient tree is the address metric of the readings. -/
lemma addrDist_pvals (u v : GWord N) :
    addrDist (pvals u) (pvals v) = BranchingProcess.treeDist u v := by
  rw [addrDist, BranchingProcess.treeDist, wedgeN_pvals, pvals_length, pvals_length,
    pvals_length]


end ChainClasses
