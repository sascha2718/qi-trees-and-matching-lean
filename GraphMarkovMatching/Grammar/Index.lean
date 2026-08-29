/-
The accessible coordinate system of the general-ν screen block
(`arbitrary_offspring_matching.tex`, `def:ordacc`, `def:scracc`, and
`thm:nilpotence`): the ordered pairs and screens reachable from the
fresh comparison form the finite accessible index, every accessible
screen is anchored, and the concrete block matrix on the live
accessible screens is nilpotent.

* `OrdAcc` / `ordIndex`: the accessible ordered pairs, generated from
  the fresh seed `(F, F)` by the product successor step `pairSucc`;
  closed under swap and the two diagonals, anchored, Fk-free, and
  contained in the bounded alphabet;
* `ScrAcc` / `scrIndex`: the accessible screens: seeded by a quadratic
  comparison over an accessible pair (`ScrSeed`) and propagated by the
  sub-successor relation `SubSuccRel`, which contains the full
  `screenSucc` step (`screenSucc_subSucc`); every accessible screen is
  anchored (`ScrAcc.anchored`) with nonempty zero list, and the live
  ones form the finite index `scrIndex`, closed under live successors
  (`scrIndex_succ`);
* `accN` / `accN_acyclic`: the block matrix charging `CW` on each
  `screenSucc` edge of the live accessible index has an acyclic
  support graph: a support cycle yields a periodic anchored live
  screen path, which `no_anchored_live_cycle` kills;
* `accN_nilpotent` (`thm:nilpotence` for the concrete block): the
  accessible block matrix is nilpotent at exponent `card + 1`, by
  `nilpotent_of_acyclic`.
-/
import GraphMarkovMatching.Grammar.Nilpotence
import GraphMarkovMatching.Grammar.Accessible

namespace GraphMarkovMatching

open scoped ENNReal Classical

/-! ### Accessible ordered pairs -/

/-- The product successor step on ordered pairs of targets. -/
def pairSucc (S : Finset ℕ) (p : Tgt × Tgt) : Finset (Tgt × Tgt) :=
  (tgtSucc S p.1) ×ˢ (tgtSucc S p.2)

/-- Membership in the product successor componentwise. -/
lemma mem_pairSucc {S : Finset ℕ} {p q : Tgt × Tgt} :
    q ∈ pairSucc S p ↔ q.1 ∈ tgtSucc S p.1 ∧ q.2 ∈ tgtSucc S p.2 :=
  Finset.mem_product

/-- The accessible ordered pairs (`def:ordacc`): generated from the
fresh comparison by the product successor step. -/
inductive OrdAcc (S : Finset ℕ) : Tgt × Tgt → Prop
  | seed : OrdAcc S (Tgt.F, Tgt.F)
  | step {p q : Tgt × Tgt} (hp : OrdAcc S p) (hq : q ∈ pairSucc S p) :
      OrdAcc S q

/-- Both components of an accessible pair are anchored at a common
absolute depth (`thm:anchor-step`). -/
lemma OrdAcc.anchored {S : Finset ℕ} {p : Tgt × Tgt} (h : OrdAcc S p) :
    ∃ d, TgtAnchored S d p.1 ∧ TgtAnchored S d p.2 := by
  induction h with
  | seed =>
      have hF : TgtAnchored S 0 Tgt.F := by
        intro m hm
        rw [Nat.zero_add]
        exact descend_FF_closure hm
      exact ⟨0, hF, hF⟩
  | @step r q hr hq ih =>
      obtain ⟨d, h1, h2⟩ := ih
      obtain ⟨hq1, hq2⟩ := mem_pairSucc.mp hq
      exact ⟨d + 1, h1.step hq1, h2.step hq2⟩

/-- Accessibility is symmetric in the two components. -/
lemma OrdAcc.swap {S : Finset ℕ} {p : Tgt × Tgt} (h : OrdAcc S p) :
    OrdAcc S (p.2, p.1) := by
  induction h with
  | seed => exact OrdAcc.seed
  | @step r q hr hq ih =>
      obtain ⟨hq1, hq2⟩ := mem_pairSucc.mp hq
      exact ih.step (mem_pairSucc.mpr ⟨hq2, hq1⟩)

/-- The left diagonal of an accessible pair is accessible. -/
lemma OrdAcc.diag_left {S : Finset ℕ} {p : Tgt × Tgt} (h : OrdAcc S p) :
    OrdAcc S (p.1, p.1) := by
  induction h with
  | seed => exact OrdAcc.seed
  | @step r q hr hq ih =>
      have hq1 := (mem_pairSucc.mp hq).1
      exact ih.step (mem_pairSucc.mpr ⟨hq1, hq1⟩)

/-- The right diagonal of an accessible pair is accessible. -/
lemma OrdAcc.diag_right {S : Finset ℕ} {p : Tgt × Tgt} (h : OrdAcc S p) :
    OrdAcc S (p.2, p.2) :=
  h.swap.diag_left

/-! ### The Fk-free alphabet -/

/-- The Fk-free alphabet: forced states and the fresh state. -/
def ZFtgt : Tgt → Prop
  | Tgt.Z _ => True
  | Tgt.F => True
  | Tgt.Fk _ => False

/-- Every member of a cascade pair is Fk-free. -/
lemma ZFtgt_of_mem_gpair : ∀ {j : ℕ} {t : Tgt}, t ∈ gpair j → ZFtgt t := by
  intro j t ht
  rw [gpair] at ht
  split_ifs at ht with h4 h3
  · rcases Finset.mem_insert.mp ht with rfl | ht
    · trivial
    · rw [Finset.mem_singleton.mp ht]
      trivial
  · rcases Finset.mem_insert.mp ht with rfl | ht
    · trivial
    · rw [Finset.mem_singleton.mp ht]
      trivial
  · rw [Finset.mem_singleton.mp ht]
    trivial

/-- Every successor target is Fk-free. -/
lemma ZFtgt_of_mem_tgtSucc {S : Finset ℕ} {t t' : Tgt}
    (h : t' ∈ tgtSucc S t) : ZFtgt t' := by
  cases t with
  | Z j => exact ZFtgt_of_mem_gpair h
  | F =>
      obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp h
      exact ZFtgt_of_mem_gpair hk
  | Fk k => exact ZFtgt_of_mem_gpair h

/-- Accessible pairs live in the Fk-free alphabet. -/
lemma OrdAcc.zf {S : Finset ℕ} {p : Tgt × Tgt} (h : OrdAcc S p) :
    ZFtgt p.1 ∧ ZFtgt p.2 := by
  induction h with
  | seed => exact ⟨trivial, trivial⟩
  | @step r q hr hq ih =>
      obtain ⟨hq1, hq2⟩ := mem_pairSucc.mp hq
      exact ⟨ZFtgt_of_mem_tgtSucc hq1, ZFtgt_of_mem_tgtSucc hq2⟩

/-- Accessible pairs live in the bounded alphabet. -/
lemma OrdAcc.mem_univ {N : ℕ} {S : Finset ℕ} {p : Tgt × Tgt}
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (h : OrdAcc S p) :
    p.1 ∈ tgtUniv N ∧ p.2 ∈ tgtUniv N := by
  induction h with
  | seed => exact ⟨F_mem_tgtUniv, F_mem_tgtUniv⟩
  | @step r q hr hq ih =>
      obtain ⟨hq1, hq2⟩ := mem_pairSucc.mp hq
      exact ⟨tgtSucc_subset hN hS ih.1 hq1, tgtSucc_subset hN hS ih.2 hq2⟩

/-- The finite index of accessible ordered pairs. -/
noncomputable def ordIndex (N : ℕ) (S : Finset ℕ) : Finset (Tgt × Tgt) :=
  ((tgtUniv N) ×ˢ (tgtUniv N)).filter (OrdAcc S)

/-- Membership in the ordered index is exactly accessibility. -/
lemma mem_ordIndex {N : ℕ} {S : Finset ℕ} {p : Tgt × Tgt}
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) :
    p ∈ ordIndex N S ↔ OrdAcc S p := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    obtain ⟨h1, h2⟩ := OrdAcc.mem_univ hN hS h
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, h⟩

/-! ### Accessible screens -/

/-- A screen seed: a quadratic comparison over an accessible pair.  The
cell, every zero-list member, and the normalization (if present) are
successors of the pair components, and the zero list is nonempty. -/
def ScrSeed (S : Finset ℕ) (sc : GScreen) : Prop :=
  ∃ p : Tgt × Tgt, OrdAcc S p
    ∧ (sc.cell ∈ tgtSucc S p.1 ∨ sc.cell ∈ tgtSucc S p.2)
    ∧ (∀ t ∈ sc.zlist, t ∈ tgtSucc S p.1 ∪ tgtSucc S p.2)
    ∧ sc.zlist.Nonempty
    ∧ (sc.norm = none
        ∨ ∃ u, sc.norm = some u
            ∧ (u ∈ tgtSucc S p.1 ∨ u ∈ tgtSucc S p.2))

/-- The sub-successor relation: the cell advances one grammar step, the
zero list is a nonempty subset of the successor zero list, and the
normalization descends.  Full `screenSucc` members satisfy it, and so
do the quadratic witnesses with singleton sub-lists. -/
def SubSuccRel (S : Finset ℕ) (sc sc' : GScreen) : Prop :=
  sc'.cell ∈ tgtSucc S sc.cell ∧ sc'.zlist ⊆ zsucc S sc.zlist
    ∧ sc'.zlist.Nonempty ∧ sc'.norm ∈ normSucc S sc.norm

/-- The accessible screens: screen seeds propagated by the
sub-successor relation. -/
inductive ScrAcc (S : Finset ℕ) : GScreen → Prop
  | seed {sc} (h : ScrSeed S sc) : ScrAcc S sc
  | step {sc sc'} (h : ScrAcc S sc) (h' : SubSuccRel S sc sc') :
      ScrAcc S sc'

/-- Accessible screens have nonempty zero lists. -/
lemma ScrAcc.nonempty {S : Finset ℕ} {sc : GScreen} (h : ScrAcc S sc) :
    sc.zlist.Nonempty := by
  induction h with
  | @seed sc h =>
      obtain ⟨q, _, _, _, hne, _⟩ := h
      exact hne
  | @step sc sc' h h' ih => exact h'.2.2.1

/-- Accessible screens are anchored (`thm:anchor-step`; the
sub-successor propagation step is proved inline here). -/
lemma ScrAcc.anchored {S : Finset ℕ} {sc : GScreen} (h : ScrAcc S sc) :
    ∃ d, Anchored S d sc := by
  induction h with
  | @seed sc h =>
      obtain ⟨q, hacc, hcell, hz, hne, hn⟩ := h
      obtain ⟨d, h1, h2⟩ := hacc.anchored
      refine ⟨d + 1, ?_, fun t ht => ?_⟩
      · rcases hcell with hc | hc
        · exact h1.step hc
        · exact h2.step hc
      · rcases Finset.mem_union.mp (hz t ht) with h' | h'
        · exact h1.step h'
        · exact h2.step h'
  | @step sc sc' h h' ih =>
      obtain ⟨d, hc, hzl⟩ := ih
      refine ⟨d + 1, hc.step h'.1, fun t ht => ?_⟩
      obtain ⟨u, hu, htu⟩ := Finset.mem_biUnion.mp (h'.2.1 ht)
      exact (hzl u hu).step htu

/-- Accessible screens live in the Fk-free alphabet. -/
lemma ScrAcc.zf {S : Finset ℕ} {sc : GScreen} (h : ScrAcc S sc) :
    ZFtgt sc.cell ∧ (∀ t ∈ sc.zlist, ZFtgt t)
      ∧ ∀ u, sc.norm = some u → ZFtgt u := by
  induction h with
  | @seed sc h =>
      obtain ⟨q, hacc, hcell, hz, hne, hn⟩ := h
      refine ⟨?_, fun t ht => ?_, fun u hu => ?_⟩
      · rcases hcell with hc | hc <;> exact ZFtgt_of_mem_tgtSucc hc
      · rcases Finset.mem_union.mp (hz t ht) with h' | h' <;>
          exact ZFtgt_of_mem_tgtSucc h'
      · rcases hn with hn | ⟨v, hv, hv'⟩
        · rw [hn] at hu
          exact absurd hu (by simp)
        · rw [hv] at hu
          obtain rfl := Option.some_inj.mp hu
          rcases hv' with h' | h' <;> exact ZFtgt_of_mem_tgtSucc h'
  | @step sc sc' h h' ih =>
      refine ⟨ZFtgt_of_mem_tgtSucc h'.1, fun t ht => ?_, fun u hu => ?_⟩
      · obtain ⟨w, hw, htw⟩ := Finset.mem_biUnion.mp (h'.2.1 ht)
        exact ZFtgt_of_mem_tgtSucc htw
      · have hns := h'.2.2.2
        cases hsc : sc.norm with
        | none =>
            rw [hsc] at hns
            simp only [normSucc, Finset.mem_singleton] at hns
            rw [hns] at hu
            exact absurd hu (by simp)
        | some v =>
            rw [hsc] at hns
            simp only [normSucc] at hns
            obtain ⟨w, hw, hwn⟩ := Finset.mem_image.mp hns
            rw [← hwn] at hu
            obtain rfl := Option.some_inj.mp hu
            exact ZFtgt_of_mem_tgtSucc hw

/-- The cell together with the normalization of an accessible screen is
an accessible pair. -/
lemma ScrAcc.norm_pair {S : Finset ℕ} {sc : GScreen} (h : ScrAcc S sc) :
    ∀ u, sc.norm = some u → OrdAcc S (sc.cell, u) := by
  induction h with
  | @seed sc h =>
      intro u hu
      obtain ⟨q, hacc, hcell, hz, hne, hn⟩ := h
      rcases hn with hn | ⟨v, hv, hv'⟩
      · rw [hn] at hu
        exact absurd hu (by simp)
      · rw [hv] at hu
        obtain rfl := Option.some_inj.mp hu
        rcases hcell with hc | hc <;> rcases hv' with hu' | hu'
        · exact hacc.diag_left.step (mem_pairSucc.mpr ⟨hc, hu'⟩)
        · exact hacc.step (mem_pairSucc.mpr ⟨hc, hu'⟩)
        · exact hacc.swap.step (mem_pairSucc.mpr ⟨hc, hu'⟩)
        · exact hacc.diag_right.step (mem_pairSucc.mpr ⟨hc, hu'⟩)
  | @step sc sc' h h' ih =>
      intro u' hu'
      have hns := h'.2.2.2
      cases hsc : sc.norm with
      | none =>
          rw [hsc] at hns
          simp only [normSucc, Finset.mem_singleton] at hns
          rw [hns] at hu'
          exact absurd hu' (by simp)
      | some v =>
          rw [hsc] at hns
          simp only [normSucc] at hns
          obtain ⟨w, hw, hwn⟩ := Finset.mem_image.mp hns
          rw [← hwn] at hu'
          obtain rfl := Option.some_inj.mp hu'
          exact (ih v hsc).step (mem_pairSucc.mpr ⟨h'.1, hw⟩)

/-- The diagonal pair of the cell of an accessible screen is
accessible. -/
lemma ScrAcc.cell_pair {S : Finset ℕ} {sc : GScreen} (h : ScrAcc S sc) :
    OrdAcc S (sc.cell, sc.cell) := by
  induction h with
  | @seed sc h =>
      obtain ⟨q, hacc, hcell, _, _, _⟩ := h
      rcases hcell with hc | hc
      · exact hacc.diag_left.step (mem_pairSucc.mpr ⟨hc, hc⟩)
      · exact hacc.diag_right.step (mem_pairSucc.mpr ⟨hc, hc⟩)
  | @step sc sc' h h' ih =>
      exact ih.step (mem_pairSucc.mpr ⟨h'.1, h'.1⟩)

/-- Accessible screens live in the bounded screen family. -/
lemma ScrAcc.mem_univ {N : ℕ} {S : Finset ℕ} {sc : GScreen}
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (h : ScrAcc S sc) :
    sc ∈ screenUniv N := by
  induction h with
  | @seed sc h =>
      obtain ⟨q, hacc, hcell, hz, hne, hn⟩ := h
      obtain ⟨hq1, hq2⟩ := OrdAcc.mem_univ hN hS hacc
      refine mem_screenUniv.mpr ⟨?_, fun t ht => ?_, fun u hu => ?_⟩
      · rcases hcell with hc | hc
        · exact tgtSucc_subset hN hS hq1 hc
        · exact tgtSucc_subset hN hS hq2 hc
      · rcases Finset.mem_union.mp (hz t ht) with h' | h'
        · exact tgtSucc_subset hN hS hq1 h'
        · exact tgtSucc_subset hN hS hq2 h'
      · rcases hn with hn | ⟨v, hv, hv'⟩
        · rw [hn] at hu
          exact absurd hu (by simp)
        · rw [hv] at hu
          obtain rfl := Option.some_inj.mp hu
          rcases hv' with h' | h'
          · exact tgtSucc_subset hN hS hq1 h'
          · exact tgtSucc_subset hN hS hq2 h'
  | @step sc sc' h h' ih =>
      obtain ⟨h1, h2, h3⟩ := mem_screenUniv.mp ih
      refine mem_screenUniv.mpr ⟨tgtSucc_subset hN hS h1 h'.1,
        fun t ht => zsucc_subset hN hS h2 (h'.2.1 ht), fun u hu => ?_⟩
      have hns := h'.2.2.2
      cases hsc : sc.norm with
      | none =>
          rw [hsc] at hns
          simp only [normSucc, Finset.mem_singleton] at hns
          rw [hns] at hu
          exact absurd hu (by simp)
      | some v =>
          rw [hsc] at hns
          simp only [normSucc] at hns
          obtain ⟨w, hw, hwn⟩ := Finset.mem_image.mp hns
          rw [← hwn] at hu
          obtain rfl := Option.some_inj.mp hu
          exact tgtSucc_subset hN hS (h3 v hsc) hw

/-! ### The live index -/

/-- The live accessible screen index: accessible screens whose zero
list avoids the cell and the normalization. -/
noncomputable def scrIndex (N : ℕ) (S : Finset ℕ) : Finset GScreen :=
  (screenUniv N).filter
    (fun sc => ScrAcc S sc ∧ sc.cell ∉ sc.zlist
      ∧ ∀ u, sc.norm = some u → u ∉ sc.zlist)

/-- Membership in the live index. -/
lemma mem_scrIndex {N : ℕ} {S : Finset ℕ} {sc : GScreen}
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) :
    sc ∈ scrIndex N S
      ↔ ScrAcc S sc ∧ sc.cell ∉ sc.zlist
        ∧ ∀ u, sc.norm = some u → u ∉ sc.zlist := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨ScrAcc.mem_univ hN hS h.1, h⟩

/-! ### Nonemptiness and the full successor step -/

/-- Every cascade pair is nonempty. -/
lemma gpair_nonempty (j : ℕ) : (gpair j).Nonempty := by
  rw [gpair]
  split_ifs
  · exact ⟨_, Finset.mem_insert_self _ _⟩
  · exact ⟨_, Finset.mem_insert_self _ _⟩
  · exact Finset.singleton_nonempty _

/-- Every target has a successor when the support is nonempty. -/
lemma tgtSucc_nonempty {S : Finset ℕ} (hS : S.Nonempty) (t : Tgt) :
    (tgtSucc S t).Nonempty := by
  cases t with
  | Z j => exact gpair_nonempty j
  | F =>
      obtain ⟨k, hk⟩ := hS
      obtain ⟨x, hx⟩ := gpair_nonempty k
      exact ⟨x, Finset.mem_biUnion.mpr ⟨k, hk, hx⟩⟩
  | Fk k => exact gpair_nonempty k

/-- The successor of a nonempty zero list is nonempty. -/
lemma zsucc_nonempty {S : Finset ℕ} (hS : S.Nonempty) {z : Finset Tgt}
    (hz : z.Nonempty) : (zsucc S z).Nonempty := by
  obtain ⟨t, ht⟩ := hz
  obtain ⟨x, hx⟩ := tgtSucc_nonempty hS t
  exact ⟨x, Finset.mem_biUnion.mpr ⟨t, ht, hx⟩⟩

/-- Full `screenSucc` members satisfy the sub-successor relation. -/
lemma screenSucc_subSucc {S : Finset ℕ} (hS : S.Nonempty)
    {sc sc' : GScreen} (hne : sc.zlist.Nonempty)
    (h : sc' ∈ screenSucc S sc) : SubSuccRel S sc sc' := by
  obtain ⟨⟨t, u⟩, hmem, rfl⟩ := Finset.mem_image.mp h
  obtain ⟨ht, hu⟩ := Finset.mem_product.mp hmem
  exact ⟨ht, Finset.Subset.refl _, zsucc_nonempty hS hne, hu⟩

/-- The live index is closed under live successors. -/
lemma scrIndex_succ {N : ℕ} {S : Finset ℕ} {sc sc' : GScreen}
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hsc : sc ∈ scrIndex N S) (h : sc' ∈ screenSucc S sc)
    (hlive : sc'.cell ∉ sc'.zlist)
    (hlive2 : ∀ u, sc'.norm = some u → u ∉ sc'.zlist) :
    sc' ∈ scrIndex N S := by
  obtain ⟨hacc, _, _⟩ := (mem_scrIndex hN hS).mp hsc
  have hsub := screenSucc_subSucc hSne hacc.nonempty h
  exact (mem_scrIndex hN hS).mpr ⟨hacc.step hsub, hlive, hlive2⟩

/-! ### The block matrix and its nilpotence -/

/-- The accessible block matrix: the constant `CW` on each `screenSucc`
edge of the live accessible index. -/
noncomputable def accN (N : ℕ) (S : Finset ℕ) (CW : ℝ≥0∞) :
    {sc // sc ∈ scrIndex N S} → {sc // sc ∈ scrIndex N S} → ℝ≥0∞ :=
  fun i j => if j.val ∈ screenSucc S i.val then CW else 0

/-- A nonzero entry of the accessible block matrix is a `screenSucc`
edge. -/
private lemma accN_support {N : ℕ} {S : Finset ℕ} {CW : ℝ≥0∞}
    {i j : {sc // sc ∈ scrIndex N S}} (h : accN N S CW i j ≠ 0) :
    j.val ∈ screenSucc S i.val := by
  by_contra hne
  apply h
  simp only [accN]
  exact if_neg hne

/-- A transitive chain unfolds into a finite indexed chain of single
steps. -/
private lemma transGen_chain {ι : Type} {r : ι → ι → Prop} {a b : ι}
    (h : Relation.TransGen r a b) :
    ∃ p : ℕ, 0 < p ∧ ∃ g : ℕ → ι, g 0 = a ∧ g p = b
      ∧ ∀ n < p, r (g n) (g (n + 1)) := by
  induction h with
  | @single c hac =>
      refine ⟨1, Nat.one_pos, fun n => if n = 0 then a else c, ?_, ?_, ?_⟩
      · exact if_pos rfl
      · exact if_neg Nat.one_ne_zero
      · intro n hn
        have hn0 : n = 0 := by omega
        subst hn0
        show r (if (0 : ℕ) = 0 then a else c)
          (if (0 + 1 : ℕ) = 0 then a else c)
        rw [if_pos rfl, if_neg (by omega)]
        exact hac
  | @tail b c hab hbc ih =>
      obtain ⟨p, hp, g, hg0, hgp, hstep⟩ := ih
      refine ⟨p + 1, by omega, fun n => if n ≤ p then g n else c,
        ?_, ?_, ?_⟩
      · exact (if_pos (Nat.zero_le p)).trans hg0
      · exact if_neg (by omega)
      · intro n hn
        show r (if n ≤ p then g n else c)
          (if n + 1 ≤ p then g (n + 1) else c)
        by_cases hnp : n + 1 ≤ p
        · rw [if_pos (by omega), if_pos hnp]
          exact hstep n (by omega)
        · have hne : n = p := by omega
          subst hne
          rw [if_pos (le_refl n), if_neg hnp, hgp]
          exact hbc

/-- A transitive cycle unfolds into a finite indexed closed chain
(`thm:nilpotence`, acyclicity). -/
lemma transGen_exists_chain {ι : Type} {r : ι → ι → Prop} {a : ι}
    (h : Relation.TransGen r a a) :
    ∃ p : ℕ, 0 < p ∧ ∃ g : ℕ → ι, g 0 = a ∧ g p = a
      ∧ ∀ n < p, r (g n) (g (n + 1)) :=
  transGen_chain h

/-- **Acyclicity of the accessible block** (`thm:nilpotence`): the
support graph of the accessible block matrix has no directed cycle: a
cycle would give a periodic anchored live screen path. -/
theorem accN_acyclic {N : ℕ} {S : Finset ℕ} (hN : 2 ≤ N)
    (hS : ∀ k ∈ S, k ≤ N) (CW : ℝ≥0∞) :
    ∀ i, ¬ Relation.TransGen (supportRel (accN N S CW)) i i := by
  intro i hcyc
  obtain ⟨p, hp, g, hg0, hgp, hstep⟩ := transGen_exists_chain hcyc
  have hedge : ∀ n, n < p → (g (n + 1)).val ∈ screenSucc S ((g n).val) :=
    fun n hn => accN_support (hstep n hn)
  have hscr : ∀ m : ℕ, ScrAcc S ((g m).val)
      ∧ (g m).val.cell ∉ (g m).val.zlist
      ∧ ∀ u, (g m).val.norm = some u → u ∉ (g m).val.zlist :=
    fun m => (mem_scrIndex hN hS).mp (g m).property
  have hmod1 : ∀ n : ℕ, (n + 1) % p = (n % p + 1) % p :=
    fun n => (Nat.mod_add_mod n p 1).symm
  have hpath : ∀ n : ℕ,
      (g ((n + 1) % p)).val ∈ screenSucc S ((g (n % p)).val) := by
    intro n
    have hm : n % p < p := Nat.mod_lt n hp
    by_cases hcase : n % p + 1 < p
    · have h1 : (n + 1) % p = n % p + 1 := by
        rw [hmod1 n, Nat.mod_eq_of_lt hcase]
      rw [h1]
      exact hedge (n % p) hm
    · have hpe : n % p + 1 = p := by omega
      have h1 : (n + 1) % p = 0 := by
        rw [hmod1 n, hpe, Nat.mod_self]
      have h2 := hedge (n % p) hm
      rw [hpe, hgp, ← hg0] at h2
      rw [h1]
      exact h2
  have hper : ∀ n : ℕ, (g ((n + p) % p)).val = (g (n % p)).val := by
    intro n
    rw [Nat.add_mod_right]
  obtain ⟨d₀, hanch⟩ := (hscr (0 % p)).1.anchored
  exact no_anchored_live_cycle hp (fun n => (g (n % p)).val) hpath hper
    hanch ((hscr (0 % p)).1.nonempty) (fun n _ => (hscr (n % p)).2.1)

/-- **Nilpotence of the accessible block** (`thm:nilpotence` for the
concrete block matrix): the accessible block matrix annihilates every
vector at the positive exponent `card + 1`. -/
theorem accN_nilpotent {N : ℕ} {S : Finset ℕ} (hN : 2 ≤ N)
    (hS : ∀ k ∈ S, k ≤ N) (CW : ℝ≥0∞) :
    ∀ x, (mulVec (accN N S CW))^[Fintype.card {sc // sc ∈ scrIndex N S} + 1] x
      = fun _ => 0 := by
  intro x
  have h := nilpotent_of_acyclic (accN N S CW) (accN_acyclic hN hS CW)
  rw [Function.iterate_succ_apply]
  exact h (mulVec (accN N S CW) x)

end GraphMarkovMatching
