/-
The general-ν closure: coordinates, dichotomies, and levels
(`arbitrary_offspring_matching.tex`: the assembly of the transfer rows
(`sec:rows`) and the closed recursion (`sec:recursion`, `thm:engine`)
over the accessible index).

* `genPsi` / `genE`: the ordinary scalar and the screen vector over
  the accessible index;
* `interpPhi_le_genPsi` / `interpScreen_le_genE_sup`: accessible
  coordinates are below the running suprema; for screens this is the
  pruning dichotomy: an accessible screen is live and indexed, or it
  is self-pruned and vanishes;
* `accN_row_sum_le`: the uniform row bound of the block matrix,
  feeding the geometric invariant bound;
* `genPsi_base` / `genE_base`: the height-0 levels;
* `failure_le_genPsi`: the failure bridge through the principal
  coordinate.
-/
import GraphMarkovMatching.Grammar.Index
import GraphMarkovMatching.Rows.Base
import GraphMarkovMatching.Closure.Geometric
import GraphMarkovMatching.Rows.Psi

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (ν : PMF ℕ) (v0 : V) (N : ℕ) (S : Finset ℕ)

/-- The ordinary scalar of `def:running`: the supremum of the
accessible ordinary coordinates. -/
noncomputable def genPsi (h : ℕ) : ℝ≥0∞ :=
  ⨆ p : {p // p ∈ ordIndex N S}, interpPhi α Rv μ ν v0 h p.val

/-- The screen vector of `def:running`, over the accessible live
index. -/
noncomputable def genE (h : ℕ) : {sc // sc ∈ scrIndex N S} → ℝ≥0∞ :=
  fun i => interpScreen α Rv μ ν v0 h i.val

/-- Accessible ordinary coordinates are below the ordinary scalar
(`def:running`). -/
lemma interpPhi_le_genPsi (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (h : ℕ)
    {p : Tgt × Tgt} (hp : OrdAcc S p) :
    interpPhi α Rv μ ν v0 h p ≤ genPsi α Rv μ ν v0 N S h :=
  le_iSup (fun p : {p // p ∈ ordIndex N S} =>
      interpPhi α Rv μ ν v0 h p.val)
    (⟨p, (mem_ordIndex hN hS).mpr hp⟩ : {p // p ∈ ordIndex N S})

/-- **The pruning dichotomy** (`def:running`): an accessible screen is
either live,
hence an index coordinate below the screen supremum, or self-pruned,
in which case its interpretation vanishes. -/
lemma interpScreen_le_genE_sup (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N)
    (hrefl : ∀ v, Rv v v) (h : ℕ) {sc : GScreen} (hacc : ScrAcc S sc) :
    interpScreen α Rv μ ν v0 h sc
      ≤ ⨆ i : {sc // sc ∈ scrIndex N S}, genE α Rv μ ν v0 N S h i := by
  by_cases hcell : sc.cell ∈ sc.zlist
  · rw [interpScreen_prune α Rv μ ν v0 hrefl hcell]
    exact zero_le
  · by_cases hnorm : ∃ u, sc.norm = some u ∧ u ∈ sc.zlist
    · obtain ⟨u, hu, humem⟩ := hnorm
      rw [interpScreen_tilt_prune α Rv μ ν v0 hu humem]
      exact zero_le
    · have hmem : sc ∈ scrIndex N S :=
        (mem_scrIndex hN hS).mpr
          ⟨hacc, hcell, fun u hu hum => hnorm ⟨u, hu, hum⟩⟩
      exact le_iSup (fun i : {sc // sc ∈ scrIndex N S} =>
        genE α Rv μ ν v0 N S h i) (⟨sc, hmem⟩ : {sc // sc ∈ scrIndex N S})

/-- The uniform row bound of the block matrix (`thm:geom`). -/
lemma accN_row_sum_le (CW : ℝ≥0∞) (i : {sc // sc ∈ scrIndex N S}) :
    ∑ j, accN N S CW i j ≤ CW * (scrIndex N S).card := by
  calc ∑ j, accN N S CW i j
      ≤ ∑ _j : {sc // sc ∈ scrIndex N S}, CW := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hj : j.val ∈ screenSucc S i.val
        · exact le_of_eq (by rw [accN, if_pos hj])
        · rw [accN, if_neg hj]
          exact zero_le
    _ = (Fintype.card {sc // sc ∈ scrIndex N S}) * CW := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = CW * (scrIndex N S).card := by
        rw [Fintype.card_coe, mul_comm]

/-- The height-0 ordinary bound. -/
lemma genPsi_base (hα0 : 0 ≤ α) (hrefl : ∀ v, Rv v v) :
    genPsi α Rv μ ν v0 N S 0 ≤ etaG α Rv μ + phiE α (q μ Rv v0) := by
  refine iSup_le fun p => ?_
  have hzf := (Finset.mem_filter.mp p.property).2.zf
  refine interpPhi_base α Rv μ ν v0 hα0 (hrefl v0) p.val ?_ ?_
  · intro i hi
    rw [hi] at hzf
    exact hzf.1.elim
  · intro i hi
    rw [hi] at hzf
    exact hzf.2.elim

/-- The height-0 screen bound. -/
lemma genE_base (hα : 0 < α) (hrefl : ∀ v, Rv v v)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0)
    (i : {sc // sc ∈ scrIndex N S}) :
    genE α Rv μ ν v0 N S 0 i ≤ baseScreenBound α Rv μ := by
  have hmem := Finset.mem_filter.mp i.property
  have hacc : ScrAcc S i.val := hmem.2.1
  have hzf := hacc.zf
  refine interpScreen_base α Rv μ ν v0 hα hrefl hsymm hhalf i.val
    hacc.nonempty (fun t ht m hm => ?_) (fun m hm => ?_)
  · have h1 := hzf.2.1 t ht
    rw [hm] at h1
    exact h1.elim
  · exact (hzf.2.2 _ hm).elim

/-- **Failure below the running scalar** (`eq:failure-principal`): the
expected bad degree of the process at any height is below the fresh
diagonal coordinate, hence below the ordinary scalar. -/
lemma failure_le_genPsi (hα0 : 0 ≤ α) (hN : 2 ≤ N)
    (hS : ∀ k ∈ S, k ≤ N) (hrefl : ∀ v, Rv v v) (h : ℕ) :
    (∑' x, Tlaw μ ν v0 h x
        * qE (Tlaw μ ν v0 h) (fullSim (labRel Rv) h) x)
      ≤ genPsi α Rv μ ν v0 N S h := by
  refine le_trans ?_
    (interpPhi_le_genPsi α Rv μ ν v0 N S hN hS h OrdAcc.seed)
  exact tsum_qE_le_PhiDres hα0 (Tlaw μ ν v0 h) (fullSim (labRel Rv) h)
    (fullSim_refl (labRel Rv) (fun s => hrefl s.1) h)

/-! ### The ordinary step function -/

/-- The generic ordinary step function (`def:step-functions`,
`eq:genF`): root injections, one mixture cell bound with its one-sided
tilt mass, and the quadratic cross term. -/
noncomputable def genF (α δ L K : ℝ) (theta0 Tν : ℝ≥0∞) (cS : ℕ)
    (a b : ℝ≥0∞) : ℝ≥0∞ :=
  theta0 + (cellCB α δ L K a b b + oneSidedBound α Tν cS a b)
    + ENNReal.ofReal (2 * α)
      * (theta0 * (cellCB α δ L K a b b + oneSidedBound α Tν cS a b))

lemma genF_mono (α δ L K : ℝ) (theta0 Tν : ℝ≥0∞) (cS : ℕ)
    {a a' b b' : ℝ≥0∞} (ha : a ≤ a') (hb : b ≤ b') :
    genF α δ L K theta0 Tν cS a b ≤ genF α δ L K theta0 Tν cS a' b' := by
  have hcb : cellCB α δ L K a b b + oneSidedBound α Tν cS a b
      ≤ cellCB α δ L K a' b' b' + oneSidedBound α Tν cS a' b' :=
    add_le_add (cellCB_mono α δ L K ha hb hb)
      (oneSidedBound_mono α Tν cS ha hb)
  exact add_le_add (add_le_add le_rfl hcb)
    (mul_le_mul_right (mul_le_mul_right hcb _) _)

/-! ### Membership dischargers -/

lemma gcomp_mem_tgtSucc_Z {S : Finset ℕ} {k : ℕ} {s : Tgt}
    (hs : s = gcomp0 k ∨ s = gcomp1 k) : s ∈ tgtSucc S (Tgt.Z k) := by
  rcases hs with rfl | rfl
  · exact (gcomp_mem_gpair k).1
  · exact (gcomp_mem_gpair k).2

lemma gcomp_mem_tgtSucc_F {S : Finset ℕ} {k : ℕ} (hk : k ∈ S) {s : Tgt}
    (hs : s = gcomp0 k ∨ s = gcomp1 k) : s ∈ tgtSucc S Tgt.F := by
  rcases hs with rfl | rfl
  · exact Finset.mem_biUnion.mpr ⟨k, hk, (gcomp_mem_gpair k).1⟩
  · exact Finset.mem_biUnion.mpr ⟨k, hk, (gcomp_mem_gpair k).2⟩

/-- The seed screens of the ordinary rows are accessible. -/
lemma scrAcc_seed_of {S : Finset ℕ} {p : Tgt × Tgt} (hp : OrdAcc S p)
    {c : Tgt} {z : Finset Tgt} {u : Option Tgt}
    (hc : c ∈ tgtSucc S p.1 ∨ c ∈ tgtSucc S p.2)
    (hz : ∀ t ∈ z, t ∈ tgtSucc S p.1 ∪ tgtSucc S p.2)
    (hne : z.Nonempty)
    (hu : u = none ∨ ∃ w, u = some w
      ∧ (w ∈ tgtSucc S p.1 ∨ w ∈ tgtSucc S p.2)) :
    ScrAcc S ⟨c, z, u⟩ :=
  ScrAcc.seed ⟨p, hp, hc, hz, hne, hu⟩

/-! ### The successor charge as a matrix action -/

/-- **The successor collection**: the weighted sum of successor-screen
interpretations of an index screen is below the matrix action of the
block matrix on the screen vector.  Pruned successors vanish by the
pruning lemmas; live successors are index coordinates by the closure
of the accessible index. -/
lemma succ_sum_le_mulVec (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N)
    (hSne : S.Nonempty) (hrefl : ∀ v, Rv v v) {sc : GScreen}
    (hsc : sc ∈ scrIndex N S) (CW : ℝ≥0∞) (h : ℕ) :
    CW * (∑ sc' ∈ screenSucc S sc, interpScreen α Rv μ ν v0 h sc')
      ≤ mulVec (accN N S CW) (genE α Rv μ ν v0 N S h) ⟨sc, hsc⟩ := by
  have hacc : ScrAcc S sc := ((mem_scrIndex hN hS).mp hsc).1
  rw [Finset.mul_sum]
  rw [show (∑ sc' ∈ screenSucc S sc, CW * interpScreen α Rv μ ν v0 h sc')
      = ∑ sc' ∈ (screenSucc S sc).filter (· ∈ scrIndex N S),
          CW * interpScreen α Rv μ ν v0 h sc' from ?_]
  · rw [show mulVec (accN N S CW) (genE α Rv μ ν v0 N S h) ⟨sc, hsc⟩
        = ∑ j : {sc // sc ∈ scrIndex N S},
            (if j.val ∈ screenSucc S sc then CW else 0)
              * genE α Rv μ ν v0 N S h j from rfl]
    rw [show (∑ j : {sc // sc ∈ scrIndex N S},
        (if j.val ∈ screenSucc S sc then CW else 0)
          * genE α Rv μ ν v0 N S h j)
        = ∑ j ∈ Finset.univ.filter
            (fun j : {sc // sc ∈ scrIndex N S} =>
              j.val ∈ screenSucc S sc),
            (if j.val ∈ screenSucc S sc then CW else 0)
              * genE α Rv μ ν v0 N S h j from ?_]
    · refine le_of_eq (Finset.sum_bij
        (fun sc' hsc' => (⟨sc', (Finset.mem_filter.mp hsc').2⟩ :
          {sc // sc ∈ scrIndex N S})) ?_ ?_ ?_ ?_)
      · intro sc' hsc'
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hsc').1⟩
      · intro a ha b hb hab
        exact congrArg Subtype.val hab
      · intro j hj
        refine ⟨j.val, Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hj).2, j.property⟩, ?_⟩
        exact Subtype.ext rfl
      · intro sc' hsc'
        rw [if_pos (Finset.mem_filter.mp hsc').1]
        rfl
    · refine (Finset.sum_filter_of_ne fun j _ hne => ?_).symm
      by_contra hj
      rw [if_neg hj, zero_mul] at hne
      exact hne rfl
  · refine (Finset.sum_filter_of_ne fun sc' hsc' hne => ?_).symm
    by_contra hmem
    have hacc' : ScrAcc S sc' :=
      hacc.step (screenSucc_subSucc hSne hacc.nonempty hsc')
    have hnotlive : ¬ (sc'.cell ∉ sc'.zlist
        ∧ ∀ u, sc'.norm = some u → u ∉ sc'.zlist) := by
      intro hlive
      exact hmem ((mem_scrIndex hN hS).mpr ⟨hacc', hlive.1, hlive.2⟩)
    rcases Classical.not_and_iff_not_or_not.mp hnotlive with hc | hn
    · rw [interpScreen_prune α Rv μ ν v0 hrefl (Classical.not_not.mp hc),
        mul_zero] at hne
      exact hne rfl
    · push Not at hn
      obtain ⟨u, hu, hum⟩ := hn
      rw [interpScreen_tilt_prune α Rv μ ν v0 hu hum, mul_zero] at hne
      exact hne rfl

/-- The successor list of an index screen is uniformly small. -/
lemma zsucc_card_le (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) {sc : GScreen}
    (hsc : sc ∈ scrIndex N S) :
    (zsucc S sc.zlist).card ≤ (tgtUniv N).card := by
  have hacc : ScrAcc S sc := ((mem_scrIndex hN hS).mp hsc).1
  have huniv := mem_screenUniv.mp (hacc.mem_univ hN hS)
  exact Finset.card_le_card (zsucc_subset hN hS huniv.2.1)

/-! ### The assembled ordinary step -/

/-- **The assembled ordinary step** (`thm:psi-step`): every accessible
ordinary
coordinate at height `h + 1` is bounded through its transfer row by
the generic step function evaluated at the running bounds; the row
hypotheses are discharged by the grammar bookkeeping of the accessible
index and the pruning dichotomy. -/
theorem genPsi_step {δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hrefl : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (Tν : ℝ≥0∞)
    (hTν : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-α)) ≤ Tν)
    (h : ℕ) :
    genPsi α Rv μ ν v0 N S (h + 1)
      ≤ genF α δ L K (etaG α Rv μ + phiE α (q μ Rv v0)) Tν S.card
          (genPsi α Rv μ ν v0 N S h)
          (⨆ i, genE α Rv μ ν v0 N S h i) := by
  refine iSup_le fun pp => ?_
  obtain ⟨⟨p1, p2⟩, hpmem⟩ := pp
  have hp : OrdAcc S (p1, p2) := (mem_ordIndex hN hS).mp hpmem
  have hzf := hp.zf
  have hMle : ∀ {s t : Tgt}, OrdAcc S (s, t) →
      interpPhi α Rv μ ν v0 h (s, t) ≤ genPsi α Rv μ ν v0 N S h :=
    fun hst => interpPhi_le_genPsi α Rv μ ν v0 N S hN hS h hst
  have hScr : ∀ {sc : GScreen}, ScrAcc S sc →
      interpScreen α Rv μ ν v0 h sc
        ≤ ⨆ i, genE α Rv μ ν v0 N S h i :=
    fun hsc => interpScreen_le_genE_sup α Rv μ ν v0 N S hN hS hrefl h hsc
  -- the final domination of each row output by the step function
  have hcell_le : cellCB α δ L K (genPsi α Rv μ ν v0 N S h)
      (⨆ i, genE α Rv μ ν v0 N S h i) (⨆ i, genE α Rv μ ν v0 N S h i)
      ≤ genF α δ L K (etaG α Rv μ + phiE α (q μ Rv v0)) Tν S.card
          (genPsi α Rv μ ν v0 N S h)
          (⨆ i, genE α Rv μ ν v0 N S h i) :=
    le_trans le_self_add (le_trans le_add_self le_self_add)
  cases p1 with
  | Fk m => exact hzf.1.elim
  | Z k =>
      cases p2 with
      | Fk m => exact hzf.2.elim
      | Z j =>
          refine le_trans (psiRow_ZZ Rv μ ν v0 hα hδ hL0 hL hK0 hK hsymm
            (hrefl v0) k j h _ _ _ ?_ ?_ ?_) hcell_le
          · intro s t hs ht
            exact ⟨hMle (hp.step (mem_pairSucc.mpr
                ⟨gcomp_mem_tgtSucc_Z hs, gcomp_mem_tgtSucc_Z ht⟩)),
              hMle (hp.swap.step (mem_pairSucc.mpr
                ⟨gcomp_mem_tgtSucc_Z ht, gcomp_mem_tgtSucc_Z hs⟩))⟩
          · intro s t hs ht
            rw [← interpScreen_singleton_none α Rv μ ν v0 h t s]
            exact hScr (scrAcc_seed_of hp
              (Or.inr (gcomp_mem_tgtSucc_Z ht))
              (fun x hx => Finset.mem_union.mpr (Or.inl
                (by rw [Finset.mem_singleton.mp hx]
                    exact gcomp_mem_tgtSucc_Z hs)))
              ⟨s, Finset.mem_singleton_self s⟩ (Or.inl rfl))
          · intro s t t' hs htt'
            rw [← interpScreen_singleton_some α Rv μ ν v0 h s t t']
            have ht : t = gcomp0 j ∨ t = gcomp1 j := by
              rcases htt' with ⟨h1, _⟩ | ⟨h1, _⟩
              · exact Or.inl h1
              · exact Or.inr h1
            have ht' : t' = gcomp0 j ∨ t' = gcomp1 j := by
              rcases htt' with ⟨_, h2⟩ | ⟨_, h2⟩
              · exact Or.inr h2
              · exact Or.inl h2
            exact hScr (scrAcc_seed_of hp
              (Or.inl (gcomp_mem_tgtSucc_Z hs))
              (fun x hx => Finset.mem_union.mpr (Or.inr
                (by rw [Finset.mem_singleton.mp hx]
                    exact gcomp_mem_tgtSucc_Z ht)))
              ⟨t, Finset.mem_singleton_self t⟩
              (Or.inr ⟨t', rfl, Or.inr (gcomp_mem_tgtSucc_Z ht')⟩))
      | F =>
          refine le_trans (psiRow_ZF Rv μ ν v0 hα hδ hL0 hL hK0 hK hsymm
            S hSsupp k h (genPsi α Rv μ ν v0 N S h)
            (⨆ i, genE α Rv μ ν v0 N S h i)
            (⨆ i, genE α Rv μ ν v0 N S h i) Tν hTν ?_ ?_ ?_ ?_ ?_) ?_
          · intro j hj s t hs ht
            exact ⟨hMle (hp.step (mem_pairSucc.mpr
                ⟨gcomp_mem_tgtSucc_Z hs, gcomp_mem_tgtSucc_F hj ht⟩)),
              hMle (hp.swap.step (mem_pairSucc.mpr
                ⟨gcomp_mem_tgtSucc_F hj ht, gcomp_mem_tgtSucc_Z hs⟩))⟩
          · intro j hj s t hs ht
            rw [← interpScreen_singleton_none α Rv μ ν v0 h t s]
            exact hScr (scrAcc_seed_of hp
              (Or.inr (gcomp_mem_tgtSucc_F hj ht))
              (fun x hx => Finset.mem_union.mpr (Or.inl
                (by rw [Finset.mem_singleton.mp hx]
                    exact gcomp_mem_tgtSucc_Z hs)))
              ⟨s, Finset.mem_singleton_self s⟩ (Or.inl rfl))
          · intro j hj s t t' hs htt'
            rw [← interpScreen_singleton_some α Rv μ ν v0 h s t t']
            have ht : t = gcomp0 j ∨ t = gcomp1 j := by
              rcases htt' with ⟨h1, _⟩ | ⟨h1, _⟩
              · exact Or.inl h1
              · exact Or.inr h1
            have ht' : t' = gcomp0 j ∨ t' = gcomp1 j := by
              rcases htt' with ⟨_, h2⟩ | ⟨_, h2⟩
              · exact Or.inr h2
              · exact Or.inl h2
            exact hScr (scrAcc_seed_of hp
              (Or.inl (gcomp_mem_tgtSucc_Z hs))
              (fun x hx => Finset.mem_union.mpr (Or.inr
                (by rw [Finset.mem_singleton.mp hx]
                    exact gcomp_mem_tgtSucc_F hj ht)))
              ⟨t, Finset.mem_singleton_self t⟩
              (Or.inr ⟨t', rfl, Or.inr (gcomp_mem_tgtSucc_F hj ht')⟩))
          · intro j' hj' j hj s t hs ht
            rw [← interpScreen_pair_some α Rv μ ν v0 h s
              (gcomp0 j') (gcomp1 j') t]
            refine hScr (scrAcc_seed_of hp
              (Or.inl (gcomp_mem_tgtSucc_Z hs))
              (fun x hx => Finset.mem_union.mpr (Or.inr ?_))
              ⟨gcomp0 j', Finset.mem_insert_self _ _⟩
              (Or.inr ⟨t, rfl, Or.inr (gcomp_mem_tgtSucc_F hj ht)⟩))
            rcases Finset.mem_insert.mp hx with rfl | hx2
            · exact gcomp_mem_tgtSucc_F hj' (Or.inl rfl)
            · rw [Finset.mem_singleton.mp hx2]
              exact gcomp_mem_tgtSucc_F hj' (Or.inr rfl)
          · intro j' hj' j hj s u t hs hu ht
            rw [← interpScreen_singleton_some α Rv μ ν v0 h s u t]
            exact hScr (scrAcc_seed_of hp
              (Or.inl (gcomp_mem_tgtSucc_Z hs))
              (fun x hx => Finset.mem_union.mpr (Or.inr
                (by rw [Finset.mem_singleton.mp hx]
                    exact gcomp_mem_tgtSucc_F hj' hu)))
              ⟨u, Finset.mem_singleton_self u⟩
              (Or.inr ⟨t, rfl, Or.inr (gcomp_mem_tgtSucc_F hj ht)⟩))
          · rw [genF]
            refine add_le_add (add_le_add le_add_self le_rfl)
              (mul_le_mul_right (mul_le_mul_left le_add_self _) _)
  | F =>
      cases p2 with
      | Fk m => exact hzf.2.elim
      | Z j =>
          refine le_trans (psiRow_FZ Rv μ ν v0 hα hδ hL0 hL hK0 hK hsymm
            S hSsupp j h _ _ _ ?_ ?_ ?_) hcell_le
          · intro k hk s t hs ht
            exact ⟨hMle (hp.step (mem_pairSucc.mpr
                ⟨gcomp_mem_tgtSucc_F hk hs, gcomp_mem_tgtSucc_Z ht⟩)),
              hMle (hp.swap.step (mem_pairSucc.mpr
                ⟨gcomp_mem_tgtSucc_Z ht, gcomp_mem_tgtSucc_F hk hs⟩))⟩
          · intro k hk s t hs ht
            rw [← interpScreen_singleton_none α Rv μ ν v0 h t s]
            exact hScr (scrAcc_seed_of hp
              (Or.inr (gcomp_mem_tgtSucc_Z ht))
              (fun x hx => Finset.mem_union.mpr (Or.inl
                (by rw [Finset.mem_singleton.mp hx]
                    exact gcomp_mem_tgtSucc_F hk hs)))
              ⟨s, Finset.mem_singleton_self s⟩ (Or.inl rfl))
          · intro k hk s t t' hs htt'
            rw [← interpScreen_singleton_some α Rv μ ν v0 h s t t']
            have ht : t = gcomp0 j ∨ t = gcomp1 j := by
              rcases htt' with ⟨h1, _⟩ | ⟨h1, _⟩
              · exact Or.inl h1
              · exact Or.inr h1
            have ht' : t' = gcomp0 j ∨ t' = gcomp1 j := by
              rcases htt' with ⟨_, h2⟩ | ⟨_, h2⟩
              · exact Or.inr h2
              · exact Or.inl h2
            exact hScr (scrAcc_seed_of hp
              (Or.inl (gcomp_mem_tgtSucc_F hk hs))
              (fun x hx => Finset.mem_union.mpr (Or.inr
                (by rw [Finset.mem_singleton.mp hx]
                    exact gcomp_mem_tgtSucc_Z ht)))
              ⟨t, Finset.mem_singleton_self t⟩
              (Or.inr ⟨t', rfl, Or.inr (gcomp_mem_tgtSucc_Z ht')⟩))
      | F =>
          refine le_trans (psiRow_FF Rv μ ν v0 hα hδ hL0 hL hK0 hK hsymm
            S hSsupp h (genPsi α Rv μ ν v0 N S h)
            (⨆ i, genE α Rv μ ν v0 N S h i)
            (⨆ i, genE α Rv μ ν v0 N S h i) Tν hTν ?_ ?_ ?_ ?_ ?_) ?_
          · intro k hk j hj s t hs ht
            exact ⟨hMle (hp.step (mem_pairSucc.mpr
                ⟨gcomp_mem_tgtSucc_F hk hs, gcomp_mem_tgtSucc_F hj ht⟩)),
              hMle (hp.swap.step (mem_pairSucc.mpr
                ⟨gcomp_mem_tgtSucc_F hj ht, gcomp_mem_tgtSucc_F hk hs⟩))⟩
          · intro k hk j hj s t hs ht
            rw [← interpScreen_singleton_none α Rv μ ν v0 h t s]
            exact hScr (scrAcc_seed_of hp
              (Or.inr (gcomp_mem_tgtSucc_F hj ht))
              (fun x hx => Finset.mem_union.mpr (Or.inl
                (by rw [Finset.mem_singleton.mp hx]
                    exact gcomp_mem_tgtSucc_F hk hs)))
              ⟨s, Finset.mem_singleton_self s⟩ (Or.inl rfl))
          · intro k hk j hj s t t' hs htt'
            rw [← interpScreen_singleton_some α Rv μ ν v0 h s t t']
            have ht : t = gcomp0 j ∨ t = gcomp1 j := by
              rcases htt' with ⟨h1, _⟩ | ⟨h1, _⟩
              · exact Or.inl h1
              · exact Or.inr h1
            have ht' : t' = gcomp0 j ∨ t' = gcomp1 j := by
              rcases htt' with ⟨_, h2⟩ | ⟨_, h2⟩
              · exact Or.inr h2
              · exact Or.inl h2
            exact hScr (scrAcc_seed_of hp
              (Or.inl (gcomp_mem_tgtSucc_F hk hs))
              (fun x hx => Finset.mem_union.mpr (Or.inr
                (by rw [Finset.mem_singleton.mp hx]
                    exact gcomp_mem_tgtSucc_F hj ht)))
              ⟨t, Finset.mem_singleton_self t⟩
              (Or.inr ⟨t', rfl, Or.inr (gcomp_mem_tgtSucc_F hj ht')⟩))
          · intro k hk j' hj' j hj s t hs ht
            rw [← interpScreen_pair_some α Rv μ ν v0 h s
              (gcomp0 j') (gcomp1 j') t]
            refine hScr (scrAcc_seed_of hp
              (Or.inl (gcomp_mem_tgtSucc_F hk hs))
              (fun x hx => Finset.mem_union.mpr (Or.inr ?_))
              ⟨gcomp0 j', Finset.mem_insert_self _ _⟩
              (Or.inr ⟨t, rfl, Or.inr (gcomp_mem_tgtSucc_F hj ht)⟩))
            rcases Finset.mem_insert.mp hx with rfl | hx2
            · exact gcomp_mem_tgtSucc_F hj' (Or.inl rfl)
            · rw [Finset.mem_singleton.mp hx2]
              exact gcomp_mem_tgtSucc_F hj' (Or.inr rfl)
          · intro k hk j' hj' j hj s u t hs hu ht
            rw [← interpScreen_singleton_some α Rv μ ν v0 h s u t]
            exact hScr (scrAcc_seed_of hp
              (Or.inl (gcomp_mem_tgtSucc_F hk hs))
              (fun x hx => Finset.mem_union.mpr (Or.inr
                (by rw [Finset.mem_singleton.mp hx]
                    exact gcomp_mem_tgtSucc_F hj' hu)))
              ⟨u, Finset.mem_singleton_self u⟩
              (Or.inr ⟨t, rfl, Or.inr (gcomp_mem_tgtSucc_F hj ht)⟩))
          · rw [genF]
            refine add_le_add (add_le_add le_self_add le_rfl)
              (mul_le_mul_right (mul_le_mul_left le_self_add _) _)

end GraphMarkovMatching
