/-
The assembled screen step of the general-ν block recursion
(`arbitrary_offspring_matching.tex`, `thm:e-step` in `sec:recursion`):
every accessible live screen coordinate at height
`h + 1` steps to the block-matrix action on the running screen vector
plus a uniform inhomogeneity.  The six live cell/normalization cases
dispatch to the certified transfer rows, whose far-root injections and
quadratic charges are collected into the monotone step function
`genG`, and whose successor sums are collected into the block matrix.

* `genG` / `genG_mono`: the screen step function and its monotonicity
  in the two running bounds;
* `rE_v0_ne_zero`: the root degree is positive on the support;
* `genE_step`: the assembled screen step.
-/
import GraphMarkovMatching.Closure.Gen
import GraphMarkovMatching.Rows.EForced
import GraphMarkovMatching.Rows.EFresh

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (ν : PMF ℕ) (v0 : V) (N : ℕ) (S : Finset ℕ)

/-! ### The screen step function -/

/-- The generic screen step function (`def:step-functions`,
`eq:genG`): the far-root mass, the fresh
tilted root mass with its charged pair moment, and the common survivor
charges of the tilted rows, controlled by the root and tilt bounds. -/
noncomputable def genG (α : ℝ) (Tν RT FM FT : ℝ≥0∞) (nA : ℕ)
    (a b : ℝ≥0∞) : ℝ≥0∞ :=
  FM
    + FT * (Tν * (2 * ((1 + ENNReal.ofReal α * a)
        * (1 + ENNReal.ofReal α * a))))
    + (1 + RT * Tν) * (4 * (ENNReal.ofReal α * a * b)
        + 2 * ((nA * b) * (nA * b)))

/-- The screen step function is monotone in the two running bounds. -/
lemma genG_mono (α : ℝ) (Tν RT FM FT : ℝ≥0∞) (nA : ℕ)
    {a a' b b' : ℝ≥0∞} (ha : a ≤ a') (hb : b ≤ b') :
    genG α Tν RT FM FT nA a b ≤ genG α Tν RT FM FT nA a' b' := by
  rw [genG, genG]
  have h1 : 1 + ENNReal.ofReal α * a ≤ 1 + ENNReal.ofReal α * a' :=
    add_le_add le_rfl (mul_le_mul_right ha _)
  refine add_le_add (add_le_add le_rfl ?_) ?_
  · exact mul_le_mul_right (mul_le_mul_right
      (mul_le_mul_right (mul_le_mul' h1 h1) 2) Tν) FT
  · refine mul_le_mul_right (add_le_add ?_ ?_) _
    · exact mul_le_mul_right (mul_le_mul' (mul_le_mul_right ha _) hb) 4
    · exact mul_le_mul_right (mul_le_mul'
        (mul_le_mul_right hb _) (mul_le_mul_right hb _)) 2

/-- The root degree at the root is positive on the support. -/
lemma rE_v0_ne_zero (hrefl : Rv v0 v0) (hpos : (μ v0 : ℝ≥0∞) ≠ 0) :
    rE μ Rv v0 ≠ 0 := fun h0 =>
  hpos (le_antisymm (h0 ▸ le_rE_of_refl hrefl) zero_le)

/-! ### Absorption of the row outputs -/

/-- The unit-normalization output absorbs into the step function and
the matrix action. -/
private lemma genG_absorb_none {α : ℝ} {Tν RT FM FT : ℝ≥0∞}
    {nA nz : ℕ} {a b Eplus CW MV : ℝ≥0∞} (hnA : nz ≤ nA) (hCW4 : 4 ≤ CW)
    (hMV : CW * Eplus ≤ MV) :
    FM + (2 * Eplus + ((nz : ℝ≥0∞) * b) * ((nz : ℝ≥0∞) * b))
      ≤ genG α Tν RT FM FT nA a b + MV := by
  have hnAb : (nz : ℝ≥0∞) * b ≤ (nA : ℝ≥0∞) * b :=
    mul_le_mul_left (Nat.cast_le.mpr hnA) b
  have hone : ∀ x : ℝ≥0∞, x ≤ (1 + RT * Tν) * x := fun x =>
    le_trans (le_of_eq (one_mul x).symm) (mul_le_mul_left le_self_add x)
  have hquad : ((nz : ℝ≥0∞) * b) * ((nz : ℝ≥0∞) * b)
      ≤ (1 + RT * Tν) * (4 * (ENNReal.ofReal α * a * b)
          + 2 * (((nA : ℝ≥0∞) * b) * ((nA : ℝ≥0∞) * b))) :=
    le_trans (mul_le_mul' hnAb hnAb)
      (le_trans (le_trans (le_of_eq (one_mul _).symm)
          (mul_le_mul_left one_le_two _))
        (le_trans le_add_self (hone _)))
  rw [genG]
  calc FM + (2 * Eplus + ((nz : ℝ≥0∞) * b) * ((nz : ℝ≥0∞) * b))
      = (FM + ((nz : ℝ≥0∞) * b) * ((nz : ℝ≥0∞) * b)) + 2 * Eplus := by ring
    _ ≤ (FM + FT * (Tν * (2 * ((1 + ENNReal.ofReal α * a)
            * (1 + ENNReal.ofReal α * a)))))
          + (1 + RT * Tν) * (4 * (ENNReal.ofReal α * a * b)
            + 2 * (((nA : ℝ≥0∞) * b) * ((nA : ℝ≥0∞) * b))) + MV :=
        add_le_add (add_le_add le_self_add hquad)
          (le_trans (mul_le_mul_left
            (le_trans (by norm_num : (2 : ℝ≥0∞) ≤ 4) hCW4) Eplus) hMV)

/-- The forced-normalization output absorbs into the step function and
the matrix action. -/
private lemma genG_absorb_forced {α : ℝ} {Tν RT FM FT : ℝ≥0∞}
    {nA nz : ℕ} {a b Eplus CW MV : ℝ≥0∞} (hnA : nz ≤ nA) (hCW4 : 4 ≤ CW)
    (hMV : CW * Eplus ≤ MV) :
    4 * Eplus + 4 * (ENNReal.ofReal α * a * b)
        + 2 * (((nz : ℝ≥0∞) * b) * ((nz : ℝ≥0∞) * b))
      ≤ genG α Tν RT FM FT nA a b + MV := by
  have hnAb : (nz : ℝ≥0∞) * b ≤ (nA : ℝ≥0∞) * b :=
    mul_le_mul_left (Nat.cast_le.mpr hnA) b
  have hone : ∀ x : ℝ≥0∞, x ≤ (1 + RT * Tν) * x := fun x =>
    le_trans (le_of_eq (one_mul x).symm) (mul_le_mul_left le_self_add x)
  have hcore : 4 * (ENNReal.ofReal α * a * b)
        + 2 * (((nz : ℝ≥0∞) * b) * ((nz : ℝ≥0∞) * b))
      ≤ 4 * (ENNReal.ofReal α * a * b)
        + 2 * (((nA : ℝ≥0∞) * b) * ((nA : ℝ≥0∞) * b)) :=
    add_le_add le_rfl (mul_le_mul_right (mul_le_mul' hnAb hnAb) 2)
  rw [genG]
  calc 4 * Eplus + 4 * (ENNReal.ofReal α * a * b)
        + 2 * (((nz : ℝ≥0∞) * b) * ((nz : ℝ≥0∞) * b))
      = (4 * (ENNReal.ofReal α * a * b)
          + 2 * (((nz : ℝ≥0∞) * b) * ((nz : ℝ≥0∞) * b))) + 4 * Eplus := by
        ring
    _ ≤ (FM + FT * (Tν * (2 * ((1 + ENNReal.ofReal α * a)
            * (1 + ENNReal.ofReal α * a)))))
          + (1 + RT * Tν) * (4 * (ENNReal.ofReal α * a * b)
            + 2 * (((nA : ℝ≥0∞) * b) * ((nA : ℝ≥0∞) * b))) + MV :=
        add_le_add (le_trans (le_trans hcore (hone _)) le_add_self)
          (le_trans (mul_le_mul_left hCW4 Eplus) hMV)

/-- The fresh-normalization output absorbs into the step function and
the matrix action. -/
private lemma genG_absorb_fresh {α : ℝ} {Tν RT FM FT : ℝ≥0∞}
    {nA nz : ℕ} {a b Eplus CW MV : ℝ≥0∞} (hnA : nz ≤ nA)
    (hCWRT : 4 * (RT * Tν) ≤ CW) (hMV : CW * Eplus ≤ MV) :
    FT * (Tν * (2 * ((1 + ENNReal.ofReal α * a)
          * (1 + ENNReal.ofReal α * a))))
        + RT * Tν * (4 * Eplus + 4 * (ENNReal.ofReal α * a * b)
          + 2 * (((nz : ℝ≥0∞) * b) * ((nz : ℝ≥0∞) * b)))
      ≤ genG α Tν RT FM FT nA a b + MV := by
  have hnAb : (nz : ℝ≥0∞) * b ≤ (nA : ℝ≥0∞) * b :=
    mul_le_mul_left (Nat.cast_le.mpr hnA) b
  have hcore : 4 * (ENNReal.ofReal α * a * b)
        + 2 * (((nz : ℝ≥0∞) * b) * ((nz : ℝ≥0∞) * b))
      ≤ 4 * (ENNReal.ofReal α * a * b)
        + 2 * (((nA : ℝ≥0∞) * b) * ((nA : ℝ≥0∞) * b)) :=
    add_le_add le_rfl (mul_le_mul_right (mul_le_mul' hnAb hnAb) 2)
  have hRTν : RT * Tν * (4 * (ENNReal.ofReal α * a * b)
        + 2 * (((nz : ℝ≥0∞) * b) * ((nz : ℝ≥0∞) * b)))
      ≤ (1 + RT * Tν) * (4 * (ENNReal.ofReal α * a * b)
        + 2 * (((nA : ℝ≥0∞) * b) * ((nA : ℝ≥0∞) * b))) :=
    le_trans (mul_le_mul_right hcore (RT * Tν))
      (mul_le_mul_left le_add_self _)
  rw [genG]
  calc FT * (Tν * (2 * ((1 + ENNReal.ofReal α * a)
          * (1 + ENNReal.ofReal α * a))))
        + RT * Tν * (4 * Eplus + 4 * (ENNReal.ofReal α * a * b)
          + 2 * (((nz : ℝ≥0∞) * b) * ((nz : ℝ≥0∞) * b)))
      = (FT * (Tν * (2 * ((1 + ENNReal.ofReal α * a)
            * (1 + ENNReal.ofReal α * a))))
          + RT * Tν * (4 * (ENNReal.ofReal α * a * b)
            + 2 * (((nz : ℝ≥0∞) * b) * ((nz : ℝ≥0∞) * b))))
        + 4 * (RT * Tν) * Eplus := by ring
    _ ≤ (FM + FT * (Tν * (2 * ((1 + ENNReal.ofReal α * a)
            * (1 + ENNReal.ofReal α * a)))))
          + (1 + RT * Tν) * (4 * (ENNReal.ofReal α * a * b)
            + 2 * (((nA : ℝ≥0∞) * b) * ((nA : ℝ≥0∞) * b))) + MV :=
        add_le_add (add_le_add le_add_self hRTν)
          (le_trans (mul_le_mul_left hCWRT Eplus) hMV)

/-! ### The assembled screen step -/

/-- **The assembled screen step** (`thm:e-step`): every accessible
live screen
coordinate at height `h + 1` is bounded through its transfer row by
the step function evaluated at the running bounds plus the
block-matrix action on the running screen vector.  The row hypotheses
are discharged by the grammar bookkeeping of the accessible index and
the pruning dichotomy. -/
theorem genE_step (hα : 1 ≤ α) (hrefl : ∀ v, Rv v v)
    (hN : 2 ≤ N) (hS : ∀ k ∈ S, k ≤ N) (hSne : S.Nonempty)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (hpos : (μ v0 : ℝ≥0∞) ≠ 0)
    (Tν RT FM FT CW : ℝ≥0∞)
    (hTν : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-α)) ≤ Tν)
    (hRT : ∀ v, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    (hFM : (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞)) ≤ FM)
    (hFT : (∑' v, if Rv v v0 then 0
        else (μ v : ℝ≥0∞) * WresD α μ Rv v) ≤ FT)
    (hCW4 : 4 ≤ CW) (hCWRT : 4 * (RT * Tν) ≤ CW)
    (h : ℕ) (i : {sc // sc ∈ scrIndex N S}) :
    genE α Rv μ ν v0 N S (h + 1) i
      ≤ genG α Tν RT FM FT (tgtUniv N).card
          (genPsi α Rv μ ν v0 N S h) (⨆ j, genE α Rv μ ν v0 N S h j)
        + mulVec (accN N S CW) (genE α Rv μ ν v0 N S h) i := by
  obtain ⟨⟨c, z, u⟩, hsc⟩ := i
  have hacc : ScrAcc S ⟨c, z, u⟩ := ((mem_scrIndex hN hS).mp hsc).1
  have hzf3 := hacc.zf
  have hz : z.Nonempty := hacc.nonempty
  have hzfree : ∀ t ∈ z, ∀ m, t ≠ Tgt.Fk m := fun t ht m heq =>
    (heq ▸ hzf3.2.1 t ht).elim
  have hScr : ∀ {sc' : GScreen}, ScrAcc S sc' →
      interpScreen α Rv μ ν v0 h sc'
        ≤ ⨆ j, genE α Rv μ ν v0 N S h j :=
    fun ha => interpScreen_le_genE_sup α Rv μ ν v0 N S hN hS hrefl h ha
  have hMle : ∀ {p : Tgt × Tgt}, OrdAcc S p →
      interpPhi α Rv μ ν v0 h p ≤ genPsi α Rv μ ν v0 N S h :=
    fun hp => interpPhi_le_genPsi α Rv μ ν v0 N S hN hS h hp
  have hEd : ∀ sc' ∈ screenSucc S (⟨c, z, u⟩ : GScreen),
      interpScreen α Rv μ ν v0 h sc'
        ≤ ⨆ j, genE α Rv μ ν v0 N S h j :=
    fun _ hsc' => hScr (hacc.step (screenSucc_subSucc hSne hz hsc'))
  have hMV : CW * (∑ sc' ∈ screenSucc S (⟨c, z, u⟩ : GScreen),
        interpScreen α Rv μ ν v0 h sc')
      ≤ mulVec (accN N S CW) (genE α Rv μ ν v0 N S h) ⟨⟨c, z, u⟩, hsc⟩ :=
    succ_sum_le_mulVec α Rv μ ν v0 N S hN hS hSne hrefl hsc CW h
  have hcard : (zsucc S z).card ≤ (tgtUniv N).card :=
    zsucc_card_le N S hN hS hsc
  cases c with
  | Fk m => exact hzf3.1.elim
  | Z i₀ =>
      cases u with
      | none =>
          refine le_trans (eRowZ_none α Rv μ ν v0 S hSsupp (hrefl v0)
              (rE_v0_ne_zero Rv μ v0 (hrefl v0) hpos) i₀ z hzfree hz h
              (⨆ j, genE α Rv μ ν v0 N S h j) ?_)
            (le_trans le_add_self (genG_absorb_none hcard hCW4 hMV))
          intro t' ht' c' hc'
          rw [screenE_one_eq_zMass,
            ← interpScreen_singleton_none α Rv μ ν v0 h c' t']
          exact hScr (hacc.step ⟨hc', Finset.singleton_subset_iff.mpr ht',
            Finset.singleton_nonempty t', none_mem_normSucc S⟩)
      | some w =>
          cases w with
          | Fk m => exact (hzf3.2.2 _ rfl).elim
          | Z m =>
              refine le_trans (eRowZ_forced α Rv μ ν v0 hα S hSsupp
                  (hrefl v0) (rE_v0_ne_zero Rv μ v0 (hrefl v0) hpos)
                  i₀ z hzfree hz m h (genPsi α Rv μ ν v0 N S h)
                  (⨆ j, genE α Rv μ ν v0 N S h j) ?_ ?_ hEd)
                (genG_absorb_forced hcard hCW4 hMV)
              · intro c' hc' w' hw'
                exact hMle ((hacc.norm_pair (Tgt.Z m) rfl).step
                  (mem_pairSucc.mpr ⟨hc', hw'⟩))
              · intro t' ht' c' hc' w' hw'
                rw [← interpScreen_singleton_some α Rv μ ν v0 h c' t' w']
                exact hScr (hacc.step
                  ⟨hc', Finset.singleton_subset_iff.mpr ht',
                    Finset.singleton_nonempty t', some_mem_normSucc hw'⟩)
          | F =>
              refine le_trans (eRowZ_fresh α Rv μ ν v0 hα S hSsupp
                  (hrefl v0) (rE_v0_ne_zero Rv μ v0 (hrefl v0) hpos)
                  i₀ z hzfree hz h (genPsi α Rv μ ν v0 N S h)
                  (⨆ j, genE α Rv μ ν v0 N S h j) Tν RT
                  (hRT v0 (hrefl v0)) hTν ?_ ?_ hEd)
                (le_trans le_add_self (genG_absorb_fresh hcard hCWRT hMV))
              · intro j hj c' hc' w' hw'
                exact hMle ((hacc.norm_pair Tgt.F rfl).step
                  (mem_pairSucc.mpr
                    ⟨hc', Finset.mem_biUnion.mpr ⟨j, hj, hw'⟩⟩))
              · intro j hj t' ht' c' hc' w' hw'
                rw [← interpScreen_singleton_some α Rv μ ν v0 h c' t' w']
                exact hScr (hacc.step
                  ⟨hc', Finset.singleton_subset_iff.mpr ht',
                    Finset.singleton_nonempty t',
                    some_mem_normSucc (Finset.mem_biUnion.mpr
                      ⟨j, hj, hw'⟩)⟩)
  | F =>
      cases u with
      | none =>
          refine le_trans (eRowF_none α Rv μ ν v0 S hSsupp hpos z hzfree h
              (⨆ j, genE α Rv μ ν v0 N S h j) FM hFM ?_)
            (genG_absorb_none hcard hCW4 hMV)
          intro t' ht' k hk c' hc'
          rw [screenE_one_eq_zMass,
            ← interpScreen_singleton_none α Rv μ ν v0 h c' t']
          exact hScr (hacc.step ⟨Finset.mem_biUnion.mpr ⟨k, hk, hc'⟩,
            Finset.singleton_subset_iff.mpr ht',
            Finset.singleton_nonempty t', none_mem_normSucc S⟩)
      | some w =>
          cases w with
          | Fk m => exact (hzf3.2.2 _ rfl).elim
          | Z m =>
              refine le_trans (eRowF_forced α Rv μ ν v0 hα S hSsupp hpos
                  z hzfree m h (genPsi α Rv μ ν v0 N S h)
                  (⨆ j, genE α Rv μ ν v0 N S h j) ?_ ?_ hEd)
                (genG_absorb_forced hcard hCW4 hMV)
              · intro k hk c' hc' w' hw'
                exact hMle ((hacc.norm_pair (Tgt.Z m) rfl).step
                  (mem_pairSucc.mpr
                    ⟨Finset.mem_biUnion.mpr ⟨k, hk, hc'⟩, hw'⟩))
              · intro t' ht' k hk c' hc' w' hw'
                rw [← interpScreen_singleton_some α Rv μ ν v0 h c' t' w']
                exact hScr (hacc.step
                  ⟨Finset.mem_biUnion.mpr ⟨k, hk, hc'⟩,
                    Finset.singleton_subset_iff.mpr ht',
                    Finset.singleton_nonempty t', some_mem_normSucc hw'⟩)
          | F =>
              refine le_trans (eRowF_fresh α Rv μ ν v0 hα S hSsupp hpos
                  z hzfree h (genPsi α Rv μ ν v0 N S h)
                  (⨆ j, genE α Rv μ ν v0 N S h j) Tν RT FT hRT hTν hFT
                  ?_ ?_ hEd)
                (genG_absorb_fresh hcard hCWRT hMV)
              · intro k hk j hj c' hc' w' hw'
                exact hMle ((hacc.norm_pair Tgt.F rfl).step
                  (mem_pairSucc.mpr
                    ⟨Finset.mem_biUnion.mpr ⟨k, hk, hc'⟩,
                      Finset.mem_biUnion.mpr ⟨j, hj, hw'⟩⟩))
              · intro j hj t' ht' k hk c' hc' w' hw'
                rw [← interpScreen_singleton_some α Rv μ ν v0 h c' t' w']
                exact hScr (hacc.step
                  ⟨Finset.mem_biUnion.mpr ⟨k, hk, hc'⟩,
                    Finset.singleton_subset_iff.mpr ht',
                    Finset.singleton_nonempty t',
                    some_mem_normSucc (Finset.mem_biUnion.mpr
                      ⟨j, hj, hw'⟩)⟩)

end GraphMarkovMatching
