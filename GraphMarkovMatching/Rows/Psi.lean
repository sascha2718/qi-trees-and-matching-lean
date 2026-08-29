/-
The general-ν ordinary rows of the transfer step
(`arbitrary_offspring_matching.tex`, `sec:rows`, ordinary
outputs at arbitrary finitely supported offspring law), in
hypothesis-parameterized form: every height-`h` quantity on the right
side is bounded through an explicit hypothesis (`≤ M` for ordinary
coordinates, `≤ Z` for zero masses, `≤ E'` for screens) or is an
explicit closed-form constant.

* `gcomp0` / `gcomp1`: the two product components of a counter cell,
  following the kernel; `Xi_eq_prod` writes every `Ξ_k` as a product of
  interpreted formal targets, and `gpair_eq_pair` identifies the cascade
  pair with the component pair;
* `cellCB`: the common square-cell bound, the output shape of the
  one-cell ledger row with the four screens collapsed to `4·E'`;
* `psiRow_square` / `psiRow_ZZ`: the square cell and the forced-forced
  row;
* `oneSided_charge_le` / `oneSidedBound`: the mixture one-sided
  conversion: the pair-level one-sided screen of the fresh-target
  mixture, after the pointwise mixture tilt bound (the
  `ν_*^{-5/2}`-type insertion of `thm:mixture-tilt`), factorizes over
  the charged support into screens and moments;
* `psiRow_ZF` / `psiRow_FZ` / `psiRow_FF`: the forced-fresh,
  fresh-forced and fresh-fresh rows.
-/
import GraphMarkovMatching.Process.Descent
import GraphMarkovMatching.Process.Coordinates

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (ν : PMF ℕ)
  (v0 : V)

/-! ### The grammar bridge -/

/-- The first product component of a counter cell. -/
def gcomp0 : ℕ → Tgt := fun k =>
  if 4 ≤ k then Tgt.Z (k / 2) else if k = 3 then Tgt.Z 2 else Tgt.F

/-- The second product component of a counter cell. -/
def gcomp1 : ℕ → Tgt := fun k =>
  if 4 ≤ k then Tgt.Z (k - k / 2) else if k = 3 then Tgt.F else Tgt.F

/-- Every counter cell is the product of its two interpreted
components. -/
lemma Xi_eq_prod (k h : ℕ) :
    Xi μ ν v0 k h
      = prodPMF (interpT μ ν v0 h (gcomp0 k))
          (interpT μ ν v0 h (gcomp1 k)) := by
  by_cases h4 : 4 ≤ k
  · rw [Xi_of_four_le μ ν v0 h4 h]
    rw [show gcomp0 k = Tgt.Z (k / 2) from if_pos h4,
      show gcomp1 k = Tgt.Z (k - k / 2) from if_pos h4, interpT, interpT]
  · by_cases h3 : k = 3
    · subst h3
      rw [Xi_three μ ν v0 h]
      rw [show gcomp0 3 = Tgt.Z 2 from by rw [gcomp0]; norm_num,
        show gcomp1 3 = Tgt.F from by rw [gcomp1]; norm_num, interpT,
        interpT]
    · rw [Xi_of_le_two μ ν v0 (by omega) h]
      rw [show gcomp0 k = Tgt.F from by rw [gcomp0, if_neg h4, if_neg h3],
        show gcomp1 k = Tgt.F from by rw [gcomp1, if_neg h4, if_neg h3],
        interpT]

/-- Both components lie in the cascade pair. -/
lemma gcomp_mem_gpair (k : ℕ) :
    gcomp0 k ∈ gpair k ∧ gcomp1 k ∈ gpair k := by
  rw [gcomp0, gcomp1, gpair]
  split_ifs with h4 h3 <;> simp

/-- The cascade pair is exactly the component pair. -/
lemma gpair_eq_pair (k : ℕ) : gpair k = {gcomp0 k, gcomp1 k} := by
  rw [gcomp0, gcomp1, gpair]
  split_ifs with h4 h3 <;> simp

/-! ### The common square-cell bound -/

/-- The common square-cell bound: the output shape of the one-cell
ledger row `PhiDres_square_le` with the four resolved screens collapsed
to `4·E'`. -/
noncomputable def cellCB (α δ L K : ℝ) (M Z E' : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * L + 2 * (1 + δ) * K) * M
    + ENNReal.ofReal (2 * L * chordConst α + 20 + 2 * (1 + δ⁻¹) * α ^ 2)
      * M ^ 2
    + ENNReal.ofReal (2 * (1 + δ)) * Z
    + 4 * E' * (1 + ENNReal.ofReal α * M)

/-- The square-cell bound is monotone in all three arguments. -/
lemma cellCB_mono (α δ L K : ℝ) {M M' Z Z' E E'' : ℝ≥0∞}
    (hM : M ≤ M') (hZ : Z ≤ Z') (hE : E ≤ E'') :
    cellCB α δ L K M Z E ≤ cellCB α δ L K M' Z' E'' := by
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
  · exact mul_le_mul_right hM _
  · exact mul_le_mul_right (pow_le_pow_left' hM 2) _
  · exact mul_le_mul_right hZ _
  · exact mul_le_mul' (mul_le_mul_right hE 4)
      (add_le_add le_rfl (mul_le_mul_right hM _))

/-! ### The square row -/

/-- **The square cell** (`sec:rows`, `thm:psirow-square`): the restricted square coordinate `Φres(Ξ_k → Ξ_j; R^□)`
is bounded by `cellCB` from the componentwise ordinary bounds `≤ M`, the
zero masses `≤ Z`, and the resolved screens `≤ E'`. -/
lemma psiRow_square {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (k j h : ℕ) (M Z E' : ℝ≥0∞)
    (hM : ∀ s t : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      interpPhi α Rv μ ν v0 h (s, t) ≤ M
        ∧ interpPhi α Rv μ ν v0 h (t, s) ≤ M)
    (hZ : ∀ s t : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      zMass (interpT μ ν v0 h t) (interpT μ ν v0 h s)
        (fullSim (labRel Rv) h) ≤ Z)
    (hE : ∀ s t t' : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      ((t = gcomp0 j ∧ t' = gcomp1 j) ∨ (t = gcomp1 j ∧ t' = gcomp0 j)) →
      screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
        [interpT μ ν v0 h t]
        (WresD α (interpT μ ν v0 h t') (fullSim (labRel Rv) h)) ≤ E') :
    PhiDres α (Xi μ ν v0 k h) (Xi μ ν v0 j h)
        (SquareRel (fullSim (labRel Rv) h))
      ≤ cellCB α δ L K M Z E' := by
  rw [Xi_eq_prod μ ν v0 k h, Xi_eq_prod μ ν v0 j h]
  refine le_trans (PhiDres_square_le hα hδ hL0 hL hK0 hK
    (interpT μ ν v0 h (gcomp0 k)) (interpT μ ν v0 h (gcomp1 k))
    (interpT μ ν v0 h (gcomp0 j)) (interpT μ ν v0 h (gcomp1 j))
    (fullSim (labRel Rv) h)
    (fullSim_symm (labRel Rv) (fun a b hab => hsymm a.1 b.1 hab) h) M Z
    (hM (gcomp0 k) (gcomp0 j) (Or.inl rfl) (Or.inl rfl)).1
    (hM (gcomp0 k) (gcomp1 j) (Or.inl rfl) (Or.inr rfl)).1
    (hM (gcomp1 k) (gcomp0 j) (Or.inr rfl) (Or.inl rfl)).1
    (hM (gcomp1 k) (gcomp1 j) (Or.inr rfl) (Or.inr rfl)).1
    (hM (gcomp0 k) (gcomp0 j) (Or.inl rfl) (Or.inl rfl)).2
    (hM (gcomp1 k) (gcomp0 j) (Or.inr rfl) (Or.inl rfl)).2
    (hM (gcomp0 k) (gcomp1 j) (Or.inl rfl) (Or.inr rfl)).2
    (hM (gcomp1 k) (gcomp1 j) (Or.inr rfl) (Or.inr rfl)).2
    (hZ (gcomp0 k) (gcomp0 j) (Or.inl rfl) (Or.inl rfl))
    (hZ (gcomp1 k) (gcomp0 j) (Or.inr rfl) (Or.inl rfl))
    (hZ (gcomp0 k) (gcomp1 j) (Or.inl rfl) (Or.inr rfl))
    (hZ (gcomp1 k) (gcomp1 j) (Or.inr rfl) (Or.inr rfl))) ?_
  rw [cellCB]
  refine add_le_add le_rfl ?_
  refine le_trans (mul_le_mul_left
    (add_le_add (add_le_add (add_le_add
      (hE (gcomp0 k) (gcomp0 j) (gcomp1 j) (Or.inl rfl) (Or.inl ⟨rfl, rfl⟩))
      (hE (gcomp0 k) (gcomp1 j) (gcomp0 j) (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩)))
      (hE (gcomp1 k) (gcomp0 j) (gcomp1 j) (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩)))
      (hE (gcomp1 k) (gcomp1 j) (gcomp0 j) (Or.inr rfl) (Or.inr ⟨rfl, rfl⟩)))
    (1 + ENNReal.ofReal α * M)) (le_of_eq (by ring))

/-! ### The forced-forced row -/

/-- **The forced-forced row** (`eq:row-ZZ`; `s = Z_k`, `t = Z_j`): the
height-`(h+1)` ordinary coordinate is exactly the height-`h` square
cell, which `psiRow_square` bounds by `cellCB`. -/
lemma psiRow_ZZ {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hrefl : Rv v0 v0)
    (k j h : ℕ) (M Z E' : ℝ≥0∞)
    (hM : ∀ s t : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      interpPhi α Rv μ ν v0 h (s, t) ≤ M
        ∧ interpPhi α Rv μ ν v0 h (t, s) ≤ M)
    (hZ : ∀ s t : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      zMass (interpT μ ν v0 h t) (interpT μ ν v0 h s)
        (fullSim (labRel Rv) h) ≤ Z)
    (hE : ∀ s t t' : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      ((t = gcomp0 j ∧ t' = gcomp1 j) ∨ (t = gcomp1 j ∧ t' = gcomp0 j)) →
      screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
        [interpT μ ν v0 h t]
        (WresD α (interpT μ ν v0 h t') (fullSim (labRel Rv) h)) ≤ E') :
    interpPhi α Rv μ ν v0 (h + 1) (Tgt.Z k, Tgt.Z j)
      ≤ cellCB α δ L K M Z E' := by
  show PhiDres α (Zlaw μ ν v0 k (h + 1)) (Zlaw μ ν v0 j (h + 1))
      (fullSim (labRel Rv) (h + 1)) ≤ cellCB α δ L K M Z E'
  rw [PhiDres_Zlaw_Zlaw_succ α Rv μ ν v0 hrefl k j h]
  exact psiRow_square Rv μ ν v0 hα hδ hL0 hL hK0 hK hsymm k j h M Z E'
    hM hZ hE

/-! ### The one-sided mixture bound -/

/-- The one-sided mixture bound: the closed form of the pair-level
one-sided screen of the fresh-target mixture after the pointwise
mixture tilt bound.  `Tν` bounds the charged tilt sum
`∑_j ν_j^{-α}`, `cS` is the size of the support, and each
`(j', j)`-cell factorizes into screens and moments. -/
noncomputable def oneSidedBound (α : ℝ) (Tν : ℝ≥0∞) (cS : ℕ)
    (M E' : ℝ≥0∞) : ℝ≥0∞ :=
  Tν * (cS * (4 * E' * (1 + ENNReal.ofReal α * M) + 4 * (E' * E')))

/-- The one-sided bound is monotone in the moment and screen
arguments. -/
lemma oneSidedBound_mono (α : ℝ) (Tν : ℝ≥0∞) (cS : ℕ)
    {M M' E E'' : ℝ≥0∞} (hM : M ≤ M') (hE : E ≤ E'') :
    oneSidedBound α Tν cS M E ≤ oneSidedBound α Tν cS M' E'' := by
  refine mul_le_mul_right (mul_le_mul_right (add_le_add ?_ ?_) _) _
  · exact mul_le_mul' (mul_le_mul_right hE 4)
      (add_le_add le_rfl (mul_le_mul_right hM _))
  · exact mul_le_mul_right (mul_le_mul' hE hE) 4

/-! ### The one-sided tilt mass -/

/-- The per-`(j', j)` cell of the one-sided tilt mass: the `j'`-dead
indicated, `Ξ_j`-tilted mass of the source cell factorizes through the
survivor split and the Hall factorization into screens and moments. -/
private lemma oneSided_cell_le {α : ℝ} (hα : 1 ≤ α) (k j j' h : ℕ)
    (M E' : ℝ≥0∞)
    (hmom : ∀ s t : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      interpPhi α Rv μ ν v0 h (s, t) ≤ M)
    (hP : ∀ s t : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
        [interpT μ ν v0 h (gcomp0 j'), interpT μ ν v0 h (gcomp1 j')]
        (WresD α (interpT μ ν v0 h t) (fullSim (labRel Rv) h)) ≤ E')
    (hS : ∀ s u t : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      (u = gcomp0 j' ∨ u = gcomp1 j') → (t = gcomp0 j ∨ t = gcomp1 j) →
      screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
        [interpT μ ν v0 h u]
        (WresD α (interpT μ ν v0 h t) (fullSim (labRel Rv) h)) ≤ E') :
    ∑' xp, Xi μ ν v0 k h xp
        * ((if ν j' ≠ 0 ∧ rE (Xi μ ν v0 j' h)
              (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (Xi μ ν v0 j h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
      ≤ 4 * E' * (1 + ENNReal.ofReal α * M) + 4 * (E' * E') := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hmomW : ∀ s t : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      (∑' x, interpT μ ν v0 h s x
        * WresD α (interpT μ ν v0 h t) (fullSim (labRel Rv) h) x)
      ≤ 1 + ENNReal.ofReal α * M := fun s t hs ht =>
    le_trans (tsum_WresD_le hα _ _ _)
      (add_le_add le_rfl (mul_le_mul_right (hmom s t hs ht) _))
  have hsplit : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      Xi μ ν v0 k h xp
        * ((if ν j' ≠ 0 ∧ rE (Xi μ ν v0 j' h)
              (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (Xi μ ν v0 j h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
      ≤ Xi μ ν v0 k h xp
          * ((if rE (Xi μ ν v0 j' h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * (WresD α (interpT μ ν v0 h (gcomp0 j))
                  (fullSim (labRel Rv) h) xp.1
              * WresD α (interpT μ ν v0 h (gcomp1 j))
                  (fullSim (labRel Rv) h) xp.2))
        + Xi μ ν v0 k h xp
          * ((if rE (Xi μ ν v0 j' h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * (WresD α (interpT μ ν v0 h (gcomp1 j))
                  (fullSim (labRel Rv) h) xp.1
              * WresD α (interpT μ ν v0 h (gcomp0 j))
                  (fullSim (labRel Rv) h) xp.2)) := by
    intro xp
    have hW : WresD α (Xi μ ν v0 j h)
          (SquareRel (fullSim (labRel Rv) h)) xp
        ≤ WresD α (interpT μ ν v0 h (gcomp0 j))
              (fullSim (labRel Rv) h) xp.1
            * WresD α (interpT μ ν v0 h (gcomp1 j))
                (fullSim (labRel Rv) h) xp.2
          + WresD α (interpT μ ν v0 h (gcomp1 j))
              (fullSim (labRel Rv) h) xp.1
            * WresD α (interpT μ ν v0 h (gcomp0 j))
                (fullSim (labRel Rv) h) xp.2 := by
      rw [Xi_eq_prod μ ν v0 j h]
      exact WresD_square_le_sum hα0 _ _ _ xp
    by_cases hc : ν j' ≠ 0 ∧ rE (Xi μ ν v0 j' h)
        (SquareRel (fullSim (labRel Rv) h)) xp = 0
    · rw [if_pos hc, if_pos hc.2]
      simp only [one_mul]
      refine le_trans (mul_le_mul_right hW (Xi μ ν v0 k h xp))
        (le_of_eq (by ring))
    · rw [if_neg hc, zero_mul, mul_zero]
      exact zero_le
  have hfac1 : (∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      Xi μ ν v0 k h xp
        * ((if rE (Xi μ ν v0 j' h)
              (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
          * (WresD α (interpT μ ν v0 h (gcomp0 j))
                (fullSim (labRel Rv) h) xp.1
            * WresD α (interpT μ ν v0 h (gcomp1 j))
                (fullSim (labRel Rv) h) xp.2)))
      ≤ E' * (1 + ENNReal.ofReal α * M)
        + (1 + ENNReal.ofReal α * M) * E' + E' * E' + E' * E' := by
    rw [Xi_eq_prod μ ν v0 k h, Xi_eq_prod μ ν v0 j' h]
    refine le_trans (deadScreen_factorize
      (interpT μ ν v0 h (gcomp0 k)) (interpT μ ν v0 h (gcomp1 k))
      (interpT μ ν v0 h (gcomp0 j')) (interpT μ ν v0 h (gcomp1 j'))
      (fullSim (labRel Rv) h)
      (WresD α (interpT μ ν v0 h (gcomp0 j)) (fullSim (labRel Rv) h))
      (WresD α (interpT μ ν v0 h (gcomp1 j)) (fullSim (labRel Rv) h))) ?_
    exact add_le_add (add_le_add (add_le_add
      (mul_le_mul' (hP (gcomp0 k) (gcomp0 j) (Or.inl rfl) (Or.inl rfl))
        (hmomW (gcomp1 k) (gcomp1 j) (Or.inr rfl) (Or.inr rfl)))
      (mul_le_mul' (hmomW (gcomp0 k) (gcomp0 j) (Or.inl rfl) (Or.inl rfl))
        (hP (gcomp1 k) (gcomp1 j) (Or.inr rfl) (Or.inr rfl))))
      (mul_le_mul' (hS (gcomp0 k) (gcomp0 j') (gcomp0 j)
          (Or.inl rfl) (Or.inl rfl) (Or.inl rfl))
        (hS (gcomp1 k) (gcomp0 j') (gcomp1 j)
          (Or.inr rfl) (Or.inl rfl) (Or.inr rfl))))
      (mul_le_mul' (hS (gcomp0 k) (gcomp1 j') (gcomp0 j)
          (Or.inl rfl) (Or.inr rfl) (Or.inl rfl))
        (hS (gcomp1 k) (gcomp1 j') (gcomp1 j)
          (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)))
  have hfac2 : (∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
      Xi μ ν v0 k h xp
        * ((if rE (Xi μ ν v0 j' h)
              (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
          * (WresD α (interpT μ ν v0 h (gcomp1 j))
                (fullSim (labRel Rv) h) xp.1
            * WresD α (interpT μ ν v0 h (gcomp0 j))
                (fullSim (labRel Rv) h) xp.2)))
      ≤ E' * (1 + ENNReal.ofReal α * M)
        + (1 + ENNReal.ofReal α * M) * E' + E' * E' + E' * E' := by
    rw [Xi_eq_prod μ ν v0 k h, Xi_eq_prod μ ν v0 j' h]
    refine le_trans (deadScreen_factorize
      (interpT μ ν v0 h (gcomp0 k)) (interpT μ ν v0 h (gcomp1 k))
      (interpT μ ν v0 h (gcomp0 j')) (interpT μ ν v0 h (gcomp1 j'))
      (fullSim (labRel Rv) h)
      (WresD α (interpT μ ν v0 h (gcomp1 j)) (fullSim (labRel Rv) h))
      (WresD α (interpT μ ν v0 h (gcomp0 j)) (fullSim (labRel Rv) h))) ?_
    exact add_le_add (add_le_add (add_le_add
      (mul_le_mul' (hP (gcomp0 k) (gcomp1 j) (Or.inl rfl) (Or.inr rfl))
        (hmomW (gcomp1 k) (gcomp0 j) (Or.inr rfl) (Or.inl rfl)))
      (mul_le_mul' (hmomW (gcomp0 k) (gcomp1 j) (Or.inl rfl) (Or.inr rfl))
        (hP (gcomp1 k) (gcomp0 j) (Or.inr rfl) (Or.inl rfl))))
      (mul_le_mul' (hS (gcomp0 k) (gcomp0 j') (gcomp1 j)
          (Or.inl rfl) (Or.inl rfl) (Or.inr rfl))
        (hS (gcomp1 k) (gcomp0 j') (gcomp0 j)
          (Or.inr rfl) (Or.inl rfl) (Or.inl rfl))))
      (mul_le_mul' (hS (gcomp0 k) (gcomp1 j') (gcomp1 j)
          (Or.inl rfl) (Or.inr rfl) (Or.inr rfl))
        (hS (gcomp1 k) (gcomp1 j') (gcomp0 j)
          (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)))
  refine le_trans (ENNReal.tsum_le_tsum hsplit) ?_
  rw [ENNReal.tsum_add]
  exact le_trans (add_le_add hfac1 hfac2) (le_of_eq (by ring))

/-- Exchange of a charged tilt sum against a weighted bound: the
weighted, indicated form of the pointwise mixture tilt bound. -/
private lemma tilt_exchange {α : ℝ} (w c W : ℝ≥0∞) (g : ℕ → ℝ≥0∞)
    (hW : W ≤ ∑' i, (if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-α) * g i)) :
    w * (c * W)
      ≤ ∑' i, (if (ν i : ℝ≥0∞) = 0 then 0
          else (ν i : ℝ≥0∞) ^ (-α) * (w * (c * g i))) := by
  calc w * (c * W)
      ≤ w * (c * ∑' i, (if (ν i : ℝ≥0∞) = 0 then 0
          else (ν i : ℝ≥0∞) ^ (-α) * g i)) :=
        mul_le_mul_right (mul_le_mul_right hW _) _
    _ = ∑' i, w * (c * (if (ν i : ℝ≥0∞) = 0 then 0
          else (ν i : ℝ≥0∞) ^ (-α) * g i)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ = ∑' i, (if (ν i : ℝ≥0∞) = 0 then 0
          else (ν i : ℝ≥0∞) ^ (-α) * (w * (c * g i))) :=
        tsum_congr fun i => by
          by_cases hi0 : (ν i : ℝ≥0∞) = 0
          · rw [if_pos hi0, if_pos hi0, mul_zero, mul_zero]
          · rw [if_neg hi0, if_neg hi0]; ring

/-- **The mixture one-sided conversion** (`sec:rows`, `thm:one-sided`): the pair-level one-sided screen of the fresh-target mixture,
normalized by the mixture degree, is bounded by `oneSidedBound`.  The
existential dead indicator splits over the charged support, the mixture
tilt converts pointwise into charged component tilts weighted by
`ν_j^{-α}` (the `ν_*^{-5/2}`-type insertion), and each `(j', j)`-cell
factorizes into screens and moments. -/
lemma oneSided_charge_le {α : ℝ} (hα : 1 ≤ α) (S : Finset ℕ)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S) (k h : ℕ)
    (M E' Tν : ℝ≥0∞)
    (hTν : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-α)) ≤ Tν)
    (hMomΦ : ∀ j ∈ S, ∀ s t : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      interpPhi α Rv μ ν v0 h (s, t) ≤ M)
    (hscrP : ∀ j' ∈ S, ∀ j ∈ S, ∀ s t : Tgt,
      (s = gcomp0 k ∨ s = gcomp1 k) → (t = gcomp0 j ∨ t = gcomp1 j) →
      screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
        [interpT μ ν v0 h (gcomp0 j'), interpT μ ν v0 h (gcomp1 j')]
        (WresD α (interpT μ ν v0 h t) (fullSim (labRel Rv) h)) ≤ E')
    (hscrS : ∀ j' ∈ S, ∀ j ∈ S, ∀ s u t : Tgt,
      (s = gcomp0 k ∨ s = gcomp1 k) → (u = gcomp0 j' ∨ u = gcomp1 j') →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
        [interpT μ ν v0 h u]
        (WresD α (interpT μ ν v0 h t) (fullSim (labRel Rv) h)) ≤ E') :
    ∑' xp, Xi μ ν v0 k h xp
        * ((if ∃ i, ν i ≠ 0 ∧ rE (Xi μ ν v0 i h)
              (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
      ≤ oneSidedBound α Tν S.card M E' := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hUj : ∀ j' ∈ S,
      (∑' xp, Xi μ ν v0 k h xp
        * ((if ν j' ≠ 0 ∧ rE (Xi μ ν v0 j' h)
              (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp))
      ≤ Tν * (4 * E' * (1 + ENNReal.ofReal α * M) + 4 * (E' * E')) := by
    intro j' hj'
    have hpt : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
        Xi μ ν v0 k h xp
          * ((if ν j' ≠ 0 ∧ rE (Xi μ ν v0 j' h)
                (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
            * WresD α (XiBar μ ν v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp)
        ≤ ∑' i, (if (ν i : ℝ≥0∞) = 0 then 0
            else (ν i : ℝ≥0∞) ^ (-α)
              * (Xi μ ν v0 k h xp
                * ((if ν j' ≠ 0 ∧ rE (Xi μ ν v0 j' h)
                      (SquareRel (fullSim (labRel Rv) h)) xp = 0
                    then 1 else 0)
                  * WresD α (Xi μ ν v0 i h)
                      (SquareRel (fullSim (labRel Rv) h)) xp))) :=
      fun xp => tilt_exchange ν (Xi μ ν v0 k h xp) _
        (WresD α (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp)
        (fun i => WresD α (Xi μ ν v0 i h)
          (SquareRel (fullSim (labRel Rv) h)) xp)
        (WresD_XiBar_le_sum α Rv μ ν v0 hα0 h xp)
    have hterm : ∀ i : ℕ,
        (∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
          (if (ν i : ℝ≥0∞) = 0 then 0
            else (ν i : ℝ≥0∞) ^ (-α)
              * (Xi μ ν v0 k h xp
                * ((if ν j' ≠ 0 ∧ rE (Xi μ ν v0 j' h)
                      (SquareRel (fullSim (labRel Rv) h)) xp = 0
                    then 1 else 0)
                  * WresD α (Xi μ ν v0 i h)
                      (SquareRel (fullSim (labRel Rv) h)) xp))))
        ≤ (if (ν i : ℝ≥0∞) = 0 then 0 else (ν i : ℝ≥0∞) ^ (-α))
          * (4 * E' * (1 + ENNReal.ofReal α * M) + 4 * (E' * E')) := by
      intro i
      by_cases hi0 : (ν i : ℝ≥0∞) = 0
      · exact le_trans (le_of_eq (tsum_congr fun xp => if_pos hi0))
          (le_trans (le_of_eq tsum_zero) zero_le)
      · have hiS : i ∈ S := (hSsupp i).mp hi0
        rw [if_neg hi0]
        refine le_trans (le_of_eq (tsum_congr fun xp => if_neg hi0)) ?_
        rw [ENNReal.tsum_mul_left]
        exact mul_le_mul_right
          (oneSided_cell_le Rv μ ν v0 hα k i j' h M E'
            (hMomΦ i hiS) (hscrP j' hj' i hiS) (hscrS j' hj' i hiS)) _
    refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
    rw [ENNReal.tsum_comm]
    refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
    rw [ENNReal.tsum_mul_right]
    exact mul_le_mul_left hTν _
  have hvanish : ∀ j' ∉ S,
      (∑' xp, Xi μ ν v0 k h xp
        * ((if ν j' ≠ 0 ∧ rE (Xi μ ν v0 j' h)
              (SquareRel (fullSim (labRel Rv) h)) xp = 0 then 1 else 0)
          * WresD α (XiBar μ ν v0 h)
              (SquareRel (fullSim (labRel Rv) h)) xp)) = 0 := by
    intro j' hj'
    have hz : (ν j' : ℝ≥0∞) = 0 := by
      by_contra hne
      exact hj' ((hSsupp j').mp hne)
    refine ENNReal.tsum_eq_zero.mpr fun xp => ?_
    rw [if_neg (fun hc => hc.1 hz), zero_mul, mul_zero]
  refine le_trans (pairScreen_exists_le Rv μ ν v0 k h
    (WresD α (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)))) ?_
  rw [tsum_eq_sum hvanish]
  refine le_trans (Finset.sum_le_sum hUj) ?_
  rw [Finset.sum_const, nsmul_eq_mul, oneSidedBound]
  exact le_of_eq (by ring)

/-! ### The mixture rows -/

/-- Collapse of a `ν`-average against a uniform bound on the charged
support: uncharged indices vanish, and the charged weights sum to at
most one. -/
private lemma nu_avg_le (S : Finset ℕ)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S)
    (f : ℕ → ℝ≥0∞) (C : ℝ≥0∞) (hf : ∀ i ∈ S, f i ≤ C) :
    (∑' i, ν i * f i) ≤ C := by
  have hvan : ∀ i ∉ S, (ν i : ℝ≥0∞) * f i = 0 := by
    intro i hi
    have hz : (ν i : ℝ≥0∞) = 0 := by
      by_contra hne
      exact hi ((hSsupp i).mp hne)
    rw [hz, zero_mul]
  rw [tsum_eq_sum hvan]
  calc ∑ i ∈ S, ν i * f i
      ≤ ∑ i ∈ S, ν i * C :=
        Finset.sum_le_sum fun i hi => mul_le_mul_right (hf i hi) _
    _ = (∑ i ∈ S, (ν i : ℝ≥0∞)) * C := by rw [Finset.sum_mul]
    _ ≤ 1 * C := mul_le_mul_left
        (le_trans (ENNReal.sum_le_tsum S) (le_of_eq ν.tsum_coe)) _
    _ = C := one_mul C

/-- **The forced-fresh row** (`eq:row-ZF`; `s = Z_k`, `t = F`): the split bound at
the root `v0`, the mixture of square cells collapsed over the charged
support, and the one-sided tilt mass. -/
lemma psiRow_ZF {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (S : Finset ℕ)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S) (k h : ℕ)
    (M Z E' Tν : ℝ≥0∞)
    (hTν : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-α)) ≤ Tν)
    (hM : ∀ j ∈ S, ∀ s t : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      interpPhi α Rv μ ν v0 h (s, t) ≤ M
        ∧ interpPhi α Rv μ ν v0 h (t, s) ≤ M)
    (hZ : ∀ j ∈ S, ∀ s t : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      zMass (interpT μ ν v0 h t) (interpT μ ν v0 h s)
        (fullSim (labRel Rv) h) ≤ Z)
    (hE : ∀ j ∈ S, ∀ s t t' : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      ((t = gcomp0 j ∧ t' = gcomp1 j) ∨ (t = gcomp1 j ∧ t' = gcomp0 j)) →
      screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
        [interpT μ ν v0 h t]
        (WresD α (interpT μ ν v0 h t') (fullSim (labRel Rv) h)) ≤ E')
    (hscrP : ∀ j' ∈ S, ∀ j ∈ S, ∀ s t : Tgt,
      (s = gcomp0 k ∨ s = gcomp1 k) → (t = gcomp0 j ∨ t = gcomp1 j) →
      screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
        [interpT μ ν v0 h (gcomp0 j'), interpT μ ν v0 h (gcomp1 j')]
        (WresD α (interpT μ ν v0 h t) (fullSim (labRel Rv) h)) ≤ E')
    (hscrS : ∀ j' ∈ S, ∀ j ∈ S, ∀ s u t : Tgt,
      (s = gcomp0 k ∨ s = gcomp1 k) → (u = gcomp0 j' ∨ u = gcomp1 j') →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
        [interpT μ ν v0 h u]
        (WresD α (interpT μ ν v0 h t) (fullSim (labRel Rv) h)) ≤ E') :
    interpPhi α Rv μ ν v0 (h + 1) (Tgt.Z k, Tgt.F)
      ≤ phiE α (q μ Rv v0)
        + (cellCB α δ L K M Z E' + oneSidedBound α Tν S.card M E')
        + ENNReal.ofReal (2 * α)
          * (phiE α (q μ Rv v0)
            * (cellCB α δ L K M Z E'
              + oneSidedBound α Tν S.card M E')) := by
  have hmid : PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
      (SquareRel (fullSim (labRel Rv) h))
      ≤ cellCB α δ L K M Z E' + oneSidedBound α Tν S.card M E' := by
    refine le_trans (PhiDres_Xi_XiBar_le α Rv μ ν v0 hα k h)
      (add_le_add ?_ ?_)
    · exact nu_avg_le ν S hSsupp _ _ (fun j hj =>
        psiRow_square Rv μ ν v0 hα hδ hL0 hL hK0 hK hsymm k j h M Z E'
          (hM j hj) (hZ j hj) (hE j hj))
    · exact oneSided_charge_le Rv μ ν v0 hα S hSsupp k h M E' Tν hTν
        (fun j hj s t hs ht => (hM j hj s t hs ht).1) hscrP hscrS
  show PhiDres α (Zlaw μ ν v0 k (h + 1)) (Tlaw μ ν v0 (h + 1))
      (fullSim (labRel Rv) (h + 1)) ≤ _
  refine le_trans (PhiDres_Zlaw_Tlaw_succ α Rv μ ν v0 hα k h) ?_
  exact add_le_add (add_le_add le_rfl hmid)
    (mul_le_mul_right (mul_le_mul_right hmid _) _)

/-- **The fresh-forced row** (`eq:row-FZ`; `s = F`, `t = Z_j`): the cascade mixture
collapses over the charged support into a single square-cell bound. -/
lemma psiRow_FZ {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (S : Finset ℕ)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S) (j h : ℕ)
    (M Z E' : ℝ≥0∞)
    (hM : ∀ k ∈ S, ∀ s t : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      interpPhi α Rv μ ν v0 h (s, t) ≤ M
        ∧ interpPhi α Rv μ ν v0 h (t, s) ≤ M)
    (hZ : ∀ k ∈ S, ∀ s t : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      zMass (interpT μ ν v0 h t) (interpT μ ν v0 h s)
        (fullSim (labRel Rv) h) ≤ Z)
    (hE : ∀ k ∈ S, ∀ s t t' : Tgt, (s = gcomp0 k ∨ s = gcomp1 k) →
      ((t = gcomp0 j ∧ t' = gcomp1 j) ∨ (t = gcomp1 j ∧ t' = gcomp0 j)) →
      screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
        [interpT μ ν v0 h t]
        (WresD α (interpT μ ν v0 h t') (fullSim (labRel Rv) h)) ≤ E') :
    interpPhi α Rv μ ν v0 (h + 1) (Tgt.F, Tgt.Z j)
      ≤ cellCB α δ L K M Z E' := by
  show PhiDres α (Tlaw μ ν v0 (h + 1)) (Zlaw μ ν v0 j (h + 1))
      (fullSim (labRel Rv) (h + 1)) ≤ _
  refine le_trans (PhiDres_Tlaw_Zlaw_succ α Rv μ ν v0 j h) ?_
  exact nu_avg_le ν S hSsupp _ _ (fun k hk =>
    psiRow_square Rv μ ν v0 hα hδ hL0 hL hK0 hK hsymm k j h M Z E'
      (hM k hk) (hZ k hk) (hE k hk))

/-- **The fresh-fresh row** (`eq:row-FF`; `s = F`, `t = F`): the root integrates to
the graph potential `η`, each charged cascade cell contributes one mixture
bound `cellCB + oneSidedBound`, and the cross term is quadratic. -/
lemma psiRow_FF {α δ L K : ℝ} (hα : 1 ≤ α) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hL : ∀ t : ℝ, 0 ≤ t → t / (1 + t) ^ α ≤ L)
    (hK0 : 0 < K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * (1 - t) ^ α ≤ K)
    (hsymm : ∀ a b, Rv a b → Rv b a) (S : Finset ℕ)
    (hSsupp : ∀ i : ℕ, (ν i : ℝ≥0∞) ≠ 0 ↔ i ∈ S) (h : ℕ)
    (M Z E' Tν : ℝ≥0∞)
    (hTν : (∑' i, if (ν i : ℝ≥0∞) = 0 then 0
        else (ν i : ℝ≥0∞) ^ (-α)) ≤ Tν)
    (hM : ∀ k ∈ S, ∀ j ∈ S, ∀ s t : Tgt,
      (s = gcomp0 k ∨ s = gcomp1 k) → (t = gcomp0 j ∨ t = gcomp1 j) →
      interpPhi α Rv μ ν v0 h (s, t) ≤ M
        ∧ interpPhi α Rv μ ν v0 h (t, s) ≤ M)
    (hZ : ∀ k ∈ S, ∀ j ∈ S, ∀ s t : Tgt,
      (s = gcomp0 k ∨ s = gcomp1 k) → (t = gcomp0 j ∨ t = gcomp1 j) →
      zMass (interpT μ ν v0 h t) (interpT μ ν v0 h s)
        (fullSim (labRel Rv) h) ≤ Z)
    (hE : ∀ k ∈ S, ∀ j ∈ S, ∀ s t t' : Tgt,
      (s = gcomp0 k ∨ s = gcomp1 k) →
      ((t = gcomp0 j ∧ t' = gcomp1 j) ∨ (t = gcomp1 j ∧ t' = gcomp0 j)) →
      screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
        [interpT μ ν v0 h t]
        (WresD α (interpT μ ν v0 h t') (fullSim (labRel Rv) h)) ≤ E')
    (hscrP : ∀ k ∈ S, ∀ j' ∈ S, ∀ j ∈ S, ∀ s t : Tgt,
      (s = gcomp0 k ∨ s = gcomp1 k) → (t = gcomp0 j ∨ t = gcomp1 j) →
      screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
        [interpT μ ν v0 h (gcomp0 j'), interpT μ ν v0 h (gcomp1 j')]
        (WresD α (interpT μ ν v0 h t) (fullSim (labRel Rv) h)) ≤ E')
    (hscrS : ∀ k ∈ S, ∀ j' ∈ S, ∀ j ∈ S, ∀ s u t : Tgt,
      (s = gcomp0 k ∨ s = gcomp1 k) → (u = gcomp0 j' ∨ u = gcomp1 j') →
      (t = gcomp0 j ∨ t = gcomp1 j) →
      screenE (interpT μ ν v0 h s) (fullSim (labRel Rv) h)
        [interpT μ ν v0 h u]
        (WresD α (interpT μ ν v0 h t) (fullSim (labRel Rv) h)) ≤ E') :
    interpPhi α Rv μ ν v0 (h + 1) (Tgt.F, Tgt.F)
      ≤ etaG α Rv μ
        + (cellCB α δ L K M Z E' + oneSidedBound α Tν S.card M E')
        + ENNReal.ofReal (2 * α)
          * (etaG α Rv μ
            * (cellCB α δ L K M Z E'
              + oneSidedBound α Tν S.card M E')) := by
  have hmix : (∑' k, ν k * PhiDres α (Xi μ ν v0 k h) (XiBar μ ν v0 h)
      (SquareRel (fullSim (labRel Rv) h)))
      ≤ cellCB α δ L K M Z E' + oneSidedBound α Tν S.card M E' := by
    refine nu_avg_le ν S hSsupp _ _ (fun k hk => ?_)
    refine le_trans (PhiDres_Xi_XiBar_le α Rv μ ν v0 hα k h)
      (add_le_add ?_ ?_)
    · exact nu_avg_le ν S hSsupp _ _ (fun j hj =>
        psiRow_square Rv μ ν v0 hα hδ hL0 hL hK0 hK hsymm k j h M Z E'
          (hM k hk j hj) (hZ k hk j hj) (hE k hk j hj))
    · exact oneSided_charge_le Rv μ ν v0 hα S hSsupp k h M E' Tν hTν
        (fun j hj s t hs ht => (hM k hk j hj s t hs ht).1)
        (hscrP k hk) (hscrS k hk)
  show PhiDres α (Tlaw μ ν v0 (h + 1)) (Tlaw μ ν v0 (h + 1))
      (fullSim (labRel Rv) (h + 1)) ≤ _
  refine le_trans (PhiDres_Tlaw_Tlaw_succ α Rv μ ν v0 hα h) ?_
  exact add_le_add (add_le_add le_rfl hmix)
    (mul_le_mul_right (mul_le_mul_right hmix _) _)

end GraphMarkovMatching
