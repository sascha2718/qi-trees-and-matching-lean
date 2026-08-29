/-
The fresh-source screen rows of the general-νR transfer lemma
(`arbitrary_offspring_matching.tex`, `thm:screen-rows` in `sec:rows`,
at the fresh source cell `F`): the height-`(h+1)` interpreted
screen with source `F` is a `freshQ`-mixture over root states, and the
mixture splits into far-root injections through the normalization
tilts and near-root successor charges through the Hall
factorization.

* `crossInterpScreen_fresh_split`: the root decomposition: the fresh source
  law is a mixture, so the screen is the `freshQ`-average of per-root
  screens (`screenE_bind_left`);
* `crossScreen_cell_step`: at a near root the per-root screen descends to
  the pair-level dead event of the member pairs (`memInd_branch_iff`);
* `crossCell_factor`: the near-root Hall factorization: the indicated,
  componentwise-tilted pair mass splits into full-list screens times
  moments plus a product of summed singleton screens
  (`hallFactorize` at the member pairs of the zero list);
* `crossERowF_none` / `crossERowF_forced` / `crossERowF_fresh`: the three norm
  conversions: the unit tilt (far mass bounded by the uncharged root
  mass), the forced tilt (far roots vanish through
  `WresD_Zlaw_succ_branch`), and the fresh tilt (far roots inject into
  the fresh-tilted root mass, near roots contribute the charged tilt sum).
-/
import GraphMarkovMatching.Archive.VaryingCrossERowCore

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (νL νR : PMF ℕ)
  (v0 : V)

/-! ### Elementary helpers -/

/-- At a root compatible with `v0` the root degree is charged as soon
as `v0` is. -/
private lemma rE_ne_zero_of_near (hpos : (μ v0 : ℝ≥0∞) ≠ 0) {v : V}
    (hv : Rv v v0) : rE μ Rv v ≠ 0 := by
  intro h0
  have hle : (μ v0 : ℝ≥0∞) ≤ rE μ Rv v := by
    rw [rE]
    exact le_trans (le_of_eq (if_pos hv).symm) (ENNReal.le_tsum v0)
  rw [h0] at hle
  exact hpos (le_antisymm hle zero_le)

/-- The zero-event indicator is at most one. -/
private lemma screenInd_le_one {X : Type} (R : X → X → Prop)
    (zs : List (PMF X)) (x : X) : screenInd R zs x ≤ 1 := by
  rw [screenInd]
  split_ifs <;> simp

/-- A unit-tilted screen is a subprobability. -/
private lemma screenE_one_le_one {X : Type} (ρs : PMF X)
    (R : X → X → Prop) (zs : List (PMF X)) :
    screenE ρs R zs (fun _ => 1) ≤ 1 := by
  rw [screenE]
  calc ∑' x, ρs x * screenInd R zs x * 1
      ≤ ∑' x, ρs x := ENNReal.tsum_le_tsum fun x => by
        rw [mul_one]
        exact le_trans (mul_le_mul_right (screenInd_le_one R zs x) _)
          (le_of_eq (mul_one _))
    _ = 1 := ρs.tsum_coe

/-- Interpreted screens with the unit normalization, unfolded. -/
private lemma crossInterpScreen_none_eq (c : Tgt) (z' : Finset Tgt) (h : ℕ) :
    crossInterpScreen α Rv μ νL νR v0 h ⟨c, z', none⟩
      = screenE (interpT μ νL v0 h c) (fullSim (labRel Rv) h)
          ((z'.toList).map (interpT μ νR v0 h)) (fun _ => 1) := rfl

/-- Interpreted screens with a target normalization, unfolded. -/
private lemma crossInterpScreen_some_eq (c : Tgt) (z' : Finset Tgt) (w : Tgt)
    (h : ℕ) :
    crossInterpScreen α Rv μ νL νR v0 h ⟨c, z', some w⟩
      = screenE (interpT μ νL v0 h c) (fullSim (labRel Rv) h)
          ((z'.toList).map (interpT μ νR v0 h))
          (WresD α (interpT μ νR v0 h w) (fullSim (labRel Rv) h)) := rfl

/-! ### The root decomposition -/

/-- **The root decomposition** (`sec:rows`, fresh screen rows): the
fresh source law is the `freshQ`-mixture of the per-root process laws,
so the interpreted screen is the corresponding mixture of per-root
screens. -/
lemma crossInterpScreen_fresh_split (z : Finset Tgt) (u : Option Tgt) (h : ℕ) :
    crossInterpScreen α Rv μ νL νR v0 (h + 1) ⟨Tgt.F, z, u⟩
      = ∑' s : V × ℕ, freshQ μ νL s
          * screenE (muM (varyK μ νL v0) s (h + 1))
              (fullSim (labRel Rv) (h + 1))
              ((z.toList).map (interpT μ νR v0 (h + 1)))
              (interpNorm α Rv μ νR v0 (h + 1) u) := by
  show screenE ((freshQ μ νL).bind fun s => muM (varyK μ νL v0) s (h + 1))
      (fullSim (labRel Rv) (h + 1)) ((z.toList).map (interpT μ νR v0 (h + 1)))
      (interpNorm α Rv μ νR v0 (h + 1) u) = _
  exact screenE_bind_left _ _ _ _ _

/-- The per-root screen as a pair-level sum below the branch point. -/
private lemma crossScreenE_branch_eq (v : V) (k h : ℕ)
    (zs : List (PMF (FullLab (V × ℕ) (h + 1))))
    (g : FullLab (V × ℕ) (h + 1) → ℝ≥0∞) :
    screenE (muM (varyK μ νL v0) (v, k) (h + 1))
        (fullSim (labRel Rv) (h + 1)) zs g
      = ∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
          Xi μ νL v0 k h xp
            * (screenInd (fullSim (labRel Rv) (h + 1)) zs (branch (v, k) xp)
              * g (branch (v, k) xp)) := by
  rw [screenE,
    tsum_congr fun x => mul_assoc (muM (varyK μ νL v0) (v, k) (h + 1) x)
      (screenInd (fullSim (labRel Rv) (h + 1)) zs x) (g x),
    muM_varyK_succ μ νL v0 v k h]
  exact tsum_map_mul _ _ _

/-! ### The near-root descent -/

/-- **The near-root change of variables** (`sec:rows`, fresh screen
rows): at a compatible charged root, the per-root screen equals the
pair-level mass of the joint dead event of the member pairs, tilted by
the normalization at the branch point. -/
lemma crossScreen_cell_step (SL SR : Finset ℕ)
    (hRsupp : ∀ j : ℕ, (νR j : ℝ≥0∞) ≠ 0 ↔ j ∈ SR)
    {v : V} (hv0 : Rv v v0) (hvpos : rE μ Rv v ≠ 0) (k h : ℕ)
    (z : Finset Tgt) (hzf : ∀ t ∈ z, ∀ m, t ≠ Tgt.Fk m) (u : Option Tgt) :
    screenE (muM (varyK μ νL v0) (v, k) (h + 1))
        (fullSim (labRel Rv) (h + 1))
        ((z.toList).map (interpT μ νR v0 (h + 1)))
        (interpNorm α Rv μ νR v0 (h + 1) u)
      = ∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
          Xi μ νL v0 k h xp
            * ((if ∀ p ∈ memPairs μ νR v0 SR h z,
                  rE (prodPMF p.1 p.2)
                    (SquareRel (fullSim (labRel Rv) h)) xp = 0
                then (1 : ℝ≥0∞) else 0)
              * interpNorm α Rv μ νR v0 (h + 1) u (branch (v, k) xp)) := by
  have _SL := SL
  rw [crossScreenE_branch_eq Rv μ νL v0 v k h _ _]
  refine tsum_congr fun xp => ?_
  rw [screenInd,
    if_congr (memInd_branch_iff μ νR v0 Rv SR hRsupp hv0 hvpos k h z hzf xp)
      rfl rfl]

/-! ### The near-root Hall factorization -/

/-- **The near-root cell workhorse** (`sec:rows`, fresh screen
rows): the indicated, componentwise-tilted pair mass at a counter-`k`
cell splits into two full-list successor screens times moments plus a
product of summed singleton screens, by the Hall factorization at
the member pairs of the zero list. -/
private lemma crossCell_factor (SL SR : Finset ℕ) (k h : ℕ) (z : Finset Tgt)
    (G₀ G₁ : FullLab (V × ℕ) h → ℝ≥0∞) :
    ∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
        Xi μ νL v0 k h xp
          * ((if ∀ p ∈ memPairs μ νR v0 SR h z,
                rE (prodPMF p.1 p.2)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then (1 : ℝ≥0∞) else 0)
            * (G₀ xp.1 * G₁ xp.2))
      ≤ screenE (interpT μ νL v0 h (gcomp0 k)) (fullSim (labRel Rv) h)
            (((zsucc SR z).toList).map (interpT μ νR v0 h)) G₀
          * (∑' x, interpT μ νL v0 h (gcomp1 k) x * G₁ x)
        + (∑' x, interpT μ νL v0 h (gcomp0 k) x * G₀ x)
          * screenE (interpT μ νL v0 h (gcomp1 k)) (fullSim (labRel Rv) h)
              (((zsucc SR z).toList).map (interpT μ νR v0 h)) G₁
        + ((((zsucc SR z).toList).map (interpT μ νR v0 h)).map fun ρ =>
              screenE (interpT μ νL v0 h (gcomp0 k))
                (fullSim (labRel Rv) h) [ρ] G₀).sum
          * ((((zsucc SR z).toList).map (interpT μ νR v0 h)).map fun ρ' =>
              screenE (interpT μ νL v0 h (gcomp1 k))
                (fullSim (labRel Rv) h) [ρ'] G₁).sum := by
  have _SL := SL
  simp only [Xi_eq_prod μ νL v0 k h]
  exact hallFactorize _ _ _ _ _ (memPairs_mem μ νR v0 SR h z)
    (memPairs_cov μ νR v0 SR h z) G₀ G₁

/-- One order of the survivor split, resolved: the Hall factorization
with `W`-tilts toward a target pair `(a, b)`, the screens absorbed into
the successor sum and the screen bound `E'`, the moments into
`1 + α·M`, and the quadratic term into the counted singleton bound. -/
private lemma crossCell_W_order (SL SR : Finset ℕ) (hα : 1 ≤ α) (k h : ℕ)
    (z : Finset Tgt) (a b : Tgt) (sc : GScreen) (M E' : ℝ≥0∞)
    (hm0 : (⟨gcomp0 k, zsucc SR z, some a⟩ : GScreen) ∈ crossScreenSucc SL SR sc)
    (hm1 : (⟨gcomp1 k, zsucc SR z, some b⟩ : GScreen) ∈ crossScreenSucc SL SR sc)
    (hE : ∀ sc' ∈ crossScreenSucc SL SR sc, crossInterpScreen α Rv μ νL νR v0 h sc' ≤ E')
    (hmom0 : PhiDres α (interpT μ νL v0 h (gcomp0 k))
      (interpT μ νR v0 h a) (fullSim (labRel Rv) h) ≤ M)
    (hmom1 : PhiDres α (interpT μ νL v0 h (gcomp1 k))
      (interpT μ νR v0 h b) (fullSim (labRel Rv) h) ≤ M)
    (hsng0 : ∀ t' ∈ zsucc SR z,
      screenE (interpT μ νL v0 h (gcomp0 k)) (fullSim (labRel Rv) h)
        [interpT μ νR v0 h t']
        (WresD α (interpT μ νR v0 h a) (fullSim (labRel Rv) h)) ≤ E')
    (hsng1 : ∀ t' ∈ zsucc SR z,
      screenE (interpT μ νL v0 h (gcomp1 k)) (fullSim (labRel Rv) h)
        [interpT μ νR v0 h t']
        (WresD α (interpT μ νR v0 h b) (fullSim (labRel Rv) h)) ≤ E') :
    ∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
        Xi μ νL v0 k h xp
          * ((if ∀ p ∈ memPairs μ νR v0 SR h z,
                rE (prodPMF p.1 p.2)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then (1 : ℝ≥0∞) else 0)
            * (WresD α (interpT μ νR v0 h a) (fullSim (labRel Rv) h) xp.1
              * WresD α (interpT μ νR v0 h b) (fullSim (labRel Rv) h) xp.2))
      ≤ 2 * (∑ sc' ∈ crossScreenSucc SL SR sc, crossInterpScreen α Rv μ νL νR v0 h sc')
        + 2 * (ENNReal.ofReal α * M * E')
        + ((zsucc SR z).card * E') * ((zsucc SR z).card * E') := by
  refine le_trans (crossCell_factor Rv μ νL νR v0 SL SR k h z
    (WresD α (interpT μ νR v0 h a) (fullSim (labRel Rv) h))
    (WresD α (interpT μ νR v0 h b) (fullSim (labRel Rv) h))) ?_
  set Ss := ∑ sc' ∈ crossScreenSucc SL SR sc, crossInterpScreen α Rv μ νL νR v0 h sc'
    with hSs
  have hscrA : screenE (interpT μ νL v0 h (gcomp0 k)) (fullSim (labRel Rv) h)
      (((zsucc SR z).toList).map (interpT μ νR v0 h))
      (WresD α (interpT μ νR v0 h a) (fullSim (labRel Rv) h))
      = crossInterpScreen α Rv μ νL νR v0 h ⟨gcomp0 k, zsucc SR z, some a⟩ :=
    (crossInterpScreen_some_eq α Rv μ νL νR v0 (gcomp0 k) (zsucc SR z) a h).symm
  have hscrB : screenE (interpT μ νL v0 h (gcomp1 k)) (fullSim (labRel Rv) h)
      (((zsucc SR z).toList).map (interpT μ νR v0 h))
      (WresD α (interpT μ νR v0 h b) (fullSim (labRel Rv) h))
      = crossInterpScreen α Rv μ νL νR v0 h ⟨gcomp1 k, zsucc SR z, some b⟩ :=
    (crossInterpScreen_some_eq α Rv μ νL νR v0 (gcomp1 k) (zsucc SR z) b h).symm
  have hmomA : (∑' x, interpT μ νL v0 h (gcomp0 k) x
      * WresD α (interpT μ νR v0 h a) (fullSim (labRel Rv) h) x)
      ≤ 1 + ENNReal.ofReal α * M :=
    le_trans (tsum_WresD_le hα _ _ _)
      (add_le_add le_rfl (mul_le_mul_right hmom0 _))
  have hmomB : (∑' x, interpT μ νL v0 h (gcomp1 k) x
      * WresD α (interpT μ νR v0 h b) (fullSim (labRel Rv) h) x)
      ≤ 1 + ENNReal.ofReal α * M :=
    le_trans (tsum_WresD_le hα _ _ _)
      (add_le_add le_rfl (mul_le_mul_right hmom1 _))
  have hlin : ∀ (scr : ℝ≥0∞), scr ≤ Ss → scr ≤ E' →
      scr * (1 + ENNReal.ofReal α * M)
        ≤ Ss + ENNReal.ofReal α * M * E' := by
    intro scr hSb hEs
    calc scr * (1 + ENNReal.ofReal α * M)
        = scr + scr * (ENNReal.ofReal α * M) := by ring
      _ ≤ Ss + E' * (ENNReal.ofReal α * M) :=
          add_le_add hSb (mul_le_mul_left hEs _)
      _ = Ss + ENNReal.ofReal α * M * E' := by ring
  have hquad0 : ((((zsucc SR z).toList).map (interpT μ νR v0 h)).map fun ρ =>
      screenE (interpT μ νL v0 h (gcomp0 k)) (fullSim (labRel Rv) h) [ρ]
        (WresD α (interpT μ νR v0 h a) (fullSim (labRel Rv) h))).sum
      ≤ (zsucc SR z).card * E' := by
    refine le_trans (list_map_sum_le _ _ E' fun ρ hρ => ?_) ?_
    · obtain ⟨t', ht', hρt⟩ := List.mem_map.mp hρ
      rw [← hρt]
      exact hsng0 t' (Finset.mem_toList.mp ht')
    · rw [zsucc_map_length μ νR v0 SR h z]
  have hquad1 : ((((zsucc SR z).toList).map (interpT μ νR v0 h)).map fun ρ' =>
      screenE (interpT μ νL v0 h (gcomp1 k)) (fullSim (labRel Rv) h) [ρ']
        (WresD α (interpT μ νR v0 h b) (fullSim (labRel Rv) h))).sum
      ≤ (zsucc SR z).card * E' := by
    refine le_trans (list_map_sum_le _ _ E' fun ρ hρ => ?_) ?_
    · obtain ⟨t', ht', hρt⟩ := List.mem_map.mp hρ
      rw [← hρt]
      exact hsng1 t' (Finset.mem_toList.mp ht')
    · rw [zsucc_map_length μ νR v0 SR h z]
  have hT1 : screenE (interpT μ νL v0 h (gcomp0 k)) (fullSim (labRel Rv) h)
      (((zsucc SR z).toList).map (interpT μ νR v0 h))
      (WresD α (interpT μ νR v0 h a) (fullSim (labRel Rv) h))
      * (∑' x, interpT μ νL v0 h (gcomp1 k) x
          * WresD α (interpT μ νR v0 h b) (fullSim (labRel Rv) h) x)
      ≤ Ss + ENNReal.ofReal α * M * E' := by
    rw [hscrA]
    refine le_trans (mul_le_mul' le_rfl hmomB) ?_
    exact hlin _ (Finset.single_le_sum (fun _ _ => zero_le) hm0)
      (hE _ hm0)
  have hT2 : (∑' x, interpT μ νL v0 h (gcomp0 k) x
        * WresD α (interpT μ νR v0 h a) (fullSim (labRel Rv) h) x)
      * screenE (interpT μ νL v0 h (gcomp1 k)) (fullSim (labRel Rv) h)
          (((zsucc SR z).toList).map (interpT μ νR v0 h))
          (WresD α (interpT μ νR v0 h b) (fullSim (labRel Rv) h))
      ≤ Ss + ENNReal.ofReal α * M * E' := by
    rw [hscrB]
    refine le_trans (mul_le_mul' hmomA le_rfl) ?_
    rw [mul_comm]
    exact hlin _ (Finset.single_le_sum (fun _ _ => zero_le) hm1)
      (hE _ hm1)
  refine le_trans (add_le_add (add_le_add hT1 hT2)
    (mul_le_mul' hquad0 hquad1)) (le_of_eq (by ring))

/-- Distributing a two-term pointwise bound over a weighted, indicated
sum. -/
private lemma crossTsum_ind_split {Y : Type} (ρs : PMF Y)
    (c W P Q : Y → ℝ≥0∞) (hW : ∀ y, W y ≤ P y + Q y) :
    ∑' y, ρs y * (c y * W y)
      ≤ (∑' y, ρs y * (c y * P y)) + ∑' y, ρs y * (c y * Q y) := by
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun y => ?_
  calc ρs y * (c y * W y)
      ≤ ρs y * (c y * (P y + Q y)) :=
        mul_le_mul_right (mul_le_mul_right (hW y) _) _
    _ = ρs y * (c y * P y) + ρs y * (c y * Q y) := by ring

/-- The full square cell of the fresh screen rows: the survivor split
of the `Ξ_j`-tilt into the two orders, each resolved by
`crossCell_W_order`. -/
private lemma crossCell_W_pair (SL SR : Finset ℕ) (hα : 1 ≤ α) (k h : ℕ)
    (z : Finset Tgt) (j : ℕ) (sc : GScreen) (M E' : ℝ≥0∞)
    (hm00 : (⟨gcomp0 k, zsucc SR z, some (gcomp0 j)⟩ : GScreen)
      ∈ crossScreenSucc SL SR sc)
    (hm11 : (⟨gcomp1 k, zsucc SR z, some (gcomp1 j)⟩ : GScreen)
      ∈ crossScreenSucc SL SR sc)
    (hm01 : (⟨gcomp0 k, zsucc SR z, some (gcomp1 j)⟩ : GScreen)
      ∈ crossScreenSucc SL SR sc)
    (hm10 : (⟨gcomp1 k, zsucc SR z, some (gcomp0 j)⟩ : GScreen)
      ∈ crossScreenSucc SL SR sc)
    (hE : ∀ sc' ∈ crossScreenSucc SL SR sc, crossInterpScreen α Rv μ νL νR v0 h sc' ≤ E')
    (hmom : ∀ c' ∈ gpair k, ∀ w' ∈ gpair j,
      PhiDres α (interpT μ νL v0 h c') (interpT μ νR v0 h w')
        (fullSim (labRel Rv) h) ≤ M)
    (hsng : ∀ t' ∈ zsucc SR z, ∀ c' ∈ gpair k, ∀ w' ∈ gpair j,
      screenE (interpT μ νL v0 h c') (fullSim (labRel Rv) h)
        [interpT μ νR v0 h t']
        (WresD α (interpT μ νR v0 h w') (fullSim (labRel Rv) h)) ≤ E') :
    ∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
        Xi μ νL v0 k h xp
          * ((if ∀ p ∈ memPairs μ νR v0 SR h z,
                rE (prodPMF p.1 p.2)
                  (SquareRel (fullSim (labRel Rv) h)) xp = 0
              then (1 : ℝ≥0∞) else 0)
            * WresD α (Xi μ νR v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp)
      ≤ 4 * (∑ sc' ∈ crossScreenSucc SL SR sc, crossInterpScreen α Rv μ νL νR v0 h sc')
        + 4 * (ENNReal.ofReal α * M * E')
        + 2 * (((zsucc SR z).card * E') * ((zsucc SR z).card * E')) := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hsplit := crossTsum_ind_split (Xi μ νL v0 k h)
    (fun xp => if ∀ p ∈ memPairs μ νR v0 SR h z,
        rE (prodPMF p.1 p.2) (SquareRel (fullSim (labRel Rv) h)) xp = 0
      then (1 : ℝ≥0∞) else 0)
    (WresD α (Xi μ νR v0 j h) (SquareRel (fullSim (labRel Rv) h)))
    (fun xp => WresD α (interpT μ νR v0 h (gcomp0 j))
        (fullSim (labRel Rv) h) xp.1
      * WresD α (interpT μ νR v0 h (gcomp1 j)) (fullSim (labRel Rv) h) xp.2)
    (fun xp => WresD α (interpT μ νR v0 h (gcomp1 j))
        (fullSim (labRel Rv) h) xp.1
      * WresD α (interpT μ νR v0 h (gcomp0 j)) (fullSim (labRel Rv) h) xp.2)
    (fun xp => by
      rw [Xi_eq_prod μ νR v0 j h]
      exact WresD_square_le_sum hα0 _ _ _ xp)
  refine le_trans hsplit ?_
  have h1 := crossCell_W_order α Rv μ νL νR v0 SL SR hα k h z
    (gcomp0 j) (gcomp1 j)
    sc M E' hm00 hm11 hE
    (hmom _ (gcomp_mem_gpair k).1 _ (gcomp_mem_gpair j).1)
    (hmom _ (gcomp_mem_gpair k).2 _ (gcomp_mem_gpair j).2)
    (fun t' ht' => hsng t' ht' _ (gcomp_mem_gpair k).1
      _ (gcomp_mem_gpair j).1)
    (fun t' ht' => hsng t' ht' _ (gcomp_mem_gpair k).2
      _ (gcomp_mem_gpair j).2)
  have h2 := crossCell_W_order α Rv μ νL νR v0 SL SR hα k h z
    (gcomp1 j) (gcomp0 j)
    sc M E' hm01 hm10 hE
    (hmom _ (gcomp_mem_gpair k).1 _ (gcomp_mem_gpair j).2)
    (hmom _ (gcomp_mem_gpair k).2 _ (gcomp_mem_gpair j).1)
    (fun t' ht' => hsng t' ht' _ (gcomp_mem_gpair k).1
      _ (gcomp_mem_gpair j).2)
    (fun t' ht' => hsng t' ht' _ (gcomp_mem_gpair k).2
      _ (gcomp_mem_gpair j).1)
  exact le_trans (add_le_add h1 h2) (le_of_eq (by ring))

/-! ### The charged tilt exchange -/

/-- **The mixture tilt exchange**: a weighted sum against the fresh
mixture tilt is at most `TνR` times any uniform bound on the charged
component sums (the `νR_*^{-α}` insertion of `thm:mixture-tilt`, in
integrated form). -/
private lemma crossTsum_XiBar_exchange (hα0 : 0 ≤ α) (h : ℕ)
    (ρs : PMF (FullLab (V × ℕ) h × FullLab (V × ℕ) h))
    (c : FullLab (V × ℕ) h × FullLab (V × ℕ) h → ℝ≥0∞) (bnd TνR : ℝ≥0∞)
    (hTνR : (∑' j, if (νR j : ℝ≥0∞) = 0 then 0
        else (νR j : ℝ≥0∞) ^ (-α)) ≤ TνR)
    (hbnd : ∀ j : ℕ, (νR j : ℝ≥0∞) ≠ 0 →
      (∑' xp, ρs xp * (c xp * WresD α (Xi μ νR v0 j h)
          (SquareRel (fullSim (labRel Rv) h)) xp)) ≤ bnd) :
    ∑' xp, ρs xp * (c xp * WresD α (XiBar μ νR v0 h)
        (SquareRel (fullSim (labRel Rv) h)) xp)
      ≤ TνR * bnd := by
  have hpt : ∀ xp, ρs xp * (c xp * WresD α (XiBar μ νR v0 h)
      (SquareRel (fullSim (labRel Rv) h)) xp)
      ≤ ∑' j, (if (νR j : ℝ≥0∞) = 0 then 0
          else (νR j : ℝ≥0∞) ^ (-α)
            * (ρs xp * (c xp * WresD α (Xi μ νR v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp))) := by
    intro xp
    calc ρs xp * (c xp * WresD α (XiBar μ νR v0 h)
          (SquareRel (fullSim (labRel Rv) h)) xp)
        ≤ ρs xp * (c xp * ∑' j, (if (νR j : ℝ≥0∞) = 0 then 0
            else (νR j : ℝ≥0∞) ^ (-α)
              * WresD α (Xi μ νR v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp)) :=
          mul_le_mul_right (mul_le_mul_right
            (WresD_XiBar_le_sum α Rv μ νR v0 hα0 h xp) _) _
      _ = ∑' j, ρs xp * (c xp * (if (νR j : ℝ≥0∞) = 0 then 0
            else (νR j : ℝ≥0∞) ^ (-α)
              * WresD α (Xi μ νR v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp)) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ = ∑' j, (if (νR j : ℝ≥0∞) = 0 then 0
            else (νR j : ℝ≥0∞) ^ (-α)
              * (ρs xp * (c xp * WresD α (Xi μ νR v0 j h)
                  (SquareRel (fullSim (labRel Rv) h)) xp))) :=
          tsum_congr fun j => by
            by_cases hj : (νR j : ℝ≥0∞) = 0
            · rw [if_pos hj, if_pos hj, mul_zero, mul_zero]
            · rw [if_neg hj, if_neg hj]; ring
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_comm]
  have hterm : ∀ j : ℕ,
      (∑' xp, (if (νR j : ℝ≥0∞) = 0 then 0
          else (νR j : ℝ≥0∞) ^ (-α)
            * (ρs xp * (c xp * WresD α (Xi μ νR v0 j h)
                (SquareRel (fullSim (labRel Rv) h)) xp))))
      ≤ (if (νR j : ℝ≥0∞) = 0 then 0 else (νR j : ℝ≥0∞) ^ (-α)) * bnd := by
    intro j
    by_cases hj : (νR j : ℝ≥0∞) = 0
    · rw [if_pos hj, zero_mul,
        tsum_congr fun xp => if_pos (c := (νR j : ℝ≥0∞) = 0) hj, tsum_zero]
    · rw [if_neg hj, tsum_congr fun xp => if_neg (c := (νR j : ℝ≥0∞) = 0) hj,
        ENNReal.tsum_mul_left]
      exact mul_le_mul_right (hbnd j hj) _
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  rw [ENNReal.tsum_mul_right]
  exact mul_le_mul_left hTνR _

/-- Pulling a bounded root factor out of a tilted, indicated sum. -/
private lemma crossTsum_tilt_pull {Y : Type} (ρs : PMF Y) (c W : Y → ℝ≥0∞)
    (r RT : ℝ≥0∞) (hr : r ≤ RT) :
    ∑' y, ρs y * (c y * (r * W y))
      ≤ RT * ∑' y, ρs y * (c y * W y) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun y => ?_
  exact le_trans (le_of_eq (by ring)) (mul_le_mul_left hr _)

/-- Dropping a subunit indicator and pulling a root factor out of a
tilted sum. -/
private lemma crossTsum_tilt_drop {Y : Type} (ρs : PMF Y) (c W : Y → ℝ≥0∞)
    (hc : ∀ y, c y ≤ 1) (r : ℝ≥0∞) :
    ∑' y, ρs y * (c y * (r * W y))
      ≤ r * ∑' y, ρs y * ((1 : ℝ≥0∞) * W y) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun y => ?_
  calc ρs y * (c y * (r * W y))
      ≤ ρs y * (1 * (r * W y)) :=
        mul_le_mul_right (mul_le_mul_left (hc y) _) _
    _ = r * (ρs y * (1 * W y)) := by ring

/-- The raw pair `W`-moment of a charged cell: both survivor orders
factor through `tsum_prod_split` into two restricted inverse moments,
each at most `1 + α·M`. -/
private lemma crossPairW_moment_le (hα : 1 ≤ α) (k j h : ℕ) (M : ℝ≥0∞)
    (hmom : ∀ c' ∈ gpair k, ∀ w' ∈ gpair j,
      PhiDres α (interpT μ νL v0 h c') (interpT μ νR v0 h w')
        (fullSim (labRel Rv) h) ≤ M) :
    ∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
        Xi μ νL v0 k h xp
          * (1 * WresD α (Xi μ νR v0 j h)
              (SquareRel (fullSim (labRel Rv) h)) xp)
      ≤ 2 * ((1 + ENNReal.ofReal α * M) * (1 + ENNReal.ofReal α * M)) := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  have hsplit := crossTsum_ind_split (Xi μ νL v0 k h) (fun _ => 1)
    (WresD α (Xi μ νR v0 j h) (SquareRel (fullSim (labRel Rv) h)))
    (fun xp => WresD α (interpT μ νR v0 h (gcomp0 j))
        (fullSim (labRel Rv) h) xp.1
      * WresD α (interpT μ νR v0 h (gcomp1 j)) (fullSim (labRel Rv) h) xp.2)
    (fun xp => WresD α (interpT μ νR v0 h (gcomp1 j))
        (fullSim (labRel Rv) h) xp.1
      * WresD α (interpT μ νR v0 h (gcomp0 j)) (fullSim (labRel Rv) h) xp.2)
    (fun xp => by
      rw [Xi_eq_prod μ νR v0 j h]
      exact WresD_square_le_sum hα0 _ _ _ xp)
  refine le_trans hsplit ?_
  have hmomW : ∀ c' ∈ gpair k, ∀ w' ∈ gpair j,
      (∑' x, interpT μ νL v0 h c' x
        * WresD α (interpT μ νR v0 h w') (fullSim (labRel Rv) h) x)
      ≤ 1 + ENNReal.ofReal α * M := fun c' hc' w' hw' =>
    le_trans (tsum_WresD_le hα _ _ _)
      (add_le_add le_rfl (mul_le_mul_right (hmom c' hc' w' hw') _))
  have horder : ∀ a b : Tgt, a ∈ gpair j → b ∈ gpair j →
      (∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
        Xi μ νL v0 k h xp
          * ((1 : ℝ≥0∞) * (WresD α (interpT μ νR v0 h a)
                (fullSim (labRel Rv) h) xp.1
              * WresD α (interpT μ νR v0 h b)
                  (fullSim (labRel Rv) h) xp.2)))
      ≤ (1 + ENNReal.ofReal α * M) * (1 + ENNReal.ofReal α * M) := by
    intro a b ha hb
    calc ∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
        Xi μ νL v0 k h xp
          * ((1 : ℝ≥0∞) * (WresD α (interpT μ νR v0 h a)
                (fullSim (labRel Rv) h) xp.1
              * WresD α (interpT μ νR v0 h b)
                  (fullSim (labRel Rv) h) xp.2))
        = ∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
            (interpT μ νL v0 h (gcomp0 k) xp.1
                * WresD α (interpT μ νR v0 h a)
                    (fullSim (labRel Rv) h) xp.1)
              * (interpT μ νL v0 h (gcomp1 k) xp.2
                * WresD α (interpT μ νR v0 h b)
                    (fullSim (labRel Rv) h) xp.2) := by
          rw [Xi_eq_prod μ νL v0 k h]
          exact tsum_congr fun xp => by
            rw [prodPMF_apply]
            ring
      _ = (∑' x, interpT μ νL v0 h (gcomp0 k) x
              * WresD α (interpT μ νR v0 h a) (fullSim (labRel Rv) h) x)
            * ∑' x, interpT μ νL v0 h (gcomp1 k) x
              * WresD α (interpT μ νR v0 h b) (fullSim (labRel Rv) h) x :=
          tsum_prod_split
            (fun x => interpT μ νL v0 h (gcomp0 k) x
              * WresD α (interpT μ νR v0 h a) (fullSim (labRel Rv) h) x)
            (fun x => interpT μ νL v0 h (gcomp1 k) x
              * WresD α (interpT μ νR v0 h b) (fullSim (labRel Rv) h) x)
      _ ≤ (1 + ENNReal.ofReal α * M) * (1 + ENNReal.ofReal α * M) :=
          mul_le_mul' (hmomW _ (gcomp_mem_gpair k).1 a ha)
            (hmomW _ (gcomp_mem_gpair k).2 b hb)
  refine le_trans (add_le_add
    (horder (gcomp0 j) (gcomp1 j) (gcomp_mem_gpair j).1 (gcomp_mem_gpair j).2)
    (horder (gcomp1 j) (gcomp0 j) (gcomp_mem_gpair j).2 (gcomp_mem_gpair j).1))
    (le_of_eq (by ring))

/-! ### The three norm conversions -/

/-- The exact unit-normalized Hall output of one exposed left counter cell.
Unlike the support-supremum row below, this keeps the counter index available
so that a later fresh-source mixture can retain its `νL k` coefficient. -/
noncomputable def crossUnitCellDebt (SR : Finset ℕ) (k : ℕ)
    (z : Finset Tgt) (h : ℕ) : ℝ≥0∞ :=
  let R := fullSim (labRel Rv) h
  let zs := ((zsucc SR z).toList).map (interpT μ νR v0 h)
  let L0 := interpT μ νL v0 h (gcomp0 k)
  let L1 := interpT μ νL v0 h (gcomp1 k)
  screenE L0 R zs (fun _ => 1)
    + screenE L1 R zs (fun _ => 1)
    + ((zs.map fun ρ => screenE L0 R [ρ] (fun _ => 1)).sum
        * (zs.map fun ρ => screenE L1 R [ρ] (fun _ => 1)).sum)

/-- **The fresh screen row, unit normalization** (`sec:rows`,
`thm:screen-rows`, row `⟨F, z, none⟩`): far roots inject into the uncharged
root mass `FM`, near roots contribute two full successor screens and a
quadratic singleton charge. -/
lemma crossERowF_none (SL SR : Finset ℕ)
    (hLsupp : ∀ k : ℕ, (νL k : ℝ≥0∞) ≠ 0 ↔ k ∈ SL)
    (hRsupp : ∀ j : ℕ, (νR j : ℝ≥0∞) ≠ 0 ↔ j ∈ SR)
    (hpos : (μ v0 : ℝ≥0∞) ≠ 0) (z : Finset Tgt)
    (hzf : ∀ t ∈ z, ∀ m, t ≠ Tgt.Fk m) (h : ℕ) (E' FM : ℝ≥0∞)
    (hFM : (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞)) ≤ FM)
    (hscrS : ∀ t' ∈ zsucc SR z, ∀ k ∈ SL, ∀ c' ∈ gpair k,
      screenE (interpT μ νL v0 h c') (fullSim (labRel Rv) h)
        [interpT μ νR v0 h t'] (fun _ => 1) ≤ E') :
    crossInterpScreen α Rv μ νL νR v0 (h + 1) ⟨Tgt.F, z, none⟩
      ≤ FM + (2 * (∑ sc' ∈ crossScreenSucc SL SR ⟨Tgt.F, z, none⟩,
            crossInterpScreen α Rv μ νL νR v0 h sc')
          + ((zsucc SR z).card * E') * ((zsucc SR z).card * E')) := by
  set nearB := 2 * (∑ sc' ∈ crossScreenSucc SL SR (⟨Tgt.F, z, none⟩ : GScreen),
      crossInterpScreen α Rv μ νL νR v0 h sc')
    + ((zsucc SR z).card * E') * ((zsucc SR z).card * E') with hnearB
  have hnear : ∀ (v : V) (k : ℕ), Rv v v0 → k ∈ SL →
      screenE (muM (varyK μ νL v0) (v, k) (h + 1))
          (fullSim (labRel Rv) (h + 1))
          ((z.toList).map (interpT μ νR v0 (h + 1)))
          (interpNorm α Rv μ νR v0 (h + 1) none)
        ≤ nearB := by
    intro v k hv hkS
    have hvpos : rE μ Rv v ≠ 0 := rE_ne_zero_of_near Rv μ v0 hpos hv
    rw [crossScreen_cell_step α Rv μ νL νR v0 SL SR hRsupp hv hvpos k h z hzf none]
    refine le_trans (le_trans (ENNReal.tsum_le_tsum fun xp =>
        mul_le_mul_right (mul_le_mul_right
          (le_of_eq (one_mul (1 : ℝ≥0∞)).symm) _) _)
      (crossCell_factor Rv μ νL νR v0 SL SR k h z
        (fun _ => 1) (fun _ => 1))) ?_
    have hmom : ∀ c : Tgt,
        (∑' x, interpT μ νL v0 h c x
          * (fun _ : FullLab (V × ℕ) h => (1 : ℝ≥0∞)) x) = 1 := by
      intro c
      simp only [mul_one]
      exact (interpT μ νL v0 h c).tsum_coe
    have hscr : ∀ c' : Tgt, c' ∈ gpair k →
        screenE (interpT μ νL v0 h c') (fullSim (labRel Rv) h)
          (((zsucc SR z).toList).map (interpT μ νR v0 h)) (fun _ => 1)
        ≤ ∑ sc' ∈ crossScreenSucc SL SR (⟨Tgt.F, z, none⟩ : GScreen),
            crossInterpScreen α Rv μ νL νR v0 h sc' := by
      intro c' hc'
      rw [← crossInterpScreen_none_eq α Rv μ νL νR v0 c' (zsucc SR z) h]
      exact Finset.single_le_sum (fun _ _ => zero_le)
        (mem_crossScreenSucc_mk
          (Finset.mem_biUnion.mpr ⟨k, hkS, hc'⟩) (none_mem_normSucc SR))
    have hquad : ∀ c' : Tgt, c' ∈ gpair k →
        ((((zsucc SR z).toList).map (interpT μ νR v0 h)).map fun ρ =>
          screenE (interpT μ νL v0 h c') (fullSim (labRel Rv) h) [ρ]
            (fun _ => 1)).sum ≤ (zsucc SR z).card * E' := by
      intro c' hc'
      refine le_trans (list_map_sum_le _ _ E' fun ρ hρ => ?_) ?_
      · obtain ⟨t', ht', hρt⟩ := List.mem_map.mp hρ
        rw [← hρt]
        exact hscrS t' (Finset.mem_toList.mp ht') k hkS c' hc'
      · rw [zsucc_map_length μ νR v0 SR h z]
    refine le_trans (add_le_add (add_le_add
        (mul_le_mul' (hscr _ (gcomp_mem_gpair k).1)
          (le_of_eq (hmom (gcomp1 k))))
        (mul_le_mul' (le_of_eq (hmom (gcomp0 k)))
          (hscr _ (gcomp_mem_gpair k).2)))
        (mul_le_mul' (hquad _ (gcomp_mem_gpair k).1)
          (hquad _ (gcomp_mem_gpair k).2)))
      (le_of_eq ?_)
    rw [hnearB]
    ring
  rw [crossInterpScreen_fresh_split α Rv μ νL νR v0 z none h]
  have hpt : ∀ s : V × ℕ,
      freshQ μ νL s * screenE (muM (varyK μ νL v0) s (h + 1))
          (fullSim (labRel Rv) (h + 1))
          ((z.toList).map (interpT μ νR v0 (h + 1)))
          (interpNorm α Rv μ νR v0 (h + 1) none)
        ≤ (if Rv s.1 v0 then 0 else freshQ μ νL s) + freshQ μ νL s * nearB := by
    rintro ⟨v, k⟩
    by_cases hv : Rv v v0
    · rw [if_pos hv, zero_add]
      by_cases hk : (νL k : ℝ≥0∞) = 0
      · rw [show freshQ μ νL (v, k) = 0 from by
            rw [show freshQ μ νL (v, k) = μ v * νL k from
              prodPMF_apply μ νL (v, k), hk, mul_zero],
          zero_mul, zero_mul]
      · exact mul_le_mul_right (hnear v k hv ((hLsupp k).mp hk)) _
    · rw [if_neg hv]
      refine le_trans ?_ le_self_add
      exact le_trans (mul_le_mul_right (screenE_one_le_one _ _ _) _)
        (le_of_eq (mul_one _))
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_add]
  refine add_le_add ?_ ?_
  · have hsplit : (∑' s : V × ℕ, (if Rv s.1 v0 then 0 else freshQ μ νL s))
        = (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞))
          * ∑' l, (νL l : ℝ≥0∞) := by
      rw [← tsum_prod_split (fun v => if Rv v v0 then 0 else (μ v : ℝ≥0∞))
        (fun l => (νL l : ℝ≥0∞))]
      refine tsum_congr fun s => ?_
      by_cases hv : Rv s.1 v0
      · rw [if_pos hv, if_pos hv, zero_mul]
      · rw [if_neg hv, if_neg hv,
          show freshQ μ νL s = μ s.1 * νL s.2 from prodPMF_apply μ νL s]
    rw [hsplit, νL.tsum_coe, mul_one]
    exact hFM
  · rw [ENNReal.tsum_mul_right, (freshQ μ νL).tsum_coe, one_mul]

/-- **Probability-retaining fresh unit row.**  The same Hall factorization as
`crossERowF_none`, but before taking a support supremum: every exposed left
counter keeps its original `νL k` coefficient. -/
lemma crossERowF_none_weighted (SR : Finset ℕ)
    (hRsupp : ∀ j : ℕ, (νR j : ℝ≥0∞) ≠ 0 ↔ j ∈ SR)
    (hpos : (μ v0 : ℝ≥0∞) ≠ 0) (z : Finset Tgt)
    (hzf : ∀ t ∈ z, ∀ m, t ≠ Tgt.Fk m) (h : ℕ) (FM : ℝ≥0∞)
    (hFM : (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞)) ≤ FM) :
    crossInterpScreen α Rv μ νL νR v0 (h + 1) ⟨Tgt.F, z, none⟩
      ≤ FM + ∑' k, νL k *
          crossUnitCellDebt Rv μ νL νR v0 SR k z h := by
  have hnear : ∀ (v : V) (k : ℕ), Rv v v0 →
      screenE (muM (varyK μ νL v0) (v, k) (h + 1))
          (fullSim (labRel Rv) (h + 1))
          ((z.toList).map (interpT μ νR v0 (h + 1)))
          (interpNorm α Rv μ νR v0 (h + 1) none)
        ≤ crossUnitCellDebt Rv μ νL νR v0 SR k z h := by
    intro v k hv
    have hvpos : rE μ Rv v ≠ 0 := rE_ne_zero_of_near Rv μ v0 hpos hv
    rw [crossScreen_cell_step α Rv μ νL νR v0 ∅ SR
      hRsupp hv hvpos k h z hzf none]
    refine le_trans (le_trans (ENNReal.tsum_le_tsum fun xp =>
        mul_le_mul_right (mul_le_mul_right
          (le_of_eq (one_mul (1 : ℝ≥0∞)).symm) _) _)
      (crossCell_factor Rv μ νL νR v0 ∅ SR k h z
        (fun _ => 1) (fun _ => 1))) ?_
    have hmom : ∀ c : Tgt,
        (∑' x, interpT μ νL v0 h c x
          * (fun _ : FullLab (V × ℕ) h => (1 : ℝ≥0∞)) x) = 1 := by
      intro c
      simp only [mul_one]
      exact (interpT μ νL v0 h c).tsum_coe
    rw [hmom, hmom, mul_one, one_mul]
    exact le_of_eq (by simp [crossUnitCellDebt])
  rw [crossInterpScreen_fresh_split α Rv μ νL νR v0 z none h]
  have hpt : ∀ s : V × ℕ,
      freshQ μ νL s * screenE (muM (varyK μ νL v0) s (h + 1))
          (fullSim (labRel Rv) (h + 1))
          ((z.toList).map (interpT μ νR v0 (h + 1)))
          (interpNorm α Rv μ νR v0 (h + 1) none)
        ≤ (if Rv s.1 v0 then 0 else freshQ μ νL s)
          + μ s.1 * (νL s.2 *
              crossUnitCellDebt Rv μ νL νR v0 SR s.2 z h) := by
    rintro ⟨v, k⟩
    by_cases hv : Rv v v0
    · rw [if_pos hv, zero_add,
        show freshQ μ νL (v, k) = μ v * νL k from prodPMF_apply μ νL (v, k)]
      refine le_trans (mul_le_mul_right (hnear v k hv) (μ v * νL k)) ?_
      exact le_of_eq (by ring)
    · rw [if_neg hv]
      refine le_trans ?_ le_self_add
      exact le_trans (mul_le_mul_right (screenE_one_le_one _ _ _) _)
        (le_of_eq (mul_one _))
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_add]
  refine add_le_add ?_ ?_
  · have hsplit : (∑' s : V × ℕ,
        (if Rv s.1 v0 then 0 else freshQ μ νL s))
        = (∑' v, if Rv v v0 then 0 else (μ v : ℝ≥0∞))
          * ∑' l, (νL l : ℝ≥0∞) := by
      rw [← tsum_prod_split
        (fun v => if Rv v v0 then 0 else (μ v : ℝ≥0∞))
        (fun l => (νL l : ℝ≥0∞))]
      refine tsum_congr fun s => ?_
      by_cases hv : Rv s.1 v0
      · rw [if_pos hv, if_pos hv, zero_mul]
      · rw [if_neg hv, if_neg hv,
          show freshQ μ νL s = μ s.1 * νL s.2 from prodPMF_apply μ νL s]
    rw [hsplit, νL.tsum_coe, mul_one]
    exact hFM
  · calc
      (∑' s : V × ℕ, μ s.1 * (νL s.2 *
          crossUnitCellDebt Rv μ νL νR v0 SR s.2 z h))
          = (∑' v, (μ v : ℝ≥0∞)) *
              ∑' k, νL k *
                crossUnitCellDebt Rv μ νL νR v0 SR k z h :=
            tsum_prod_split (fun v => (μ v : ℝ≥0∞))
              (fun k => νL k *
                crossUnitCellDebt Rv μ νL νR v0 SR k z h)
      _ = ∑' k, νL k *
              crossUnitCellDebt Rv μ νL νR v0 SR k z h := by
            rw [μ.tsum_coe, one_mul]
      _ ≤ ∑' k, νL k *
              crossUnitCellDebt Rv μ νL νR v0 SR k z h := le_rfl

/-- **The fresh screen row, forced normalization** (`sec:rows`,
`thm:screen-rows`, row `⟨F, z, some (Z m)⟩`): the forced tilt kills far
roots outright (`WresD_Zlaw_succ_branch`), and each charged near cell
contributes the survivor split of the `Ξ_m`-tilt: four successor screens,
four moment-screen cross terms, and two quadratic singleton
charges. -/
lemma crossERowF_forced (hα : 1 ≤ α) (SL SR : Finset ℕ)
    (hLsupp : ∀ k : ℕ, (νL k : ℝ≥0∞) ≠ 0 ↔ k ∈ SL)
    (hRsupp : ∀ j : ℕ, (νR j : ℝ≥0∞) ≠ 0 ↔ j ∈ SR)
    (hpos : (μ v0 : ℝ≥0∞) ≠ 0) (z : Finset Tgt)
    (hzf : ∀ t ∈ z, ∀ m', t ≠ Tgt.Fk m') (m h : ℕ) (M E' : ℝ≥0∞)
    (hMom : ∀ k ∈ SL, ∀ c' ∈ gpair k, ∀ w' ∈ gpair m,
      PhiDres α (interpT μ νL v0 h c') (interpT μ νR v0 h w')
        (fullSim (labRel Rv) h) ≤ M)
    (hscrS : ∀ t' ∈ zsucc SR z, ∀ k ∈ SL, ∀ c' ∈ gpair k, ∀ w' ∈ gpair m,
      screenE (interpT μ νL v0 h c') (fullSim (labRel Rv) h)
        [interpT μ νR v0 h t']
        (WresD α (interpT μ νR v0 h w') (fullSim (labRel Rv) h)) ≤ E')
    (hE : ∀ sc' ∈ crossScreenSucc SL SR ⟨Tgt.F, z, some (Tgt.Z m)⟩,
      crossInterpScreen α Rv μ νL νR v0 h sc' ≤ E') :
    crossInterpScreen α Rv μ νL νR v0 (h + 1) ⟨Tgt.F, z, some (Tgt.Z m)⟩
      ≤ 4 * (∑ sc' ∈ crossScreenSucc SL SR ⟨Tgt.F, z, some (Tgt.Z m)⟩,
            crossInterpScreen α Rv μ νL νR v0 h sc')
        + 4 * (ENNReal.ofReal α * M * E')
        + 2 * (((zsucc SR z).card * E') * ((zsucc SR z).card * E')) := by
  set nearB := 4 * (∑ sc' ∈ crossScreenSucc SL SR (⟨Tgt.F, z, some (Tgt.Z m)⟩ : GScreen),
      crossInterpScreen α Rv μ νL νR v0 h sc')
    + 4 * (ENNReal.ofReal α * M * E')
    + 2 * (((zsucc SR z).card * E') * ((zsucc SR z).card * E')) with hnearB
  have hmemS : ∀ k ∈ SL, ∀ c' ∈ gpair k, ∀ w' ∈ gpair m,
      (⟨c', zsucc SR z, some w'⟩ : GScreen)
        ∈ crossScreenSucc SL SR ⟨Tgt.F, z, some (Tgt.Z m)⟩ := by
    intro k hkS c' hc' w' hw'
    exact mem_crossScreenSucc_mk (Finset.mem_biUnion.mpr ⟨k, hkS, hc'⟩)
      (some_mem_normSucc hw')
  have hnear : ∀ (v : V) (k : ℕ), Rv v v0 → k ∈ SL →
      screenE (muM (varyK μ νL v0) (v, k) (h + 1))
          (fullSim (labRel Rv) (h + 1))
          ((z.toList).map (interpT μ νR v0 (h + 1)))
          (interpNorm α Rv μ νR v0 (h + 1) (some (Tgt.Z m)))
        ≤ nearB := by
    intro v k hv hkS
    have hvpos : rE μ Rv v ≠ 0 := rE_ne_zero_of_near Rv μ v0 hpos hv
    rw [crossScreen_cell_step α Rv μ νL νR v0 SL SR hRsupp hv hvpos k h z hzf
      (some (Tgt.Z m))]
    have hbr : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
        interpNorm α Rv μ νR v0 (h + 1) (some (Tgt.Z m)) (branch (v, k) xp)
          = WresD α (Xi μ νR v0 m h)
              (SquareRel (fullSim (labRel Rv) h)) xp := by
      intro xp
      show WresD α (Zlaw μ νR v0 m (h + 1)) (fullSim (labRel Rv) (h + 1))
          (branch (v, k) xp) = _
      rw [WresD_Zlaw_succ_branch α Rv μ νR v0 v m k h xp, if_pos hv]
    simp only [hbr]
    refine le_trans (crossCell_W_pair α Rv μ νL νR v0 SL SR hα k h z m
      (⟨Tgt.F, z, some (Tgt.Z m)⟩ : GScreen) M E'
      (hmemS k hkS _ (gcomp_mem_gpair k).1 _ (gcomp_mem_gpair m).1)
      (hmemS k hkS _ (gcomp_mem_gpair k).2 _ (gcomp_mem_gpair m).2)
      (hmemS k hkS _ (gcomp_mem_gpair k).1 _ (gcomp_mem_gpair m).2)
      (hmemS k hkS _ (gcomp_mem_gpair k).2 _ (gcomp_mem_gpair m).1)
      hE (hMom k hkS)
      (fun t' ht' => hscrS t' ht' k hkS)) (le_of_eq hnearB.symm)
  have hfar : ∀ (v : V) (k : ℕ), ¬ Rv v v0 →
      screenE (muM (varyK μ νL v0) (v, k) (h + 1))
          (fullSim (labRel Rv) (h + 1))
          ((z.toList).map (interpT μ νR v0 (h + 1)))
          (interpNorm α Rv μ νR v0 (h + 1) (some (Tgt.Z m))) = 0 := by
    intro v k hv
    rw [crossScreenE_branch_eq Rv μ νL v0 v k h _ _]
    refine ENNReal.tsum_eq_zero.mpr fun xp => ?_
    have hz0 : interpNorm α Rv μ νR v0 (h + 1) (some (Tgt.Z m))
        (branch (v, k) xp) = 0 := by
      show WresD α (Zlaw μ νR v0 m (h + 1)) (fullSim (labRel Rv) (h + 1))
          (branch (v, k) xp) = 0
      rw [WresD_Zlaw_succ_branch α Rv μ νR v0 v m k h xp, if_neg hv]
    rw [hz0, mul_zero, mul_zero]
  rw [crossInterpScreen_fresh_split α Rv μ νL νR v0 z (some (Tgt.Z m)) h]
  have hpt : ∀ s : V × ℕ,
      freshQ μ νL s * screenE (muM (varyK μ νL v0) s (h + 1))
          (fullSim (labRel Rv) (h + 1))
          ((z.toList).map (interpT μ νR v0 (h + 1)))
          (interpNorm α Rv μ νR v0 (h + 1) (some (Tgt.Z m)))
        ≤ freshQ μ νL s * nearB := by
    rintro ⟨v, k⟩
    by_cases hv : Rv v v0
    · by_cases hk : (νL k : ℝ≥0∞) = 0
      · rw [show freshQ μ νL (v, k) = 0 from by
            rw [show freshQ μ νL (v, k) = μ v * νL k from
              prodPMF_apply μ νL (v, k), hk, mul_zero],
          zero_mul, zero_mul]
      · exact mul_le_mul_right (hnear v k hv ((hLsupp k).mp hk)) _
    · rw [hfar v k hv, mul_zero]
      exact zero_le
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_mul_right, (freshQ μ νL).tsum_coe, one_mul]

/-- **The fresh screen row, fresh normalization** (`sec:rows`,
`thm:screen-rows`, row `⟨F, z, some F⟩`): the fresh tilt factors through the
root degree.  Far roots inject into the fresh-tilted root mass `FT`,
each contributing the charged tilt sum `TνR` times a pair moment; near roots
contribute the root bound `RT` and the charged tilt sum times the survivor
split of each component cell. -/
lemma crossERowF_fresh (hα : 1 ≤ α) (SL SR : Finset ℕ)
    (hLsupp : ∀ k : ℕ, (νL k : ℝ≥0∞) ≠ 0 ↔ k ∈ SL)
    (hRsupp : ∀ j : ℕ, (νR j : ℝ≥0∞) ≠ 0 ↔ j ∈ SR)
    (hpos : (μ v0 : ℝ≥0∞) ≠ 0) (z : Finset Tgt)
    (hzf : ∀ t ∈ z, ∀ m, t ≠ Tgt.Fk m) (h : ℕ) (M E' TνR RT FT : ℝ≥0∞)
    (hRT : ∀ v : V, Rv v v0 → (rE μ Rv v) ^ (-α) ≤ RT)
    (hTνR : (∑' j, if (νR j : ℝ≥0∞) = 0 then 0
        else (νR j : ℝ≥0∞) ^ (-α)) ≤ TνR)
    (hFT : (∑' v, if Rv v v0 then 0
        else (μ v : ℝ≥0∞) * WresD α μ Rv v) ≤ FT)
    (hMom : ∀ k ∈ SL, ∀ j ∈ SR, ∀ c' ∈ gpair k, ∀ w' ∈ gpair j,
      PhiDres α (interpT μ νL v0 h c') (interpT μ νR v0 h w')
        (fullSim (labRel Rv) h) ≤ M)
    (hscrS : ∀ j ∈ SR, ∀ t' ∈ zsucc SR z, ∀ k ∈ SL, ∀ c' ∈ gpair k,
      ∀ w' ∈ gpair j,
      screenE (interpT μ νL v0 h c') (fullSim (labRel Rv) h)
        [interpT μ νR v0 h t']
        (WresD α (interpT μ νR v0 h w') (fullSim (labRel Rv) h)) ≤ E')
    (hE : ∀ sc' ∈ crossScreenSucc SL SR ⟨Tgt.F, z, some Tgt.F⟩,
      crossInterpScreen α Rv μ νL νR v0 h sc' ≤ E') :
    crossInterpScreen α Rv μ νL νR v0 (h + 1) ⟨Tgt.F, z, some Tgt.F⟩
      ≤ FT * (TνR * (2 * ((1 + ENNReal.ofReal α * M)
            * (1 + ENNReal.ofReal α * M))))
        + RT * TνR * (4 * (∑ sc' ∈ crossScreenSucc SL SR ⟨Tgt.F, z, some Tgt.F⟩,
              crossInterpScreen α Rv μ νL νR v0 h sc')
            + 4 * (ENNReal.ofReal α * M * E')
            + 2 * (((zsucc SR z).card * E') * ((zsucc SR z).card * E'))) := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  set rowB := 4 * (∑ sc' ∈ crossScreenSucc SL SR (⟨Tgt.F, z, some Tgt.F⟩ : GScreen),
      crossInterpScreen α Rv μ νL νR v0 h sc')
    + 4 * (ENNReal.ofReal α * M * E')
    + 2 * (((zsucc SR z).card * E') * ((zsucc SR z).card * E')) with hrowB
  set PB := 2 * ((1 + ENNReal.ofReal α * M)
    * (1 + ENNReal.ofReal α * M)) with hPB
  have hfarW : ∀ k : ℕ, (νL k : ℝ≥0∞) ≠ 0 →
      (∑' xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
        Xi μ νL v0 k h xp * ((1 : ℝ≥0∞) * WresD α (XiBar μ νR v0 h)
          (SquareRel (fullSim (labRel Rv) h)) xp)) ≤ TνR * PB :=
    fun k hk => crossTsum_XiBar_exchange α Rv μ νR v0 hα0 h (Xi μ νL v0 k h)
      (fun _ => 1) PB TνR hTνR fun j hj =>
        le_trans (crossPairW_moment_le α Rv μ νL νR v0 hα k j h M
          (hMom k ((hLsupp k).mp hk) j ((hRsupp j).mp hj)))
          (le_of_eq hPB.symm)
  have hfar : ∀ (v : V) (k : ℕ), ¬ Rv v v0 → (νL k : ℝ≥0∞) ≠ 0 →
      screenE (muM (varyK μ νL v0) (v, k) (h + 1))
          (fullSim (labRel Rv) (h + 1))
          ((z.toList).map (interpT μ νR v0 (h + 1)))
          (interpNorm α Rv μ νR v0 (h + 1) (some Tgt.F))
        ≤ WresD α μ Rv v * (TνR * PB) := by
    intro v k hv hk
    rw [crossScreenE_branch_eq Rv μ νL v0 v k h _ _]
    by_cases hvr : rE μ Rv v = 0
    · refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun xp => ?_))
        zero_le
      have hz0 : interpNorm α Rv μ νR v0 (h + 1) (some Tgt.F)
          (branch (v, k) xp) = 0 := by
        show WresD α (Tlaw μ νR v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
            (branch (v, k) xp) = 0
        rw [WresD, if_pos (show rE (Tlaw μ νR v0 (h + 1))
            (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp) = 0 from by
          rw [rE_Tlaw_succ_branch μ νR v0 Rv v k h xp, hvr, zero_mul])]
      rw [hz0, mul_zero, mul_zero]
    · have hbr : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
          interpNorm α Rv μ νR v0 (h + 1) (some Tgt.F) (branch (v, k) xp)
            = (rE μ Rv v) ^ (-α)
              * WresD α (XiBar μ νR v0 h)
                  (SquareRel (fullSim (labRel Rv) h)) xp :=
        fun xp => WresD_Tlaw_succ_branch α Rv μ νR v0 v hvr k h xp
      simp only [hbr]
      refine le_trans (crossTsum_tilt_drop (Xi μ νL v0 k h) _ _
        (fun xp => screenInd_le_one _ _ _) ((rE μ Rv v) ^ (-α))) ?_
      rw [rE_rpow_neg_eq_WresD μ Rv v hvr]
      exact mul_le_mul_right (hfarW k hk) _
  have hnear : ∀ (v : V) (k : ℕ), Rv v v0 → k ∈ SL →
      screenE (muM (varyK μ νL v0) (v, k) (h + 1))
          (fullSim (labRel Rv) (h + 1))
          ((z.toList).map (interpT μ νR v0 (h + 1)))
          (interpNorm α Rv μ νR v0 (h + 1) (some Tgt.F))
        ≤ RT * (TνR * rowB) := by
    intro v k hv hkS
    have hvpos : rE μ Rv v ≠ 0 := rE_ne_zero_of_near Rv μ v0 hpos hv
    rw [crossScreen_cell_step α Rv μ νL νR v0 SL SR hRsupp hv hvpos k h z hzf
      (some Tgt.F)]
    have hbr : ∀ xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h,
        interpNorm α Rv μ νR v0 (h + 1) (some Tgt.F) (branch (v, k) xp)
          = (rE μ Rv v) ^ (-α)
            * WresD α (XiBar μ νR v0 h)
                (SquareRel (fullSim (labRel Rv) h)) xp :=
      fun xp => WresD_Tlaw_succ_branch α Rv μ νR v0 v hvpos k h xp
    simp only [hbr]
    refine le_trans (crossTsum_tilt_pull (Xi μ νL v0 k h) _ _
      ((rE μ Rv v) ^ (-α)) RT (hRT v hv)) ?_
    refine mul_le_mul_right ?_ RT
    refine crossTsum_XiBar_exchange α Rv μ νR v0 hα0 h (Xi μ νL v0 k h)
      (fun xp => if ∀ p ∈ memPairs μ νR v0 SR h z,
          rE (prodPMF p.1 p.2) (SquareRel (fullSim (labRel Rv) h)) xp = 0
        then (1 : ℝ≥0∞) else 0) rowB TνR hTνR ?_
    intro j hj
    have hjS : j ∈ SR := (hRsupp j).mp hj
    have hmemFF : ∀ c' ∈ gpair k, ∀ w' ∈ gpair j,
        (⟨c', zsucc SR z, some w'⟩ : GScreen)
          ∈ crossScreenSucc SL SR ⟨Tgt.F, z, some Tgt.F⟩ :=
      fun c' hc' w' hw' => mem_crossScreenSucc_mk
        (Finset.mem_biUnion.mpr ⟨k, hkS, hc'⟩)
        (some_mem_normSucc (Finset.mem_biUnion.mpr ⟨j, hjS, hw'⟩))
    refine le_trans (crossCell_W_pair α Rv μ νL νR v0 SL SR hα k h z j
      (⟨Tgt.F, z, some Tgt.F⟩ : GScreen) M E'
      (hmemFF _ (gcomp_mem_gpair k).1 _ (gcomp_mem_gpair j).1)
      (hmemFF _ (gcomp_mem_gpair k).2 _ (gcomp_mem_gpair j).2)
      (hmemFF _ (gcomp_mem_gpair k).1 _ (gcomp_mem_gpair j).2)
      (hmemFF _ (gcomp_mem_gpair k).2 _ (gcomp_mem_gpair j).1)
      hE (hMom k hkS j hjS)
      (fun t' ht' c' hc' w' hw' => hscrS j hjS t' ht' k hkS c' hc' w' hw'))
      (le_of_eq hrowB.symm)
  rw [crossInterpScreen_fresh_split α Rv μ νL νR v0 z (some Tgt.F) h]
  have hpt : ∀ s : V × ℕ,
      freshQ μ νL s * screenE (muM (varyK μ νL v0) s (h + 1))
          (fullSim (labRel Rv) (h + 1))
          ((z.toList).map (interpT μ νR v0 (h + 1)))
          (interpNorm α Rv μ νR v0 (h + 1) (some Tgt.F))
        ≤ (if Rv s.1 v0 then 0
            else (μ s.1 : ℝ≥0∞) * WresD α μ Rv s.1 * (νL s.2 : ℝ≥0∞)
              * (TνR * PB))
          + freshQ μ νL s * (RT * (TνR * rowB)) := by
    rintro ⟨v, k⟩
    by_cases hv : Rv v v0
    · rw [if_pos hv, zero_add]
      by_cases hk : (νL k : ℝ≥0∞) = 0
      · rw [show freshQ μ νL (v, k) = 0 from by
            rw [show freshQ μ νL (v, k) = μ v * νL k from
              prodPMF_apply μ νL (v, k), hk, mul_zero],
          zero_mul, zero_mul]
      · exact mul_le_mul_right (hnear v k hv ((hLsupp k).mp hk)) _
    · rw [if_neg hv]
      refine le_trans ?_ le_self_add
      by_cases hk : (νL k : ℝ≥0∞) = 0
      · rw [show freshQ μ νL (v, k) = 0 from by
            rw [show freshQ μ νL (v, k) = μ v * νL k from
              prodPMF_apply μ νL (v, k), hk, mul_zero], zero_mul]
        exact zero_le
      · refine le_trans (mul_le_mul_right (hfar v k hv hk) _) (le_of_eq ?_)
        rw [show freshQ μ νL (v, k) = μ v * νL k from prodPMF_apply μ νL (v, k)]
        ring
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_add]
  refine add_le_add ?_ ?_
  · have h1 : ∀ s : V × ℕ,
        (if Rv s.1 v0 then 0
          else (μ s.1 : ℝ≥0∞) * WresD α μ Rv s.1 * (νL s.2 : ℝ≥0∞)
            * (TνR * PB))
        = ((if Rv s.1 v0 then 0
            else (μ s.1 : ℝ≥0∞) * WresD α μ Rv s.1) * (TνR * PB))
          * (νL s.2 : ℝ≥0∞) := by
      intro s
      by_cases hv : Rv s.1 v0
      · rw [if_pos hv, if_pos hv, zero_mul, zero_mul]
      · rw [if_neg hv, if_neg hv]; ring
    rw [tsum_congr h1, tsum_prod_split
      (fun v => (if Rv v v0 then 0
        else (μ v : ℝ≥0∞) * WresD α μ Rv v) * (TνR * PB))
      (fun l => (νL l : ℝ≥0∞)), νL.tsum_coe, mul_one, ENNReal.tsum_mul_right]
    exact mul_le_mul_left hFT _
  · rw [ENNReal.tsum_mul_right, (freshQ μ νL).tsum_coe, one_mul, mul_assoc]

end GraphMarkovMatching
