/-
The varying-offspring process of `arbitrary_offspring_matching.tex`
(`sec:statement`): the binary-tree encoding of an arbitrary finitely
supported offspring law.

States are pairs `(v, k)` of a label `v` (only the label is matched) and a
counter `k`.  A fresh sample draws `(v, k) ~ μ ⊗ ν`; the distinguished
forced label is `v0`.  The splitting rules:

* `k ≥ 4`: both children forced, `(v0, ⌊k/2⌋)` and `(v0, ⌈k/2⌉)`;
* `k = 3`: left child forced `(v0, 2)`, right child fresh;
* `k ≤ 2`: both children fresh.

This is a Markov label system in the sense of `Process/Basic.lean`, so the
whole `muM` infrastructure applies.  The per-state kernel budgets are
infinite for this system (the phenomenon certified in
`Archive/CaretObstruction.lean`), so the matching theorem is instead proved
by the change-of-measure route (`Process/Contraction.lean`); this file
provides the structural inputs:

* the fresh law `Tlaw`, the forced-context laws `Zlaw`, the child-pair
  component laws `Xi` and their mixture `XiBar`;
* the component product identities (`Xi_of_le_two`, `Xi_three`,
  `Xi_of_four_le`);
* the component domination `Q(v0,k) · Z_k ≤ T` and the two-sided mixture
  comparison `ν₂ · T⊗T ≤ Ξ̄ ≤ C̄ · T⊗T` under halving closure;
* certain mismatch at incompatible roots (`qE_succ_branch_mismatch`).
-/
import GraphMarkovMatching.Process.TreePotential

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u

/-! ### Certain mismatch at incompatible roots -/

variable {S : Type u}

/-- If the attached roots are incompatible, the bad degree of the attached
sample against the started tree law is one: matching fails certainly. -/
lemma qE_succ_branch_mismatch (P : S → PMF (S × S)) (R₀ : S → S → Prop)
    {s t : S} (hst : ¬ R₀ s t) (n : ℕ) (xp : FullLab S n × FullLab S n) :
    qE (muM P t (n + 1)) (fullSim R₀ (n + 1)) (branch s xp) = 1 := by
  have hr : rE (muM P t (n + 1)) (fullSim R₀ (n + 1)) (branch s xp) = 0 := by
    rw [rE]
    refine ENNReal.tsum_eq_zero.mpr fun y => ?_
    by_cases hy : fullSim R₀ (n + 1) (branch s xp) y
    · rw [if_pos hy]
      by_contra hne
      have hroot := fullSim_root R₀ (n + 1) _ _ hy
      rw [rootLab_branch, rootLab_of_ne_zero P (n + 1) t y hne] at hroot
      exact hst hroot
    · rw [if_neg hy]
  have h := rE_add_qE (muM P t (n + 1)) (fullSim R₀ (n + 1)) (branch s xp)
  rw [hr, zero_add] at h
  exact h

/-! ### States, relation, kernel -/

variable {V : Type}

/-- The matching relation on states sees only the label. -/
def labRel (Rv : V → V → Prop) : V × ℕ → V × ℕ → Prop := fun s t => Rv s.1 t.1

lemma labRel_symm (Rv : V → V → Prop) (h : ∀ a b, Rv a b → Rv b a) :
    ∀ s t, labRel Rv s t → labRel Rv t s := fun _ _ hst => h _ _ hst

/-- The fresh law `Q = μ ⊗ ν`. -/
noncomputable def freshQ (μ : PMF V) (ν : PMF ℕ) : PMF (V × ℕ) := prodPMF μ ν

variable (μ : PMF V) (ν : PMF ℕ) (v0 : V)

/-- The varying-offspring kernel. -/
noncomputable def varyK : V × ℕ → PMF ((V × ℕ) × (V × ℕ)) := fun s =>
  if 4 ≤ s.2 then PMF.pure ((v0, s.2 / 2), (v0, s.2 - s.2 / 2))
  else if s.2 = 3 then (freshQ μ ν).map fun f => ((v0, 2), f)
  else prodPMF (freshQ μ ν) (freshQ μ ν)

/-! ### The context laws -/

/-- The fresh height-`h` law: root a fresh `Q`-sample. -/
noncomputable def Tlaw (h : ℕ) : PMF (FullLab (V × ℕ) h) :=
  (freshQ μ ν).bind fun s => muM (varyK μ ν v0) s h

/-- The forced-context law with counter `k`. -/
noncomputable def Zlaw (k h : ℕ) : PMF (FullLab (V × ℕ) h) :=
  muM (varyK μ ν v0) (v0, k) h

/-- The child-pair component law below a counter-`k` root. -/
noncomputable def Xi (k h : ℕ) : PMF (FullLab (V × ℕ) h × FullLab (V × ℕ) h) :=
  pairMix (varyK μ ν v0) (v0, k) h

/-- The full child-pair mixture below a fresh root. -/
noncomputable def XiBar (h : ℕ) : PMF (FullLab (V × ℕ) h × FullLab (V × ℕ) h) :=
  ν.bind fun k => Xi μ ν v0 k h

/-- The kernel is label-blind, hence so is the pair mixture. -/
lemma pairMix_varyK (v : V) (k h : ℕ) :
    pairMix (varyK μ ν v0) (v, k) h = Xi μ ν v0 k h := rfl

lemma muM_varyK_succ (v : V) (k h : ℕ) :
    muM (varyK μ ν v0) (v, k) (h + 1) = (Xi μ ν v0 k h).map (branch (v, k)) := rfl

/-! ### Product identities -/

/-- Componentwise binding of a product source gives the product of binds. -/
lemma prodPMF_bind_prodPMF {A B C D : Type*} (p : PMF A) (q : PMF B)
    (f : A → PMF C) (g : B → PMF D) :
    (prodPMF p q).bind (fun z => prodPMF (f z.1) (g z.2))
      = prodPMF (p.bind f) (q.bind g) := by
  apply PMF.ext
  intro x
  simp only [PMF.bind_apply, prodPMF_apply]
  calc (∑' z : A × B, p z.1 * q z.2 * (f z.1 x.1 * g z.2 x.2))
      = ∑' z : A × B, (p z.1 * f z.1 x.1) * (q z.2 * g z.2 x.2) :=
        tsum_congr fun z => by ring
    _ = (∑' a, p a * f a x.1) * (∑' b, q b * g b x.2) :=
        tsum_prod_split (fun a => p a * f a x.1) (fun b => q b * g b x.2)

/-- Binding only the second coordinate against a constant first factor. -/
lemma bind_prodPMF_const_left {B C D : Type*} (Z : PMF C) (qb : PMF B) (g : B → PMF D) :
    qb.bind (fun b => prodPMF Z (g b)) = prodPMF Z (qb.bind g) := by
  apply PMF.ext
  intro x
  simp only [PMF.bind_apply, prodPMF_apply]
  calc (∑' b, qb b * (Z x.1 * g b x.2))
      = ∑' b, Z x.1 * (qb b * g b x.2) := tsum_congr fun b => by ring
    _ = Z x.1 * ∑' b, qb b * g b x.2 := ENNReal.tsum_mul_left

/-! ### The three component shapes -/

lemma varyK_of_four_le {k : ℕ} (hk : 4 ≤ k) (v : V) :
    varyK μ ν v0 (v, k) = PMF.pure ((v0, k / 2), (v0, k - k / 2)) := by
  show (if 4 ≤ k then PMF.pure ((v0, k / 2), (v0, k - k / 2))
    else if k = 3 then (freshQ μ ν).map fun f => ((v0, 2), f)
    else prodPMF (freshQ μ ν) (freshQ μ ν)) = _
  rw [if_pos hk]

lemma varyK_three (v : V) :
    varyK μ ν v0 (v, 3) = (freshQ μ ν).map fun f => ((v0, 2), f) := by
  show (if 4 ≤ 3 then PMF.pure ((v0, 3 / 2), (v0, 3 - 3 / 2))
    else if 3 = 3 then (freshQ μ ν).map fun f => ((v0, 2), f)
    else prodPMF (freshQ μ ν) (freshQ μ ν)) = _
  rw [if_neg (by omega), if_pos rfl]

lemma varyK_of_le_two {k : ℕ} (hk : k ≤ 2) (v : V) :
    varyK μ ν v0 (v, k) = prodPMF (freshQ μ ν) (freshQ μ ν) := by
  show (if 4 ≤ k then PMF.pure ((v0, k / 2), (v0, k - k / 2))
    else if k = 3 then (freshQ μ ν).map fun f => ((v0, 2), f)
    else prodPMF (freshQ μ ν) (freshQ μ ν)) = _
  rw [if_neg (by omega), if_neg (by omega)]

lemma Xi_of_four_le {k : ℕ} (hk : 4 ≤ k) (h : ℕ) :
    Xi μ ν v0 k h
      = prodPMF (Zlaw μ ν v0 (k / 2) h) (Zlaw μ ν v0 (k - k / 2) h) := by
  rw [Xi, pairMix, varyK_of_four_le μ ν v0 hk, PMF.pure_bind]
  rfl

lemma Xi_three (h : ℕ) :
    Xi μ ν v0 3 h = prodPMF (Zlaw μ ν v0 2 h) (Tlaw μ ν v0 h) := by
  rw [Xi, pairMix, varyK_three μ ν v0, PMF.bind_map]
  rw [show ((fun στ : (V × ℕ) × (V × ℕ) =>
        prodPMF (muM (varyK μ ν v0) στ.1 h) (muM (varyK μ ν v0) στ.2 h))
      ∘ fun f => ((v0, 2), f))
    = fun f => prodPMF (Zlaw μ ν v0 2 h) (muM (varyK μ ν v0) f h) from rfl]
  exact bind_prodPMF_const_left _ _ _

lemma Xi_of_le_two {k : ℕ} (hk : k ≤ 2) (h : ℕ) :
    Xi μ ν v0 k h = prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) := by
  rw [Xi, pairMix, varyK_of_le_two μ ν v0 hk]
  exact prodPMF_bind_prodPMF (freshQ μ ν) (freshQ μ ν)
    (fun s => muM (varyK μ ν v0) s h) (fun s => muM (varyK μ ν v0) s h)

/-! ### Component domination -/

/-- Every forced context is a component of the fresh law. -/
lemma mul_Zlaw_le_Tlaw (k h : ℕ) (x : FullLab (V × ℕ) h) :
    freshQ μ ν (v0, k) * Zlaw μ ν v0 k h x ≤ Tlaw μ ν v0 h x := by
  rw [Tlaw, PMF.bind_apply]
  exact ENNReal.le_tsum (v0, k)

lemma Zlaw_le_inv_mul_Tlaw {k : ℕ} (hk : freshQ μ ν (v0, k) ≠ 0) (h : ℕ)
    (x : FullLab (V × ℕ) h) :
    Zlaw μ ν v0 k h x ≤ (freshQ μ ν (v0, k))⁻¹ * Tlaw μ ν v0 h x := by
  calc Zlaw μ ν v0 k h x
      = ((freshQ μ ν (v0, k))⁻¹ * freshQ μ ν (v0, k)) * Zlaw μ ν v0 k h x := by
        rw [ENNReal.inv_mul_cancel hk (PMF.apply_ne_top _ _), one_mul]
    _ = (freshQ μ ν (v0, k))⁻¹ * (freshQ μ ν (v0, k) * Zlaw μ ν v0 k h x) := by
        rw [mul_assoc]
    _ ≤ (freshQ μ ν (v0, k))⁻¹ * Tlaw μ ν v0 h x :=
        mul_le_mul_right (mul_Zlaw_le_Tlaw μ ν v0 k h x) _

/-- **The mixture lower bound**: the counter-`2` component supplies the
product `ν₂ · T ⊗ T ≤ Ξ̄`. -/
lemma XiBar_ge (h : ℕ) (x : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    ν 2 * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x ≤ XiBar μ ν v0 h x := by
  rw [XiBar, PMF.bind_apply, ← Xi_of_le_two μ ν v0 (le_refl 2) h]
  exact ENNReal.le_tsum 2

/-! ### The mixture upper bound under halving closure -/

/-- The per-component change-of-measure factor. -/
noncomputable def Cfac (k : ℕ) : ℝ≥0∞ :=
  if 4 ≤ k then (freshQ μ ν (v0, k / 2))⁻¹ * (freshQ μ ν (v0, k - k / 2))⁻¹
  else if k = 3 then (freshQ μ ν (v0, 2))⁻¹
  else 1

/-- The mixture change-of-measure constant `C̄ = ∑ ν_k C_k`. -/
noncomputable def CBar : ℝ≥0∞ := ∑' k, ν k * Cfac μ ν v0 k

/-- Halving closure: the distinguished label is charged, and every forced
counter arising below a charged fresh counter is itself charged. -/
def HalvingClosed : Prop :=
  μ v0 ≠ 0 ∧ (∀ k, ν k ≠ 0 → 4 ≤ k → ν (k / 2) ≠ 0 ∧ ν (k - k / 2) ≠ 0)
    ∧ (ν 3 ≠ 0 → ν 2 ≠ 0)

lemma one_le_inv_of_le_one {a : ℝ≥0∞} (ha : a ≤ 1) : 1 ≤ a⁻¹ := by
  rcases eq_or_ne a 0 with rfl | h0
  · simp
  · calc (1 : ℝ≥0∞) = a⁻¹ * a :=
        (ENNReal.inv_mul_cancel h0 (ne_top_of_le_ne_top ENNReal.one_ne_top ha)).symm
    _ ≤ a⁻¹ * 1 := mul_le_mul_right ha _
    _ = a⁻¹ := mul_one _

lemma one_le_Cfac (k : ℕ) : 1 ≤ Cfac μ ν v0 k := by
  rw [Cfac]
  split_ifs with h4 h3
  · calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
      _ ≤ _ := mul_le_mul' (one_le_inv_of_le_one (PMF.coe_le_one _ _))
          (one_le_inv_of_le_one (PMF.coe_le_one _ _))
  · exact one_le_inv_of_le_one (PMF.coe_le_one _ _)
  · exact le_refl 1

lemma one_le_CBar : 1 ≤ CBar μ ν v0 := by
  calc (1 : ℝ≥0∞) = ∑' k, ν k := ν.tsum_coe.symm
    _ ≤ ∑' k, ν k * Cfac μ ν v0 k :=
        ENNReal.tsum_le_tsum fun k => by
          calc (ν k : ℝ≥0∞) = ν k * 1 := (mul_one _).symm
            _ ≤ ν k * Cfac μ ν v0 k := mul_le_mul_right (one_le_Cfac μ ν v0 k) _
    _ = CBar μ ν v0 := rfl

lemma Xi_le_Cfac (hcl : HalvingClosed μ ν v0) {k : ℕ} (hνk : ν k ≠ 0) (h : ℕ)
    (x : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    Xi μ ν v0 k h x
      ≤ Cfac μ ν v0 k * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x := by
  obtain ⟨hμ0, hcl4, hcl3⟩ := hcl
  by_cases h4 : 4 ≤ k
  · obtain ⟨hL, hR⟩ := hcl4 k hνk h4
    have hqL : freshQ μ ν (v0, k / 2) ≠ 0 := by
      rw [show freshQ μ ν (v0, k / 2) = μ v0 * ν (k / 2) from rfl]
      exact mul_ne_zero hμ0 hL
    have hqR : freshQ μ ν (v0, k - k / 2) ≠ 0 := by
      rw [show freshQ μ ν (v0, k - k / 2) = μ v0 * ν (k - k / 2) from rfl]
      exact mul_ne_zero hμ0 hR
    rw [Xi_of_four_le μ ν v0 h4 h, Cfac, if_pos h4, prodPMF_apply, prodPMF_apply]
    calc Zlaw μ ν v0 (k / 2) h x.1 * Zlaw μ ν v0 (k - k / 2) h x.2
        ≤ ((freshQ μ ν (v0, k / 2))⁻¹ * Tlaw μ ν v0 h x.1)
            * ((freshQ μ ν (v0, k - k / 2))⁻¹ * Tlaw μ ν v0 h x.2) :=
          mul_le_mul' (Zlaw_le_inv_mul_Tlaw μ ν v0 hqL h x.1)
            (Zlaw_le_inv_mul_Tlaw μ ν v0 hqR h x.2)
      _ = (freshQ μ ν (v0, k / 2))⁻¹ * (freshQ μ ν (v0, k - k / 2))⁻¹
            * (Tlaw μ ν v0 h x.1 * Tlaw μ ν v0 h x.2) := by ring
  · by_cases h3 : k = 3
    · subst h3
      have hq2 : freshQ μ ν (v0, 2) ≠ 0 := by
        rw [show freshQ μ ν (v0, 2) = μ v0 * ν 2 from rfl]
        exact mul_ne_zero hμ0 (hcl3 hνk)
      rw [Xi_three μ ν v0 h, Cfac, if_neg (by omega), if_pos rfl,
        prodPMF_apply, prodPMF_apply]
      calc Zlaw μ ν v0 2 h x.1 * Tlaw μ ν v0 h x.2
          ≤ ((freshQ μ ν (v0, 2))⁻¹ * Tlaw μ ν v0 h x.1) * Tlaw μ ν v0 h x.2 :=
            mul_le_mul_left (Zlaw_le_inv_mul_Tlaw μ ν v0 hq2 h x.1) _
        _ = (freshQ μ ν (v0, 2))⁻¹ * (Tlaw μ ν v0 h x.1 * Tlaw μ ν v0 h x.2) := by
            rw [mul_assoc]
    · have hk2 : k ≤ 2 := by omega
      rw [Xi_of_le_two μ ν v0 hk2 h, Cfac, if_neg h4, if_neg h3, one_mul]

/-- **The mixture upper bound**: under halving closure `Ξ̄ ≤ C̄ · T ⊗ T`. -/
lemma XiBar_le_CBar (hcl : HalvingClosed μ ν v0) (h : ℕ)
    (x : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    XiBar μ ν v0 h x
      ≤ CBar μ ν v0 * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x := by
  rw [XiBar, PMF.bind_apply, CBar, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hνk : ν k = 0
  · simp [hνk]
  · calc ν k * Xi μ ν v0 k h x
        ≤ ν k * (Cfac μ ν v0 k * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x) :=
          mul_le_mul_right (Xi_le_Cfac μ ν v0 hcl hνk h x) _
      _ = ν k * Cfac μ ν v0 k * prodPMF (Tlaw μ ν v0 h) (Tlaw μ ν v0 h) x := by
          rw [mul_assoc]

end GraphMarkovMatching
