/-
The base case of the `ν = δ₃` screen system
(`arbitrary_offspring_matching.tex`, base case of the closure induction):
at height zero the live screens and masses are far-label quantities, bounded
by the zero-interface estimates:

* the fresh-source screen `e₂` and the fresh-source mass `z_{TZ}` are the
  far tilt and the far mass, at most `2η` by `far_tilt_le`/`qE_zero_le`;
* the forced-source screens and the forced-source mass vanish, because
  the root `v0` is charged (`μ(v0) ≥ 1/2` and reflexivity).
-/
import GraphMarkovMatching.Process.Descent
import GraphMarkovMatching.Process.ScreenBridges

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u

/-- The good degree against a point mass. -/
lemma rE_pure {X : Type u} (b : X) (R : X → X → Prop) (z : X) :
    rE (PMF.pure b) R z = if R z b then 1 else 0 := by
  rw [rE_eq_tsum_mul, tsum_pure_mul b (goodInd R z), goodInd]

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-- The height-zero fresh tilt is the label tilt. -/
lemma WresD_Tlaw_zero_le (ν : PMF ℕ) (v : V) (k : ℕ) :
    WresD α (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0) (leaf (v, k))
      ≤ (rE μ Rv v) ^ (-α) := by
  by_cases hres : rE (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0)
      (leaf (v, k)) = 0
  · rw [WresD, if_pos hres]
    exact zero_le
  · rw [← rE_rpow_neg_eq_WresD (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0)
      (leaf (v, k)) hres, rE_Tlaw_zero Rv μ ν v0 v k]

/-- The height-zero forced target is dead exactly at far roots. -/
lemma rE_Zlaw_zero_eq (ν : PMF ℕ) (v : V) (k j : ℕ) :
    rE (Zlaw μ ν v0 j 0) (fullSim (labRel Rv) 0) (leaf (v, k))
      = if Rv v v0 then 1 else 0 := by
  rw [show Zlaw μ ν v0 j 0 = PMF.pure (leaf (v0, j)) from rfl,
    rE_pure]
  by_cases hv : Rv v v0
  · rw [if_pos ((fullSim_leaf (labRel Rv) (v, k) (v0, j)).mpr hv),
      if_pos hv]
  · rw [if_neg (fun hc =>
      hv ((fullSim_leaf (labRel Rv) (v, k) (v0, j)).mp hc)), if_neg hv]

/-- **Base of the fresh-source screen** (`e₂` at height zero): at most the
far tilt, hence at most `2η`. -/
lemma delta3_e2_base (hα : 0 < α)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0) :
    screenE (Tlaw μ (PMF.pure 3) v0 0) (fullSim (labRel Rv) 0)
        [Zlaw μ (PMF.pure 3) v0 2 0]
        (WresD α (Tlaw μ (PMF.pure 3) v0 0) (fullSim (labRel Rv) 0))
      ≤ 2 * etaG α Rv μ := by
  rw [screenE_singleton,
    show Tlaw μ (PMF.pure 3) v0 0 = (freshQ μ (PMF.pure 3)).bind
      (fun s => muM (varyK μ (PMF.pure 3) v0) s 0) from rfl,
    tsum_bind_mul]
  calc ∑' s : V × ℕ, freshQ μ (PMF.pure 3) s
        * ∑' x, muM (varyK μ (PMF.pure 3) v0) s 0 x
          * ((if rE (Zlaw μ (PMF.pure 3) v0 2 0) (fullSim (labRel Rv) 0) x
                = 0 then 1 else 0)
            * WresD α (Tlaw μ (PMF.pure 3) v0 0) (fullSim (labRel Rv) 0) x)
      ≤ ∑' s : V × ℕ, freshQ μ (PMF.pure 3) s
          * ((if Rv v0 s.1 then 0 else (rE μ Rv s.1) ^ (-α))) := by
        refine ENNReal.tsum_le_tsum fun s => mul_le_mul_right ?_ _
        obtain ⟨v, k⟩ := s
        rw [show muM (varyK μ (PMF.pure 3) v0) (v, k) 0
            = PMF.pure (leaf (v, k)) from rfl,
          tsum_pure_mul (leaf (v, k)) (fun x =>
            (if rE (Zlaw μ (PMF.pure 3) v0 2 0) (fullSim (labRel Rv) 0) x
                = 0 then 1 else 0)
              * WresD α (Tlaw μ (PMF.pure 3) v0 0)
                  (fullSim (labRel Rv) 0) x)]
        by_cases hv : Rv v v0
        · rw [rE_Zlaw_zero_eq Rv μ v0 (PMF.pure 3) v k 2, if_pos hv,
            if_neg one_ne_zero, zero_mul]
          exact zero_le
        · rw [rE_Zlaw_zero_eq Rv μ v0 (PMF.pure 3) v k 2, if_neg hv,
            if_pos rfl, one_mul,
            if_neg (fun hc : Rv v0 v => hv (hsymm v0 v hc))]
          exact WresD_Tlaw_zero_le α Rv μ v0 (PMF.pure 3) v k
    _ = ∑' v, if Rv v0 v then 0 else μ v * (rE μ Rv v) ^ (-α) := by
        rw [tsum_congr fun s : V × ℕ => show freshQ μ (PMF.pure 3) s
            * (if Rv v0 s.1 then 0 else (rE μ Rv s.1) ^ (-α))
            = (if Rv v0 s.1 then 0 else μ s.1 * (rE μ Rv s.1) ^ (-α))
              * (PMF.pure 3 : PMF ℕ) s.2
            from by
              rw [show freshQ μ (PMF.pure 3) s
                = μ s.1 * (PMF.pure 3 : PMF ℕ) s.2 from rfl]
              by_cases hv : Rv v0 s.1 <;> simp [hv],
          tsum_prod_split
            (fun v => if Rv v0 v then 0 else μ v * (rE μ Rv v) ^ (-α))
            (fun k => (PMF.pure 3 : PMF ℕ) k), PMF.tsum_coe, mul_one]
    _ ≤ 2 * etaG α Rv μ := far_tilt_le α Rv μ v0 hα hsymm hhalf

/-- **Base of the forced-source screens** (`e₄`, `e₆` at height zero):
the forced root is charged, so the fresh zero list is unsatisfiable. -/
lemma delta3_forced_screen_base (hrefl : Rv v0 v0) (hhalf : 2⁻¹ ≤ μ v0)
    (nrm : FullLab (V × ℕ) 0 → ℝ≥0∞) :
    screenE (Zlaw μ (PMF.pure 3) v0 2 0) (fullSim (labRel Rv) 0)
        [Tlaw μ (PMF.pure 3) v0 0] nrm = 0 := by
  rw [screenE_singleton,
    show Zlaw μ (PMF.pure 3) v0 2 0 = PMF.pure (leaf (v0, 2)) from rfl,
    tsum_pure_mul (leaf (v0, 2)) (fun x =>
      (if rE (Tlaw μ (PMF.pure 3) v0 0) (fullSim (labRel Rv) 0) x = 0
        then 1 else 0) * nrm x)]
  have hne : rE (Tlaw μ (PMF.pure 3) v0 0) (fullSim (labRel Rv) 0)
      (leaf (v0, 2)) ≠ 0 := by
    rw [rE_Tlaw_zero Rv μ (PMF.pure 3) v0 v0 2]
    intro h0
    have hle : μ v0 ≤ rE μ Rv v0 := le_rE_of_refl hrefl
    rw [h0] at hle
    have : (2⁻¹ : ℝ≥0∞) ≤ 0 := le_trans hhalf hle
    simp at this
  rw [if_neg hne, zero_mul]

/-- **Base of the forced-source mass** (`z_{ZT}` at height zero). -/
lemma delta3_zZT_base (hrefl : Rv v0 v0) (hhalf : 2⁻¹ ≤ μ v0) :
    zMass (Zlaw μ (PMF.pure 3) v0 2 0) (Tlaw μ (PMF.pure 3) v0 0)
      (fullSim (labRel Rv) 0) = 0 := by
  rw [← screenE_one_eq_zMass]
  exact delta3_forced_screen_base Rv μ v0 hrefl hhalf _

/-- **Base of the fresh-source mass** (`z_{TZ}` at height zero): the far
mass, at most `2η`. -/
lemma delta3_zTZ_base (hα : 0 ≤ α)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0) :
    zMass (Tlaw μ (PMF.pure 3) v0 0) (Zlaw μ (PMF.pure 3) v0 2 0)
        (fullSim (labRel Rv) 0)
      ≤ 2 * etaG α Rv μ := by
  rw [zMass,
    show Tlaw μ (PMF.pure 3) v0 0 = (freshQ μ (PMF.pure 3)).bind
      (fun s => muM (varyK μ (PMF.pure 3) v0) s 0) from rfl,
    tsum_bind_mul]
  calc ∑' s : V × ℕ, freshQ μ (PMF.pure 3) s
        * ∑' x, muM (varyK μ (PMF.pure 3) v0) s 0 x
          * (if rE (Zlaw μ (PMF.pure 3) v0 2 0) (fullSim (labRel Rv) 0) x
              = 0 then 1 else 0)
      ≤ ∑' s : V × ℕ, freshQ μ (PMF.pure 3) s
          * (if Rv v0 s.1 then 0 else 1) := by
        refine ENNReal.tsum_le_tsum fun s => mul_le_mul_right ?_ _
        obtain ⟨v, k⟩ := s
        rw [show muM (varyK μ (PMF.pure 3) v0) (v, k) 0
            = PMF.pure (leaf (v, k)) from rfl,
          tsum_pure_mul (leaf (v, k)) (fun x =>
            if rE (Zlaw μ (PMF.pure 3) v0 2 0) (fullSim (labRel Rv) 0) x
              = 0 then 1 else 0),
          rE_Zlaw_zero_eq Rv μ v0 (PMF.pure 3) v k 2]
        by_cases hv : Rv v v0
        · rw [if_pos hv, if_neg one_ne_zero]
          exact zero_le
        · rw [if_neg hv, if_pos rfl,
            if_neg (fun hc : Rv v0 v => hv (hsymm v0 v hc))]
    _ = ∑' v, if Rv v0 v then 0 else μ v := by
        rw [tsum_congr fun s : V × ℕ => show freshQ μ (PMF.pure 3) s
            * (if Rv v0 s.1 then 0 else 1)
            = (if Rv v0 s.1 then 0 else μ s.1)
              * (PMF.pure 3 : PMF ℕ) s.2
            from by
              rw [show freshQ μ (PMF.pure 3) s
                = μ s.1 * (PMF.pure 3 : PMF ℕ) s.2 from rfl]
              by_cases hv : Rv v0 s.1 <;> simp [hv],
          tsum_prod_split (fun v => if Rv v0 v then 0 else μ v)
            (fun k => (PMF.pure 3 : PMF ℕ) k), PMF.tsum_coe, mul_one]
    _ ≤ 2 * etaG α Rv μ := by
        rw [show (∑' v, if Rv v0 v then 0 else μ v) = qE μ Rv v0 from rfl]
        exact qE_zero_le α Rv μ v0 hα hhalf

end GraphMarkovMatching
