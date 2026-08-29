/-
The closure keystone of the `ν = δ₃` instantiation
(`arbitrary_offspring_matching.tex`, the induction of `thm:main-matching` at pure
ternary law): the concrete coordinate system, the five-dimensional screen
matrix with its nilpotence certificate and invariant bound, and the
uniform failure theorem.

* `delta3Psi` / `delta3E`: the ordinary supremum and the screen vector
  `(e₄, e₆, z_{ZT}, e₂, z_{TZ})`;
* `delta3N`: the screen matrix — `e₂` receives the two forced-source
  screens with the full-tilt constant, `z_{TZ}` receives `z_{ZT}` with
  coefficient one, everything else vanishes;
* `delta3N_nilpotent`: `N² = 0` by the rank certificate
  `(0,0,0,1,1)`;
* `delta3_nilSum_le`: the invariant vector is at most `u·(2 + 2·tilt)`;
* `delta3_failure_uniform`: given the two assembled step bounds (the
  ordinary and screen rows massaged into monotone step functions, the
  remaining assembly), the base values, and the closure inequalities,
  the matching failure is at most `Kc·η` at every height.
-/
import GraphMarkovMatching.Delta3.Rows
import GraphMarkovMatching.Delta3.ScreensA
import GraphMarkovMatching.Delta3.ScreensB
import GraphMarkovMatching.Delta3.Base
import GraphMarkovMatching.Process.Failure
import GraphMarkovMatching.Grammar.Nilpotence
import GraphMarkovMatching.Potential.Numerals

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (v0 : V)

/-- The full label tilt `∑_v μ(v) r(v)^{-α}` (bounded by `2^α + 2η`
through `tilt_le_pow_add`; enters the screen matrix as a constant). -/
noncomputable def delta3Tilt : ℝ≥0∞ :=
  ∑' v, μ v * (rE μ Rv v) ^ (-α)

/-- The ordinary block supremum: the four restricted state coordinates. -/
noncomputable def delta3Psi (h : ℕ) : ℝ≥0∞ :=
  PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h) (Zlaw μ (PMF.pure 3) v0 2 h)
      (fullSim (labRel Rv) h)
    ⊔ PhiDres α (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
      (fullSim (labRel Rv) h)
    ⊔ PhiDres α (Tlaw μ (PMF.pure 3) v0 h) (Zlaw μ (PMF.pure 3) v0 2 h)
      (fullSim (labRel Rv) h)
    ⊔ PhiDres α (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
      (fullSim (labRel Rv) h)

/-- The screen vector `(e₄, e₆, z_{ZT}, e₂, z_{TZ})`. -/
noncomputable def delta3E (h : ℕ) : Fin 5 → ℝ≥0∞ :=
  ![screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
      [Tlaw μ (PMF.pure 3) v0 h]
      (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)),
    screenE (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)
      [Tlaw μ (PMF.pure 3) v0 h]
      (WresD α (Zlaw μ (PMF.pure 3) v0 2 h) (fullSim (labRel Rv) h)),
    zMass (Zlaw μ (PMF.pure 3) v0 2 h) (Tlaw μ (PMF.pure 3) v0 h)
      (fullSim (labRel Rv) h),
    screenE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)
      [Zlaw μ (PMF.pure 3) v0 2 h]
      (WresD α (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h)),
    zMass (Tlaw μ (PMF.pure 3) v0 h) (Zlaw μ (PMF.pure 3) v0 2 h)
      (fullSim (labRel Rv) h)]

/-- The screen matrix: rows `0,1,2` (the forced-source coordinates)
vanish; row `3` (`e₂`) carries the full tilt toward `e₄` and `e₆`;
row `4` (`z_{TZ}`) carries `z_{ZT}` with coefficient one. -/
noncomputable def delta3N : Fin 5 → Fin 5 → ℝ≥0∞ := fun i j =>
  if i = 3 ∧ (j = 0 ∨ j = 1) then delta3Tilt α Rv μ
  else if i = 4 ∧ j = 2 then 1 else 0

/-- **Nilpotence of the `δ₃` screen matrix**: the rank certificate
`(0, 0, 0, 1, 1)` decreases along the support, so `N² = 0`. -/
lemma delta3N_nilpotent (u : ℝ≥0∞) :
    (mulVec (delta3N α Rv μ))^[2] (fun _ => u) = fun _ => 0 := by
  refine nilpotent_of_rank (delta3N α Rv μ)
    (fun i => if i = 3 ∨ i = 4 then 1 else 0) 2 ?_ ?_ (fun _ => u)
  · intro i j hij
    by_cases h3 : i = 3 ∧ (j = 0 ∨ j = 1)
    · obtain ⟨hi, hj⟩ := h3
      subst hi
      rcases hj with hj | hj <;> subst hj <;> simp
    · by_cases h4 : i = 4 ∧ j = 2
      · obtain ⟨hi, hj⟩ := h4
        subst hi; subst hj
        simp
      · rw [delta3N, if_neg h3, if_neg h4] at hij
        exact absurd rfl hij
  · intro i
    by_cases h : i = 3 ∨ i = 4 <;> simp [h]

/-- The `δ₃` matrix applied to a constant vector. -/
lemma delta3N_mulVec_const (u : ℝ≥0∞) (i : Fin 5) :
    mulVec (delta3N α Rv μ) (fun _ => u) i
      ≤ u * (1 + 2 * delta3Tilt α Rv μ) := by
  rw [mulVec, Fin.sum_univ_five]
  fin_cases i
  · simp [delta3N]
  · simp [delta3N]
  · simp [delta3N]
  · show delta3N α Rv μ 3 0 * u + delta3N α Rv μ 3 1 * u
        + delta3N α Rv μ 3 2 * u + delta3N α Rv μ 3 3 * u
        + delta3N α Rv μ 3 4 * u
      ≤ u * (1 + 2 * delta3Tilt α Rv μ)
    rw [show delta3N α Rv μ 3 0 = delta3Tilt α Rv μ from by simp [delta3N],
      show delta3N α Rv μ 3 1 = delta3Tilt α Rv μ from by simp [delta3N],
      show delta3N α Rv μ 3 2 = 0 from by simp [delta3N],
      show delta3N α Rv μ 3 3 = 0 from by simp [delta3N],
      show delta3N α Rv μ 3 4 = 0 from by simp [delta3N]]
    calc delta3Tilt α Rv μ * u + delta3Tilt α Rv μ * u + 0 * u + 0 * u
          + 0 * u
        = u * (2 * delta3Tilt α Rv μ) := by ring
      _ ≤ u * (1 + 2 * delta3Tilt α Rv μ) := mul_le_mul_right le_add_self u
  · show delta3N α Rv μ 4 0 * u + delta3N α Rv μ 4 1 * u
        + delta3N α Rv μ 4 2 * u + delta3N α Rv μ 4 3 * u
        + delta3N α Rv μ 4 4 * u
      ≤ u * (1 + 2 * delta3Tilt α Rv μ)
    rw [show delta3N α Rv μ 4 0 = 0 from by simp [delta3N],
      show delta3N α Rv μ 4 1 = 0 from by simp [delta3N],
      show delta3N α Rv μ 4 2 = 1 from by simp [delta3N],
      show delta3N α Rv μ 4 3 = 0 from by simp [delta3N],
      show delta3N α Rv μ 4 4 = 0 from by simp [delta3N]]
    calc (0 : ℝ≥0∞) * u + 0 * u + 1 * u + 0 * u + 0 * u
        = u * 1 := by ring
      _ ≤ u * (1 + 2 * delta3Tilt α Rv μ) := mul_le_mul_right le_self_add u

/-- The invariant screen vector is at most `u·(2 + 2·tilt)`. -/
lemma delta3_nilSum_le (u : ℝ≥0∞) (i : Fin 5) :
    nilSum (delta3N α Rv μ) 2 u i
      ≤ u * (2 + 2 * delta3Tilt α Rv μ) := by
  have hsum : nilSum (delta3N α Rv μ) 2 u i
      = u + mulVec (delta3N α Rv μ) (fun _ => u) i := by
    rw [nilSum, Finset.sum_range_succ, Finset.sum_range_one]
    rfl
  rw [hsum]
  calc u + mulVec (delta3N α Rv μ) (fun _ => u) i
      ≤ u + u * (1 + 2 * delta3Tilt α Rv μ) :=
        add_le_add le_rfl (delta3N_mulVec_const α Rv μ u i)
    _ = u * (2 + 2 * delta3Tilt α Rv μ) := by ring

/-- **The `δ₃` uniform failure bound, closure form**: given the two
assembled step bounds (monotone step functions dominating the ordinary
and screen rows), the closure inequalities at the bounds, and
`μ(v0) ≥ 1/2`, the matching failure is at most `Kc·η` at every height. -/
theorem delta3_failure_uniform
    (hα : 1 ≤ α) (hRv : ∀ v, Rv v v) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0)
    (f g : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞)
    (hf : ∀ a a' b b', a ≤ a' → b ≤ b' → f a b ≤ f a' b')
    (hg : ∀ a a' b b', a ≤ a' → b ≤ b' → g a b ≤ g a' b')
    (hΨstep : ∀ h, delta3Psi α Rv μ v0 (h + 1)
      ≤ f (delta3Psi α Rv μ v0 h) (⨆ i, delta3E α Rv μ v0 h i))
    (hEstep : ∀ h i, delta3E α Rv μ v0 (h + 1) i
      ≤ g (delta3Psi α Rv μ v0 h) (⨆ i, delta3E α Rv μ v0 h i)
        + mulVec (delta3N α Rv μ) (delta3E α Rv μ v0 h) i)
    (Kc η u Ξ : ℝ≥0∞)
    (hΞ : u * (2 + 2 * delta3Tilt α Rv μ) ≤ Ξ)
    (hKη1 : etaG α Rv μ ≤ Kc * η)
    (hKη2 : phiE α (q μ Rv v0) ≤ Kc * η)
    (hu0 : 2 * etaG α Rv μ ≤ u)
    (hu : g (Kc * η) Ξ ≤ u)
    (hclose : f (Kc * η) Ξ ≤ Kc * η) :
    ∀ h, (∑' x, Tlaw μ (PMF.pure 3) v0 h x
        * qE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) x)
      ≤ Kc * η := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hΨ : ∀ h, delta3Psi α Rv μ v0 h ≤ Kc * η := by
    refine screened_uniform_bound_mono (by norm_num : 0 < 2)
      (delta3Psi α Rv μ v0) (delta3E α Rv μ v0) f g hf hg Kc η u Ξ
      (delta3N_nilpotent α Rv μ u)
      (fun i => le_trans (delta3_nilSum_le α Rv μ u i) hΞ)
      ?_ ?_ hΨstep hEstep hu hclose
    · -- the ordinary base
      rw [delta3Psi]
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · rw [PhiDres_Zlaw_Zlaw_zero α Rv μ (PMF.pure 3) v0 (hRv v0) 2 2]
        exact zero_le
      · exact le_trans
          (PhiDres_Zlaw_Tlaw_zero α Rv μ (PMF.pure 3) v0 2) hKη2
      · rw [PhiDres_Tlaw_Zlaw_zero α Rv μ (PMF.pure 3) v0 2]
        exact zero_le
      · exact le_trans (PhiDres_Tlaw_Tlaw_zero_le α Rv μ (PMF.pure 3) v0)
          hKη1
    · -- the screen base
      intro i
      match i with
      | 0 => exact le_trans (le_of_eq (show delta3E α Rv μ v0 0 0 = 0 from
          delta3_forced_screen_base Rv μ v0 (hRv v0) hhalf _)) zero_le
      | 1 => exact le_trans (le_of_eq (show delta3E α Rv μ v0 0 1 = 0 from
          delta3_forced_screen_base Rv μ v0 (hRv v0) hhalf _)) zero_le
      | 2 => exact le_trans (le_of_eq (show delta3E α Rv μ v0 0 2 = 0 from
          delta3_zZT_base Rv μ v0 (hRv v0) hhalf)) zero_le
      | 3 => exact le_trans (show delta3E α Rv μ v0 0 3 ≤ 2 * etaG α Rv μ
          from delta3_e2_base α Rv μ v0 (lt_of_lt_of_le one_pos hα) hsymm
            hhalf) hu0
      | 4 => exact le_trans (show delta3E α Rv μ v0 0 4 ≤ 2 * etaG α Rv μ
          from delta3_zTZ_base α Rv μ v0 hα0 hsymm hhalf) hu0
  intro h
  calc (∑' x, Tlaw μ (PMF.pure 3) v0 h x
        * qE (Tlaw μ (PMF.pure 3) v0 h) (fullSim (labRel Rv) h) x)
      ≤ PhiDres α (Tlaw μ (PMF.pure 3) v0 h) (Tlaw μ (PMF.pure 3) v0 h)
          (fullSim (labRel Rv) h) :=
        tsum_qE_le_PhiDres hα0 (Tlaw μ (PMF.pure 3) v0 h)
          (fullSim (labRel Rv) h)
          (fullSim_refl (labRel Rv) (fun s => hRv s.1) h)
    _ ≤ delta3Psi α Rv μ v0 h := by
        rw [delta3Psi]
        exact le_sup_right
    _ ≤ Kc * η := hΨ h

end GraphMarkovMatching
