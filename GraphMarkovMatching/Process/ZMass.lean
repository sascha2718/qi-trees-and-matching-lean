/-
The zero-mass rows of the transfer ledger
(`arbitrary_offspring_matching.tex`, `sec:rows`, zero-mass
outputs): the reversed zero-interface masses `zMass` feeding the
restricted four-law reduce, one level down, to root indicators plus
pair-level dead masses, and the pair-level dead mass Hall-factorizes
into unit-tilt screens.

* `deadMass_factorize`: the unit-tilt corollary of `deadScreen_factorize`:
  the mass of a dead product target under a product cell splits into two
  two-list screens plus two products of singleton screens, all with unit
  normalization;
* `zMass_Zlaw_succ`: the forced zero-mass row: at a root compatible with
  the forced label, the height-`(h+1)` dead mass toward `Z_j` is the
  height-`h` pair-level dead mass toward `Ξ_j` (`eq:decomp-forced` on the
  zero event); at an incompatible root it is one;
* `zMass_Tlaw_succ`: the fresh zero-mass row: the fresh degree factors as
  `r_μ(v) · r_{Ξ̄}` (`eq:decomp-fresh`), so the dead mass toward the fresh
  law is one at an uncharged root and the pair-level dead mass toward the
  mixture `Ξ̄` at a charged root;
* `zMass_eq_tsum`: the bridge between the ledger's `zMass` and its
  indicator tsum form.
-/
import GraphMarkovMatching.Process.Cells
import GraphMarkovMatching.Process.Ledger

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (ν : PMF ℕ)
  (v0 : V)

/-! ### The pair-level dead mass -/

section DeadMass

/- The Hall-factorization layer of `Process/Ledger.lean` lives at universe
zero; the dead-mass corollary is used at the process laws, which are
also at universe zero. -/
variable {X : Type}

/-- **Unit-tilt Hall factorization of the dead mass** (the zero-mass
corollary of `deadScreen_factorize`; the zero-row/zero-column table of
`thm:hall`): the mass of a dead product target under a product cell is
at most the two unit-tilt two-list screens plus the two products of
unit-tilt singleton screens. -/
lemma deadMass_factorize (ρa ρb ρc ρd : PMF X) (R : X → X → Prop) :
    ∑' xp : X × X, prodPMF ρa ρb xp
        * (if rE (prodPMF ρc ρd) (SquareRel R) xp = 0 then 1 else 0)
      ≤ screenE ρa R [ρc, ρd] (fun _ => 1)
          + screenE ρb R [ρc, ρd] (fun _ => 1)
        + screenE ρa R [ρc] (fun _ => 1) * screenE ρb R [ρc] (fun _ => 1)
        + screenE ρa R [ρd] (fun _ => 1) * screenE ρb R [ρd] (fun _ => 1) := by
  calc ∑' xp : X × X, prodPMF ρa ρb xp
        * (if rE (prodPMF ρc ρd) (SquareRel R) xp = 0 then 1 else 0)
      = ∑' xp : X × X, prodPMF ρa ρb xp
          * ((if rE (prodPMF ρc ρd) (SquareRel R) xp = 0 then 1 else 0)
            * ((1 : ℝ≥0∞) * 1)) :=
        tsum_congr fun xp => by rw [one_mul, mul_one]
    _ ≤ screenE ρa R [ρc, ρd] (fun _ => 1) * (∑' x, ρb x * 1)
          + (∑' x, ρa x * 1) * screenE ρb R [ρc, ρd] (fun _ => 1)
          + screenE ρa R [ρc] (fun _ => 1) * screenE ρb R [ρc] (fun _ => 1)
          + screenE ρa R [ρd] (fun _ => 1)
            * screenE ρb R [ρd] (fun _ => 1) :=
        deadScreen_factorize ρa ρb ρc ρd R (fun _ => 1) (fun _ => 1)
    _ = screenE ρa R [ρc, ρd] (fun _ => 1)
          + screenE ρb R [ρc, ρd] (fun _ => 1)
        + screenE ρa R [ρc] (fun _ => 1) * screenE ρb R [ρc] (fun _ => 1)
        + screenE ρa R [ρd] (fun _ => 1)
          * screenE ρb R [ρd] (fun _ => 1) := by
        rw [tsum_congr fun x => mul_one (ρb x), PMF.tsum_coe, mul_one,
          tsum_congr fun x => mul_one (ρa x), PMF.tsum_coe, one_mul]

end DeadMass

/-! ### The two zero-mass descent rows -/

/-- **Forced zero-mass row** (`sec:rows`, zero-mass outputs, forced
member): at a root compatible with the forced label, the height-`(h+1)`
dead mass toward `Z_j` descends to the height-`h` pair-level dead mass
of the square degree toward `Ξ_j` (`eq:decomp-forced` on the zero
event); at an incompatible root the target degree vanishes identically,
so the dead mass is one. -/
lemma zMass_Zlaw_succ (v : V) (k j h : ℕ) :
    ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * (if rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
            then 1 else 0)
      = if Rv v v0 then
          ∑' xp, Xi μ ν v0 k h xp
            * (if rE (Xi μ ν v0 j h) (SquareRel (fullSim (labRel Rv) h)) xp
                  = 0 then 1 else 0)
        else 1 := by
  have hmap : ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * (if rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
            then 1 else 0)
      = ∑' xp, Xi μ ν v0 k h xp
        * (if rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1))
              (branch (v, k) xp) = 0 then 1 else 0) := by
    rw [muM_varyK_succ μ ν v0 v k h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  by_cases hv : Rv v v0
  · rw [if_pos hv]
    refine tsum_congr fun xp => ?_
    have h1 := rE_Zlaw_succ_branch μ ν v0 Rv v k j h xp
    rw [if_pos hv] at h1
    rw [h1]
  · rw [if_neg hv]
    have hpt : ∀ xp, Xi μ ν v0 k h xp
        * (if rE (Zlaw μ ν v0 j (h + 1)) (fullSim (labRel Rv) (h + 1))
              (branch (v, k) xp) = 0 then 1 else 0)
        = Xi μ ν v0 k h xp := by
      intro xp
      have h1 := rE_Zlaw_succ_branch μ ν v0 Rv v k j h xp
      rw [if_neg hv] at h1
      rw [if_pos h1, mul_one]
    rw [tsum_congr hpt, PMF.tsum_coe]

/-- **Fresh zero-mass row** (`sec:rows`, zero-mass outputs, fresh
member): the fresh degree at a branch point factors as `r_μ(v) · r_{Ξ̄}`
(`eq:decomp-fresh`), so at an uncharged root the dead mass is one, and
at a charged root it is the height-`h` pair-level dead mass of the
square degree toward the mixture `Ξ̄`. -/
lemma zMass_Tlaw_succ (v : V) (k h : ℕ) :
    ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * (if rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
            then 1 else 0)
      = if rE μ Rv v = 0 then 1
        else ∑' xp, Xi μ ν v0 k h xp
          * (if rE (XiBar μ ν v0 h) (SquareRel (fullSim (labRel Rv) h)) xp
                = 0 then 1 else 0) := by
  have hmap : ∑' x, muM (varyK μ ν v0) (v, k) (h + 1) x
        * (if rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1)) x = 0
            then 1 else 0)
      = ∑' xp, Xi μ ν v0 k h xp
        * (if rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
              (branch (v, k) xp) = 0 then 1 else 0) := by
    rw [muM_varyK_succ μ ν v0 v k h]
    exact tsum_map_mul _ _ _
  rw [hmap]
  by_cases hv : rE μ Rv v = 0
  · rw [if_pos hv]
    have hpt : ∀ xp, Xi μ ν v0 k h xp
        * (if rE (Tlaw μ ν v0 (h + 1)) (fullSim (labRel Rv) (h + 1))
              (branch (v, k) xp) = 0 then 1 else 0)
        = Xi μ ν v0 k h xp := by
      intro xp
      have h1 := rE_Tlaw_succ_branch μ ν v0 Rv v k h xp
      rw [hv, zero_mul] at h1
      rw [if_pos h1, mul_one]
    rw [tsum_congr hpt, PMF.tsum_coe]
  · rw [if_neg hv]
    refine tsum_congr fun xp => ?_
    rw [rE_Tlaw_succ_branch μ ν v0 Rv v k h xp]
    by_cases hbar : rE (XiBar μ ν v0 h)
        (SquareRel (fullSim (labRel Rv) h)) xp = 0
    · rw [if_pos (mul_eq_zero_of_right (rE μ Rv v) hbar), if_pos hbar]
    · rw [if_neg (mul_ne_zero hv hbar), if_neg hbar]

/-! ### The bridge to the ledger's `zMass` -/

section ZMassBridge

variable {X : Type}

/-- The ledger's zero-interface mass in indicator form: `zMass` is by
definition the indicator-tilted mass of the reversed zero interface
(`eq:screen-mass`, mass side).  Downstream files rewrite between the two
forms with this lemma. -/
lemma zMass_eq_tsum (ρs ρt : PMF X) (R : X → X → Prop) :
    zMass ρs ρt R = ∑' y, ρs y * (if rE ρt R y = 0 then 1 else 0) := rfl

end ZMassBridge

end GraphMarkovMatching
