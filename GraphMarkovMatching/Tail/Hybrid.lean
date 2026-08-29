/-
Hybrid annealed/quenched screen lemmas for the unbounded-support attempt.

Quenched component targets remove inverse degrees of countable mixtures from
the ordinary rows, while the annealed mixture is still needed as the common
diagonal target.  The lemmas here provide the elementary conversions:

* a component charged by a mixture has a zero screen against that mixture
  under a reflexive relation;
* after retaining and summing the component weight, a component-dead screen
  with the aggregate inverse tilt is bounded by the aggregate restricted
  potential;
* after independently sampling a component inverse tilt, reverse pruning
  removes the annealed zero interface and comparison of the two positive
  good degrees bounds the regular remainder by two ordinary restricted
  potentials.  A mixed coordinate and its product row are also recorded,
  but are not needed for this sharper closed conversion.
-/
import GraphMarkovMatching.Tail.QuenchedRows
import GraphMarkovMatching.Tail.Mixture
import GraphMarkovMatching.Tail.Combinatorics
import GraphMarkovMatching.Grammar.Interp
import GraphMarkovMatching.Process.Coordinates

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {A X : Type}

/-- A zero good degree forces bad degree one, so the dead indicator is
pointwise below the bad degree. -/
lemma deadInd_le_qE (ρ : PMF X) (R : X → X → Prop) (x : X) :
    (if rE ρ R x = 0 then (1 : ℝ≥0∞) else 0) ≤ qE ρ R x := by
  by_cases hr : rE ρ R x = 0
  · rw [if_pos hr]
    have hsum := rE_add_qE ρ R x
    rw [hr, zero_add] at hsum
    exact hsum.ge
  · rw [if_neg hr]
    exact zero_le

/-- The mixture-weighted average of singleton component-dead screens is at
most the corresponding bad-degree integral toward the aggregate mixture. -/
lemma avg_component_screen_le_failureD (ρs : PMF X) (w : PMF A)
    (f : A → PMF X) (R : X → X → Prop) :
    ∑' a, w a * screenE ρs R [f a] (fun _ => 1)
      ≤ failureD ρs (w.bind f) R := by
  rw [failureD]
  calc
    (∑' a, w a * screenE ρs R [f a] (fun _ => 1))
        ≤ ∑' a, w a * ∑' x, ρs x * qE (f a) R x := by
            refine ENNReal.tsum_le_tsum fun a => mul_le_mul_right ?_ _
            rw [screenE_singleton]
            refine ENNReal.tsum_le_tsum fun x => ?_
            simpa only [mul_one, one_mul, mul_assoc, mul_comm] using
              (mul_le_mul_left (deadInd_le_qE (f a) R x) (ρs x))
    _ = ∑' x, ρs x * ∑' a, w a * qE (f a) R x := by
          calc
            (∑' a, w a * ∑' x, ρs x * qE (f a) R x)
                = ∑' a, ∑' x, w a * (ρs x * qE (f a) R x) := by
                    refine tsum_congr fun a => ?_
                    rw [ENNReal.tsum_mul_left]
            _ = ∑' x, ∑' a, w a * (ρs x * qE (f a) R x) :=
                  ENNReal.tsum_comm
            _ = ∑' x, ρs x * ∑' a, w a * qE (f a) R x := by
                  refine tsum_congr fun x => ?_
                  calc
                    (∑' a, w a * (ρs x * qE (f a) R x))
                        = ∑' a, ρs x * (w a * qE (f a) R x) := by
                            exact tsum_congr fun a => by ring
                    _ = ρs x * ∑' a, w a * qE (f a) R x :=
                          ENNReal.tsum_mul_left
    _ = ∑' x, ρs x * qE (w.bind f) R x := by
          refine tsum_congr fun x => ?_
          rw [qE_bind]

/-- With the restricted inverse degree of the aggregate mixture as tilt,
the weighted component-dead screens are absorbed by the aggregate ordinary
potential.  No inverse atom `w(a)⁻¹` occurs. -/
lemma avg_component_screen_WresD_le_PhiDres (α : ℝ) (hα : 0 < α)
    (ρs : PMF X) (w : PMF A) (f : A → PMF X) (R : X → X → Prop) :
    ∑' a, w a * screenE ρs R [f a] (WresD α (w.bind f) R)
      ≤ PhiDres α ρs (w.bind f) R := by
  rw [PhiDres_bind_eq_tsum_bad_tilt α hα]
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul_right ?_ _
  rw [screenE_singleton]
  refine ENNReal.tsum_le_tsum fun x => ?_
  exact mul_le_mul_right
    (mul_le_mul_left (deadInd_le_qE (f a) R x) _) _

/-- The regular (nonzero aggregate degree) part of a bad-degree integral
with an arbitrary nonnegative tilt. -/
noncomputable def regularBadTilt (ρs ρt : PMF X) (R : X → X → Prop)
    (g : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, ρs x * ((if rE ρt R x = 0 then 0 else qE ρt R x) * g x)

/-- A mixed ordinary coordinate: the bad degree is measured toward `ρbad`
and the restricted inverse normalization toward `ρnorm`.  The diagonal
case is the usual restricted potential. -/
noncomputable def crossDres (α : ℝ) (ρs ρbad ρnorm : PMF X)
    (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, ρs x * (qE ρbad R x * WresD α ρnorm R x)

lemma crossDres_self (α : ℝ) (hα : 0 < α) (ρs ρt : PMF X)
    (R : X → X → Prop) :
    crossDres α ρs ρt ρt R = PhiDres α ρs ρt R := by
  rw [crossDres, PhiDres]
  refine tsum_congr fun x => ?_
  by_cases hr : rE ρt R x = 0
  · simp [WresD, hr]
  · rw [if_neg hr, phiE_eq_qE_mul_rpow α R ρt hα x,
      rE_rpow_neg_eq_WresD ρt R x hr]

/-- Bad-target mixtures are linear in the bad slot of `crossDres`. -/
lemma crossDres_bind_bad (α : ℝ) (ρs : PMF X) (w : PMF A)
    (f : A → PMF X) (ρnorm : PMF X) (R : X → X → Prop) :
    crossDres α ρs (w.bind f) ρnorm R
      = ∑' a, w a * crossDres α ρs (f a) ρnorm R := by
  rw [crossDres]
  calc
    (∑' x, ρs x * (qE (w.bind f) R x * WresD α ρnorm R x))
        = ∑' x, ρs x *
            ((∑' a, w a * qE (f a) R x) * WresD α ρnorm R x) := by
              refine tsum_congr fun x => ?_
              rw [qE_bind]
    _ = ∑' a, w a * crossDres α ρs (f a) ρnorm R := by
          calc
            (∑' x, ρs x *
                ((∑' a, w a * qE (f a) R x) * WresD α ρnorm R x))
                = ∑' x, ∑' a, w a *
                    (ρs x * (qE (f a) R x * WresD α ρnorm R x)) := by
                      refine tsum_congr fun x => ?_
                      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
                      exact tsum_congr fun a => by ring
            _ = ∑' a, ∑' x, w a *
                (ρs x * (qE (f a) R x * WresD α ρnorm R x)) :=
                  ENNReal.tsum_comm
            _ = ∑' a, w a * crossDres α ρs (f a) ρnorm R := by
                  refine tsum_congr fun a => ?_
                  rw [crossDres, ENNReal.tsum_mul_left]

/-- The source slot of `crossDres` is linear under mixtures as well. -/
lemma crossDres_bind_source (α : ℝ) (w : PMF A) (f : A → PMF X)
    (ρbad ρnorm : PMF X) (R : X → X → Prop) :
    crossDres α (w.bind f) ρbad ρnorm R
      = ∑' a, w a * crossDres α (f a) ρbad ρnorm R := by
  rw [crossDres, tsum_bind_mul]
  refine tsum_congr fun a => ?_
  rw [crossDres]

/-- A fixed straight matching gives a union bound for the bad degree of a
product target.  This deliberately discards the crossed matching; the
resulting loss is additive and therefore separates against product source
laws. -/
lemma qE_square_le_straight_sum (ρc ρd : PMF X) (R : X → X → Prop)
    (x₀ x₁ : X) :
    qE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁)
      ≤ qE ρc R x₀ + qE ρd R x₁ := by
  rw [← ENNReal.toReal_le_toReal qE_ne_top
    (ENNReal.add_ne_top.mpr ⟨qE_ne_top, qE_ne_top⟩), ENNReal.toReal_add
      qE_ne_top qE_ne_top]
  have hstraight := ENNReal.toReal_mono rE_ne_top
    (straight_le_rE_square ρc ρd R x₀ x₁)
  rw [ENNReal.toReal_mul] at hstraight
  have hc := toReal_rE_add_toReal_qE ρc R x₀
  have hd := toReal_rE_add_toReal_qE ρd R x₁
  have hs := toReal_rE_add_toReal_qE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁)
  have hrc0 : (0 : ℝ) ≤ (rE ρc R x₀).toReal := ENNReal.toReal_nonneg
  have hrc1 : (rE ρc R x₀).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top rE_le_one
  have hqd : (0 : ℝ) ≤ (qE ρd R x₁).toReal := ENNReal.toReal_nonneg
  nlinarith

/-- The bad degree of a fixed-root tree law is the child bad degree when
the roots are compatible, and is one otherwise. -/
lemma qE_map_branch_law {S : Type} (ρ : PMF (FullLab S h × FullLab S h))
    (R₀ : S → S → Prop) (s t : S) (xp : FullLab S h × FullLab S h) :
    qE (ρ.map (branch t)) (fullSim R₀ (h + 1)) (branch s xp)
      = if R₀ s t then qE ρ (SquareRel (fullSim R₀ h)) xp else 1 := by
  by_cases hst : R₀ s t
  · rw [if_pos hst]
    apply (ENNReal.toReal_eq_toReal_iff' qE_ne_top qE_ne_top).mp
    have hs := toReal_rE_add_toReal_qE
      (ρ.map (branch t)) (fullSim R₀ (h + 1)) (branch s xp)
    have hc := toReal_rE_add_toReal_qE ρ (SquareRel (fullSim R₀ h)) xp
    have hr := rE_map_branch_law ρ R₀ s t xp
    rw [if_pos hst] at hr
    rw [hr] at hs
    linarith
  · rw [if_neg hst]
    have hr := rE_map_branch_law ρ R₀ s t xp
    rw [if_neg hst] at hr
    have hs := rE_add_qE
      (ρ.map (branch t)) (fullSim R₀ (h + 1)) (branch s xp)
    rw [hr, zero_add] at hs
    exact hs

/-- Restricted inverse normalization also passes exactly through a
compatible fixed root and vanishes at an incompatible one. -/
lemma WresD_map_branch_law {S : Type} (α : ℝ)
    (ρ : PMF (FullLab S h × FullLab S h)) (R₀ : S → S → Prop)
    (s t : S) (xp : FullLab S h × FullLab S h) :
    WresD α (ρ.map (branch t)) (fullSim R₀ (h + 1)) (branch s xp)
      = if R₀ s t then WresD α ρ (SquareRel (fullSim R₀ h)) xp else 0 := by
  rw [WresD, WresD, WnnD, WnnD, q, q]
  have hr := rE_map_branch_law ρ R₀ s t xp
  have hq := qE_map_branch_law ρ R₀ s t xp
  by_cases hst : R₀ s t
  · rw [if_pos hst] at hr hq
    rw [if_pos hst]
    rw [hr, hq]
  · rw [if_neg hst] at hr hq
    rw [if_neg hst]
    rw [hr]
    simp

/-- Exact root transfer for three fixed-root component laws.  If the
normalizing root is incompatible the mixed coordinate vanishes; if only
the bad root is incompatible it reduces to an ordinary inverse moment. -/
lemma crossDres_map_branch_law {S : Type} (α : ℝ)
    (ρs ρbad ρnorm : PMF (FullLab S h × FullLab S h))
    (R₀ : S → S → Prop) (s tb tn : S) :
    crossDres α (ρs.map (branch s)) (ρbad.map (branch tb))
        (ρnorm.map (branch tn)) (fullSim R₀ (h + 1))
      = if R₀ s tn then
          if R₀ s tb then
            crossDres α ρs ρbad ρnorm (SquareRel (fullSim R₀ h))
          else ∑' xp, ρs xp * WresD α ρnorm (SquareRel (fullSim R₀ h)) xp
        else 0 := by
  rw [crossDres, tsum_map_mul]
  by_cases hn : R₀ s tn
  · rw [if_pos hn]
    by_cases hb : R₀ s tb
    · rw [if_pos hb, crossDres]
      refine tsum_congr fun xp => ?_
      rw [qE_map_branch_law, WresD_map_branch_law, if_pos hb, if_pos hn]
    · rw [if_neg hb]
      refine tsum_congr fun xp => ?_
      rw [qE_map_branch_law, WresD_map_branch_law, if_neg hb, if_pos hn,
        one_mul]
  · rw [if_neg hn]
    refine ENNReal.tsum_eq_zero.mpr fun xp => ?_
    rw [WresD_map_branch_law, if_neg hn, mul_zero, mul_zero]

/-- The sharp product row for a mixed coordinate, before estimating the
four ordinary inverse moments.  Each term remembers which target supplies
the bad degree and which target supplies the normalization. -/
lemma crossDres_square_le_four_moments (α : ℝ) (hα0 : 0 ≤ α)
    (ρa ρb ρc ρd ρe ρf : PMF X) (R : X → X → Prop) :
    crossDres α (prodPMF ρa ρb) (prodPMF ρc ρd) (prodPMF ρe ρf)
        (SquareRel R)
      ≤ crossDres α ρa ρc ρe R * (∑' x, ρb x * WresD α ρf R x)
        + crossDres α ρa ρc ρf R * (∑' x, ρb x * WresD α ρe R x)
        + (∑' x, ρa x * WresD α ρe R x) * crossDres α ρb ρd ρf R
        + (∑' x, ρa x * WresD α ρf R x) * crossDres α ρb ρd ρe R := by
  rw [crossDres]
  have hpoint : ∀ p : X × X,
      prodPMF ρa ρb p
          * (qE (prodPMF ρc ρd) (SquareRel R) p
            * WresD α (prodPMF ρe ρf) (SquareRel R) p)
        ≤ (ρa p.1 * (qE ρc R p.1 * WresD α ρe R p.1))
              * (ρb p.2 * WresD α ρf R p.2)
          + (ρa p.1 * (qE ρc R p.1 * WresD α ρf R p.1))
              * (ρb p.2 * WresD α ρe R p.2)
          + (ρa p.1 * WresD α ρe R p.1)
              * (ρb p.2 * (qE ρd R p.2 * WresD α ρf R p.2))
          + (ρa p.1 * WresD α ρf R p.1)
              * (ρb p.2 * (qE ρd R p.2 * WresD α ρe R p.2)) := by
    intro p
    have hq := qE_square_le_straight_sum ρc ρd R p.1 p.2
    have hW := WresD_square_le_sum hα0 ρe ρf R p
    rw [prodPMF_apply]
    calc
      ρa p.1 * ρb p.2
            * (qE (prodPMF ρc ρd) (SquareRel R) p
              * WresD α (prodPMF ρe ρf) (SquareRel R) p)
          ≤ ρa p.1 * ρb p.2
              * ((qE ρc R p.1 + qE ρd R p.2)
                * (WresD α ρe R p.1 * WresD α ρf R p.2
                  + WresD α ρf R p.1 * WresD α ρe R p.2)) :=
            mul_le_mul_right (mul_le_mul' hq hW) _
      _ = _ := by ring
  calc
    (∑' p, prodPMF ρa ρb p
        * (qE (prodPMF ρc ρd) (SquareRel R) p
          * WresD α (prodPMF ρe ρf) (SquareRel R) p))
      ≤ ∑' p, (
          (ρa p.1 * (qE ρc R p.1 * WresD α ρe R p.1))
              * (ρb p.2 * WresD α ρf R p.2)
          + (ρa p.1 * (qE ρc R p.1 * WresD α ρf R p.1))
              * (ρb p.2 * WresD α ρe R p.2)
          + (ρa p.1 * WresD α ρe R p.1)
              * (ρb p.2 * (qE ρd R p.2 * WresD α ρf R p.2))
          + (ρa p.1 * WresD α ρf R p.1)
              * (ρb p.2 * (qE ρd R p.2 * WresD α ρe R p.2))) :=
        ENNReal.tsum_le_tsum hpoint
    _ = (∑' p : X × X,
            (ρa p.1 * (qE ρc R p.1 * WresD α ρe R p.1))
              * (ρb p.2 * WresD α ρf R p.2))
        + (∑' p : X × X,
            (ρa p.1 * (qE ρc R p.1 * WresD α ρf R p.1))
              * (ρb p.2 * WresD α ρe R p.2))
        + (∑' p : X × X,
            (ρa p.1 * WresD α ρe R p.1)
              * (ρb p.2 * (qE ρd R p.2 * WresD α ρf R p.2)))
        + (∑' p : X × X,
            (ρa p.1 * WresD α ρf R p.1)
              * (ρb p.2 * (qE ρd R p.2 * WresD α ρe R p.2))) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    _ = _ := by
      rw [crossDres,
        tsum_prod_split
          (fun x => ρa x * (qE ρc R x * WresD α ρe R x))
          (fun x => ρb x * WresD α ρf R x),
        tsum_prod_split
          (fun x => ρa x * (qE ρc R x * WresD α ρf R x))
          (fun x => ρb x * WresD α ρe R x),
        tsum_prod_split
          (fun x => ρa x * WresD α ρe R x)
          (fun x => ρb x * (qE ρd R x * WresD α ρf R x)),
        tsum_prod_split
          (fun x => ρa x * WresD α ρf R x)
          (fun x => ρb x * (qE ρd R x * WresD α ρe R x))]
      simp only [crossDres]

/-- Closed form of the mixed product row.  The coefficient of each mixed
child coordinate is an ordinary restricted inverse moment, hence is
controlled by `1 + α Φres`; no directed failure term is introduced. -/
lemma crossDres_square_le (α : ℝ) (hα : 1 ≤ α)
    (ρa ρb ρc ρd ρe ρf : PMF X) (R : X → X → Prop) :
    crossDres α (prodPMF ρa ρb) (prodPMF ρc ρd) (prodPMF ρe ρf)
        (SquareRel R)
      ≤ crossDres α ρa ρc ρe R
            * (1 + ENNReal.ofReal α * PhiDres α ρb ρf R)
        + crossDres α ρa ρc ρf R
            * (1 + ENNReal.ofReal α * PhiDres α ρb ρe R)
        + (1 + ENNReal.ofReal α * PhiDres α ρa ρe R)
            * crossDres α ρb ρd ρf R
        + (1 + ENNReal.ofReal α * PhiDres α ρa ρf R)
            * crossDres α ρb ρd ρe R := by
  refine le_trans (crossDres_square_le_four_moments α
    (le_trans zero_le_one hα) ρa ρb ρc ρd ρe ρf R) ?_
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul' le_rfl (tsum_WresD_le hα ρb ρf R))
    (mul_le_mul' le_rfl (tsum_WresD_le hα ρb ρe R)))
    (mul_le_mul' (tsum_WresD_le hα ρa ρe R) le_rfl))
    (mul_le_mul' (tsum_WresD_le hα ρa ρf R) le_rfl)

/-- The sharp mixed row specialized to the three independently quenched
child targets.  This is the concrete product/child transfer that was
missing from the first hybrid audit. -/
lemma crossDres_qChildren_le {V : Type} (α : ℝ) (hα : 1 ≤ α)
    (μ : PMF V) (v0 : V) {h : ℕ} (ts tb tn : QTgt (h + 1))
    (R : FullLab (V × ℕ) h → FullLab (V × ℕ) h → Prop) :
    crossDres α (qChildren μ v0 ts) (qChildren μ v0 tb)
        (qChildren μ v0 tn) (SquareRel R)
      ≤ crossDres α (qInterp μ v0 (qchild0 ts))
            (qInterp μ v0 (qchild0 tb)) (qInterp μ v0 (qchild0 tn)) R
          * (1 + ENNReal.ofReal α * PhiDres α
              (qInterp μ v0 (qchild1 ts)) (qInterp μ v0 (qchild1 tn)) R)
        + crossDres α (qInterp μ v0 (qchild0 ts))
            (qInterp μ v0 (qchild0 tb)) (qInterp μ v0 (qchild1 tn)) R
          * (1 + ENNReal.ofReal α * PhiDres α
              (qInterp μ v0 (qchild1 ts)) (qInterp μ v0 (qchild0 tn)) R)
        + (1 + ENNReal.ofReal α * PhiDres α
              (qInterp μ v0 (qchild0 ts)) (qInterp μ v0 (qchild0 tn)) R)
          * crossDres α (qInterp μ v0 (qchild1 ts))
              (qInterp μ v0 (qchild1 tb)) (qInterp μ v0 (qchild1 tn)) R
        + (1 + ENNReal.ofReal α * PhiDres α
              (qInterp μ v0 (qchild0 ts)) (qInterp μ v0 (qchild1 tn)) R)
          * crossDres α (qInterp μ v0 (qchild1 ts))
              (qInterp μ v0 (qchild1 tb)) (qInterp μ v0 (qchild0 tn)) R := by
  simpa only [qChildren] using crossDres_square_le α hα
    (qInterp μ v0 (qchild0 ts)) (qInterp μ v0 (qchild1 ts))
    (qInterp μ v0 (qchild0 tb)) (qInterp μ v0 (qchild1 tb))
    (qInterp μ v0 (qchild0 tn)) (qInterp μ v0 (qchild1 tn)) R

/-- A generic fallback bound for a mixed coordinate.  It is finite whenever
the corresponding directed failure and normalization potential are finite;
the sharper transfer keeps `crossDres` instead of using this estimate
linearly. -/
lemma crossDres_le_failureD_add_PhiDres (α : ℝ) (hα : 1 ≤ α)
    (ρs ρbad ρnorm : PMF X) (R : X → X → Prop) :
    crossDres α ρs ρbad ρnorm R
      ≤ failureD ρs ρbad R
        + ENNReal.ofReal α * PhiDres α ρs ρnorm R := by
  rw [crossDres, failureD, PhiDres]
  calc
    (∑' x, ρs x * (qE ρbad R x * WresD α ρnorm R x))
        ≤ ∑' x, (ρs x * qE ρbad R x
          + ENNReal.ofReal α * (ρs x * (if rE ρnorm R x = 0 then 0
              else phiE α (q ρnorm R x)))) := by
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hr : rE ρnorm R x = 0
      · simp [WresD, hr]
      · have hW : WresD α ρnorm R x
        ≤ 1 + ENNReal.ofReal α * phiE α (q ρnorm R x) := by
          rw [WresD, if_neg hr]
          exact WnnD_le hα ρnorm R x
        have hqphi : qE ρbad R x * phiE α (q ρnorm R x)
            ≤ phiE α (q ρnorm R x) := by
          calc
            qE ρbad R x * phiE α (q ρnorm R x)
                ≤ 1 * phiE α (q ρnorm R x) :=
                  by simpa [mul_comm] using
                    (mul_le_mul_right qE_le_one (phiE α (q ρnorm R x)))
            _ = phiE α (q ρnorm R x) := one_mul _
        calc
          ρs x * (qE ρbad R x * WresD α ρnorm R x)
              ≤ ρs x * (qE ρbad R x
                  * (1 + ENNReal.ofReal α * phiE α (q ρnorm R x))) :=
                mul_le_mul_right (mul_le_mul_right hW _) _
          _ = ρs x * qE ρbad R x
              + ENNReal.ofReal α
                * (ρs x * (qE ρbad R x * phiE α (q ρnorm R x))) := by ring
          _ ≤ ρs x * qE ρbad R x
              + ENNReal.ofReal α
                * (ρs x * phiE α (q ρnorm R x)) := by
                  exact add_le_add le_rfl
                    (mul_le_mul_right
                      (mul_le_mul_right hqphi (ρs x)) (ENNReal.ofReal α))
          _ = ρs x * qE ρbad R x
              + ENNReal.ofReal α
                * (ρs x * (if rE ρnorm R x = 0 then 0
                    else phiE α (q ρnorm R x))) := by rw [if_neg hr]
    _ = (∑' x, ρs x * qE ρbad R x)
        + ENNReal.ofReal α * ∑' x, ρs x *
            (if rE ρnorm R x = 0 then 0 else phiE α (q ρnorm R x)) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]

/-- Weighted component-dead screens are bounded by the aggregate bad
degree with the same arbitrary tilt. -/
lemma avg_component_screen_le_bad_tilt (ρs : PMF X) (w : PMF A)
    (f : A → PMF X) (R : X → X → Prop) (g : X → ℝ≥0∞) :
    ∑' a, w a * screenE ρs R [f a] g
      ≤ ∑' x, ρs x * (qE (w.bind f) R x * g x) := by
  calc
    (∑' a, w a * screenE ρs R [f a] g)
        ≤ ∑' a, w a * ∑' x, ρs x * (qE (f a) R x * g x) := by
            refine ENNReal.tsum_le_tsum fun a => mul_le_mul_right ?_ _
            rw [screenE_singleton]
            refine ENNReal.tsum_le_tsum fun x => ?_
            exact mul_le_mul_right
              (mul_le_mul_left (deadInd_le_qE (f a) R x) _) _
    _ = ∑' x, ρs x * (qE (w.bind f) R x * g x) := by
          calc
            (∑' a, w a * ∑' x, ρs x * (qE (f a) R x * g x))
                = ∑' a, ∑' x, w a * (ρs x * (qE (f a) R x * g x)) := by
                    refine tsum_congr fun a => ?_
                    rw [ENNReal.tsum_mul_left]
            _ = ∑' x, ∑' a, w a * (ρs x * (qE (f a) R x * g x)) :=
                  ENNReal.tsum_comm
            _ = ∑' x, ρs x * ((∑' a, w a * qE (f a) R x) * g x) := by
                  refine tsum_congr fun x => ?_
                  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
                  exact tsum_congr fun a => by ring
            _ = ∑' x, ρs x * (qE (w.bind f) R x * g x) := by
                  refine tsum_congr fun x => ?_
                  rw [qE_bind]

/-- The aggregate bad-degree tilt splits exactly into its annealed zero
interface and its regular part. -/
lemma bad_tilt_eq_screen_add_regular (ρs ρt : PMF X)
    (R : X → X → Prop) (g : X → ℝ≥0∞) :
    (∑' x, ρs x * (qE ρt R x * g x))
      = screenE ρs R [ρt] g + regularBadTilt ρs ρt R g := by
  rw [screenE_singleton, regularBadTilt, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  by_cases hr : rE ρt R x = 0
  · have hsum := rE_add_qE ρt R x
    rw [hr, zero_add] at hsum
    rw [if_pos hr, if_pos hr, hsum]
    ring
  · rw [if_neg hr, if_neg hr]
    ring

/-- On the positive part of the bad target, a mixed inverse tilt is paid
by one of the two ordinary potentials.  Compare the two good degrees: if
the normalizing degree is larger, its inverse power is smaller; if it is
smaller, the bad degree of the bad target is smaller. -/
lemma regularBadTilt_WresD_le_PhiDres_add (α : ℝ) (hα : 0 < α)
    (ρs ρbad ρnorm : PMF X) (R : X → X → Prop) :
    regularBadTilt ρs ρbad R (WresD α ρnorm R)
      ≤ PhiDres α ρs ρbad R + PhiDres α ρs ρnorm R := by
  rw [regularBadTilt, PhiDres, PhiDres, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hb : rE ρbad R x = 0
  · simp [hb]
  · by_cases hn : rE ρnorm R x = 0
    · simp [hb, WresD, hn]
    · simp only [hb, hn, if_false]
      have hpb := phiE_eq_qE_mul_rpow α R ρbad hα x
      have hpn := phiE_eq_qE_mul_rpow α R ρnorm hα x
      rw [← rE_rpow_neg_eq_WresD ρnorm R x hn]
      rcases le_total (rE ρbad R x) (rE ρnorm R x) with hdeg | hdeg
      · have hpow : (rE ρnorm R x) ^ (-α) ≤ (rE ρbad R x) ^ (-α) :=
          rpow_neg_antitone hα.le hdeg
        calc
          ρs x * (qE ρbad R x * (rE ρnorm R x) ^ (-α))
              ≤ ρs x * (qE ρbad R x * (rE ρbad R x) ^ (-α)) :=
                mul_le_mul_right (mul_le_mul_right hpow _) _
          _ = ρs x * phiE α (q ρbad R x) := by rw [hpb]
          _ ≤ ρs x * phiE α (q ρbad R x)
                + ρs x * phiE α (q ρnorm R x) := le_self_add
      · have hq : qE ρbad R x ≤ qE ρnorm R x := by
          rw [← ENNReal.toReal_le_toReal qE_ne_top qE_ne_top]
          have hbq := toReal_rE_add_toReal_qE ρbad R x
          have hnq := toReal_rE_add_toReal_qE ρnorm R x
          have hreal := ENNReal.toReal_mono rE_ne_top hdeg
          linarith
        calc
          ρs x * (qE ρbad R x * (rE ρnorm R x) ^ (-α))
              ≤ ρs x * (qE ρnorm R x * (rE ρnorm R x) ^ (-α)) :=
                mul_le_mul' le_rfl (mul_le_mul' hq le_rfl)
          _ = ρs x * phiE α (q ρnorm R x) := by rw [hpn]
          _ ≤ ρs x * phiE α (q ρbad R x)
                + ρs x * phiE α (q ρnorm R x) := le_add_self

/-- Averaging the regular hybrid remainder introduces only the annealed
ordinary potential and the averaged component ordinary potential. -/
lemma avg_regular_component_WresD_le_PhiDres (α : ℝ) (hα : 0 < α)
    (ρs : PMF X) (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) :
    ∑' b, w b * regularBadTilt ρs (w.bind f) R (WresD α (f b) R)
      ≤ PhiDres α ρs (w.bind f) R
        + ∑' b, w b * PhiDres α ρs (f b) R := by
  calc
    (∑' b, w b * regularBadTilt ρs (w.bind f) R (WresD α (f b) R))
      ≤ ∑' b, w b *
          (PhiDres α ρs (w.bind f) R + PhiDres α ρs (f b) R) := by
            refine ENNReal.tsum_le_tsum fun b => mul_le_mul_right ?_ _
            exact regularBadTilt_WresD_le_PhiDres_add α hα ρs (w.bind f) (f b) R
    _ = PhiDres α ρs (w.bind f) R
        + ∑' b, w b * PhiDres α ρs (f b) R := by
          calc
            (∑' b, w b *
                (PhiDres α ρs (w.bind f) R + PhiDres α ρs (f b) R))
              = ∑' b, (w b * PhiDres α ρs (w.bind f) R
                  + w b * PhiDres α ρs (f b) R) := by
                    refine tsum_congr fun b => by ring
            _ = (∑' b, w b * PhiDres α ρs (w.bind f) R)
                  + ∑' b, w b * PhiDres α ρs (f b) R :=
                    ENNReal.tsum_add
            _ = PhiDres α ρs (w.bind f) R
                  + ∑' b, w b * PhiDres α ρs (f b) R := by
                    rw [ENNReal.tsum_mul_right, w.tsum_coe, one_mul]

/-- Reverse tilt pruning.  If the zero list contains a mixture and the
normalization is a charged component of that mixture, then the screen
vanishes. -/
theorem screenE_mix_mem_component_WresD_eq_zero (α : ℝ)
    (ρs : PMF X) (w : PMF A) (f : A → PMF X) (R : X → X → Prop)
    (a : A) (ha : w a ≠ 0) (zs : List (PMF X))
    (hmix : w.bind f ∈ zs) :
    screenE ρs R zs (WresD α (f a) R) = 0 := by
  rw [screenE]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hcomp : rE (f a) R x = 0
  · rw [WresD, if_pos hcomp, mul_zero]
  · have hmixdeg : rE (w.bind f) R x ≠ 0 := by
      rw [rE_bind]
      have hterm : w a * rE (f a) R x ≠ 0 := mul_ne_zero ha hcomp
      exact fun hzero => hterm
        (le_antisymm (hzero ▸ ENNReal.le_tsum a) zero_le)
    have hind : screenInd R zs x = 0 := by
      rw [screenInd, if_neg]
      exact fun hall => hmixdeg (hall _ hmix)
    rw [hind, mul_zero, zero_mul]

/-- **Hybrid component-screen conversion.**  Average both the dead
component and an independently sampled inverse-normalization component of
the same mixture.  The annealed zero-interface term vanishes by reverse
tilt pruning, leaving only the regular mixed ordinary moment. -/
lemma avg_component_screen_component_WresD_le_regular (α : ℝ)
    (ρs : PMF X) (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) :
    ∑' b, w b * ∑' a, w a *
        screenE ρs R [f a] (WresD α (f b) R)
      ≤ ∑' b, w b * regularBadTilt ρs (w.bind f) R
          (WresD α (f b) R) := by
  refine ENNReal.tsum_le_tsum fun b => ?_
  by_cases hb : w b = 0
  · simp [hb]
  · refine mul_le_mul_right ?_ _
    calc
        (∑' a, w a * screenE ρs R [f a] (WresD α (f b) R))
            ≤ ∑' x, ρs x *
                (qE (w.bind f) R x * WresD α (f b) R x) :=
              avg_component_screen_le_bad_tilt ρs w f R _
        _ = screenE ρs R [w.bind f] (WresD α (f b) R)
              + regularBadTilt ρs (w.bind f) R (WresD α (f b) R) :=
            bad_tilt_eq_screen_add_regular ρs (w.bind f) R _
        _ = regularBadTilt ρs (w.bind f) R (WresD α (f b) R) := by
            rw [screenE_mix_mem_component_WresD_eq_zero α ρs w f R b hb
              [w.bind f] (List.mem_singleton_self _), zero_add]

/-- **Closed hybrid conversion.**  The averaged component screen is paid
entirely by ordinary restricted potentials: one toward the annealed
mixture and one averaged over the normalizing components.  Thus no mixed
coordinate needs to be propagated through the child product. -/
lemma avg_component_screen_component_WresD_le_PhiDres_pair
    (α : ℝ) (hα : 0 < α) (ρs : PMF X) (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) :
    ∑' b, w b * ∑' a, w a *
        screenE ρs R [f a] (WresD α (f b) R)
      ≤ PhiDres α ρs (w.bind f) R
        + ∑' b, w b * PhiDres α ρs (f b) R := by
  exact le_trans
    (avg_component_screen_component_WresD_le_regular α ρs w f R)
    (avg_regular_component_WresD_le_PhiDres α hα ρs w f R)

/-- The same hybrid conversion in the closed mixed-coordinate form.  No
screen survives: the output is the environment-weighted family of
`crossDres` coordinates. -/
lemma avg_component_screen_component_WresD_le_crossDres (α : ℝ)
    (ρs : PMF X) (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) :
    ∑' b, w b * ∑' a, w a *
        screenE ρs R [f a] (WresD α (f b) R)
      ≤ ∑' b, w b * ∑' a, w a * crossDres α ρs (f a) (f b) R := by
  refine ENNReal.tsum_le_tsum fun b => mul_le_mul_right ?_ _
  calc
    (∑' a, w a * screenE ρs R [f a] (WresD α (f b) R))
        ≤ crossDres α ρs (w.bind f) (f b) R :=
          avg_component_screen_le_bad_tilt ρs w f R _
    _ = ∑' a, w a * crossDres α ρs (f a) (f b) R :=
      crossDres_bind_bad α ρs w f (f b) R

/-- A charged component has no zero interface toward its own annealed
mixture: the mixture contains a positive multiple of the component and
reflexivity supplies the diagonal compatible atom. -/
theorem screenE_component_to_mix_eq_zero (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) (hrefl : ∀ x, R x x) (a : A) (ha : w a ≠ 0)
    (g : X → ℝ≥0∞) :
    screenE (f a) R [w.bind f] g = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : f a x = 0
  · simp [hx]
  · have hmix : (w.bind f) x ≠ 0 := by
      have hterm : w a * f a x ≠ 0 := mul_ne_zero ha hx
      rw [PMF.bind_apply]
      exact fun hzero => hterm (le_antisymm (hzero ▸ ENNReal.le_tsum a) zero_le)
    have hr : rE (w.bind f) R x ≠ 0 := fun hzero =>
      hmix (le_antisymm (hzero ▸ le_rE_of_refl (hrefl x)) zero_le)
    have hind : screenInd R [w.bind f] x = 0 := by
      rw [screenInd, if_neg]
      simpa using hr
    simp [hind]

/-- The same component-in-mixture pruning holds for any zero list containing
the aggregate mixture. -/
theorem screenE_component_to_mix_mem_eq_zero (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) (hrefl : ∀ x, R x x) (a : A) (ha : w a ≠ 0)
    (zs : List (PMF X)) (hmix : w.bind f ∈ zs) (g : X → ℝ≥0∞) :
    screenE (f a) R zs g = 0 := by
  apply le_antisymm _ zero_le
  calc
    screenE (f a) R zs g ≤ screenE (f a) R [w.bind f] g :=
      screenE_le_of_subset (f a) R (fun ρ hρ => by
        rw [List.mem_singleton.mp hρ]
        exact hmix) g
    _ = 0 := screenE_component_to_mix_eq_zero w f R hrefl a ha g

/-! ### Process specializations of component pruning -/

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V)
  (ν : PMF ℕ) (v0 : V)

/-- Environment-averaged hybrid component screens feed only the mixed
ordinary `crossDres` family. -/
lemma avg_quenchedFresh_screen_le_crossDres (h : ℕ)
    (ρs : PMF (FullLab (V × ℕ) h)) :
    ∑' eb, counterEnvLaw ν h eb * ∑' ea, counterEnvLaw ν h ea *
        screenE ρs (fullSim (labRel Rv) h)
          [quenchedFresh μ v0 h ea]
          (WresD α (quenchedFresh μ v0 h eb)
            (fullSim (labRel Rv) h))
      ≤ ∑' eb, counterEnvLaw ν h eb * ∑' ea, counterEnvLaw ν h ea *
          crossDres α ρs (quenchedFresh μ v0 h ea)
            (quenchedFresh μ v0 h eb) (fullSim (labRel Rv) h) :=
  avg_component_screen_component_WresD_le_crossDres α ρs
    (counterEnvLaw ν h) (quenchedFresh μ v0 h)
    (fullSim (labRel Rv) h)

/-- Environment specialization of the closed hybrid conversion. -/
lemma avg_quenchedFresh_screen_le_PhiDres_pair (hα : 0 < α) (h : ℕ)
    (ρs : PMF (FullLab (V × ℕ) h)) :
    ∑' eb, counterEnvLaw ν h eb * ∑' ea, counterEnvLaw ν h ea *
        screenE ρs (fullSim (labRel Rv) h)
          [quenchedFresh μ v0 h ea]
          (WresD α (quenchedFresh μ v0 h eb)
            (fullSim (labRel Rv) h))
      ≤ PhiDres α ρs (Tlaw μ ν v0 h) (fullSim (labRel Rv) h)
        + ∑' eb, counterEnvLaw ν h eb *
            PhiDres α ρs (quenchedFresh μ v0 h eb)
              (fullSim (labRel Rv) h) := by
  have hgen := avg_component_screen_component_WresD_le_PhiDres_pair
    α hα ρs (counterEnvLaw ν h) (quenchedFresh μ v0 h)
      (fullSim (labRel Rv) h)
  rw [(counterEnv_bind_quenched μ ν v0 h).2] at hgen
  exact hgen

/-- In the sharper decomposition, the zero-interface part is annealed and
vanishes; only the regular mixed moment toward `Tlaw` remains. -/
lemma avg_quenchedFresh_screen_le_regular (h : ℕ)
    (ρs : PMF (FullLab (V × ℕ) h)) :
    ∑' eb, counterEnvLaw ν h eb * ∑' ea, counterEnvLaw ν h ea *
        screenE ρs (fullSim (labRel Rv) h)
          [quenchedFresh μ v0 h ea]
          (WresD α (quenchedFresh μ v0 h eb)
            (fullSim (labRel Rv) h))
      ≤ ∑' eb, counterEnvLaw ν h eb *
          regularBadTilt ρs (Tlaw μ ν v0 h) (fullSim (labRel Rv) h)
            (WresD α (quenchedFresh μ v0 h eb)
              (fullSim (labRel Rv) h)) := by
  have hgen := avg_component_screen_component_WresD_le_regular α ρs
    (counterEnvLaw ν h) (quenchedFresh μ v0 h)
    (fullSim (labRel Rv) h)
  have hfresh := (counterEnv_bind_quenched μ ν v0 h).2
  rw [hfresh] at hgen
  exact hgen

/-! ### Root transfer for the mixed coordinate -/

/-- Exact fresh-root bad-degree split in `ℝ≥0∞`. -/
lemma qE_qInterp_F_succ_branch (v : V) (k h : ℕ)
    (e : FullLab ℕ (h + 1))
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    qE (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
      = qE μ Rv v + rE μ Rv v
          * qE (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp := by
  apply (ENNReal.toReal_eq_toReal_iff' qE_ne_top
    (ENNReal.add_ne_top.mpr ⟨qE_ne_top,
      ENNReal.mul_ne_top rE_ne_top qE_ne_top⟩)).mp
  rw [ENNReal.toReal_add qE_ne_top
      (ENNReal.mul_ne_top rE_ne_top qE_ne_top), ENNReal.toReal_mul]
  change q (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
      = q μ Rv v + (rE μ Rv v).toReal
          * q (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp
  rw [q_qInterp_F_succ_branch Rv μ v0 v k h e xp, toReal_rE_eq]

/-- The restricted inverse weight of a fresh-root component factors into
the state-root weight and the component child-pair weight. -/
lemma WresD_qInterp_F_succ_branch (v : V) (k h : ℕ)
    (e : FullLab ℕ (h + 1))
    (xp : FullLab (V × ℕ) h × FullLab (V × ℕ) h) :
    WresD α (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp)
      = WresD α μ Rv v
          * WresD α
              (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
              (SquareRel (fullSim (labRel Rv) h)) xp := by
  have hr := rE_qInterp_F_succ_branch Rv μ v0 v k h e xp
  by_cases hv : rE μ Rv v = 0
  · have hfull : rE (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp) = 0 := by
      rw [hr, hv, zero_mul]
    rw [WresD, if_pos hfull, WresD, if_pos hv, zero_mul]
  · by_cases hc : rE
        (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
          (SquareRel (fullSim (labRel Rv) h)) xp = 0
    · have hfull : rE (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
          (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp) = 0 := by
        rw [hr, hc, mul_zero]
      have hWc : WresD α
          (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
          (SquareRel (fullSim (labRel Rv) h)) xp = 0 := by
        rw [WresD, if_pos hc]
      rw [WresD, if_pos hfull, hWc, mul_zero]
    · have hfull : rE (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
          (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp) ≠ 0 := by
        rw [hr]
        exact mul_ne_zero hv hc
      rw [← rE_rpow_neg_eq_WresD
          (qInterp μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
          (fullSim (labRel Rv) (h + 1)) (branch (v, k) xp) hfull,
        ← rE_rpow_neg_eq_WresD μ Rv v hv,
        ← rE_rpow_neg_eq_WresD
          (qChildren μ v0 (⟨QMode.F, e⟩ : QTgt (h + 1)))
          (SquareRel (fullSim (labRel Rv) h)) xp hc,
        hr, ENNReal.mul_rpow_of_ne_zero hv hc]

/-- Three forced quenched roots pass exactly to their child mixed
coordinate. -/
lemma crossDres_qInterp_Z_Z_Z_succ (hrefl : Rv v0 v0)
    (ks kb kn h : ℕ) (es eb en : FullLab ℕ (h + 1)) :
    crossDres α
        (qInterp μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)))
        (qInterp μ v0 (⟨QMode.Z kb, eb⟩ : QTgt (h + 1)))
        (qInterp μ v0 (⟨QMode.Z kn, en⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1))
      = crossDres α
          (qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)))
          (qChildren μ v0 (⟨QMode.Z kb, eb⟩ : QTgt (h + 1)))
          (qChildren μ v0 (⟨QMode.Z kn, en⟩ : QTgt (h + 1)))
          (SquareRel (fullSim (labRel Rv) h)) := by
  rw [qInterp_Z_succ, qInterp_Z_succ, qInterp_Z_succ,
    crossDres_map_branch_law]
  simp only [labRel, hrefl, if_true]

/-- A fresh normalizing root contributes exactly its state inverse weight
to a forced-source/forced-bad mixed row. -/
lemma crossDres_qInterp_Z_Z_F_succ (hrefl : Rv v0 v0)
    (ks kb h : ℕ) (es eb en : FullLab ℕ (h + 1)) :
    crossDres α
        (qInterp μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)))
        (qInterp μ v0 (⟨QMode.Z kb, eb⟩ : QTgt (h + 1)))
        (qInterp μ v0 (⟨QMode.F, en⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1))
      = WresD α μ Rv v0 * crossDres α
          (qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)))
          (qChildren μ v0 (⟨QMode.Z kb, eb⟩ : QTgt (h + 1)))
          (qChildren μ v0 (⟨QMode.F, en⟩ : QTgt (h + 1)))
          (SquareRel (fullSim (labRel Rv) h)) := by
  simp only [qInterp_Z_succ]
  rw [crossDres, tsum_map_mul]
  calc
    _ = ∑' xp, WresD α μ Rv v0
          * (qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)) xp
            * (qE (qChildren μ v0 (⟨QMode.Z kb, eb⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h)) xp
              * WresD α
                  (qChildren μ v0 (⟨QMode.F, en⟩ : QTgt (h + 1)))
                  (SquareRel (fullSim (labRel Rv) h)) xp)) := by
            refine tsum_congr fun xp => ?_
            rw [qE_map_branch_law, WresD_qInterp_F_succ_branch]
            simp only [labRel, hrefl, if_true]
            ring
    _ = WresD α μ Rv v0 * ∑' xp,
          qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)) xp
            * (qE (qChildren μ v0 (⟨QMode.Z kb, eb⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h)) xp
              * WresD α
                  (qChildren μ v0 (⟨QMode.F, en⟩ : QTgt (h + 1)))
                  (SquareRel (fullSim (labRel Rv) h)) xp) :=
            ENNReal.tsum_mul_left
    _ = _ := by rw [crossDres]

/-- A fresh bad root splits into a root mismatch charge plus the child
mixed coordinate when the source and normalization roots are forced. -/
lemma crossDres_qInterp_Z_F_Z_succ (hrefl : Rv v0 v0)
    (ks kn h : ℕ) (es eb en : FullLab ℕ (h + 1)) :
    crossDres α
        (qInterp μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)))
        (qInterp μ v0 (⟨QMode.F, eb⟩ : QTgt (h + 1)))
        (qInterp μ v0 (⟨QMode.Z kn, en⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1))
      = qE μ Rv v0 *
          (∑' xp, qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)) xp
            * WresD α
                (qChildren μ v0 (⟨QMode.Z kn, en⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h)) xp)
        + rE μ Rv v0 * crossDres α
            (qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)))
            (qChildren μ v0 (⟨QMode.F, eb⟩ : QTgt (h + 1)))
            (qChildren μ v0 (⟨QMode.Z kn, en⟩ : QTgt (h + 1)))
            (SquareRel (fullSim (labRel Rv) h)) := by
  simp only [qInterp_Z_succ]
  rw [crossDres, tsum_map_mul]
  calc
    _ = ∑' xp, (
          qE μ Rv v0 *
              (qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)) xp
                * WresD α
                    (qChildren μ v0 (⟨QMode.Z kn, en⟩ : QTgt (h + 1)))
                    (SquareRel (fullSim (labRel Rv) h)) xp)
          + rE μ Rv v0 *
              (qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)) xp
                * (qE (qChildren μ v0 (⟨QMode.F, eb⟩ : QTgt (h + 1)))
                    (SquareRel (fullSim (labRel Rv) h)) xp
                  * WresD α
                      (qChildren μ v0 (⟨QMode.Z kn, en⟩ : QTgt (h + 1)))
                      (SquareRel (fullSim (labRel Rv) h)) xp))) := by
            refine tsum_congr fun xp => ?_
            rw [qE_qInterp_F_succ_branch,
              WresD_map_branch_law]
            simp only [labRel, hrefl, if_true]
            ring
    _ = qE μ Rv v0 * (∑' xp,
          qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)) xp
            * WresD α
                (qChildren μ v0 (⟨QMode.Z kn, en⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h)) xp)
        + rE μ Rv v0 * (∑' xp,
          qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)) xp
            * (qE (qChildren μ v0 (⟨QMode.F, eb⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h)) xp
              * WresD α
                  (qChildren μ v0 (⟨QMode.Z kn, en⟩ : QTgt (h + 1)))
                  (SquareRel (fullSim (labRel Rv) h)) xp)) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left,
              ENNReal.tsum_mul_left]
    _ = _ := by rw [crossDres]

/-- With both targets fresh, the two exact root factors multiply; the
remaining terms are one inverse moment and one child mixed coordinate. -/
lemma crossDres_qInterp_Z_F_F_succ
    (ks h : ℕ) (es eb en : FullLab ℕ (h + 1)) :
    crossDres α
        (qInterp μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)))
        (qInterp μ v0 (⟨QMode.F, eb⟩ : QTgt (h + 1)))
        (qInterp μ v0 (⟨QMode.F, en⟩ : QTgt (h + 1)))
        (fullSim (labRel Rv) (h + 1))
      = WresD α μ Rv v0 * qE μ Rv v0 *
          (∑' xp, qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)) xp
            * WresD α
                (qChildren μ v0 (⟨QMode.F, en⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h)) xp)
        + WresD α μ Rv v0 * rE μ Rv v0 * crossDres α
            (qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)))
            (qChildren μ v0 (⟨QMode.F, eb⟩ : QTgt (h + 1)))
            (qChildren μ v0 (⟨QMode.F, en⟩ : QTgt (h + 1)))
            (SquareRel (fullSim (labRel Rv) h)) := by
  simp only [qInterp_Z_succ]
  rw [crossDres, tsum_map_mul]
  calc
    (∑' xp, qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)) xp
        * (qE (qInterp μ v0 (⟨QMode.F, eb⟩ : QTgt (h + 1)))
            (fullSim (labRel Rv) (h + 1)) (branch (v0, ks) xp)
          * WresD α (qInterp μ v0 (⟨QMode.F, en⟩ : QTgt (h + 1)))
              (fullSim (labRel Rv) (h + 1)) (branch (v0, ks) xp)))
      = ∑' xp, (
          (WresD α μ Rv v0 * qE μ Rv v0) *
              (qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)) xp
                * WresD α
                    (qChildren μ v0 (⟨QMode.F, en⟩ : QTgt (h + 1)))
                    (SquareRel (fullSim (labRel Rv) h)) xp)
          + (WresD α μ Rv v0 * rE μ Rv v0) *
              (qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)) xp
                * (qE (qChildren μ v0 (⟨QMode.F, eb⟩ : QTgt (h + 1)))
                    (SquareRel (fullSim (labRel Rv) h)) xp
                  * WresD α
                      (qChildren μ v0 (⟨QMode.F, en⟩ : QTgt (h + 1)))
                      (SquareRel (fullSim (labRel Rv) h)) xp))) := by
            refine tsum_congr fun xp => ?_
            rw [qE_qInterp_F_succ_branch,
              WresD_qInterp_F_succ_branch]
            ring
    _ = (WresD α μ Rv v0 * qE μ Rv v0) * (∑' xp,
          qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)) xp
            * WresD α
                (qChildren μ v0 (⟨QMode.F, en⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h)) xp)
        + (WresD α μ Rv v0 * rE μ Rv v0) * (∑' xp,
          qChildren μ v0 (⟨QMode.Z ks, es⟩ : QTgt (h + 1)) xp
            * (qE (qChildren μ v0 (⟨QMode.F, eb⟩ : QTgt (h + 1)))
                (SquareRel (fullSim (labRel Rv) h)) xp
              * WresD α
                  (qChildren μ v0 (⟨QMode.F, en⟩ : QTgt (h + 1)))
                  (SquareRel (fullSim (labRel Rv) h)) xp)) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left,
              ENNReal.tsum_mul_left]
    _ = _ := by rw [crossDres]

/-- A charged fixed-counter fresh cell is a component of `Tlaw`, so a
screen whose zero list contains `Tlaw` vanishes. -/
lemma screenE_Flaw_Tlaw_mem_eq_zero (hrefl : ∀ v, Rv v v) {k h : ℕ}
    (hνk : ν k ≠ 0) (zs : List (PMF (FullLab (V × ℕ) h)))
    (hT : Tlaw μ ν v0 h ∈ zs) (g : FullLab (V × ℕ) h → ℝ≥0∞) :
    screenE (Flaw μ ν v0 k h) (fullSim (labRel Rv) h) zs g = 0 := by
  rw [Tlaw_eq_bind_Flaw μ ν v0 h] at hT
  exact screenE_component_to_mix_mem_eq_zero ν
    (fun j => Flaw μ ν v0 j h) (fullSim (labRel Rv) h)
    (fullSim_refl (labRel Rv) (fun s => hrefl s.1) h) k hνk zs hT g

/-- A charged forced context is a positive component of `Tlaw` with weight
`μ(v0)ν(k)`, so it enjoys the same stronger diagonal pruning. -/
lemma screenE_Zlaw_Tlaw_mem_eq_zero (hrefl : ∀ v, Rv v v)
    (hμ0 : μ v0 ≠ 0) {k h : ℕ} (hνk : ν k ≠ 0)
    (zs : List (PMF (FullLab (V × ℕ) h))) (hT : Tlaw μ ν v0 h ∈ zs)
    (g : FullLab (V × ℕ) h → ℝ≥0∞) :
    screenE (Zlaw μ ν v0 k h) (fullSim (labRel Rv) h) zs g = 0 := by
  have hQ : freshQ μ ν (v0, k) ≠ 0 := mul_ne_zero hμ0 hνk
  exact screenE_component_to_mix_mem_eq_zero (freshQ μ ν)
    (fun s => muM (varyK μ ν v0) s h) (fullSim (labRel Rv) h)
    (fullSim_refl (labRel Rv) (fun s => hrefl s.1) h) (v0, k) hQ zs hT g

/-- Formal grammar version: a charged `Fk k` cell is pruned whenever its
zero list contains the annealed fresh target `F`. -/
lemma interpScreen_Fk_F_prune (hrefl : ∀ v, Rv v v) {k h : ℕ}
    (hνk : ν k ≠ 0) (sc : GScreen) (hcell : sc.cell = Tgt.Fk k)
    (hF : Tgt.F ∈ sc.zlist) :
    interpScreen α Rv μ ν v0 h sc = 0 := by
  rw [interpScreen, hcell]
  exact screenE_Flaw_Tlaw_mem_eq_zero Rv μ ν v0 hrefl hνk _
    (List.mem_map.mpr ⟨Tgt.F, Finset.mem_toList.mpr hF, rfl⟩) _

/-- Formal grammar version for a charged forced cell `Z k`. -/
lemma interpScreen_Z_F_prune (hrefl : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0)
    {k h : ℕ} (hνk : ν k ≠ 0) (sc : GScreen)
    (hcell : sc.cell = Tgt.Z k) (hF : Tgt.F ∈ sc.zlist) :
    interpScreen α Rv μ ν v0 h sc = 0 := by
  rw [interpScreen, hcell]
  exact screenE_Zlaw_Tlaw_mem_eq_zero Rv μ ν v0 hrefl hμ0 hνk _
    (List.mem_map.mpr ⟨Tgt.F, Finset.mem_toList.mpr hF, rfl⟩) _

/-- A charged fixed-counter fresh normalization is killed by an annealed
fresh zero requirement. -/
lemma interpScreen_F_Fk_tilt_prune {k h : ℕ} (hνk : ν k ≠ 0)
    (sc : GScreen) (hnorm : sc.norm = some (Tgt.Fk k))
    (hF : Tgt.F ∈ sc.zlist) :
    interpScreen α Rv μ ν v0 h sc = 0 := by
  rw [interpScreen, hnorm]
  exact screenE_mix_mem_component_WresD_eq_zero α _ ν
    (fun j => Flaw μ ν v0 j h) (fullSim (labRel Rv) h) k hνk _
    (by
      rw [← Tlaw_eq_bind_Flaw μ ν v0 h]
      exact List.mem_map.mpr ⟨Tgt.F, Finset.mem_toList.mpr hF, rfl⟩)

/-- A charged forced normalization is likewise killed by an annealed
fresh zero requirement. -/
lemma interpScreen_F_Z_tilt_prune (hμ0 : μ v0 ≠ 0) {k h : ℕ}
    (hνk : ν k ≠ 0) (sc : GScreen)
    (hnorm : sc.norm = some (Tgt.Z k)) (hF : Tgt.F ∈ sc.zlist) :
    interpScreen α Rv μ ν v0 h sc = 0 := by
  rw [interpScreen, hnorm]
  exact screenE_mix_mem_component_WresD_eq_zero α _ (freshQ μ ν)
    (fun s => muM (varyK μ ν v0) s h) (fullSim (labRel Rv) h)
    (v0, k) (mul_ne_zero hμ0 hνk) _
    (List.mem_map.mpr ⟨Tgt.F, Finset.mem_toList.mpr hF, rfl⟩)

/-! ### Eventual-support consequences -/

/-- Under saturation of the off-by-one semigroup, a sufficiently large
shifted arity `m` in that semigroup gives a charged counter `m + 1`, whose
forced source cell is pruned by an annealed fresh zero requirement. -/
theorem EventuallyChargesShiftedSemigroup.large_Z_cell_prune
    (hsat : EventuallyChargesShiftedSemigroup ν)
    (hrefl : ∀ v, Rv v v) (hμ0 : μ v0 ≠ 0) :
    ∃ K : ℕ, ∀ {m h : ℕ} (sc : GScreen), K ≤ m →
      m ∈ shiftedSupportSemigroup ν →
      sc.cell = Tgt.Z (m + 1) → Tgt.F ∈ sc.zlist →
      interpScreen α Rv μ ν v0 h sc = 0 := by
  obtain ⟨K, hK⟩ := hsat
  exact ⟨K, fun sc hm hmem hcell hF =>
    interpScreen_Z_F_prune α Rv μ ν v0 hrefl hμ0
      (hK _ hm hmem) sc hcell hF⟩

/-- The same shifted-semigroup pruning for fixed-counter fresh source
cells. -/
theorem EventuallyChargesShiftedSemigroup.large_Fk_cell_prune
    (hsat : EventuallyChargesShiftedSemigroup ν)
    (hrefl : ∀ v, Rv v v) :
    ∃ K : ℕ, ∀ {m h : ℕ} (sc : GScreen), K ≤ m →
      m ∈ shiftedSupportSemigroup ν →
      sc.cell = Tgt.Fk (m + 1) → Tgt.F ∈ sc.zlist →
      interpScreen α Rv μ ν v0 h sc = 0 := by
  obtain ⟨K, hK⟩ := hsat
  exact ⟨K, fun sc hm hmem hcell hF =>
    interpScreen_Fk_F_prune α Rv μ ν v0 hrefl
      (hK _ hm hmem) sc hcell hF⟩

/-- Shifted-semigroup pruning for a large forced normalization. -/
theorem EventuallyChargesShiftedSemigroup.large_Z_tilt_prune
    (hsat : EventuallyChargesShiftedSemigroup ν)
    (hμ0 : μ v0 ≠ 0) :
    ∃ K : ℕ, ∀ {m h : ℕ} (sc : GScreen), K ≤ m →
      m ∈ shiftedSupportSemigroup ν →
      sc.norm = some (Tgt.Z (m + 1)) → Tgt.F ∈ sc.zlist →
      interpScreen α Rv μ ν v0 h sc = 0 := by
  obtain ⟨K, hK⟩ := hsat
  exact ⟨K, fun sc hm hmem hnorm hF =>
    interpScreen_F_Z_tilt_prune α Rv μ ν v0 hμ0
      (hK _ hm hmem) sc hnorm hF⟩

/-- Shifted-semigroup pruning for a large fixed-counter fresh
normalization. -/
theorem EventuallyChargesShiftedSemigroup.large_Fk_tilt_prune
    (hsat : EventuallyChargesShiftedSemigroup ν) :
    ∃ K : ℕ, ∀ {m h : ℕ} (sc : GScreen), K ≤ m →
      m ∈ shiftedSupportSemigroup ν →
      sc.norm = some (Tgt.Fk (m + 1)) → Tgt.F ∈ sc.zlist →
      interpScreen α Rv μ ν v0 h sc = 0 := by
  obtain ⟨K, hK⟩ := hsat
  exact ⟨K, fun sc hm hmem hnorm hF =>
    interpScreen_F_Fk_tilt_prune α Rv μ ν v0
      (hK _ hm hmem) sc hnorm hF⟩

/-- If the component-dead event and the inverse normalization are sampled
independently, the integrated inverse-moment estimate reduces their average
to an averaged unit screen plus averaged ordinary potentials. -/
lemma avg_component_screen_component_WresD_le (α : ℝ) (hα : 1 ≤ α)
    (ρs : PMF X) (wa : PMF A) (fa : A → PMF X)
    (wb : PMF A) (fb : A → PMF X) (R : X → X → Prop) :
    ∑' a, wa a * ∑' b, wb b * screenE ρs R [fa a] (WresD α (fb b) R)
      ≤ failureD ρs (wa.bind fa) R
        + ENNReal.ofReal α * ∑' b, wb b * PhiDres α ρs (fb b) R := by
  calc
    (∑' a, wa a * ∑' b, wb b * screenE ρs R [fa a] (WresD α (fb b) R))
        ≤ ∑' a, wa a * ∑' b, wb b
            * (screenE ρs R [fa a] (fun _ => 1)
              + ENNReal.ofReal α * PhiDres α ρs (fb b) R) := by
                refine ENNReal.tsum_le_tsum fun a => mul_le_mul_right ?_ _
                refine ENNReal.tsum_le_tsum fun b => mul_le_mul_right ?_ _
                exact screenE_WresD_le hα ρs (fb b) R [fa a]
    _ = (∑' a, wa a * screenE ρs R [fa a] (fun _ => 1))
        + ENNReal.ofReal α * ∑' b, wb b * PhiDres α ρs (fb b) R := by
          calc
            (∑' a, wa a * ∑' b, wb b
                * (screenE ρs R [fa a] (fun _ => 1)
                  + ENNReal.ofReal α * PhiDres α ρs (fb b) R))
                = ∑' a, wa a * (screenE ρs R [fa a] (fun _ => 1)
                    + ENNReal.ofReal α
                      * ∑' b, wb b * PhiDres α ρs (fb b) R) := by
                    refine tsum_congr fun a => ?_
                    congr 1
                    rw [tsum_congr fun b => show wb b
                        * (screenE ρs R [fa a] (fun _ => 1)
                          + ENNReal.ofReal α * PhiDres α ρs (fb b) R)
                        = wb b * screenE ρs R [fa a] (fun _ => 1)
                          + ENNReal.ofReal α
                            * (wb b * PhiDres α ρs (fb b) R) from by ring,
                      ENNReal.tsum_add, ENNReal.tsum_mul_right,
                      PMF.tsum_coe, one_mul, ENNReal.tsum_mul_left]
            _ = (∑' a, wa a * screenE ρs R [fa a] (fun _ => 1))
                + ENNReal.ofReal α * ∑' b, wb b * PhiDres α ρs (fb b) R := by
                    rw [tsum_congr fun a => show wa a
                        * (screenE ρs R [fa a] (fun _ => 1)
                          + ENNReal.ofReal α
                            * ∑' b, wb b * PhiDres α ρs (fb b) R)
                        = wa a * screenE ρs R [fa a] (fun _ => 1)
                          + ENNReal.ofReal α * (wa a
                            * ∑' b, wb b * PhiDres α ρs (fb b) R) from by ring,
                      ENNReal.tsum_add, ENNReal.tsum_mul_left,
                      ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ failureD ρs (wa.bind fa) R
        + ENNReal.ofReal α * ∑' b, wb b * PhiDres α ρs (fb b) R :=
          add_le_add (avg_component_screen_le_failureD ρs wa fa R) le_rfl

/-! ### Diagonal screens against a member of their zero list -/

/-- A screen whose zero list contains `ρbad`, with unit normalization, is
bounded by the directed failure from its source to `ρbad`. -/
lemma screenE_le_failureD_of_mem (ρs ρbad : PMF X)
    (R : X → X → Prop) (zs : List (PMF X))
    (hmem : ρbad ∈ zs) :
    screenE ρs R zs (fun _ => 1) ≤ failureD ρs ρbad R := by
  rw [screenE, failureD]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have hind : screenInd R zs x ≤
      if rE ρbad R x = 0 then (1 : ℝ≥0∞) else 0 := by
    rw [screenInd]
    by_cases hall : ∀ ρ ∈ zs, rE ρ R x = 0
    · rw [if_pos hall, if_pos (hall ρbad hmem)]
    · rw [if_neg hall]
      exact zero_le
  calc
    ρs x * screenInd R zs x * 1
        ≤ ρs x * (if rE ρbad R x = 0 then 1 else 0) := by
          simpa only [mul_one] using mul_le_mul_right hind (ρs x)
    _ ≤ ρs x * qE ρbad R x :=
      mul_le_mul_right (deadInd_le_qE ρbad R x) _

/-- With an inverse normalization, a formal diagonal screen returns to the
mixed bad-degree/inverse-normalization coordinate `crossDres`. -/
lemma screenE_WresD_le_crossDres_of_mem (α : ℝ)
    (ρs ρbad ρnorm : PMF X) (R : X → X → Prop)
    (zs : List (PMF X)) (hmem : ρbad ∈ zs) :
    screenE ρs R zs (WresD α ρnorm R)
      ≤ crossDres α ρs ρbad ρnorm R := by
  rw [screenE, crossDres]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have hind : screenInd R zs x ≤
      if rE ρbad R x = 0 then (1 : ℝ≥0∞) else 0 := by
    rw [screenInd]
    by_cases hall : ∀ ρ ∈ zs, rE ρ R x = 0
    · rw [if_pos hall, if_pos (hall ρbad hmem)]
    · rw [if_neg hall]
      exact zero_le
  calc
    ρs x * screenInd R zs x * WresD α ρnorm R x
        ≤ ρs x * (if rE ρbad R x = 0 then 1 else 0)
            * WresD α ρnorm R x :=
          mul_le_mul_left (mul_le_mul_right hind _) _
    _ ≤ ρs x * qE ρbad R x * WresD α ρnorm R x :=
      mul_le_mul_left (mul_le_mul_right
        (deadInd_le_qE ρbad R x) _) _
    _ = ρs x * (qE ρbad R x * WresD α ρnorm R x) := by ring

end GraphMarkovMatching
