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
import GraphMarkovMatching.Tail.Mixture
import GraphMarkovMatching.Tail.Combinatorics
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

end GraphMarkovMatching
