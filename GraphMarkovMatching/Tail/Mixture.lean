/-
Weighted mixture identities for the unbounded-offspring proof attempt.

The finite-support ledger splits a fresh target into an unweighted union
of dead components and then pays inverse powers of the component atoms.
That operation cannot survive an infinite support.  The identity below is
the replacement starting point: it keeps the mixture coefficient on every
component and retains the inverse degree of the aggregate target.

This identity alone is not a closure theorem.  Its aggregate inverse tilt
must still be controlled by a weighted ordinary/screen ledger.
-/
import GraphMarkovMatching.Process.Ledger
import GraphMarkovMatching.Process.Screens

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

variable {A X : Type}

/-- **Weighted bad-degree decomposition of a mixture target.**  The
restricted potential toward `w.bind f` is exactly the mixture-weighted
sum of component bad degrees, all carrying the inverse degree of the
aggregate target.  In particular no factor `w(a)⁻¹` is introduced. -/
lemma PhiDres_bind_eq_tsum_bad_tilt (α : ℝ) (hα : 0 < α)
    (ρs : PMF X) (w : PMF A) (f : A → PMF X) (R : X → X → Prop) :
    PhiDres α ρs (w.bind f) R
      = ∑' a, w a * ∑' x, ρs x
          * (qE (f a) R x * WresD α (w.bind f) R x) := by
  rw [PhiDres]
  calc
    (∑' x, ρs x *
        (if rE (w.bind f) R x = 0 then 0
          else phiE α (q (w.bind f) R x)))
        = ∑' x, ∑' a, w a *
            (ρs x * (qE (f a) R x * WresD α (w.bind f) R x)) := by
            refine tsum_congr fun x => ?_
            by_cases hr : rE (w.bind f) R x = 0
            · rw [if_pos hr, mul_zero]
              refine (ENNReal.tsum_eq_zero.mpr fun a => ?_).symm
              rw [WresD, if_pos hr, mul_zero, mul_zero, mul_zero]
            · rw [if_neg hr,
                phiE_eq_qE_mul_rpow α R (w.bind f) hα x,
                rE_rpow_neg_eq_WresD (w.bind f) R x hr,
                qE_bind]
              calc
                ρs x * ((∑' a, w a * qE (f a) R x)
                    * WresD α (w.bind f) R x)
                    = (∑' a, w a * qE (f a) R x)
                        * (ρs x * WresD α (w.bind f) R x) := by ring
                _ = ∑' a, (w a * qE (f a) R x)
                        * (ρs x * WresD α (w.bind f) R x) :=
                      ENNReal.tsum_mul_right.symm
                _ = ∑' a, w a *
                      (ρs x * (qE (f a) R x
                        * WresD α (w.bind f) R x)) := by
                      refine tsum_congr fun a => ?_
                      ring
    _ = ∑' a, ∑' x, w a *
          (ρs x * (qE (f a) R x * WresD α (w.bind f) R x)) :=
        ENNReal.tsum_comm
    _ = ∑' a, w a * ∑' x, ρs x
          * (qE (f a) R x * WresD α (w.bind f) R x) := by
        refine tsum_congr fun a => ?_
        rw [ENNReal.tsum_mul_left]

end GraphMarkovMatching
