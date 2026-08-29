/-
The infinite-tree matching theorem for Markov label fields
(`thm:konig` in `arbitrary_offspring_matching.tex`, the König/measure
packaging).

The combinatorial and abstract measure layers of the `Support` support layer
are generic in `(k, m)` and are reused verbatim at `k = 1`, `m = 0` (the full
group): restriction of automorphisms and labellings, König's lemma
(`infinite_matchingK_of_forall_level`), continuity from above, and the
interface theorem `infinite_tree_matchingK_prob`. What is new here:

* `muM_map_restrictLab`: the height-`n` marginal consistency of the Markov
  tree law, the fact any Kolmogorov-type construction must verify;
* `mix_map_restrictLab`: its root-mixture form, the projective input every
  endpoint theorem of the library instantiates.
-/
import GraphMarkovMatching.Process.Basic
import GraphMarkovMatching.Support.Measure

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical
open MeasureTheory

universe u
variable {S : Type u}

/-! ### Marginal consistency of the tree law -/

/-- Pushforward of a product PMF under a componentwise map. -/
lemma prodPMF_map_prodMap {A B C D : Type u} (p : PMF A) (q : PMF B)
    (f : A → C) (g : B → D) :
    (prodPMF p q).map (Prod.map f g) = prodPMF (p.map f) (q.map g) := by
  apply PMF.ext
  intro z
  rw [PMF.map_apply, prodPMF_apply, PMF.map_apply, PMF.map_apply,
    show ((∑' a, if z.1 = f a then p a else 0) * ∑' b, if z.2 = g b then q b else 0)
        = ∑' ab : A × B, (if z.1 = f ab.1 then p ab.1 else 0)
            * (if z.2 = g ab.2 then q ab.2 else 0) from
      (tsum_prod_split (fun a => if z.1 = f a then p a else 0)
        (fun b => if z.2 = g b then q b else 0)).symm]
  refine tsum_congr fun ab => ?_
  by_cases h1 : z.1 = f ab.1 <;> by_cases h2 : z.2 = g ab.2
  · rw [if_pos (show z = Prod.map f g ab from Prod.ext h1 h2), if_pos h1, if_pos h2,
      prodPMF_apply]
  · rw [if_neg (show ¬ z = Prod.map f g ab from fun hc => h2 (congrArg Prod.snd hc)),
      if_pos h1, if_neg h2, mul_zero]
  · rw [if_neg (show ¬ z = Prod.map f g ab from fun hc => h1 (congrArg Prod.fst hc)),
      if_neg h1, zero_mul]
  · rw [if_neg (show ¬ z = Prod.map f g ab from fun hc => h1 (congrArg Prod.fst hc)),
      if_neg h1, zero_mul]

/-- **Marginal consistency**: restricting a height-`(n+1)` Markov sample to
height `n` recovers the height-`n` law. -/
lemma muM_map_restrictLab (P : S → PMF (S × S)) (s : S) :
    ∀ n, (muM P s (n + 1)).map (restrictLab n) = muM P s n := by
  intro n
  induction n generalizing s with
  | zero =>
      rw [muM_succ, PMF.map_comp, muM_zero]
      have h : (restrictLab 0 ∘ branch (n := 0) s) = fun _ => leaf s := by
        funext p
        rfl
      rw [h]
      apply PMF.ext
      intro x
      rw [PMF.map_apply, PMF.pure_apply]
      by_cases hx : x = leaf s
      · rw [if_pos hx]
        calc (∑' p, if x = leaf s then pairMix P s 0 p else 0)
            = ∑' p, pairMix P s 0 p := tsum_congr fun p => by rw [if_pos hx]
          _ = 1 := PMF.tsum_coe _
      · rw [if_neg hx]
        refine ENNReal.tsum_eq_zero.mpr fun p => ?_
        rw [if_neg hx]
  | succ n ih =>
      rw [muM_succ, PMF.map_comp]
      have h : (restrictLab (n + 1) ∘ branch (n := n + 1) s)
          = (branch (n := n) s) ∘ (Prod.map (restrictLab n) (restrictLab n)) := by
        funext p
        rfl
      rw [h, ← PMF.map_comp, muM_succ]
      congr 1
      rw [pairMix, pairMix, PMF.map_bind]
      refine congrArg _ (funext fun στ => ?_)
      rw [prodPMF_map_prodMap, ih στ.1, ih στ.2]

/-- The root-mixture form of marginal consistency. -/
lemma mix_map_restrictLab (P : S → PMF (S × S)) (ι : PMF S) (n : ℕ) :
    ((ι.bind fun s => muM P s (n + 1)).map (restrictLab n))
      = ι.bind fun s => muM P s n := by
  rw [PMF.map_bind]
  exact congrArg _ (funext fun s => muM_map_restrictLab P s n)

/-! ### Full-group infinite matching -/

/-- Full-group infinite matching (the `k = 1` instance of `InfMatchK`). -/
abbrev InfMatch (R₀ : S → S → Prop) (X Y : (n : ℕ) → FullLab S n) : Prop :=
  InfMatchK R₀ 1 0 X Y

end GraphMarkovMatching
