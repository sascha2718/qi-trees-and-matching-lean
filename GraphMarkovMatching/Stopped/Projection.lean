/-
State projections of typed tree labellings and elementary probability-law transports.
-/
import GraphMarkovMatching.Stopped.Model

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support Model
open scoped ENNReal Classical

variable {V : Type}

def statesOf {X : Type} : (h : ℕ) → FullLab (V × X) h → FullLab V h
  | 0, x => x.1
  | h + 1, x => (x.1.1, statesOf h x.2.1, statesOf h x.2.2)

def statesOf' {X : Type} : (h : ℕ) → FullLab (X × V) h → FullLab V h
  | 0, x => x.2
  | h + 1, x => (x.1.2, statesOf' h x.2.1, statesOf' h x.2.2)

lemma statesOf_leaf {X : Type} (s : V × X) : statesOf 0 (leaf s) = leaf s.1 := rfl

lemma statesOf_branch {X : Type} {h : ℕ} (s : V × X) (p : FullLab (V × X) h × FullLab (V × X) h) :
    statesOf (h + 1) (branch s p) = branch s.1 (statesOf h p.1, statesOf h p.2) := rfl

lemma statesOf'_leaf {X : Type} (s : X × V) : statesOf' 0 (leaf s) = leaf s.2 := rfl

lemma statesOf'_branch {X : Type} {h : ℕ} (s : X × V)
    (p : FullLab (X × V) h × FullLab (X × V) h) :
    statesOf' (h + 1) (branch s p) = branch s.2 (statesOf' h p.1, statesOf' h p.2) := rfl

lemma fullMatchesK_fst_iff {X : Type} (Rv : V → V → Prop) :
    ∀ (h : ℕ) (π : AutK 1 0 h) (x y : FullLab (V × X) h),
      fullMatchesK (fun s t : V × X => Rv s.1 t.1) 1 0 h π x y
        ↔ fullMatchesK Rv 1 0 h π (statesOf h x) (statesOf h y) := by
  intro h
  induction h with
  | zero => exact fun _ _ _ => Iff.rfl
  | succ h ih =>
    intro π x y
    obtain ⟨b, π₁, π₂⟩ := π
    cases b
    · exact and_congr Iff.rfl (and_congr (ih π₁ x.2.1 y.2.1) (ih π₂ x.2.2 y.2.2))
    · exact and_congr Iff.rfl (and_congr (ih π₁ x.2.1 y.2.2) (ih π₂ x.2.2 y.2.1))

lemma fullMatchesK_srel_iff {I : Type} (M : Model V I) :
    ∀ (h : ℕ) (π : AutK 1 0 h) (x y : FullLab (I × V) h),
      fullMatchesK M.srel 1 0 h π x y
        ↔ fullMatchesK M.R 1 0 h π (statesOf' h x) (statesOf' h y) := by
  intro h
  induction h with
  | zero => exact fun _ _ _ => Iff.rfl
  | succ h ih =>
    intro π x y
    obtain ⟨b, π₁, π₂⟩ := π
    cases b
    · exact and_congr Iff.rfl (and_congr (ih π₁ x.2.1 y.2.1) (ih π₂ x.2.2 y.2.2))
    · exact and_congr Iff.rfl (and_congr (ih π₁ x.2.1 y.2.2) (ih π₂ x.2.2 y.2.1))

lemma fullSim_srel_iff {I : Type} (M : Model V I) (h : ℕ) (x y : FullLab (I × V) h) :
    M.sim h x y ↔ fullSim M.R h (statesOf' h x) (statesOf' h y) :=
  exists_congr fun π => fullMatchesK_srel_iff M h π x y

lemma prodPMF_bind_eq {A B D : Type} (p : PMF A) (q : PMF B) (f : A × B → PMF D) :
    (prodPMF p q).bind f = p.bind fun a => q.bind fun b => f (a, b) := by
  ext x
  rw [PMF.bind_apply, PMF.bind_apply, ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  rw [prodPMF_apply, mul_assoc]

lemma prodPMF_map_prod {A B A' B' : Type} (p : PMF A) (q : PMF B) (f : A → A') (g : B → B') :
    (prodPMF p q).map (Prod.map f g) = prodPMF (p.map f) (q.map g) := by
  ext x
  rw [PMF.map_apply, prodPMF_apply, PMF.map_apply, PMF.map_apply, ← tsum_prod_split]
  refine tsum_congr fun s => ?_
  rw [prodPMF_apply]
  by_cases h1 : x.1 = f s.1
  · by_cases h2 : x.2 = g s.2
    · rw [if_pos h1, if_pos h2, if_pos (Prod.ext h1 h2)]
    · rw [if_neg h2, if_neg (fun h => h2 (congrArg Prod.snd h)), mul_zero]
  · rw [if_neg h1, if_neg (fun h => h1 (congrArg Prod.fst h)), zero_mul]

lemma bind_congr_of_ne_zero {A D : Type} (p : PMF A) {f g : A → PMF D}
    (h : ∀ a, p a ≠ 0 → f a = g a) : p.bind f = p.bind g := by
  ext x
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p a = 0
  · rw [ha, zero_mul, zero_mul]
  · rw [h a ha]

end GraphMarkovMatching.Stopped
