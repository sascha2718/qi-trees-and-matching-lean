/-
Good degrees under pure laws, maps and mixtures, and independent product laws.
-/
import GraphMarkovMatching.Potential.Directed

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

noncomputable def goodInd (R : X → X → Prop) (z y : X) : ℝ≥0∞ :=
  if R z y then 1 else 0

lemma rE_eq_tsum_mul (ν : PMF X) (R : X → X → Prop) (z : X) :
    rE ν R z = ∑' y, ν y * goodInd R z y := by
  rw [rE]
  exact tsum_congr fun y => by by_cases h : R z y <;> simp [goodInd, h]

lemma rE_map {A : Type u} (μ : PMF A) (g : A → X) (R : X → X → Prop) (z : X) :
    rE (μ.map g) R z = ∑' a, μ a * goodInd R z (g a) := by
  rw [rE_eq_tsum_mul, tsum_map_mul]

lemma rE_bind {A : Type u} (w : PMF A) (f : A → PMF X) (R : X → X → Prop)
    (z : X) :
    rE (w.bind f) R z = ∑' a, w a * rE (f a) R z := by
  rw [rE_eq_tsum_mul, tsum_bind_mul]
  exact tsum_congr fun a => by rw [rE_eq_tsum_mul]

lemma rE_bind_eq_zero_iff {A : Type u} (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) (z : X) :
    rE (w.bind f) R z = 0 ↔ ∀ a, w a = 0 ∨ rE (f a) R z = 0 := by
  rw [rE_bind, ENNReal.tsum_eq_zero]
  exact forall_congr' fun a => mul_eq_zero

lemma mul_rE_le_rE_bind {A : Type u} (w : PMF A) (f : A → PMF X)
    (R : X → X → Prop) (z : X) (a : A) :
    w a * rE (f a) R z ≤ rE (w.bind f) R z := by
  rw [rE_bind]
  exact ENNReal.le_tsum a

lemma rE_pure {X : Type u} (b : X) (R : X → X → Prop) (z : X) :
    rE (PMF.pure b) R z = if R z b then 1 else 0 := by
  rw [rE]
  have hf : ∀ y, (if R z y then (PMF.pure b) y else 0)
      = if y = b then (if R z b then (1 : ℝ≥0∞) else 0) else 0 := by
    intro y
    by_cases h : y = b
    · subst y; simp [PMF.pure_apply]
    · simp [PMF.pure_apply, h]
  simp_rw [hf]
  simp

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

lemma bind_prodPMF_const_left {B C D : Type*} (Z : PMF C) (qb : PMF B) (g : B → PMF D) :
    qb.bind (fun b => prodPMF Z (g b)) = prodPMF Z (qb.bind g) := by
  apply PMF.ext
  intro x
  simp only [PMF.bind_apply, prodPMF_apply]
  calc (∑' b, qb b * (Z x.1 * g b x.2))
      = ∑' b, Z x.1 * (qb b * g b x.2) := tsum_congr fun b => by ring
    _ = Z x.1 * ∑' b, qb b * g b x.2 := ENNReal.tsum_mul_left


lemma tsum_pure_mul {A : Type u} (a : A) (F : A → ℝ≥0∞) :
    ∑' x, (PMF.pure a) x * F x = F a := by
  rw [show (∑' x, (PMF.pure a) x * F x) = ∑' x, if x = a then F x else 0 from
    tsum_congr fun x => by by_cases h : x = a <;> simp [PMF.pure_apply, h]]
  exact tsum_ite_eq a F


lemma tsum_mass_prod (μ₀ μ₁ : PMF X) (F G : X → ℝ≥0∞) :
    ∑' p : X × X, prodPMF μ₀ μ₁ p * (F p.1 * G p.2)
      = (∑' x, μ₀ x * F x) * (∑' x, μ₁ x * G x) := by
  rw [tsum_congr fun p : X × X => show prodPMF μ₀ μ₁ p * (F p.1 * G p.2)
      = (μ₀ p.1 * F p.1) * (μ₁ p.2 * G p.2) from by rw [prodPMF_apply]; ring]
  exact tsum_prod_split (fun x => μ₀ x * F x) (fun x => μ₁ x * G x)

end GraphMarkovMatching
