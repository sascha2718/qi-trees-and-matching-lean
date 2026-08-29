/-
Generic support witnesses for directed matching.

A support witness records that every charged source atom has a related
charged target atom.  The property composes under mixtures, maps, products
and branch constructors, it kills the zero-interface mass `zMass`, and it
makes the restricted potential `PhiDres` agree with the ordinary directed
potential `PhiD`.  Nothing here refers to a particular grammar, so the
interface is shared by the grafted development and by the composite
two-law route.
-/
import GraphMarkovMatching.Process.Ledger

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

/-- Every charged source atom admits a related charged target atom. -/
def HasMatchingSupport {X Y : Type} (ρs : PMF X) (ρt : PMF Y)
    (R : X → Y → Prop) : Prop :=
  ∀ x, ρs x ≠ 0 → ∃ y, ρt y ≠ 0 ∧ R x y

lemma HasMatchingSupport.rE_ne_zero {X : Type} {ρs ρt : PMF X}
    {R : X → X → Prop} (h : HasMatchingSupport ρs ρt R)
    {x : X} (hx : ρs x ≠ 0) : rE ρt R x ≠ 0 := by
  obtain ⟨y, hy, hxy⟩ := h x hx
  rw [rE]
  have hterm : (if R x y then ρt y else 0) ≠ 0 := by
    simpa [hxy] using hy
  have hle : (if R x y then ρt y else 0) ≤
      ∑' z, if R x z then ρt z else 0 := ENNReal.le_tsum y
  intro hz
  exact hterm (le_antisymm (hle.trans (le_of_eq hz)) zero_le)

lemma HasMatchingSupport.zMass_eq_zero {X : Type} {ρs ρt : PMF X}
    {R : X → X → Prop} (h : HasMatchingSupport ρs ρt R) :
    zMass ρs ρt R = 0 := by
  rw [zMass]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : ρs x = 0
  · simp [hx]
  · simp [h.rE_ne_zero hx]

/-- Under an actual support witness the restriction in `PhiDres` removes no
charged source atom.  This is the safe bridge from the support induction to
the ordinary product estimates for `PhiD`. -/
lemma HasMatchingSupport.PhiDres_eq_PhiD {X : Type} {ρs ρt : PMF X}
    {R : X → X → Prop} (h : HasMatchingSupport ρs ρt R) (α : ℝ) :
    PhiDres α ρs ρt R = PhiD α ρs ρt R := by
  rw [PhiDres, PhiD]
  refine tsum_congr fun x => ?_
  by_cases hx : ρs x = 0
  · simp [hx]
  · simp [h.rE_ne_zero hx]

lemma matchingSupport_prod_square {X : Type}
    {ρa ρb ρc ρd : PMF X} {R : X → X → Prop}
    (h0 : HasMatchingSupport ρa ρc R)
    (h1 : HasMatchingSupport ρb ρd R) :
    HasMatchingSupport (prodPMF ρa ρb) (prodPMF ρc ρd) (SquareRel R) := by
  intro x hx
  have hxa : ρa x.1 ≠ 0 := by
    intro hz
    exact hx (by simp [prodPMF_apply, hz])
  have hxb : ρb x.2 ≠ 0 := by
    intro hz
    exact hx (by simp [prodPMF_apply, hz])
  obtain ⟨y0, hy0, hxy0⟩ := h0 x.1 hxa
  obtain ⟨y1, hy1, hxy1⟩ := h1 x.2 hxb
  refine ⟨(y0, y1), ?_, Or.inl ⟨hxy0, hxy1⟩⟩
  simpa [prodPMF_apply] using mul_ne_zero hy0 hy1

lemma matchingSupport_map {A B X Y : Type}
    {ρs : PMF A} {ρt : PMF B} {R : A → B → Prop}
    (fs : A → X) (ft : B → Y) (Q : X → Y → Prop)
    (hmap : ∀ a b, R a b → Q (fs a) (ft b))
    (h : HasMatchingSupport ρs ρt R) :
    HasMatchingSupport (ρs.map fs) (ρt.map ft) Q := by
  intro x hx
  have hpre : ∃ a, ρs a ≠ 0 ∧ x = fs a := by
    by_contra hn
    have hall : ∀ a, (if x = fs a then ρs a else 0) = 0 := by
      intro a
      by_cases heq : x = fs a
      · have ha : ρs a = 0 := by
          by_contra ha
          exact hn ⟨a, ha, heq⟩
        simp [heq, ha]
      · simp [heq]
    rw [PMF.map_apply, ENNReal.tsum_eq_zero.mpr hall] at hx
    exact hx rfl
  obtain ⟨a, ha, hxa⟩ := hpre
  obtain ⟨b, hb, hab⟩ := h a ha
  refine ⟨ft b, ?_, ?_⟩
  · rw [PMF.map_apply]
    have hterm : (if ft b = ft b then ρt b else 0) ≠ 0 := by
      simpa using hb
    have hle : (if ft b = ft b then ρt b else 0) ≤
        ∑' a, if ft b = ft a then ρt a else 0 := ENNReal.le_tsum b
    intro hz
    exact hterm (le_antisymm (hle.trans (le_of_eq hz)) zero_le)
  · rw [hxa]
    exact hmap a b hab

lemma matchingSupport_bind {A B X Y : Type}
    (wa : PMF A) (fa : A → PMF X) (wb : PMF B) (fb : B → PMF Y)
    (R : X → Y → Prop)
    (hchoice : ∀ a, wa a ≠ 0 →
      ∃ b, wb b ≠ 0 ∧ HasMatchingSupport (fa a) (fb b) R) :
    HasMatchingSupport (wa.bind fa) (wb.bind fb) R := by
  intro x hx
  have hpre : ∃ a, wa a ≠ 0 ∧ fa a x ≠ 0 := by
    by_contra hn
    have hall : ∀ a, wa a * fa a x = 0 := by
      intro a
      by_cases ha : wa a = 0
      · simp [ha]
      · have hfax : fa a x = 0 := by
          by_contra hfax
          exact hn ⟨a, ha, hfax⟩
        simp [hfax]
    rw [PMF.bind_apply, ENNReal.tsum_eq_zero.mpr hall] at hx
    exact hx rfl
  obtain ⟨a, ha, hax⟩ := hpre
  obtain ⟨b, hb, hab⟩ := hchoice a ha
  obtain ⟨y, hy, hxy⟩ := hab x hax
  refine ⟨y, ?_, hxy⟩
  rw [PMF.bind_apply]
  have hterm : wb b * fb b y ≠ 0 := mul_ne_zero hb hy
  intro hz
  exact hterm (le_antisymm (hz ▸ ENNReal.le_tsum b) zero_le)

lemma matchingSupport_mono_target {X : Type} {ρs ρm ρt : PMF X}
    {R : X → X → Prop} {p : ℝ≥0∞} (hp : p ≠ 0)
    (hminor : ∀ y, p * ρm y ≤ ρt y)
    (h : HasMatchingSupport ρs ρm R) :
    HasMatchingSupport ρs ρt R := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := h x hx
  refine ⟨y, ?_, hxy⟩
  have hprod : p * ρm y ≠ 0 := mul_ne_zero hp hy
  intro hzero
  exact hprod (le_antisymm ((hminor y).trans (le_of_eq hzero)) zero_le)

lemma matchingSupport_branch {S : Type} {h : ℕ}
    {ρs ρt : PMF (FullLab S h × FullLab S h)}
    {R0 : S → S → Prop} {s t : S} (hst : R0 s t)
    (hchild : HasMatchingSupport ρs ρt (SquareRel (fullSim R0 h))) :
    HasMatchingSupport (ρs.map (branch s)) (ρt.map (branch t))
      (fullSim R0 (h + 1)) := by
  apply matchingSupport_map (branch s) (branch t) _ _ hchild
  intro x y hxy
  exact (fullSim_branch R0 h s t x y).mpr ⟨hst, hxy⟩

lemma matchingSupport_pure {X Y : Type} {x : X} {y : Y}
    {R : X → Y → Prop} (hxy : R x y) :
    HasMatchingSupport (PMF.pure x) (PMF.pure y) R := by
  intro z hz
  have hzx : z = x := by
    by_contra hne
    exact hz (by simp [PMF.pure_apply, hne])
  subst z
  exact ⟨y, by simp, hxy⟩

/-- If one member of a zero list supports every charged source atom, the
screen is exactly zero, independently of its normalization. -/
lemma screenE_eq_zero_of_matching_mem {X : Type}
    {rhoS rho0 : PMF X} {R : X → X → Prop}
    (hsupp : HasMatchingSupport rhoS rho0 R)
    (zs : List (PMF X)) (hmem : rho0 ∈ zs) (W : X → ℝ≥0∞) :
    screenE rhoS R zs W = 0 := by
  rw [screenE]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  by_cases hx : rhoS x = 0
  · simp [hx]
  · have hr : rE rho0 R x ≠ 0 := hsupp.rE_ne_zero hx
    have hi : screenInd R zs x = 0 := by
      rw [screenInd, if_neg]
      intro hall
      exact hr (hall rho0 hmem)
    simp [hi]

end GraphMarkovMatching
