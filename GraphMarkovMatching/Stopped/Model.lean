/-
The Markov label models of `markov_matching_new_proof.tex` (`sec:markov-proof`):
a countable state space `V` with a compatibility relation `R`, a distinguished
state `zero`, and a state law `μ`; a countable type set `I` with the fresh
types and the child-type kernel `π`.  A vertex of a fresh type carries a state
drawn from `μ`, a vertex of a forced type carries the state `zero`; independently
the child-type pair is drawn from the kernel, and the two subtrees are
conditionally independent.

The process is realised on typed labellings `FullLab (I × V) h`: every vertex
records its type together with its state.  Matching compares states only
(`srel`), so the typed labellings are a harmless enrichment of the state
labellings `ρ_{t,h}` of the note, and the existing tree law `muM` of
`Process/Basic` supplies the recursion, the marginal consistency, and the
König/trajectory endpoints.

* `Model`, `rootLaw`, `rootT`, `kernel`, `rho`, `childMix`, `sim`, `deg`:
  the process and its matching degrees `r_{t,h}(x) = ρ_{t,h}{y : x ≈_h y}`;
* `rho_zero`, `rho_succ`, `pairMix_kernel`, `rho_map_restrictLab`: the
  recursion of the laws and the marginal consistency;
* `rho_zero_apply`, `rho_succ_apply`, `branch_inj`, `rho_zero_ne_zero_iff`,
  `rho_succ_ne_zero_iff`: the point masses and the support of the laws;
* `deg_zero`, `deg_succ`, `rE_childMix`: the root factor `c_t(v)` times the
  child-pair degree, and the mixture over target transitions;
* `Vmu`, `StatesIn`, `statesIn_of_rho_ne_zero`: every realised state lies
  in `V_μ = supp μ ∪ {0}`.

The one-site quantities are in `Constants.lean`; the restricted potentials, the
zero events, the phases, the paths and the selections in `Paths.lean`.
-/
import GraphMarkovMatching.Potential.Restricted
import GraphMarkovMatching.Process.Recursion
import GraphMarkovMatching.Potential.Degrees
import GraphMarkovMatching.Process.Consistency

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

/-! ### The model -/

/-- A Markov label model (`sec:markov-proof`): states with a compatibility relation and a
distinguished state, a fresh state law, and types with a fresh subset and a child-type
kernel. -/
structure Model (V I : Type) where
  /-- compatibility of states, `v ∼ w` -/
  R : V → V → Prop
  /-- the distinguished state `0` -/
  zero : V
  /-- the fresh state law -/
  μ : PMF V
  /-- the fresh types -/
  fresh : I → Prop
  /-- the kernel on ordered child-type pairs -/
  π : I → PMF (I × I)

namespace Model

variable {V I : Type} (M : Model V I)

/-- Reflexivity and symmetry of the compatibility relation. -/
structure IsCompat (M : Model V I) : Prop where
  refl : ∀ v, M.R v v
  symm : ∀ v w, M.R v w → M.R w v

/-- The state-only relation on typed states. -/
def srel : I × V → I × V → Prop := fun a b => M.R a.2 b.2

lemma srel_symm (hc : M.IsCompat) : ∀ a b, M.srel a b → M.srel b a :=
  fun _ _ h => hc.symm _ _ h

lemma srel_refl (hc : M.IsCompat) : ∀ a, M.srel a a := fun a => hc.refl a.2

/-- The root state law of a type: `μ` at a fresh type, the point mass at `0` otherwise. -/
noncomputable def rootLaw (t : I) : PMF V :=
  if M.fresh t then M.μ else PMF.pure M.zero

/-- The typed root law. -/
noncomputable def rootT (t : I) : PMF (I × V) :=
  (M.rootLaw t).map fun v => (t, v)

/-- The child kernel on typed states: draw the child-type pair from `π`, then independent
root states. -/
noncomputable def kernel : I × V → PMF ((I × V) × (I × V)) := fun s =>
  (M.π s.1).bind fun j => prodPMF (M.rootT j.1) (M.rootT j.2)

/-- The height-`h` law `ρ_{t,h}` of the labelling of type `t`, as a typed labelling. -/
noncomputable def rho (t : I) (h : ℕ) : PMF (FullLab (I × V) h) :=
  (M.rootT t).bind fun s => muM M.kernel s h

/-- The child-pair mixture of type `t` at height `h`: the law of the two subtrees below a
vertex of type `t`. -/
noncomputable def childMix (t : I) (h : ℕ) :
    PMF (FullLab (I × V) h × FullLab (I × V) h) :=
  (M.π t).bind fun j => prodPMF (M.rho j.1 h) (M.rho j.2 h)

/-- Matching at height `h`: state compatibility at every vertex under some rooted
automorphism, `x ≈_h y`. -/
abbrev sim (h : ℕ) : FullLab (I × V) h → FullLab (I × V) h → Prop :=
  fullSim M.srel h

/-- The matching degree `r_{t,h}(x) = ρ_{t,h}{y : x ≈_h y}`. -/
noncomputable def deg (t : I) (h : ℕ) (x : FullLab (I × V) h) : ℝ≥0∞ :=
  rE (M.rho t h) (M.sim h) x

/-- The root factor `c_t(v) = rootLaw t {w : v ∼ w}`: the compatible root mass of a
target of type `t` against a source root state `v`. -/
noncomputable def rootDeg (t : I) (v : V) : ℝ≥0∞ := rE (M.rootLaw t) M.R v

/-! ### The recursion of the laws -/

lemma rootLaw_fresh {t : I} (ht : M.fresh t) : M.rootLaw t = M.μ := if_pos ht

lemma rootLaw_forced {t : I} (ht : ¬ M.fresh t) : M.rootLaw t = PMF.pure M.zero := if_neg ht

lemma rootT_apply (t : I) (s : I × V) :
    M.rootT t s = if s.1 = t then M.rootLaw t s.2 else 0 := by
  rw [rootT, PMF.map_apply]
  by_cases hs : s.1 = t
  · rw [if_pos hs]
    refine (tsum_congr fun v => ?_).trans (tsum_ite_eq s.2 (M.rootLaw t))
    congr 1
    apply propext
    constructor
    · intro h; rw [h]
    · intro h; rw [h, ← hs]
  · rw [if_neg hs]
    refine ENNReal.tsum_eq_zero.mpr fun v => ?_
    rw [if_neg]
    intro h
    exact hs (by rw [h])

lemma rho_zero (t : I) : M.rho t 0 = (M.rootT t).map leaf := by
  rw [rho, ← PMF.bind_pure_comp]
  rfl

/-- The pair mixture of the kernel does not depend on the root state. -/
lemma pairMix_kernel (t : I) (v : V) (h : ℕ) :
    pairMix M.kernel (t, v) h = M.childMix t h := by
  rw [pairMix, childMix]
  show ((M.π t).bind fun j => prodPMF (M.rootT j.1) (M.rootT j.2)).bind _ = _
  rw [PMF.bind_bind]
  refine congrArg _ (funext fun j => ?_)
  simp only [rho]
  exact prodPMF_bind_prodPMF (M.rootT j.1) (M.rootT j.2)
    (fun s => muM M.kernel s h) (fun s => muM M.kernel s h)

/-- **The recursion of the laws**: a height-`(h+1)` sample is an independent root state
attached to a child-pair sample. -/
lemma rho_succ (t : I) (h : ℕ) :
    M.rho t (h + 1) = (M.rootT t).bind fun s => (M.childMix t h).map (branch s) := by
  rw [rho, rootT, PMF.bind_map, PMF.bind_map]
  refine congrArg _ (funext fun v => ?_)
  show muM M.kernel (t, v) (h + 1) = (M.childMix t h).map (branch (t, v))
  rw [muM_succ, pairMix_kernel]

/-- **Marginal consistency**: restricting a height-`(h+1)` sample to height `h` recovers
the height-`h` law. -/
lemma rho_map_restrictLab (t : I) (h : ℕ) :
    (M.rho t (h + 1)).map (restrictLab h) = M.rho t h :=
  mix_map_restrictLab M.kernel (M.rootT t) h

/-- The pair law of the leaf-attached root law: `ρ_{t,0}` is the pushforward of the typed
root law. -/
lemma rho_zero_apply (t : I) (s : I × V) :
    M.rho t 0 (leaf s) = M.rootT t s := by
  rw [rho_zero, PMF.map_apply]
  rw [show (fun a => if leaf s = leaf a then M.rootT t a else 0)
      = fun a => if a = s then M.rootT t a else 0 from
    funext fun a => by
      congr 1
      apply propext
      exact ⟨fun h => (congrArg id h).symm, fun h => congrArg leaf h.symm⟩]
  exact tsum_ite_eq s (M.rootT t)

/-- The root of a charged sample carries the type and a charged root state. -/
lemma rootLab_of_rho_ne_zero {t : I} {h : ℕ} {x : FullLab (I × V) h}
    (hx : M.rho t h x ≠ 0) :
    (rootLab h x).1 = t ∧ M.rootLaw t (rootLab h x).2 ≠ 0 := by
  rw [rho, PMF.bind_apply, Ne, ENNReal.tsum_eq_zero] at hx
  push Not at hx
  obtain ⟨s, hs⟩ := hx
  have h1 : M.rootT t s ≠ 0 := left_ne_zero_of_mul hs
  have h2 : muM M.kernel s h x ≠ 0 := right_ne_zero_of_mul hs
  rw [rootLab_of_ne_zero M.kernel h s x h2, rootT_apply] at *
  by_cases hst : s.1 = t
  · rw [if_pos hst] at h1
    exact ⟨hst, h1⟩
  · rw [if_neg hst] at h1
    exact absurd rfl h1

/-! ### The support of the laws -/

lemma rho_zero_ne_zero_iff (t : I) (s : I × V) :
    M.rho t 0 (leaf s) ≠ 0 ↔ s.1 = t ∧ M.rootLaw t s.2 ≠ 0 := by
  rw [rho_zero_apply, rootT_apply]
  by_cases hst : s.1 = t
  · rw [if_pos hst]
    exact ⟨fun h => ⟨hst, h⟩, fun h => h.2⟩
  · rw [if_neg hst]
    exact ⟨fun h => absurd rfl h, fun h => absurd h.1 hst⟩

/-- Attaching a root is injective in both arguments (`sec:markov-proof`). -/
lemma branch_inj {S : Type} {n : ℕ} {s s' : S} {p p' : FullLab S n × FullLab S n} :
    branch s p = branch s' p' ↔ s = s' ∧ p = p' := by
  constructor
  · intro h
    have h1 : (branch s p).1 = (branch s' p').1 := congrArg Prod.fst h
    have h2 : (branch s p).2 = (branch s' p').2 := congrArg Prod.snd h
    exact ⟨h1, Prod.ext (congrArg Prod.fst h2) (congrArg Prod.snd h2)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The mass of a branch: the typed root mass times the child-pair mass
(`sec:markov-proof`). -/
lemma rho_succ_apply (t : I) (h : ℕ) (s : I × V)
    (p : FullLab (I × V) h × FullLab (I × V) h) :
    M.rho t (h + 1) (branch s p) = M.rootT t s * M.childMix t h p := by
  rw [rho_succ, PMF.bind_apply, tsum_eq_single s]
  · congr 1
    rw [PMF.map_apply]
    refine (tsum_congr fun p' => ?_).trans (tsum_ite_eq p (M.childMix t h))
    congr 1
    apply propext
    exact ⟨fun hc => (branch_inj.mp hc).2.symm, fun hc => by rw [hc]⟩
  · intro s' hs'
    rw [PMF.map_apply]
    refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr fun p' => ?_)
    rw [if_neg]
    intro hc
    exact hs' (branch_inj.mp hc).1.symm

/-- **The support recursion**: a branch is charged exactly when its root is a charged
typed root state and some charged transition charges both subtrees. -/
lemma rho_succ_ne_zero_iff (t : I) (h : ℕ) (s : I × V)
    (p : FullLab (I × V) h × FullLab (I × V) h) :
    M.rho t (h + 1) (branch s p) ≠ 0
      ↔ s.1 = t ∧ M.rootLaw t s.2 ≠ 0
        ∧ ∃ j, M.π t j ≠ 0 ∧ M.rho j.1 h p.1 ≠ 0 ∧ M.rho j.2 h p.2 ≠ 0 := by
  have hsum : (∑' a, M.π t a * prodPMF (M.rho a.1 h) (M.rho a.2 h) p) ≠ 0
      ↔ ∃ j, M.π t j ≠ 0 ∧ M.rho j.1 h p.1 ≠ 0 ∧ M.rho j.2 h p.2 ≠ 0 := by
    rw [Ne, ENNReal.tsum_eq_zero]
    push Not
    refine exists_congr fun j => ?_
    rw [prodPMF_apply, mul_ne_zero_iff, mul_ne_zero_iff]
  rw [rho_succ_apply, mul_ne_zero_iff, rootT_apply, childMix, PMF.bind_apply, hsum]
  by_cases hst : s.1 = t
  · rw [if_pos hst]
    exact ⟨fun h => ⟨hst, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
  · rw [if_neg hst]
    exact ⟨fun h => absurd rfl h.1, fun h => absurd h.1 hst⟩

/-- Every height-`(h+1)` labelling is a branch. -/
lemma eq_branch {h : ℕ} (x : FullLab (I × V) (h + 1)) :
    x = branch x.1 (x.2.1, x.2.2) := rfl

/-! ### The degrees -/

lemma rootDeg_fresh {t : I} (ht : M.fresh t) (v : V) : M.rootDeg t v = rE M.μ M.R v := by
  rw [rootDeg, rootLaw_fresh M ht]

lemma rootDeg_forced {t : I} (ht : ¬ M.fresh t) (v : V) :
    M.rootDeg t v = if M.R v M.zero then 1 else 0 := by
  rw [rootDeg, rootLaw_forced M ht, rE_pure]

lemma rootDeg_le_one (t : I) (v : V) : M.rootDeg t v ≤ 1 := rE_le_one

/-- The height-zero degree is the root factor. -/
lemma deg_zero (u : I) (s : I × V) : M.deg u 0 (leaf s) = M.rootDeg u s.2 := by
  rw [deg, rho_zero, rE_map, rootT, tsum_map_mul, rootDeg, rE_eq_tsum_mul]
  refine tsum_congr fun v => ?_
  congr 1
  simp only [goodInd]
  by_cases hR : M.R s.2 v
  · rw [if_pos hR, if_pos ((fullSim_leaf M.srel s (u, v)).mpr hR)]
  · rw [if_neg hR, if_neg (fun hc => hR ((fullSim_leaf M.srel s (u, v)).mp hc))]

/-- **The degree recursion** (`sec:root-contributions`): the degree of a branch against a
type is the root factor at the source root state times the degree of the child pair
against the target's child-pair mixture under straight-or-crossed matching. -/
lemma deg_succ (u : I) (h : ℕ) (s : I × V) (p : FullLab (I × V) h × FullLab (I × V) h) :
    M.deg u (h + 1) (branch s p)
      = M.rootDeg u s.2 * rE (M.childMix u h) (SquareRel (M.sim h)) p := by
  rw [deg, rho, rE_bind, rootT, tsum_map_mul, rootDeg, rE_eq_tsum_mul,
    ← ENNReal.tsum_mul_right]
  refine tsum_congr fun v => ?_
  rw [rE_succ_branch, pairMix_kernel, goodInd]
  by_cases hR : M.srel s (u, v)
  · rw [if_pos hR, if_pos (show M.R s.2 v from hR), mul_one]
  · rw [if_neg hR, if_neg (show ¬ M.R s.2 v from hR), mul_zero, zero_mul]

/-- The child-pair degree is the mixture over the target transitions of the component pair
degrees. -/
lemma rE_childMix (u : I) (h : ℕ) (p : FullLab (I × V) h × FullLab (I × V) h) :
    rE (M.childMix u h) (SquareRel (M.sim h)) p
      = ∑' j, M.π u j * rE (prodPMF (M.rho j.1 h) (M.rho j.2 h)) (SquareRel (M.sim h)) p :=
  rE_bind _ _ _ _

/-! ### Realised states -/

/-- The realised states `V_μ = supp μ ∪ {0}`. -/
def Vmu : Set V := {v | M.μ v ≠ 0} ∪ {M.zero}

/-- All states of a typed labelling lie in `A`. -/
def StatesIn (A : Set V) : (h : ℕ) → FullLab (I × V) h → Prop
  | 0, x => x.2 ∈ A
  | _ + 1, x => x.1.2 ∈ A ∧ StatesIn A _ x.2.1 ∧ StatesIn A _ x.2.2

lemma statesIn_zero (A : Set V) (x : FullLab (I × V) 0) : StatesIn A 0 x ↔ x.2 ∈ A := Iff.rfl

lemma statesIn_succ (A : Set V) (h : ℕ) (x : FullLab (I × V) (h + 1)) :
    StatesIn A (h + 1) x ↔ x.1.2 ∈ A ∧ StatesIn A h x.2.1 ∧ StatesIn A h x.2.2 := Iff.rfl

lemma rootLaw_mem_Vmu {t : I} {v : V} (hv : M.rootLaw t v ≠ 0) : v ∈ M.Vmu := by
  by_cases ht : M.fresh t
  · rw [rootLaw_fresh M ht] at hv
    exact Or.inl hv
  · rw [rootLaw_forced M ht, PMF.pure_apply] at hv
    by_cases hz : v = M.zero
    · exact Or.inr hz
    · rw [if_neg hz] at hv
      exact absurd rfl hv

/-- Every charged sample has all its states in `V_μ`. -/
lemma statesIn_of_rho_ne_zero (t : I) (h : ℕ) (x : FullLab (I × V) h)
    (hx : M.rho t h x ≠ 0) : StatesIn M.Vmu h x := by
  induction h generalizing t with
  | zero =>
      rw [statesIn_zero]
      exact M.rootLaw_mem_Vmu ((M.rho_zero_ne_zero_iff t x).mp hx).2
  | succ h ih =>
      rw [statesIn_succ]
      have hx' : M.rho t (h + 1) (branch x.1 (x.2.1, x.2.2)) ≠ 0 := hx
      rw [rho_succ_ne_zero_iff] at hx'
      obtain ⟨_, h1, j, _, hj1, hj2⟩ := hx'
      exact ⟨M.rootLaw_mem_Vmu h1, ih j.1 _ hj1, ih j.2 _ hj2⟩

/-- A realised state has positive fresh compatible mass (`sec:quantitative-stopping`): a
charged state matches itself by reflexivity, and `0` has positive compatible mass by
hypothesis. -/
private lemma rE_mu_ne_zero (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0) {v : V}
    (hv : v ∈ M.Vmu) : rE M.μ M.R v ≠ 0 := by
  rcases hv with hv | hv
  · intro h0
    have := le_rE_of_refl (μ := M.μ) (hc.refl v)
    rw [h0, nonpos_iff_eq_zero] at this
    exact hv this
  · rw [Set.mem_singleton_iff.mp hv]
    exact hb0

/-- A realised state compatible with `0` has positive root factor against every type
(`sec:unweighted`): a forced target contributes mass one, a fresh target its positive
compatible mass. -/
lemma rootDeg_ne_zero (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0) (t : I) {v : V}
    (hv : v ∈ M.Vmu) (hv0 : M.R v M.zero) : M.rootDeg t v ≠ 0 := by
  by_cases ht : M.fresh t
  · rw [rootDeg_fresh M ht]
    exact M.rE_mu_ne_zero hc hb0 hv
  · rw [rootDeg_forced M ht, if_pos hv0]
    exact one_ne_zero

/-- The root factor vanishes exactly at incompatible roots for forced targets, and a
fresh target has positive root factor at every realised state. -/
lemma rootDeg_fresh_ne_zero (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0) {t : I}
    (ht : M.fresh t) {v : V} (hv : v ∈ M.Vmu) : M.rootDeg t v ≠ 0 := by
  rw [rootDeg_fresh M ht]
  exact M.rE_mu_ne_zero hc hb0 hv

end Model

end GraphMarkovMatching.Stopped
