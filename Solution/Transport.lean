/- Proofs identifying the concise challenge vocabulary with the library representations. -/
import Solution.Infrastructure
import GraphMarkovMatching.Stopped.Projection

open scoped ENNReal Classical
open MeasureTheory Challenge

namespace Solution.Transport

lemma potential_eq_iid {V : Type*} (μ : PMF V) (R : V → V → Prop)
    (hrefl : ∀ v, R v v) : potential (5 / 2) μ R = Infrastructure.PhiIid μ R := by
  unfold potential Infrastructure.PhiIid
  apply tsum_congr
  intro v
  by_cases hv : μ v = 0
  · simp [hv]
  · have hq : q μ R v < 1 := GraphMatching.q_lt_one (hrefl v) hv
    rw [phiE, ite_eq_left hq]

lemma potential_eq_graph {V : Type*} (μ : PMF V) (G : SimpleGraph V) :
    potential (5 / 2) μ (compat G) = Infrastructure.etaGraph μ G := by
  rw [potential_eq_iid μ _ (fun _ => Or.inl rfl)]
  exact (GraphMatching.etaG_eq_Phi μ G).symm

lemma wordGraph_adj {A : Type*} (T : List A → Prop) (u v : {w // T w}) :
    (wordGraph T).Adj u v ↔ (∃ a, v.1 = u.1 ++ [a]) ∨ (∃ a, u.1 = v.1 ++ [a]) := by
  change (u ≠ v ∧ _) ↔ _
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
      have := congrArg List.length ha <;> simp at this

private lemma treeDistN_one {N : ℕ} {u v : GWWord N} :
    BranchingProcess.treeDist u v = 1 ↔
      (∃ a, v = u ++ [a]) ∨ (∃ a, u = v ++ [a]) := by
  open BranchingProcess in
    constructor
    · intro h
      have h1 := treeDist_add u v
      have h2 := wedge_length_le_left u v
      have h3 := wedge_length_le_right u v
      rcases Nat.lt_or_ge (wedge u v).length u.length with hlt | hge
      · have hv : wedge u v = v := (wedge_prefix_right u v).eq_of_length (by omega)
        obtain ⟨s, hs⟩ : v <+: u := hv ▸ wedge_prefix_left u v
        have hlen : s.length = 1 := by
          have := congrArg List.length hs
          simp only [List.length_append] at this
          omega
        obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
        exact Or.inr ⟨a, hs.symm⟩
      · have hu : wedge u v = u := (wedge_prefix_left u v).eq_of_length (by omega)
        obtain ⟨s, hs⟩ : u <+: v := hu ▸ wedge_prefix_right u v
        have hlen : s.length = 1 := by
          have := congrArg List.length hs
          simp only [List.length_append] at this
          omega
        obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
        exact Or.inl ⟨a, hs.symm⟩
    · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
      · exact treeDist_append_singleton u a
      · rw [treeDist_comm]; exact treeDist_append_singleton v a

lemma wordGraph_eq_N {N : ℕ} (T : GWWord N → Prop) :
    wordGraph T = ChainClasses.wordGraphN T := by
  ext u v
  rw [wordGraph_adj, ChainClasses.wordGraphN_adj]
  exact treeDistN_one.symm

lemma wordGraph_eq_bool (T : Word → Prop) : wordGraph T = ChainClasses.wordGraph T := by
  ext u v
  rw [wordGraph_adj]
  exact ChainClasses.treeDist_eq_one_iff.symm

lemma sampleGraph_eq {N : ℕ} (c : GWWord N → ℕ) :
    wordGraph (inGWSample c) = Infrastructure.gwTreeGraph c := by
  rw [Infrastructure.gwTreeGraph_eq, wordGraph_eq_N]
  rfl

lemma twovalue_qi {χ χ' : Word → Bool} {K : ℕ} {f : Word → Word}
    (hf : Infrastructure.IsQIWith K (InTree χ) (InTree χ') f) (hroot : f [] = []) :
    ∃ g : {w // InTree χ w} → {w // InTree χ' w},
      GraphQIWith K (wordGraph (InTree χ)) (wordGraph (InTree χ')) g ∧
        g ⟨[], InTree.root⟩ = ⟨[], InTree.root⟩ := by
  have h : ChainClasses.IsQIWith K (InTree χ) (InTree χ') f :=
    (Infrastructure.isQIWith_iff _ _ _ _).1 hf
  have hT : ChainClasses.PrefixClosed (InTree χ) := by
    rw [Infrastructure.inTree_eq]
    exact ChainClasses.prefixClosed_inTree χ
  have hT' : ChainClasses.PrefixClosed (InTree χ') := by
    rw [Infrastructure.inTree_eq]
    exact ChainClasses.prefixClosed_inTree χ'
  refine ⟨ChainClasses.restrictQI h, ?_, ?_⟩
  · rw [wordGraph_eq_bool, wordGraph_eq_bool, Infrastructure.graphQIWith_iff]
    exact ChainClasses.isQIWith_wordGraph hT hT' h
  · exact Subtype.ext hroot

end Solution.Transport

namespace Challenge.Stopped.Model

/-- The typed implementation model. Types will be forgotten by `erase`. -/
def toOld {V I : Type} (M : Model V I) : Solution.Infrastructure.Stopped.Model V I :=
  ⟨M.R, M.zero, M.μ, M.fresh, M.π⟩

lemma toOld_compat {V I : Type} (M : Model V I) (hc : M.IsCompat) : M.toOld.IsCompat :=
  ⟨hc.refl, hc.symm⟩

def Phase.toOld {V I : Type} {M : Model V I} {g : ℕ} (Θ : Phase M g) :
    Solution.Infrastructure.Stopped.Model.Phase M.toOld g :=
  ⟨Θ.θ, Θ.fresh_zero, Θ.child⟩

lemma toOld_zeta {V I : Type} (M : Model V I) (α : ℝ) :
    M.toOld.zeta α = M.zeta α := rfl

lemma reach_toOld {V I : Type} (M : Model V I) (t : I) : ∀ n,
    M.toOld.reach {t} n = M.reach t n
  | 0 => rfl
  | n + 1 => by
      change {u | ∃ s ∈ M.toOld.reach {t} n, M.toOld.child s u} = _
      rw [reach_toOld M t n]
      rfl

lemma returns_toOld {V I : Type} (M : Model V I) {g : ℕ} (Θ : Phase M g) (H : ℕ)
    (h : M.CommonReturns Θ H) : M.toOld.CommonReturns Θ.toOld H := by
  intro s t hst p hp hpath
  obtain ⟨n, hn, hf, u, hu, hfu⟩ := h s t hst p hp hpath
  exact ⟨n, hn, hf, u, (reach_toOld M t n).symm ▸ hu, hfu⟩

end Challenge.Stopped.Model

namespace Solution.Transport

lemma lambda_eq (α : ℝ) : Challenge.Stopped.lambda α = Infrastructure.Stopped.lambda α := rfl

def erase {V I : Type} : (h : ℕ) → FullLab (I × V) h → FullLab V h
  | 0, x => x.2
  | h + 1, x => (x.1.2, erase h x.2.1, erase h x.2.2)

def autRestricted : (h : ℕ) → Aut h ≃ Infrastructure.AutK 1 0 h
  | 0 => Equiv.refl _
  | h + 1 => Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (autRestricted h) (autRestricted h))

lemma matches_erase {V I : Type} (R : V → V → Prop) :
    ∀ (h : ℕ) (π : Aut h) (x y : FullLab (I × V) h),
      fullMatchesA R h π (erase h x) (erase h y) ↔
        Infrastructure.fullMatchesK (fun a b => R a.2 b.2) 1 0 h (autRestricted h π) x y := by
  intro h
  induction h with
  | zero => exact fun _ _ _ => Iff.rfl
  | succ h ih =>
    rintro ⟨b, p, q⟩ x y
    cases b
    · exact and_congr Iff.rfl (and_congr (ih p x.2.1 y.2.1) (ih q x.2.2 y.2.2))
    · exact and_congr Iff.rfl (and_congr (ih p x.2.1 y.2.2) (ih q x.2.2 y.2.1))

lemma sim_erase {V I : Type} (R : V → V → Prop) (h : ℕ) (x y : FullLab (I × V) h) :
    fullSim R h (erase h x) (erase h y) ↔
      Infrastructure.fullSim (fun a b => R a.2 b.2) h x y := by
  constructor
  · rintro ⟨π, hp⟩
    exact ⟨autRestricted h π, (matches_erase R h π x y).1 hp⟩
  · rintro ⟨π, hp⟩
    refine ⟨(autRestricted h).symm π, (matches_erase R h _ x y).2 ?_⟩
    simpa only [Equiv.apply_symm_apply] using hp

set_option backward.isDefEq.respectTransparency false in
lemma old_rho_succ {V I : Type} (M : Challenge.Stopped.Model V I) (t : I) (h : ℕ) :
    M.toOld.rho t (h + 1) = (M.rootLaw t).bind fun v =>
      ((M.π t).bind fun j => prodPMF (M.toOld.rho j.1 h) (M.toOld.rho j.2 h)).map
        fun p => ((t, v), p) := by
  unfold Infrastructure.Stopped.Model.rho Infrastructure.Stopped.Model.rootT
  rw [PMF.bind_map]
  simp only [Infrastructure.muM]
  change (M.rootLaw t).bind _ = _
  congr 1
  funext v
  dsimp only [Function.comp_apply, Infrastructure.Stopped.Model.kernel]
  apply congrArg (PMF.map (fun p : FullLab (I × V) h × FullLab (I × V) h => ((t, v), p)))
  rw [PMF.bind_bind]
  apply congrArg (PMF.bind (M.π t))
  funext j
  simp only [Infrastructure.prodPMF_eq]
  exact GraphMarkovMatching.prodPMF_bind_prodPMF (M.toOld.rootT j.1) (M.toOld.rootT j.2)
    (fun s => Infrastructure.muM M.toOld.kernel s h)
    (fun s => Infrastructure.muM M.toOld.kernel s h)

set_option backward.isDefEq.respectTransparency false in
lemma rho_erase {V I : Type} (M : Challenge.Stopped.Model V I) : ∀ h t,
    (M.toOld.rho t h).map (erase h) = M.rho t h := by
  intro h
  induction h with
  | zero =>
    intro t
    simp only [Infrastructure.Stopped.Model.rho, Infrastructure.muM, Infrastructure.leaf,
      PMF.bind_pure, Infrastructure.Stopped.Model.rootT, PMF.map_comp, FullLab]
    change (M.rootLaw t).map id = M.rootLaw t
    exact PMF.map_id _
  | succ h ih =>
    intro t
    rw [old_rho_succ, PMF.map_bind, Challenge.Stopped.Model.rho]
    congr 1
    funext v
    rw [PMF.map_comp, PMF.map_bind]
    change (M.π t).bind (fun j => (prodPMF (M.toOld.rho j.1 h) (M.toOld.rho j.2 h)).map
      ((fun p => (v, p)) ∘ Prod.map (erase h) (erase h))) = _
    simp only [← PMF.map_comp, Infrastructure.map_prodPMF, ih, PMF.map_bind]

end Solution.Transport

namespace Solution.Transport

lemma degree_erase {V I : Type} (R : V → V → Prop) (h : ℕ)
    (μ : PMF (FullLab (I × V) h)) (x : FullLab (I × V) h) :
    rE (μ.map (erase h)) (fullSim R h) (erase h x) =
      rE μ (Infrastructure.fullSim (fun a b => R a.2 b.2) h) x := by
  change GraphMarkovMatching.Support.rE _ _ _ = GraphMarkovMatching.Support.rE _ _ _
  rw [GraphMarkovMatching.rE_map, GraphMarkovMatching.rE_eq_tsum_mul]
  apply tsum_congr
  intro y
  simp only [GraphMarkovMatching.goodInd, sim_erase]

lemma badDegree_erase {V I : Type} (R : V → V → Prop) (h : ℕ)
    (μ : PMF (FullLab (I × V) h)) (x : FullLab (I × V) h) :
    qE (μ.map (erase h)) (fullSim R h) (erase h x) =
      qE μ (Infrastructure.fullSim (fun a b => R a.2 b.2) h) x := by
  change GraphMarkovMatching.Support.qE _ _ _ = GraphMarkovMatching.Support.qE _ _ _
  rw [GraphMarkovMatching.qE_map, GraphMarkovMatching.qE_eq_tsum_mul]
  apply tsum_congr
  intro y
  simp only [GraphMarkovMatching.badInd, sim_erase]

lemma failProb_eq {V I : Type} (M : Challenge.Stopped.Model V I) (s t : I) (h : ℕ) :
    M.failProb s t h = M.toOld.failProb s t h := by
  unfold Challenge.Stopped.Model.failProb Infrastructure.Stopped.Model.failProb Infrastructure.failureD
  rw [← rho_erase M h s, GraphMarkovMatching.tsum_map_mul, ← rho_erase M h t]
  exact tsum_congr fun x => congrArg (fun q => M.toOld.rho s h x * q)
    (badDegree_erase M.R h (M.toOld.rho t h) x)

lemma freshPositive_toOld {V I : Type} (M : Challenge.Stopped.Model V I)
    (hp : M.FreshPositive) : M.toOld.FreshPositive := by
  intro h s t x hs ht hx
  have hx' : M.rho s h (erase h x) ≠ 0 := by
    rw [← rho_erase M h s]
    exact (PMF.mem_support_iff _ _).1 ((PMF.mem_support_map_iff _ _ _).2 ⟨x, hx, rfl⟩)
  have hd := hp h s t (erase h x) hs ht hx'
  rw [← rho_erase M h t, degree_erase] at hd
  exact hd

noncomputable def fullSelection {V I : Type} (M : Challenge.Stopped.Model V I) [Fintype I] :
    Infrastructure.Stopped.Model.Selection M.toOld where
  J t := Finset.univ.filter fun j => M.π t j ≠ 0
  nonempty t := by
    obtain ⟨j, hj⟩ := (M.π t).support_nonempty
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  charged _ _ hj := (Finset.mem_filter.mp hj).2
  positive t h p _ _ hr := by
    unfold Infrastructure.Stopped.Model.childMix at hr
    change GraphMarkovMatching.Support.rE ((M.π t).bind _) _ p ≠ 0 at hr
    rw [Ne, GraphMarkovMatching.rE_bind_eq_zero_iff] at hr
    push Not at hr
    obtain ⟨j, hj, hj'⟩ := hr
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hj'⟩

lemma fullSelection_sum {V I : Type} (M : Challenge.Stopped.Model V I) [Fintype I]
    (α : ℝ) (t : I) : (fullSelection M).inverseSum α t = M.inverseSum α t := rfl

end Solution.Transport

namespace Solution.Transport

lemma restrict_erase {V I : Type} : ∀ h (x : FullLab (I × V) (h + 1)),
    restrictLab h (erase (h + 1) x) = erase h (restrictLab h x)
  | 0, _ => rfl
  | h + 1, x => by
      change (_, restrictLab h (erase (h + 1) x.2.1), restrictLab h (erase (h + 1) x.2.2)) = _
      rw [restrict_erase h x.2.1, restrict_erase h x.2.2]
      rfl

lemma coord_erase {V I : Type} : ∀ h (x : FullLab (I × V) h) w,
    coord h (erase h x) w = (coord h x w).2
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | h + 1, x, false :: w => coord_erase h x.2.1 w
  | h + 1, x, true :: w => coord_erase h x.2.2 w

lemma measurable_erase {V I : Type} [MeasurableSpace V] [MeasurableSpace I] :
    ∀ h, Measurable (erase (V := V) (I := I) h)
  | 0 => measurable_snd
  | h + 1 =>
      (measurable_snd.comp measurable_fst).prodMk
        (((measurable_erase h).comp (measurable_fst.comp measurable_snd)).prodMk
          ((measurable_erase h).comp (measurable_snd.comp measurable_snd)))

/-- Internal notation for transporting a process and its matching event. -/
def MatchingProcess {S : Type} [MeasurableSpace S] (R : S → S → Prop)
    (μ ν : (h : ℕ) → PMF (FullLab S h)) (b : ℝ≥0∞) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (X Y : (h : ℕ) → Ω → FullLab S h),
    (∀ h ω, restrictLab h (X (h + 1) ω) = X h ω) ∧
    (∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω) ∧
    (∀ h, Measurable (fun ω => (X h ω, Y h ω))) ∧
    (∀ h, P.map (fun ω => (X h ω, Y h ω)) = (prodPMF (μ h) (ν h)).toMeasure) ∧
    b ≤ P {ω | ∃ aut : List Bool ≃ List Bool, IsTreeAut aut ∧
      ∀ w, R (coord (aut w).length (X (aut w).length ω) (aut w))
        (coord w.length (Y w.length ω) w)}

lemma matchingProcess_erase {V I : Type} [MeasurableSpace V] [MeasurableSpace I]
    (M : Challenge.Stopped.Model V I) (s t : I) (b : ℝ≥0∞)
    (h : MatchingProcess M.toOld.srel (M.toOld.rho s) (M.toOld.rho t) b) :
    MatchingProcess M.R (M.rho s) (M.rho t) b := by
  obtain ⟨Ω, inst, P, instP, X, Y, hX, hY, hmeas, hlaw, hbound⟩ := h
  let := inst
  let := instP
  refine ⟨Ω, inst, P, instP, fun n ω => erase n (X n ω), fun n ω => erase n (Y n ω),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro n ω
    rw [restrict_erase, hX]
  · intro n ω
    rw [restrict_erase, hY]
  · intro n
    exact ((measurable_erase n).comp measurable_fst).prodMk
      ((measurable_erase n).comp measurable_snd) |>.comp (hmeas n)
  · intro n
    have hm : Measurable (Prod.map (erase (V := V) (I := I) n) (erase (V := V) (I := I) n)) :=
      ((measurable_erase n).comp measurable_fst).prodMk ((measurable_erase n).comp measurable_snd)
    change P.map (Prod.map (erase n) (erase n) ∘ (fun ω => (X n ω, Y n ω))) = _
    rw [← Measure.map_map hm (hmeas n), hlaw, PMF.toMeasure_map _ _ hm,
      Infrastructure.map_prodPMF, rho_erase, rho_erase]
  · refine hbound.trans (measure_mono ?_)
    rintro ω ⟨aut, haut, hw⟩
    refine ⟨aut, haut, fun w => ?_⟩
    simpa only [coord_erase, Infrastructure.Stopped.Model.srel,
      Challenge.Stopped.Model.toOld] using hw w

end Solution.Transport
