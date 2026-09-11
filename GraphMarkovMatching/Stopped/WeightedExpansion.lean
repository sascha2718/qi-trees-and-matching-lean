/-
The weighted stopped expansion of `markov_matching_new_proof.tex`
(`sec:one-weight`, `thm:explicit-weighted-bound`): one inverse-degree weight `W_{u,h}` is
carried through the stopped expansion of an impossible comparison.

* `wZero_succ_le`: the expansion step; the incompatible root contributes
  `2 B U(M)² f`, the split contributes `2 B R_μ (T Z + α M)²`, and the four continuing
  terms carry the factor `R_μ U(M)` times the selected inverse mixture of total
  coefficient at most `B`;
* `wZero_zero_le`: the height-zero terminal case, at most `f`;
* `wZero_le_of_stops`: the stopped expansion under `Stops`;
* `wZero_le_Efun` (`thm:explicit-weighted-bound`): under common returns within `H`,
  every equal-phase weighted zero integral at height `h` is at most `E(M)` of
  `eq:explicit-weighted-error`, given the potentials at heights below `h`.
-/
import GraphMarkovMatching.Stopped.ZeroExpansion

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

namespace Model

variable {V I : Type} (M : Model V I)

/-! ### Fubini identities for the child pair (`sec:one-weight`) -/

/-- A separated integrand against a product law integrates to the product of the two
marginal integrals (`sec:one-weight`, conditional independence of the children). -/
private lemma tsum_prodPMF_mul {X Y : Type} (ρ₁ : PMF X) (ρ₂ : PMF Y) (f : X → ℝ≥0∞)
    (g : Y → ℝ≥0∞) :
    ∑' p : X × Y, prodPMF ρ₁ ρ₂ p * (f p.1 * g p.2)
      = (∑' x, ρ₁ x * f x) * (∑' y, ρ₂ y * g y) := by
  rw [← tsum_prod_split (fun x => ρ₁ x * f x) (fun y => ρ₂ y * g y)]
  exact tsum_congr fun p => by rw [prodPMF_apply]; ring

/-- A finite selected sum commutes with the integral (`eq:selected-inverse-mixture`). -/
private lemma tsum_mul_finset_sum {X ι : Type} (ρ : X → ℝ≥0∞) (s : Finset ι)
    (c : ι → ℝ≥0∞) (f : ι → X → ℝ≥0∞) :
    ∑' p, ρ p * ∑ i ∈ s, c i * f i p = ∑ i ∈ s, c i * ∑' p, ρ p * f i p := by
  calc ∑' p, ρ p * ∑ i ∈ s, c i * f i p
      = ∑' p, ∑ i ∈ s, c i * (ρ p * f i p) := by
        refine tsum_congr fun p => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i ∈ s, ∑' p, c i * (ρ p * f i p) :=
        Summable.tsum_finsetSum fun i _ => ENNReal.summable
    _ = ∑ i ∈ s, c i * ∑' p, ρ p * f i p :=
        Finset.sum_congr rfl fun i _ => ENNReal.tsum_mul_left

/-- Two constants pulled out of an integral (`sec:one-weight`). -/
private lemma tsum_mul_const_add {X : Type} (ρ f g : X → ℝ≥0∞) (x y : ℝ≥0∞) :
    ∑' p, ρ p * (x * f p + y * g p) = x * ∑' p, ρ p * f p + y * ∑' p, ρ p * g p := by
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  exact tsum_congr fun p => by ring

/-- Two integrals pulled out of a root-state average (`sec:one-weight`). -/
private lemma tsum_mul_add_mul {X : Type} (ρ a c : X → ℝ≥0∞) (x y : ℝ≥0∞) :
    ∑' v, ρ v * (a v * x + c v * y) = (∑' v, ρ v * a v) * x + (∑' v, ρ v * c v) * y := by
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  exact tsum_congr fun v => by ring

/-- A constant and a scaled integrand averaged against a probability law
(`sec:one-weight`, the source transition is averaged with its original law). -/
private lemma tsum_pmf_mul_const_add {X : Type} (ρ : PMF X) (f : X → ℝ≥0∞) (x y : ℝ≥0∞) :
    ∑' p, ρ p * (x + y * f p) = x + y * ∑' p, ρ p * f p := by
  calc ∑' p, ρ p * (x + y * f p)
      = ∑' p, (ρ p * x + y * (ρ p * f p)) := tsum_congr fun p => by ring
    _ = (∑' p, ρ p) * x + y * ∑' p, ρ p * f p := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
    _ = x + y * ∑' p, ρ p * f p := by rw [PMF.tsum_coe, one_mul]

/-! ### The pointwise ingredients of the expansion step -/

/-- The two-pairing product of child weights against a target pair `j'`
(`sec:one-weight`): the restricted inverse pair degree is at most this sum. -/
private noncomputable def pairW (α : ℝ) (h : ℕ) (j' : I × I)
    (p : FullLab (I × V) h × FullLab (I × V) h) : ℝ≥0∞ :=
  M.W α j'.1 h p.1 * M.W α j'.2 h p.2 + M.W α j'.2 h p.1 * M.W α j'.1 h p.2

/-- The selected inverse mixture weight of a source child pair against the normaliser
`u` (`eq:selected-inverse-mixture`, split along the two pairings). -/
private noncomputable def selW (α : ℝ) (Sel : Selection M) (u : I) (h : ℕ)
    (p : FullLab (I × V) h × FullLab (I × V) h) : ℝ≥0∞ :=
  ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α) * pairW M α h j' p

/-- The split indicator of a source child pair against the child types `D'`
(`sec:unweighted`): one child in the zero event, or both children in the union event. -/
private noncomputable def indW (D' : Set I) (h : ℕ)
    (p : FullLab (I × V) h × FullLab (I × V) h) : ℝ≥0∞ :=
  (if M.ZeroEv D' h p.1 then 1 else 0) + (if M.ZeroEv D' h p.2 then 1 else 0)
    + (if M.UnionEv D' h p.1 then 1 else 0) * (if M.UnionEv D' h p.2 then 1 else 0)

/-- **The pointwise bound of the weighted expansion step** (`sec:one-weight`): at a
realised root state and a realised child pair, the zero-restricted weight of the branch is
at most the incompatible-root weight times the selected pair weight, plus the
compatible-root weight times the selected pair weight times the split indicator. -/
private lemma branch_weight_le (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0) {α : ℝ}
    (hα : 0 ≤ α) (Sel : Selection M) {D : Set I} {h : ℕ} (s u : I) {v : V}
    (hv : v ∈ M.Vmu) {p : FullLab (I × V) h × FullLab (I × V) h}
    (hp1 : StatesIn M.Vmu h p.1) (hp2 : StatesIn M.Vmu h p.2) :
    (if M.ZeroEv D (h + 1) (branch (s, v) p) then M.W α u (h + 1) (branch (s, v) p) else 0)
      ≤ (if M.R v M.zero then 0 else WresD α (M.rootLaw u) M.R v) * selW M α Sel u h p
        + (if M.R v M.zero then WresD α (M.rootLaw u) M.R v else 0)
          * (selW M α Sel u h p * indW M (M.children D) h p) := by
  have hW : WresD α (M.childMix u h) (SquareRel (M.sim h)) p ≤ selW M α Sel u h p := by
    refine (M.WresD_childMix_le hα Sel u h p hp1 hp2).trans ?_
    unfold selW
    exact Finset.sum_le_sum fun j' _ => mul_le_mul_right (M.WresD_pair_le hα j'.1 j'.2 h p) _
  have hWs : M.W α u (h + 1) (branch (s, v) p)
      = WresD α (M.rootLaw u) M.R v * WresD α (M.childMix u h) (SquareRel (M.sim h)) p :=
    M.W_succ α u h (s, v) p
  by_cases hv0 : M.R v M.zero
  · rw [if_pos hv0, if_pos hv0, zero_mul, zero_add]
    by_cases hz : M.ZeroEv D (h + 1) (branch (s, v) p)
    · rw [if_pos hz, hWs]
      have h1 : 1 ≤ indW M (M.children D) h p := by
        rcases M.zeroEv_succ_imp hc hb0 hv hv0 hz with h1 | h2 | ⟨h3, h4⟩
        · simp only [indW, h1, ite_true]
          exact le_self_add.trans le_self_add
        · simp only [indW, h2, ite_true]
          exact le_add_self.trans le_self_add
        · simp only [indW, h3, h4, ite_true, one_mul]
          exact le_add_self
      calc WresD α (M.rootLaw u) M.R v * WresD α (M.childMix u h) (SquareRel (M.sim h)) p
          ≤ WresD α (M.rootLaw u) M.R v * (selW M α Sel u h p * 1) := by
            rw [mul_one]; exact mul_le_mul_right hW _
        _ ≤ _ := mul_le_mul_right (mul_le_mul_right h1 _) _
    · rw [if_neg hz]
      exact zero_le
  · rw [if_neg hv0, if_neg hv0, zero_mul, add_zero]
    refine le_trans ?_ (mul_le_mul_right hW _)
    rw [← hWs]
    split_ifs <;> simp

/-- An inverse moment against an equal-phase normaliser is at most `U(M)` (`eq:moment`). -/
private lemma moment_le_Ufun {α : ℝ} (hα : 1 ≤ α) {Mb : ℝ≥0∞} {a c : I} {h : ℕ}
    (hac : M.P α a c h ≤ Mb) : ∑' x, M.rho a h x * M.W α c h x ≤ Ufun α Mb :=
  (M.moment_le hα a c h).trans (add_le_add_right (mul_le_mul_right hac _) _)

/-- A weighted union integral over the children of an equal-phase set is at most
`T Z + α M` (`eq:zero-union-moment` over the phase class of the children). -/
private lemma wUnion_le_Zt [Fintype I] {α : ℝ} (hα : 1 ≤ α) {g : ℕ} (Θ : Phase M g) {T : ℕ}
    (hT : ∀ i, Θ.count i ≤ T) {h : ℕ} {Mb Zm : ℝ≥0∞}
    (hM : ∀ s u, Θ.θ s = Θ.θ u → M.P α s u h ≤ Mb)
    (hz : ∀ s t, Θ.θ s = Θ.θ t → M.z s t h ≤ Zm) {a c : I} {D' : Set I}
    (hD' : ∀ t ∈ D', Θ.θ t = Θ.θ a) (hca : Θ.θ c = Θ.θ a) :
    M.wUnion α a D' c h ≤ (T : ℝ≥0∞) * Zm + ENNReal.ofReal α * Mb := by
  have hsub : D' ⊆ ↑(Θ.cls (Θ.θ a)) := fun t ht =>
    Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD' t ht⟩)
  refine (M.wUnion_mono hsub h).trans ((M.wUnion_le_card hα a (Θ.cls (Θ.θ a)) c h
    fun t ht => hz a t ?_).trans ?_)
  · exact ((Finset.mem_filter.mp ht).2).symm
  · refine add_le_add (mul_le_mul_left ?_ _) (mul_le_mul_right (hM a c hca.symm) _)
    rw [Phase.card_cls]
    exact_mod_cast hT _

/-- **The unrestricted pair moment**: against an independent source child pair, the
two-pairing weight integrates to at most `2 U(M)²` (`sec:one-weight`). -/
private lemma pair_unres_le {α : ℝ} {h : ℕ} {Mb : ℝ≥0∞} {j j' : I × I}
    (hm11 : ∑' x, M.rho j.1 h x * M.W α j'.1 h x ≤ Ufun α Mb)
    (hm12 : ∑' x, M.rho j.1 h x * M.W α j'.2 h x ≤ Ufun α Mb)
    (hm21 : ∑' x, M.rho j.2 h x * M.W α j'.1 h x ≤ Ufun α Mb)
    (hm22 : ∑' x, M.rho j.2 h x * M.W α j'.2 h x ≤ Ufun α Mb) :
    ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p * pairW M α h j' p
      ≤ 2 * Ufun α Mb ^ 2 := by
  calc ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p * pairW M α h j' p
      = ∑' p, (prodPMF (M.rho j.1 h) (M.rho j.2 h) p * (M.W α j'.1 h p.1 * M.W α j'.2 h p.2)
          + prodPMF (M.rho j.1 h) (M.rho j.2 h) p
            * (M.W α j'.2 h p.1 * M.W α j'.1 h p.2)) :=
        tsum_congr fun p => by unfold pairW; ring
    _ = (∑' x, M.rho j.1 h x * M.W α j'.1 h x) * (∑' y, M.rho j.2 h y * M.W α j'.2 h y)
          + (∑' x, M.rho j.1 h x * M.W α j'.2 h x)
            * (∑' y, M.rho j.2 h y * M.W α j'.1 h y) := by
        rw [ENNReal.tsum_add,
          tsum_prodPMF_mul (M.rho j.1 h) (M.rho j.2 h) (M.W α j'.1 h) (M.W α j'.2 h),
          tsum_prodPMF_mul (M.rho j.1 h) (M.rho j.2 h) (M.W α j'.2 h) (M.W α j'.1 h)]
    _ ≤ Ufun α Mb * Ufun α Mb + Ufun α Mb * Ufun α Mb :=
        add_le_add (mul_le_mul' hm11 hm22) (mul_le_mul' hm12 hm21)
    _ = 2 * Ufun α Mb ^ 2 := by ring

/-- **One pairing against the split indicator**: the continuing terms carry one weighted
zero integral times an unrestricted moment, the split term the product of two weighted
union integrals (`sec:one-weight`). -/
private lemma pair_zero_le {α : ℝ} {h : ℕ} {Mb Zt : ℝ≥0∞} {a b c d : I} {D' : Set I}
    (hm1 : ∑' x, M.rho a h x * M.W α c h x ≤ Ufun α Mb)
    (hm2 : ∑' x, M.rho b h x * M.W α d h x ≤ Ufun α Mb)
    (hu1 : M.wUnion α a D' c h ≤ Zt) (hu2 : M.wUnion α b D' d h ≤ Zt) :
    ∑' p, prodPMF (M.rho a h) (M.rho b h) p
        * (M.W α c h p.1 * M.W α d h p.2 * indW M D' h p)
      ≤ Ufun α Mb * (M.wZero α a D' c h + M.wZero α b D' d h) + Zt ^ 2 := by
  have hsplit : ∀ p : FullLab (I × V) h × FullLab (I × V) h,
      M.W α c h p.1 * M.W α d h p.2 * indW M D' h p
        = (if M.ZeroEv D' h p.1 then M.W α c h p.1 else 0) * M.W α d h p.2
          + M.W α c h p.1 * (if M.ZeroEv D' h p.2 then M.W α d h p.2 else 0)
          + (if M.UnionEv D' h p.1 then M.W α c h p.1 else 0)
            * (if M.UnionEv D' h p.2 then M.W α d h p.2 else 0) := by
    intro p
    unfold indW
    split_ifs <;> ring
  have e1 : ∑' p, prodPMF (M.rho a h) (M.rho b h) p
        * ((if M.ZeroEv D' h p.1 then M.W α c h p.1 else 0) * M.W α d h p.2)
      = M.wZero α a D' c h * ∑' y, M.rho b h y * M.W α d h y :=
    tsum_prodPMF_mul (M.rho a h) (M.rho b h)
      (fun x => if M.ZeroEv D' h x then M.W α c h x else 0) (M.W α d h)
  have e2 : ∑' p, prodPMF (M.rho a h) (M.rho b h) p
        * (M.W α c h p.1 * (if M.ZeroEv D' h p.2 then M.W α d h p.2 else 0))
      = (∑' x, M.rho a h x * M.W α c h x) * M.wZero α b D' d h :=
    tsum_prodPMF_mul (M.rho a h) (M.rho b h) (M.W α c h)
      (fun y => if M.ZeroEv D' h y then M.W α d h y else 0)
  have e3 : ∑' p, prodPMF (M.rho a h) (M.rho b h) p
        * ((if M.UnionEv D' h p.1 then M.W α c h p.1 else 0)
          * (if M.UnionEv D' h p.2 then M.W α d h p.2 else 0))
      = M.wUnion α a D' c h * M.wUnion α b D' d h :=
    tsum_prodPMF_mul (M.rho a h) (M.rho b h)
      (fun x => if M.UnionEv D' h x then M.W α c h x else 0)
      (fun y => if M.UnionEv D' h y then M.W α d h y else 0)
  calc ∑' p, prodPMF (M.rho a h) (M.rho b h) p
        * (M.W α c h p.1 * M.W α d h p.2 * indW M D' h p)
      = ∑' p, (prodPMF (M.rho a h) (M.rho b h) p
            * ((if M.ZeroEv D' h p.1 then M.W α c h p.1 else 0) * M.W α d h p.2)
          + prodPMF (M.rho a h) (M.rho b h) p
            * (M.W α c h p.1 * (if M.ZeroEv D' h p.2 then M.W α d h p.2 else 0))
          + prodPMF (M.rho a h) (M.rho b h) p
            * ((if M.UnionEv D' h p.1 then M.W α c h p.1 else 0)
              * (if M.UnionEv D' h p.2 then M.W α d h p.2 else 0))) :=
        tsum_congr fun p => by rw [hsplit p, mul_add, mul_add]
    _ = M.wZero α a D' c h * (∑' y, M.rho b h y * M.W α d h y)
          + (∑' x, M.rho a h x * M.W α c h x) * M.wZero α b D' d h
          + M.wUnion α a D' c h * M.wUnion α b D' d h := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, e1, e2, e3]
    _ ≤ M.wZero α a D' c h * Ufun α Mb + Ufun α Mb * M.wZero α b D' d h + Zt * Zt :=
        add_le_add (add_le_add (mul_le_mul_right hm2 _) (mul_le_mul_left hm1 _))
          (mul_le_mul' hu1 hu2)
    _ = Ufun α Mb * (M.wZero α a D' c h + M.wZero α b D' d h) + Zt ^ 2 := by ring

/-- **Both pairings against the split indicator** (`sec:one-weight`): the four continuing
weighted zero integrals times `U(M)`, plus twice the split term. -/
private lemma pair_total_le {α : ℝ} {h : ℕ} {Mb Zt : ℝ≥0∞} {j j' : I × I} {D' : Set I}
    (hm11 : ∑' x, M.rho j.1 h x * M.W α j'.1 h x ≤ Ufun α Mb)
    (hm12 : ∑' x, M.rho j.1 h x * M.W α j'.2 h x ≤ Ufun α Mb)
    (hm21 : ∑' x, M.rho j.2 h x * M.W α j'.1 h x ≤ Ufun α Mb)
    (hm22 : ∑' x, M.rho j.2 h x * M.W α j'.2 h x ≤ Ufun α Mb)
    (hu11 : M.wUnion α j.1 D' j'.1 h ≤ Zt) (hu12 : M.wUnion α j.1 D' j'.2 h ≤ Zt)
    (hu21 : M.wUnion α j.2 D' j'.1 h ≤ Zt) (hu22 : M.wUnion α j.2 D' j'.2 h ≤ Zt) :
    ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p * (pairW M α h j' p * indW M D' h p)
      ≤ Ufun α Mb * (M.wZero α j.1 D' j'.1 h + M.wZero α j.1 D' j'.2 h
          + M.wZero α j.2 D' j'.1 h + M.wZero α j.2 D' j'.2 h) + 2 * Zt ^ 2 := by
  calc ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p * (pairW M α h j' p * indW M D' h p)
      = ∑' p, (prodPMF (M.rho j.1 h) (M.rho j.2 h) p
            * (M.W α j'.1 h p.1 * M.W α j'.2 h p.2 * indW M D' h p)
          + prodPMF (M.rho j.1 h) (M.rho j.2 h) p
            * (M.W α j'.2 h p.1 * M.W α j'.1 h p.2 * indW M D' h p)) :=
        tsum_congr fun p => by unfold pairW; ring
    _ = ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p
            * (M.W α j'.1 h p.1 * M.W α j'.2 h p.2 * indW M D' h p)
          + ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p
            * (M.W α j'.2 h p.1 * M.W α j'.1 h p.2 * indW M D' h p) := ENNReal.tsum_add
    _ ≤ (Ufun α Mb * (M.wZero α j.1 D' j'.1 h + M.wZero α j.2 D' j'.2 h) + Zt ^ 2)
          + (Ufun α Mb * (M.wZero α j.1 D' j'.2 h + M.wZero α j.2 D' j'.1 h) + Zt ^ 2) :=
        add_le_add (M.pair_zero_le hm11 hm22 hu11 hu22) (M.pair_zero_le hm12 hm21 hu12 hu21)
    _ = _ := by ring

/-! ### The expansion step -/

/-- **The weighted expansion step**: for a nonempty equal-phase target set `D`, a source
`s` and a normaliser `u`, with the potentials and zero masses of all equal-phase pairs at
height `h` at most `Mb` and `Zm`, the weighted zero integral at height `h+1` is at most
the incompatible-root term, the split term, and `R_μ U(M)` times the selected inverse
mixture (coefficients `π_u(j')^{-α}`, total at most `B`) of the four continuing weighted zero
integrals against the children at height `h`, averaged over the source transition. -/
theorem wZero_succ_le [Fintype I] (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0)
    {α : ℝ} (hα : 1 ≤ α) {g : ℕ} (Θ : Phase M g) {T : ℕ} (hT : ∀ i, Θ.count i ≤ T)
    (Sel : Selection M) {B : ℝ≥0∞} (hB : ∀ t, Sel.budget α t ≤ B)
    {h : ℕ} {Mb Zm : ℝ≥0∞} (hM : ∀ s u, Θ.θ s = Θ.θ u → M.P α s u h ≤ Mb)
    (hz : ∀ s t, Θ.θ s = Θ.θ t → M.z s t h ≤ Zm)
    (s : I) {D : Set I} (hD : ∀ t ∈ D, Θ.θ t = Θ.θ s) (u : I) (hu : Θ.θ u = Θ.θ s) :
    M.wZero α s D u (h + 1)
      ≤ 2 * B * (Ufun α Mb) ^ 2 * M.fRoot α
        + 2 * B * M.RmuC α * ((T : ℝ≥0∞) * Zm + ENNReal.ofReal α * Mb) ^ 2
        + M.RmuC α * Ufun α Mb
          * ∑' j, M.π s j * ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α) *
              (M.wZero α j.1 (M.children D) j'.1 h + M.wZero α j.1 (M.children D) j'.2 h
                + M.wZero α j.2 (M.children D) j'.1 h
                + M.wZero α j.2 (M.children D) j'.2 h) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  -- phases of the children of `D`, of the source transitions and of the selected pairs
  have hphase : ∀ t ∈ M.children D, Θ.θ t = Θ.θ s + 1 := fun t ht => by
    obtain ⟨t₀, ht₀, hch⟩ := ht
    rw [Θ.child_eq hch, hD t₀ ht₀]
  have hJ : ∀ j' ∈ Sel.J u, Θ.θ j'.1 = Θ.θ s + 1 ∧ Θ.θ j'.2 = Θ.θ s + 1 := fun j' hj' => by
    have := Θ.child u j' (Sel.charged u j' hj')
    rw [hu] at this
    exact this
  -- the expansion of the source law
  have hexp : M.wZero α s D u (h + 1)
      = ∑' v, M.rootLaw s v * ∑' j, M.π s j * ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p
          * (if M.ZeroEv D (h + 1) (branch (s, v) p) then M.W α u (h + 1) (branch (s, v) p)
              else 0) := by
    rw [wZero, rho_succ, tsum_bind_mul, rootT, tsum_map_mul]
    refine tsum_congr fun v => ?_
    rw [tsum_map_mul, childMix, tsum_bind_mul]
  -- the pointwise bound on charged root states and charged child pairs
  have hpt : ∀ v, M.rootLaw s v * ∑' j, M.π s j * ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p
        * (if M.ZeroEv D (h + 1) (branch (s, v) p) then M.W α u (h + 1) (branch (s, v) p)
            else 0)
      ≤ M.rootLaw s v * ∑' j, M.π s j * ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p
        * ((if M.R v M.zero then 0 else WresD α (M.rootLaw u) M.R v) * selW M α Sel u h p
          + (if M.R v M.zero then WresD α (M.rootLaw u) M.R v else 0)
            * (selW M α Sel u h p * indW M (M.children D) h p)) := by
    intro v
    by_cases hv : M.rootLaw s v = 0
    · simp [hv]
    refine mul_le_mul_right (ENNReal.tsum_le_tsum fun j =>
      mul_le_mul_right (ENNReal.tsum_le_tsum fun p => ?_) _) _
    by_cases hp : prodPMF (M.rho j.1 h) (M.rho j.2 h) p = 0
    · simp [hp]
    refine mul_le_mul_right ?_ _
    rw [prodPMF_apply] at hp
    obtain ⟨hp1, hp2⟩ := mul_ne_zero_iff.mp hp
    exact M.branch_weight_le hc hb0 hα0 Sel s u (M.rootLaw_mem_Vmu hv)
      (M.statesIn_of_rho_ne_zero _ _ _ hp1) (M.statesIn_of_rho_ne_zero _ _ _ hp2)
  -- the two integrals of the bound
  have hre : ∑' v, M.rootLaw s v * ∑' j, M.π s j * ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p
        * ((if M.R v M.zero then 0 else WresD α (M.rootLaw u) M.R v) * selW M α Sel u h p
          + (if M.R v M.zero then WresD α (M.rootLaw u) M.R v else 0)
            * (selW M α Sel u h p * indW M (M.children D) h p))
      = (∑' v, M.rootLaw s v * (if M.R v M.zero then 0 else WresD α (M.rootLaw u) M.R v))
          * ∑' j, M.π s j * ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p * selW M α Sel u h p
        + (∑' v, M.rootLaw s v * (if M.R v M.zero then WresD α (M.rootLaw u) M.R v else 0))
          * ∑' j, M.π s j * ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p
            * (selW M α Sel u h p * indW M (M.children D) h p) := by
    rw [← tsum_mul_add_mul]
    refine tsum_congr fun v => ?_
    congr 1
    rw [← tsum_mul_const_add]
    refine tsum_congr fun j => ?_
    congr 1
    exact tsum_mul_const_add _ _ _ _ _
  -- the incompatible-root factor and the unrestricted child moments
  have hA : ∑' v, M.rootLaw s v * (if M.R v M.zero then 0 else WresD α (M.rootLaw u) M.R v)
      ≤ M.fRoot α := by
    refine (M.root_incompatible_le hc s u).trans ?_
    split_ifs <;> simp
  have hI1 : ∑' j, M.π s j * ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p * selW M α Sel u h p
      ≤ 2 * B * Ufun α Mb ^ 2 := by
    calc ∑' j, M.π s j * ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p * selW M α Sel u h p
        ≤ ∑' j, M.π s j * (2 * B * Ufun α Mb ^ 2) := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          by_cases hj : M.π s j = 0
          · simp [hj]
          refine mul_le_mul_right ?_ _
          have hjp := Θ.child s j hj
          unfold selW
          rw [tsum_mul_finset_sum]
          calc ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α)
                * ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p * pairW M α h j' p
              ≤ ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α) * (2 * Ufun α Mb ^ 2) := by
                refine Finset.sum_le_sum fun j' hj' => mul_le_mul_right ?_ _
                obtain ⟨h1, h2⟩ := hJ j' hj'
                exact M.pair_unres_le (M.moment_le_Ufun hα (hM _ _ (by rw [hjp.1, h1])))
                  (M.moment_le_Ufun hα (hM _ _ (by rw [hjp.1, h2])))
                  (M.moment_le_Ufun hα (hM _ _ (by rw [hjp.2, h1])))
                  (M.moment_le_Ufun hα (hM _ _ (by rw [hjp.2, h2])))
            _ = Sel.budget α u * (2 * Ufun α Mb ^ 2) := by
                rw [Selection.budget, Finset.sum_mul]
            _ ≤ B * (2 * Ufun α Mb ^ 2) := mul_le_mul_left (hB u) _
            _ = 2 * B * Ufun α Mb ^ 2 := by ring
      _ = 2 * B * Ufun α Mb ^ 2 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  -- the compatible-root factor and the split child integrals
  have hC : ∑' v, M.rootLaw s v * (if M.R v M.zero then WresD α (M.rootLaw u) M.R v else 0)
      ≤ M.RmuC α := M.root_compatible_le hc s u
  have hI2 : ∑' j, M.π s j * ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p
        * (selW M α Sel u h p * indW M (M.children D) h p)
      ≤ 2 * B * ((T : ℝ≥0∞) * Zm + ENNReal.ofReal α * Mb) ^ 2
        + Ufun α Mb * ∑' j, M.π s j * ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α) *
            (M.wZero α j.1 (M.children D) j'.1 h + M.wZero α j.1 (M.children D) j'.2 h
              + M.wZero α j.2 (M.children D) j'.1 h
              + M.wZero α j.2 (M.children D) j'.2 h) := by
    have hsel : ∀ p : FullLab (I × V) h × FullLab (I × V) h,
        selW M α Sel u h p * indW M (M.children D) h p
          = ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α)
              * (pairW M α h j' p * indW M (M.children D) h p) := by
      intro p
      unfold selW
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    calc ∑' j, M.π s j * ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p
          * (selW M α Sel u h p * indW M (M.children D) h p)
        ≤ ∑' j, M.π s j * (2 * B * ((T : ℝ≥0∞) * Zm + ENNReal.ofReal α * Mb) ^ 2
            + Ufun α Mb * ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α) *
              (M.wZero α j.1 (M.children D) j'.1 h + M.wZero α j.1 (M.children D) j'.2 h
                + M.wZero α j.2 (M.children D) j'.1 h
                + M.wZero α j.2 (M.children D) j'.2 h)) := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          by_cases hj : M.π s j = 0
          · simp [hj]
          refine mul_le_mul_right ?_ _
          have hjp := Θ.child s j hj
          simp_rw [hsel]
          rw [tsum_mul_finset_sum]
          calc ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α)
                * ∑' p, prodPMF (M.rho j.1 h) (M.rho j.2 h) p
                  * (pairW M α h j' p * indW M (M.children D) h p)
              ≤ ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α)
                  * (Ufun α Mb * (M.wZero α j.1 (M.children D) j'.1 h
                      + M.wZero α j.1 (M.children D) j'.2 h
                      + M.wZero α j.2 (M.children D) j'.1 h
                      + M.wZero α j.2 (M.children D) j'.2 h)
                    + 2 * ((T : ℝ≥0∞) * Zm + ENNReal.ofReal α * Mb) ^ 2) := by
                refine Finset.sum_le_sum fun j' hj' => mul_le_mul_right ?_ _
                obtain ⟨h1, h2⟩ := hJ j' hj'
                have hD1 : ∀ t ∈ M.children D, Θ.θ t = Θ.θ j.1 := fun t ht => by
                  rw [hphase t ht, hjp.1]
                have hD2 : ∀ t ∈ M.children D, Θ.θ t = Θ.θ j.2 := fun t ht => by
                  rw [hphase t ht, hjp.2]
                exact M.pair_total_le (M.moment_le_Ufun hα (hM _ _ (by rw [hjp.1, h1])))
                  (M.moment_le_Ufun hα (hM _ _ (by rw [hjp.1, h2])))
                  (M.moment_le_Ufun hα (hM _ _ (by rw [hjp.2, h1])))
                  (M.moment_le_Ufun hα (hM _ _ (by rw [hjp.2, h2])))
                  (M.wUnion_le_Zt hα Θ hT hM hz hD1 (by rw [h1, hjp.1]))
                  (M.wUnion_le_Zt hα Θ hT hM hz hD1 (by rw [h2, hjp.1]))
                  (M.wUnion_le_Zt hα Θ hT hM hz hD2 (by rw [h1, hjp.2]))
                  (M.wUnion_le_Zt hα Θ hT hM hz hD2 (by rw [h2, hjp.2]))
            _ = Ufun α Mb * ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α) *
                  (M.wZero α j.1 (M.children D) j'.1 h + M.wZero α j.1 (M.children D) j'.2 h
                    + M.wZero α j.2 (M.children D) j'.1 h
                    + M.wZero α j.2 (M.children D) j'.2 h)
                + Sel.budget α u * (2 * ((T : ℝ≥0∞) * Zm + ENNReal.ofReal α * Mb) ^ 2) := by
                rw [Selection.budget, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
                exact Finset.sum_congr rfl fun _ _ => by ring
            _ ≤ Ufun α Mb * ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α) *
                  (M.wZero α j.1 (M.children D) j'.1 h + M.wZero α j.1 (M.children D) j'.2 h
                    + M.wZero α j.2 (M.children D) j'.1 h
                    + M.wZero α j.2 (M.children D) j'.2 h)
                + B * (2 * ((T : ℝ≥0∞) * Zm + ENNReal.ofReal α * Mb) ^ 2) :=
                add_le_add_right (mul_le_mul_left (hB u) _) _
            _ = _ := by ring
      _ = 2 * B * ((T : ℝ≥0∞) * Zm + ENNReal.ofReal α * Mb) ^ 2
            + Ufun α Mb * ∑' j, M.π s j * ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α) *
              (M.wZero α j.1 (M.children D) j'.1 h + M.wZero α j.1 (M.children D) j'.2 h
                + M.wZero α j.2 (M.children D) j'.1 h
                + M.wZero α j.2 (M.children D) j'.2 h) := by
          exact tsum_pmf_mul_const_add (M.π s) _ _ _
  -- assembly
  calc M.wZero α s D u (h + 1)
      = _ := hexp
    _ ≤ _ := ENNReal.tsum_le_tsum hpt
    _ = _ := hre
    _ ≤ M.fRoot α * (2 * B * Ufun α Mb ^ 2)
          + M.RmuC α * (2 * B * ((T : ℝ≥0∞) * Zm + ENNReal.ofReal α * Mb) ^ 2
            + Ufun α Mb * ∑' j, M.π s j * ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α) *
              (M.wZero α j.1 (M.children D) j'.1 h + M.wZero α j.1 (M.children D) j'.2 h
                + M.wZero α j.2 (M.children D) j'.1 h
                + M.wZero α j.2 (M.children D) j'.2 h)) :=
        add_le_add (mul_le_mul' hA hI1) (mul_le_mul' hC hI2)
    _ = _ := by ring

/-! ### The terminal cases and the stopped expansion -/

/-- **The height-zero terminal case**: against a nonempty `D`, the weighted zero integral
at height zero is at most `f` for a fresh normaliser and zero for a forced one. -/
lemma wZero_zero_le (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0) {α : ℝ} (s : I)
    {D : Set I} (hD : D.Nonempty) (u : I) : M.wZero α s D u 0 ≤ M.fRoot α := by
  have hexp : M.wZero α s D u 0
      = ∑' v, M.rootLaw s v
          * (if M.ZeroEv D 0 (leaf (s, v)) then M.W α u 0 (leaf (s, v)) else 0) := by
    rw [wZero, rho_zero, tsum_map_mul, rootT, tsum_map_mul]
  have hpt : ∀ v, M.rootLaw s v
        * (if M.ZeroEv D 0 (leaf (s, v)) then M.W α u 0 (leaf (s, v)) else 0)
      ≤ M.rootLaw s v * (if M.R v M.zero then 0 else WresD α (M.rootLaw u) M.R v) := by
    intro v
    by_cases hv : M.rootLaw s v = 0
    · simp [hv]
    refine mul_le_mul_right ?_ _
    rw [W_zero]
    by_cases hz : M.ZeroEv D 0 (leaf (s, v))
    · rw [if_pos hz]
      have hv0 : ¬ M.R v M.zero := M.zeroEv_zero_imp hc hb0 hD (M.rootLaw_mem_Vmu hv) hz
      rw [if_neg hv0]
    · rw [if_neg hz]
      exact zero_le
  calc M.wZero α s D u 0 = _ := hexp
    _ ≤ ∑' v, M.rootLaw s v * (if M.R v M.zero then 0 else WresD α (M.rootLaw u) M.R v) :=
        ENNReal.tsum_le_tsum hpt
    _ ≤ if M.fresh u then M.fRoot α else 0 := M.root_incompatible_le hc s u
    _ ≤ M.fRoot α := by split_ifs <;> simp

/-- **The weighted stopped expansion**: with the equal-phase potentials and zero masses at
heights below `h` at most `Mb` and `Zm`, every stopping equal-phase triple has weighted
zero integral at most `G_n(4 B R_μ U(M)) · (2 B U(M)² f + 2 B R_μ (T Z + α M)²)`. -/
theorem wZero_le_of_stops [Fintype I] (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0)
    (hFP : M.FreshPositive) {α : ℝ} (hα : 1 ≤ α) {g : ℕ} (Θ : Phase M g) {T : ℕ}
    (hT : ∀ i, Θ.count i ≤ T) (Sel : Selection M) {B : ℝ≥0∞} (hB : ∀ t, Sel.budget α t ≤ B)
    {h : ℕ} {Mb Zm : ℝ≥0∞} (hM : ∀ j < h, ∀ s u, Θ.θ s = Θ.θ u → M.P α s u j ≤ Mb)
    (hz : ∀ j < h, ∀ s t, Θ.θ s = Θ.θ t → M.z s t j ≤ Zm) :
    ∀ (n : ℕ) (s : I) (D : Set I) (u : I), D.Nonempty → (∀ t ∈ D, Θ.θ t = Θ.θ s) →
      Θ.θ u = Θ.θ s → M.Stops s D n →
      M.wZero α s D u h ≤ Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb := by
  intro n
  induction n generalizing h with
  | zero =>
    intro s D u _ _ _ hst
    obtain ⟨hs, f, hfD, hf⟩ := hst.zero
    rw [M.wZero_eq_zero_of_fresh hFP hs hf hfD u h]
    exact zero_le
  | succ n ih =>
    intro s D u hD hDθ hu hst
    by_cases h0 : M.fresh s ∧ ∃ f ∈ D, M.fresh f
    · obtain ⟨hs, f, hfD, hf⟩ := h0
      rw [M.wZero_eq_zero_of_fresh hFP hs hf hfD u h]
      exact zero_le
    cases h with
    | zero =>
      -- the truncation: `f ≤ 2 B U(M)² f ≤ E`
      have hB1 : 1 ≤ B := (Sel.one_le_budget (by linarith) s).trans (hB s)
      have hU1 : 1 ≤ Ufun α Mb := le_self_add
      have h2BU : 1 ≤ 2 * B * Ufun α Mb ^ 2 := by
        calc (1 : ℝ≥0∞) = 1 * 1 * (1 * 1) := by norm_num
          _ ≤ 2 * B * (Ufun α Mb * Ufun α Mb) :=
            mul_le_mul' (mul_le_mul' one_le_two hB1) (mul_le_mul' hU1 hU1)
          _ = 2 * B * Ufun α Mb ^ 2 := by ring
      refine (M.wZero_zero_le hc hb0 s hD u).trans ?_
      rw [Efun]
      calc M.fRoot α ≤ 2 * B * Ufun α Mb ^ 2 * M.fRoot α := le_mul_of_one_le_left' h2BU
        _ ≤ 2 * B * Ufun α Mb ^ 2 * M.fRoot α
            + 2 * B * M.RmuC α * ((T : ℝ≥0∞) * Zm + ENNReal.ofReal α * Mb) ^ 2 := le_self_add
        _ ≤ _ := le_mul_of_one_le_left' (one_le_GHe _ _)
    | succ h' =>
      have hM' : ∀ j < h', ∀ s u, Θ.θ s = Θ.θ u → M.P α s u j ≤ Mb :=
        fun j hj => hM j (Nat.lt_succ_of_lt hj)
      have hz' : ∀ j < h', ∀ s t, Θ.θ s = Θ.θ t → M.z s t j ≤ Zm :=
        fun j hj => hz j (Nat.lt_succ_of_lt hj)
      have hMh := hM h' (Nat.lt_succ_self h')
      have hzh := hz h' (Nat.lt_succ_self h')
      have hD'ne : (M.children D).Nonempty := M.children_nonempty hD
      have hphase : ∀ t ∈ M.children D, Θ.θ t = Θ.θ s + 1 := fun t ht => by
        obtain ⟨t₀, ht₀, hch⟩ := ht
        rw [Θ.child_eq hch, hDθ t₀ ht₀]
      have hJ : ∀ j' ∈ Sel.J u, Θ.θ j'.1 = Θ.θ s + 1 ∧ Θ.θ j'.2 = Θ.θ s + 1 :=
        fun j' hj' => by
          have := Θ.child u j' (Sel.charged u j' hj')
          rw [hu] at this
          exact this
      -- the four continuing terms by the induction hypothesis
      have hS4 : ∀ j, M.π s j ≠ 0 → ∀ j' ∈ Sel.J u,
          M.wZero α j.1 (M.children D) j'.1 h' + M.wZero α j.1 (M.children D) j'.2 h'
              + M.wZero α j.2 (M.children D) j'.1 h' + M.wZero α j.2 (M.children D) j'.2 h'
            ≤ 4 * Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb := by
        intro j hj j' hj'
        have hjp := Θ.child s j hj
        obtain ⟨h1, h2⟩ := hJ j' hj'
        have hst1 : M.Stops j.1 (M.children D) n := hst.succ h0 ⟨j, hj, Or.inl rfl⟩
        have hst2 : M.Stops j.2 (M.children D) n := hst.succ h0 ⟨j, hj, Or.inr rfl⟩
        have hD1 : ∀ t ∈ M.children D, Θ.θ t = Θ.θ j.1 := fun t ht => by
          rw [hphase t ht, hjp.1]
        have hD2 : ∀ t ∈ M.children D, Θ.θ t = Θ.θ j.2 := fun t ht => by
          rw [hphase t ht, hjp.2]
        have e11 := ih hM' hz' j.1 (M.children D) j'.1 hD'ne hD1 (by rw [h1, hjp.1]) hst1
        have e12 := ih hM' hz' j.1 (M.children D) j'.2 hD'ne hD1 (by rw [h2, hjp.1]) hst1
        have e21 := ih hM' hz' j.2 (M.children D) j'.1 hD'ne hD2 (by rw [h1, hjp.2]) hst2
        have e22 := ih hM' hz' j.2 (M.children D) j'.2 hD'ne hD2 (by rw [h2, hjp.2]) hst2
        calc _ ≤ Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb
              + Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb
              + Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb
              + Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb :=
            add_le_add (add_le_add (add_le_add e11 e12) e21) e22
          _ = _ := by ring
      -- the selected sum of the continuing terms
      have hSig : ∑' j, M.π s j * ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α) *
            (M.wZero α j.1 (M.children D) j'.1 h' + M.wZero α j.1 (M.children D) j'.2 h'
              + M.wZero α j.2 (M.children D) j'.1 h'
              + M.wZero α j.2 (M.children D) j'.2 h')
          ≤ 4 * B * Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb := by
        calc ∑' j, M.π s j * ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α) *
              (M.wZero α j.1 (M.children D) j'.1 h' + M.wZero α j.1 (M.children D) j'.2 h'
                + M.wZero α j.2 (M.children D) j'.1 h'
                + M.wZero α j.2 (M.children D) j'.2 h')
            ≤ ∑' j, M.π s j * (4 * B * Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb) := by
              refine ENNReal.tsum_le_tsum fun j => ?_
              by_cases hj : M.π s j = 0
              · simp [hj]
              refine mul_le_mul_right ?_ _
              calc ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α) *
                    (M.wZero α j.1 (M.children D) j'.1 h'
                      + M.wZero α j.1 (M.children D) j'.2 h'
                      + M.wZero α j.2 (M.children D) j'.1 h'
                      + M.wZero α j.2 (M.children D) j'.2 h')
                  ≤ ∑ j' ∈ Sel.J u, (M.π u j') ^ (-α)
                      * (4 * Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb) :=
                    Finset.sum_le_sum fun j' hj' => mul_le_mul_right (hS4 j hj j' hj') _
                _ = Sel.budget α u * (4 * Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb) := by
                    rw [Selection.budget, Finset.sum_mul]
                _ ≤ B * (4 * Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb) :=
                    mul_le_mul_left (hB u) _
                _ = 4 * B * Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb := by ring
          _ = 4 * B * Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb := by
              rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      calc M.wZero α s D u (h' + 1)
          ≤ _ := M.wZero_succ_le hc hb0 hα Θ hT Sel hB hMh hzh s hDθ u hu
        _ ≤ 2 * B * (Ufun α Mb) ^ 2 * M.fRoot α
              + 2 * B * M.RmuC α * ((T : ℝ≥0∞) * Zm + ENNReal.ofReal α * Mb) ^ 2
              + M.RmuC α * Ufun α Mb * (4 * B * Efun α n T B (M.fRoot α) (M.RmuC α) Zm Mb) :=
            add_le_add_right (mul_le_mul_right hSig _) _
        _ = Efun α (n + 1) T B (M.fRoot α) (M.RmuC α) Zm Mb := by
            simp only [Efun, GHe_succ]
            ring

/-- **`thm:explicit-weighted-bound`**: under common returns within `H`, with the
equal-phase potentials and zero masses at heights below `h` at most `Mb` and `Zm`, every
equal-phase weighted zero integral at height `h` against a nonempty equal-phase `D` is at
most `E(M)` of `eq:explicit-weighted-error`. -/
theorem wZero_le_Efun [Fintype I] (hc : M.IsCompat) (hb0 : rE M.μ M.R M.zero ≠ 0)
    (hFP : M.FreshPositive) {α : ℝ} (hα : 1 ≤ α) {g : ℕ} (Θ : Phase M g) {T : ℕ}
    (hT : ∀ i, Θ.count i ≤ T) {H : ℕ} (hCR : M.CommonReturns Θ H) (Sel : Selection M)
    {B : ℝ≥0∞} (hB : ∀ t, Sel.budget α t ≤ B) {h : ℕ} {Mb Zm : ℝ≥0∞}
    (hM : ∀ j < h, ∀ s u, Θ.θ s = Θ.θ u → M.P α s u j ≤ Mb)
    (hz : ∀ j < h, ∀ s t, Θ.θ s = Θ.θ t → M.z s t j ≤ Zm) :
    ∀ (s : I) (D : Set I) (u : I), D.Nonempty → (∀ t ∈ D, Θ.θ t = Θ.θ s) →
      Θ.θ u = Θ.θ s → M.wZero α s D u h ≤ Efun α H T B (M.fRoot α) (M.RmuC α) Zm Mb := by
  intro s D u hD hDθ hu
  obtain ⟨t, ht⟩ := hD
  exact M.wZero_le_of_stops hc hb0 hFP hα Θ hT Sel hB hM hz H s D u ⟨t, ht⟩ hDθ hu
    (stops_of_mem ht (hCR s t (hDθ t ht).symm))

end Model

end GraphMarkovMatching.Stopped
