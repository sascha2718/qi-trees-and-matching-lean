/-
Finite-height stability under truncation: two Markov models over the same states with the
same fresh types whose kernels are within
`t` in total variation at every type have level laws within `(2^{h+1} - 1) t` at height `h`,
so the failure probability of one is at most that of the other plus the sum of the two
initial types' errors. A presentation whose arity laws are conditioned on `k ≤ N` keeps its
core and its profiles; its model on the reduced live types has the same failure
probabilities as the truncated kernel on the original live types, and the kernel distance
is the tail mass `t_σ(N) = ν_σ{k > N}`.

* `tvDist`, `tvDist_comm`, `tsum_mul_le_add_tvDist`, `tvDist_bind_le`, `tvDist_map_le`,
  `tvDist_prodPMF_le`: the one-sided total variation `∑ (p x - q x)` and its behaviour under
  bounded test functions, mixtures, pushforwards and products;
* `Model.tvDist_rho_le_of_hered`, `Model.tvDist_rho_le`: the level laws of two models with
  kernels within `d s` at every type, `d` nonincreasing along charged transitions, are within
  `(2^{h+1} - 1) d s` at height `h`;
* `Model.failProb_le_add_tvDist`, `Model.failProb_le_truncated`: the corresponding failure
  bound for two arbitrary models, with the two sides' errors `d s` and `d t`;
* `labMap`, `Model.IsEmbed`, `IsEmbed.rho`, `IsEmbed.failProb`: relabelling the types of a
  model along an embedding preserves the level laws and the failure probabilities;
* `Presentation.tail`, `Presentation.truncate`, `Presentation.truncate_tail`,
  `Presentation.toModelTrunc`, `Presentation.tvDist_kernel_truncate`,
  `Presentation.failProb_toModelTrunc_eq`, `Presentation.failProb_le_truncate`: the truncated
  presentation `ν_σ^{(N)}` and the corresponding failure bound for its model.

Formulation of the two-sided bound: the kernel distance is bounded by a function `d` of the
type which is nonincreasing along charged transitions (hereditary), and the conclusion
carries `d s + d t` for the initial types `s`, `t`. For a presentation `d` is the tail mass of
the type's side, which the kernel preserves, so `d (freshL σ) = t_σ(N)`.
-/
import GraphMarkovMatching.Stopped.Presentation
import GraphMarkovMatching.Stopped.Semigroup

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

/-! ### Total variation -/

/-- The one-sided total variation `∑_x (p x - q x)` with truncated subtraction; for
probability laws it equals `∑_x (q x - p x)` (`tvDist_comm`) and is the disagreement
probability of an optimal coupling. -/
noncomputable def tvDist {X : Type} (p q : PMF X) : ℝ≥0∞ := ∑' x, (p x - q x)

/-- A law is at distance zero from itself. -/
lemma tvDist_self {X : Type} (p : PMF X) : tvDist p p = 0 := by
  rw [tvDist]
  exact ENNReal.tsum_eq_zero.mpr fun x => tsub_self _

/-- A point mass is split as its excess over the other law plus the common part. -/
private lemma tsub_add_min {X : Type} (p q : PMF X) (x : X) :
    p x - q x + min (p x) (q x) = p x := by
  rcases le_total (p x) (q x) with hab | hab
  · rw [tsub_eq_zero_of_le hab, min_eq_left hab, zero_add]
  · rw [min_eq_right hab, tsub_add_cancel_of_le hab]

/-- The one-sided total variation is symmetric for probability laws. -/
lemma tvDist_comm {X : Type} (p q : PMF X) : tvDist p q = tvDist q p := by
  have hmin : (∑' x, min (p x) (q x)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      ((ENNReal.tsum_le_tsum fun x => min_le_left _ _).trans_eq p.tsum_coe)
  have h1 : tvDist p q + ∑' x, min (p x) (q x) = 1 := by
    rw [tvDist, ← ENNReal.tsum_add, ← p.tsum_coe]
    exact tsum_congr fun x => tsub_add_min p q x
  have h2 : tvDist q p + ∑' x, min (p x) (q x) = 1 := by
    rw [tvDist, ← ENNReal.tsum_add, ← q.tsum_coe]
    exact tsum_congr fun x => by rw [min_comm]; exact tsub_add_min q p x
  exact (ENNReal.add_left_inj hmin).mp (h1.trans h2.symm)

/-- The expectation of a test function bounded by one changes by at most the total
variation. -/
lemma tsum_mul_le_add_tvDist {X : Type} (p q : PMF X) (F : X → ℝ≥0∞)
    (hF : ∀ x, F x ≤ 1) : ∑' x, p x * F x ≤ (∑' x, q x * F x) + tvDist p q := by
  rw [tvDist, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  calc p x * F x ≤ (q x + (p x - q x)) * F x := mul_le_mul_left le_add_tsub _
    _ = q x * F x + (p x - q x) * F x := add_mul _ _ _
    _ ≤ q x * F x + (p x - q x) * 1 := add_le_add le_rfl (mul_le_mul_right (hF x) _)
    _ = q x * F x + (p x - q x) := by rw [mul_one]

/-- **Total variation of mixtures**: the distance of two mixtures is at most the distance
of the mixing laws plus the mixture of the component distances. -/
lemma tvDist_bind_le {A B : Type} (w w' : PMF A) (f f' : A → PMF B) :
    tvDist (w.bind f) (w'.bind f') ≤ tvDist w w' + ∑' a, w a * tvDist (f a) (f' a) := by
  have key : ∀ b, (w.bind f) b - (w'.bind f') b
      ≤ (∑' a, (w a - w' a) * f' a b) + ∑' a, w a * (f a b - f' a b) := by
    intro b
    rw [tsub_le_iff_right, PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_add,
      ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun a => ?_
    calc w a * f a b ≤ w a * (f' a b + (f a b - f' a b)) := mul_le_mul_right le_add_tsub _
      _ = w a * f' a b + w a * (f a b - f' a b) := mul_add _ _ _
      _ ≤ (w' a + (w a - w' a)) * f' a b + w a * (f a b - f' a b) :=
        add_le_add (mul_le_mul_left le_add_tsub _) le_rfl
      _ = (w a - w' a) * f' a b + w a * (f a b - f' a b) + w' a * f' a b := by ring
  calc tvDist (w.bind f) (w'.bind f')
      ≤ ∑' b, ((∑' a, (w a - w' a) * f' a b) + ∑' a, w a * (f a b - f' a b)) :=
        ENNReal.tsum_le_tsum key
    _ = (∑' b, ∑' a, (w a - w' a) * f' a b) + ∑' b, ∑' a, w a * (f a b - f' a b) :=
        ENNReal.tsum_add
    _ = (∑' a, ∑' b, (w a - w' a) * f' a b) + ∑' a, ∑' b, w a * (f a b - f' a b) := by
        rw [ENNReal.tsum_comm (f := fun b a => (w a - w' a) * f' a b),
          ENNReal.tsum_comm (f := fun b a => w a * (f a b - f' a b))]
    _ = tvDist w w' + ∑' a, w a * tvDist (f a) (f' a) := by
        rw [tvDist]
        congr 1
        · refine tsum_congr fun a => ?_
          rw [ENNReal.tsum_mul_left, (f' a).tsum_coe, mul_one]
        · refine tsum_congr fun a => ?_
          rw [ENNReal.tsum_mul_left, tvDist]

/-- A pushforward contracts the total variation. -/
lemma tvDist_map_le {A B : Type} (p q : PMF A) (g : A → B) :
    tvDist (p.map g) (q.map g) ≤ tvDist p q := by
  have h := tvDist_bind_le p q (pure ∘ g) (pure ∘ g)
  change tvDist (p.bind (pure ∘ g)) (q.bind (pure ∘ g)) ≤ tvDist p q
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.tsum_eq_zero.mpr fun a => by rw [tvDist_self, mul_zero], add_zero]

/-- The total variation of two products is at most the sum of the marginal distances. -/
lemma tvDist_prodPMF_le {A B : Type} (p p' : PMF A) (q q' : PMF B) :
    tvDist (prodPMF p q) (prodPMF p' q') ≤ tvDist p p' + tvDist q q' := by
  have key : ∀ z : A × B, prodPMF p q z - prodPMF p' q' z
      ≤ (p z.1 - p' z.1) * q z.2 + p' z.1 * (q z.2 - q' z.2) := by
    intro z
    rw [tsub_le_iff_right, prodPMF_apply, prodPMF_apply]
    calc p z.1 * q z.2 ≤ (p' z.1 + (p z.1 - p' z.1)) * q z.2 := mul_le_mul_left le_add_tsub _
      _ = p' z.1 * q z.2 + (p z.1 - p' z.1) * q z.2 := add_mul _ _ _
      _ ≤ p' z.1 * (q' z.2 + (q z.2 - q' z.2)) + (p z.1 - p' z.1) * q z.2 :=
        add_le_add (mul_le_mul_right le_add_tsub _) le_rfl
      _ = (p z.1 - p' z.1) * q z.2 + p' z.1 * (q z.2 - q' z.2) + p' z.1 * q' z.2 := by ring
  calc tvDist (prodPMF p q) (prodPMF p' q')
      ≤ ∑' z : A × B, ((p z.1 - p' z.1) * q z.2 + p' z.1 * (q z.2 - q' z.2)) :=
        ENNReal.tsum_le_tsum key
    _ = (∑' z : A × B, (p z.1 - p' z.1) * q z.2) + ∑' z : A × B, p' z.1 * (q z.2 - q' z.2) :=
        ENNReal.tsum_add
    _ = tvDist p p' * 1 + 1 * tvDist q q' := by
        rw [tsum_prod_split (fun a => p a - p' a) (fun b => q b),
          tsum_prod_split (fun a => p' a) (fun b => q b - q' b), q.tsum_coe, p'.tsum_coe,
          tvDist, tvDist]
    _ = tvDist p p' + tvDist q q' := by rw [mul_one, one_mul]

/-! ### The level laws of two models -/

/-- The address count `2^{h+2} - 1 = 1 + 2 (2^{h+1} - 1)`. -/
lemma two_pow_sub_one_succ (h : ℕ) :
    (2 ^ (h + 2) - 1 : ℝ≥0∞) = 1 + 2 * (2 ^ (h + 1) - 1) := by
  have h1 : (1 : ℝ≥0∞) ≤ 2 ^ (h + 1) := one_le_pow₀ (by norm_num)
  symm
  apply ENNReal.eq_sub_of_add_eq ENNReal.one_ne_top
  calc (1 : ℝ≥0∞) + 2 * (2 ^ (h + 1) - 1) + 1 = 2 * (2 ^ (h + 1) - 1 + 1) := by ring
    _ = 2 * 2 ^ (h + 1) := by rw [tsub_add_cancel_of_le h1]
    _ = 2 ^ (h + 2) := by ring

/-- The bad indicator is at most one. -/
lemma badInd_le_one {X : Type} (R : X → X → Prop) (z y : X) : badInd R z y ≤ 1 := by
  unfold badInd
  split_ifs <;> simp

namespace Model

variable {V I : Type}

/-- Two models with the same fresh types, fresh law and distinguished state have the same
typed root laws. -/
lemma rootT_eq_of (M M' : Model V I) (hz : M.zero = M'.zero) (hμ : M.μ = M'.μ)
    (hf : M.fresh = M'.fresh) : M.rootT = M'.rootT := by
  funext t
  rw [rootT, rootT, rootLaw, rootLaw, hz, hμ, hf]

/-- **The level laws of two models**: if the kernels are within `d s` in total variation at
every type `s`, with `d`
nonincreasing along charged transitions, then the level laws at height `h` are within
`(2^{h+1} - 1) d s`, the number of addresses through depth `h` times the disagreement
bound at each. -/
theorem tvDist_rho_le_of_hered (M M' : Model V I) (hz : M.zero = M'.zero) (hμ : M.μ = M'.μ)
    (hf : M.fresh = M'.fresh) (d : I → ℝ≥0∞) (hd : ∀ s, tvDist (M.π s) (M'.π s) ≤ d s)
    (hher : ∀ s j, M.π s j ≠ 0 → d j.1 ≤ d s ∧ d j.2 ≤ d s) :
    ∀ h s, tvDist (M.rho s h) (M'.rho s h) ≤ (2 ^ (h + 1) - 1 : ℝ≥0∞) * d s := by
  intro h
  induction h with
  | zero =>
    intro s
    rw [rho_zero, rho_zero, rootT_eq_of M M' hz hμ hf, tvDist_self]
    exact zero_le
  | succ h ih =>
    intro s
    rw [rho_succ, rho_succ, rootT_eq_of M M' hz hμ hf]
    calc tvDist ((M'.rootT s).bind fun r => (M.childMix s h).map (branch r))
          ((M'.rootT s).bind fun r => (M'.childMix s h).map (branch r))
        ≤ tvDist (M'.rootT s) (M'.rootT s) + ∑' r, M'.rootT s r
            * tvDist ((M.childMix s h).map (branch r)) ((M'.childMix s h).map (branch r)) :=
          tvDist_bind_le _ _ _ _
      _ ≤ 0 + ∑' r, M'.rootT s r * tvDist (M.childMix s h) (M'.childMix s h) := by
          rw [tvDist_self]
          exact add_le_add le_rfl
            (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (tvDist_map_le _ _ _) _)
      _ = tvDist (M.childMix s h) (M'.childMix s h) := by
          rw [zero_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      _ ≤ tvDist (M.π s) (M'.π s) + ∑' j, M.π s j
            * tvDist (prodPMF (M.rho j.1 h) (M.rho j.2 h))
              (prodPMF (M'.rho j.1 h) (M'.rho j.2 h)) :=
          tvDist_bind_le _ _ _ _
      _ ≤ d s + ∑' j, M.π s j * (2 * ((2 ^ (h + 1) - 1) * d s)) := by
          refine add_le_add (hd s) (ENNReal.tsum_le_tsum fun j => ?_)
          by_cases hj : M.π s j = 0
          · rw [hj, zero_mul, zero_mul]
          · refine mul_le_mul_right ?_ _
            obtain ⟨h1, h2⟩ := hher s j hj
            calc tvDist (prodPMF (M.rho j.1 h) (M.rho j.2 h))
                  (prodPMF (M'.rho j.1 h) (M'.rho j.2 h))
                ≤ tvDist (M.rho j.1 h) (M'.rho j.1 h) + tvDist (M.rho j.2 h) (M'.rho j.2 h) :=
                  tvDist_prodPMF_le _ _ _ _
              _ ≤ (2 ^ (h + 1) - 1) * d j.1 + (2 ^ (h + 1) - 1) * d j.2 :=
                  add_le_add (ih j.1) (ih j.2)
              _ ≤ (2 ^ (h + 1) - 1) * d s + (2 ^ (h + 1) - 1) * d s :=
                  add_le_add (mul_le_mul_right h1 _) (mul_le_mul_right h2 _)
              _ = 2 * ((2 ^ (h + 1) - 1) * d s) := (two_mul _).symm
      _ = (1 + 2 * (2 ^ (h + 1) - 1)) * d s := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
          ring
      _ = (2 ^ (h + 1 + 1) - 1) * d s := by rw [two_pow_sub_one_succ]

/-- **The level laws under a uniform kernel distance**: kernels within `t` at fresh types
and equal at forced types give level laws within
`(2^{h+1} - 1) t` at height `h`. -/
theorem tvDist_rho_le (M M' : Model V I) (hz : M.zero = M'.zero) (hμ : M.μ = M'.μ)
    (hf : M.fresh = M'.fresh) (t : ℝ≥0∞)
    (hπ : ∀ s, tvDist (M.π s) (M'.π s) ≤ if M.fresh s then t else 0) :
    ∀ h s, tvDist (M.rho s h) (M'.rho s h) ≤ (2 ^ (h + 1) - 1 : ℝ≥0∞) * t :=
  M.tvDist_rho_le_of_hered M' hz hμ hf (fun _ => t)
    (fun s => (hπ s).trans (by split_ifs <;> simp)) (fun _ _ _ => ⟨le_rfl, le_rfl⟩)

/-- The failure probability of one model is at most that of the other plus the total
variation of the two initial level laws. -/
theorem failProb_le_add_tvDist (M M' : Model V I) (hR : M.R = M'.R) (s t : I) (h : ℕ) :
    M.failProb s t h ≤ M'.failProb s t h
      + (tvDist (M.rho s h) (M'.rho s h) + tvDist (M.rho t h) (M'.rho t h)) := by
  have hsim : M.sim h = M'.sim h := by
    show fullSim M.srel h = fullSim M'.srel h
    unfold srel
    rw [hR]
  have hq : ∀ x, qE (M.rho t h) (M'.sim h) x
      ≤ qE (M'.rho t h) (M'.sim h) x + tvDist (M.rho t h) (M'.rho t h) := by
    intro x
    rw [qE_eq_tsum_mul, qE_eq_tsum_mul]
    exact tsum_mul_le_add_tvDist _ _ _ fun y => badInd_le_one _ _ _
  unfold failProb failureD
  rw [hsim]
  calc ∑' x, M.rho s h x * qE (M.rho t h) (M'.sim h) x
      ≤ (∑' x, M'.rho s h x * qE (M.rho t h) (M'.sim h) x)
          + tvDist (M.rho s h) (M'.rho s h) :=
        tsum_mul_le_add_tvDist _ _ _ fun x => qE_le_one
    _ ≤ (∑' x, M'.rho s h x
          * (qE (M'.rho t h) (M'.sim h) x + tvDist (M.rho t h) (M'.rho t h)))
          + tvDist (M.rho s h) (M'.rho s h) :=
        add_le_add (ENNReal.tsum_le_tsum fun x => mul_le_mul_right (hq x) _) le_rfl
    _ = (∑' x, M'.rho s h x * qE (M'.rho t h) (M'.sim h) x)
          + tvDist (M.rho t h) (M'.rho t h) + tvDist (M.rho s h) (M'.rho s h) := by
        rw [tsum_congr fun x => mul_add (M'.rho s h x) _ _, ENNReal.tsum_add,
          ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ = _ := by ring

/-- **Failure under truncated kernels**: with kernels within `d s` at every type `s` and
`d` nonincreasing along charged transitions, the failure
probability of the first model at height `h` is at most that of the second plus
`(2^{h+1} - 1) (d s + d t)`, the two sides' errors at the initial types. -/
theorem failProb_le_truncated (M M' : Model V I) (hR : M.R = M'.R) (hz : M.zero = M'.zero)
    (hμ : M.μ = M'.μ) (hf : M.fresh = M'.fresh) (d : I → ℝ≥0∞)
    (hd : ∀ s, tvDist (M.π s) (M'.π s) ≤ d s)
    (hher : ∀ s j, M.π s j ≠ 0 → d j.1 ≤ d s ∧ d j.2 ≤ d s) (s t : I) (h : ℕ) :
    M.failProb s t h ≤ M'.failProb s t h + (2 ^ (h + 1) - 1 : ℝ≥0∞) * (d s + d t) := by
  refine (M.failProb_le_add_tvDist M' hR s t h).trans ?_
  rw [mul_add]
  exact add_le_add le_rfl (add_le_add (M.tvDist_rho_le_of_hered M' hz hμ hf d hd hher h s)
    (M.tvDist_rho_le_of_hered M' hz hμ hf d hd hher h t))

/-- With a uniform kernel distance `t`, the error is
`(2^{h+1} - 1) (t + t)`. -/
theorem failProb_le_truncated_uniform (M M' : Model V I) (hR : M.R = M'.R)
    (hz : M.zero = M'.zero) (hμ : M.μ = M'.μ) (hf : M.fresh = M'.fresh) (t : ℝ≥0∞)
    (hπ : ∀ s, tvDist (M.π s) (M'.π s) ≤ if M.fresh s then t else 0) (s u : I) (h : ℕ) :
    M.failProb s u h ≤ M'.failProb s u h + (2 ^ (h + 1) - 1 : ℝ≥0∞) * (t + t) :=
  M.failProb_le_truncated M' hR hz hμ hf (fun _ => t)
    (fun s => (hπ s).trans (by split_ifs <;> simp)) (fun _ _ _ => ⟨le_rfl, le_rfl⟩) s u h

end Model

/-! ### Relabelling the types -/

/-- The product of two pushforwards is the pushforward of the product. -/
lemma prodPMF_map_map {A B C D : Type} (p : PMF A) (q : PMF B) (f : A → C) (g : B → D) :
    prodPMF (p.map f) (q.map g) = (prodPMF p q).map (Prod.map f g) := by
  apply PMF.ext
  intro z
  simp only [prodPMF_apply, PMF.map_apply]
  rw [← tsum_prod_split (fun a => if z.1 = f a then p a else 0)
    (fun b => if z.2 = g b then q b else 0)]
  refine tsum_congr fun w => ?_
  by_cases h1 : z.1 = f w.1 <;> by_cases h2 : z.2 = g w.2 <;>
    simp [Prod.ext_iff, h1, h2]

/-- Two pushforwards along maps agreeing on the support coincide. -/
lemma map_congr_support {A B : Type} (p : PMF A) {f g : A → B}
    (h : ∀ a, p a ≠ 0 → f a = g a) : p.map f = p.map g := by
  apply PMF.ext
  intro b
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ha]

/-- Relabelling the types of a typed labelling along `ι`, keeping the states. -/
def labMap {V I I' : Type} (ι : I' → I) :
    (h : ℕ) → FullLab (I' × V) h → FullLab (I × V) h
  | 0, x => leaf (Prod.map ι id (rootLab 0 x))
  | h + 1, x =>
      branch (Prod.map ι id (rootLab (h + 1) x)) (labMap ι h x.2.1, labMap ι h x.2.2)

/-- Relabelling a leaf. -/
lemma labMap_leaf {V I I' : Type} (ι : I' → I) (s : I' × V) :
    labMap ι 0 (leaf s) = leaf (Prod.map ι id s) := rfl

/-- Relabelling a branch. -/
lemma labMap_branch {V I I' : Type} (ι : I' → I) (h : ℕ) (s : I' × V)
    (p : FullLab (I' × V) h × FullLab (I' × V) h) :
    labMap ι (h + 1) (branch s p)
      = branch (Prod.map ι id s) (labMap ι h p.1, labMap ι h p.2) := rfl

namespace Model

variable {V I : Type}

/-- An embedding of the types of `M'` into those of `M` over the same states: the states,
the fresh types and the kernels correspond, the kernel of `M` at an embedded type being the
pushforward of the kernel of `M'`. -/
structure IsEmbed {I' : Type} (M' : Model V I') (M : Model V I) (ι : I' → I) : Prop where
  hR : M'.R = M.R
  hzero : M'.zero = M.zero
  hmu : M'.μ = M.μ
  hfresh : ∀ t, M.fresh (ι t) ↔ M'.fresh t
  hpi : ∀ t, M.π (ι t) = (M'.π t).map (Prod.map ι ι)

namespace IsEmbed

variable {I' : Type} {M' : Model V I'} {M : Model V I} {ι : I' → I} (e : M'.IsEmbed M ι)
include e

/-- The root laws correspond. -/
lemma rootLaw (t : I') : M.rootLaw (ι t) = M'.rootLaw t := by
  rw [Model.rootLaw, Model.rootLaw, e.hzero, e.hmu]
  by_cases ht : M'.fresh t
  · rw [ite_eq_left ((e.hfresh t).mpr ht), ite_eq_left ht]
  · rw [ite_eq_right fun h => ht ((e.hfresh t).mp h), ite_eq_right ht]

/-- The typed root laws correspond. -/
lemma rootT (t : I') : M.rootT (ι t) = (M'.rootT t).map (Prod.map ι id) := by
  rw [Model.rootT, Model.rootT, e.rootLaw, PMF.map_comp]
  rfl

/-- The child-pair mixtures correspond once the level laws do. -/
lemma childMix_of_rho (h : ℕ)
    (hrho : ∀ t, M.rho (ι t) h = (M'.rho t h).map (labMap ι h)) (t : I') :
    M.childMix (ι t) h = (M'.childMix t h).map (Prod.map (labMap ι h) (labMap ι h)) := by
  rw [Model.childMix, Model.childMix, e.hpi, PMF.bind_map, PMF.map_bind]
  refine congrArg _ (funext fun j => ?_)
  show prodPMF (M.rho (ι j.1) h) (M.rho (ι j.2) h) = _
  rw [hrho, hrho, prodPMF_map_map]

/-- **The level laws correspond**: the level law of `M` at an embedded type is the
relabelling of the level law of `M'`. -/
theorem rho : ∀ (h : ℕ) (t : I'), M.rho (ι t) h = (M'.rho t h).map (labMap ι h) := by
  intro h
  induction h with
  | zero =>
    intro t
    rw [rho_zero, rho_zero, e.rootT, PMF.map_comp, PMF.map_comp]
    rfl
  | succ h ih =>
    intro t
    rw [rho_succ, rho_succ, e.rootT, e.childMix_of_rho h ih, PMF.bind_map, PMF.map_bind]
    refine congrArg _ (funext fun s => ?_)
    show ((M'.childMix t h).map (Prod.map (labMap ι h) (labMap ι h))).map
      (branch (Prod.map ι id s)) = _
    rw [PMF.map_comp, PMF.map_comp]
    rfl

/-- Matching only compares states, so it is invariant under relabelling the types. -/
theorem sim (h : ℕ) : ∀ x y : FullLab (I' × V) h,
    fullSim M.srel h (labMap ι h x) (labMap ι h y) ↔ fullSim M'.srel h x y := by
  induction h with
  | zero =>
    intro x y
    show fullSim M.srel 0 (leaf (Prod.map ι id x)) (leaf (Prod.map ι id y))
      ↔ fullSim M'.srel 0 (leaf x) (leaf y)
    rw [fullSim_leaf, fullSim_leaf M'.srel x y]
    show M.R x.2 y.2 ↔ M'.R x.2 y.2
    rw [e.hR]
  | succ h ih =>
    intro x y
    show fullSim M.srel (h + 1)
        (branch (Prod.map ι id x.1) (labMap ι h x.2.1, labMap ι h x.2.2))
        (branch (Prod.map ι id y.1) (labMap ι h y.2.1, labMap ι h y.2.2))
      ↔ fullSim M'.srel (h + 1) (branch x.1 (x.2.1, x.2.2)) (branch y.1 (y.2.1, y.2.2))
    rw [fullSim_branch, fullSim_branch]
    have hroot : M.srel (Prod.map ι id x.1) (Prod.map ι id y.1) ↔ M'.srel x.1 y.1 := by
      show M.R x.1.2 y.1.2 ↔ M'.R x.1.2 y.1.2
      rw [e.hR]
    simp only [SquareRel, hroot, ih]

/-- **The failure probabilities correspond** under an embedding of the types. -/
theorem failProb (s t : I') (h : ℕ) : M.failProb (ι s) (ι t) h = M'.failProb s t h := by
  rw [Model.failProb, Model.failProb, failureD, failureD, e.rho h s, e.rho h t, tsum_map_mul]
  refine tsum_congr fun x => ?_
  congr 1
  rw [qE_map, qE_eq_tsum_mul]
  refine tsum_congr fun y => ?_
  congr 1
  unfold badInd
  by_cases hs : M'.sim h x y
  · rw [ite_eq_left ((e.sim h x y).mpr hs), ite_eq_left hs]
  · rw [ite_eq_right fun hc => hs ((e.sim h x y).mp hc), ite_eq_right hs]

end IsEmbed

end Model

/-! ### The truncated presentation -/

/-- The side of a type built from a remaining tree. -/
lemma typeOf_fst (σ : Bool) (τ : MTree) : (typeOf σ τ).1 = σ := by
  cases τ <;> rfl

/-- The root pair of a remaining tree stays on its side. -/
lemma rootPair_fst (σ : Bool) (τ : MTree) :
    (rootPair σ τ).1.1 = σ ∧ (rootPair σ τ).2.1 = σ := by
  cases τ with
  | leaf => exact ⟨rfl, rfl⟩
  | node l r => exact ⟨typeOf_fst σ l, typeOf_fst σ r⟩
  | gnode l r => exact ⟨typeOf_fst σ l, typeOf_fst σ r⟩

namespace Presentation

variable (P : Presentation)

/-- The raw kernel preserves the side (`sec:types-degrees`). -/
lemma rawKernel_side (t : PType) (p : PType × PType) (hp : P.rawKernel t p ≠ 0) :
    p.1.1 = t.1 ∧ p.2.1 = t.1 := by
  obtain ⟨σ, oτ⟩ := t
  cases oτ with
  | none =>
    obtain ⟨k, -, rfl⟩ := (P.rawKernel_fresh_ne_zero_iff σ p).mp hp
    exact rootPair_fst σ _
  | some τ =>
    obtain rfl := (P.rawKernel_forced_ne_zero_iff σ τ p).mp hp
    exact rootPair_fst σ τ

/-- The live kernel preserves the side (`sec:types-degrees`). -/
lemma kernelL_side (t : P.Live) (j : P.Live × P.Live) (hj : P.kernelL t j ≠ 0) :
    j.1.1.1 = t.1.1 ∧ j.2.1.1 = t.1.1 :=
  P.rawKernel_side t.1 (j.1.1, j.2.1) ((P.kernelL_ne_zero_iff t j).mp hj)

/-- The tail mass `t_σ(N) = ν_σ{k > N}`. -/
noncomputable def tail (σ : Bool) (N : ℕ) : ℝ≥0∞ := ∑' k, if N < k then P.ν σ k else 0

/-- The event `k ≤ N` is charged once `N` bounds the core arities. -/
lemma exists_le_charged (N : ℕ) (hN : ∀ a ∈ P.S, a ≤ N) (σ : Bool) :
    ∃ k ∈ {k : ℕ | k ≤ N}, k ∈ (P.ν σ).support := by
  obtain ⟨a, ha⟩ := P.S_nonempty
  exact ⟨a, hN a ha,
    (PMF.mem_support_iff _ _).mpr ((P.mem_supp σ a).mpr (P.S_subset_supp σ ha))⟩

/-- The truncated arity law `ν_σ^{(N)}`: `ν_σ` conditioned on `k ≤ N`. -/
noncomputable def nuTrunc (N : ℕ) (hN : ∀ a ∈ P.S, a ≤ N) (σ : Bool) : PMF ℕ :=
  (P.ν σ).filter {k | k ≤ N} (P.exists_le_charged N hN σ)

/-- **The truncated presentation**: the arity laws conditioned on `k ≤ N`, for `N` at least
every core arity, with the same core, core profiles and
composite profiles; its supports still contain the core, hence generate the common
semigroup. -/
noncomputable def truncate (N : ℕ) (hN : ∀ a ∈ P.S, a ≤ N) : Presentation where
  S := P.S
  D := P.D
  ν := P.nuTrunc N hN
  supp := fun σ => (P.supp σ).filter fun k => k ≤ N
  C := P.C
  mem_supp := by
    intro σ k
    rw [nuTrunc, PMF.filter_apply_ne_zero_iff, Finset.mem_filter, PMF.mem_support_iff,
      P.mem_supp, Set.mem_ofPred_eq]
    exact and_comm
  S_nonempty := P.S_nonempty
  two_le_S := P.two_le_S
  D_leaves := P.D_leaves
  D_noGraft := P.D_noGraft
  D_node := P.D_node
  S_subset_supp := fun σ a ha => Finset.mem_filter.mpr ⟨P.S_subset_supp σ ha, hN a ha⟩
  two_le_supp := fun σ k hk => P.two_le_supp σ k (Finset.mem_filter.mp hk).1
  C_leaves := fun σ k hk => P.C_leaves σ k (Finset.mem_filter.mp hk).1
  C_gnode := fun σ k hk => P.C_gnode σ k (Finset.mem_filter.mp hk).1
  C_allComp := fun σ k hk => P.C_allComp σ k (Finset.mem_filter.mp hk).1
  C_core := P.C_core

variable (N : ℕ) (hN : ∀ a ∈ P.S, a ≤ N)

/-- The truncation keeps the core. -/
@[simp] lemma truncate_S : (P.truncate N hN).S = P.S := rfl

/-- The truncation keeps the composite profiles. -/
@[simp] lemma truncate_C : (P.truncate N hN).C = P.C := rfl

/-- The support of the truncation is the support restricted to `k ≤ N`. -/
@[simp] lemma truncate_supp (σ : Bool) :
    (P.truncate N hN).supp σ = (P.supp σ).filter fun k => k ≤ N := rfl

/-- The arity law of the truncation is the conditioned law. -/
@[simp] lemma truncate_nu (σ : Bool) : (P.truncate N hN).ν σ = P.nuTrunc N hN σ := rfl

/-- **The kernel distance of the truncation is the tail mass**:
`∑_k (ν_σ(k) - ν_σ^{(N)}(k)) = t_σ(N)`, since the conditioned law dominates `ν_σ` on
`k ≤ N` and vanishes on `k > N`. -/
theorem truncate_tail (σ : Bool) : tvDist (P.ν σ) ((P.truncate N hN).ν σ) = P.tail σ N := by
  rw [tvDist, tail]
  refine tsum_congr fun k => ?_
  rw [truncate_nu, nuTrunc, PMF.filter_apply]
  by_cases hk : N < k
  · rw [ite_eq_left hk, Set.indicator_of_notMem (by simp only [Set.mem_ofPred_eq]; omega),
      zero_mul, tsub_zero]
  · rw [ite_eq_right hk]
    apply tsub_eq_zero_of_le
    rw [Set.indicator_of_mem (by simp only [Set.mem_ofPred_eq]; omega)]
    refine le_mul_of_one_le_right zero_le ?_
    rw [ENNReal.one_le_inv]
    exact (ENNReal.tsum_le_tsum fun a => Set.indicator_le_self _ _ a).trans_eq
      (P.ν σ).tsum_coe

/-- The live types of the truncation are live types of the presentation. -/
lemma truncate_live_subset : (P.truncate N hN).live ⊆ P.live := by
  intro t ht
  obtain ⟨σ, oτ⟩ := t
  cases oτ with
  | none => exact P.fresh_mem_live σ
  | some τ =>
    rw [mem_live_some_iff] at ht ⊢
    obtain ⟨k, hk, h1, h2, h3⟩ := ht
    exact ⟨k, (Finset.mem_filter.mp hk).1, h1, h2, h3⟩

/-- The inclusion of the truncated live types into the live types. -/
def truncLive (t : (P.truncate N hN).Live) : P.Live := ⟨t.1, P.truncate_live_subset N hN t.2⟩

variable {V : Type} (R : V → V → Prop) (zero : V) (μ : PMF V)

/-- **The truncated kernel on the original live types**: the model with the truncated
arity laws, carried by the live types of `P`. It is the process of the truncated
presentation (`failProb_toModelTrunc_eq`) and it is at kernel distance `t_σ(N)` from the
model of `P` on side `σ` (`tvDist_kernel_truncate`). -/
noncomputable def toModelTrunc : Model V P.Live where
  R := R
  zero := zero
  μ := μ
  fresh := fun t => t.1.2 = none
  π := fun t => ((P.truncate N hN).rawKernel t.1).map fun p => (P.toLive p.1, P.toLive p.2)

/-- The kernels of the presentation and of its truncation are within the tail mass of the
type's side; at forced types they agree. -/
theorem tvDist_kernel_truncate (t : P.Live) :
    tvDist ((P.toModel R zero μ).π t) ((P.toModelTrunc N hN R zero μ).π t)
      ≤ P.tail t.1.1 N := by
  obtain ⟨⟨σ, oτ⟩, ht⟩ := t
  cases oτ with
  | none =>
    show tvDist ((P.rawKernel (σ, none)).map _)
      (((P.truncate N hN).rawKernel (σ, none)).map _) ≤ P.tail σ N
    rw [rawKernel_fresh, rawKernel_fresh, PMF.map_comp, PMF.map_comp, truncate_C]
    exact (tvDist_map_le _ _ _).trans_eq (P.truncate_tail N hN σ)
  | some τ =>
    show tvDist ((P.rawKernel (σ, some τ)).map _)
      (((P.truncate N hN).rawKernel (σ, some τ)).map _) ≤ _
    rw [rawKernel_forced, rawKernel_forced, tvDist_self]
    exact zero_le

/-- The model of the truncated presentation embeds into the truncated kernel on the
original live types. -/
theorem isEmbed_truncate :
    ((P.truncate N hN).toModel R zero μ).IsEmbed (P.toModelTrunc N hN R zero μ)
      (P.truncLive N hN) where
  hR := rfl
  hzero := rfl
  hmu := rfl
  hfresh := fun _ => Iff.rfl
  hpi := by
    intro t
    show ((P.truncate N hN).rawKernel t.1).map _
      = (((P.truncate N hN).rawKernel t.1).map _).map _
    rw [PMF.map_comp]
    apply map_congr_support
    intro p hp
    obtain ⟨h1, h2⟩ := (P.truncate N hN).rawKernel_live t p hp
    show (P.toLive p.1, P.toLive p.2)
      = (P.truncLive N hN ((P.truncate N hN).toLive p.1),
          P.truncLive N hN ((P.truncate N hN).toLive p.2))
    rw [toLive_of_mem _ h1, toLive_of_mem _ h2,
      P.toLive_of_mem (P.truncate_live_subset N hN h1),
      P.toLive_of_mem (P.truncate_live_subset N hN h2)]
    rfl

/-- **The truncated kernel on the original live types is the process of the truncated
presentation**: the failure probabilities between the fresh types agree. -/
theorem failProb_toModelTrunc_eq (σ σ' : Bool) (h : ℕ) :
    (P.toModelTrunc N hN R zero μ).failProb (P.freshL σ) (P.freshL σ') h
      = ((P.truncate N hN).toModel R zero μ).failProb ((P.truncate N hN).freshL σ)
          ((P.truncate N hN).freshL σ') h := by
  have hσ : P.truncLive N hN ((P.truncate N hN).freshL σ) = P.freshL σ := rfl
  have hσ' : P.truncLive N hN ((P.truncate N hN).freshL σ') = P.freshL σ' := rfl
  rw [← hσ, ← hσ']
  exact (P.isEmbed_truncate N hN R zero μ).failProb ((P.truncate N hN).freshL σ)
    ((P.truncate N hN).freshL σ') h

/-- **Failure under presentation truncation**: if `M_N` bounds the failure probability of
the truncated presentation between the fresh types of sides `σ`, `σ'` at
height `h`, then the failure probability of the presentation itself is at most
`M_N + (2^{h+1} - 1) (t_σ(N) + t_{σ'}(N))`. -/
theorem failProb_le_truncate (h : ℕ) (σ σ' : Bool) (MN : ℝ≥0∞)
    (hMN : ((P.truncate N hN).toModel R zero μ).failProb ((P.truncate N hN).freshL σ)
      ((P.truncate N hN).freshL σ') h ≤ MN) :
    (P.toModel R zero μ).failProb (P.freshL σ) (P.freshL σ') h
      ≤ MN + (2 ^ (h + 1) - 1 : ℝ≥0∞) * (P.tail σ N + P.tail σ' N) := by
  have hmain := (P.toModel R zero μ).failProb_le_truncated (P.toModelTrunc N hN R zero μ)
    rfl rfl rfl rfl (fun t => P.tail t.1.1 N) (P.tvDist_kernel_truncate N hN R zero μ)
    (fun t j hj => by
      obtain ⟨h1, h2⟩ := P.kernelL_side t j hj
      exact ⟨by rw [h1], by rw [h2]⟩)
    (P.freshL σ) (P.freshL σ') h
  rw [P.failProb_toModelTrunc_eq] at hmain
  exact hmain.trans (add_le_add hMN le_rfl)

end Presentation

end GraphMarkovMatching.Stopped
