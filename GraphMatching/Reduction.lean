/-
`sec:reduction` of `graph_matching_selfcontained.tex`, the reduction (`thm:reduction`).

The recursion is run at a free exponent and under hypotheses, not with fixed constants:
all it asks of the analysis is a one-step bound with constants `A`, `B` (`eq:one-step`)
and a product bound with a constant `c` (`eq:product-bound`).

    Φ_h := Φ_α(μ_h, ≈^leaf_h),   A + B·Φ_0 ≤ ρ ≤ 1  ⟹  Φ_h ≤ ρ^h Φ_0
    Θ_h := Φ_α(μ_h, ≈_h),        1 + (1+cη)(AK + BK²η) ≤ K  ⟹  Θ_h ≤ K η

The second hypothesis is `eq:full-hyp` with the truncated subtraction of `ℝ≥0∞`
avoided: the paper writes that inequality as `(1+cη)(A𝔎 + B𝔎²η) ≤ 𝔎 - 1`, and its free
constant `𝔎` is the binder `K` here.

`thm:contraction` and `thm:product` supply the two hypotheses at every `α ≥ 1`, with
`A = A_α`, `B = B_α` and `c = 2α` (`oneStepA`, `prodStepA`); running the recursion on
them is `thm:reduction` as the paper states it (`leaf_matching_boundA`,
`full_matching_boundA`).

The failure probability of matching two independent labellings is the mean bad degree
`𝔼[q]`, and `q ≤ φ_α(q)` gives `𝔼[q] ≤ Φ_h`. The `α = 5/2` instances close the file.
-/
import GraphMatching.Tree
import GraphMatching.Contraction

namespace GraphMatching

open scoped ENNReal Classical

/-! ### The mean bad degree is below the potential -/

variable {X : Type*}

/-- `𝔼[q] ≤ Φ_α`: the failure probability (mean bad degree) is at most the
potential, since `q ≤ φ_α(q)` on the support (`eq:phi-dominates`). The exponent
enters only through that inequality, so `α ≥ 0` is all it asks. -/
lemma meanBad_le_PhiA {α : ℝ} (hα : 0 ≤ α) {μ : PMF X} {R : X → X → Prop}
    (hrefl : ∀ x, R x x) :
    ∑' x, μ x * qE μ R x ≤ PhiA α μ R := by
  rw [PhiA]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : μ x = 0
  · simp [hx]
  · have hq : μ x * qE μ R x = μ x * ENNReal.ofReal (q μ R x) := by
      rw [q, ENNReal.ofReal_toReal qE_ne_top]
    rw [hq]
    exact mul_q_le_summandA hα (hrefl x) hx

/-- `𝔼[q] ≤ Φ` at `α = 5/2`. -/
lemma meanBad_le_Phi {μ : PMF X} {R : X → X → Prop} (hrefl : ∀ x, R x x) :
    ∑' x, μ x * qE μ R x ≤ Phi μ R :=
  meanBad_le_PhiA alpha_nonneg hrefl

universe u
variable {V : Type u}

/-! ### The two analytic inputs, as hypotheses

`OneStepA α A B` is `eq:one-step` and `ProdStepA α c` is `eq:product-bound`. The
reduction uses nothing else about the weight, and nothing at all about the exponent
beyond what these two carry. -/

/-- **`eq:one-step` as a hypothesis**: at exponent `α` the symmetrised square contracts
with constants `A` (linear) and `B` (quadratic). -/
def OneStepA (α : ℝ) (A B : ℝ≥0∞) : Prop :=
  ∀ (W : Type u) (ν : PMF W) (S : W → W → Prop), (∀ x, S x x) → (∀ a b, S a b → S b a) →
    PhiA α (prodPMF ν ν) (SquareRel S) ≤ A * PhiA α ν S + B * PhiA α ν S ^ 2

/-- `eq:one-step` as a hypothesis at `α = 5/2`. -/
abbrev OneStep (A B : ℝ≥0∞) : Prop := OneStepA.{u} alpha A B

/-- **`eq:product-bound` as a hypothesis**: at exponent `α` the product of two relations
carries the factor `c` on the cross term. -/
def ProdStepA (α : ℝ) (c : ℝ≥0∞) : Prop :=
  ∀ (W₁ W₂ : Type u) (ν₁ : PMF W₁) (ν₂ : PMF W₂)
      (S₁ : W₁ → W₁ → Prop) (S₂ : W₂ → W₂ → Prop),
    (∀ x, S₁ x x) → (∀ x, S₂ x x) →
    PhiA α (prodPMF ν₁ ν₂) (ProdRel S₁ S₂)
      ≤ PhiA α ν₁ S₁ + PhiA α ν₂ S₂ + c * (PhiA α ν₁ S₁ * PhiA α ν₂ S₂)

/-- `eq:product-bound` as a hypothesis at `α = 5/2`. -/
abbrev ProdStep (c : ℝ≥0∞) : Prop := ProdStepA.{u} alpha c

/-! ### The potential of the leaf recursion, and its decay -/

/-- `Φ_h = Φ_α(μ_h, ≈^leaf_h)`, the potential of the level-`h` leaf relation. -/
noncomputable def PhiLeafA (α : ℝ) (μ : PMF V) (R₀ : V → V → Prop) (h : ℕ) : ℝ≥0∞ :=
  PhiA α (leafMu μ h) (leafSim R₀ h)

/-- `Φ_h` at `α = 5/2`. -/
noncomputable def PhiLeaf (μ : PMF V) (R₀ : V → V → Prop) (h : ℕ) : ℝ≥0∞ :=
  PhiLeafA alpha μ R₀ h

@[simp] lemma PhiLeafA_zero (α : ℝ) (μ : PMF V) (R₀ : V → V → Prop) :
    PhiLeafA α μ R₀ 0 = PhiA α μ R₀ := by rw [PhiLeafA, leafSim_zero]; rfl

@[simp] lemma PhiLeaf_zero (μ : PMF V) (R₀ : V → V → Prop) :
    PhiLeaf μ R₀ 0 = Phi μ R₀ := PhiLeafA_zero alpha μ R₀

/-- **`eq:leaf-rec` applied to Φ**: one contraction step, `Φ_{h+1} ≤ ρ Φ_h` as soon as
`A + B Φ_h ≤ ρ`. This is `eq:strict`. -/
lemma PhiLeafA_succ_le_of {α : ℝ} {A B ρ : ℝ≥0∞} (hc : OneStepA.{u} α A B)
    (μ : PMF V) (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v)
    (hsymm : ∀ a b, R₀ a b → R₀ b a) (h : ℕ) (hsmall : A + B * PhiLeafA α μ R₀ h ≤ ρ) :
    PhiLeafA α μ R₀ (h + 1) ≤ ρ * PhiLeafA α μ R₀ h := by
  rw [PhiLeafA, PhiLeafA] at *
  rw [leafSim_succ, leafMu_succ]
  calc PhiA α (prodPMF (leafMu μ h) (leafMu μ h)) (SquareRel (leafSim R₀ h))
      ≤ A * PhiA α (leafMu μ h) (leafSim R₀ h)
          + B * PhiA α (leafMu μ h) (leafSim R₀ h) ^ 2 :=
        hc _ (leafMu μ h) (leafSim R₀ h) (leafSim_refl R₀ hrefl h) (leafSim_symm R₀ hsymm h)
    _ = (A + B * PhiA α (leafMu μ h) (leafSim R₀ h))
          * PhiA α (leafMu μ h) (leafSim R₀ h) := by ring
    _ ≤ ρ * PhiA α (leafMu μ h) (leafSim R₀ h) := by gcongr

/-- **`eq:leaf-red`** for the potential: geometric decay `Φ_h ≤ ρ^h Φ_0` under the
hypothesis `A + B Φ_0 ≤ ρ ≤ 1` of `thm:reduction`. -/
theorem PhiLeafA_le_of {α : ℝ} {A B ρ : ℝ≥0∞} (hc : OneStepA.{u} α A B)
    (μ : PMF V) (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v)
    (hsymm : ∀ a b, R₀ a b → R₀ b a) (h0 : A + B * PhiA α μ R₀ ≤ ρ) (hρ : ρ ≤ 1) (h : ℕ) :
    PhiLeafA α μ R₀ h ≤ ρ ^ h * PhiA α μ R₀ := by
  induction h with
  | zero => simp
  | succ h ih =>
      have hpow : ρ ^ h ≤ 1 := pow_le_one₀ zero_le hρ
      have hbound : PhiLeafA α μ R₀ h ≤ PhiA α μ R₀ := by
        calc PhiLeafA α μ R₀ h ≤ ρ ^ h * PhiA α μ R₀ := ih
          _ ≤ 1 * PhiA α μ R₀ := by gcongr
          _ = PhiA α μ R₀ := one_mul _
      have hsmall : A + B * PhiLeafA α μ R₀ h ≤ ρ :=
        le_trans (by gcongr) h0
      calc PhiLeafA α μ R₀ (h + 1)
          ≤ ρ * PhiLeafA α μ R₀ h := PhiLeafA_succ_le_of hc μ R₀ hrefl hsymm h hsmall
        _ ≤ ρ * (ρ ^ h * PhiA α μ R₀) := by gcongr
        _ = ρ ^ (h + 1) * PhiA α μ R₀ := by ring

/-- **`thm:reduction`, leaf case (`eq:leaf-red`)**: the probability that two
independent leaf labellings of `𝔹_h` admit no matching automorphism is at most
`ρ^h Φ_0`. -/
theorem leaf_matching_boundA_of {α : ℝ} (hα : 0 ≤ α) {A B ρ : ℝ≥0∞}
    (hc : OneStepA.{u} α A B)
    (μ : PMF V) (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v)
    (hsymm : ∀ a b, R₀ a b → R₀ b a) (h0 : A + B * PhiA α μ R₀ ≤ ρ) (hρ : ρ ≤ 1) (h : ℕ) :
    ∑' x, leafMu μ h x * qE (leafMu μ h) (leafSim R₀ h) x
      ≤ ρ ^ h * PhiA α μ R₀ :=
  le_trans (meanBad_le_PhiA hα (leafSim_refl R₀ hrefl h))
    (PhiLeafA_le_of hc μ R₀ hrefl hsymm h0 hρ h)

/-! ### The full case -/

/-- `Θ_h = Φ_α(μ_h, ≈_h)`, the potential of the level-`h` full relation. -/
noncomputable def PhiFullA (α : ℝ) (μ : PMF V) (R₀ : V → V → Prop) (h : ℕ) : ℝ≥0∞ :=
  PhiA α (fullMu μ h) (fullSim R₀ h)

/-- `Θ_h` at `α = 5/2`. -/
noncomputable def PhiFull (μ : PMF V) (R₀ : V → V → Prop) (h : ℕ) : ℝ≥0∞ :=
  PhiFullA alpha μ R₀ h

@[simp] lemma PhiFullA_zero (α : ℝ) (μ : PMF V) (R₀ : V → V → Prop) :
    PhiFullA α μ R₀ 0 = PhiA α μ R₀ := by rw [PhiFullA, fullSim_zero]; rfl

@[simp] lemma PhiFull_zero (μ : PMF V) (R₀ : V → V → Prop) :
    PhiFull μ R₀ 0 = Phi μ R₀ := PhiFullA_zero alpha μ R₀

/-- **`eq:theta-rec`**: one step of the full recursion. `OneStepA` bounds the child
pair (`eq:sigma`), then `ProdStepA` adjoins the root factor `η = Φ_α(μ, R₀)`. -/
lemma PhiFullA_succ_le_of {α : ℝ} {A B c : ℝ≥0∞} (hc : OneStepA.{u} α A B)
    (hp : ProdStepA.{u} α c)
    (μ : PMF V) (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v)
    (hsymm : ∀ a b, R₀ a b → R₀ b a) (h : ℕ) :
    PhiFullA α μ R₀ (h + 1)
      ≤ PhiA α μ R₀
        + (1 + c * PhiA α μ R₀) * (A * PhiFullA α μ R₀ h + B * PhiFullA α μ R₀ h ^ 2) := by
  have hr : ∀ x, fullSim R₀ h x x := fullSim_refl R₀ hrefl h
  have hs : ∀ a b, fullSim R₀ h a b → fullSim R₀ h b a := fullSim_symm R₀ hsymm h
  simp only [PhiFullA]
  rw [fullSim_succ, fullMu_succ]
  have hPhiSq : PhiA α (prodPMF (fullMu μ h) (fullMu μ h)) (SquareRel (fullSim R₀ h))
      ≤ A * PhiA α (fullMu μ h) (fullSim R₀ h)
        + B * PhiA α (fullMu μ h) (fullSim R₀ h) ^ 2 :=
    hc _ (fullMu μ h) (fullSim R₀ h) hr hs
  calc PhiA α (prodPMF μ (prodPMF (fullMu μ h) (fullMu μ h)))
          (ProdRel R₀ (SquareRel (fullSim R₀ h)))
      ≤ PhiA α μ R₀
          + PhiA α (prodPMF (fullMu μ h) (fullMu μ h)) (SquareRel (fullSim R₀ h))
          + c * (PhiA α μ R₀
            * PhiA α (prodPMF (fullMu μ h) (fullMu μ h)) (SquareRel (fullSim R₀ h))) :=
        hp _ _ μ (prodPMF (fullMu μ h) (fullMu μ h)) R₀ (SquareRel (fullSim R₀ h))
          hrefl (SquareRel_refl hr)
    _ ≤ PhiA α μ R₀
          + (A * PhiA α (fullMu μ h) (fullSim R₀ h)
             + B * PhiA α (fullMu μ h) (fullSim R₀ h) ^ 2)
          + c * (PhiA α μ R₀
            * (A * PhiA α (fullMu μ h) (fullSim R₀ h)
               + B * PhiA α (fullMu μ h) (fullSim R₀ h) ^ 2)) := by gcongr
    _ = PhiA α μ R₀ + (1 + c * PhiA α μ R₀)
          * (A * PhiA α (fullMu μ h) (fullSim R₀ h)
             + B * PhiA α (fullMu μ h) (fullSim R₀ h) ^ 2) := by ring

/-- **F-invariance** under `eq:full-hyp`: `[0, Kη]` is invariant under the full
recursion map. In `ℝ≥0∞` the whole step is monotonicity, with no passage to `ℝ`:
the hypothesis is used once, as `η · (1 + X) ≤ η · K`. -/
lemma F_invariant_of {A B c η K t : ℝ≥0∞}
    (hyp : 1 + (1 + c * η) * (A * K + B * K ^ 2 * η) ≤ K) (ht : t ≤ K * η) :
    η + (1 + c * η) * (A * t + B * t ^ 2) ≤ K * η := by
  have hinner : A * t + B * t ^ 2 ≤ A * (K * η) + B * (K * η) ^ 2 := by gcongr
  calc η + (1 + c * η) * (A * t + B * t ^ 2)
      ≤ η + (1 + c * η) * (A * (K * η) + B * (K * η) ^ 2) := by gcongr
    _ = η * (1 + (1 + c * η) * (A * K + B * K ^ 2 * η)) := by ring
    _ ≤ η * K := by gcongr
    _ = K * η := by ring

/-- **`eq:theta-uniform`**: the full potential stays below `K η` uniformly in `h`,
under `eq:full-hyp`. -/
theorem PhiFullA_le_of {α : ℝ} {A B c K : ℝ≥0∞} (hc : OneStepA.{u} α A B)
    (hp : ProdStepA.{u} α c)
    (μ : PMF V) (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v)
    (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (hyp : 1 + (1 + c * PhiA α μ R₀) * (A * K + B * K ^ 2 * PhiA α μ R₀) ≤ K) (h : ℕ) :
    PhiFullA α μ R₀ h ≤ K * PhiA α μ R₀ := by
  have hK : (1 : ℝ≥0∞) ≤ K := le_trans le_self_add hyp
  induction h with
  | zero => rw [PhiFullA_zero]; exact le_mul_of_one_le_left zero_le hK
  | succ h ih =>
      exact le_trans (PhiFullA_succ_le_of hc hp μ R₀ hrefl hsymm h) (F_invariant_of hyp ih)

/-- **`thm:reduction`, full case (`eq:full-red`)**: the failure probability for full
labellings is at most `K η`, uniformly in `h`. -/
theorem full_matching_boundA_of {α : ℝ} (hα : 0 ≤ α) {A B c K : ℝ≥0∞}
    (hc : OneStepA.{u} α A B) (hp : ProdStepA.{u} α c)
    (μ : PMF V) (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v)
    (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (hyp : 1 + (1 + c * PhiA α μ R₀) * (A * K + B * K ^ 2 * PhiA α μ R₀) ≤ K) (h : ℕ) :
    ∑' x, fullMu μ h x * qE (fullMu μ h) (fullSim R₀ h) x ≤ K * PhiA α μ R₀ :=
  le_trans (meanBad_le_PhiA hα (fullSim_refl R₀ hrefl h))
    (PhiFullA_le_of hc hp μ R₀ hrefl hsymm hyp h)

/-! ### The two analytic inputs at a general exponent

`thm:contraction` and `thm:product` discharge the two hypotheses at every `α ≥ 1`,
with the constants `A_α`, `B_α` of `eq:contraction-constants` and `c = 2α`. -/

/-- **`eq:one-step`**: `thm:contraction` is `OneStepA` at `A_α`, `B_α`. -/
lemma oneStepA {α : ℝ} (hα : 1 ≤ α) :
    OneStepA.{u} α (ENNReal.ofReal (AA α)) (ENNReal.ofReal (BA α)) :=
  fun _ ν S hr hs => Phi_square_leA hα ν S hr hs

/-- **`eq:product-bound`**: `thm:product` is `ProdStepA` at `c = 2α`. -/
lemma prodStepA {α : ℝ} (hα : 1 ≤ α) : ProdStepA.{u} α (ENNReal.ofReal (2 * α)) :=
  fun _ _ ν₁ ν₂ S₁ S₂ h₁ h₂ => PhiA_prodPMF_le hα ν₁ ν₂ S₁ S₂ h₁ h₂

/-! ### `thm:reduction` at a general exponent -/

/-- **`eq:leaf-red`** for the potential, at a general exponent: `Φ_h ≤ ρ^h Φ_0` whenever
`ρ` dominates `A_α + B_α Φ_0` and `ρ ≤ 1`. -/
theorem PhiLeafA_le {α : ℝ} (hα : 1 ≤ α) {ρ : ℝ≥0∞} (μ : PMF V) (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (h0 : ENNReal.ofReal (AA α) + ENNReal.ofReal (BA α) * PhiA α μ R₀ ≤ ρ) (hρ : ρ ≤ 1)
    (h : ℕ) :
    PhiLeafA α μ R₀ h ≤ ρ ^ h * PhiA α μ R₀ :=
  PhiLeafA_le_of (oneStepA hα) μ R₀ hrefl hsymm h0 hρ h

/-- **`thm:reduction`, leaf case (`eq:leaf-red`)** at a general exponent: with
`ρ = A_α + B_α Φ_0 ≤ 1`, two independent leaf labellings of `𝔹_h` fail to match with
probability at most `ρ^h Φ_0`. -/
theorem leaf_matching_boundA {α : ℝ} (hα : 1 ≤ α) {ρ : ℝ≥0∞} (μ : PMF V)
    (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (h0 : ENNReal.ofReal (AA α) + ENNReal.ofReal (BA α) * PhiA α μ R₀ ≤ ρ) (hρ : ρ ≤ 1)
    (h : ℕ) :
    ∑' x, leafMu μ h x * qE (leafMu μ h) (leafSim R₀ h) x
      ≤ ρ ^ h * PhiA α μ R₀ :=
  leaf_matching_boundA_of (zero_le_one.trans hα) (oneStepA hα) μ R₀ hrefl hsymm h0 hρ h

/-- **`eq:theta-uniform`** at a general exponent: `eq:full-hyp` at `K` keeps the full
potential below `K Φ_0`, uniformly in `h`. -/
theorem PhiFullA_le {α : ℝ} (hα : 1 ≤ α) {K : ℝ≥0∞} (μ : PMF V) (R₀ : V → V → Prop)
    (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (hyp : 1 + (1 + ENNReal.ofReal (2 * α) * PhiA α μ R₀)
        * (ENNReal.ofReal (AA α) * K + ENNReal.ofReal (BA α) * K ^ 2 * PhiA α μ R₀) ≤ K)
    (h : ℕ) :
    PhiFullA α μ R₀ h ≤ K * PhiA α μ R₀ :=
  PhiFullA_le_of (oneStepA hα) (prodStepA hα) μ R₀ hrefl hsymm hyp h

/-- **`thm:reduction`, full case (`eq:full-red`)** at a general exponent: under
`eq:full-hyp` the failure probability for full labellings is at most `K Φ_0`,
uniformly in `h`. -/
theorem full_matching_boundA {α : ℝ} (hα : 1 ≤ α) {K : ℝ≥0∞} (μ : PMF V)
    (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (hyp : 1 + (1 + ENNReal.ofReal (2 * α) * PhiA α μ R₀)
        * (ENNReal.ofReal (AA α) * K + ENNReal.ofReal (BA α) * K ^ 2 * PhiA α μ R₀) ≤ K)
    (h : ℕ) :
    ∑' x, fullMu μ h x * qE (fullMu μ h) (fullSim R₀ h) x ≤ K * PhiA α μ R₀ :=
  full_matching_boundA_of (zero_le_one.trans hα) (oneStepA hα) (prodStepA hα) μ R₀ hrefl
    hsymm hyp h

/-! ### The two analytic inputs at `α = 5/2` -/

lemma oneStep_alpha : OneStep.{u} (7 / 8) 29 :=
  fun _ ν S hr hs => Phi_square_le ν S hr hs

lemma prodStep_alpha : ProdStep.{u} 5 :=
  fun _ _ ν₁ ν₂ S₁ S₂ h₁ h₂ => Phi_prodPMF_le ν₁ ν₂ S₁ S₂ h₁ h₂

lemma ratio_le_one : (253 : ℝ≥0∞) / 256 ≤ 1 := by
  rw [show (253 : ℝ≥0∞) / 256 = ENNReal.ofReal (253 / 256) from by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat],
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- The leaf hypothesis at `α = 5/2`: `Φ_0 ≤ 1/256` gives `A + 29Φ_0 ≤ 253/256`. -/
lemma leaf_hyp_alpha {Φ : ℝ≥0∞} (h0 : Φ ≤ 1 / 256) :
    (7 : ℝ≥0∞) / 8 + 29 * Φ ≤ 253 / 256 := by
  have h29 : (29 : ℝ≥0∞) * Φ ≤ 29 * (1 / 256) := by gcongr
  have hsum : (7 : ℝ≥0∞) / 8 + 29 * (1 / 256) = 253 / 256 := by
    rw [mul_one_div,
        show (7 : ℝ≥0∞) / 8 = ENNReal.ofReal (7 / 8) from by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_ofNat],
        show (29 : ℝ≥0∞) / 256 = ENNReal.ofReal (29 / 256) from by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_add (by norm_num) (by norm_num),
        show (253 : ℝ≥0∞) / 256 = ENNReal.ofReal (253 / 256) from by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_ofNat]]
    congr 1; norm_num
  calc (7 : ℝ≥0∞) / 8 + 29 * Φ
      ≤ 7 / 8 + 29 * (1 / 256) := by gcongr
    _ = 253 / 256 := hsum

/-- **`eq:leaf-red`** at `α = 5/2`: `Φ_0 ≤ 1/256` gives decay at rate `253/256`. -/
theorem leaf_matching_bound (μ : PMF V) (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v)
    (hsymm : ∀ a b, R₀ a b → R₀ b a) (h0 : Phi μ R₀ ≤ 1 / 256) (h : ℕ) :
    ∑' x, leafMu μ h x * qE (leafMu μ h) (leafSim R₀ h) x
      ≤ (253 / 256) ^ h * Phi μ R₀ :=
  leaf_matching_boundA_of alpha_nonneg oneStep_alpha μ R₀ hrefl hsymm (leaf_hyp_alpha h0)
    ratio_le_one h

/-- **`eq:leaf-red`** for the potential itself, at `α = 5/2`. -/
theorem PhiLeaf_le (μ : PMF V) (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v)
    (hsymm : ∀ a b, R₀ a b → R₀ b a) (h0 : Phi μ R₀ ≤ 1 / 256) (h : ℕ) :
    PhiLeaf μ R₀ h ≤ (253 / 256) ^ h * Phi μ R₀ :=
  PhiLeafA_le_of oneStep_alpha μ R₀ hrefl hsymm (leaf_hyp_alpha h0) ratio_le_one h

/-- The full hypothesis `eq:full-hyp` at `α = 5/2` with `K = 16`: for `η ≤ 10⁻⁴`,
`1 + (1+5η)(16A + 29·256·η) ≤ 16`, whose numeric core is `(1+5η)(14+7424η) < 15`. -/
lemma full_hyp_alpha {η : ℝ≥0∞} (hη : η ≤ 1 / 10000) :
    1 + (1 + 5 * η) * ((7 : ℝ≥0∞) / 8 * 16 + 29 * 16 ^ 2 * η) ≤ 16 := by
  -- the numeric core, lifted through `toReal`
  have hηfin : η ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hη
  have hLfin : (1 : ℝ≥0∞) + (1 + 5 * η) * (7 / 8 * 16 + 29 * 16 ^ 2 * η) ≠ ⊤ := by finiteness
  have hηr : η.toReal ≤ 1 / 10000 := by
    rw [show (1 : ℝ≥0∞) / 10000 = ENNReal.ofReal (1 / 10000) from by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]]
      at hη
    calc η.toReal ≤ (ENNReal.ofReal (1 / 10000)).toReal := ENNReal.toReal_mono (by finiteness) hη
      _ = 1 / 10000 := ENNReal.toReal_ofReal (by norm_num)
  have h5 : (5 : ℝ≥0∞) * η ≠ ⊤ := by finiteness
  have hb : (7 : ℝ≥0∞) / 8 * 16 ≠ ⊤ := by finiteness
  have hcc : (29 : ℝ≥0∞) * 16 ^ 2 * η ≠ ⊤ := by finiteness
  have hprod : (1 + 5 * η) * ((7 : ℝ≥0∞) / 8 * 16 + 29 * 16 ^ 2 * η) ≠ ⊤ := by finiteness
  rw [← ENNReal.toReal_le_toReal hLfin (by finiteness),
      ENNReal.toReal_add ENNReal.one_ne_top hprod,
      ENNReal.toReal_mul,
      ENNReal.toReal_add ENNReal.one_ne_top h5,
      ENNReal.toReal_add hb hcc]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one,
    ENNReal.toReal_div]
  nlinarith [hηr, ENNReal.toReal_nonneg (a := η)]

/-- **`eq:theta-uniform`** at `α = 5/2`: `Θ_h ≤ 16η` for `η ≤ 10⁻⁴`. -/
theorem PhiFull_le (μ : PMF V) (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v)
    (hsymm : ∀ a b, R₀ a b → R₀ b a) (hη : Phi μ R₀ ≤ 1 / 10000) (h : ℕ) :
    PhiFull μ R₀ h ≤ 16 * Phi μ R₀ :=
  PhiFullA_le_of oneStep_alpha prodStep_alpha μ R₀ hrefl hsymm (full_hyp_alpha hη) h

/-- **`eq:full-red`** at `α = 5/2`: the failure probability is at most `16η`. -/
theorem full_matching_bound (μ : PMF V) (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v)
    (hsymm : ∀ a b, R₀ a b → R₀ b a) (hη : Phi μ R₀ ≤ 1 / 10000) (h : ℕ) :
    ∑' x, fullMu μ h x * qE (fullMu μ h) (fullSim R₀ h) x ≤ 16 * Phi μ R₀ :=
  full_matching_boundA_of alpha_nonneg oneStep_alpha prodStep_alpha μ R₀ hrefl hsymm
    (full_hyp_alpha hη) h

end GraphMatching
