/-
The i.i.d. product measure on the infinite tree (the Kolmogorov construction of
`sec:reduction`). Rather than an abstract Kolmogorov extension, this uses Mathlib's
ready-made infinite product measure `Measure.infinitePi` over the tree-vertex
index `List Bool`, and reads a level-`h` full labelling out of a vertex labelling
via `readLab`. The core is `map_readLab`: the pushforward of the product measure
under `readLab · h` is `fullMu μ h`. It is proved by singleton agreement, since
`FullLab V h` is countable: the fibre over `x` is a finite box, whose product
mass is `∏ μ(x at vertex)` (`infinitePi_pi`), which is `fullMu μ h x`
(`fullMu_apply_prod`).

`exists_infinite_tree_matching` assembles two independent copies and discharges
the `hlaw` hypothesis of `infinite_tree_matching_prob_of_law`, closing the
infinite-tree case of `thm:matching`: the constructed level truncations are
consistent under restriction, jointly measurable, and carry the pair law
`fullMu μ h × fullMu μ h` at every height, and `P(some automorphism matches
every vertex) ≥ 1 - 16Φ₀`.
-/
import GraphMatching.Measure
import Mathlib.Probability.ProductMeasure

namespace GraphMatching
open scoped ENNReal Classical
open MeasureTheory

universe u
variable {V : Type u}

/-! ### Reading a tree labelling out of a function on addresses -/

/-- Assemble a level-`h` full labelling from a labelling `f` of tree addresses
(`List Bool`): the root is `f []`, and the two subtrees read `f` shifted by
`false`/`true`. -/
def readLab (f : List Bool → V) : (h : ℕ) → FullLab V h
  | 0 => f []
  | h + 1 => (f [], readLab (fun t => f (false :: t)) h, readLab (fun t => f (true :: t)) h)

/-- Read the label at address `s` from a level-`h` full labelling. -/
def coord : (h : ℕ) → FullLab V h → List Bool → V
  | 0, x, _ => x
  | _ + 1, x, [] => x.1
  | h + 1, x, false :: t => coord h x.2.1 t
  | h + 1, x, true :: t => coord h x.2.2 t

/-- Addresses of `𝔹_h`: Boolean strings of length `≤ h`. -/
def Vtx : ℕ → Finset (List Bool)
  | 0 => {[]}
  | h + 1 => insert [] ((Vtx h).image (List.cons false) ∪ (Vtx h).image (List.cons true))

@[simp] lemma mem_Vtx_zero {s : List Bool} : s ∈ Vtx 0 ↔ s = [] := by simp [Vtx]

lemma mem_Vtx_succ {s : List Bool} {h : ℕ} :
    s ∈ Vtx (h + 1) ↔ s = [] ∨ (∃ t ∈ Vtx h, false :: t = s) ∨ (∃ t ∈ Vtx h, true :: t = s) := by
  simp only [Vtx, Finset.mem_insert, Finset.mem_union, Finset.mem_image]

/-- `readLab ∘ coord = id`: reading back the coordinates recovers the labelling. -/
lemma readLab_coord (h : ℕ) (x : FullLab V h) : readLab (fun s => coord h x s) h = x := by
  induction h with
  | zero => rfl
  | succ h ih =>
      obtain ⟨a, x₀, x₁⟩ := x
      have e : readLab (fun s => coord (h + 1) (a, x₀, x₁) s) (h + 1)
          = (a, readLab (fun t => coord h x₀ t) h, readLab (fun t => coord h x₁ t) h) := rfl
      rw [e, ih x₀, ih x₁]

/-- On addresses of `𝔹_h`, `coord ∘ readLab = f`. -/
lemma coord_readLab (h : ℕ) (f : List Bool → V) (s : List Bool) (hs : s ∈ Vtx h) :
    coord h (readLab f h) s = f s := by
  induction h generalizing f s with
  | zero =>
      rw [mem_Vtx_zero] at hs; subst hs; rfl
  | succ h ih =>
      rw [mem_Vtx_succ] at hs
      rcases hs with rfl | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · rfl
      · exact ih (fun t => f (false :: t)) t ht
      · exact ih (fun t => f (true :: t)) t ht

/-- `readLab` depends only on the values on `Vtx h`. -/
lemma readLab_congr (h : ℕ) {f g : List Bool → V} (hfg : ∀ s ∈ Vtx h, f s = g s) :
    readLab f h = readLab g h := by
  induction h generalizing f g with
  | zero => simp only [readLab]; exact hfg [] (by simp)
  | succ h ih =>
      have hf : readLab f (h + 1)
          = (f [], readLab (fun t => f (false :: t)) h, readLab (fun t => f (true :: t)) h) := rfl
      have hg : readLab g (h + 1)
          = (g [], readLab (fun t => g (false :: t)) h, readLab (fun t => g (true :: t)) h) := rfl
      have hroot : f [] = g [] := hfg [] (by rw [mem_Vtx_succ]; exact Or.inl rfl)
      have c0 : readLab (fun t => f (false :: t)) h = readLab (fun t => g (false :: t)) h :=
        ih (fun s hs => hfg (false :: s) (by rw [mem_Vtx_succ]; exact Or.inr (Or.inl ⟨s, hs, rfl⟩)))
      have c1 : readLab (fun t => f (true :: t)) h = readLab (fun t => g (true :: t)) h :=
        ih (fun s hs => hfg (true :: s) (by rw [mem_Vtx_succ]; exact Or.inr (Or.inr ⟨s, hs, rfl⟩)))
      rw [hf, hg, hroot, c0, c1]

/-- The fibre of `readLab · h` over `x` is the box "agree with `coord h x` on `Vtx h`". -/
lemma readLab_eq_iff (h : ℕ) (f : List Bool → V) (x : FullLab V h) :
    readLab f h = x ↔ ∀ s ∈ Vtx h, f s = coord h x s := by
  constructor
  · rintro rfl s hs; exact (coord_readLab h f s hs).symm
  · intro hfg
    rw [← readLab_coord h x]
    exact readLab_congr h hfg

/-- The mass `fullMu μ h x` is the product of the single-vertex masses. -/
lemma fullMu_apply_prod (μ : PMF V) (h : ℕ) (x : FullLab V h) :
    fullMu μ h x = ∏ s ∈ Vtx h, μ (coord h x s) := by
  induction h with
  | zero => simp only [Vtx, Finset.prod_singleton]; rfl
  | succ h ih =>
      obtain ⟨a, x₀, x₁⟩ := x
      have hnotmem : ([] : List Bool) ∉
          (Vtx h).image (List.cons false) ∪ (Vtx h).image (List.cons true) := by
        simp [Finset.mem_union, Finset.mem_image]
      have hdisj : Disjoint ((Vtx h).image (List.cons false)) ((Vtx h).image (List.cons true)) := by
        rw [Finset.disjoint_left]
        rintro s hsf hst
        simp only [Finset.mem_image] at hsf hst
        obtain ⟨t, _, rfl⟩ := hsf
        obtain ⟨t', _, ht⟩ := hst
        exact absurd ht (by simp)
      have hVtx : Vtx (h + 1)
          = insert [] ((Vtx h).image (List.cons false) ∪ (Vtx h).image (List.cons true)) := rfl
      have hLHS : fullMu μ (h + 1) (a, x₀, x₁) = μ a * (fullMu μ h x₀ * fullMu μ h x₁) := rfl
      rw [hLHS, hVtx, Finset.prod_insert hnotmem, Finset.prod_union hdisj,
        Finset.prod_image (fun p _ q _ he => by simpa using he),
        Finset.prod_image (fun p _ q _ he => by simpa using he)]
      simp only [coord]
      rw [ih x₀, ih x₁]

/-- `readLab · h` is measurable. -/
lemma measurable_readLab [MeasurableSpace V] (h : ℕ) :
    Measurable (fun f : List Bool → V => readLab f h) := by
  induction h with
  | zero => exact measurable_pi_apply []
  | succ h ih =>
      refine Measurable.prodMk (measurable_pi_apply []) (Measurable.prodMk ?_ ?_)
      · exact ih.comp (measurable_pi_lambda _ (fun t => measurable_pi_apply (false :: t)))
      · exact ih.comp (measurable_pi_lambda _ (fun t => measurable_pi_apply (true :: t)))

/-- **The pushforward law**: reading a level-`h` labelling out of an i.i.d.
labelling of the tree vertices has law `μ_h = fullMu μ h`. Proved by singleton
agreement: the fibre over `x` is a finite box, whose product-measure mass is the
product of single-vertex masses, which is `fullMu μ h x`. -/
lemma map_readLab (μ : PMF V) [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (h : ℕ) :
    (Measure.infinitePi (fun _ : List Bool => μ.toMeasure)).map (fun f => readLab f h)
      = (fullMu μ h).toMeasure := by
  refine Measure.ext_of_singleton (fun x => ?_)
  rw [Measure.map_apply (measurable_readLab h) (measurableSet_singleton x)]
  have hpre : (fun f : List Bool → V => readLab f h) ⁻¹' {x}
      = Set.pi (↑(Vtx h)) (fun s => {coord h x s}) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Finset.mem_coe]
    exact readLab_eq_iff h f x
  rw [hpre, Measure.infinitePi_pi (fun _ : List Bool => μ.toMeasure)
      (fun s _ => measurableSet_singleton _),
    PMF.toMeasure_apply_singleton (fullMu μ h) x (measurableSet_singleton x), fullMu_apply_prod]
  exact Finset.prod_congr rfl
    (fun s _ => PMF.toMeasure_apply_singleton μ (coord h x s) (measurableSet_singleton _))

/-- Restriction commutes with reading: dropping the deepest level of a read
labelling is the same as reading at the lower level. -/
lemma restrictLab_readLab (h : ℕ) (f : List Bool → V) :
    restrictLab h (readLab f (h + 1)) = readLab f h := by
  induction h generalizing f with
  | zero => rfl
  | succ h ih =>
      show (f [], restrictLab h (readLab (fun t => f (false :: t)) (h + 1)),
            restrictLab h (readLab (fun t => f (true :: t)) (h + 1)))
          = (f [], readLab (fun t => f (false :: t)) h, readLab (fun t => f (true :: t)) h)
      rw [ih (fun t => f (false :: t)), ih (fun t => f (true :: t))]

/-- The product PMF's measure is the product of the two measures. -/
lemma toMeasure_prodPMF {A B : Type*} [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]
    [MeasurableSpace B] [MeasurableSingletonClass B] [Countable B] (p : PMF A) (q : PMF B) :
    (prodPMF p q).toMeasure = p.toMeasure.prod q.toMeasure := by
  refine Measure.ext_of_singleton (fun z => ?_)
  obtain ⟨a, b⟩ := z
  have hsingle : ({(a, b)} : Set (A × B)) = {a} ×ˢ {b} := by
    ext ⟨a', b'⟩; simp [Prod.ext_iff]
  rw [PMF.toMeasure_apply_singleton (prodPMF p q) (a, b) (measurableSet_singleton _), prodPMF_apply,
    hsingle, Measure.prod_prod, PMF.toMeasure_apply_singleton p a (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton q b (measurableSet_singleton _)]

/-! ### The i.i.d. tree measure -/

/-- **The Kolmogorov construction.** For a countable label space with a symmetric
reflexive relation and `Φ₀ ≤ 10⁻⁴`, there is a probability space carrying two
independent i.i.d. infinite labellings, presented through their level truncations:
consistent under restriction at every point, jointly measurable, and with the
height-`h` pair law `fullMu μ h × fullMu μ h`, so each field is i.i.d. with label
law `μ` and the two fields are independent.  Some automorphism of the infinite
tree matches every vertex with probability `≥ 1 - 16Φ₀`. This closes the
infinite-tree case of `thm:matching`. -/
theorem exists_infinite_tree_matching (μ : PMF V) [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable V] (R₀ : V → V → Prop) (hrefl : ∀ v, R₀ v v) (hsymm : ∀ a b, R₀ a b → R₀ b a)
    (hη : Phi μ R₀ ≤ 1 / 10000) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X Y : (h : ℕ) → Ω → FullLab V h),
      (∀ h ω, restrictLab h (X (h + 1) ω) = X h ω) ∧
      (∀ h ω, restrictLab h (Y (h + 1) ω) = Y h ω) ∧
      (∀ h, Measurable (fun ω => (X h ω, Y h ω))) ∧
      (∀ h, P.map (fun ω => (X h ω, Y h ω))
        = (prodPMF (fullMu μ h) (fullMu μ h)).toMeasure) ∧
      1 - 16 * Phi μ R₀ ≤ P {ω | InfMatch R₀ (fun h => X h ω) (fun h => Y h ω)} := by
  have hlaw : ∀ h, ((Measure.infinitePi (fun _ : List Bool => μ.toMeasure)).prod
        (Measure.infinitePi (fun _ : List Bool => μ.toMeasure))).map
          (fun ω : (List Bool → V) × (List Bool → V) => (readLab ω.1 h, readLab ω.2 h))
      = (prodPMF (fullMu μ h) (fullMu μ h)).toMeasure := by
    intro h
    rw [show (fun ω : (List Bool → V) × (List Bool → V) => (readLab ω.1 h, readLab ω.2 h))
          = Prod.map (fun f => readLab f h) (fun g => readLab g h) from rfl,
      ← Measure.map_prod_map _ _ (measurable_readLab h) (measurable_readLab h),
      map_readLab, toMeasure_prodPMF]
  refine ⟨(List Bool → V) × (List Bool → V), inferInstance,
    (Measure.infinitePi (fun _ : List Bool => μ.toMeasure)).prod
      (Measure.infinitePi (fun _ : List Bool => μ.toMeasure)),
    inferInstance, (fun h ω => readLab ω.1 h), (fun h ω => readLab ω.2 h),
    (fun h ω => restrictLab_readLab h ω.1), (fun h ω => restrictLab_readLab h ω.2),
    (fun h => ((measurable_readLab h).comp measurable_fst).prodMk
      ((measurable_readLab h).comp measurable_snd)), hlaw, ?_⟩
  apply infinite_tree_matching_prob_of_law _ μ R₀ hrefl hsymm hη
  · intro h ω; exact restrictLab_readLab h ω.1
  · intro h ω; exact restrictLab_readLab h ω.2
  · intro h
    exact ((measurable_readLab h).comp measurable_fst).prodMk
      ((measurable_readLab h).comp measurable_snd)
  · exact hlaw

end GraphMatching
