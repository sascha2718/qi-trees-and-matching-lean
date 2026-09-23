import ChainClasses.Chain.Eta
import ChainClasses.Chain.GWInstance
import ChainClasses.Chain.Isometry
import ChainClasses.Chain.Transfer
import GraphMatching.Kolmogorov

/-!
`thm:twovalue` of `prelims.tex`, assembled as in `sec:proof-main` of
`gw_classes_simple.tex`: two independent samples of the two-value offspring law
are quasi-isometric with high probability, at the rate `eq:rate`.

* `twoSampleMeasure`: the law of an independent pair of chain fields, two copies
  of `chainMeasure`, with `labFst` and `labSnd` the two label fields.
* `chainMeasure_level_marginal`, `chainMeasure_level_prod`: the quantised labels
  of one sample are i.i.d. with law `p^{(D)}`, the marginal and the joint law
  over a finite set of vertices.
* `matchEvent`, `measurableSet_matchEvent`, `matching_prob_ge`: the matching
  event at scale `D`, the level-`h` projections of the two quantised fields
  being fed to `infinite_tree_matching_prob_of_law` over the two-sample space;
  the potential bound of `thm:eta-bound` supplies its hypothesis.
* `portrait_of_matchEvent`: on the matching event a single portrait matches the
  two quantised fields to within one level.
* `psi_nil`, `relabelMap_nil`, `IsQIWith.exists_root_fixing`:
  the transfer and relabelling maps fix the root, and a quasi-isometry into a
  subtree containing the root can be redefined at the root so that it fixes it.
* `qi_of_matching`: the deterministic core, `level_close_comparable` into
  `transfer` and `relabelMap_isometry`, giving a root-fixing
  `(D²+3)`-quasi-isometry.
* `twovalue_rate`: `eq:rate`, the failure probability at scale `D` is at most
  `256 θ₁^{D(D-5/2)}`; `twovalue_ae` is the almost sure statement obtained by
  letting the scale run.
* `twoSampleMeasure_chains_ae`, `inTree_eq_inAssoc`: the good event has full
  probability and carries `thm:chains`, so `twovalue_rate_tree` and
  `twovalue_ae_tree` state the same bounds for the sampled trees themselves.

The four largeness conditions `eq:d0-conditions` are carried as hypotheses,
exactly as in `ChainClasses.Chain.Eta`.
-/

namespace ChainClasses

open MeasureTheory ProbabilityTheory GraphMatching
open scoped ENNReal

variable {t : ℝ}

/-! ### The two-sample space -/

/-- The law of two independent samples of the offspring field: the product of
two copies of `chainMeasure`. -/
noncomputable def twoSampleMeasure (ht : 0 < t) (ht1 : t ≤ 1) :
    Measure ((Word → Bool) × (Word → Bool)) :=
  (chainMeasure ht ht1).prod (chainMeasure ht ht1)

instance isProbabilityMeasure_twoSampleMeasure (ht : 0 < t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (twoSampleMeasure ht ht1) :=
  inferInstanceAs (IsProbabilityMeasure ((chainMeasure ht ht1).prod (chainMeasure ht ht1)))

/-- The label field of the first sample. -/
noncomputable def labFst (ω : (Word → Bool) × (Word → Bool)) : Word → ℕ := labAux ω.1

/-- The label field of the second sample. -/
noncomputable def labSnd (ω : (Word → Bool) × (Word → Bool)) : Word → ℕ := labAux ω.2

/-! ### The quantised labels of one sample

The coordinate family of `chainMeasure` is the offspring field, so the three
hypotheses of `ChainClasses.Chain.Geometric` are available in the concrete form
recorded in `ChainClasses.Chain.GWInstance`. -/

/-- The offspring field of `chainMeasure`, as a family of coordinates. -/
noncomputable def chainField : Word → (Word → Bool) → Bool :=
  fun v ↦ (BranchingProcess.coord v : (Word → Bool) → Bool)

/-- The label events of the offspring field are measurable. -/
lemma measurableSet_chain_labAux (w : Word) (m : ℕ) :
    MeasurableSet {χ : Word → Bool | labAux χ w = m} :=
  measurableSet_labAux chainField measurable_chainMeasure_coord w m

/-- Each label of the offspring field is a measurable function. -/
lemma measurable_chain_labAux (w : Word) :
    Measurable fun χ : Word → Bool ↦ labAux χ w :=
  measurable_labAux chainField measurable_chainMeasure_coord w

/-- The junk value of the label never occurs. -/
lemma chainMeasure_labAux_zero (ht : 0 < t) (ht1 : t ≤ 1) (w : Word) :
    chainMeasure ht ht1 {χ : Word → Bool | labAux χ w = 0} = 0 :=
  labAux_zero_null (chainMeasure ht ht1) chainField t measurable_chainMeasure_coord
    (chainMeasure_iIndepFun ht ht1) (chainMeasure_coord_true ht ht1) ht w

/-- A chain that never terminates is a null event. -/
lemma chainMeasure_not_chains (ht : 0 < t) (ht1 : t ≤ 1) :
    chainMeasure ht ht1 {χ : Word → Bool | ¬ Chains χ} = 0 :=
  not_chains_null (chainMeasure ht ht1) chainField t measurable_chainMeasure_coord
    (chainMeasure_iIndepFun ht ht1) (chainMeasure_coord_true ht ht1) ht

/-- The quantised geometric law `p^{(D)}` of the chain labels, at `a = θ₁ = 1 - t`. -/
noncomputable def chainQPMF (ht : 0 < t) (ht1 : t ≤ 1) {D : ℕ} (hD : 2 ≤ D) : PMF ℕ :=
  qPMF (by linarith : (0 : ℝ) ≤ 1 - t) (by linarith : (1 : ℝ) - t < 1) hD

/-- The masses of the quantised law are the class masses `eq:qk`. -/
lemma chainQPMF_apply (ht : 0 < t) (ht1 : t ≤ 1) {D : ℕ} (hD : 2 ≤ D) (k : ℕ) :
    chainQPMF ht ht1 hD k = ENNReal.ofReal (qF (1 - t) D k) := rfl

/-- **The marginal clause of `thm:quantised-law`**: the quantised label of a
vertex has the quantised geometric law, `ℙ(ℓ_D(λ(w)) = k) = p^{(D)}_k`. -/
theorem chainMeasure_level_marginal (ht : 0 < t) (ht1 : t ≤ 1) {D : ℕ} (hD : 2 ≤ D)
    (w : Word) (k : ℕ) :
    chainMeasure ht ht1 {χ : Word → Bool | levelMap D (labAux χ w) = k}
      = ENNReal.ofReal (qF (1 - t) D k) := by
  have ha : (0 : ℝ) ≤ 1 - t := by linarith
  set P := chainMeasure ht ht1 with hP
  set S : Finset ℕ := Finset.Ico (D ^ k) (D ^ (k + 1)) with hS
  set N : Set (Word → Bool) := ⋃ m ∈ S, {χ : Word → Bool | labAux χ w = m} with hN
  have hone : ∀ m ∈ S, 1 ≤ m := by
    intro m hm
    have := (Finset.mem_Ico.mp hm).1
    have h1 : 1 ≤ D ^ k := Nat.one_le_pow _ _ (by omega)
    omega
  have hsub1 : N ⊆ {χ : Word → Bool | levelMap D (labAux χ w) = k} := by
    intro χ hχ
    obtain ⟨m, hm, hχm⟩ := Set.mem_iUnion₂.mp hχ
    have hmem := Finset.mem_Ico.mp hm
    have : labAux χ w = m := hχm
    rw [Set.mem_ofPred_eq, this]
    exact (level_eq_iff hD (hone m hm)).mpr ⟨hmem.1, hmem.2⟩
  have hsub2 : {χ : Word → Bool | levelMap D (labAux χ w) = k}
      ⊆ N ∪ {χ : Word → Bool | labAux χ w = 0} := by
    intro χ hχ
    by_cases hz : labAux χ w = 0
    · exact Or.inr hz
    · refine Or.inl (Set.mem_iUnion₂.mpr ⟨labAux χ w, ?_, rfl⟩)
      obtain ⟨h1, h2⟩ := (level_eq_iff hD (Nat.one_le_iff_ne_zero.mpr hz)).mp hχ
      exact Finset.mem_Ico.mpr ⟨h1, h2⟩
  have hdisj : (S : Set ℕ).PairwiseDisjoint
      (fun m ↦ {χ : Word → Bool | labAux χ w = m}) := by
    intro m _ m' _ hne
    refine Set.disjoint_left.mpr fun χ hχ hχ' ↦ hne ?_
    have h1 : labAux χ w = m := hχ
    have h2 : labAux χ w = m' := hχ'
    omega
  have hNval : P N = ENNReal.ofReal (qF (1 - t) D k) := by
    rw [hN, measure_biUnion_finset hdisj (fun m _ ↦ measurableSet_chain_labAux w m)]
    have hterm : ∀ m ∈ S, P {χ : Word → Bool | labAux χ w = m}
        = ENNReal.ofReal ((1 - t) ^ (m - 1) * (1 - (1 - t))) := by
      intro m hm
      rw [hP, chainMeasure_label_marginal ht ht1 w (hone m hm)]
      congr 1
      ring
    rw [Finset.sum_congr rfl hterm,
      ← ENNReal.ofReal_sum_of_nonneg
        (fun m _ ↦ mul_nonneg (pow_nonneg ha _) (by linarith)),
      hS, class_sum ha hD k]
  refine le_antisymm ?_ (hNval ▸ measure_mono hsub1)
  calc P {χ : Word → Bool | levelMap D (labAux χ w) = k}
      ≤ P (N ∪ {χ : Word → Bool | labAux χ w = 0}) := measure_mono hsub2
    _ ≤ P N + P {χ : Word → Bool | labAux χ w = 0} := measure_union_le _ _
    _ = ENNReal.ofReal (qF (1 - t) D k) := by
        rw [hNval, hP, chainMeasure_labAux_zero ht ht1 w, add_zero]

/-- **The independence clause of `thm:quantised-law`, in product form**: the
joint law of the quantised labels over a finite set of vertices factorises into
the masses of `p^{(D)}`. -/
theorem chainMeasure_level_prod (ht : 0 < t) (ht1 : t ≤ 1) {D : ℕ} (hD : 2 ≤ D)
    (S : Finset Word) (n : Word → ℕ) :
    chainMeasure ht ht1 (⋂ w ∈ S, {χ : Word → Bool | levelMap D (labAux χ w) = n w})
      = ∏ w ∈ S, ENNReal.ofReal (qF (1 - t) D (n w)) := by
  have hind := (chainMeasure_quantised_label_iIndepFun ht ht1 D).measure_inter_preimage_eq_mul
    S (sets := fun w ↦ {n w}) (fun w _ ↦ measurableSet_singleton (n w))
  have hpre : ∀ w : Word, (fun χ : Word → Bool ↦ levelMap D (labAux χ w)) ⁻¹' {n w}
      = {χ : Word → Bool | levelMap D (labAux χ w) = n w} := fun _ ↦ rfl
  simp only [hpre] at hind
  rw [hind]
  exact Finset.prod_congr rfl fun w _ ↦ chainMeasure_level_marginal ht ht1 hD w (n w)

/-! ### The level projections of the two quantised fields -/

/-- The level-`h` projection of the quantised label field of the first sample. -/
noncomputable def qX (D h : ℕ) (ω : (Word → Bool) × (Word → Bool)) : FullLab ℕ h :=
  readLab (fun s ↦ levelMap D (labAux ω.1 s)) h

/-- The level-`h` projection of the quantised label field of the second sample. -/
noncomputable def qY (D h : ℕ) (ω : (Word → Bool) × (Word → Bool)) : FullLab ℕ h :=
  readLab (fun s ↦ levelMap D (labAux ω.2 s)) h

/-- The projections are compatible: dropping the deepest level of `qX` at height
`h+1` gives `qX` at height `h`. -/
lemma restrictLab_qX (D h : ℕ) (ω : (Word → Bool) × (Word → Bool)) :
    restrictLab h (qX D (h + 1) ω) = qX D h ω :=
  restrictLab_readLab h _

/-- The same for the second sample. -/
lemma restrictLab_qY (D h : ℕ) (ω : (Word → Bool) × (Word → Bool)) :
    restrictLab h (qY D (h + 1) ω) = qY D h ω :=
  restrictLab_readLab h _

/-- The pair of level-`h` projections is measurable. -/
lemma measurable_qXY (D h : ℕ) :
    Measurable fun ω : (Word → Bool) × (Word → Bool) ↦ (qX D h ω, qY D h ω) := by
  have hfst : Measurable fun ω : (Word → Bool) × (Word → Bool) ↦
      fun s : Word ↦ levelMap D (labAux ω.1 s) :=
    Measurable.of_eval fun s ↦
      (measurable_from_top (f := levelMap D)).comp
        ((measurable_chain_labAux s).comp measurable_fst)
  have hsnd : Measurable fun ω : (Word → Bool) × (Word → Bool) ↦
      fun s : Word ↦ levelMap D (labAux ω.2 s) :=
    Measurable.of_eval fun s ↦
      (measurable_from_top (f := levelMap D)).comp
        ((measurable_chain_labAux s).comp measurable_snd)
  exact ((measurable_readLab h).comp hfst).prodMk ((measurable_readLab h).comp hsnd)

/-- The level-`h` projection of one sample has the i.i.d. law `μ_h` of the
quantised geometric law: reading a level-`h` labelling out of the quantised
chain labels gives `fullMu p^{(D)} h`. -/
lemma chainMeasure_readLab (ht : 0 < t) (ht1 : t ≤ 1) {D : ℕ} (hD : 2 ≤ D) (h : ℕ)
    (x : FullLab ℕ h) :
    chainMeasure ht ht1 {χ : Word → Bool | readLab (fun s ↦ levelMap D (labAux χ s)) h = x}
      = fullMu (chainQPMF ht ht1 hD) h x := by
  have hset : {χ : Word → Bool | readLab (fun s ↦ levelMap D (labAux χ s)) h = x}
      = ⋂ s ∈ Vtx h, {χ : Word → Bool | levelMap D (labAux χ s) = GraphMatching.coord h x s} := by
    ext χ
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact readLab_eq_iff h _ x
  rw [hset, chainMeasure_level_prod ht ht1 hD (Vtx h) (fun s ↦ GraphMatching.coord h x s),
    fullMu_apply_prod]
  exact Finset.prod_congr rfl fun s _ ↦ rfl

/-- **The two-sample law**: the pair of level-`h` projections of the two
quantised label fields is distributed as two independent `μ_h`-labellings. This
is the `hlaw` hypothesis of `infinite_tree_matching_prob_of_law`. -/
lemma twoSampleMeasure_map (ht : 0 < t) (ht1 : t ≤ 1) {D : ℕ} (hD : 2 ≤ D) (h : ℕ) :
    (twoSampleMeasure ht ht1).map (fun ω ↦ (qX D h ω, qY D h ω))
      = (prodPMF (fullMu (chainQPMF ht ht1 hD) h) (fullMu (chainQPMF ht ht1 hD) h)).toMeasure := by
  refine Measure.ext_of_singleton fun z ↦ ?_
  obtain ⟨x, y⟩ := z
  rw [Measure.map_apply (measurable_qXY D h) (measurableSet_singleton _)]
  have hpre : (fun ω : (Word → Bool) × (Word → Bool) ↦ (qX D h ω, qY D h ω)) ⁻¹' {(x, y)}
      = {χ : Word → Bool | readLab (fun s ↦ levelMap D (labAux χ s)) h = x}
        ×ˢ {χ : Word → Bool | readLab (fun s ↦ levelMap D (labAux χ s)) h = y} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Set.mem_ofPred_eq,
      Prod.mk.injEq, qX, qY]
  rw [hpre, twoSampleMeasure, Measure.prod_prod, chainMeasure_readLab ht ht1 hD,
    chainMeasure_readLab ht ht1 hD,
    PMF.toMeasure_apply_singleton _ (x, y) (measurableSet_singleton _), prodPMF_apply]

/-! ### The matching event -/

/-- **The matching event at scale `D`**: a single automorphism of the infinite
binary tree matches the two quantised label fields at every vertex, so that the
matched levels differ by at most one. -/
def matchEvent (D : ℕ) : Set ((Word → Bool) × (Word → Bool)) :=
  {ω | InfMatch (compat pathGraph) (fun h ↦ qX D h ω) (fun h ↦ qY D h ω)}

/-- The matching event is the intersection of the level-`h` matching events, so
it is measurable. -/
lemma measurableSet_matchEvent (D : ℕ) : MeasurableSet (matchEvent D) := by
  have hset : matchEvent D
      = ⋂ h : ℕ, {ω : (Word → Bool) × (Word → Bool) |
          fullSim (compat pathGraph) h (qX D h ω) (qY D h ω)} := by
    ext ω
    simp only [matchEvent, Set.mem_ofPred_eq, Set.mem_iInter]
    exact infMatch_iff_forall_level (compat pathGraph) _ _ (fun h ↦ restrictLab_qX D h ω)
      (fun h ↦ restrictLab_qY D h ω)
  rw [hset]
  refine MeasurableSet.iInter fun h ↦ ?_
  exact measurable_qXY D h
    ((Set.to_countable {p : FullLab ℕ h × FullLab ℕ h |
      fullSim (compat pathGraph) h p.1 p.2}).measurableSet)

/-- **The matching bound**: under the largeness conditions `eq:d0-conditions`
the matching event at scale `D` has probability at least
`1 - 256 θ₁^{D(D-5/2)}`. The potential estimate of `thm:eta-bound` supplies the
hypothesis of the i.i.d. matching theorem, and the two-sample law identifies the
level projections with two independent `μ_h`-labellings. -/
theorem matching_prob_ge (ht : 0 < t) (ht1 : t < 1) {D : ℕ} (hD : 5 ≤ D)
    (h1 : (1 - t) ^ (D - 1) ≤ 1 / 10) (h2 : (1 - t) ^ (D ^ 2 - D) ≤ 1 / 2)
    (h3 : 36 * (1 - t) ^ (5 * D - 2) ≤ 1) (h4 : 16 * qBound (1 - t) D ≤ 1 / 10000) :
    1 - ENNReal.ofReal (256 * qBound (1 - t) D)
      ≤ twoSampleMeasure ht ht1.le (matchEvent D) := by
  have ha : (0 : ℝ) < 1 - t := by linarith
  have ha1 : (1 : ℝ) - t < 1 := by linarith
  have hD2 : 2 ≤ D := by omega
  have heta : etaP (chainQPMF ht ht1.le hD2) ≤ ENNReal.ofReal (16 * qBound (1 - t) D) :=
    quantised_eta_le ha ha1 hD h1 h2 h3
  have hPhi : Phi (chainQPMF ht ht1.le hD2) (compat pathGraph) ≤ 1 / 10000 := by
    rw [← etaG_eq_Phi]
    refine le_trans heta ?_
    rw [show (1 : ℝ≥0∞) / 10000 = ENNReal.ofReal (1 / 10000) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]]
    exact ENNReal.ofReal_le_ofReal h4
  have hmain := infinite_tree_matching_prob_of_law (twoSampleMeasure ht ht1.le)
    (chainQPMF ht ht1.le hD2) (compat pathGraph) (compat_refl pathGraph) (compat_symm pathGraph)
    hPhi (fun h ω ↦ qX D h ω) (fun h ω ↦ qY D h ω)
    (fun h ω ↦ restrictLab_qX D h ω) (fun h ω ↦ restrictLab_qY D h ω)
    (fun h ↦ measurable_qXY D h) (fun h ↦ twoSampleMeasure_map ht ht1.le hD2 h)
  have hconst : (16 : ℝ≥0∞) * ENNReal.ofReal (16 * qBound (1 - t) D)
      = ENNReal.ofReal (256 * qBound (1 - t) D) := by
    rw [show (256 : ℝ) * qBound (1 - t) D = 16 * (16 * qBound (1 - t) D) from by ring,
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 16 by norm_num) (q := 16 * qBound (1 - t) D),
      ENNReal.ofReal_ofNat]
  refine le_trans (tsub_le_tsub_left ?_ 1) hmain
  rw [← etaG_eq_Phi, ← hconst]
  gcongr
  exact heta

/-! ### From a tree automorphism to a portrait

The automorphisms of `GraphMatching` are the recursive swap group, so a
compatible family of them is a portrait of the index tree, the very datum
`autOf` consumes. `autAddr` is the address map of an automorphism of `𝔹_h` and
`swapBit` its swap bit at a vertex; a compatible family has a well-defined swap
bit at every vertex, and its `autOf` reproduces the address maps. -/

/-- The swap of `Bool` with bit `b`. -/
def flipOn (b j : Bool) : Bool := bif b then !j else j

/-- The swap of `Bool` with bit `b`, as an equivalence. -/
def flipEquiv (b : Bool) : Bool ≃ Bool where
  toFun := flipOn b
  invFun := flipOn b
  left_inv j := by cases b <;> cases j <;> rfl
  right_inv j := by cases b <;> cases j <;> rfl

/-- The address map of an automorphism of `𝔹_h`: the swap bit at the root acts
on the first letter, and the descent continues in the corresponding subtree. -/
def autAddr : (h : ℕ) → Aut h → Word → Word
  | 0, _, s => s
  | _ + 1, _, [] => []
  | h + 1, π, j :: u => flipOn π.1 j :: autAddr h (bif j then π.2.2 else π.2.1) u

/-- The swap bit of an automorphism of `𝔹_h` at the vertex `s`. -/
def swapBit : (h : ℕ) → Aut h → Word → Bool
  | 0, _, _ => false
  | _ + 1, π, [] => π.1
  | h + 1, π, j :: u => swapBit h (bif j then π.2.2 else π.2.1) u

/-- Address maps fix the root. -/
@[simp] lemma autAddr_nil : ∀ (h : ℕ) (π : Aut h), autAddr h π [] = []
  | 0, _ => rfl
  | _ + 1, _ => rfl

/-- Address maps preserve lengths. -/
lemma autAddr_length : ∀ (h : ℕ) (π : Aut h) (s : Word), (autAddr h π s).length = s.length
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | h + 1, π, j :: u => by
      simp only [autAddr, List.length_cons]
      rw [autAddr_length h _ u]

/-- The recursion of `autOf`, for the address map of an automorphism of `𝔹_h`:
appending a letter appends its image under the swap bit at the vertex. -/
lemma autAddr_concat : ∀ (w : Word) (h : ℕ) (π : Aut h) (j : Bool), w.length < h →
    autAddr h π (w ++ [j]) = autAddr h π w ++ [flipOn (swapBit h π w) j]
  | [], h, π, j, hw => by
      match h, hw with
      | h + 1, _ => simp [autAddr, swapBit]
  | i :: u, h, π, j, hw => by
      match h, hw with
      | h + 1, hw =>
          have hu : u.length < h := by simpa using hw
          simp only [autAddr, swapBit, List.cons_append]
          rw [autAddr_concat u h _ j hu]

/-- The swap bit is stable under restriction. -/
lemma swapBit_restrict : ∀ (h : ℕ) (π : Aut (h + 1)) (s : Word), s.length < h →
    swapBit h (restrictAut h π) s = swapBit (h + 1) π s := by
  intro h
  induction h with
  | zero => intro _ _ hs; omega
  | succ h ih =>
      intro π s hs
      match s with
      | [] => rfl
      | j :: u =>
          have hu : u.length < h := by simpa using hs
          show swapBit h (bif j then restrictAut h π.2.2 else restrictAut h π.2.1) u
            = swapBit (h + 1) (bif j then π.2.2 else π.2.1) u
          cases j
          · exact ih π.2.1 u hu
          · exact ih π.2.2 u hu

/-- The address map is stable under restriction. -/
lemma autAddr_restrict : ∀ (h : ℕ) (π : Aut (h + 1)) (s : Word), s.length ≤ h →
    autAddr h (restrictAut h π) s = autAddr (h + 1) π s := by
  intro h
  induction h with
  | zero =>
      intro π s hs
      rw [List.eq_nil_of_length_eq_zero (by omega : s.length = 0)]
      rfl
  | succ h ih =>
      intro π s hs
      match s with
      | [] => simp
      | j :: u =>
          have hu : u.length ≤ h := by simpa using hs
          show flipOn π.1 j
              :: autAddr h (bif j then restrictAut h π.2.2 else restrictAut h π.2.1) u
            = flipOn π.1 j :: autAddr (h + 1) (bif j then π.2.2 else π.2.1) u
          cases j
          · exact congrArg (fun z ↦ flipOn π.1 false :: z) (ih π.2.1 u hu)
          · exact congrArg (fun z ↦ flipOn π.1 true :: z) (ih π.2.2 u hu)

/-- Words of length at most `h` are vertices of `𝔹_h`. -/
lemma mem_Vtx_of_length_le : ∀ (h : ℕ) (s : Word), s.length ≤ h → s ∈ Vtx h := by
  intro h
  induction h with
  | zero =>
      intro s hs
      rw [mem_Vtx_zero]
      exact List.eq_nil_of_length_eq_zero (by omega)
  | succ h ih =>
      intro s hs
      rw [mem_Vtx_succ]
      match s with
      | [] => exact Or.inl rfl
      | j :: u =>
          have hu : u ∈ Vtx h := ih u (by simpa using hs)
          cases j
          · exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
          · exact Or.inr (Or.inr ⟨u, hu, rfl⟩)

/-- A vertexwise matching under `π` relates the label at `s` to the label at the
image address `autAddr h π s`. -/
lemma rel_coord_autAddr {V : Type*} (R₀ : V → V → Prop) :
    ∀ (h : ℕ) (π : Aut h) (x y : FullLab V h), fullMatchesA R₀ h π x y →
      ∀ s ∈ Vtx h, R₀ (GraphMatching.coord h x s) (GraphMatching.coord h y (autAddr h π s)) := by
  intro h
  induction h with
  | zero =>
      intro π x y hm s _
      exact hm
  | succ h ih =>
      intro π x y hm s hs
      rw [mem_Vtx_succ] at hs
      obtain ⟨hroot, hleft, hright⟩ := hm
      rcases hs with rfl | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · exact hroot
      · have := ih π.2.1 x.2.1 (bif π.1 then y.2.2 else y.2.1) hleft u hu
        show R₀ (GraphMatching.coord h x.2.1 u)
          (GraphMatching.coord (h + 1) y (flipOn π.1 false :: autAddr h π.2.1 u))
        revert this
        cases π.1 <;> exact fun h' ↦ h'
      · have := ih π.2.2 x.2.2 (bif π.1 then y.2.1 else y.2.2) hright u hu
        show R₀ (GraphMatching.coord h x.2.2 u)
          (GraphMatching.coord (h + 1) y (flipOn π.1 true :: autAddr h π.2.2 u))
        revert this
        cases π.1 <;> exact fun h' ↦ h'

/-- The portrait of a compatible family of tree automorphisms: the swap bit at
the vertex `p` read off at the first height where it is defined. -/
def portraitOf (σ : (h : ℕ) → Aut h) (p : Word) : Bool ≃ Bool :=
  flipEquiv (swapBit (p.length + 1) (σ (p.length + 1)) p)

/-- Along a compatible family the swap bit at a vertex does not depend on the
height at which it is read. -/
lemma swapBit_compat {σ : (h : ℕ) → Aut h} (hσ : ∀ h, restrictAut h (σ (h + 1)) = σ h) :
    ∀ (h : ℕ) (s : Word), s.length < h →
      swapBit h (σ h) s = swapBit (s.length + 1) (σ (s.length + 1)) s := by
  intro h
  induction h with
  | zero => intro _ hs; omega
  | succ h ih =>
      intro s hs
      rcases Nat.lt_or_ge s.length h with hlt | hge
      · rw [← swapBit_restrict h (σ (h + 1)) s hlt, hσ h]
        exact ih s hlt
      · have : s.length = h := by omega
        rw [this]

/-- The `autOf` of the portrait of a compatible family is the address map at
every height where the address map is defined. -/
lemma autOf_portraitOf {σ : (h : ℕ) → Aut h} (hσ : ∀ h, restrictAut h (σ (h + 1)) = σ h) :
    ∀ (w : Word) (h : ℕ), w.length ≤ h → autOf (portraitOf σ) w = autAddr h (σ h) w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro h _; rw [autOf_nil, autAddr_nil]
  | append_singleton w j ih =>
      intro h hw
      have hlt : w.length < h := by simpa using hw
      rw [autOf_concat, ih h hlt.le, autAddr_concat w h (σ h) j hlt]
      congr 1
      show [flipOn (swapBit (w.length + 1) (σ (w.length + 1)) w) j]
        = [flipOn (swapBit h (σ h) w) j]
      rw [swapBit_compat hσ h w hlt]

/-- **The portrait of an infinite-tree matching.** If one automorphism of the
infinite binary tree matches the labellings `f` and `g` at every vertex, then a
portrait `σ` of the index tree does the same: `f w` is related to
`g (autOf σ w)` at every vertex `w`. -/
theorem exists_portrait_of_infMatch {V : Type*} (R₀ : V → V → Prop) (f g : Word → V)
    (hm : InfMatch R₀ (fun h ↦ readLab f h) (fun h ↦ readLab g h)) :
    ∃ σ : Word → Bool ≃ Bool, ∀ w : Word, R₀ (f w) (g (autOf σ w)) := by
  obtain ⟨σ, hσ, hgood⟩ := hm
  refine ⟨portraitOf σ, fun w ↦ ?_⟩
  have hw : w ∈ Vtx w.length := mem_Vtx_of_length_le _ w le_rfl
  have himg : autAddr w.length (σ w.length) w ∈ Vtx w.length :=
    mem_Vtx_of_length_le _ _ (by rw [autAddr_length])
  have hkey := rel_coord_autAddr R₀ w.length (σ w.length) _ _ (hgood w.length) w hw
  rw [coord_readLab w.length f w hw, coord_readLab w.length g _ himg] at hkey
  rwa [← autOf_portraitOf hσ w w.length le_rfl] at hkey

/-- On the matching event a single portrait matches the two quantised label
fields to within one level. -/
theorem portrait_of_matchEvent {D : ℕ} {ω : (Word → Bool) × (Word → Bool)}
    (hω : ω ∈ matchEvent D) :
    ∃ σ : Word → Bool ≃ Bool, ∀ w : Word,
      compat pathGraph (levelMap D (labAux ω.1 w)) (levelMap D (labAux ω.2 (autOf σ w))) :=
  exists_portrait_of_infMatch (compat pathGraph)
    (fun s ↦ levelMap D (labAux ω.1 s)) (fun s ↦ levelMap D (labAux ω.2 s)) hω

/-! ### The deterministic core -/

/-- A quasi-isometry followed by an isometry onto a third tree is a
quasi-isometry with the same constant. -/
lemma IsQIWith.comp_isometry {K : ℕ} {T T₂ T' : Word → Prop} {f g : Word → Word}
    (hf : IsQIWith K T T₂ f) (hmaps : ∀ x, T₂ x → T' (g x))
    (honto : ∀ y, T' y → ∃ x, T₂ x ∧ g x = y)
    (hdist : ∀ x y, T₂ x → T₂ y → treeDist (g x) (g y) = treeDist x y) :
    IsQIWith K T T' (fun x ↦ g (f x)) := by
  refine ⟨fun x hx ↦ hmaps _ (hf.maps x hx), fun x y hx hy ↦ ?_, fun x y hx hy ↦ ?_,
    fun y' hy' ↦ ?_⟩
  · rw [hdist _ _ (hf.maps x hx) (hf.maps y hy)]
    exact hf.upper x y hx hy
  · rw [hdist _ _ (hf.maps x hx) (hf.maps y hy)]
    exact hf.lower x y hx hy
  · obtain ⟨z, hz, rfl⟩ := honto y' hy'
    obtain ⟨x, hx, hd⟩ := hf.dense z hz
    exact ⟨x, hx, by rw [hdist _ _ (hf.maps x hx) hz]; exact hd⟩

/-! ### Root-fixing maps

The maps of `thm:transfer` and `thm:isometry` send the root to the root, and a
quasi-isometry between two subtrees containing the root can be redefined at the
root alone so that it fixes the root, at the cost of a larger constant. -/

/-- The transfer map fixes the root. -/
lemma psi_nil {lam lam' : Word → ℕ} (hlam : ∀ u, 1 ≤ lam u) : psi lam lam' [] = [] := by
  have h := psi_apply (lam' := lam') hlam (w := []) (l := 0) (Nat.zero_le _)
  simpa [levelPhi] using h

/-- The relabelling map fixes the root. -/
lemma relabelMap_nil (σ : Word → Bool ≃ Bool) {lam : Word → ℕ} (lam' : Word → ℕ)
    (hlam : ∀ u, 1 ≤ lam u) : relabelMap σ lam lam' [] = [] := by
  have h := relabelMap_apply σ lam' hlam (w := []) (l := 0) (Nat.zero_le _)
  simpa using h

/-- A quasi-isometry into a subtree containing the root can be redefined to fix
the root: moving the image of the root costs twice its depth in the constant. -/
lemma IsQIWith.exists_root_fixing {K : ℕ} {T T' : Word → Prop} {f : Word → Word}
    (h : IsQIWith K T T' f) (hT' : T' []) :
    ∃ (K' : ℕ) (g : Word → Word), IsQIWith K' T T' g ∧ g [] = [] := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = treeDist (f []) [] := ⟨_, rfl⟩
  set g : Word → Word := Function.update f [] [] with hg
  have hg0 : g [] = [] := Function.update_self _ _ _
  refine ⟨K + 2 * c, g, ?_, hg0⟩
  -- every vertex moves by at most `c`
  have hclose : ∀ x, treeDist (g x) (f x) ≤ c := by
    intro x
    by_cases hx : x = []
    · subst hx
      rw [hg0, treeDist_comm]
      exact hc.ge
    · rw [hg, Function.update_of_ne hx, treeDist_self]
      exact Nat.zero_le _
  refine ⟨fun x hx ↦ ?_, fun x y hx hy ↦ ?_, fun x y hx hy ↦ ?_, fun y' hy' ↦ ?_⟩
  · -- the redefined map still lands in `T'`
    by_cases hx0 : x = []
    · subst hx0
      rw [hg0]
      exact hT'
    · rw [hg, Function.update_of_ne hx0]
      exact h.maps x hx
  · -- upper bound: the two endpoints move by at most `c` each
    have h1 := treeDist_triangle (g x) (f x) (g y)
    have h2 := treeDist_triangle (f x) (f y) (g y)
    have h3 := hclose x
    have h4 := hclose y
    have e4 := treeDist_comm (f y) (g y)
    have h5 := h.upper x y hx hy
    have h6 : treeDist (g x) (g y) ≤ treeDist (f x) (f y) + 2 * c := by omega
    nlinarith [Nat.zero_le (c * treeDist x y)]
  · -- lower bound: the images move by at most `c` each
    have h1 := treeDist_triangle (f x) (g x) (f y)
    have h2 := treeDist_triangle (g x) (g y) (f y)
    have h3 := hclose x
    have h4 := hclose y
    have e3 := treeDist_comm (f x) (g x)
    have h5 := h.lower x y hx hy
    have h6 : treeDist (f x) (f y) ≤ treeDist (g x) (g y) + 2 * c := by omega
    have h7 : K * treeDist (f x) (f y) ≤ K * (treeDist (g x) (g y) + 2 * c) :=
      Nat.mul_le_mul_left K h6
    nlinarith [Nat.zero_le (c * treeDist (g x) (g y)), Nat.zero_le (c * c), Nat.zero_le (K * c)]
  · -- density: the preimage of `h` still serves
    obtain ⟨x, hx, hd⟩ := h.dense y' hy'
    refine ⟨x, hx, ?_⟩
    have h1 := treeDist_triangle (g x) (f x) y'
    have h3 := hclose x
    omega

/-- **The deterministic core of `sec:proof-main`**: if a portrait matches the
quantised labellings `ℓ_D ∘ λ` and `ℓ_D ∘ λ'` to within one level, then the two
associated trees admit a `(D²+3)`-quasi-isometry. The levels within one force
length ratios within `D²` (`thm:level`), the Transfer lemma turns that into a
quasi-isometry onto the tree of the relabelled labelling, and `thm:isometry`
identifies that tree with the tree of `λ'`. -/
theorem qi_of_matching {D : ℕ} (hD : 2 ≤ D) (σ : Word → Bool ≃ Bool) {lam lam' : Word → ℕ}
    (hlam : ∀ w, 1 ≤ lam w) (hlam' : ∀ w, 1 ≤ lam' w)
    (hmatch : ∀ w, compat pathGraph (levelMap D (lam w)) (levelMap D (lam' (autOf σ w)))) :
    ∃ f : Word → Word,
      IsQIWith (D ^ 2 + 3) (InAssoc lam) (InAssoc lam') f ∧ f [] = [] := by
  have hcomp : ∀ u, lam u ≤ D ^ 2 * lam' (autOf σ u) ∧ lam' (autOf σ u) ≤ D ^ 2 * lam u := by
    intro u
    have h := hmatch u
    rw [compat_pathGraph] at h
    obtain ⟨e1, e2⟩ := level_close_comparable hD (hlam u) (hlam' (autOf σ u))
      (by omega) (by omega)
    exact ⟨e1.le, e2.le⟩
  have hqi : IsQIWith (D ^ 2 + 3) (InAssoc lam) (InAssoc fun w ↦ lam' (autOf σ w))
      (psi lam fun w ↦ lam' (autOf σ w)) :=
    transfer hlam (fun w ↦ hlam' _) (Nat.one_le_pow 2 D (by omega)) hcomp
  obtain ⟨hg1, hg2, hg3⟩ :=
    relabelMap_isometry σ (lam := fun w ↦ lam' (autOf σ w)) (lam' := lam') (fun w ↦ hlam' _)
      fun _ ↦ rfl
  refine ⟨fun x ↦ relabelMap σ (fun w ↦ lam' (autOf σ w)) lam'
    (psi lam (fun w ↦ lam' (autOf σ w)) x), hqi.comp_isometry hg1 hg2 hg3, ?_⟩
  show relabelMap σ (fun w ↦ lam' (autOf σ w)) lam' (psi lam (fun w ↦ lam' (autOf σ w)) []) = []
  rw [psi_nil hlam, relabelMap_nil σ lam' fun w ↦ hlam' _]

/-! ### The good event and `thm:chains` -/

/-- A sample with a non-terminating chain in either coordinate is a null event. -/
lemma twoSampleMeasure_not_chains (ht : 0 < t) (ht1 : t ≤ 1) :
    twoSampleMeasure ht ht1
      {ω : (Word → Bool) × (Word → Bool) | ¬ (Chains ω.1 ∧ Chains ω.2)} = 0 := by
  have hbadsub : {ω : (Word → Bool) × (Word → Bool) | ¬ (Chains ω.1 ∧ Chains ω.2)}
      ⊆ ({χ : Word → Bool | ¬ Chains χ} ×ˢ (Set.univ : Set (Word → Bool)))
        ∪ ((Set.univ : Set (Word → Bool)) ×ˢ {χ : Word → Bool | ¬ Chains χ}) := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, Set.mem_ofPred_eq, and_true, true_and]
    by_cases hc : Chains ω.1
    · exact Or.inr fun hc2 ↦ hω ⟨hc, hc2⟩
    · exact Or.inl hc
  refine measure_mono_null hbadsub (measure_union_null ?_ ?_) <;>
    simp [twoSampleMeasure, Measure.prod_prod, chainMeasure_not_chains ht ht1]

/-- **The good event has full probability**: almost surely every chain of both
samples terminates. -/
theorem twoSampleMeasure_chains_ae (ht : 0 < t) (ht1 : t ≤ 1) :
    twoSampleMeasure ht ht1
      {ω : (Word → Bool) × (Word → Bool) | Chains ω.1 ∧ Chains ω.2} = 1 := by
  refine le_antisymm prob_le_one ?_
  have hcover : (Set.univ : Set ((Word → Bool) × (Word → Bool)))
      ⊆ {ω : (Word → Bool) × (Word → Bool) | Chains ω.1 ∧ Chains ω.2}
        ∪ {ω : (Word → Bool) × (Word → Bool) | ¬ (Chains ω.1 ∧ Chains ω.2)} := by
    intro ω _
    by_cases hc : Chains ω.1 ∧ Chains ω.2
    · exact Or.inl hc
    · exact Or.inr hc
  calc (1 : ℝ≥0∞) = twoSampleMeasure ht ht1 Set.univ := (measure_univ).symm
    _ ≤ twoSampleMeasure ht ht1 ({ω | Chains ω.1 ∧ Chains ω.2}
          ∪ {ω | ¬ (Chains ω.1 ∧ Chains ω.2)}) := measure_mono hcover
    _ ≤ twoSampleMeasure ht ht1 {ω | Chains ω.1 ∧ Chains ω.2}
          + twoSampleMeasure ht ht1 {ω | ¬ (Chains ω.1 ∧ Chains ω.2)} := measure_union_le _ _
    _ = twoSampleMeasure ht ht1 {ω | Chains ω.1 ∧ Chains ω.2} := by
        rw [twoSampleMeasure_not_chains ht ht1, add_zero]

/-- **`thm:chains`** for the totalised labelling: on the good event the sample
tree of an offspring field is the tree associated with its label field. -/
lemma inTree_eq_inAssoc {χ : Word → Bool} (hχ : Chains χ) : InTree χ = InAssoc (labAux χ) := by
  rw [labAux_eq hχ]
  exact funext fun v ↦ propext (inTree_iff_inAssoc hχ v)

/-! ### `thm:twovalue` -/

/-- **`eq:rate`, the two-value rate.** Under the largeness conditions
`eq:d0-conditions`, outside an event of probability at most
`256 θ₁^{D(D-5/2)}` the trees of two independent samples of the two-value
offspring law admit a `(D²+3)`-quasi-isometry. -/
theorem twovalue_rate (ht : 0 < t) (ht1 : t < 1) {D : ℕ} (hD : 5 ≤ D)
    (h1 : (1 - t) ^ (D - 1) ≤ 1 / 10) (h2 : (1 - t) ^ (D ^ 2 - D) ≤ 1 / 2)
    (h3 : 36 * (1 - t) ^ (5 * D - 2) ≤ 1) (h4 : 16 * qBound (1 - t) D ≤ 1 / 10000) :
    twoSampleMeasure ht ht1.le
        {ω | ¬ ∃ f : Word → Word,
          IsQIWith (D ^ 2 + 3) (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f ∧ f [] = []}
      ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
  have hD2 : 2 ≤ D := by omega
  have hqb : (0 : ℝ) ≤ qBound (1 - t) D := qBound_nonneg _ _
  have hc1 : ENNReal.ofReal (256 * qBound (1 - t) D) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (by nlinarith)
  have hmc : twoSampleMeasure ht ht1.le (matchEvent D)ᶜ
      ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
    rw [prob_compl_eq_one_sub (measurableSet_matchEvent D)]
    calc (1 : ℝ≥0∞) - twoSampleMeasure ht ht1.le (matchEvent D)
        ≤ 1 - (1 - ENNReal.ofReal (256 * qBound (1 - t) D)) :=
          tsub_le_tsub_left (matching_prob_ge ht ht1 hD h1 h2 h3 h4) 1
      _ = ENNReal.ofReal (256 * qBound (1 - t) D) :=
          ENNReal.sub_sub_cancel ENNReal.one_ne_top hc1
  have hbad := twoSampleMeasure_not_chains ht ht1.le
  have hsub : {ω : (Word → Bool) × (Word → Bool) | ¬ ∃ f : Word → Word,
        IsQIWith (D ^ 2 + 3) (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f ∧ f [] = []}
      ⊆ (matchEvent D)ᶜ
        ∪ {ω : (Word → Bool) × (Word → Bool) | ¬ (Chains ω.1 ∧ Chains ω.2)} := by
    intro ω hω
    by_cases hM : ω ∈ matchEvent D
    · refine Or.inr fun hch ↦ hω ?_
      obtain ⟨σ, hσ⟩ := portrait_of_matchEvent hM
      exact qi_of_matching hD2 σ (one_le_labAux hch.1) (one_le_labAux hch.2) hσ
    · exact Or.inl hM
  calc twoSampleMeasure ht ht1.le {ω | ¬ ∃ f : Word → Word,
          IsQIWith (D ^ 2 + 3) (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f ∧ f [] = []}
      ≤ twoSampleMeasure ht ht1.le ((matchEvent D)ᶜ
          ∪ {ω : (Word → Bool) × (Word → Bool) | ¬ (Chains ω.1 ∧ Chains ω.2)}) :=
        measure_mono hsub
    _ ≤ twoSampleMeasure ht ht1.le (matchEvent D)ᶜ
        + twoSampleMeasure ht ht1.le {ω | ¬ (Chains ω.1 ∧ Chains ω.2)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by rw [hbad, add_zero]; exact hmc

/-- **`thm:twovalue`, the almost sure statement**: almost surely the trees of
two independent samples are quasi-isometric, for some constant.  The largeness
conditions `eq:d0-conditions` are met at some scale by `exists_scale`. -/
theorem twovalue_ae (ht : 0 < t) (ht1 : t < 1) :
    twoSampleMeasure ht ht1.le
        {ω | ¬ ∃ (K : ℕ) (f : Word → Word),
          IsQIWith K (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f} = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) (zero_le)
  obtain ⟨D, hD, -, h1, h2, h3, h4, hlt⟩ :=
    exists_scale (by linarith : (0:ℝ) < 1 - t) (by linarith : (1:ℝ) - t < 1)
      (NNReal.coe_pos.mpr hε) 0
  have hsub : {ω : (Word → Bool) × (Word → Bool) | ¬ ∃ (K : ℕ) (f : Word → Word),
        IsQIWith K (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f}
      ⊆ {ω : (Word → Bool) × (Word → Bool) | ¬ ∃ f : Word → Word,
        IsQIWith (D ^ 2 + 3) (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f ∧ f [] = []} := by
    rintro ω hω ⟨f, hf, -⟩
    exact hω ⟨D ^ 2 + 3, f, hf⟩
  calc twoSampleMeasure ht ht1.le {ω | ¬ ∃ (K : ℕ) (f : Word → Word),
          IsQIWith K (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f}
      ≤ twoSampleMeasure ht ht1.le {ω | ¬ ∃ f : Word → Word,
          IsQIWith (D ^ 2 + 3) (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f ∧ f [] = []} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := twovalue_rate ht ht1 hD h1 h2 h3 h4
    _ ≤ (ε : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hlt.le
    _ = 0 + (ε : ℝ≥0∞) := (zero_add _).symm

/-- **`thm:twovalue`, `eq:rate` on the sample trees.** Under the largeness
conditions `eq:d0-conditions`, outside an event of probability at most
`256 θ₁^{D(D-5/2)}` the two sampled Galton-Watson trees admit a
`(D²+3)`-quasi-isometry. The failure event differs from the one of
`twovalue_rate` only inside the null event that some chain fails to terminate,
where `thm:chains` identifies the sample tree with the associated tree. -/
theorem twovalue_rate_tree (ht : 0 < t) (ht1 : t < 1) {D : ℕ} (hD : 5 ≤ D)
    (h1 : (1 - t) ^ (D - 1) ≤ 1 / 10) (h2 : (1 - t) ^ (D ^ 2 - D) ≤ 1 / 2)
    (h3 : 36 * (1 - t) ^ (5 * D - 2) ≤ 1) (h4 : 16 * qBound (1 - t) D ≤ 1 / 10000) :
    twoSampleMeasure ht ht1.le
        {ω | ¬ ∃ f : Word → Word, IsQIWith (D ^ 2 + 3) (InTree ω.1) (InTree ω.2) f ∧ f [] = []}
      ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
  have hsub : {ω : (Word → Bool) × (Word → Bool) | ¬ ∃ f : Word → Word,
        IsQIWith (D ^ 2 + 3) (InTree ω.1) (InTree ω.2) f ∧ f [] = []}
      ⊆ {ω : (Word → Bool) × (Word → Bool) | ¬ ∃ f : Word → Word,
          IsQIWith (D ^ 2 + 3) (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f ∧ f [] = []}
        ∪ {ω : (Word → Bool) × (Word → Bool) | ¬ (Chains ω.1 ∧ Chains ω.2)} := by
    intro ω hω
    by_cases hch : Chains ω.1 ∧ Chains ω.2
    · refine Or.inl fun hcon ↦ hω ?_
      rwa [inTree_eq_inAssoc hch.1, inTree_eq_inAssoc hch.2]
    · exact Or.inr hch
  calc twoSampleMeasure ht ht1.le
        {ω | ¬ ∃ f : Word → Word, IsQIWith (D ^ 2 + 3) (InTree ω.1) (InTree ω.2) f ∧ f [] = []}
      ≤ twoSampleMeasure ht ht1.le ({ω | ¬ ∃ f : Word → Word,
            IsQIWith (D ^ 2 + 3) (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f ∧ f [] = []}
          ∪ {ω | ¬ (Chains ω.1 ∧ Chains ω.2)}) := measure_mono hsub
    _ ≤ twoSampleMeasure ht ht1.le {ω | ¬ ∃ f : Word → Word,
            IsQIWith (D ^ 2 + 3) (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f ∧ f [] = []}
        + twoSampleMeasure ht ht1.le {ω | ¬ (Chains ω.1 ∧ Chains ω.2)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
        rw [twoSampleMeasure_not_chains ht ht1.le, add_zero]
        exact twovalue_rate ht ht1 hD h1 h2 h3 h4

/-- **`eq:rate` past one threshold**: there is `D₀ = D₀(θ₁)` such that for every
`D ≥ D₀` the two sampled Galton-Watson trees admit a `(D²+3)`-quasi-isometry
outside an event of probability at most `256·θ₁^{D(D-5/2)}`, the largeness
conditions `eq:d0-conditions` holding at every scale past `D₀` by
`forall_scale`. -/
theorem exists_twovalue_rate_tree (ht : 0 < t) (ht1 : t < 1) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      twoSampleMeasure ht ht1.le
          {ω | ¬ ∃ f : Word → Word,
            IsQIWith (D ^ 2 + 3) (InTree ω.1) (InTree ω.2) f ∧ f [] = []}
        ≤ ENNReal.ofReal (256 * qBound (1 - t) D) := by
  obtain ⟨D₀, hD₀⟩ := forall_scale (by linarith : (0:ℝ) < 1 - t)
    (by linarith : (1:ℝ) - t < 1)
  refine ⟨D₀, fun D hD ↦ ?_⟩
  obtain ⟨hD5, h1, h2, h3, h4⟩ := hD₀ D hD
  exact twovalue_rate_tree ht ht1 hD5 h1 h2 h3 h4

/-- **`thm:twovalue` on the sample trees, the almost sure statement**: if the
largeness conditions `eq:d0-conditions` hold at scales driving the rate to zero,
then almost surely the two sampled Galton-Watson trees are quasi-isometric, for
some constant. -/
theorem twovalue_ae_tree (ht : 0 < t) (ht1 : t < 1) :
    twoSampleMeasure ht ht1.le
        {ω | ¬ ∃ (K : ℕ) (f : Word → Word),
          IsQIWith K (InTree ω.1) (InTree ω.2) f ∧ f [] = []} = 0 := by
  have hsub : {ω : (Word → Bool) × (Word → Bool) | ¬ ∃ (K : ℕ) (f : Word → Word),
        IsQIWith K (InTree ω.1) (InTree ω.2) f ∧ f [] = []}
      ⊆ {ω : (Word → Bool) × (Word → Bool) | ¬ ∃ (K : ℕ) (f : Word → Word),
          IsQIWith K (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f}
        ∪ {ω : (Word → Bool) × (Word → Bool) | ¬ (Chains ω.1 ∧ Chains ω.2)} := by
    intro ω hω
    by_cases hch : Chains ω.1 ∧ Chains ω.2
    · refine Or.inl fun hcon ↦ hω ?_
      obtain ⟨K, f, hf⟩ := hcon
      rw [inTree_eq_inAssoc hch.1, inTree_eq_inAssoc hch.2]
      refine hf.exists_root_fixing ?_
      show InAssoc (labAux ω.2) []
      rw [← inTree_eq_inAssoc hch.2]
      exact InTree.root
    · exact Or.inr hch
  refine le_antisymm ?_ zero_le
  calc twoSampleMeasure ht ht1.le
        {ω | ¬ ∃ (K : ℕ) (f : Word → Word),
          IsQIWith K (InTree ω.1) (InTree ω.2) f ∧ f [] = []}
      ≤ twoSampleMeasure ht ht1.le ({ω | ¬ ∃ (K : ℕ) (f : Word → Word),
            IsQIWith K (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f}
          ∪ {ω | ¬ (Chains ω.1 ∧ Chains ω.2)}) := measure_mono hsub
    _ ≤ twoSampleMeasure ht ht1.le {ω | ¬ ∃ (K : ℕ) (f : Word → Word),
            IsQIWith K (InAssoc (labFst ω)) (InAssoc (labSnd ω)) f}
        + twoSampleMeasure ht ht1.le {ω | ¬ (Chains ω.1 ∧ Chains ω.2)} := measure_union_le _ _
    _ = 0 := by
        rw [twovalue_ae ht ht1, twoSampleMeasure_not_chains ht ht1.le, add_zero]

/-! ### The two endpoints of the family -/

/-- The identity is a `1`-quasi-isometry of a vertex set with itself. -/
lemma isQIWith_one_id (T : Word → Prop) : IsQIWith 1 T T id := by
  refine ⟨fun x hx ↦ hx, fun x y _ _ ↦ ?_, fun x y _ _ ↦ ?_, fun y' hy' ↦ ⟨y', hy', ?_⟩⟩
  · show treeDist x y ≤ 1 * treeDist x y + 1
    omega
  · show treeDist x y ≤ 1 * treeDist x y + 1 * 1
    omega
  · show treeDist y' y' ≤ 1
    rw [treeDist_self]
    omega

/-- **The endpoint fields are constant**: at `t = 0` and `t = 1` every vertex of
the offspring field almost surely carries the deterministic offspring count. -/
lemma bernoulliField_ae_const {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (b : Bool)
    (hb : t = if b then 1 else 0) :
    ∀ᵐ χ ∂(BranchingProcess.bernoulliField (ι := Word) ht0 ht1), ∀ v : Word, χ v = b := by
  rw [ae_iff]
  have hsub : {χ : Word → Bool | ¬ ∀ v : Word, χ v = b}
      ⊆ ⋃ v : Word, {χ : Word → Bool | ¬ χ v = b} := by
    intro χ hχ
    push Not at hχ
    obtain ⟨v, hv⟩ := hχ
    exact Set.mem_iUnion.mpr ⟨v, hv⟩
  refine measure_mono_null hsub (measure_iUnion_null fun v ↦ ?_)
  have htrue := BranchingProcess.bernoulliField_apply_true (ι := Word) ht0 ht1 v
  cases b with
  | true =>
      have hset : {χ : Word → Bool | ¬ χ v = true}
          = {χ : Word → Bool | χ v = true}ᶜ := rfl
      rw [hset, measure_compl ?_ (measure_ne_top _ _), htrue, measure_univ, hb]
      · simp
      · exact BranchingProcess.measurable_bernoulliField_coord v (measurableSet_singleton true)
  | false =>
      have hset : {χ : Word → Bool | ¬ χ v = false}
          = {χ : Word → Bool | χ v = true} := by
        ext χ
        simp [Bool.not_eq_false]
      rw [hset, htrue, hb]
      simp

/-- **The deterministic members of the family**: at an endpoint both samples
are almost surely the same deterministic tree, the ray at `t = 0` and the
binary tree at `t = 1`, and the identity matches them. -/
lemma twovalue_ae_tree_const {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (b : Bool)
    (hb : t = if b then 1 else 0) :
    ((BranchingProcess.bernoulliField (ι := Word) ht0 ht1).prod
        (BranchingProcess.bernoulliField ht0 ht1))
      {ω | ¬ ∃ (K : ℕ) (f : Word → Word),
        IsQIWith K (InTree ω.1) (InTree ω.2) f ∧ f [] = []} = 0 := by
  have hae := ae_iff.mp (bernoulliField_ae_const ht0 ht1 b hb)
  have hnull : ((BranchingProcess.bernoulliField (ι := Word) ht0 ht1).prod
      (BranchingProcess.bernoulliField ht0 ht1))
      ({χ : Word → Bool | ¬ ∀ v : Word, χ v = b} ×ˢ Set.univ
        ∪ Set.univ ×ˢ {χ : Word → Bool | ¬ ∀ v : Word, χ v = b}) = 0 := by
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod, hae, zero_mul]
    · rw [Measure.prod_prod, hae, mul_zero]
  refine measure_mono_null (fun ω hω ↦ ?_) hnull
  by_cases h1 : ∀ v : Word, ω.1 v = b
  · by_cases h2 : ∀ v : Word, ω.2 v = b
    · exfalso
      refine hω ⟨1, id, ?_, rfl⟩
      have he : InTree ω.1 = InTree ω.2 := by
        rw [funext h1, funext h2]
      rw [he]
      exact isQIWith_one_id _
    · exact Or.inr ⟨Set.mem_univ _, h2⟩
  · exact Or.inl ⟨h1, Set.mem_univ _⟩

/-- **`thm:twovalue` on the whole two-value family, the almost sure
statement**: for every offspring law with `θ₁ + θ₂ = 1`, the endpoints
included, the two sampled Galton-Watson trees are almost surely
quasi-isometric.  At `t = 0` the sample is the ray, at `t = 1` the binary
tree, and in the interior the statement is `twovalue_ae_tree`. -/
theorem twovalue_ae_tree_family {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((BranchingProcess.bernoulliField (ι := Word) ht0 ht1).prod
        (BranchingProcess.bernoulliField ht0 ht1))
      {ω | ¬ ∃ (K : ℕ) (f : Word → Word),
        IsQIWith K (InTree ω.1) (InTree ω.2) f ∧ f [] = []} = 0 := by
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · exact twovalue_ae_tree_const ht0 ht1 false (by rw [← h0]; rfl)
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · exact twovalue_ae_tree_const ht0 ht1 true (by rw [h1]; rfl)
  · exact twovalue_ae_tree h0 h1

end ChainClasses
