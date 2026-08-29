/-
`thm:regime-obstructions`\labelcref{it:obstr-hair} of `gw_classes_simple.tex`:
conditioned on survival, a sample of an offspring law on `{0,1,2}` with
`θ₀ > 0` almost surely has hairs of unbounded depth.

The sample tree is read as a set of binary words through the alphabet
translation, the setting `Trichotomy.lean` assembles the classification in.
The hairs are the bushes: a bush is joined to the rest of the sample by the
single edge at its neck vertex, so it is a component of the punctured sample,
finite because its subtree dies, and its depth is realised by a deepest bush
vertex.  A bush of depth exceeding `n` appears almost surely because the shape
`deepShape n`, one neck vertex carrying the complete binary tree of height
`n`, has positive mass, and by the product formula of `thm:shape-iid` the
shapes along a ray of index words avoid it with probability `(1-p)^N → 0`.

* `letterBack`, `unletters`, `letters_treeDist`, `sampleWord`, `sampleEquiv`:
  the alphabet translation and its inverse, an isometry of the two ambient
  trees, and the sample of an offspring field as a set of binary words.
* `exists_componentCompl_cone`, `exists_isHair_cone`, `UnboundedHairs`,
  `unboundedHairs_of_deep_cones`: the deterministic half.  In the graph of a
  prefix-closed set the vertices extending a child `x ++ [b]` form the
  component of `x`'s complement containing it; when that cone is finite it is
  a hair at `x`, of depth the largest distance to `x`, realised by a deepest
  cone vertex.
* `Tri.complete`, `deepShape`, `shapeMass_deepShape_pos`: the witness shape,
  one neck vertex decorated by the complete binary tree of height `n`; it is
  supported, so its mass is at least `shapeWeight θ ^ |σ|`.
* `survivalMeasure_shapes_avoid`, `ae_exists_deepShape`: the shapes over a
  prefix-closed finite set of index words avoid a shape `σ₀` with probability
  `(1 - shapeMass θ σ₀)^{|S|}`, by the product formula of `thm:shape-iid`, so
  almost surely some shape along the leftmost ray of index words equals
  `deepShape n`.
* `deep_cone_of_shapeAt`: the bridge.  A copy whose shape is `deepShape n`
  has a neck vertex with a dying second child whose subtree realises the
  complete binary tree, giving a finite cone with a vertex at distance
  `n + 1` from the neck vertex.
* `unbounded_hairs_ae`, `HairsInHairyRegime`, `hairsInHairyRegime`:
  **`thm:regime-obstructions`\labelcref{it:obstr-hair}**, in the form the
  separations of `Trichotomy.lean` consume.
-/
import ChainClasses.ThreeRays
import ChainClasses.ShapeLabelLaw
import ChainClasses.ShapeEtaSelf

namespace ChainClasses

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BranchingProcess (Offspring IsHair sample survivalMeasure Survives)

/-! ### The two ambient alphabets -/

/-- The letter of the index alphabet named by a letter of the ambient alphabet,
the inverse of `letterOf`. -/
def letterBack (i : Fin 2) : Bool := decide (i = 1)

@[simp] lemma letterBack_letterOf (b : Bool) : letterBack (letterOf b) = b := by
  cases b <;> rfl

@[simp] lemma letterOf_letterBack (i : Fin 2) : letterOf (letterBack i) = i := by
  revert i; decide

/-- A word of the ambient alphabet read letter by letter in the index alphabet. -/
def unletters (v : Amb) : Word := v.map letterBack

@[simp] lemma unletters_letters (a : Word) : unletters (letters a) = a := by
  simp [unletters, letters, List.map_map, Function.comp_def]

@[simp] lemma letters_unletters (v : Amb) : letters (unletters v) = v := by
  simp [unletters, letters, List.map_map, Function.comp_def]

/-- The letterwise translation is the constant-letter-map translation of
`ShapeDecomposition`. -/
lemma letters_eq_transWith (a : Word) : transWith (fun _ ↦ letterOf) a = letters a := by
  induction a using List.reverseRecOn with
  | nil => rfl
  | append_singleton a b ih => rw [transWith_concat, ih, letters_append]; rfl

/-- **The alphabet translation is an isometry.** -/
lemma letters_treeDist (a a' : Word) :
    BranchingProcess.treeDist (letters a) (letters a') = treeDist a a' := by
  rw [← letters_eq_transWith, ← letters_eq_transWith]
  exact transWith_treeDist (fun _ ↦ letterOf_injective) a a'

lemma letters_prefix {a a' : Word} (h : a <+: a') : letters a <+: letters a' :=
  h.map letterOf

lemma letters_injective : Function.Injective letters := fun a a' h ↦ by
  rw [← unletters_letters a, ← unletters_letters a', h]

lemma unletters_append (v v' : Amb) : unletters (v ++ v') = unletters v ++ unletters v' :=
  List.map_append ..

/-- Two prefixes of one word of the same length agree. -/
lemma eq_of_prefix_of_length {x y w : Amb} (hx : x <+: w) (hy : y <+: w)
    (h : x.length = y.length) : x = y := by
  rw [List.prefix_iff_eq_take.mp hx, List.prefix_iff_eq_take.mp hy, h]

lemma unletters_injective : Function.Injective unletters := by
  intro x y h
  rw [← letters_unletters x, ← letters_unletters y, h]

/-- The tree distance is read through the alphabet translation. -/
lemma treeDist_unletters (x y : Amb) :
    treeDist (unletters x) (unletters y) = BranchingProcess.treeDist x y := by
  rw [← letters_treeDist, letters_unletters, letters_unletters]

/-! ### The sample of an offspring field as a set of binary words -/

/-- The sample tree of an offspring field on the ambient binary tree, read as a
set of binary words through the alphabet translation. -/
def sampleWord (c : Amb → ℕ) (a : Word) : Prop := letters a ∈ sample c

lemma prefixClosed_sampleWord (c : Amb → ℕ) : PrefixClosed (sampleWord c) :=
  fun _ _ huv hv ↦ BranchingProcess.Subtree.mem_of_prefix (letters_prefix huv) hv

lemma sampleWord_nil (c : Amb → ℕ) : sampleWord c [] :=
  BranchingProcess.nil_mem_sample c

lemma sampleWord_unletters {c : Amb → ℕ} {x : Amb} (hx : x ∈ sample c) :
    sampleWord c (unletters x) := by
  show letters (unletters x) ∈ sample c
  rwa [letters_unletters]

/-- The vertices of the sample, transported to the index alphabet. -/
noncomputable def sampleEquiv (c : Amb → ℕ) :
    {a : Word // sampleWord c a} ≃ {v : Amb // v ∈ sample c} where
  toFun a := ⟨letters a.1, a.2⟩
  invFun v := ⟨unletters v.1, by simp only [sampleWord, letters_unletters]; exact v.2⟩
  left_inv a := by ext; simp
  right_inv v := by ext; simp

/-! ### The cone above a child is a component of the punctured tree -/

variable {T : Word → Prop}

/-- One step of the tree metric keeps the cone: a neighbour of a vertex
extending `x ++ [b]`, other than `x` itself, extends `x ++ [b]` too. -/
lemma prefix_of_adj {x : Word} {b : Bool} {p q : {w : Word // T w}}
    (hadj : (wordGraph T).Adj p q) (hqx : q.1 ≠ x) (hp : x ++ [b] <+: p.1) :
    x ++ [b] <+: q.1 := by
  rcases treeDist_eq_one_iff.mp (wordGraph_adj.mp hadj) with ⟨b', hb'⟩ | ⟨b', hb'⟩
  · exact hp.trans (by rw [hb']; exact List.prefix_append _ _)
  · rcases eq_or_ne (x ++ [b]) p.1 with heq | hne
    · exact absurd ((List.append_inj' (heq.trans hb') rfl).1).symm hqx
    · have hq1 : q.1 <+: p.1 := by rw [hb']; exact List.prefix_append _ _
      refine prefix_of_prefix_of_length_le hp hq1 ?_
      have hlt : (x ++ [b]).length < p.1.length :=
        lt_of_le_of_ne hp.length_le fun h ↦ hne (hp.eq_of_length h)
      rw [hb'] at hlt
      simp only [List.length_append, List.length_singleton] at hlt ⊢
      omega

/-- **The cone above a child is a component.**  In the graph of a prefix-closed
set the vertices extending `x ++ [b]` are the component of the complement of
`x` containing `x ++ [b]`. -/
theorem exists_componentCompl_cone (hT : PrefixClosed T) {x : Word} {b : Bool}
    (hx : T x) (hy : T (x ++ [b])) :
    ∃ C : (wordGraph T).ComponentCompl ({(⟨x, hx⟩ : {w : Word // T w})} : Set {w : Word // T w}),
      (C : Set {w : Word // T w}) = {w : {w : Word // T w} | x ++ [b] <+: w.1} := by
  have hyx : (⟨x ++ [b], hy⟩ : {w : Word // T w})
      ∉ ({(⟨x, hx⟩ : {w : Word // T w})} : Set {w : Word // T w}) := by
    simp only [Set.mem_singleton_iff]
    intro h
    have := congrArg (fun w : {w : Word // T w} ↦ w.1.length) h
    simp at this
  refine ⟨(wordGraph T).componentComplMk hyx, Set.eq_of_subset_of_subset ?_ ?_⟩
  · -- every component vertex extends the child: the walk to `x ++ [b]` avoids `x`
    intro z hz
    rw [SetLike.mem_coe, SimpleGraph.ComponentCompl.mem_supp_iff] at hz
    obtain ⟨hzK, hzC⟩ := hz
    obtain ⟨W⟩ := (SimpleGraph.ConnectedComponent.exact hzC).symm
    show x ++ [b] <+: z.1
    have hwalk : ∀ {p q : ↥(({(⟨x, hx⟩ : {w : Word // T w})} : Set {w : Word // T w})ᶜ)}
        (_ : ((wordGraph T).induce
          (({(⟨x, hx⟩ : {w : Word // T w})} : Set {w : Word // T w})ᶜ)).Walk p q),
        x ++ [b] <+: p.1.1 → x ++ [b] <+: q.1.1 := by
      intro p q W
      induction W with
      | nil => exact id
      | @cons p' v' q' hadj W ih =>
          intro hp
          exact ih (prefix_of_adj (SimpleGraph.induce_adj.mp hadj)
            (fun h ↦ v'.2 (Set.mem_singleton_iff.mpr (Subtype.ext h))) hp)
    exact hwalk W List.prefix_rfl
  · -- every cone vertex reaches the child along its ancestors, avoiding `x`
    have key : ∀ (t : Word) (hzv : T (x ++ [b] ++ t)),
        (⟨x ++ [b] ++ t, hzv⟩ : {w : Word // T w}) ∈ (wordGraph T).componentComplMk hyx := by
      intro t
      induction t using List.reverseRecOn with
      | nil =>
          intro hzv
          have he : (⟨x ++ [b] ++ [], hzv⟩ : {w : Word // T w}) = ⟨x ++ [b], hy⟩ :=
            Subtype.ext (List.append_nil _)
          rw [he]
          exact SimpleGraph.componentComplMk_mem _ hyx
      | append_singleton t a ih =>
          intro hzv
          have hTt : T (x ++ [b] ++ t) :=
            hT (by rw [← List.append_assoc]; exact List.prefix_append _ _) hzv
          refine SimpleGraph.ComponentCompl.mem_of_adj ⟨x ++ [b] ++ t, hTt⟩ _ (ih hTt) ?_ ?_
          · simp only [Set.mem_singleton_iff]
            intro h
            have hlen := congrArg (fun w : {w : Word // T w} ↦ w.1.length) h
            simp only [List.length_append, List.length_singleton] at hlen
            omega
          · rw [wordGraph_adj]
            show treeDist (x ++ [b] ++ t) (x ++ [b] ++ (t ++ [a])) = 1
            rw [treeDist_of_prefix (by rw [← List.append_assoc]; exact List.prefix_append _ _),
              ← List.append_assoc]
            simp only [List.length_append, List.length_singleton]
            omega
    rintro ⟨zv, hzv⟩ hz
    rw [SetLike.mem_coe]
    obtain ⟨t, rfl⟩ := hz
    exact key t hzv

/-- **A finite cone is a hair**, of depth the largest distance to the puncture,
realised by a deepest cone vertex. -/
theorem exists_isHair_cone (hT : PrefixClosed T) {x : Word} {b : Bool}
    (hx : T x) (hy : T (x ++ [b])) (hfin : {w : Word | T w ∧ x ++ [b] <+: w}.Finite) :
    ∃ h : ℕ, IsHair (wordGraph T) ⟨x, hx⟩ {w : {w : Word // T w} | x ++ [b] <+: w.1} h ∧
      ∀ z : Word, (hz : T z) → x ++ [b] <+: z →
        (wordGraph T).dist ⟨z, hz⟩ ⟨x, hx⟩ ≤ h := by
  classical
  have hfin' : {w : {w : Word // T w} | x ++ [b] <+: w.1}.Finite := by
    have he : {w : {w : Word // T w} | x ++ [b] <+: w.1}
        = Subtype.val ⁻¹' {w : Word | T w ∧ x ++ [b] <+: w} := by
      ext w
      simp [w.2]
    rw [he]
    exact Set.Finite.preimage Subtype.val_injective.injOn hfin
  have hFne : hfin'.toFinset.Nonempty :=
    ⟨⟨x ++ [b], hy⟩, hfin'.mem_toFinset.mpr List.prefix_rfl⟩
  obtain ⟨w0, hw0F, hw0⟩ :=
    hfin'.toFinset.exists_mem_eq_sup hFne fun w ↦ (wordGraph T).dist w ⟨x, hx⟩
  refine ⟨hfin'.toFinset.sup fun w ↦ (wordGraph T).dist w ⟨x, hx⟩,
    ⟨exists_componentCompl_cone hT hx hy, fun v hv ↦ ?_, ⟨w0, ?_, hw0.symm⟩⟩, fun z hz hpre ↦ ?_⟩
  · exact Finset.le_sup (f := fun w ↦ (wordGraph T).dist w ⟨x, hx⟩)
      (hfin'.mem_toFinset.mpr hv)
  · exact hfin'.mem_toFinset.mp hw0F
  · exact Finset.le_sup (f := fun w ↦ (wordGraph T).dist w ⟨x, hx⟩)
      (hfin'.mem_toFinset.mpr hpre)

/-- **`thm:regime-obstructions`\labelcref{it:obstr-hair}**, in the form
`thm:hair-separation` consumes: hairs of unbounded depth. -/
def UnboundedHairs (T : Word → Prop) : Prop :=
  ∀ n : ℕ, ∃ (c : {w : Word // T w}) (P : Set {w : Word // T w}) (h : ℕ),
    n < h ∧ IsHair (wordGraph T) c P h

/-- A finite cone with a deep vertex for every depth gives hairs of unbounded
depth. -/
theorem unboundedHairs_of_deep_cones (hT : PrefixClosed T)
    (hdeep : ∀ n : ℕ, ∃ (x : Word) (b : Bool) (z : Word), T (x ++ [b]) ∧
      {w : Word | T w ∧ x ++ [b] <+: w}.Finite ∧ T z ∧ x ++ [b] <+: z ∧ n < treeDist z x) :
    UnboundedHairs T := by
  intro n
  obtain ⟨x, b, z, hy, hfin, hz, hyz, hn⟩ := hdeep n
  have hx : T x := hT (List.prefix_append x [b]) hy
  obtain ⟨h, hhair, hle⟩ := exists_isHair_cone hT hx hy hfin
  refine ⟨⟨x, hx⟩, _, h, ?_, hhair⟩
  have hd : treeDist z x ≤ h := by
    have h0 := hle z hz hyz
    rwa [wordGraph_dist hT] at h0
  omega

/-! ### The witness shape: one neck vertex, a complete binary bush -/

/-- The complete binary tree of height `n`. -/
def Tri.complete : ℕ → Tri
  | 0 => .leaf
  | n + 1 => .two (Tri.complete n) (Tri.complete n)

/-- The complete binary tree has no vertex of exactly one child. -/
lemma Tri.complete_full : ∀ n, (Tri.complete n).Full
  | 0 => trivial
  | n + 1 => ⟨complete_full n, complete_full n⟩

/-- The complete binary tree of height `n` has a vertex at depth `n`. -/
lemma Tri.complete_isAddr : ∀ n, (Tri.complete n).IsAddr (List.replicate n false)
  | 0 => Tri.isAddr_nil _
  | n + 1 => by
      rw [List.replicate_succ]
      exact complete_isAddr n

/-- The shape whose neck vertex carries the complete binary tree of height
`n`: its realisation has a bush vertex at distance `n + 1` from the entry. -/
def deepShape (n : ℕ) : Shape := Shape.ofList [some (Tri.complete n)]

lemma decs_deepShape (n : ℕ) : (deepShape n).decs = [some (Tri.complete n)] :=
  Shape.decs_ofList _

lemma supported_deepShape (n : ℕ) : (deepShape n).Supported := by
  intro o ho
  rw [decs_deepShape, List.mem_singleton] at ho
  rw [ho]
  show (Tri.complete n).Full
  exact Tri.complete_full n

/-- The witness shape has positive mass, being supported. -/
lemma shapeMass_deepShape_pos (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (n : ℕ) : 0 < shapeMass θ (deepShape n) :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (pow_pos (shapeWeight_pos θ hq hq0 h2) _))
    (ofReal_pow_size_le_shapeMass_of_supported θ hq hq0 h2 (supported_deepShape n))

/-! ### The shapes avoid a fixed shape with geometric probability -/

open Classical in
/-- The complement mass: the shapes other than `σ₀` carry `1 - shapeMass θ σ₀`. -/
lemma tsum_shapeMass_ne (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (σ₀ : Shape) :
    ∑' σ : Shape, (if σ = σ₀ then 0 else shapeMass θ σ) = 1 - shapeMass θ σ₀ := by
  have htot := tsum_shapeMass θ hq hq0 h2
  have hsplit := ENNReal.tsum_eq_add_tsum_ite (f := shapeMass θ) σ₀
  rw [htot] at hsplit
  have hle : shapeMass θ σ₀ ≤ 1 := by
    rw [← htot]
    exact ENNReal.le_tsum σ₀
  have hne : shapeMass θ σ₀ ≠ ⊤ := (hle.trans_lt ENNReal.one_lt_top).ne
  exact ENNReal.eq_sub_of_add_eq hne (by rw [add_comm]; exact hsplit.symm)

/-- **The product formula against a fixed shape**: over a prefix-closed finite
set of index words the shapes avoid `σ₀` with probability
`(1 - shapeMass θ σ₀)^{|S|}`. -/
theorem survivalMeasure_shapes_avoid (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (σ₀ : Shape) (S : Finset Word)
    (hS : ∀ w ∈ S, ∀ p, p <+: w → p ∈ S) :
    survivalMeasure (N := 2) θ (⋂ w ∈ S, {c : Amb → ℕ | shapeAt c w ≠ σ₀})
      = (1 - shapeMass θ σ₀) ^ S.card := by
  classical
  set E := ⋂ w ∈ S, {c : Amb → ℕ | shapeAt c w ≠ σ₀} with hE
  have hEmeas : MeasurableSet E := by
    refine MeasurableSet.biInter S.countable_toSet fun w _ ↦ ?_
    have : {c : Amb → ℕ | shapeAt c w ≠ σ₀} = {c : Amb → ℕ | shapeAt c w = σ₀}ᶜ := rfl
    rw [this]
    exact (measurableSet_shapeAt_eq w σ₀).compl
  have hdecomp : survivalMeasure (N := 2) θ E
      = ∑' f : ↥S → Shape, survivalMeasure (N := 2) θ (E ∩ shapeEvent S f) := by
    conv_lhs => rw [← Set.inter_univ E, ← iUnion_shapeEvent S, Set.inter_iUnion]
    exact measure_iUnion
      (fun f f' hff ↦ (pairwise_shapeEvent S hff).mono Set.inter_subset_right
        Set.inter_subset_right)
      fun f ↦ hEmeas.inter (measurableSet_shapeEvent S f)
  have hsummand : ∀ f : ↥S → Shape, survivalMeasure (N := 2) θ (E ∩ shapeEvent S f)
      = ∏ w ∈ S.attach, (if f w = σ₀ then 0 else shapeMass θ (f w)) := by
    intro f
    by_cases hf : ∀ w : ↥S, f w ≠ σ₀
    · have hsub : shapeEvent S f ⊆ E := by
        intro c hc
        simp only [hE, Set.mem_iInter, Set.mem_setOf_eq]
        intro w hw
        rw [show shapeAt c w = f ⟨w, hw⟩ from hc ⟨w, hw⟩]
        exact hf ⟨w, hw⟩
      rw [Set.inter_eq_self_of_subset_right hsub, survivalMeasure_shapeEvent θ hq hq0 h2 S hS f]
      exact Finset.prod_congr rfl fun w _ ↦ (if_neg (hf w)).symm
    · push Not at hf
      obtain ⟨w₀, hw₀⟩ := hf
      have hempty : E ∩ shapeEvent S f = ∅ := by
        ext c
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, hE,
          Set.mem_iInter, Set.mem_setOf_eq]
        intro hcE hcev
        exact hcE w₀.1 w₀.2 (by rw [hcev w₀, hw₀])
      rw [hempty, measure_empty]
      exact (Finset.prod_eq_zero (Finset.mem_attach S w₀) (by rw [if_pos hw₀])).symm
  calc survivalMeasure (N := 2) θ E
      = ∑' f : ↥S → Shape, ∏ w ∈ S.attach, (if f w = σ₀ then 0 else shapeMass θ (f w)) := by
        rw [hdecomp]; exact tsum_congr hsummand
    _ = ∏ w ∈ S, ∑' σ : Shape, (if σ = σ₀ then 0 else shapeMass θ σ) :=
        tsum_pi_finset S fun _ σ ↦ if σ = σ₀ then 0 else shapeMass θ σ
    _ = ∏ _w ∈ S, (1 - shapeMass θ σ₀) :=
        Finset.prod_congr rfl fun w _ ↦ tsum_shapeMass_ne θ hq hq0 h2 σ₀
    _ = (1 - shapeMass θ σ₀) ^ S.card := Finset.prod_const _

/-! ### Along the leftmost ray of index words -/

/-- The first `n` index words of the leftmost ray. -/
def rayWords (n : ℕ) : Finset Word := (Finset.range n).image fun k ↦ List.replicate k false

lemma mem_rayWords {n : ℕ} {w : Word} :
    w ∈ rayWords n ↔ ∃ k < n, w = List.replicate k false := by
  simp only [rayWords, Finset.mem_image, Finset.mem_range]
  exact ⟨fun ⟨k, hk, h⟩ ↦ ⟨k, hk, h.symm⟩, fun ⟨k, hk, h⟩ ↦ ⟨k, hk, h.symm⟩⟩

lemma card_rayWords (n : ℕ) : (rayWords n).card = n := by
  rw [rayWords, Finset.card_image_of_injective _ fun k l h ↦ by
    simpa using congrArg List.length h]
  exact Finset.card_range n

lemma prefixClosed_rayWords {n : ℕ} : ∀ w ∈ rayWords n, ∀ p, p <+: w → p ∈ rayWords n := by
  intro w hw p hp
  obtain ⟨k, hk, rfl⟩ := mem_rayWords.mp hw
  have hlen : p.length ≤ k := by simpa using hp.length_le
  have hrep : p = List.replicate p.length false :=
    List.eq_replicate_iff.mpr ⟨rfl, fun x hx ↦ List.eq_of_mem_replicate (hp.subset hx)⟩
  exact mem_rayWords.mpr ⟨p.length, by omega, hrep⟩

/-- **A positive-mass shape appears almost surely** along the leftmost ray of
index words: avoiding it for ever has probability at most `(1-p)^N` for
every `N`. -/
theorem ae_exists_shapeAt (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) (σ₀ : Shape) (hσ : 0 < shapeMass θ σ₀) :
    ∀ᵐ c ∂(survivalMeasure (N := 2) θ), ∃ k : ℕ, shapeAt c (List.replicate k false) = σ₀ := by
  rw [ae_iff]
  have hle : ∀ n : ℕ,
      survivalMeasure (N := 2) θ {c : Amb → ℕ | ¬ ∃ k, shapeAt c (List.replicate k false) = σ₀}
        ≤ (1 - shapeMass θ σ₀) ^ n := by
    intro n
    have hsub : {c : Amb → ℕ | ¬ ∃ k, shapeAt c (List.replicate k false) = σ₀}
        ⊆ ⋂ w ∈ rayWords n, {c : Amb → ℕ | shapeAt c w ≠ σ₀} := by
      intro c hc
      simp only [Set.mem_setOf_eq, not_exists] at hc
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro w hw
      obtain ⟨k, _, rfl⟩ := mem_rayWords.mp hw
      exact hc k
    calc survivalMeasure (N := 2) θ _
        ≤ survivalMeasure (N := 2) θ (⋂ w ∈ rayWords n, {c : Amb → ℕ | shapeAt c w ≠ σ₀}) :=
          measure_mono hsub
      _ = (1 - shapeMass θ σ₀) ^ (rayWords n).card :=
          survivalMeasure_shapes_avoid θ hq hq0 h2 σ₀ _ prefixClosed_rayWords
      _ = (1 - shapeMass θ σ₀) ^ n := by rw [card_rayWords]
  have hlt : (1 : ℝ≥0∞) - shapeMass θ σ₀ < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hσ.ne'
  exact nonpos_iff_eq_zero.mp
    (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt) hle)

/-! ### From the witness shape to a hair in the sample -/

/-- **The bridge.**  A copy whose shape is `deepShape n` has a neck vertex
with a dying second child; the cone above that child is finite and reaches
depth `n + 1` below the neck vertex. -/
theorem deep_cone_of_shapeAt {c : Amb → ℕ} (hc : IsHairySample c) {w : Word} {n : ℕ}
    (hshape : shapeAt c w = deepShape n) :
    ∃ (x : Word) (b : Bool) (z : Word), sampleWord c (x ++ [b]) ∧
      {a : Word | sampleWord c a ∧ x ++ [b] <+: a}.Finite ∧
      sampleWord c z ∧ x ++ [b] <+: z ∧ n < treeDist z x := by
  obtain ⟨humem, husurv⟩ := entryV_mem_skeleton hc w
  -- the copy has one neck vertex, the entry itself
  have hsplit : splitDepth c (entryV c w) = 1 := by
    have h := congrArg Shape.necks hshape
    rw [shapeAt_necks] at h
    exact h
  -- its decoration is the complete binary tree
  have hdec : decAt c (entryV c w) = some (Tri.complete n) := by
    have h0 := shapeAt_decs_getElem? c w (i := 0) (by omega)
    have h1 : (shapeAt c w).decs = [some (Tri.complete n)] := by
      rw [hshape]
      exact decs_deepShape n
    rw [h1, neckRay_zero] at h0
    exact (Option.some.inj h0).symm
  have h2u : c (entryV c w) = 2 := by
    by_contra h
    rw [decAt, if_neg h] at hdec
    simp at hdec
  have hbush : bushTri (shift c (entryV c w ++ [bushLetter c (entryV c w)]))
      = Tri.complete n := by
    rw [decAt, if_pos h2u] at hdec
    exact Option.some.inj hdec
  -- the second child dies
  have hdeg : BranchingProcess.skeletonDegree (shift c (entryV c w)) = 1 := by
    have h := splitDepth_min husurv (k := 0) (by omega)
    rwa [neckRay_zero] at h
  have hnots : ¬ Survives (shift c (entryV c w ++ [bushLetter c (entryV c w)])) :=
    not_survives_bush husurv hdeg h2u
  have hymem : entryV c w ++ [bushLetter c (entryV c w)] ∈ sample c :=
    BranchingProcess.mem_sample_append_singleton.mpr ⟨humem, bushLetter_lt h2u⟩
  -- the bush has a vertex at depth `n`
  have haddr : letters (List.replicate n false)
      ∈ sample (shift c (entryV c w ++ [bushLetter c (entryV c w)])) := by
    refine (isAddr_bushTri (d := shift c (entryV c w ++ [bushLetter c (entryV c w)]))
      (fun v ↦ hc.offspring _) hnots (List.replicate n false)).mp ?_
    rw [hbush]
    exact Tri.complete_isAddr n
  have hzmem : (entryV c w ++ [bushLetter c (entryV c w)]) ++ letters (List.replicate n false)
      ∈ sample c := by
    rw [BranchingProcess.append_mem_sample_iff]
    exact ⟨hymem, haddr⟩
  -- the cone above the dying child is finite
  have hcamb : {v : Amb | v ∈ sample c
      ∧ entryV c w ++ [bushLetter c (entryV c w)] <+: v}.Finite := by
    have he : {v : Amb | v ∈ sample c ∧ entryV c w ++ [bushLetter c (entryV c w)] <+: v}
        = (fun r ↦ entryV c w ++ [bushLetter c (entryV c w)] ++ r)
          '' (sample (shift c (entryV c w ++ [bushLetter c (entryV c w)])) : Set Amb) := by
      ext v
      constructor
      · rintro ⟨hv, r, rfl⟩
        exact ⟨r, (BranchingProcess.append_mem_sample_iff ..).mp hv |>.2, rfl⟩
      · rintro ⟨r, hr, rfl⟩
        exact ⟨(BranchingProcess.append_mem_sample_iff ..).mpr ⟨hymem, hr⟩,
          List.prefix_append _ _⟩
    rw [he]
    exact (Set.not_infinite.mp hnots).image _
  -- transport to the index alphabet
  have hxb : unletters (entryV c w) ++ [letterBack (bushLetter c (entryV c w))]
      = unletters (entryV c w ++ [bushLetter c (entryV c w)]) := by
    rw [unletters_append]; rfl
  refine ⟨unletters (entryV c w), letterBack (bushLetter c (entryV c w)),
    unletters ((entryV c w ++ [bushLetter c (entryV c w)]) ++ letters (List.replicate n false)),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxb]
    exact sampleWord_unletters hymem
  · rw [hxb]
    refine Set.Finite.of_finite_image (f := letters) (hcamb.subset ?_)
      letters_injective.injOn
    rintro v ⟨a, ⟨ha, hpre⟩, rfl⟩
    refine ⟨ha, ?_⟩
    have h := letters_prefix hpre
    rwa [letters_unletters] at h
  · exact sampleWord_unletters hzmem
  · rw [unletters_append, hxb]
    exact List.prefix_append _ _
  · have hz : unletters
        ((entryV c w ++ [bushLetter c (entryV c w)]) ++ letters (List.replicate n false))
        = (unletters (entryV c w) ++ [letterBack (bushLetter c (entryV c w))])
          ++ List.replicate n false := by
      rw [unletters_append, unletters_letters, ← hxb]
    rw [hz, treeDist_comm, treeDist_of_prefix
      ((List.prefix_append _ _).trans (List.prefix_append _ _))]
    simp only [List.length_append, List.length_replicate, List.length_singleton]
    omega

/-! ### The obstruction, almost surely -/

/-- **`thm:regime-obstructions`\labelcref{it:obstr-hair}**: conditioned on
survival, the sample almost surely has hairs of unbounded depth. -/
theorem unbounded_hairs_ae (θ : Offspring 2) (hq : θ.extinction < 1)
    (hq0 : 0 < θ.extinction) (h2 : 0 < θ 2) :
    ∀ᵐ c ∂(survivalMeasure (N := 2) θ), UnboundedHairs (sampleWord c) := by
  have hae : ∀ᵐ c ∂(survivalMeasure (N := 2) θ), ∀ n : ℕ,
      ∃ k : ℕ, shapeAt c (List.replicate k false) = deepShape n :=
    ae_all_iff.mpr fun n ↦ ae_exists_shapeAt θ hq hq0 h2 (deepShape n)
      (shapeMass_deepShape_pos θ hq hq0 h2 n)
  filter_upwards [ae_isHairySample_of_pos θ hq h2, hae] with c hc hdeep
  refine unboundedHairs_of_deep_cones (prefixClosed_sampleWord c) fun n ↦ ?_
  obtain ⟨k, hk⟩ := hdeep n
  obtain ⟨x, b, z, hy, hfin, hz, hyz, hn⟩ := deep_cone_of_shapeAt hc hk
  exact ⟨x, b, z, hy, hfin, hz, hyz, hn⟩

/-- **`thm:regime-obstructions`\labelcref{it:obstr-hair} in regime (H)**, the
form the separations of `Trichotomy.lean` consume. -/
def HairsInHairyRegime : Prop :=
  ∀ θ : Offspring 2, θ.extinction < 1 → 0 < θ.extinction → 0 < θ 2 →
    ∀ᵐ c ∂(survivalMeasure (N := 2) θ), UnboundedHairs (sampleWord c)

/-- The obstruction holds: `unbounded_hairs_ae` packaged. -/
theorem hairsInHairyRegime : HairsInHairyRegime :=
  fun θ hq hq0 h2 ↦ unbounded_hairs_ae θ hq hq0 h2

end ChainClasses
