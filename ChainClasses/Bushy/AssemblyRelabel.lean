import ChainClasses.Shape.Assembly
import ChainClasses.Chain.Isometry

/-!
`thm:hairy` of `gw_classes_simple.tex`: the deterministic core of
**`thm:hairy`**.  A portrait matching the shape labels of two samples supplies
a marked quasi-isometry between the shape at every copy of the first sample and
the shape at the image copy of the second, and `thm:glued-transfer` glues these
into a quasi-isometry of the assemblies.  What has to be added to the gluing is
the step "the assembly of `(S(πw))_w` is isometric to that of `(S(w))_w`": the
portrait automorphism carries the copies of one assembly to the copies of the
other, and the gluing recursion follows it, because `autOf π` maps the children
of a word to the children of its image.

* `autOf_take` and `wedge_autOf_length`: the two facts about `autOf π` that the
  distance formulas of `ChainClasses.Shape.Assembly` consume, the prefix of a word
  going to the prefix of its image and the wedge to the wedge.
* `Assembly.relabel`, `Assembly.dist_relabel`, `Assembly.relabel_surjective`:
  **the relabelling of an assembly**, moving the copy at `w` to the copy at
  `autOf π w`, a distance-preserving surjection of the assembly of `σ ∘ autOf π`
  onto the assembly of `σ`.
* `IsQIMap` and its algebra `IsQIMap.mono`, `IsQIMap.comp`, `IsQIMap.exists_symm`,
  `IsQIMap.isometry_comp_left`, `IsQIMap.comp_isometry_symm`: `def:qi` between metric
  spaces with all three constants equal, the unmarked form of `IsMarkedQI`, in which
  `thm:glued-transfer` delivers its conclusion; the constant is monotone, composites are
  quasi-isometries at `3KK'`, quasi-inverses exist at `3K²`, and isometries transport in
  either direction.
* `qi_of_shape_matching`: **the deterministic core of `thm:hairy`**.  If the
  shape at `w` and the shape at `autOf π w` are `K`-comparable for every `w`,
  then the two assemblies admit an `8K²`-quasi-isometry.
-/

namespace ChainClasses

/-! ### The portrait automorphism on prefixes and wedges -/

/-- The portrait automorphism commutes with truncation: it maps the prefix of
length `i` of a word to the prefix of length `i` of its image. -/
lemma autOf_take (π : Word → Bool ≃ Bool) (v : Word) (i : ℕ) :
    autOf π (v.take i) = (autOf π v).take i := by
  rcases le_total i v.length with h | h
  · have hpre : autOf π (v.take i) <+: autOf π v := autOf_prefix π (List.take_prefix i v)
    have hlen : (autOf π (v.take i)).length = i := by
      rw [autOf_length, List.length_take, min_eq_left h]
    conv_lhs => rw [List.prefix_iff_eq_take.mp hpre, hlen]
  · have h1 : v.take i = v := List.take_of_length_le h
    have h2 : (autOf π v).take i = autOf π v :=
      List.take_of_length_le (by rw [autOf_length]; exact h)
    rw [h1, h2]

/-- The portrait automorphism preserves the depth of the wedge: the branch
point of two words goes to the branch point of their images. -/
lemma wedge_autOf_length (π : Word → Bool ≃ Bool) (u v : Word) :
    (wedge (autOf π u) (autOf π v)).length = (wedge u v).length := by
  by_cases h1 : u <+: v
  · rw [wedge_of_prefix h1, wedge_of_prefix (autOf_prefix π h1), autOf_length]
  · by_cases h2 : v <+: u
    · rw [wedge_comm (autOf π u) (autOf π v), wedge_comm u v, wedge_of_prefix h2,
        wedge_of_prefix (autOf_prefix π h2), autOf_length]
    · obtain ⟨p, a, b, hab, hpa, hpb⟩ := exists_diverge h1 h2
      obtain ⟨hab', hpa', hpb'⟩ := autOf_diverge π hab hpa hpb
      rw [wedge_of_diverge hab hpa hpb, wedge_of_diverge hab' hpa' hpb', autOf_length]

namespace Assembly

/-! ### The relabelling of an assembly -/

variable {σ σ' : Word → Shape}

/-- **The relabelling of an assembly along a portrait**: the copy at `w` of the
assembly of `σ ∘ autOf π` is the copy at `autOf π w` of the assembly of `σ`,
carrying the same shape and hence the same vertices. -/
def relabel (π : Word → Bool ≃ Bool) (σ : Word → Shape)
    (x : Assembly (fun w ↦ σ (autOf π w))) : Assembly σ :=
  ⟨autOf π x.copy, x.vert⟩

/-- **The relabelling is an isometry**: each of the three distance formulas of
the assembly is preserved, the portrait automorphism preserving lengths,
prefixes, truncations and wedges. -/
theorem dist_relabel (π : Word → Bool ≃ Bool) (σ : Word → Shape)
    (x y : Assembly (fun w ↦ σ (autOf π w))) :
    dist (relabel π σ x) (relabel π σ y) = dist x y := by
  obtain ⟨u, p⟩ := x
  obtain ⟨v, q⟩ := y
  show dist (⟨autOf π u, p⟩ : Assembly σ) ⟨autOf π v, q⟩
    = dist (⟨u, p⟩ : Assembly (fun w ↦ σ (autOf π w))) ⟨v, q⟩
  rcases copy_trichotomy u v with rfl | ⟨huv, hne⟩ | ⟨hvu, hne⟩ | ⟨hu, hv⟩
  · rw [dist_same σ (autOf π u) p q, dist_same (fun w ↦ σ (autOf π w)) u p q]
  · have hne' : autOf π u ≠ autOf π v := fun h ↦ hne (autOf_injective π h)
    rw [dist_anc σ (autOf_prefix π huv) hne' p q,
      dist_anc (fun w ↦ σ (autOf π w)) huv hne p q]
    simp only [autOf_length, ← autOf_take]
  · have hne' : autOf π v ≠ autOf π u := fun h ↦ hne (autOf_injective π h)
    rw [dist_comm (⟨autOf π u, p⟩ : Assembly σ),
      dist_comm (⟨u, p⟩ : Assembly (fun w ↦ σ (autOf π w))),
      dist_anc σ (autOf_prefix π hvu) hne' q p,
      dist_anc (fun w ↦ σ (autOf π w)) hvu hne q p]
    simp only [autOf_length, ← autOf_take]
  · have hu' : ¬ autOf π u <+: autOf π v := fun h ↦ hu ((autOf_prefix_iff π).mp h)
    have hv' : ¬ autOf π v <+: autOf π u := fun h ↦ hv ((autOf_prefix_iff π).mp h)
    rw [dist_div σ hu' hv' p q, dist_div (fun w ↦ σ (autOf π w)) hu hv p q]
    simp only [autOf_length, wedge_autOf_length, ← autOf_take]

/-- The relabelling is onto: every copy of the assembly of `σ` is the image of
a copy, the portrait automorphism being onto. -/
lemma relabel_surjective (π : Word → Bool ≃ Bool) (σ : Word → Shape) :
    Function.Surjective (relabel π σ) := by
  rintro ⟨v, q⟩
  obtain ⟨w, rfl⟩ := autOf_surjective π v
  exact ⟨⟨w, q⟩, rfl⟩

end Assembly

/-! ### Quasi-isometries of metric spaces -/

/-- **`def:qi`** between metric spaces, with all three constants equal to `K`:
the unmarked form of `IsMarkedQI`, and the shape in which
`thm:glued-transfer` delivers its conclusion. -/
structure IsQIMap (K : ℝ) {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : Prop where
  /-- The upper bound of `def:qi`. -/
  upper : ∀ a b, dist (f a) (f b) ≤ K * dist a b + K
  /-- The lower bound of `def:qi`, in division-free form. -/
  lower : ∀ a b, dist a b ≤ K * dist (f a) (f b) + K ^ 2
  /-- The image is `K`-dense. -/
  dense : ∀ b, ∃ a, dist (f a) b ≤ K

/-! ### The algebra of quasi-isometries -/

lemma IsQIMap.mono {K K' : ℝ} {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y}
    (hK : 0 ≤ K) (hKK' : K ≤ K') (hf : IsQIMap K f) : IsQIMap K' f := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun y => ?_⟩
  · have h1 := hf.upper a b
    have h2 : K * dist a b ≤ K' * dist a b := mul_le_mul_of_nonneg_right hKK' dist_nonneg
    linarith
  · have h1 := hf.lower a b
    have h2 : K * dist (f a) (f b) ≤ K' * dist (f a) (f b) :=
      mul_le_mul_of_nonneg_right hKK' dist_nonneg
    have h3 : K ^ 2 ≤ K' ^ 2 := by nlinarith
    linarith
  · obtain ⟨a, ha⟩ := hf.dense y
    exact ⟨a, ha.trans hKK'⟩

/-- Quasi-isometries of metric spaces compose, at the constant `3KK'`. -/
lemma IsQIMap.comp {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    {K K' : ℝ} (hK : 1 ≤ K) (hK' : 1 ≤ K') {f : X → Y} {g : Y → Z} (hf : IsQIMap K f)
    (hg : IsQIMap K' g) : IsQIMap (3 * K * K') (g ∘ f) := by
  have hK0 : 0 ≤ K := by linarith
  have hK0' : 0 ≤ K' := by linarith
  have hKK' : 1 ≤ K * K' := one_le_mul_of_one_le_of_one_le hK hK'
  refine ⟨fun a b ↦ ?_, fun a b ↦ ?_, fun z ↦ ?_⟩
  · have h1 := hg.upper (f a) (f b)
    have h2 := hf.upper a b
    have h3 := mul_le_mul_of_nonneg_left h2 hK0'
    have h4 := dist_nonneg (x := a) (y := b)
    have h5 : 0 ≤ K * K' * dist a b := by positivity
    have h6 : K' ≤ K * K' := by nlinarith
    simp only [Function.comp]
    linarith
  · have h1 := hf.lower a b
    have h2 := hg.lower (f a) (f b)
    have h3 := mul_le_mul_of_nonneg_left h2 hK0
    have h4 := dist_nonneg (x := g (f a)) (y := g (f b))
    have h5 : 0 ≤ K * K' * dist (g (f a)) (g (f b)) := by positivity
    have h6 : 0 ≤ K * K' ^ 2 * (K - 1) := mul_nonneg (by positivity) (by linarith)
    have h7 : 0 ≤ K ^ 2 * (K' ^ 2 - 1) := mul_nonneg (by positivity) (by nlinarith)
    have h8 : 0 ≤ K ^ 2 * K' ^ 2 := by positivity
    simp only [Function.comp]
    linarith
  · obtain ⟨y, hy⟩ := hg.dense z
    obtain ⟨x, hx⟩ := hf.dense y
    refine ⟨x, ?_⟩
    have h1 := dist_triangle (g (f x)) (g y) z
    have h2 := hg.upper (f x) y
    have h3 : K' * dist (f x) y ≤ K' * K := mul_le_mul_of_nonneg_left hx hK0'
    have h4 : K' ≤ K * K' := by nlinarith
    simp only [Function.comp]
    linarith

/-- A quasi-isometry of metric spaces has a quasi-inverse, at the constant `3K²`. -/
lemma IsQIMap.exists_symm {X Y : Type*} [MetricSpace X] [MetricSpace Y] {K : ℝ} (hK : 1 ≤ K)
    {f : X → Y} (hf : IsQIMap K f) : ∃ g : Y → X, IsQIMap (3 * K ^ 2) g := by
  choose g hg using hf.dense
  have hK0 : 0 ≤ K := by linarith
  have hK2 : K ≤ 3 * K ^ 2 := by nlinarith
  refine ⟨g, fun y y' ↦ ?_, fun y y' ↦ ?_, fun x ↦ ?_⟩
  · have h1 := hf.lower (g y) (g y')
    have h2 := dist_triangle (f (g y)) y (f (g y'))
    have h3 := dist_triangle y y' (f (g y'))
    have h4 := hg y
    have h5 := hg y'
    rw [dist_comm] at h5
    have h6 : K * dist (f (g y)) (f (g y')) ≤ K * (2 * K + dist y y') :=
      mul_le_mul_of_nonneg_left (by linarith) hK0
    have h7 : K * dist y y' ≤ 3 * K ^ 2 * dist y y' :=
      mul_le_mul_of_nonneg_right hK2 dist_nonneg
    linarith
  · have h1 := hf.upper (g y) (g y')
    have h2 := dist_triangle y (f (g y)) (f (g y'))
    have h3 := dist_triangle y (f (g y')) y'
    have h4 := hg y
    have h5 := hg y'
    rw [dist_comm] at h4
    have h6 := dist_nonneg (x := g y) (y := g y')
    have h7 : K * dist (g y) (g y') ≤ 3 * K ^ 2 * dist (g y) (g y') :=
      mul_le_mul_of_nonneg_right hK2 h6
    have h8 : 3 * K ≤ (3 * K ^ 2) ^ 2 := by nlinarith
    linarith
  · refine ⟨f x, ?_⟩
    have h1 := hf.lower (g (f x)) x
    have h2 := hg (f x)
    have h3 : K * dist (f (g (f x))) (f x) ≤ K * K := mul_le_mul_of_nonneg_left h2 hK0
    have h4 := sq_nonneg K
    nlinarith

/-- A quasi-isometry precomposed with a surjective isometry. -/
lemma IsQIMap.isometry_comp_left {K : ℝ} {X X' Y : Type*} [MetricSpace X] [MetricSpace X']
    [MetricSpace Y] {Φ : X → X'} (hΦ : Function.Surjective Φ)
    (hΦd : ∀ x y, dist (Φ x) (Φ y) = dist x y) {f : X' → Y} (hf : IsQIMap K f) :
    IsQIMap K (fun x => f (Φ x)) := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun y => ?_⟩
  · rw [← hΦd]; exact hf.upper _ _
  · rw [← hΦd]; exact hf.lower _ _
  · obtain ⟨x', hx'⟩ := hf.dense y
    obtain ⟨x, rfl⟩ := hΦ x'
    exact ⟨x, hx'⟩

/-- A distance-preserving bijection transports a quasi-isometry along its inverse. -/
lemma IsQIMap.comp_isometry_symm {K : ℝ} {X X' Y : Type*} [MetricSpace X] [MetricSpace X']
    [MetricSpace Y] {Φ : X → X'} (hΦ : Function.Bijective Φ)
    (hΦd : ∀ x y, dist (Φ x) (Φ y) = dist x y) {f : X → Y} (hf : IsQIMap K f) :
    IsQIMap K (fun x' => f ((Equiv.ofBijective Φ hΦ).symm x')) := by
  set e := Equiv.ofBijective Φ hΦ
  have hd : ∀ x' y', dist (e.symm x') (e.symm y') = dist x' y' := by
    intro x' y'
    rw [← hΦd]
    show dist (e (e.symm x')) (e (e.symm y')) = _
    rw [e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨fun a b => ?_, fun a b => ?_, fun y => ?_⟩
  · rw [← hd]; exact hf.upper _ _
  · rw [← hd]; exact hf.lower _ _
  · obtain ⟨a, ha⟩ := hf.dense y
    exact ⟨e a, by simpa [e] using ha⟩

/-! ### The deterministic core of `thm:hairy` -/

/-- **The deterministic core of `thm:hairy`**: if a portrait `π` matches the
shape labels of two samples, so that the shape at `w` of the first and the
shape at `autOf π w` of the second are `K`-comparable at every copy, then the
two assemblies admit an `8K²`-quasi-isometry.  The per-copy maps are glued by
`thm:glued-transfer` into a quasi-isometry onto the assembly of
`σ' ∘ autOf π`, and the relabelling identifies that assembly with the assembly
of `σ'`. -/
theorem qi_of_shape_matching {K : ℝ} (hK : 1 ≤ K) (π : Word → Bool ≃ Bool)
    {σ σ' : Word → Shape}
    (hcomp : ∀ w : Word, MarkedQI K (shapeSpace (σ w)) (shapeSpace (σ' (autOf π w)))) :
    ∃ f : Assembly σ → Assembly σ', IsQIMap (8 * K ^ 2) f := by
  choose φ hφ using hcomp
  obtain ⟨hup, hlow, hdense⟩ :=
    Assembly.glued_transfer (σ := σ) (σ' := fun w ↦ σ' (autOf π w)) hK hφ
  refine ⟨fun x ↦ Assembly.relabel π σ' (Assembly.glue φ x), ?_, ?_, ?_⟩
  · intro a b
    rw [Assembly.dist_relabel π σ']
    exact hup a b
  · intro a b
    rw [Assembly.dist_relabel π σ']
    exact hlow a b
  · intro y
    obtain ⟨z, rfl⟩ := Assembly.relabel_surjective π σ' y
    obtain ⟨x, hx⟩ := hdense z
    exact ⟨x, by rw [Assembly.dist_relabel π σ']; exact hx⟩

end ChainClasses
