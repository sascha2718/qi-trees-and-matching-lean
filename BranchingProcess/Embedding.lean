/-
The calculus of quasi-isometric embeddings behind `sec:embedding-hierarchy`: the
deterministic comparisons the embedding theorem and the strict hierarchy
`Fin ≺ Ray ≺ Supercritical` are assembled from.  Everything is stated over Mathlib's
`SimpleGraph` in its graph metric, as in `Geometry`.

* `IsQIEmbWith.comp`, `QIEmbeddable.trans`, `QIEmbeddable.trans_quasiIsometric`,
  `QuasiIsometric.trans_qiEmbeddable`: embeddings compose, with each other and with
  quasi-isometries, so `𝔹 ≼ X` is invariant under quasi-isometry of `X`.
* `isQIEmbWith_one_of_isometry`, `qiEmbeddable_of_isometry`: an isometric map is a
  `1`-embedding.
* `qiEmbeddable_of_bounded`, `IsBoundedGraph.of_qiEmbeddable`,
  `not_qiEmbeddable_of_not_bounded`: a bounded graph embeds anywhere, and nothing
  unbounded embeds into a bounded graph.  This is the comparison `Fin ≺ Ray`.
* `qiEmbeddable_rayGraph_of_isRay`: a ray is an isometric copy of `ℕ`, so the ray
  embeds into every graph carrying one.  With `not_qiEmbeddable_rayGraph` of
  `Geometry` this is the comparison `Ray ≺ Supercritical`.
-/
import BranchingProcess.Geometry

namespace BranchingProcess

open SimpleGraph

variable {V V' V'' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {G'' : SimpleGraph V''}

/-! ### Composition -/

/-- **Embeddings compose.** The constant of the composite is `(D + 1) (D' + 1)`. -/
theorem IsQIEmbWith.comp {D D' : ℕ} {f : V → V'} {g : V' → V''}
    (hf : IsQIEmbWith D G G' f) (hg : IsQIEmbWith D' G' G'' g) :
    IsQIEmbWith ((D + 1) * (D' + 1)) G G'' (g ∘ f) where
  upper x y := by
    have h1 := hg.upper (f x) (f y)
    have h2 := hf.upper x y
    have h3 : D' * G'.dist (f x) (f y) ≤ D' * (D * G.dist x y + D) :=
      Nat.mul_le_mul_left D' h2
    have h4 : D' * (D * G.dist x y + D) + D'
        ≤ (D + 1) * (D' + 1) * G.dist x y + (D + 1) * (D' + 1) := by
      nlinarith
    show G''.dist (g (f x)) (g (f y)) ≤ _
    omega
  lower x y := by
    have h1 := hf.lower x y
    have h2 := hg.lower (f x) (f y)
    have h3 : D * G'.dist (f x) (f y) ≤ D * (D' * G''.dist (g (f x)) (g (f y)) + D' * D') :=
      Nat.mul_le_mul_left D h2
    have h4 : D * (D' * G''.dist (g (f x)) (g (f y)) + D' * D') + D * D
        ≤ (D + 1) * (D' + 1) * G''.dist (g (f x)) (g (f y))
          + (D + 1) * (D' + 1) * ((D + 1) * (D' + 1)) := by
      nlinarith
    show G.dist x y ≤ (D + 1) * (D' + 1) * G''.dist (g (f x)) (g (f y)) + _
    omega

/-- Embeddability is transitive. -/
theorem QIEmbeddable.trans (h : QIEmbeddable G G') (h' : QIEmbeddable G' G'') :
    QIEmbeddable G G'' := by
  obtain ⟨D, f, hf⟩ := h
  obtain ⟨D', g, hg⟩ := h'
  exact ⟨_, g ∘ f, hf.comp hg⟩

/-- An embedding followed by a quasi-isometry is an embedding. -/
theorem QIEmbeddable.trans_quasiIsometric (h : QIEmbeddable G G')
    (h' : QuasiIsometric G' G'') : QIEmbeddable G G'' :=
  h.trans h'.qiEmbeddable

/-- A quasi-isometry followed by an embedding is an embedding. -/
theorem QuasiIsometric.trans_qiEmbeddable (h : QuasiIsometric G G')
    (h' : QIEmbeddable G' G'') : QIEmbeddable G G'' :=
  h.qiEmbeddable.trans h'

/-- Embeddability is reflexive. -/
theorem qiEmbeddable_refl (G : SimpleGraph V) : QIEmbeddable G G :=
  ⟨1, id, ⟨fun x y => by simp, fun x y => by simp⟩⟩

/-! ### Isometric maps -/

/-- An isometric map is a `1`-quasi-isometric embedding. -/
theorem isQIEmbWith_one_of_isometry {f : V → V'}
    (h : ∀ x y, G'.dist (f x) (f y) = G.dist x y) : IsQIEmbWith 1 G G' f where
  upper x y := by rw [h]; omega
  lower x y := by rw [h]; omega

/-- A graph with an isometric map into another embeds into it. -/
theorem qiEmbeddable_of_isometry {f : V → V'}
    (h : ∀ x y, G'.dist (f x) (f y) = G.dist x y) : QIEmbeddable G G' :=
  ⟨1, f, isQIEmbWith_one_of_isometry h⟩

/-! ### Bounded graphs -/

/-- **A bounded graph embeds into any nonempty graph**, by a constant map. -/
theorem qiEmbeddable_of_bounded [Nonempty V'] (hG : IsBoundedGraph G) : QIEmbeddable G G' := by
  obtain ⟨D, hD⟩ := hG
  refine ⟨D + 1, fun _ => Classical.arbitrary V', ⟨fun x y => ?_, fun x y => ?_⟩⟩
  · simp only [SimpleGraph.dist_self]
    exact Nat.zero_le _
  · have h1 : G.dist x y ≤ D := hD x y
    nlinarith

/-- The lower bound of an embedding carries boundedness back to the source. -/
theorem IsBoundedGraph.of_qiEmbeddable (h : QIEmbeddable G G') (hG' : IsBoundedGraph G') :
    IsBoundedGraph G := by
  obtain ⟨D, f, hf⟩ := h
  obtain ⟨D', hD'⟩ := hG'
  refine ⟨D * D' + D * D, fun x y => ?_⟩
  have h1 := hf.lower x y
  have h2 : D * G'.dist (f x) (f y) ≤ D * D' := Nat.mul_le_mul_left D (hD' _ _)
  omega

/-- **Nothing unbounded embeds into a bounded graph.** -/
theorem not_qiEmbeddable_of_not_bounded (hG : ¬ IsBoundedGraph G) (hG' : IsBoundedGraph G') :
    ¬ QIEmbeddable G G' :=
  fun h => hG (IsBoundedGraph.of_qiEmbeddable h hG')

/-! ### The ray -/

/-- **The ray embeds into every graph carrying a ray**: a ray is an isometric copy of
`ℕ`. -/
theorem qiEmbeddable_rayGraph_of_isRay {r : ℕ → V} (hr : IsRay G r) :
    QIEmbeddable rayGraph G :=
  qiEmbeddable_of_isometry fun m n => by rw [hr m n, rayGraph_dist]

/-- The ray is unbounded. -/
theorem not_isBoundedGraph_rayGraph : ¬ IsBoundedGraph rayGraph := by
  rintro ⟨D, hD⟩
  have h := hD 0 (D + 1)
  rw [rayGraph_dist] at h
  unfold Nat.dist at h
  omega

end BranchingProcess
