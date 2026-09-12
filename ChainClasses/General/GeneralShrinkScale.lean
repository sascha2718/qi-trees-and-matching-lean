import Mathlib.Tactic
import ChainClasses.General.GeneralContraction
import ChainClasses.General.GeneralShrink

/-!
`sec:general-relabel` of `matching_classes_general.tex`: the shrinking map of
`thm:shape-shrink` (`it:shape-shrink`) at general bounded support, the map the
cascade coupling behind `thm:relabel` and `thm:cross-relabel` runs on.

The shrinking composes the three moves certified separately: the contraction of
`GeneralContraction.lean` along the greedy cut at scale `s`, a `2s`-marked
quasi-isometry onto a rose tree of at most `n/s + 1` vertices whose offspring numbers are
at most `J·Js`; then the binarisation, the neck construction and the padding of
`GeneralShrink.lean`, an `18(d+1)`-marked quasi-isometry from a marked rose tree of
offspring at most `d` into the shapes charged at the support point `k`.  The
composition bound of `thm:shape-net` multiplies the constants, `3·2s·18(J²s+1) ≤
216 J² s²`, and the scale `s = ⌊√(D/216J²)⌋` brings the constant below `D`.

* `offspring_le_of_pos`, `GShape.ChargedG.degLe`: a charged shape realises with offspring at
  most `J`.
* `gShrink`: **the shrinking map**, `σ ↦ σ₀`, at scale `s` and support point `k`.
* `markedQI_gShrink`, `size_gShrink_le`, `chargedG_gShrink`: its three clauses, the
  `216 J² s²`-marked quasi-isometry, the size `|σ₀| ≤ 3k(n/s+1)`, and
  `σ₀ ∈ supp μ` as `ChargedG θ k`.
* `gShrinkScale`, `gShrinkScale_le`: the scale `⌊√(D/216J²)⌋` and the bound
  `216 J² s² ≤ D` it gives.
* `markedQI_gShrink_of_le`: **`thm:shape-shrink` (`it:shape-shrink`) at general
  arity**, the three clauses at a scale whose constant is at most `D`.
-/

namespace ChainClasses

open RTree BranchingProcess

/-! ### Charged shapes realise within the offspring bound -/

/-- A positive mass lies within the support bound. -/
lemma offspring_le_of_pos {J : ℕ} (θ : Offspring J) {j : ℕ} (h : 0 < θ j) : j ≤ J := by
  by_contra hlt
  have := θ.vanishing j (by omega)
  rw [this] at h
  exact lt_irrefl _ h

/-- A charged shape realises with offspring numbers at most `J`: every neck vertex
carries `1 + |β|` children with `θ(1 + |β|) > 0`, the exit carries `|β_m|` children with
`θ(κ + |β_m|) > 0` and `κ ≥ 2`, and every bush is charged. -/
lemma GShape.ChargedG.degLe {J : ℕ} {θ : Offspring J} {κ : ℕ} (hκ : 2 ≤ κ) {σ : GShape}
    (h : GShape.ChargedG θ κ σ) : DegLe J σ.realise := by
  obtain ⟨hneck, hbq⟩ := h
  refine GShape.realise_degLe σ (fun i => ?_) (fun i t ht => ?_)
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have hmem : σ.dec j.castSucc ∈ σ.neckList := by
        rw [GShape.neckList]
        exact List.mem_ofFn.mpr ⟨j, rfl⟩
      have := offspring_le_of_pos θ (hneck _ hmem).1
      omega
    · have := offspring_le_of_pos θ hbq.1
      show (σ.bouquet).length + 1 ≤ J
      omega
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have hmem : σ.dec j.castSucc ∈ σ.neckList := by
        rw [GShape.neckList]
        exact List.mem_ofFn.mpr ⟨j, rfl⟩
      exact ((hneck _ hmem).2 t ht).degLe
    · exact (hbq.2 t ht).degLe

/-! ### The shrinking map -/

/-- **The shrinking map at general arity**: contract the realisation along the greedy cut
at scale `s`, binarise, read the marked tree as a shape, and pad into the support at the
point `k`. -/
def gShrink (k s : ℕ) (σ : GShape) : GShape :=
  gShrinkOf k (gContractTree s σ.realise) (gContractMark s σ.realise σ.exitAddr)

/-- **`thm:shape-shrink` (`it:shape-shrink`), the quasi-isometry at general
arity**: the shrinking is `216 J² s²`-marked, the composition `3·2s·18(J·Js + 1)` of the
contraction with the moves after it. -/
theorem markedQI_gShrink {J s : ℕ} (hJ : 1 ≤ J) (hs : 1 ≤ s) {σ : GShape}
    (hσ : DegLe J σ.realise) (k : ℕ) :
    MarkedQI (216 * (J : ℝ) ^ 2 * (s : ℝ) ^ 2) (gShapeSpace σ) (gShapeSpace (gShrink k s σ)) := by
  have he := σ.exitAddr_mem_addrList
  have hd : 1 ≤ J * (J * s) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have step1 : MarkedQI (2 * s : ℝ) (gShapeSpace σ)
      (gSpace (gContractTree s σ.realise) (gContractMark s σ.realise σ.exitAddr)) :=
    markedQI_gContractTree hs he
  have step2 := markedQI_gShrinkOf hd (degLe_gContractTree_mul hs hσ) (gContractMark_mem he) k
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hA : (1 : ℝ) ≤ 2 * (s : ℝ) := by linarith
  have hd1 : (1 : ℝ) ≤ ((J * (J * s) : ℕ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ ((J * (J * s) : ℕ) : ℝ) := by positivity
    linarith
  have hB : (1 : ℝ) ≤ 18 * (((J * (J * s) : ℕ) : ℝ) + 1) := by linarith
  have step3 := markedQI_comp hA hB step1 step2
  refine step3.mono (by positivity) ?_
  push_cast
  have hJs : (1 : ℝ) ≤ (J : ℝ) ^ 2 * s := by nlinarith
  nlinarith

/-- **`thm:shape-shrink` (`it:shape-shrink`), the size at general arity**: the
shrunk shape has at most `3k(n/s + 1)` vertices, the contraction having at most
`n/s + 1`, the neck construction adding two, and the padding multiplying by `k`. -/
theorem size_gShrink_le {k s : ℕ} (hk : 1 ≤ k) (hs : 1 ≤ s) (σ : GShape) :
    (gShrink k s σ).size ≤ 3 * k * (σ.size / s + 1) := by
  have he := σ.exitAddr_mem_addrList
  have h1 := size_gShrinkOf_le hk (gContractMark_mem (s := s) he)
  have h2 := size_gContractTree_le_div hs σ.realise
  have hsz : σ.realise.size = σ.size := rfl
  rw [hsz] at h2
  obtain ⟨q, hq⟩ : ∃ q, σ.size / s = q := ⟨_, rfl⟩
  rw [hq] at h2 ⊢
  have h3 : (gContractTree s σ.realise).size + 2 ≤ 3 * (q + 1) := by omega
  refine h1.trans ?_
  calc k * ((gContractTree s σ.realise).size + 2) ≤ k * (3 * (q + 1)) :=
        Nat.mul_le_mul_left k h3
    _ = 3 * k * (q + 1) := by ring

/-- **`thm:shape-shrink` (`it:shape-shrink`), the support at general arity**:
the shrunk shape is charged at the support point `k`, so it carries positive mass under
every conditional law and under the mixture `μ` of `thm:conditional-explicit`. -/
theorem chargedG_gShrink {J : ℕ} {θ : Offspring J} {k : ℕ} (h0 : 0 < θ 0) (hk : 0 < θ k)
    (hk2 : 2 ≤ k) (s : ℕ) (σ : GShape) : GShape.ChargedG θ k (gShrink k s σ) :=
  chargedG_gShrinkOf h0 hk hk2 (gContractMark_mem (s := s) σ.exitAddr_mem_addrList)

/-! ### The scale -/

/-- The scale of the shrinking at a target constant `D`: `s = ⌊√(D/216J²)⌋`. -/
def gShrinkScale (J D : ℕ) : ℕ := Nat.sqrt (D / (216 * J ^ 2))

/-- **The choice of scale**: at `s = ⌊√(D/216J²)⌋` the constant of the composition is at
most `D`. -/
lemma gShrinkScale_le (J D : ℕ) :
    216 * (J : ℝ) ^ 2 * (gShrinkScale J D : ℝ) ^ 2 ≤ (D : ℝ) := by
  have h : 216 * J ^ 2 * Nat.sqrt (D / (216 * J ^ 2)) ^ 2 ≤ D := by
    have h1 : Nat.sqrt (D / (216 * J ^ 2)) ^ 2 ≤ D / (216 * J ^ 2) := Nat.sqrt_le' _
    have h2 : 216 * J ^ 2 * (D / (216 * J ^ 2)) ≤ D := Nat.mul_div_le D _
    calc 216 * J ^ 2 * Nat.sqrt (D / (216 * J ^ 2)) ^ 2 ≤ 216 * J ^ 2 * (D / (216 * J ^ 2)) :=
          Nat.mul_le_mul_left _ h1
      _ ≤ D := h2
  rw [gShrinkScale]
  exact_mod_cast h

/-- **`thm:shape-shrink` (`it:shape-shrink`) at general arity**: for every
`D ≥ 216 J² s²` with `s ≥ 1`, every shape `σ` with offspring at most `J` admits a shape
`σ₀` charged at the support point `k`, with `|σ₀| ≤ 3k(|σ|/s + 1)` and a `D`-marked
quasi-isometry `σ → σ₀`; the shape is `gShrink k s σ`, a function of `σ`. -/
theorem markedQI_gShrink_of_le {J : ℕ} {θ : Offspring J} {k s : ℕ} {D : ℝ} (hJ : 1 ≤ J)
    (hs : 1 ≤ s) (hD : 216 * (J : ℝ) ^ 2 * (s : ℝ) ^ 2 ≤ D) (h0 : 0 < θ 0) (hk : 0 < θ k)
    (hk2 : 2 ≤ k) {σ : GShape} (hσ : DegLe J σ.realise) :
    GShape.ChargedG θ k (gShrink k s σ) ∧ (gShrink k s σ).size ≤ 3 * k * (σ.size / s + 1)
      ∧ MarkedQI D (gShapeSpace σ) (gShapeSpace (gShrink k s σ)) :=
  ⟨chargedG_gShrink h0 hk hk2 s σ, size_gShrink_le (by omega) hs σ,
    (markedQI_gShrink hJ hs hσ k).mono (by positivity) hD⟩

end ChainClasses
