import ChainClasses.Regime.MatchedPresentation

/-!
`thm:chain-cross` of `trichotomy.tex`, the law level: the matched presentations
of two chain-regime laws with equal branching semigroups sit inside the
hypotheses of `thm:composite-matching`.

The engine takes two arity laws with a common core, finitely many exceptional
arities above the core on at most one side, a composite pair in the core for
each, no iterated charts, and floors bounded away from zero.  Certified here,
over the presented laws of `MatchedPresentation`:

* `exists_core_pair`: **the composite pairs**.  Every window total splits as a
  sum of two core totals, through the cofiniteness threshold of
  `thm:semigroup-threshold`; the pair of arities `(1 + s, 1 + (λ - s))`
  satisfies `a + b - 1 = 1 + λ`.
* `exists_chart`: **the chart**: a function assigning to every exceptional
  window arity its composite pair, with core components, defined nowhere else;
  `hpair`-style clauses hold because core arities are never excepted.
* `matched_core_subset`, `matched_core_charged`: **the common core**.  Both
  presented laws charge every arity of `1 + (Λ ∩ [s₀, L + min M])`, with mass
  at least `c δ`, uniformly in the failure probabilities.
* `pair_floor`: **the floors**: a composite pair carries tilt floor at least
  `(1/2) (cδ)²`, uniformly in `D`.
* `chainCross_qi_scale`: **`thm:chain-cross` (`it:chain-cross-qi`)**,
  the comparability constant `9 γ₁² D⁶` from the flattening at `γ₁ D²` and the
  class comparison at `D²`, through the composition rule `markedQI_comp`.

The identification of the presented labellings with the engine's process on
one probability space is `ChainEngineBridge`.
-/

namespace ChainClasses

namespace Matched

open Finset

/-! ### The composite pairs of the window -/

/-- **The window totals split over the core.**  Past the cofiniteness
threshold `N₀` of the semigroup in the lattice of its gcd `g`, every window
total `λ ∈ Λ ∩ (L + m, L + M]` is a sum of two core totals, one of them the
first multiple of `g` above `N₀ + M`. -/
theorem exists_core_pair {Λ : AddSubmonoid ℕ} {N₀ g : ℕ} (hg : 0 < g)
    (hN₀ : ∀ n, N₀ ≤ n → g ∣ n → n ∈ Λ) {m M L lam : ℕ} (_hmM : m ≤ M)
    (hlamg : g ∣ lam)
    (hL : 2 * N₀ + 2 * M + 2 * g ≤ L) (hlo : L + m < lam) (hhi : lam ≤ L + M) :
    ∃ a b : ℕ, a ∈ Λ ∧ b ∈ Λ ∧ 0 < a ∧ 0 < b ∧ a ≤ L + m ∧ b ≤ L + m
      ∧ a + b = lam := by
  have hqr := Nat.div_add_mod (N₀ + M) g
  have hr := Nat.mod_lt (N₀ + M) hg
  have hexp : g * ((N₀ + M) / g + 1) = g * ((N₀ + M) / g) + g := by ring
  have hadvd : g ∣ g * ((N₀ + M) / g + 1) := Dvd.intro _ rfl
  have hbdvd : g ∣ lam - g * ((N₀ + M) / g + 1) := Nat.dvd_sub hlamg hadvd
  refine ⟨g * ((N₀ + M) / g + 1), lam - g * ((N₀ + M) / g + 1),
    hN₀ _ (by omega) hadvd, hN₀ _ (by omega) hbdvd,
    by omega, by omega, by omega, by omega, by omega⟩

/-- **The chart**: every exceptional window arity `1 + λ`,
`λ ∈ Λ ∩ (L + m, L + M]`, carries a composite pair of core arities with
`a + b - 1 = 1 + λ`; the chart is `none` everywhere else, so no chart is
iterated and no core arity is excepted. -/
theorem exists_chart {Λ : AddSubmonoid ℕ} {N₀ g : ℕ} (hg : 0 < g)
    (hN₀ : ∀ n, N₀ ≤ n → g ∣ n → n ∈ Λ) (hΛg : ∀ n ∈ Λ, g ∣ n) {m M L : ℕ}
    (hL : 2 * N₀ + 2 * M + 2 * g ≤ L) :
    ∃ exc : ℕ → Option (ℕ × ℕ),
      (∀ j, j ≤ 1 + L + m → exc j = none) ∧
      (∀ j, exc j ≠ none → ∃ lam ∈ Λ, j = 1 + lam ∧ L + m < lam ∧ lam ≤ L + M) ∧
      (∀ z p, exc z = some p →
        (∃ a ∈ Λ, 0 < a ∧ a ≤ L + m ∧ p.1 = 1 + a) ∧
        (∃ b ∈ Λ, 0 < b ∧ b ≤ L + m ∧ p.2 = 1 + b) ∧
        p.1 + p.2 - 1 = z) ∧
      (∀ lam ∈ Λ, L + m < lam → lam ≤ L + M → exc (1 + lam) ≠ none) := by
  classical
  have hqr := Nat.div_add_mod (N₀ + M) g
  have hr := Nat.mod_lt (N₀ + M) hg
  have hexp : g * ((N₀ + M) / g + 1) = g * ((N₀ + M) / g) + g := by ring
  have hadvd : g ∣ g * ((N₀ + M) / g + 1) := Dvd.intro _ rfl
  refine ⟨fun j ↦ if h : 1 + L + m < j ∧ j ≤ 1 + L + M ∧ j - 1 ∈ Λ then
      some (1 + g * ((N₀ + M) / g + 1), 1 + (j - 1 - g * ((N₀ + M) / g + 1)))
    else none, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact dif_neg fun hcon ↦ absurd hcon.1 (by omega)
  · intro j hj
    by_cases h : 1 + L + m < j ∧ j ≤ 1 + L + M ∧ j - 1 ∈ Λ
    · exact ⟨j - 1, h.2.2, by omega, by omega, by omega⟩
    · exact absurd (dif_neg h) hj
  · intro z p hp
    by_cases h : 1 + L + m < z ∧ z ≤ 1 + L + M ∧ z - 1 ∈ Λ
    · have hp' : (if h' : 1 + L + m < z ∧ z ≤ 1 + L + M ∧ z - 1 ∈ Λ then
          some (1 + g * ((N₀ + M) / g + 1), 1 + (z - 1 - g * ((N₀ + M) / g + 1)))
          else none)
          = some p := hp
      rw [dif_pos h] at hp'
      obtain ⟨h1, h2, h3⟩ := h
      have hbdvd : g ∣ z - 1 - g * ((N₀ + M) / g + 1) :=
        Nat.dvd_sub (hΛg _ h3) hadvd
      have hpair := Option.some.inj hp'
      have hpa : p.1 = 1 + g * ((N₀ + M) / g + 1) := by rw [← hpair]
      have hpb : p.2 = 1 + (z - 1 - g * ((N₀ + M) / g + 1)) := by rw [← hpair]
      refine ⟨⟨g * ((N₀ + M) / g + 1), hN₀ _ (by omega) hadvd, by omega, by omega, hpa⟩,
        ⟨z - 1 - g * ((N₀ + M) / g + 1), hN₀ _ (by omega) hbdvd, by omega, by omega,
          hpb⟩, by omega⟩
    · have hp' : (if h' : 1 + L + m < z ∧ z ≤ 1 + L + M ∧ z - 1 ∈ Λ then
          some (1 + g * ((N₀ + M) / g + 1), 1 + (z - 1 - g * ((N₀ + M) / g + 1)))
          else none)
          = some p := hp
      rw [dif_neg h] at hp'
      simp at hp'
  · intro lam hmem hlo hhi
    have h : 1 + L + m < 1 + lam ∧ 1 + lam ≤ 1 + L + M ∧ 1 + lam - 1 ∈ Λ :=
      ⟨by omega, by omega, by simpa using hmem⟩
    show (if h' : _ then _ else none) ≠ none
    rw [dif_pos h]
    exact Option.some_ne_none _

/-! ### The common core and the floors -/

variable {A B : Finset ℕ} {P P' : ℕ → ℝ} {L : ℕ} {φ φ' δ : ℝ}

/-- **The common core is charged by both presented laws**: every total of
`Λ ∩ (0, L + min(MA, MB)]` carries mass at least `c δ` on either side, the
floor `c` independent of the failure probabilities and of `δ`. -/
theorem matched_core_charged {MA MB : ℕ} (hMAmem : MA ∈ A) (hMBmem : MB ∈ B)
    (hA0 : ∀ a ∈ A, 0 < a) (hB0 : ∀ b ∈ B, 0 < b) (hMAL : MA ≤ L) (hMBL : MB ≤ L)
    (hP : ∀ a ∈ A, 0 ≤ P a) (hP' : ∀ b ∈ B, 0 ≤ P' b)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hPp : ∀ a ∈ A, p ≤ P a) (hP'p : ∀ b ∈ B, p ≤ P' b)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hφ'0 : 0 ≤ φ') (hφ'1 : φ' ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hsem : AddSubmonoid.closure (A : Set ℕ) = AddSubmonoid.closure (B : Set ℕ))
    (hwinA : ∀ s' : ℕ, s' ∈ AddSubmonoid.closure (A : Set ℕ) → L < s' → s' ≤ L + MA →
      s' - MA ∈ AddSubmonoid.closure (A : Set ℕ))
    (hwinB : ∀ s' : ℕ, s' ∈ AddSubmonoid.closure (B : Set ℕ) → L < s' → s' ≤ L + MB →
      s' - MB ∈ AddSubmonoid.closure (B : Set ℕ))
    {F F' : ℕ} (hF : L + MA + 2 ≤ F) (hF' : L + MB + 2 ≤ F') {s : ℕ}
    (h1 : s ∈ AddSubmonoid.closure (A : Set ℕ)) (h2 : 0 < s)
    (h3 : s ≤ L + min MA MB) :
    δ * ((1 / 2) * p * (p * (1 - φ) / 2) ^ (L + MA))
        ≤ matchedShift A B P P' L φ δ F s
      ∧ δ * ((1 / 2) * p * (p * (1 - φ') / 2) ^ (L + MB))
        ≤ matchedShift B A P' P L φ' δ F' s := by
  constructor
  · exact matchedShift_floor hMAmem hA0 hMAL hP hP' hp0 hp1 hPp hφ0 hφ1 hδ0 hδ1
      hwinA hF h1 h2 (by omega)
  · exact matchedShift_floor hMBmem hB0 hMBL hP' hP hp0 hp1 hP'p hφ'0 hφ'1 hδ0 hδ1
      hwinB hF' (hsem ▸ h1) h2 (by omega)

/-- **The floors of a composite pair**: two core masses at least `cδ` give the
tilt floor `(1/2)(cδ)²` of `eq:composite-floor`, uniformly in the scale. -/
theorem pair_floor {c ma mb : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hma : c * δ ≤ ma) (hmb : c * δ ≤ mb) :
    (1 / 2) * (c * δ) ^ 2 ≤ (1 / 2) * (ma * mb) := by
  have h1 : (0 : ℝ) ≤ c * δ := mul_nonneg hc hδ
  nlinarith

/-! ### The comparability constant -/

/-- **`thm:chain-cross` (`it:chain-cross-qi`)**: composing the
flattening at `γ₁ D²`, the class comparison at `D²`, and the inverse
flattening through the composition rule at `3 K K'` gives `9 γ₁² D⁶`. -/
theorem chainCross_qi_scale {γ₁ D : ℝ} (hγ : 1 ≤ γ₁) (hD : 1 ≤ D)
    {X Y Z W : MarkedSpace}
    (hflat : MarkedQI (γ₁ * D ^ 2) X Y) (hclass : MarkedQI (D ^ 2) Y Z)
    (hflat' : MarkedQI (γ₁ * D ^ 2) Z W) :
    MarkedQI (9 * γ₁ ^ 2 * D ^ 6) X W := by
  have hD2 : (1 : ℝ) ≤ D ^ 2 := one_le_pow₀ hD
  have hK1 : (1 : ℝ) ≤ γ₁ * D ^ 2 := by nlinarith
  have h12 : MarkedQI (3 * (γ₁ * D ^ 2) * D ^ 2) X Z := markedQI_comp hK1 hD2 hflat hclass
  have hK12 : (1 : ℝ) ≤ 3 * (γ₁ * D ^ 2) * D ^ 2 := by nlinarith
  have h123 : MarkedQI (3 * (3 * (γ₁ * D ^ 2) * D ^ 2) * (γ₁ * D ^ 2)) X W :=
    markedQI_comp hK12 hK1 h12 hflat'
  have heq : 3 * (3 * (γ₁ * D ^ 2) * D ^ 2) * (γ₁ * D ^ 2) = 9 * γ₁ ^ 2 * D ^ 6 := by
    ring
  rwa [heq] at h123

end Matched

end ChainClasses
