/-
The averaged one-step bound, the invariance schema, and the failure bound
of the per-state Markov pipeline, in the cleaner Lean-shaped form:

    Φ_{n+1}(s,t) ≤ η(s,t) + Γ + 2α · η(s,t) · Γ

for every uniform ceiling `Γ` on the frozen-pattern square potentials at
height `n`; consequently any `B` with `ε + Γ_B + 2α ε Γ_B ≤ B` that the
four-law input keeps closed dominates the whole family, and the failure
probability of root-mixture samples at height `n` is at most `η_ι + B`.

The four-law directed contraction enters only through the hypothesis
`hFour`/`hΓ`; it is certified in `FourLaw/Assembly.lean`.
-/
import GraphMarkovMatching.Archive.Step

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {S : Type u}

variable (α : ℝ) (P : S → PMF (S × S)) (R₀ : S → S → Prop)

/-- The root-pattern weight `φ_α(e_σ)` of a pattern against the kernel at `t`. -/
noncomputable def rootA (t : S) (σp : S × S) : ℝ≥0∞ :=
  phiE α (q (P t) (SquareRel R₀) σp)

/-- The tilted weights are a probability vector whenever the compatible mass
is positive. -/
lemma tiltW_tsum_eq_one {t : S} {σp : S × S}
    (hD : rE (P t) (SquareRel R₀) σp ≠ 0) :
    ∑' τ, tiltW P R₀ t σp τ = 1 := by
  have hD_top : rE (P t) (SquareRel R₀) σp ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top rE_le_one
  calc ∑' τ, tiltW P R₀ t σp τ
      = ∑' τ, (if SquareRel R₀ σp τ then (P t) τ else 0)
          * (rE (P t) (SquareRel R₀) σp)⁻¹ :=
        tsum_congr fun τ => rfl
    _ = (∑' τ, if SquareRel R₀ σp τ then (P t) τ else 0)
          * (rE (P t) (SquareRel R₀) σp)⁻¹ :=
        ENNReal.tsum_mul_right
    _ = rE (P t) (SquareRel R₀) σp * (rE (P t) (SquareRel R₀) σp)⁻¹ := by
        rw [show (∑' τ, if SquareRel R₀ σp τ then (P t) τ else 0)
          = rE (P t) (SquareRel R₀) σp from rfl]
    _ = 1 := ENNReal.mul_inv_cancel hD hD_top

/-- The conditional part averages below any uniform frozen-pattern ceiling. -/
lemma tsum_Jmix_le {t : S} (n : ℕ) (σ : S × S) (Γ : ℝ≥0∞)
    (hΓ : ∀ τ : S × S, SquareRel R₀ σ τ →
      PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n)) (prodPMF (muM P τ.1 n) (muM P τ.2 n))
        (SquareRel (fullSim R₀ n)) ≤ Γ)
    (hD : rE (P t) (SquareRel R₀) σ ≠ 0) :
    ∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp ≤ Γ := by
  have hswap : (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp)
      = ∑' τ, tiltW P R₀ t σ τ
          * PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n))
              (prodPMF (muM P τ.1 n) (muM P τ.2 n)) (SquareRel (fullSim R₀ n)) := by
    calc (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp)
        = ∑' xp, ∑' τ, tiltW P R₀ t σ τ
            * (prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
              * phiE α (q (prodPMF (muM P τ.1 n) (muM P τ.2 n))
                  (SquareRel (fullSim R₀ n)) xp)) := by
          refine tsum_congr fun xp => ?_
          rw [Jmix, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun τ => by ring
      _ = ∑' τ, ∑' xp, tiltW P R₀ t σ τ
            * (prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
              * phiE α (q (prodPMF (muM P τ.1 n) (muM P τ.2 n))
                  (SquareRel (fullSim R₀ n)) xp)) := ENNReal.tsum_comm
      _ = ∑' τ, tiltW P R₀ t σ τ
            * PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n))
                (prodPMF (muM P τ.1 n) (muM P τ.2 n)) (SquareRel (fullSim R₀ n)) := by
          refine tsum_congr fun τ => ?_
          rw [show PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n))
              (prodPMF (muM P τ.1 n) (muM P τ.2 n)) (SquareRel (fullSim R₀ n))
            = ∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
              * phiE α (q (prodPMF (muM P τ.1 n) (muM P τ.2 n))
                  (SquareRel (fullSim R₀ n)) xp) from rfl,
            ← ENNReal.tsum_mul_left]
  rw [hswap]
  calc (∑' τ, tiltW P R₀ t σ τ
        * PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n))
            (prodPMF (muM P τ.1 n) (muM P τ.2 n)) (SquareRel (fullSim R₀ n)))
      ≤ ∑' τ, tiltW P R₀ t σ τ * Γ := by
        refine ENNReal.tsum_le_tsum fun τ => ?_
        by_cases h : SquareRel R₀ σ τ
        · exact mul_le_mul_right (hΓ τ h) _
        · have h0 : tiltW P R₀ t σ τ = 0 := by
            have e : tiltW P R₀ t σ τ
                = (if SquareRel R₀ σ τ then (P t) τ else 0)
                  * (rE (P t) (SquareRel R₀) σ)⁻¹ := rfl
            rw [e, if_neg h, zero_mul]
          rw [h0, zero_mul, zero_mul]
    _ = Γ := by rw [ENNReal.tsum_mul_right, tiltW_tsum_eq_one P R₀ hD, one_mul]

/-- The per-pattern averaged bound. -/
lemma tsum_pattern_le {t : S} {α : ℝ} (_hα : 1 ≤ α) (n : ℕ) (σ : S × S) (Γ : ℝ≥0∞)
    (hΓ : ∀ τ : S × S, SquareRel R₀ σ τ →
      PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n)) (prodPMF (muM P τ.1 n) (muM P τ.2 n))
        (SquareRel (fullSim R₀ n)) ≤ Γ) :
    (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
      * (rootA α P R₀ t σ + Jmix α P R₀ t σ n xp
          + ENNReal.ofReal (2 * α) * (rootA α P R₀ t σ * Jmix α P R₀ t σ n xp)))
      ≤ rootA α P R₀ t σ + Γ
          + ENNReal.ofReal (2 * α) * (rootA α P R₀ t σ * Γ) := by
  by_cases hD : rE (P t) (SquareRel R₀) σ = 0
  · -- fully mismatched pattern: the ceiling is `⊤`
    have hE1 : qE (P t) (SquareRel R₀) σ = 1 := by
      have h := rE_add_qE (P t) (SquareRel R₀) σ
      rw [hD, zero_add] at h
      exact h
    have htop : rootA α P R₀ t σ = ⊤ := by
      rw [rootA, q, hE1, ENNReal.toReal_one, phiE_one]
    rw [htop]
    simp
  · -- expand and bound the conditional part
    set A : ℝ≥0∞ := rootA α P R₀ t σ with hA
    set EJ : ℝ≥0∞ :=
      ∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp with hEJ
    have hexp : (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
        * (A + Jmix α P R₀ t σ n xp
            + ENNReal.ofReal (2 * α) * (A * Jmix α P R₀ t σ n xp)))
        = A + EJ + ENNReal.ofReal (2 * α) * A * EJ := by
      calc (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
          * (A + Jmix α P R₀ t σ n xp
              + ENNReal.ofReal (2 * α) * (A * Jmix α P R₀ t σ n xp)))
          = ∑' xp, (prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * A
              + prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp
              + (ENNReal.ofReal (2 * α) * A)
                  * (prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp)) :=
            tsum_congr fun xp => by ring
        _ = (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * A)
            + (∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp)
            + ∑' xp, (ENNReal.ofReal (2 * α) * A)
                * (prodPMF (muM P σ.1 n) (muM P σ.2 n) xp * Jmix α P R₀ t σ n xp) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_add]
        _ = A + EJ + ENNReal.ofReal (2 * α) * A * EJ := by
            rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
              ENNReal.tsum_mul_left, ← hEJ, mul_assoc]
    rw [hexp]
    have hEJΓ : EJ ≤ Γ := tsum_Jmix_le α P R₀ n σ Γ hΓ hD
    calc A + EJ + ENNReal.ofReal (2 * α) * A * EJ
        ≤ A + Γ + ENNReal.ofReal (2 * α) * A * Γ := by gcongr
      _ = A + Γ + ENNReal.ofReal (2 * α) * (A * Γ) := by rw [mul_assoc]

/-- **The one-step bound**: for a compatible pair `(s,t)` and any uniform
ceiling `Γ` on the frozen-pattern square potentials at height `n`,

    Φ_{n+1}(s,t) ≤ η(s,t) + Γ + 2α · η(s,t) · Γ. -/
theorem PhiM_succ_le {α : ℝ} (hα : 1 ≤ α) {s t : S} (hst : R₀ s t) (n : ℕ)
    (Γ : ℝ≥0∞)
    (hΓ : ∀ σ τ : S × S, SquareRel R₀ σ τ →
      PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n)) (prodPMF (muM P τ.1 n) (muM P τ.2 n))
        (SquareRel (fullSim R₀ n)) ≤ Γ) :
    PhiM α P R₀ s t (n + 1)
      ≤ etaD α P R₀ s t + Γ
        + ENNReal.ofReal (2 * α) * (etaD α P R₀ s t * Γ) := by
  -- the exact root-factor elimination
  have hstep1 : PhiM α P R₀ s t (n + 1)
      = ∑' xp, pairMix P s n xp
          * phiE α (q (pairMix P t n) (SquareRel (fullSim R₀ n)) xp) := by
    rw [PhiM, muM_succ, PhiD_map_left]
    refine tsum_congr fun xp => ?_
    congr 1
    have hq : q (muM P t (n + 1)) (fullSim R₀ (n + 1)) (branch s xp)
        = q (pairMix P t n) (SquareRel (fullSim R₀ n)) xp :=
      congrArg ENNReal.toReal (qE_succ_branch P R₀ hst n xp)
    rw [hq]
  -- the pointwise split-and-Jensen bound
  have hstep2 : PhiM α P R₀ s t (n + 1)
      ≤ ∑' xp, pairMix P s n xp
          * (rootA α P R₀ t (rootPat n xp) + Jmix α P R₀ t (rootPat n xp) n xp
              + ENNReal.ofReal (2 * α)
                * (rootA α P R₀ t (rootPat n xp) * Jmix α P R₀ t (rootPat n xp) n xp)) := by
    rw [hstep1]
    exact ENNReal.tsum_le_tsum fun xp =>
      mul_le_mul_right (phiE_pairMix_le P R₀ hα t n xp) _
  -- expand the kernel mixture and freeze the pattern on supports
  have hstep3 : (∑' xp, pairMix P s n xp
      * (rootA α P R₀ t (rootPat n xp) + Jmix α P R₀ t (rootPat n xp) n xp
          + ENNReal.ofReal (2 * α)
            * (rootA α P R₀ t (rootPat n xp) * Jmix α P R₀ t (rootPat n xp) n xp)))
      = ∑' σ, (P s) σ * ∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
          * (rootA α P R₀ t σ + Jmix α P R₀ t σ n xp
              + ENNReal.ofReal (2 * α)
                * (rootA α P R₀ t σ * Jmix α P R₀ t σ n xp)) := by
    rw [show pairMix P s n
        = (P s).bind fun στ => prodPMF (muM P στ.1 n) (muM P στ.2 n) from rfl,
      tsum_bind_mul]
    refine tsum_congr fun σ => ?_
    congr 1
    refine tsum_congr fun xp => ?_
    by_cases hz : prodPMF (muM P σ.1 n) (muM P σ.2 n) xp = 0
    · rw [hz, zero_mul, zero_mul]
    · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp (by rwa [prodPMF_apply] at hz)
      have hpat : rootPat n xp = σ := by
        show (rootLab n xp.1, rootLab n xp.2) = σ
        rw [rootLab_of_ne_zero P n σ.1 xp.1 h1, rootLab_of_ne_zero P n σ.2 xp.2 h2]
      rw [hpat]
  -- average the per-pattern bounds
  calc PhiM α P R₀ s t (n + 1)
      ≤ ∑' σ, (P s) σ * ∑' xp, prodPMF (muM P σ.1 n) (muM P σ.2 n) xp
          * (rootA α P R₀ t σ + Jmix α P R₀ t σ n xp
              + ENNReal.ofReal (2 * α)
                * (rootA α P R₀ t σ * Jmix α P R₀ t σ n xp)) := by
        rw [← hstep3]; exact hstep2
    _ ≤ ∑' σ, (P s) σ * (rootA α P R₀ t σ + Γ
          + ENNReal.ofReal (2 * α) * (rootA α P R₀ t σ * Γ)) := by
        refine ENNReal.tsum_le_tsum fun σ => ?_
        exact mul_le_mul_right (tsum_pattern_le P R₀ hα n σ Γ (fun τ => hΓ σ τ)) _
    _ = etaD α P R₀ s t + Γ
          + ENNReal.ofReal (2 * α) * (etaD α P R₀ s t * Γ) := by
        calc (∑' σ, (P s) σ * (rootA α P R₀ t σ + Γ
              + ENNReal.ofReal (2 * α) * (rootA α P R₀ t σ * Γ)))
            = ∑' σ, ((P s) σ * rootA α P R₀ t σ + (P s) σ * Γ
                + (ENNReal.ofReal (2 * α))
                    * (((P s) σ * rootA α P R₀ t σ) * Γ)) :=
              tsum_congr fun σ => by ring
          _ = (∑' σ, (P s) σ * rootA α P R₀ t σ) + (∑' σ, (P s) σ * Γ)
                + ∑' σ, (ENNReal.ofReal (2 * α))
                    * (((P s) σ * rootA α P R₀ t σ) * Γ) := by
              rw [ENNReal.tsum_add, ENNReal.tsum_add]
          _ = etaD α P R₀ s t + Γ
                + ENNReal.ofReal (2 * α) * (etaD α P R₀ s t * Γ) := by
              have he : (∑' σ, (P s) σ * rootA α P R₀ t σ) = etaD α P R₀ s t := rfl
              rw [he, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
                ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, he]

/-- **The invariance schema**: a ceiling `B` dominates the whole directed
family at every height, provided the kernel budget is at most `ε`, the
four-law input converts a `B`-bounded family at height `n` into a uniform
frozen-pattern ceiling `Γ`, and one closure inequality holds. The four-law
directed contraction enters only through `hFour`. -/
theorem PhiM_le_of_invariant {α : ℝ} (hα : 1 ≤ α) (ε B Γ : ℝ≥0∞)
    (hEta : ∀ s t, R₀ s t → etaD α P R₀ s t ≤ ε)
    (hFour : ∀ n, (∀ s t, R₀ s t → PhiM α P R₀ s t n ≤ B) →
      ∀ σ τ : S × S, SquareRel R₀ σ τ →
        PhiD α (prodPMF (muM P σ.1 n) (muM P σ.2 n)) (prodPMF (muM P τ.1 n) (muM P τ.2 n))
          (SquareRel (fullSim R₀ n)) ≤ Γ)
    (hclose : ε + Γ + ENNReal.ofReal (2 * α) * (ε * Γ) ≤ B) :
    ∀ n s t, R₀ s t → PhiM α P R₀ s t n ≤ B := by
  intro n
  induction n with
  | zero =>
      intro s t hst
      rw [PhiM_zero α P R₀ hst]
      exact zero_le
  | succ n ih =>
      intro s t hst
      calc PhiM α P R₀ s t (n + 1)
          ≤ etaD α P R₀ s t + Γ
              + ENNReal.ofReal (2 * α) * (etaD α P R₀ s t * Γ) :=
            PhiM_succ_le P R₀ hα hst n Γ (hFour n ih)
        _ ≤ ε + Γ + ENNReal.ofReal (2 * α) * (ε * Γ) := by
            gcongr <;> exact hEta s t hst
        _ ≤ B := hclose

/-- **The failure bound at height `n`**: two independent root-mixture samples
fail to match with probability at most the root budget plus the ceiling,

    ℙ(no g matches) = 𝔼 q ≤ η_ι + B. -/
theorem markovMatching_failure_le {α : ℝ} (hα : 1 ≤ α) (ι : PMF S) (n : ℕ)
    (B : ℝ≥0∞) (hB : ∀ s t, R₀ s t → PhiM α P R₀ s t n ≤ B) :
    ∑' x, (ι.bind fun s => muM P s n) x
        * qE (ι.bind fun t => muM P t n) (fullSim R₀ n) x
      ≤ (∑' s, ι s * qE ι R₀ s) + B := by
  have hα0 : (0 : ℝ) ≤ α := le_trans zero_le_one hα
  calc (∑' x, (ι.bind fun s => muM P s n) x
        * qE (ι.bind fun t => muM P t n) (fullSim R₀ n) x)
      = ∑' s, ι s * ∑' x, muM P s n x
          * ∑' t, ι t * qE (muM P t n) (fullSim R₀ n) x := by
        rw [tsum_bind_mul]
        refine tsum_congr fun s => ?_
        congr 1
        refine tsum_congr fun x => ?_
        rw [qE_bind]
    _ = ∑' s, ι s * ∑' t, ι t
          * ∑' x, muM P s n x * qE (muM P t n) (fullSim R₀ n) x := by
        refine tsum_congr fun s => ?_
        congr 1
        calc (∑' x, muM P s n x * ∑' t, ι t * qE (muM P t n) (fullSim R₀ n) x)
            = ∑' x, ∑' t, ι t * (muM P s n x * qE (muM P t n) (fullSim R₀ n) x) := by
              refine tsum_congr fun x => ?_
              rw [← ENNReal.tsum_mul_left]
              exact tsum_congr fun t => by ring
          _ = ∑' t, ∑' x, ι t * (muM P s n x * qE (muM P t n) (fullSim R₀ n) x) :=
              ENNReal.tsum_comm
          _ = ∑' t, ι t * ∑' x, muM P s n x * qE (muM P t n) (fullSim R₀ n) x := by
              refine tsum_congr fun t => ?_
              rw [← ENNReal.tsum_mul_left]
    _ ≤ ∑' s, ι s * ∑' t, ((if R₀ s t then 0 else ι t) + ι t * B) := by
        refine ENNReal.tsum_le_tsum fun s => mul_le_mul_right (ENNReal.tsum_le_tsum fun t => ?_) _
        by_cases h : R₀ s t
        · rw [if_pos h, zero_add]
          calc ι t * ∑' x, muM P s n x * qE (muM P t n) (fullSim R₀ n) x
              ≤ ι t * PhiD α (muM P s n) (muM P t n) (fullSim R₀ n) :=
                mul_le_mul_right (tsum_qE_le_PhiD hα0 _ _ _) _
            _ ≤ ι t * B := mul_le_mul_right (hB s t h) _
        · rw [if_neg h]
          have hF : ι t * ∑' x, muM P s n x * qE (muM P t n) (fullSim R₀ n) x ≤ ι t := by
            calc ι t * ∑' x, muM P s n x * qE (muM P t n) (fullSim R₀ n) x
                ≤ ι t * 1 := by
                  refine mul_le_mul_right ?_ _
                  calc (∑' x, muM P s n x * qE (muM P t n) (fullSim R₀ n) x)
                      ≤ ∑' x, muM P s n x * 1 :=
                        ENNReal.tsum_le_tsum fun x => mul_le_mul_right qE_le_one _
                    _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
              _ = ι t := mul_one _
          exact le_trans hF le_self_add
    _ = (∑' s, ι s * qE ι R₀ s) + B := by
        have h1 : ∀ s : S, (∑' t, ((if R₀ s t then 0 else ι t) + ι t * B))
            = qE ι R₀ s + B := by
          intro s
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            show (∑' t, if R₀ s t then 0 else ι t) = qE ι R₀ s from rfl]
        calc (∑' s, ι s * ∑' t, ((if R₀ s t then 0 else ι t) + ι t * B))
            = ∑' s, (ι s * qE ι R₀ s + ι s * B) := by
              refine tsum_congr fun s => ?_
              rw [h1 s]
              ring
          _ = (∑' s, ι s * qE ι R₀ s) + ∑' s, ι s * B := ENNReal.tsum_add
          _ = (∑' s, ι s * qE ι R₀ s) + B := by
              rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end GraphMarkovMatching
