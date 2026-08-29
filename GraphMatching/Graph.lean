/-
`sec:graph` of `graph_matching_selfcontained.tex`: the graph specialisation.
The compatibility rule (`eq:compat`) `v ~ w ⟺ d_G(v,w) ≤ 1` is, for a simple
graph, `v = w ∨ G.Adj v w` (`compat`); under the convention that vertices in
different components are at infinite distance this is exactly `d_G(v,w) ≤ 1`.
It is symmetric and reflexive, so the abstract machinery of `sec:contraction`
through `sec:reduction` applies.

The good degree of `compat` is the mass compatible with `v`,
`b(v) = μ(B_G(v,1)) = r(v)`, and `q(v) = 1 - b(v)`. Hence the one-site weight is
`φ(q(v)) = q(v)/(1-q(v))^α = (1-b(v))/b(v)^α`, and the graph potential (`eq:etaG`)

    η_{G,α}(μ) = ∑_{v : μ(v)>0} μ(v) (1 - b(v))/b(v)^{5/2}

is exactly `Φ_0 = Φ(compat, μ)` (`etaG_eq_Phi`). `thm:matching` is then `thm:reduction`
read off through this identity (`graph_leaf_matching_bound`,
`graph_full_matching_bound`).
-/
import GraphMatching.Reduction
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace GraphMatching

open scoped ENNReal Classical

universe u
variable {V : Type u}

/-! ### The compatibility relation of a graph -/

/-- **`eq:compat`**: two labels are compatible when they are equal or adjacent,
i.e. at graph distance `≤ 1`. -/
def compat (G : SimpleGraph V) (v w : V) : Prop := v = w ∨ G.Adj v w

lemma compat_refl (G : SimpleGraph V) : ∀ v, compat G v v := fun _ => Or.inl rfl

lemma compat_symm (G : SimpleGraph V) : ∀ a b, compat G a b → compat G b a := by
  rintro a b (rfl | h)
  · exact Or.inl rfl
  · exact Or.inr (G.adj_symm h)

/-! ### The good degree and the graph potential -/

/-- **`eq:mv`**: `b(v) = μ(B_G(v,1))`, the probability that an independent label is
compatible with `v`. This is the good degree `r(v)` of the compatibility relation. -/
noncomputable def gdeg (μ : PMF V) (G : SimpleGraph V) (v : V) : ℝ :=
  (rE μ (compat G) v).toReal

/-- The one-site weight in graph terms: `φ_α(q(v)) = (1 - b(v))/b(v)^α`, using
`q(v) = 1 - b(v)`. Purely algebraic from `r + q = 1`, so it holds at every `v` and
every exponent (off the support both sides are junk but the sum in `η_{G,α}`/`Φ_α`
kills the term). -/
lemma phiA_q_eq (α : ℝ) (μ : PMF V) (R : V → V → Prop) (v : V) :
    phiA α (q μ R v) = (1 - (rE μ R v).toReal) / (rE μ R v).toReal ^ α := by
  have h := toReal_rE_add_toReal_qE μ R v
  have hq : q μ R v = 1 - (rE μ R v).toReal := by rw [q]; linarith
  rw [phiA, hq]
  have hden : (1 : ℝ) - (1 - (rE μ R v).toReal) = (rE μ R v).toReal := by ring
  rw [hden]

/-- The same identity at the pinned exponent. -/
lemma phi_q_eq (μ : PMF V) (R : V → V → Prop) (v : V) :
    phi (q μ R v) = (1 - (rE μ R v).toReal) / (rE μ R v).toReal ^ alpha :=
  phiA_q_eq alpha μ R v

/-- **`eq:etaG`**: the graph potential
`η_{G,α}(μ) = ∑_v μ(v) (1 - b(v))/b(v)^α`, at a general exponent. The paper defines it
this way and fixes `α = 5/2` only in the statement of `thm:matching`. -/
noncomputable def etaGA (α : ℝ) (μ : PMF V) (G : SimpleGraph V) : ℝ≥0∞ :=
  ∑' v, μ v * ENNReal.ofReal ((1 - gdeg μ G v) / gdeg μ G v ^ α)

/-- **The specialisation identity `η_{G,α}(μ) = Φ_α(compat G, μ)`**, at every exponent:
the graph potential is exactly the abstract potential of the compatibility relation. -/
lemma etaGA_eq_PhiA (α : ℝ) (μ : PMF V) (G : SimpleGraph V) :
    etaGA α μ G = PhiA α μ (compat G) := by
  rw [etaGA, PhiA]
  refine tsum_congr fun v => ?_
  simp only [gdeg]
  rw [phiA_q_eq]

/-- `η_{G,α}` at the pinned exponent, the form `thm:matching` is stated at. -/
noncomputable def etaG (μ : PMF V) (G : SimpleGraph V) : ℝ≥0∞ :=
  ∑' v, μ v * ENNReal.ofReal ((1 - gdeg μ G v) / gdeg μ G v ^ alpha)

lemma etaG_eq_etaGA (μ : PMF V) (G : SimpleGraph V) : etaG μ G = etaGA alpha μ G := rfl

/-- **The specialisation identity `η_{G,α}(μ) = Φ_0`** at `α = 5/2`. -/
lemma etaG_eq_Phi (μ : PMF V) (G : SimpleGraph V) : etaG μ G = Phi μ (compat G) := by
  rw [etaG_eq_etaGA, etaGA_eq_PhiA, Phi_eq_PhiA]

/-! ### `thm:matching`, the graph-valued matching bounds -/

/-- **`thm:matching`(1)** (leaf case, `eq:leaf-bound`): if `η_{G,α}(μ) ≤ 1/256` then the
probability that two independent leaf labellings of `𝔹_h` admit no compatible
matching automorphism is at most `(253/256)^h η_{G,α}(μ)`, hence tends to `0`. -/
theorem graph_leaf_matching_bound (μ : PMF V) (G : SimpleGraph V)
    (h0 : etaG μ G ≤ 1 / 256) (h : ℕ) :
    ∑' x, leafMu μ h x * qE (leafMu μ h) (leafSim (compat G) h) x
      ≤ (253 / 256) ^ h * etaG μ G := by
  rw [etaG_eq_Phi] at h0 ⊢
  exact leaf_matching_bound μ (compat G) (compat_refl G) (compat_symm G) h0 h

/-- **`thm:matching`(2)** (full case, `eq:full-bound`): if `η_{G,α}(μ) ≤ 10⁻⁴` then the
failure probability for full labellings of `𝔹_h` is at most `16 η_{G,α}(μ)`,
uniformly in the height, so the full matching probability is `≥ 1 - 16 η_{G,α}(μ)`. -/
theorem graph_full_matching_bound (μ : PMF V) (G : SimpleGraph V)
    (hη : etaG μ G ≤ 1 / 10000) (h : ℕ) :
    ∑' x, fullMu μ h x * qE (fullMu μ h) (fullSim (compat G) h) x ≤ 16 * etaG μ G := by
  rw [etaG_eq_Phi] at hη ⊢
  exact full_matching_bound μ (compat G) (compat_refl G) (compat_symm G) hη h

/-! ### The local-dominance bound (`thm:dominance`)

`η_{G,α}(μ)` is bounded by the local-dominance quantity `𝒟_G(μ,o)`, which isolates a
distinguished high-mass vertex `o`: with `ε₀ = 1 - μ{o}`, `τ = μ(V ∖ B_G(o,1))`,

    𝒟_G(μ,o) = τ/(1-ε₀)^{5/2} + ∑_{v ≠ o, μ(v)>0} μ(v)/b(v)^{5/2}.

The `o`-term is bounded using `b(o) ≥ μ{o} = 1-ε₀` and `μ{o} ≤ 1`; every other
term drops `1 - b(v) ≤ 1`. -/

/-- Basic facts about the compatible mass `b(v)`. -/
lemma gdeg_nonneg (μ : PMF V) (G : SimpleGraph V) (v : V) : 0 ≤ gdeg μ G v :=
  ENNReal.toReal_nonneg

lemma mu_toReal_le_gdeg (μ : PMF V) (G : SimpleGraph V) (v : V) :
    (μ v).toReal ≤ gdeg μ G v :=
  ENNReal.toReal_mono rE_ne_top (le_rE_of_refl (compat_refl G v))

/-- `1 - b(v) = q(v) = μ(V ∖ B_G(v,1))`. -/
lemma one_sub_gdeg (μ : PMF V) (G : SimpleGraph V) (v : V) :
    1 - gdeg μ G v = (qE μ (compat G) v).toReal := by
  have h := toReal_rE_add_toReal_qE μ (compat G) v
  simp only [gdeg]; linarith

lemma mu_toReal_le_one (μ : PMF V) (v : V) : (μ v).toReal ≤ 1 := by
  have : μ v ≤ 1 := (ENNReal.le_tsum v).trans_eq μ.tsum_coe
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top this

/-- Split a nonnegative `tsum` off its value at a distinguished point `o`. -/
lemma tsum_split_at (f : V → ℝ≥0∞) (o : V) :
    ∑' v, f v = f o + ∑' v, (if v = o then 0 else f v) := by
  have hsplit : ∀ v, f v = (if v = o then f o else 0) + (if v = o then 0 else f v) := by
    intro v; split_ifs with h
    · subst h; simp
    · simp
  rw [tsum_congr hsplit, ENNReal.tsum_add, tsum_ite_eq]

/-- **`thm:dominance`** (local dominance): `η_{G,α}(μ) ≤ 𝒟_G(μ,o)`. The distinguished
vertex `o` must carry positive mass. Combined with `graph_leaf_matching_bound` /
`graph_full_matching_bound`, this gives the usable hypothesis
`𝒟_G(μ,o) ≤ 1/256` (resp. `≤ 10⁻⁴`). -/
theorem etaGA_le_localDominance {α : ℝ} (hα : 0 ≤ α) (μ : PMF V) (G : SimpleGraph V)
    (o : V) (ho : μ o ≠ 0) :
    etaGA α μ G
      ≤ ENNReal.ofReal ((qE μ (compat G) o).toReal / (μ o).toReal ^ α)
        + ∑' v, (if v = o then 0
                 else μ v * ENNReal.ofReal (1 / gdeg μ G v ^ α)) := by
  rw [etaGA, tsum_split_at _ o]
  refine add_le_add ?_ (ENNReal.tsum_le_tsum fun v => ?_)
  · -- the distinguished term
    set p : ℝ := (μ o).toReal with hp_def
    set b : ℝ := gdeg μ G o with hb_def
    set τ : ℝ := (qE μ (compat G) o).toReal with hτ_def
    have hp : 0 < p := ENNReal.toReal_pos ho (μ.apply_ne_top o)
    have hp1 : p ≤ 1 := mu_toReal_le_one μ o
    have hpb : p ≤ b := mu_toReal_le_gdeg μ G o
    have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
    have hpα : 0 < p ^ α := Real.rpow_pos_of_pos hp α
    have hbα : p ^ α ≤ b ^ α := Real.rpow_le_rpow hp.le hpb hα
    have hnum : 1 - b = τ := one_sub_gdeg μ G o
    have hreal : p * ((1 - b) / b ^ α) ≤ τ / p ^ α := by
      rw [hnum]
      have h1 : τ / b ^ α ≤ τ / p ^ α :=
        div_le_div_of_nonneg_left hτ0 hpα hbα
      calc p * (τ / b ^ α) ≤ p * (τ / p ^ α) := by
            exact mul_le_mul_of_nonneg_left h1 hp.le
        _ ≤ 1 * (τ / p ^ α) :=
            mul_le_mul_of_nonneg_right hp1 (div_nonneg hτ0 hpα.le)
        _ = τ / p ^ α := one_mul _
    calc μ o * ENNReal.ofReal ((1 - b) / b ^ α)
        = ENNReal.ofReal p * ENNReal.ofReal ((1 - b) / b ^ α) := by
          rw [ENNReal.ofReal_toReal (μ.apply_ne_top o)]
      _ = ENNReal.ofReal (p * ((1 - b) / b ^ α)) :=
          (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
      _ ≤ ENNReal.ofReal (τ / p ^ α) := ENNReal.ofReal_le_ofReal hreal
  · -- every other term: drop `1 - b(v) ≤ 1`
    split_ifs with h
    · exact le_refl 0
    · have hbv : 0 ≤ gdeg μ G v := gdeg_nonneg μ G v
      gcongr
      linarith

/-- `thm:dominance` at the pinned exponent, the form the numeric hypotheses use. -/
theorem etaG_le_localDominance (μ : PMF V) (G : SimpleGraph V) (o : V) (ho : μ o ≠ 0) :
    etaG μ G
      ≤ ENNReal.ofReal ((qE μ (compat G) o).toReal / (μ o).toReal ^ alpha)
        + ∑' v, (if v = o then 0
                 else μ v * ENNReal.ofReal (1 / gdeg μ G v ^ alpha)) := by
  rw [etaG_eq_etaGA]
  exact etaGA_le_localDominance alpha_nonneg μ G o ho

end GraphMatching
