/-
`sec:integer` of `graph_matching_selfcontained.tex`, plus the star example at the end
of `sec:graph`. The path graph `𝖯` on `ℤ≥0` (`|j-k| ≤ 1`) is a concrete instance of
the graph setup, so `thm:matching` specialises verbatim (`path_leaf_matching_bound`,
`path_full_matching_bound`). The star example (`star_bound`) is a clean corollary
of local dominance: if all support mass sits on the closed unit ball of a single
vertex `o`, then `η_{G,α}(μ) ≤ ε₀/(1-ε₀)^{5/2}`.

The double-exponential `thm:double-exp` (a specific law with `η_{𝖯,α} ≤ 4 e^{-D(D-5/2)}`)
is the remaining numeric piece.
-/
import GraphMatching.Graph

namespace GraphMatching

open scoped ENNReal Classical
open Real

/-! ### A geometric-tail tool (foundation for `thm:double-exp`)

The double-exponential law `a_j = e^{-D^j}` has ratio `a_{j+1}/a_j ≤ e^{-20} <
1/2`, so all the tail sums in `thm:double-exp` are geometric. This lemma is the
comparison that turns a `≤ 1/2` ratio into a `∑ ≤ 2·(first term)` bound. -/

/-- A nonnegative sequence with ratio `≤ 1/2` is summable, with sum at most twice
its first term. -/
lemma geo_tail {c : ℕ → ℝ} (hnn : ∀ n, 0 ≤ c n) (hr : ∀ n, c (n + 1) ≤ (1 / 2) * c n) :
    Summable c ∧ ∑' n, c n ≤ 2 * c 0 := by
  have hbound : ∀ n, c n ≤ (1 / 2) ^ n * c 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc c (n + 1) ≤ (1 / 2) * c n := hr n
          _ ≤ (1 / 2) * ((1 / 2) ^ n * c 0) := by gcongr
          _ = (1 / 2) ^ (n + 1) * c 0 := by ring
  have hgeo : Summable (fun n => (1 / 2 : ℝ) ^ n * c 0) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hsum : Summable c := hgeo.of_nonneg_of_le hnn hbound
  refine ⟨hsum, ?_⟩
  calc ∑' n, c n ≤ ∑' n, (1 / 2 : ℝ) ^ n * c 0 := Summable.tsum_le_tsum hbound hsum hgeo
    _ = (∑' n, (1 / 2 : ℝ) ^ n) * c 0 := tsum_mul_right
    _ = 2 * c 0 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num

/-! ### The star example `eq:star` -/

/-- **`eq:star`**: if every support vertex other than `o` lies in `B_G(o,1)` (is
compatible with `o`), then `η_{G,α}(μ) ≤ ε₀/(1-ε₀)^{5/2}` with `1-ε₀ = μ{o}`. The `o`-row
of `η_{G,α}` vanishes (`τ = 0`) and every other good degree is `≥ μ{o}`. -/
theorem starA_bound {V : Type*} {α : ℝ} (hα : 0 ≤ α)
    (μ : PMF V) (G : SimpleGraph V) (o : V) (ho : μ o ≠ 0)
    (hstar : ∀ v, μ v ≠ 0 → v ≠ o → G.Adj o v) :
    etaGA α μ G ≤ ENNReal.ofReal ((1 - (μ o).toReal) / (μ o).toReal ^ α) := by
  set p : ℝ := (μ o).toReal with hp_def
  have hp : 0 < p := ENNReal.toReal_pos ho (μ.apply_ne_top o)
  have hpα : 0 < p ^ α := Real.rpow_pos_of_pos hp α
  -- τ = q(o) = 0, since every support vertex is compatible with o
  have hτ : qE μ (compat G) o = 0 := by
    rw [qE, ENNReal.tsum_eq_zero]
    intro v
    by_cases hv : μ v = 0
    · simp [hv]
    · have hc : compat G o v := by
        rcases eq_or_ne v o with rfl | hvo
        · exact Or.inl rfl
        · exact Or.inr (hstar v hv hvo)
      simp [hc]
  -- the sum of the off-o masses is ε₀
  have htail : (∑' v, if v = o then 0 else μ v) = 1 - μ o := by
    have h1 : μ o + (∑' v, if v = o then 0 else μ v) = 1 := by
      rw [← tsum_split_at μ o]; exact μ.tsum_coe
    rw [← h1, ENNReal.add_sub_cancel_left (μ.apply_ne_top o)]
  have hεenn : (1 : ℝ≥0∞) - μ o = ENNReal.ofReal (1 - p) := by
    rw [show (μ o) = ENNReal.ofReal p from (ENNReal.ofReal_toReal (μ.apply_ne_top o)).symm,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (le_of_lt hp)]
  calc etaGA α μ G
      ≤ ENNReal.ofReal ((qE μ (compat G) o).toReal / p ^ α)
          + ∑' v, (if v = o then 0 else μ v * ENNReal.ofReal (1 / gdeg μ G v ^ α)) :=
        etaGA_le_localDominance hα μ G o ho
    _ = ∑' v, (if v = o then 0 else μ v * ENNReal.ofReal (1 / gdeg μ G v ^ α)) := by
        rw [hτ]; simp
    _ ≤ ∑' v, (if v = o then 0 else μ v) * ENNReal.ofReal (1 / p ^ α) := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        rcases eq_or_ne v o with rfl | hvo
        · simp
        · by_cases hv : μ v = 0
          · simp [hv]
          · rw [if_neg hvo, if_neg hvo]
            have hco : compat G v o := Or.inr (G.adj_symm (hstar v hv hvo))
            have hle : μ o ≤ rE μ (compat G) v := by
              rw [rE]
              calc μ o = if compat G v o then μ o else 0 := (if_pos hco).symm
                _ ≤ ∑' w, if compat G v w then μ w else 0 := ENNReal.le_tsum o
            have hmv : p ≤ gdeg μ G v := by
              simp only [gdeg]
              exact ENNReal.toReal_mono rE_ne_top hle
            have hdiv : (1 : ℝ) / gdeg μ G v ^ α ≤ 1 / p ^ α :=
              one_div_le_one_div_of_le hpα (Real.rpow_le_rpow hp.le hmv hα)
            exact mul_le_mul' (le_refl (μ v)) (ENNReal.ofReal_le_ofReal hdiv)
    _ = (∑' v, if v = o then 0 else μ v) * ENNReal.ofReal (1 / p ^ α) :=
        ENNReal.tsum_mul_right
    _ = ENNReal.ofReal (1 - p) * ENNReal.ofReal (1 / p ^ α) := by rw [htail, hεenn]
    _ = ENNReal.ofReal ((1 - p) / p ^ α) := by
        rw [← ENNReal.ofReal_mul (by linarith [mu_toReal_le_one μ o])]
        congr 1
        rw [mul_one_div]

/-- `eq:star` at the pinned exponent. -/
theorem star_bound {V : Type*} (μ : PMF V) (G : SimpleGraph V) (o : V) (ho : μ o ≠ 0)
    (hstar : ∀ v, μ v ≠ 0 → v ≠ o → G.Adj o v) :
    etaG μ G ≤ ENNReal.ofReal ((1 - (μ o).toReal) / (μ o).toReal ^ alpha) := by
  rw [etaG_eq_etaGA]
  exact starA_bound alpha_nonneg μ G o ho hstar

/-! ### The path graph on `ℕ` -/

/-- The path graph `𝖯` on `ℤ≥0`: `j ~ k` iff `|j-k| = 1`. -/
def pathGraph : SimpleGraph ℕ where
  Adj j k := j + 1 = k ∨ k + 1 = j
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with h | h <;> omega⟩

@[simp] lemma pathGraph_adj {j k : ℕ} : pathGraph.Adj j k ↔ j + 1 = k ∨ k + 1 = j := Iff.rfl

/-- On the path, compatibility is the nearest-neighbour rule `|j-k| ≤ 1`. -/
lemma compat_pathGraph {j k : ℕ} : compat pathGraph j k ↔ j = k ∨ j + 1 = k ∨ k + 1 = j :=
  Iff.rfl

/-- **`sec:integer`**: `η_{𝖯,α}(p)`, the path-graph potential at a general exponent. -/
noncomputable def etaPA (α : ℝ) (p : PMF ℕ) : ℝ≥0∞ := etaGA α p pathGraph

/-- `η_{𝖯,α}(p)` at the pinned exponent, the form `thm:double-exp` is stated at. -/
noncomputable def etaP (p : PMF ℕ) : ℝ≥0∞ := etaG p pathGraph

/-- **`thm:matching`(1) for the path** (`|j-k| ≤ 1` rule): geometric leaf decay. -/
theorem path_leaf_matching_bound (p : PMF ℕ) (h0 : etaP p ≤ 1 / 256) (h : ℕ) :
    ∑' x, leafMu p h x * qE (leafMu p h) (leafSim (compat pathGraph) h) x
      ≤ (253 / 256) ^ h * etaP p :=
  graph_leaf_matching_bound p pathGraph h0 h

/-- **`thm:matching`(2) for the path**: uniform full-matching bound. -/
theorem path_full_matching_bound (p : PMF ℕ) (hη : etaP p ≤ 1 / 10000) (h : ℕ) :
    ∑' x, fullMu p h x * qE (fullMu p h) (fullSim (compat pathGraph) h) x ≤ 16 * etaP p :=
  graph_full_matching_bound p pathGraph hη h

end GraphMatching
