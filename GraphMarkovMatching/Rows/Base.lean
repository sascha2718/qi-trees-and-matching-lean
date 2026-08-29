/-
The general-ν base case of the screened block recursion
(`arbitrary_offspring_matching.tex`, `thm:base` in `sec:rows`,
height zero): over the formal grammar, every ordinary root coordinate and
every screen base value is `O(η)` with explicit constants.

* `interpPhi_base`: the Fk-free ordinary coordinates at height zero
  are at most `η + φ_α(q(v0))`;
* `phiE_q_v0_le`: the root-budget linearization
  `φ_α(q(v0)) ≤ 2^α · 2η` under the smallness `4η ≤ 1`;
* `screenInd_base_near`: at a root compatible with `v0` the zero event
  of a nonempty Fk-free zero list fails, because some member law is
  alive there;
* `interpScreen_base_forced`: forced-cell screens vanish at height
  zero, the forced root being compatible with itself;
* `interpScreen_base_fresh` / `interpScreen_base`: fresh-cell and
  fresh-component screens are at most `baseScreenBound = 4η`: the
  screen charges only roots far from `v0`, and the far mass and the
  far tilt contribute `2η` each.
-/
import GraphMarkovMatching.Process.Coordinates
import GraphMarkovMatching.Process.Failure

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u

/-- A screen against a point-mass cell law is the single term at the
point. -/
lemma screenE_pure {X : Type u} (a : X) (R : X → X → Prop)
    (zs : List (PMF X)) (nrm : X → ℝ≥0∞) :
    screenE (PMF.pure a) R zs nrm = screenInd R zs a * nrm a := by
  calc screenE (PMF.pure a) R zs nrm
      = ∑' x, (PMF.pure a : PMF X) x * (screenInd R zs x * nrm x) := by
        rw [screenE]
        exact tsum_congr fun x => mul_assoc _ _ _
    _ = screenInd R zs a * nrm a :=
        tsum_pure_mul a fun x => screenInd R zs x * nrm x

variable {V : Type} (α : ℝ) (Rv : V → V → Prop) (μ : PMF V) (ν : PMF ℕ)
  (v0 : V)

/-! ### The ordinary base coordinates -/

/-- **The ordinary base case**: every Fk-free ordinary coordinate at
height zero is at most one graph potential above the root potential. -/
lemma interpPhi_base (_hα0 : 0 ≤ α) (hrefl : Rv v0 v0) (p : Tgt × Tgt)
    (h1 : ∀ i, p.1 ≠ Tgt.Fk i) (h2 : ∀ i, p.2 ≠ Tgt.Fk i) :
    interpPhi α Rv μ ν v0 0 p ≤ etaG α Rv μ + phiE α (q μ Rv v0) := by
  obtain ⟨a, b⟩ := p
  cases a with
  | Fk i => exact absurd rfl (h1 i)
  | Z k =>
      cases b with
      | Fk i => exact absurd rfl (h2 i)
      | Z j =>
          refine le_trans (le_of_eq ?_) zero_le
          exact PhiDres_Zlaw_Zlaw_zero α Rv μ ν v0 hrefl k j
      | F =>
          exact le_trans (PhiDres_Zlaw_Tlaw_zero α Rv μ ν v0 k) le_add_self
  | F =>
      cases b with
      | Fk i => exact absurd rfl (h2 i)
      | Z j =>
          refine le_trans (le_of_eq ?_) zero_le
          exact PhiDres_Tlaw_Zlaw_zero α Rv μ ν v0 j
      | F =>
          exact le_trans (PhiDres_Tlaw_Tlaw_zero_le α Rv μ ν v0) le_self_add

/-! ### The root-budget linearization -/

/-- **The root-budget linearization at height 0**: once
`4η ≤ 1`, the root potential is at most `2^α` times the far mass
`2η`. -/
lemma phiE_q_v0_le (hα0 : 0 ≤ α) (_hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0) (hsmall : (4 : ℝ≥0∞) * etaG α Rv μ ≤ 1) :
    phiE α (q μ Rv v0) ≤ (2 : ℝ≥0∞) ^ α * (2 * etaG α Rv μ) := by
  have hq2 : qE μ Rv v0 ≤ 2 * etaG α Rv μ := qE_zero_le α Rv μ v0 hα0 hhalf
  have hqhalf : qE μ Rv v0 ≤ 2⁻¹ := by
    refine le_trans hq2 (ENNReal.le_inv_iff_mul_le.mpr ?_)
    calc (2 : ℝ≥0∞) * etaG α Rv μ * 2 = 4 * etaG α Rv μ := by ring
      _ ≤ 1 := hsmall
  calc phiE α (q μ Rv v0)
      ≤ ENNReal.ofReal (2 ^ α) * qE μ Rv v0 :=
        phiE_le_of_qE_le_half hα0 μ Rv v0 hqhalf
    _ ≤ ENNReal.ofReal (2 ^ α) * (2 * etaG α Rv μ) :=
        mul_le_mul_right hq2 _
    _ = (2 : ℝ≥0∞) ^ α * (2 * etaG α Rv μ) := by
        rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2),
          show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) from by simp]

/-! ### The height-zero dead-set analysis -/

/-- **Near roots defeat nonempty Fk-free zero lists**: at a root
compatible with `v0`, every forced member of the zero list is alive
(`rE = 1`) and every fresh member carries at least the mass of `v0`,
so the zero event fails. -/
lemma screenInd_base_near (hpos : (μ v0 : ℝ≥0∞) ≠ 0)
    {z : Finset Tgt} (hz : z.Nonempty)
    (hzf : ∀ t ∈ z, ∀ m, t ≠ Tgt.Fk m) {v : V} (hv : Rv v v0) (k : ℕ) :
    screenInd (fullSim (labRel Rv) 0)
      ((z.toList).map (interpT μ ν v0 0)) (leaf (v, k)) = 0 := by
  obtain ⟨t0, ht0⟩ := hz
  have hne : ¬ ∀ ρ ∈ (z.toList).map (interpT μ ν v0 0),
      rE ρ (fullSim (labRel Rv) 0) (leaf (v, k)) = 0 := by
    intro hall
    have h0 := hall (interpT μ ν v0 0 t0)
      (List.mem_map.mpr ⟨t0, Finset.mem_toList.mpr ht0, rfl⟩)
    cases t0 with
    | Z j =>
        rw [show interpT μ ν v0 0 (Tgt.Z j) = Zlaw μ ν v0 j 0 from rfl,
          rE_Zlaw_zero_eq Rv μ v0 ν v k j, if_pos hv] at h0
        exact one_ne_zero h0
    | F =>
        rw [show interpT μ ν v0 0 Tgt.F = Tlaw μ ν v0 0 from rfl,
          rE_Tlaw_zero Rv μ ν v0 v k] at h0
        have hle : μ v0 ≤ rE μ Rv v := by
          calc (μ v0 : ℝ≥0∞) = if Rv v v0 then μ v0 else 0 := by
                rw [if_pos hv]
            _ ≤ ∑' w, if Rv v w then μ w else 0 := ENNReal.le_tsum v0
        rw [h0] at hle
        exact hpos (le_antisymm hle zero_le)
    | Fk m => exact absurd rfl (hzf _ ht0 m)
  rw [screenInd, if_neg hne]

/-- **The pointwise base screen bound**: at a near root the screen
indicator vanishes; at a far root the indicator is at most one and the
Fk-free normalization is at most `1 + r(v)^{-α}` (the forced tilt is
dead there, the fresh tilt is the label tilt). -/
lemma base_far_pointwise (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0) {z : Finset Tgt} (hz : z.Nonempty)
    (hzf : ∀ t ∈ z, ∀ m, t ≠ Tgt.Fk m) {u : Option Tgt}
    (hu : ∀ m, u ≠ some (Tgt.Fk m)) (v : V) (k : ℕ) :
    screenInd (fullSim (labRel Rv) 0)
        ((z.toList).map (interpT μ ν v0 0)) (leaf (v, k))
      * interpNorm α Rv μ ν v0 0 u (leaf (v, k))
      ≤ if Rv v0 v then 0 else 1 + (rE μ Rv v) ^ (-α) := by
  have hpos : (μ v0 : ℝ≥0∞) ≠ 0 := by
    intro h0
    rw [h0] at hhalf
    simp at hhalf
  by_cases hv : Rv v v0
  · rw [screenInd_base_near Rv μ ν v0 hpos hz hzf hv k, zero_mul]
    exact zero_le
  · rw [if_neg (fun hc : Rv v0 v => hv (hsymm v0 v hc))]
    calc screenInd (fullSim (labRel Rv) 0)
            ((z.toList).map (interpT μ ν v0 0)) (leaf (v, k))
          * interpNorm α Rv μ ν v0 0 u (leaf (v, k))
        ≤ 1 * interpNorm α Rv μ ν v0 0 u (leaf (v, k)) := by
          refine mul_le_mul_left ?_ _
          rw [screenInd]
          split_ifs
          · exact le_rfl
          · exact zero_le
      _ = interpNorm α Rv μ ν v0 0 u (leaf (v, k)) := one_mul _
      _ ≤ 1 + (rE μ Rv v) ^ (-α) := by
          cases u with
          | none => exact le_self_add
          | some t =>
              cases t with
              | Z j =>
                  have h0 : rE (Zlaw μ ν v0 j 0) (fullSim (labRel Rv) 0)
                      (leaf (v, k)) = 0 := by
                    rw [rE_Zlaw_zero_eq Rv μ v0 ν v k j, if_neg hv]
                  show WresD α (Zlaw μ ν v0 j 0) (fullSim (labRel Rv) 0)
                      (leaf (v, k)) ≤ _
                  rw [WresD, if_pos h0]
                  exact zero_le
              | F =>
                  exact le_trans (WresD_Tlaw_zero_le α Rv μ v0 ν v k)
                    le_add_self
              | Fk m => exact absurd rfl (hu m)

/-- The far sum of `μ(v)·(1 + r(v)^{-α})`: the far mass plus the far
tilt, at most `4η`. -/
lemma far_one_add_tilt_le (hα : 0 < α) (hsymm : ∀ a b, Rv a b → Rv b a)
    (hhalf : 2⁻¹ ≤ μ v0) :
    (∑' v, if Rv v0 v then 0 else μ v * (1 + (rE μ Rv v) ^ (-α)))
      ≤ 4 * etaG α Rv μ := by
  calc (∑' v, if Rv v0 v then 0 else μ v * (1 + (rE μ Rv v) ^ (-α)))
      = ∑' v, ((if Rv v0 v then 0 else μ v)
          + if Rv v0 v then 0 else μ v * (rE μ Rv v) ^ (-α)) := by
        refine tsum_congr fun v => ?_
        by_cases hv : Rv v0 v
        · rw [if_pos hv, if_pos hv, if_pos hv, add_zero]
        · rw [if_neg hv, if_neg hv, if_neg hv, mul_add, mul_one]
    _ = (∑' v, if Rv v0 v then 0 else μ v)
        + ∑' v, if Rv v0 v then 0 else μ v * (rE μ Rv v) ^ (-α) :=
        ENNReal.tsum_add
    _ ≤ 2 * etaG α Rv μ + 2 * etaG α Rv μ := by
        refine add_le_add ?_ (far_tilt_le α Rv μ v0 hα hsymm hhalf)
        rw [show (∑' v, if Rv v0 v then 0 else μ v) = qE μ Rv v0 from rfl]
        exact qE_zero_le α Rv μ v0 (le_of_lt hα) hhalf
    _ = 4 * etaG α Rv μ := by ring

/-- The height-zero fresh law under a screen sum: the counters expose
and the cell law is the fresh point-mass mixture. -/
lemma screenE_Tlaw_zero_eq (zs : List (PMF (FullLab (V × ℕ) 0)))
    (nrm : FullLab (V × ℕ) 0 → ℝ≥0∞) :
    screenE (Tlaw μ ν v0 0) (fullSim (labRel Rv) 0) zs nrm
      = ∑' s : V × ℕ, freshQ μ ν s
          * (screenInd (fullSim (labRel Rv) 0) zs (leaf s)
            * nrm (leaf s)) := by
  rw [show Tlaw μ ν v0 0
      = (freshQ μ ν).bind (fun s => muM (varyK μ ν v0) s 0) from rfl,
    screenE_bind_left]
  refine tsum_congr fun s => ?_
  show freshQ μ ν s * screenE (muM (varyK μ ν v0) s 0)
      (fullSim (labRel Rv) 0) zs nrm
    = freshQ μ ν s * (screenInd (fullSim (labRel Rv) 0) zs (leaf s)
        * nrm (leaf s))
  rw [show muM (varyK μ ν v0) s 0 = PMF.pure (leaf s) from rfl,
    screenE_pure]

/-- The height-zero fresh-component law under a screen sum: the counter
is frozen and the root label is a `μ`-sample. -/
lemma screenE_Flaw_zero_eq (m : ℕ) (zs : List (PMF (FullLab (V × ℕ) 0)))
    (nrm : FullLab (V × ℕ) 0 → ℝ≥0∞) :
    screenE (Flaw μ ν v0 m 0) (fullSim (labRel Rv) 0) zs nrm
      = ∑' v, μ v
          * (screenInd (fullSim (labRel Rv) 0) zs (leaf (v, m))
            * nrm (leaf (v, m))) := by
  rw [show Flaw μ ν v0 m 0
      = μ.bind (fun v => muM (varyK μ ν v0) (v, m) 0) from rfl,
    screenE_bind_left]
  refine tsum_congr fun v => ?_
  show μ v * screenE (muM (varyK μ ν v0) (v, m) 0)
      (fullSim (labRel Rv) 0) zs nrm
    = μ v * (screenInd (fullSim (labRel Rv) 0) zs (leaf (v, m))
        * nrm (leaf (v, m)))
  rw [show muM (varyK μ ν v0) (v, m) 0 = PMF.pure (leaf (v, m)) from rfl,
    screenE_pure]

/-! ### The screen base values -/

/-- **The forced-cell screen base vanishes**: the forced cell is the
point mass at the `v0`-rooted leaf, a near root, where a nonempty
Fk-free zero list is unsatisfiable. -/
lemma interpScreen_base_forced (hrefl : ∀ x, Rv x x) (i : ℕ)
    (z : Finset Tgt) (hz : z.Nonempty)
    (hzf : ∀ t ∈ z, ∀ m, t ≠ Tgt.Fk m) (u : Option Tgt)
    (hpos : (μ v0 : ℝ≥0∞) ≠ 0) :
    interpScreen α Rv μ ν v0 0 ⟨Tgt.Z i, z, u⟩ = 0 := by
  calc interpScreen α Rv μ ν v0 0 ⟨Tgt.Z i, z, u⟩
      = screenInd (fullSim (labRel Rv) 0)
            ((z.toList).map (interpT μ ν v0 0)) (leaf (v0, i))
          * interpNorm α Rv μ ν v0 0 u (leaf (v0, i)) :=
        screenE_pure (leaf (v0, i)) (fullSim (labRel Rv) 0)
          ((z.toList).map (interpT μ ν v0 0))
          (interpNorm α Rv μ ν v0 0 u)
    _ = 0 := by
        rw [screenInd_base_near Rv μ ν v0 hpos hz hzf (hrefl v0) i,
          zero_mul]

/-- **The fresh-cell screen base**: a fresh or fresh-component cell
with a nonempty Fk-free zero list and an Fk-free normalization charges
only far roots, so its base value is at most the far mass plus the far
tilt, `4η`. -/
lemma interpScreen_base_fresh (hα : 0 < α) (_hrefl : ∀ x, Rv x x)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0)
    (c : Tgt) (hc : c = Tgt.F ∨ ∃ m, c = Tgt.Fk m) (z : Finset Tgt)
    (hz : z.Nonempty) (hzf : ∀ t ∈ z, ∀ m, t ≠ Tgt.Fk m)
    (u : Option Tgt) (hu : ∀ m, u ≠ some (Tgt.Fk m)) :
    interpScreen α Rv μ ν v0 0 ⟨c, z, u⟩ ≤ 4 * etaG α Rv μ := by
  rcases hc with rfl | ⟨m, rfl⟩
  · calc interpScreen α Rv μ ν v0 0 ⟨Tgt.F, z, u⟩
        = ∑' s : V × ℕ, freshQ μ ν s
            * (screenInd (fullSim (labRel Rv) 0)
                  ((z.toList).map (interpT μ ν v0 0)) (leaf s)
              * interpNorm α Rv μ ν v0 0 u (leaf s)) :=
          screenE_Tlaw_zero_eq Rv μ ν v0
            ((z.toList).map (interpT μ ν v0 0))
            (interpNorm α Rv μ ν v0 0 u)
      _ ≤ ∑' s : V × ℕ, freshQ μ ν s
            * (if Rv v0 s.1 then 0 else 1 + (rE μ Rv s.1) ^ (-α)) := by
          refine ENNReal.tsum_le_tsum fun s => mul_le_mul_right ?_ _
          obtain ⟨v, k⟩ := s
          exact base_far_pointwise α Rv μ ν v0 hsymm hhalf hz hzf hu v k
      _ = ∑' v, if Rv v0 v then 0
            else μ v * (1 + (rE μ Rv v) ^ (-α)) := by
          rw [tsum_congr fun s : V × ℕ => show freshQ μ ν s
              * (if Rv v0 s.1 then 0 else 1 + (rE μ Rv s.1) ^ (-α))
              = (if Rv v0 s.1 then 0
                  else μ s.1 * (1 + (rE μ Rv s.1) ^ (-α))) * ν s.2
              from by
                rw [show freshQ μ ν s = μ s.1 * ν s.2 from rfl]
                by_cases hv : Rv v0 s.1 <;> simp [hv]; ring,
            tsum_prod_split (fun v => if Rv v0 v then 0
              else μ v * (1 + (rE μ Rv v) ^ (-α)))
              (fun k => (ν k : ℝ≥0∞)),
            ν.tsum_coe, mul_one]
      _ ≤ 4 * etaG α Rv μ := far_one_add_tilt_le α Rv μ v0 hα hsymm hhalf
  · calc interpScreen α Rv μ ν v0 0 ⟨Tgt.Fk m, z, u⟩
        = ∑' v, μ v
            * (screenInd (fullSim (labRel Rv) 0)
                  ((z.toList).map (interpT μ ν v0 0)) (leaf (v, m))
              * interpNorm α Rv μ ν v0 0 u (leaf (v, m))) :=
          screenE_Flaw_zero_eq Rv μ ν v0 m
            ((z.toList).map (interpT μ ν v0 0))
            (interpNorm α Rv μ ν v0 0 u)
      _ ≤ ∑' v, μ v
            * (if Rv v0 v then 0 else 1 + (rE μ Rv v) ^ (-α)) := by
          refine ENNReal.tsum_le_tsum fun v => mul_le_mul_right ?_ _
          exact base_far_pointwise α Rv μ ν v0 hsymm hhalf hz hzf hu v m
      _ = ∑' v, if Rv v0 v then 0
            else μ v * (1 + (rE μ Rv v) ^ (-α)) := by
          refine tsum_congr fun v => ?_
          by_cases hv : Rv v0 v
          · rw [if_pos hv, if_pos hv, mul_zero]
          · rw [if_neg hv, if_neg hv]
      _ ≤ 4 * etaG α Rv μ := far_one_add_tilt_le α Rv μ v0 hα hsymm hhalf

/-! ### Packaging -/

/-- The uniform base screen bound `4η`. -/
noncomputable def baseScreenBound : ℝ≥0∞ := 4 * etaG α Rv μ

/-- **The screen base case, packaged**: every formal screen with a
nonempty Fk-free zero list and an Fk-free normalization interprets at
height zero to at most `baseScreenBound = 4η` (forced cells vanish,
fresh and fresh-component cells contribute the far mass and the far tilt). -/
lemma interpScreen_base (hα : 0 < α) (hrefl : ∀ x, Rv x x)
    (hsymm : ∀ a b, Rv a b → Rv b a) (hhalf : 2⁻¹ ≤ μ v0)
    (sc : GScreen) (hz : sc.zlist.Nonempty)
    (hzf : ∀ t ∈ sc.zlist, ∀ m, t ≠ Tgt.Fk m)
    (hu : ∀ m, sc.norm ≠ some (Tgt.Fk m)) :
    interpScreen α Rv μ ν v0 0 sc ≤ baseScreenBound α Rv μ := by
  obtain ⟨c, z, u⟩ := sc
  show interpScreen α Rv μ ν v0 0 ⟨c, z, u⟩ ≤ 4 * etaG α Rv μ
  cases c with
  | Z i =>
      have hpos : (μ v0 : ℝ≥0∞) ≠ 0 := by
        intro h0
        rw [h0] at hhalf
        simp at hhalf
      rw [interpScreen_base_forced α Rv μ ν v0 hrefl i z hz hzf u hpos]
      exact zero_le
  | F =>
      exact interpScreen_base_fresh α Rv μ ν v0 hα hrefl hsymm hhalf
        Tgt.F (Or.inl rfl) z hz hzf u hu
  | Fk m =>
      exact interpScreen_base_fresh α Rv μ ν v0 hα hrefl hsymm hhalf
        (Tgt.Fk m) (Or.inr ⟨m, rfl⟩) z hz hzf u hu

end GraphMarkovMatching
