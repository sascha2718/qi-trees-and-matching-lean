/-
Numerical evaluation of the scalar constants of `arbitrary_offspring_matching.tex`
(`sec:exponent-values`: `sec:exponent-range`, `sec:exponent-four-thirds`,
`sec:optimal-coefficient-two`, `sec:two-exponent-values`).

* The exponent `4/3` (`sec:exponent-four-thirds`): the rational bounds
  `L_{4/3}(11/40) < 403/1000`, `K_{4/3}(11/40) < 12/125`, `λ_{4/3} < 499/500`, the quadratic
  coefficient `C_{4/3}(1/2) = 272/9 - 2^{5/3} < 28`, and the rational four-law bound
  `fourLaw_fourThirds`.
* The exponent `2` (`sec:two-exponent-values`): `L_2(1/16) = 1/4`, `K_2(1/16) = 125/1024`,
  `L_2 = 1/4`, `C_2(1/2) = 38`, `λ_2 ≤ 381/512`, the four-law bound `eq:mean-exponent-two`,
  and the scalar criterion at `η ≤ 1/2500` with `K = 1024/131`.
* The exponent range (`sec:exponent-range`): `λ` is Lipschitz, continuous and strictly
  decreasing on `[1, ∞)`, `λ_1 > 1 > λ_2`, the threshold `α_*` with `λ_α < 1 ↔ α > α_*`,
  and `α_* < 4/3`.
* The algebraic minimum at exponent two (`sec:optimal-coefficient-two`): the maximiser
  `(2β)^{-1/3} - 1` of `L_2(β)` for `1/16 < β < 1/2`, the quartic `3q⁴ + 8q³ + 6q² - 2`,
  `λ_2 = 2 (L_2(β) + K_2(β))` at `β = (3q-1)/2` for its root `q`, the closed form
  `λ_2 = 8 q³`, and the bracket `0.7003 < λ_2 < 0.7004`.

The bound `L_{4/3}(11/40) < 403/1000` is proved by a rigorous subdivision of `[0,1]` into 60
pieces (`fourThirdsBnd_all`): on each piece `[a, b]` the first summand `q/(1+q)^{4/3}` is
bounded by its value at `b` (it is increasing on `[0,1]`, `first_summand_mono`), the second
summand `(11/40)(1-q)^{4/3}` by its value at `a`, and both values are compared with rational
surrogates by cubing (`first_summand_le`, `second_summand_le`). The subdivision replaces the
derivative count of the note; the two rational cube comparisons the note displays are the
instance `[589/1000, 59/100]` of the same estimate.

The continuity and monotonicity of `λ` in the exponent rest on the modulus
`0 ≤ s^α - s^{α'} ≤ α' - α` for `s ∈ [0,1]` and `1 ≤ α ≤ α'` (`rpow_sub_rpow_exponent_le`),
and on the characterisation of `K_α(0)` as the maximum of `q (1-q)^α` (`Kfun_bound`,
`Kfun_attained`), which makes `K_α(0)` strictly decreasing without differentiating
`α^α/(α+1)^{α+1}`.
-/
import GraphMarkovMatching.Stopped.Scalar
import GraphMarkovMatching.Stopped.FourLaw

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support Real
open scoped ENNReal Classical

/-! ### Cubing rational surrogates of cube roots -/

/-- `(x^r)^3 = x^n` for `x ≥ 0` and `3 r = n`. -/
lemma rpow_cube_eq {x r : ℝ} (hx : 0 ≤ x) {n : ℕ} (hr : r * 3 = n) : (x ^ r) ^ 3 = x ^ n := by
  rw [show (x ^ r) ^ 3 = (x ^ r) ^ ((3 : ℕ) : ℝ) from (Real.rpow_natCast _ 3).symm,
    ← Real.rpow_mul hx, show r * ((3 : ℕ) : ℝ) = (n : ℝ) by push_cast; linarith,
    Real.rpow_natCast]

/-- The first summand of `L_{4/3}` at `b` is at most `c` once `b³ ≤ c³ (1+b)⁴`
(`sec:exponent-four-thirds`: cubing preserves the order). -/
lemma first_summand_le {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : b ^ 3 ≤ c ^ 3 * (1 + b) ^ 4) : b / (1 + b) ^ (4 / 3 : ℝ) ≤ c := by
  have hpos : 0 < (1 + b) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [div_le_iff₀ hpos]
  have hy : 0 ≤ c * (1 + b) ^ (4 / 3 : ℝ) := mul_nonneg hc hpos.le
  rw [← pow_le_pow_iff_left₀ hb hy (by norm_num : (3 : ℕ) ≠ 0), mul_pow,
    rpow_cube_eq (by linarith) (n := 4) (by norm_num)]
  exact h

/-- The second summand of `L_{4/3}` at `a` is at most `c` once `(1-a)⁴ ≤ c³`
(`sec:exponent-four-thirds`). -/
lemma second_summand_le {a c : ℝ} (ha : a ≤ 1) (hc : 0 ≤ c) (h : (1 - a) ^ 4 ≤ c ^ 3) :
    (1 - a) ^ (4 / 3 : ℝ) ≤ c := by
  have h0 : 0 ≤ 1 - a := by linarith
  have hx : 0 ≤ (1 - a) ^ (4 / 3 : ℝ) := Real.rpow_nonneg h0 _
  rw [← pow_le_pow_iff_left₀ hx hc (by norm_num : (3 : ℕ) ≠ 0),
    rpow_cube_eq h0 (n := 4) (by norm_num)]
  exact h

/-- `q ↦ q/(1+q)^{4/3}` is increasing on `[0,1]` (`sec:exponent-four-thirds`): cubed, the
difference `b³(1+q)⁴ - q³(1+b)⁴` factors through `b - q`. -/
lemma first_summand_mono {q b : ℝ} (hq : 0 ≤ q) (hqb : q ≤ b) (hb : b ≤ 1) :
    q / (1 + q) ^ (4 / 3 : ℝ) ≤ b / (1 + b) ^ (4 / 3 : ℝ) := by
  have hqp : 0 < (1 + q) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hbp : 0 < (1 + b) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [div_le_div_iff₀ hqp hbp]
  have hl : 0 ≤ q * (1 + b) ^ (4 / 3 : ℝ) := mul_nonneg hq hbp.le
  have hr : 0 ≤ b * (1 + q) ^ (4 / 3 : ℝ) := mul_nonneg (hq.trans hqb) hqp.le
  rw [← pow_le_pow_iff_left₀ hl hr (by norm_num : (3 : ℕ) ≠ 0), mul_pow, mul_pow,
    rpow_cube_eq (by linarith) (n := 4) (by norm_num),
    rpow_cube_eq (by linarith) (n := 4) (by norm_num)]
  have hb0 : 0 ≤ b := hq.trans hqb
  have hbq : b * q ≤ 1 := by nlinarith
  have hbq0 : 0 ≤ b * q := mul_nonneg hb0 hq
  have hcube : b ^ 3 * q ^ 3 ≤ b ^ 2 * q ^ 2 := by
    have e1 : b ^ 3 * q ^ 3 = (b * q) ^ 2 * (b * q) := by ring
    have e2 : b ^ 2 * q ^ 2 = (b * q) ^ 2 * 1 := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hbq (sq_nonneg _)
  have hQ : 0 ≤ b ^ 2 + b * q + q ^ 2 + 4 * b * q * (b + q) + 6 * b ^ 2 * q ^ 2
      - b ^ 3 * q ^ 3 := by
    nlinarith [mul_nonneg hbq0 (add_nonneg hb0 hq), sq_nonneg b, sq_nonneg q]
  have e : b ^ 3 * (1 + q) ^ 4 - q ^ 3 * (1 + b) ^ 4
      = (b - q) * (b ^ 2 + b * q + q ^ 2 + 4 * b * q * (b + q) + 6 * b ^ 2 * q ^ 2
        - b ^ 3 * q ^ 3) := by ring
  nlinarith [mul_nonneg (sub_nonneg.2 hqb) hQ]

/-! ### The exponent `4/3` (`sec:exponent-four-thirds`) -/

/-- The two-summand monotone bound on a piece `[a, b]` of `[0,1]`
(`sec:exponent-four-thirds`). -/
lemma Lsummand_fourThirds_piece {a b c₁ c₂ : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (h₁ : b ^ 3 ≤ c₁ ^ 3 * (1 + b) ^ 4)
    (h₂ : (1 - a) ^ 4 ≤ c₂ ^ 3) {q : ℝ} (hqa : a ≤ q) (hqb : q ≤ b) :
    Lsummand (4 / 3) (11 / 40) q ≤ c₁ + 11 / 40 * c₂ := by
  unfold Lsummand
  have hq0 : 0 ≤ q := ha.trans hqa
  have h1 : q / (1 + q) ^ (4 / 3 : ℝ) ≤ c₁ :=
    (first_summand_mono hq0 hqb hb).trans (first_summand_le (hq0.trans hqb) hc₁ h₁)
  have h2 : (1 - q) ^ (4 / 3 : ℝ) ≤ c₂ := by
    have hm : (1 - q) ^ (4 / 3 : ℝ) ≤ (1 - a) ^ (4 / 3 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    exact hm.trans (second_summand_le (by linarith) hc₂ h₂)
  linarith

/-- The piece predicate: `Lsummand (4/3) (11/40) ≤ 4029/10000` on `[a, b]`. -/
def FourThirdsBnd (a b : ℝ) : Prop :=
  ∀ q, a ≤ q → q ≤ b → Lsummand (4 / 3) (11 / 40) q ≤ 4029 / 10000

/-- Adjacent pieces concatenate. -/
lemma FourThirdsBnd.trans {a b c : ℝ} (h₁ : FourThirdsBnd a b) (h₂ : FourThirdsBnd b c) :
    FourThirdsBnd a c := by
  intro q hqa hqc
  rcases le_or_gt q b with h | h
  · exact h₁ q hqa h
  · exact h₂ q h.le hqc

/-- A piece is verified by seven rational inequalities. -/
lemma fourThirdsBnd_of {a b c₁ c₂ : ℝ}
    (h : 0 ≤ a ∧ b ≤ 1 ∧ 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ b ^ 3 ≤ c₁ ^ 3 * (1 + b) ^ 4
      ∧ (1 - a) ^ 4 ≤ c₂ ^ 3 ∧ c₁ + 11 / 40 * c₂ ≤ 4029 / 10000) : FourThirdsBnd a b :=
  fun _ hqa hqb =>
    (Lsummand_fourThirds_piece h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 hqa
      hqb).trans h.2.2.2.2.2.2

/-- `Lsummand (4/3) (11/40) ≤ 4029/10000` on `[0,1]`: the subdivision into 60 pieces
(`sec:exponent-four-thirds`). -/
lemma fourThirdsBnd_all : FourThirdsBnd 0 1 := by
  refine (fourThirdsBnd_of (a := 0) (b := 309/2000)
    (c₁ := 255133/2000000) (c₂ := 1) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 309/2000) (b := 49/200)
    (c₁ := 1829253/10000000) (c₂ := 1598999/2000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 49/200) (b := 609/2000)
    (c₁ := 2136299/10000000) (c₂ := 6874841/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 609/2000) (b := 347/1000)
    (c₁ := 583149/2500000) (c₂ := 6162111/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 347/1000) (b := 379/1000)
    (c₁ := 493837/2000000) (c₂ := 5665231/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 379/1000) (b := 809/2000)
    (c₁ := 642929/2500000) (c₂ := 8477/16000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 809/2000) (b := 17/40)
    (c₁ := 1325173/5000000) (c₂ := 2505027/5000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 17/40) (b := 221/500)
    (c₁ := 1356559/5000000) (c₂ := 4781423/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 221/500) (b := 913/2000)
    (c₁ := 276499/1000000) (c₂ := 4593873/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 913/2000) (b := 469/1000)
    (c₁ := 1404259/5000000) (c₂ := 22177/50000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 469/1000) (b := 12/25)
    (c₁ := 142297/500000) (c₂ := 429991/1000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 12/25) (b := 979/2000)
    (c₁ := 2877611/10000000) (c₂ := 836311/2000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 979/2000) (b := 249/500)
    (c₁ := 726363/2500000) (c₂ := 510001/1250000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 249/500) (b := 253/500)
    (c₁ := 586247/2000000) (c₂ := 3989683/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 253/500) (b := 1027/2000)
    (c₁ := 738761/2500000) (c₂ := 1952567/5000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1027/2000) (b := 13/25)
    (c₁ := 14877/50000) (c₂ := 956571/2500000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 13/25) (b := 263/500)
    (c₁ := 2993963/10000000) (c₂ := 3758273/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 263/500) (b := 133/250)
    (c₁ := 376539/1250000) (c₂ := 1847883/5000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 133/250) (b := 43/80)
    (c₁ := 3028947/10000000) (c₂ := 3633523/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 43/80) (b := 543/1000)
    (c₁ := 3045407/10000000) (c₂ := 3576699/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 543/1000) (b := 137/250)
    (c₁ := 153011/500000) (c₂ := 35201/100000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 137/250) (b := 553/1000)
    (c₁ := 768723/2500000) (c₂ := 3468843/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 553/1000) (b := 223/400)
    (c₁ := 1543989/5000000) (c₂ := 136711/400000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 223/400) (b := 281/500)
    (c₁ := 387619/1250000) (c₂ := 421497/1250000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 281/500) (b := 1133/2000)
    (c₁ := 622763/2000000) (c₂ := 831583/2500000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1133/2000) (b := 571/1000)
    (c₁ := 390821/1250000) (c₂ := 820211/2500000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 571/1000) (b := 1151/2000)
    (c₁ := 1569607/5000000) (c₂ := 3235513/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1151/2000) (b := 1159/2000)
    (c₁ := 787591/2500000) (c₂ := 159517/500000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1159/2000) (b := 1167/2000)
    (c₁ := 316143/1000000) (c₂ := 39379/125000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1167/2000) (b := 47/80)
    (c₁ := 793103/2500000) (c₂ := 3110427/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 47/80) (b := 1183/2000)
    (c₁ := 3183313/10000000) (c₂ := 1535331/5000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1183/2000) (b := 1191/2000)
    (c₁ := 3194131/10000000) (c₂ := 121241/400000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1191/2000) (b := 3/5)
    (c₁ := 641241/2000000) (c₂ := 2991517/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 3/5) (b := 1209/2000)
    (c₁ := 1609089/5000000) (c₂ := 1473613/5000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1209/2000) (b := 609/1000)
    (c₁ := 64601/200000) (c₂ := 29031/100000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 609/1000) (b := 1227/2000)
    (c₁ := 3241823/10000000) (c₂ := 1429571/5000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1227/2000) (b := 309/500)
    (c₁ := 1626749/5000000) (c₂ := 351919/1250000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 309/500) (b := 623/1000)
    (c₁ := 653271/2000000) (c₂ := 692933/2500000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 623/1000) (b := 157/250)
    (c₁ := 1639547/5000000) (c₂ := 1361733/5000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 157/250) (b := 1267/2000)
    (c₁ := 329297/1000000) (c₂ := 668853/2500000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1267/2000) (b := 639/1000)
    (c₁ := 3306707/10000000) (c₂ := 2622801/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 639/1000) (b := 129/200)
    (c₁ := 3321533/10000000) (c₂ := 2570453/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 129/200) (b := 1303/2000)
    (c₁ := 3337411/10000000) (c₂ := 2513649/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1303/2000) (b := 1317/2000)
    (c₁ := 33543/100000) (c₂ := 2452471/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1317/2000) (b := 333/500)
    (c₁ := 843039/2500000) (c₂ := 2387011/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 333/500) (b := 337/500)
    (c₁ := 1695467/5000000) (c₂ := 231737/1000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 337/500) (b := 683/1000)
    (c₁ := 682347/2000000) (c₂ := 2243659/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 683/1000) (b := 693/1000)
    (c₁ := 3434451/10000000) (c₂ := 2161453/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 693/1000) (b := 88/125)
    (c₁ := 432371/1250000) (c₂ := 2071021/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 88/125) (b := 1433/2000)
    (c₁ := 697249/2000000) (c₂ := 493169/2500000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1433/2000) (b := 1461/2000)
    (c₁ := 140643/400000) (c₂ := 1862391/10000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1461/2000) (b := 1493/2000)
    (c₁ := 709853/2000000) (c₂ := 348157/2000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1493/2000) (b := 1531/2000)
    (c₁ := 358747/1000000) (c₂ := 100273/625000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 1531/2000) (b := 197/250)
    (c₁ := 907771/2500000) (c₂ := 723037/5000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 197/250) (b := 163/200)
    (c₁ := 736239/2000000) (c₂ := 12641/100000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 163/200) (b := 339/400)
    (c₁ := 3738469/10000000) (c₂ := 527067/5000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 339/400) (b := 71/80)
    (c₁ := 3804689/10000000) (c₂ := 407377/5000000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 71/80) (b := 117/125)
    (c₁ := 193957/500000) (c₂ := 33943/625000) (by norm_num)).trans ?_
  refine (fourThirdsBnd_of (a := 117/125) (b := 397/400)
    (c₁ := 98963/250000) (c₂ := 16/625) (by norm_num)).trans ?_
  exact fourThirdsBnd_of (a := 397/400) (b := 1)
    (c₁ := 3968503/10000000) (c₂ := 14681/10000000) (by norm_num)

/-- `L_{4/3}(11/40) < 403/1000` (`sec:exponent-four-thirds`). -/
theorem Lfun_fourThirds_lt : Lfun (4 / 3) (11 / 40) < 403 / 1000 := by
  have h : Lfun (4 / 3) (11 / 40) ≤ 4029 / 10000 :=
    Lfun_le fun q hq0 hq1 => fourThirdsBnd_all q hq0 hq1
  linarith

/-- `K_{4/3}(11/40) < 12/125` (`sec:exponent-four-thirds`): cubed,
`465746660343/527067520000000 < (12/125)³`. -/
theorem Kfun_fourThirds_lt : Kfun (4 / 3) (11 / 40) < 12 / 125 := by
  unfold Kfun
  rw [show (4 / 3 : ℝ) + 1 = 7 / 3 by norm_num, show (1 : ℝ) - 11 / 40 = 29 / 40 by norm_num]
  have hA : 0 ≤ (4 / 3 : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hB : 0 < (7 / 3 : ℝ) ^ (7 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hC : 0 ≤ (29 / 40 : ℝ) ^ (7 / 3 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hK : 0 ≤ (4 / 3 : ℝ) ^ (4 / 3 : ℝ) / (7 / 3 : ℝ) ^ (7 / 3 : ℝ)
      * (29 / 40 : ℝ) ^ (7 / 3 : ℝ) := mul_nonneg (div_nonneg hA hB.le) hC
  rw [← pow_lt_pow_iff_left₀ hK (by norm_num : (0 : ℝ) ≤ 12 / 125) (by norm_num : (3 : ℕ) ≠ 0),
    mul_pow, div_pow, rpow_cube_eq (by norm_num) (n := 4) (by norm_num),
    rpow_cube_eq (by norm_num) (n := 7) (by norm_num),
    rpow_cube_eq (by norm_num) (n := 7) (by norm_num)]
  norm_num

/-- `λ_{4/3} < 499/500 < 1` (`sec:exponent-four-thirds`). -/
theorem lambda_fourThirds_lt : lambda (4 / 3) < 499 / 500 := by
  have h := lambda_le (α := 4 / 3) (β := 11 / 40) (by norm_num) (by norm_num) (by norm_num)
  have h1 := Lfun_fourThirds_lt
  have h2 := Kfun_fourThirds_lt
  linarith

/-- The quadratic coefficient at `α = 4/3`, `u = 1/2`, `L_{4/3} = 2^{-4/3}`:
`C_{4/3}(1/2) = 272/9 - 2^{5/3}` (`sec:exponent-four-thirds`). -/
theorem Cfun_fourThirds_eq :
    Cfun (4 / 3) ((2 : ℝ) ^ (-(4 / 3 : ℝ))) (1 / 2) = 272 / 9 - (2 : ℝ) ^ ((5 : ℝ) / 3) := by
  unfold Cfun
  have e1 : ((1 : ℝ) - 1 / 2) ^ (-(4 / 3 : ℝ)) = (2 : ℝ) ^ (4 / 3 : ℝ) := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num),
      ← Real.rpow_neg (by norm_num), neg_neg]
  have e2 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) * (2 : ℝ) ^ (4 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have e3 : (2 : ℝ) ^ ((5 : ℝ) / 3) = 8 * (2 : ℝ) ^ (-(4 / 3 : ℝ)) := by
    rw [show (5 : ℝ) / 3 = ((3 : ℕ) : ℝ) + (-(4 / 3 : ℝ)) by push_cast; norm_num,
      Real.rpow_add (by norm_num), Real.rpow_natCast]
    norm_num
  have e4 : (4 : ℝ) * 2 ^ (-(4 / 3 : ℝ)) * (2 ^ (4 / 3 : ℝ) - 1)
      = 4 - 4 * 2 ^ (-(4 / 3 : ℝ)) := by
    rw [mul_sub, mul_assoc, e2]
    ring
  rw [e1, e3, e4]
  ring

/-- `C_{4/3}(1/2) < 28` (`sec:exponent-four-thirds`): `2^{5/3} > 20/9`, cubed. -/
theorem Cfun_fourThirds_lt : Cfun (4 / 3) ((2 : ℝ) ^ (-(4 / 3 : ℝ))) (1 / 2) < 28 := by
  rw [Cfun_fourThirds_eq]
  have h : (20 / 9 : ℝ) < (2 : ℝ) ^ ((5 : ℝ) / 3) := by
    have h0 : 0 ≤ (2 : ℝ) ^ ((5 : ℝ) / 3) := Real.rpow_nonneg (by norm_num) _
    rw [← pow_lt_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 20 / 9) h0 (by norm_num : (3 : ℕ) ≠ 0),
      rpow_cube_eq (by norm_num) (n := 5) (by norm_num)]
    norm_num
  linarith

/-- The rational four-law bound at `α = 4/3` (the displayed inequality at the end of
`sec:exponent-four-thirds`): `β = 11/40`, `u = 1/2`, `L = 403/1000`, `K = 12/125`,
`L_{4/3} = 2^{-4/3}`. -/
theorem fourLaw_fourThirds {X : Type} (ρ₁ ρ₂ τ₁ τ₂ : PMF X) (R : X → X → Prop)
    (hsymm : ∀ a b, R a b → R b a) (Mb z e : ℝ≥0∞)
    (h11 : PhiDres (4 / 3) ρ₁ τ₁ R ≤ Mb) (h12 : PhiDres (4 / 3) ρ₁ τ₂ R ≤ Mb)
    (h21 : PhiDres (4 / 3) ρ₂ τ₁ R ≤ Mb) (h22 : PhiDres (4 / 3) ρ₂ τ₂ R ≤ Mb)
    (hr11 : PhiDres (4 / 3) τ₁ ρ₁ R ≤ Mb) (hr12 : PhiDres (4 / 3) τ₂ ρ₁ R ≤ Mb)
    (hr21 : PhiDres (4 / 3) τ₁ ρ₂ R ≤ Mb) (hr22 : PhiDres (4 / 3) τ₂ ρ₂ R ≤ Mb)
    (hz11 : zMass ρ₁ τ₁ R ≤ z) (hz12 : zMass ρ₁ τ₂ R ≤ z)
    (hz21 : zMass ρ₂ τ₁ R ≤ z) (hz22 : zMass ρ₂ τ₂ R ≤ z)
    (hzr11 : zMass τ₁ ρ₁ R ≤ z) (hzr12 : zMass τ₂ ρ₁ R ≤ z)
    (hzr21 : zMass τ₁ ρ₂ R ≤ z) (hzr22 : zMass τ₂ ρ₂ R ≤ z)
    (he11 : wZeroD (4 / 3) ρ₁ τ₁ τ₂ R ≤ e) (he12 : wZeroD (4 / 3) ρ₁ τ₂ τ₁ R ≤ e)
    (he21 : wZeroD (4 / 3) ρ₂ τ₁ τ₂ R ≤ e) (he22 : wZeroD (4 / 3) ρ₂ τ₂ τ₁ R ≤ e) :
    PhiDres (4 / 3) (prodPMF ρ₁ ρ₂) (prodPMF τ₁ τ₂) (SquareRel R)
      ≤ ENNReal.ofReal (499 / 500) * Mb + 28 * Mb ^ 2
        + (ENNReal.ofReal (51 / 20) + ENNReal.ofReal (16 / 3) * Mb) * z
        + 4 * (1 + ENNReal.ofReal (4 / 3) * Mb) * e := by
  have hL : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand (4 / 3) (11 / 40) q ≤ 403 / 1000 :=
    fun q hq0 hq1 => (le_Lfun (by norm_num) (by norm_num) hq0 hq1).trans Lfun_fourThirds_lt.le
  have hK : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → (q - 11 / 40) * (1 - q) ^ (4 / 3 : ℝ) ≤ 12 / 125 :=
    fun q hq0 hq1 =>
      (Kfun_bound (by norm_num) (by norm_num) (by norm_num) hq0 hq1).trans Kfun_fourThirds_lt.le
  have hL0 : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand (4 / 3) 0 q ≤ (2 : ℝ) ^ (-(4 / 3 : ℝ)) :=
    fun q hq0 hq1 => (le_Lfun (by norm_num) le_rfl hq0 hq1).trans
      (Lfun_zero_eq_of_le_two (by norm_num) (by norm_num)).le
  have h := fourLaw_contraction (α := 4 / 3) (β := 11 / 40) (u := 1 / 2) (L := 403 / 1000)
    (K := 12 / 125) (L0 := (2 : ℝ) ^ (-(4 / 3 : ℝ))) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hL hK hL0 ρ₁ ρ₂ τ₁ τ₂ R hsymm Mb z e h11 h12 h21 h22 hr11 hr12
    hr21 hr22 hz11 hz12 hz21 hz22 hzr11 hzr12 hzr21 hzr22 he11 he12 he21 he22
  refine h.trans ?_
  have e1 : ENNReal.ofReal (2 * (403 / 1000 + 12 / 125)) = ENNReal.ofReal (499 / 500) := by
    norm_num
  have e2 : ENNReal.ofReal (2 + 2 * (11 / 40)) = ENNReal.ofReal (51 / 20) := by norm_num
  have e3 : (4 : ℝ≥0∞) * ENNReal.ofReal (4 / 3) = ENNReal.ofReal (16 / 3) := by
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have e4 : ENNReal.ofReal (Cfun (4 / 3) ((2 : ℝ) ^ (-(4 / 3 : ℝ))) (1 / 2)) ≤ 28 := by
    rw [show (28 : ℝ≥0∞) = ENNReal.ofReal 28 by simp]
    exact ENNReal.ofReal_le_ofReal Cfun_fourThirds_lt.le
  rw [e1, e2, e3]
  gcongr

/-! ### The exponent `2` (`sec:two-exponent-values`) -/

/-- `L_2(1/16) = 1/4` (`sec:two-exponent-values`): `1/4 - q/(1+q)² = (1-q)²/(4(1+q)²)
≥ (1-q)²/16`, with equality at `q = 1`. -/
theorem Lfun_two_sixteenth : Lfun 2 (1 / 16) = 1 / 4 := by
  apply le_antisymm
  · apply Lfun_le
    intro q hq0 hq1
    unfold Lsummand
    rw [Real.rpow_two, Real.rpow_two]
    have hq : 0 < (1 + q) ^ 2 := by positivity
    have key : q / (1 + q) ^ 2 ≤ 1 / 4 - 1 / 16 * (1 - q) ^ 2 := by
      rw [div_le_iff₀ hq]
      have h4 : (0 : ℝ) ≤ 4 - (1 + q) ^ 2 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg (1 - q)) h4]
    linarith
  · have h := le_Lfun (α := 2) (β := 1 / 16) (by norm_num) (by norm_num) zero_le_one le_rfl
    have e : Lsummand 2 (1 / 16) 1 = 1 / 4 := by
      unfold Lsummand
      rw [Real.rpow_two, Real.rpow_two]
      norm_num
    rwa [e] at h

/-- `K_2(1/16) = 125/1024` (`sec:two-exponent-values`). -/
theorem Kfun_two_sixteenth : Kfun 2 (1 / 16) = 125 / 1024 := by
  unfold Kfun
  rw [show (2 : ℝ) + 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast,
    Real.rpow_two]
  norm_num

/-- `L_2 = L_2(0) = 1/4` (`sec:two-exponent-values`). -/
theorem Lfun_two_zero : Lfun 2 0 = 1 / 4 := by
  rw [Lfun_zero_eq_of_le_two (by norm_num) le_rfl, Real.rpow_neg (by norm_num), Real.rpow_two]
  norm_num

/-- `C_2(1/2) = 38` at `L_2 = 1/4` (`sec:two-exponent-values`). -/
theorem Cfun_two : Cfun 2 (1 / 4) (1 / 2) = 38 := by
  unfold Cfun
  rw [Real.rpow_neg (by norm_num), Real.rpow_two]
  norm_num

/-- `λ_2 ≤ 381/512` (`sec:two-exponent-values`, the choice `β = 1/16`). -/
theorem lambda_two_le : lambda 2 ≤ 381 / 512 := by
  have h := lambda_le (α := 2) (β := 1 / 16) (by norm_num) (by norm_num) (by norm_num)
  rw [Lfun_two_sixteenth, Kfun_two_sixteenth] at h
  linarith

/-- `eq:mean-exponent-two`: the four-law bound at `α = 2`, `β = 1/16`, `u = 1/2`. -/
theorem fourLaw_two {X : Type} (ρ₁ ρ₂ τ₁ τ₂ : PMF X) (R : X → X → Prop)
    (hsymm : ∀ a b, R a b → R b a) (Mb z e : ℝ≥0∞)
    (h11 : PhiDres 2 ρ₁ τ₁ R ≤ Mb) (h12 : PhiDres 2 ρ₁ τ₂ R ≤ Mb)
    (h21 : PhiDres 2 ρ₂ τ₁ R ≤ Mb) (h22 : PhiDres 2 ρ₂ τ₂ R ≤ Mb)
    (hr11 : PhiDres 2 τ₁ ρ₁ R ≤ Mb) (hr12 : PhiDres 2 τ₂ ρ₁ R ≤ Mb)
    (hr21 : PhiDres 2 τ₁ ρ₂ R ≤ Mb) (hr22 : PhiDres 2 τ₂ ρ₂ R ≤ Mb)
    (hz11 : zMass ρ₁ τ₁ R ≤ z) (hz12 : zMass ρ₁ τ₂ R ≤ z)
    (hz21 : zMass ρ₂ τ₁ R ≤ z) (hz22 : zMass ρ₂ τ₂ R ≤ z)
    (hzr11 : zMass τ₁ ρ₁ R ≤ z) (hzr12 : zMass τ₂ ρ₁ R ≤ z)
    (hzr21 : zMass τ₁ ρ₂ R ≤ z) (hzr22 : zMass τ₂ ρ₂ R ≤ z)
    (he11 : wZeroD 2 ρ₁ τ₁ τ₂ R ≤ e) (he12 : wZeroD 2 ρ₁ τ₂ τ₁ R ≤ e)
    (he21 : wZeroD 2 ρ₂ τ₁ τ₂ R ≤ e) (he22 : wZeroD 2 ρ₂ τ₂ τ₁ R ≤ e) :
    PhiDres 2 (prodPMF ρ₁ ρ₂) (prodPMF τ₁ τ₂) (SquareRel R)
      ≤ ENNReal.ofReal (381 / 512) * Mb + 38 * Mb ^ 2
        + (ENNReal.ofReal (17 / 8) + 8 * Mb) * z + 4 * (1 + 2 * Mb) * e := by
  have hL : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand 2 (1 / 16) q ≤ 1 / 4 :=
    fun q hq0 hq1 => (le_Lfun (by norm_num) (by norm_num) hq0 hq1).trans Lfun_two_sixteenth.le
  have hK : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → (q - 1 / 16) * (1 - q) ^ (2 : ℝ) ≤ 125 / 1024 :=
    fun q hq0 hq1 =>
      (Kfun_bound (by norm_num) (by norm_num) (by norm_num) hq0 hq1).trans Kfun_two_sixteenth.le
  have hL0 : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand 2 0 q ≤ 1 / 4 :=
    fun q hq0 hq1 => (le_Lfun (by norm_num) le_rfl hq0 hq1).trans Lfun_two_zero.le
  have h := fourLaw_contraction (α := 2) (β := 1 / 16) (u := 1 / 2) (L := 1 / 4)
    (K := 125 / 1024) (L0 := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hL hK hL0 ρ₁ ρ₂ τ₁ τ₂ R hsymm Mb z e h11 h12 h21 h22 hr11 hr12
    hr21 hr22 hz11 hz12 hz21 hz22 hzr11 hzr12 hzr21 hzr22 he11 he12 he21 he22
  refine h.trans (le_of_eq ?_)
  have e1 : ENNReal.ofReal (2 * (1 / 4 + 125 / 1024)) = ENNReal.ofReal (381 / 512) := by
    norm_num
  have e2 : ENNReal.ofReal (2 + 2 * (1 / 16)) = ENNReal.ofReal (17 / 8) := by norm_num
  have e3 : (4 : ℝ≥0∞) * ENNReal.ofReal 2 = 8 := by
    rw [ENNReal.ofReal_ofNat]
    norm_num
  have e4 : ENNReal.ofReal (Cfun 2 (1 / 4) (1 / 2)) = 38 := by
    rw [Cfun_two, ENNReal.ofReal_ofNat]
  rw [e1, e2, e3, e4, ENNReal.ofReal_ofNat]

/-- The scalar criterion at `η ≤ 1/2500`, `K = 1024/131` (`sec:two-exponent-values`):
`1 + (1 + 3η)(aK + bK²η) ≤ K` with `a = 381/512`, `b = 38`. -/
theorem two_exponent_criterion {η : ℝ} (h0 : 0 ≤ η) (h : η ≤ 1 / 2500) :
    1 + (1 + 3 * η) * (381 / 512 * (1024 / 131) + 38 * (1024 / 131) ^ 2 * η) ≤ 1024 / 131 := by
  nlinarith [mul_le_mul_of_nonneg_left h h0]

/-- The two coefficients of the reduced criterion are below `2340` and `7000`
(`sec:two-exponent-values`). -/
theorem two_exponent_criterion_coeffs :
    (40145354 : ℝ) / 17161 < 2340 ∧ (119537664 : ℝ) / 17161 < 7000 := by
  constructor <;> norm_num

/-! ### The exponent range (`sec:exponent-range`) -/

/-- The modulus of continuity of `s^α` in the exponent: for `0 ≤ s ≤ 1` and `1 ≤ α ≤ α'`,
`0 ≤ s^α - s^{α'} ≤ α' - α` (`sec:exponent-range`), from `s^h ≥ 1 + h log s`,
`s^α ≤ s` and `-s log s ≤ 1 - s`. -/
lemma rpow_sub_rpow_exponent_le {s α α' : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hα : 1 ≤ α)
    (hαα' : α ≤ α') : 0 ≤ s ^ α - s ^ α' ∧ s ^ α - s ^ α' ≤ α' - α := by
  rcases eq_or_lt_of_le hs0 with hs | hs
  · rw [← hs, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
    constructor <;> linarith
  refine ⟨by linarith [Real.rpow_le_rpow_of_exponent_ge hs hs1 hαα'], ?_⟩
  have hh : 0 ≤ α' - α := by linarith
  have e1 : s ^ α' = s ^ α * s ^ (α' - α) := by
    rw [← Real.rpow_add hs]
    ring_nf
  have hB : 1 + Real.log s * (α' - α) ≤ s ^ (α' - α) := by
    have := Real.add_one_le_exp (Real.log s * (α' - α))
    rw [← Real.rpow_def_of_pos hs] at this
    linarith
  have hsα : s ^ α ≤ s := by
    have := Real.rpow_le_rpow_of_exponent_ge hs hs1 hα
    rwa [Real.rpow_one] at this
  have hsα0 : 0 ≤ s ^ α := Real.rpow_nonneg hs0 _
  have hneg : 0 ≤ -Real.log s := by linarith [Real.log_nonpos hs0 hs1]
  have hL : s * (-Real.log s) ≤ 1 - s := by
    have h1 : Real.log s⁻¹ ≤ s⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.2 hs)
    rw [Real.log_inv] at h1
    have h2 : s * (-Real.log s) ≤ s * (s⁻¹ - 1) := mul_le_mul_of_nonneg_left h1 hs0
    rw [mul_sub, mul_inv_cancel₀ hs.ne'] at h2
    linarith
  have hstep : s ^ α - s ^ α' = s ^ α * (1 - s ^ (α' - α)) := by
    rw [e1]
    ring
  rw [hstep]
  calc s ^ α * (1 - s ^ (α' - α)) ≤ s ^ α * ((α' - α) * (-Real.log s)) := by
        apply mul_le_mul_of_nonneg_left _ hsα0
        linarith
    _ ≤ s * ((α' - α) * (-Real.log s)) :=
        mul_le_mul_of_nonneg_right hsα (mul_nonneg hh hneg)
    _ = (α' - α) * (s * (-Real.log s)) := by ring
    _ ≤ (α' - α) * (1 - s) := mul_le_mul_of_nonneg_left hL hh
    _ ≤ α' - α := by nlinarith

/-- `L_{α'}(β) ≤ L_α(β) ≤ L_{α'}(β) + (1 + β)(α' - α)` for `1 ≤ α ≤ α'`
(`sec:exponent-range`: `L_α(β)` is nonincreasing and Lipschitz in the exponent). -/
lemma Lfun_exponent_bounds {α α' β : ℝ} (hα : 1 ≤ α) (hαα' : α ≤ α') (hβ0 : 0 ≤ β) :
    Lfun α' β ≤ Lfun α β ∧ Lfun α β ≤ Lfun α' β + (1 + β) * (α' - α) := by
  have hsummand : ∀ q, 0 ≤ q → q ≤ 1 → Lsummand α' β q ≤ Lsummand α β q
      ∧ Lsummand α β q ≤ Lsummand α' β q + (1 + β) * (α' - α) := by
    intro q hq0 hq1
    unfold Lsummand
    have e : ∀ γ : ℝ, q / (1 + q) ^ γ = q * ((1 + q)⁻¹) ^ γ := by
      intro γ
      rw [Real.inv_rpow (by linarith), div_eq_mul_inv]
    rw [e α, e α']
    have hs0 : 0 ≤ (1 + q)⁻¹ := by positivity
    have hs1 : (1 + q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    obtain ⟨h1, h2⟩ := rpow_sub_rpow_exponent_le hs0 hs1 hα hαα'
    obtain ⟨h3, h4⟩ :=
      rpow_sub_rpow_exponent_le (s := 1 - q) (by linarith) (by linarith) hα hαα'
    have hh : 0 ≤ α' - α := by linarith
    constructor
    · nlinarith [mul_nonneg hq0 h1, mul_nonneg hβ0 h3]
    · nlinarith [mul_le_mul_of_nonneg_left h2 hq0, mul_le_mul_of_nonneg_left h4 hβ0,
        mul_le_mul_of_nonneg_right hq1 hh]
  constructor
  · apply Lfun_le
    intro q hq0 hq1
    exact (hsummand q hq0 hq1).1.trans (le_Lfun (by linarith) hβ0 hq0 hq1)
  · apply Lfun_le
    intro q hq0 hq1
    have := le_Lfun (α := α') (by linarith) hβ0 hq0 hq1
    linarith [(hsummand q hq0 hq1).2]

/-- `K_α(β) = K_α(0) (1-β)^{α+1}`. -/
lemma Kfun_eq_mul (α β : ℝ) : Kfun α β = Kfun α 0 * (1 - β) ^ (α + 1) := by
  unfold Kfun
  simp

/-- `0 < K_α(0)` for `α ≥ 1`. -/
lemma Kfun_zero_pos {α : ℝ} (hα : 1 ≤ α) : 0 < Kfun α 0 := by
  unfold Kfun
  have h1 : 0 < α ^ α := Real.rpow_pos_of_pos (by linarith) _
  have h2 : 0 < (α + 1) ^ (α + 1) := Real.rpow_pos_of_pos (by linarith) _
  simp only [sub_zero, Real.one_rpow, mul_one]
  exact div_pos h1 h2

/-- `K_{α'}(0) ≤ K_α(0) ≤ K_{α'}(0) + (α' - α)` for `1 ≤ α ≤ α'` (`sec:exponent-range`),
through the maximum characterisation `K_α(0) = max_q q (1-q)^α`. -/
lemma Kfun_zero_exponent_bounds {α α' : ℝ} (hα : 1 ≤ α) (hαα' : α ≤ α') :
    Kfun α' 0 ≤ Kfun α 0 ∧ Kfun α 0 ≤ Kfun α' 0 + (α' - α) := by
  obtain ⟨q, hq0, hq1, hq⟩ := Kfun_attained (α := α') (by linarith) le_rfl zero_le_one
  obtain ⟨q', hq'0, hq'1, hq'⟩ := Kfun_attained (α := α) hα le_rfl zero_le_one
  rw [sub_zero] at hq hq'
  obtain ⟨h1, -⟩ :=
    rpow_sub_rpow_exponent_le (s := 1 - q) (by linarith) (by linarith) hα hαα'
  obtain ⟨-, h4⟩ :=
    rpow_sub_rpow_exponent_le (s := 1 - q') (by linarith) (by linarith) hα hαα'
  have hKq : q * (1 - q) ^ α ≤ Kfun α 0 := by
    have := Kfun_bound (β := 0) hα le_rfl zero_le_one hq0 hq1
    rwa [sub_zero] at this
  have hKq' : q' * (1 - q') ^ α' ≤ Kfun α' 0 := by
    have := Kfun_bound (α := α') (β := 0) (by linarith) le_rfl zero_le_one hq'0 hq'1
    rwa [sub_zero] at this
  constructor
  · rw [← hq]
    calc q * (1 - q) ^ α' ≤ q * (1 - q) ^ α := mul_le_mul_of_nonneg_left (by linarith) hq0
      _ ≤ Kfun α 0 := hKq
  · rw [← hq']
    have hh : 0 ≤ α' - α := by linarith
    calc q' * (1 - q') ^ α ≤ q' * ((1 - q') ^ α' + (α' - α)) :=
          mul_le_mul_of_nonneg_left (by linarith) hq'0
      _ = q' * (1 - q') ^ α' + q' * (α' - α) := by ring
      _ ≤ Kfun α' 0 + (α' - α) := by
          nlinarith [mul_le_mul_of_nonneg_right hq'1 hh]

/-- `K_α(0)` is strictly decreasing in `α ≥ 1` (`sec:exponent-range`). -/
lemma Kfun_zero_strictAnti {α α' : ℝ} (hα : 1 ≤ α) (hαα' : α < α') :
    Kfun α' 0 < Kfun α 0 := by
  obtain ⟨q, hq0, hq1, hq⟩ := Kfun_attained (α := α') (by linarith) le_rfl zero_le_one
  rw [sub_zero] at hq
  have hKα : 0 < Kfun α 0 := Kfun_zero_pos hα
  have hKq : q * (1 - q) ^ α ≤ Kfun α 0 := by
    have := Kfun_bound (β := 0) hα le_rfl zero_le_one hq0 hq1
    rwa [sub_zero] at this
  rw [← hq]
  rcases eq_or_lt_of_le hq0 with h0 | h0
  · rw [← h0, zero_mul]
    exact hKα
  rcases eq_or_lt_of_le hq1 with h1 | h1
  · rw [h1, sub_self, Real.zero_rpow (by linarith), mul_zero]
    exact hKα
  have hlt : (1 - q) ^ α' < (1 - q) ^ α :=
    Real.rpow_lt_rpow_of_exponent_gt (by linarith) (by linarith) hαα'
  calc q * (1 - q) ^ α' < q * (1 - q) ^ α := mul_lt_mul_of_pos_left hlt h0
    _ ≤ Kfun α 0 := hKq

/-- `K_{α'}(β) ≤ K_α(β) ≤ K_{α'}(β) + 2 (α' - α)` for `1 ≤ α ≤ α'` and `β ∈ [0,1]`
(`sec:exponent-range`). -/
lemma Kfun_exponent_bounds {α α' β : ℝ} (hα : 1 ≤ α) (hαα' : α ≤ α') (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) : Kfun α' β ≤ Kfun α β ∧ Kfun α β ≤ Kfun α' β + 2 * (α' - α) := by
  rw [Kfun_eq_mul α β, Kfun_eq_mul α' β]
  obtain ⟨h1, h2⟩ := Kfun_zero_exponent_bounds hα hαα'
  obtain ⟨h3, h4⟩ := rpow_sub_rpow_exponent_le (s := 1 - β) (by linarith) (by linarith)
    (by linarith : 1 ≤ α + 1) (by linarith : α + 1 ≤ α' + 1)
  have hp0 : 0 ≤ (1 - β) ^ (α + 1) := Real.rpow_nonneg (by linarith) _
  have hp1 : (1 - β) ^ (α + 1) ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (by linarith)
  have hK' : 0 ≤ Kfun α' 0 := (Kfun_zero_pos (by linarith)).le
  have hK'q : Kfun α' 0 ≤ 1 / 4 := Kfun_zero_le_quarter (by linarith)
  have hh : 0 ≤ α' - α := by linarith
  constructor
  · calc Kfun α' 0 * (1 - β) ^ (α' + 1) ≤ Kfun α' 0 * (1 - β) ^ (α + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hK'
      _ ≤ Kfun α 0 * (1 - β) ^ (α + 1) := mul_le_mul_of_nonneg_right h1 hp0
  · have hp : (1 - β) ^ (α + 1) ≤ (1 - β) ^ (α' + 1) + (α' - α) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hp0, mul_le_mul_of_nonneg_left hp hK',
      mul_le_mul_of_nonneg_right hp1 hh, mul_le_mul_of_nonneg_right hK'q hh]

/-- `λ_{α'} ≤ λ_α ≤ λ_{α'} + 8 (α' - α)` for `1 ≤ α ≤ α'` (`sec:exponent-range`). -/
lemma lambda_exponent_bounds {α α' : ℝ} (hα : 1 ≤ α) (hαα' : α ≤ α') :
    lambda α' ≤ lambda α ∧ lambda α ≤ lambda α' + 8 * (α' - α) := by
  obtain ⟨β, hβ0, hβ1, hlam, -⟩ := exists_beta_min hα
  obtain ⟨β', hβ'0, hβ'1, hlam', -⟩ := exists_beta_min (α := α') (by linarith)
  constructor
  · rw [hlam]
    have h := lambda_le (α := α') (β := β) (by linarith) hβ0 hβ1
    have h1 := (Lfun_exponent_bounds (β := β) hα hαα' hβ0).1
    have h2 := (Kfun_exponent_bounds (β := β) hα hαα' hβ0 hβ1).1
    linarith
  · rw [hlam']
    have h := lambda_le (α := α) (β := β') hα hβ'0 hβ'1
    have h1 := (Lfun_exponent_bounds (β := β') hα hαα' hβ'0).2
    have h2 := (Kfun_exponent_bounds (β := β') hα hαα' hβ'0 hβ'1).2
    have hh : 0 ≤ α' - α := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hβ'1 hh]

/-- `λ_α` is nonincreasing on `[1, ∞)` (`sec:exponent-range`). -/
theorem lambda_antitoneOn : AntitoneOn lambda (Set.Ici 1) :=
  fun _ hα _ _ hαα' => (lambda_exponent_bounds hα hαα').1

/-- `λ_α` is strictly decreasing on `[1, ∞)` (`sec:exponent-range`): the minimising `β` is
below `1`, where `K_α(β)` strictly decreases. -/
theorem lambda_strictAntiOn : StrictAntiOn lambda (Set.Ici 1) := by
  intro α hα α' hα' hαα'
  have hα1 : (1 : ℝ) ≤ α := hα
  have hα'1 : (1 : ℝ) ≤ α' := hα'
  obtain ⟨β, hβ0, hβ1, hlam, hmin⟩ := exists_beta_min (α := α) hα1
  have hβlt : β < 1 := by
    by_contra hcon
    have hβeq : β = 1 := le_antisymm hβ1 (not_lt.1 hcon)
    have h0 := hmin 0 le_rfl zero_le_one
    have hL0 : Lfun α 0 ≤ 1 / 2 + 0 := Lfun_le_half_add hα1 le_rfl
    have hK0 : Kfun α 0 ≤ 1 / 4 := Kfun_zero_le_quarter hα1
    have hL1 : 1 ≤ Lfun α 1 := beta_le_Lfun (by linarith) zero_le_one
    have hK1 : 0 ≤ Kfun α 1 := Kfun_nonneg (by linarith) le_rfl
    rw [hβeq] at h0
    linarith
  rw [hlam]
  have h := lambda_le (α := α') (β := β) hα'1 hβ0 hβ1
  have h1 := (Lfun_exponent_bounds (β := β) hα1 hαα'.le hβ0).1
  have h2 : Kfun α' β < Kfun α β := by
    rw [Kfun_eq_mul α β, Kfun_eq_mul α' β]
    have hp : 0 < (1 - β) ^ (α' + 1) := Real.rpow_pos_of_pos (by linarith) _
    have hp' : (1 - β) ^ (α' + 1) ≤ (1 - β) ^ (α + 1) :=
      Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (by linarith)
    have hK := Kfun_zero_strictAnti hα1 hαα'
    have hK0 : 0 < Kfun α 0 := Kfun_zero_pos hα1
    calc Kfun α' 0 * (1 - β) ^ (α' + 1) < Kfun α 0 * (1 - β) ^ (α' + 1) :=
          mul_lt_mul_of_pos_right hK hp
      _ ≤ Kfun α 0 * (1 - β) ^ (α + 1) := mul_le_mul_of_nonneg_left hp' hK0.le
  linarith

/-- `λ_α` is continuous on `[1, ∞)` (`sec:exponent-range`): it is `8`-Lipschitz there. -/
theorem lambda_continuousOn : ContinuousOn lambda (Set.Ici 1) := by
  have hL : LipschitzOnWith 8 lambda (Set.Ici 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq]
    have hx1 : (1 : ℝ) ≤ x := hx
    have hy1 : (1 : ℝ) ≤ y := hy
    rcases le_total x y with h | h
    · obtain ⟨h1, h2⟩ := lambda_exponent_bounds hx1 h
      rw [abs_sub_comm x y, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x), abs_le]
      push_cast
      constructor <;> linarith
    · obtain ⟨h1, h2⟩ := lambda_exponent_bounds hy1 h
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y), abs_le]
      push_cast
      constructor <;> linarith
  exact hL.continuousOn

/-- `1 < λ_1` (`sec:exponent-range`): `L_1(β) ≥ max (1/2, β)` and `K_1(β) = (1-β)²/4`. -/
theorem one_lt_lambda_one : 1 < lambda 1 := by
  obtain ⟨β, hβ0, hβ1, hlam, -⟩ := exists_beta_min (α := 1) le_rfl
  rw [hlam]
  have hK : Kfun 1 β = (1 - β) ^ 2 / 4 := by
    unfold Kfun
    rw [Real.rpow_one, show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two, Real.rpow_two]
    ring
  have h1 : (2 : ℝ) ^ (-(1 : ℝ)) ≤ Lfun 1 β := two_rpow_neg_le_Lfun zero_le_one hβ0
  rw [Real.rpow_neg (by norm_num), Real.rpow_one] at h1
  have h2 : β ≤ Lfun 1 β := beta_le_Lfun zero_le_one hβ0
  rw [hK]
  rcases le_or_gt β (1 / 2) with h | h
  · nlinarith [sq_nonneg (1 - β)]
  · nlinarith [sq_nonneg (1 - β)]

/-- `λ_2 < 1` (`sec:exponent-range`). -/
theorem lambda_two_lt_one : lambda 2 < 1 :=
  lambda_two_le.trans_lt (by norm_num)

/-- The threshold `α_*`: the unique exponent in `(1,2)` with `λ = 1`
(`sec:exponent-range`). -/
theorem exists_unique_threshold : ∃! α₀, 1 < α₀ ∧ α₀ < 2 ∧ lambda α₀ = 1 := by
  have hcont : ContinuousOn lambda (Set.Icc 1 2) :=
    lambda_continuousOn.mono Set.Icc_subset_Ici_self
  have hmem : (1 : ℝ) ∈ Set.Icc (lambda 2) (lambda 1) :=
    ⟨lambda_two_lt_one.le, one_lt_lambda_one.le⟩
  obtain ⟨α₀, ⟨h1, h2⟩, hα₀⟩ := intermediate_value_Icc' (by norm_num : (1 : ℝ) ≤ 2) hcont hmem
  have h1' : 1 < α₀ := by
    rcases eq_or_lt_of_le h1 with h | h
    · rw [← h] at hα₀
      linarith [one_lt_lambda_one]
    · exact h
  have h2' : α₀ < 2 := by
    rcases eq_or_lt_of_le h2 with h | h
    · rw [h] at hα₀
      linarith [lambda_two_lt_one]
    · exact h
  refine ⟨α₀, ⟨h1', h2', hα₀⟩, ?_⟩
  rintro α₁ ⟨g1, -, g3⟩
  exact lambda_strictAntiOn.injOn (Set.mem_Ici.2 g1.le) (Set.mem_Ici.2 h1'.le)
    (g3.trans hα₀.symm)

/-- The threshold exponent `α_*` (`sec:exponent-range`). -/
noncomputable def alphaStar : ℝ := Classical.choose exists_unique_threshold.exists

/-- `1 < α_* < 2` and `λ_{α_*} = 1`. -/
lemma alphaStar_spec : 1 < alphaStar ∧ alphaStar < 2 ∧ lambda alphaStar = 1 :=
  Classical.choose_spec exists_unique_threshold.exists

/-- `λ_α < 1` iff `α > α_*`, for `α ≥ 1` (`sec:exponent-range`). -/
theorem lambda_lt_one_iff {α : ℝ} (hα : 1 ≤ α) : lambda α < 1 ↔ alphaStar < α := by
  obtain ⟨hs1, -, hs⟩ := alphaStar_spec
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have := lambda_antitoneOn (Set.mem_Ici.2 hα) (Set.mem_Ici.2 hs1.le) hcon
    linarith
  · intro h
    have := lambda_strictAntiOn (Set.mem_Ici.2 hs1.le) (Set.mem_Ici.2 hα) h
    linarith

/-- `α_* < 4/3` (`sec:exponent-four-thirds`). -/
theorem alphaStar_lt_fourThirds : alphaStar < 4 / 3 :=
  (lambda_lt_one_iff (by norm_num)).1 (lambda_fourThirds_lt.trans (by norm_num))

/-! ### The algebraic minimum at exponent two (`sec:optimal-coefficient-two`) -/

/-- `K_2(β) = (4/27)(1-β)³`. -/
lemma Kfun_two_eq (β : ℝ) : Kfun 2 β = 4 / 27 * (1 - β) ^ 3 := by
  unfold Kfun
  rw [show (2 : ℝ) + 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast,
    Real.rpow_two]
  norm_num

/-- The summand of `L_2(β)` at `c - 1` dominates every summand when `2 β c³ = 1` and
`1 < c < 2` (`sec:optimal-coefficient-two`): the difference is
`(x-c)² ((2-x)(x+2c-2) + 2(2-c)) / (2 c³ x²)` at `x = 1 + q`. -/
lemma Lsummand_two_le_of_cube {β c q : ℝ} (hc1 : 1 < c) (hc2 : c < 2)
    (hβ : 2 * β * c ^ 3 = 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Lsummand 2 β q ≤ Lsummand 2 β (c - 1) := by
  unfold Lsummand
  rw [Real.rpow_two, Real.rpow_two, Real.rpow_two, Real.rpow_two]
  have hc0 : 0 < c := by linarith
  have hc3 : 0 < c ^ 3 := by positivity
  have hβeq : β = 1 / (2 * c ^ 3) := by
    field_simp
    linarith
  subst hβeq
  have hx : 0 < q + 1 := by linarith
  have key : (c - 1) / (1 + (c - 1)) ^ 2 + 1 / (2 * c ^ 3) * (1 - (c - 1)) ^ 2
      - (q / (1 + q) ^ 2 + 1 / (2 * c ^ 3) * (1 - q) ^ 2)
      = (q + 1 - c) ^ 2 * ((2 - (q + 1)) * ((q + 1) + 2 * c - 2) + 2 * (2 - c))
        / (2 * c ^ 3 * (q + 1) ^ 2) := by
    rw [show (1 : ℝ) + (c - 1) = c by ring, show (1 : ℝ) + q = q + 1 by ring]
    field_simp
    ring
  have hnum : 0 ≤ (q + 1 - c) ^ 2 * ((2 - (q + 1)) * ((q + 1) + 2 * c - 2) + 2 * (2 - c)) := by
    apply mul_nonneg (sq_nonneg _)
    have : 0 ≤ (2 - (q + 1)) * ((q + 1) + 2 * c - 2) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hden : 0 < 2 * c ^ 3 * (q + 1) ^ 2 := by positivity
  have := div_nonneg hnum hden.le
  linarith [key]

/-- `L_2(β) = Lsummand 2 β (c - 1)` when `2 β c³ = 1` and `1 < c < 2`
(`sec:optimal-coefficient-two`). -/
lemma Lfun_two_eq_of_cube {β c : ℝ} (hc1 : 1 < c) (hc2 : c < 2) (hβ : 2 * β * c ^ 3 = 1) :
    Lfun 2 β = Lsummand 2 β (c - 1) := by
  have hβ0 : 0 ≤ β := by
    have hc3 : 0 < c ^ 3 := by positivity
    have : β = 1 / (2 * c ^ 3) := by
      field_simp
      linarith
    rw [this]
    positivity
  apply le_antisymm
  · exact Lfun_le fun q hq0 hq1 => Lsummand_two_le_of_cube hc1 hc2 hβ hq0 hq1
  · exact le_Lfun (by norm_num) hβ0 (by linarith) (by linarith)

/-- The maximum defining `L_2(β)` for `1/16 < β < 1/2` is attained at `q = (2β)^{-1/3} - 1`
(`sec:optimal-coefficient-two`). -/
theorem Lfun_two_eq_of_beta {β : ℝ} (h1 : 1 / 16 < β) (h2 : β < 1 / 2) :
    Lfun 2 β = Lsummand 2 β ((2 * β) ^ (-(1 / 3 : ℝ)) - 1) := by
  have h2β0 : 0 < 2 * β := by linarith
  have h2β1 : 2 * β < 1 := by linarith
  have hc1 : 1 < (2 * β) ^ (-(1 / 3 : ℝ)) :=
    Real.one_lt_rpow_of_pos_of_lt_one_of_neg h2β0 h2β1 (by norm_num)
  have hc3 : ((2 * β) ^ (-(1 / 3 : ℝ))) ^ 3 = (2 * β)⁻¹ := by
    rw [show ((2 * β) ^ (-(1 / 3 : ℝ))) ^ 3 = ((2 * β) ^ (-(1 / 3 : ℝ))) ^ ((3 : ℕ) : ℝ) from
      (Real.rpow_natCast _ 3).symm, ← Real.rpow_mul h2β0.le,
      show -(1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = -1 by push_cast; norm_num, Real.rpow_neg_one]
  have hβ : 2 * β * ((2 * β) ^ (-(1 / 3 : ℝ))) ^ 3 = 1 := by
    rw [hc3]
    field_simp
  have hc2 : (2 * β) ^ (-(1 / 3 : ℝ)) < 2 := by
    have hc0 : 0 ≤ (2 * β) ^ (-(1 / 3 : ℝ)) := by linarith
    rw [← pow_lt_pow_iff_left₀ hc0 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0), hc3,
      inv_lt_comm₀ h2β0 (by norm_num)]
    norm_num
    linarith
  exact Lfun_two_eq_of_cube hc1 hc2 hβ

/-- The quartic `3q⁴ + 8q³ + 6q² - 2` is strictly increasing on `[0, ∞)`
(`sec:optimal-coefficient-two`). -/
lemma quartic_strictMonoOn :
    StrictMonoOn (fun q : ℝ => 3 * q ^ 4 + 8 * q ^ 3 + 6 * q ^ 2 - 2) (Set.Ici 0) := by
  intro x hx y _ hxy
  have hx0 : (0 : ℝ) ≤ x := hx
  have h2 : x ^ 2 < y ^ 2 := pow_lt_pow_left₀ hxy hx0 (by norm_num)
  have h3 : x ^ 3 < y ^ 3 := pow_lt_pow_left₀ hxy hx0 (by norm_num)
  have h4 : x ^ 4 < y ^ 4 := pow_lt_pow_left₀ hxy hx0 (by norm_num)
  linarith

/-- The quartic `eq:optimal-coefficient-two-quartic` has a unique root in `(1/3, 1/2)`. -/
theorem exists_root_quartic :
    ∃! q : ℝ, 1 / 3 < q ∧ q < 1 / 2 ∧ 3 * q ^ 4 + 8 * q ^ 3 + 6 * q ^ 2 - 2 = 0 := by
  have hcont : ContinuousOn (fun q : ℝ => 3 * q ^ 4 + 8 * q ^ 3 + 6 * q ^ 2 - 2)
      (Set.Icc (1 / 3) (1 / 2)) := by fun_prop
  have hmem : (0 : ℝ) ∈ Set.Ioo (3 * (1 / 3 : ℝ) ^ 4 + 8 * (1 / 3) ^ 3 + 6 * (1 / 3) ^ 2 - 2)
      (3 * (1 / 2 : ℝ) ^ 4 + 8 * (1 / 2) ^ 3 + 6 * (1 / 2) ^ 2 - 2) := by
    constructor <;> norm_num
  obtain ⟨q, ⟨hq1, hq2⟩, hq⟩ :=
    intermediate_value_Ioo (by norm_num : (1 / 3 : ℝ) ≤ 1 / 2) hcont hmem
  refine ⟨q, ⟨hq1, hq2, hq⟩, ?_⟩
  rintro q' ⟨hq'1, -, hq'⟩
  exact quartic_strictMonoOn.injOn (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith))
    (hq'.trans hq.symm)

/-- The minimiser of `L_2(β) + K_2(β)` (`sec:optimal-coefficient-two`): `β = (3q-1)/2` with `q`
the root of `3q⁴ + 8q³ + 6q² - 2` in `(1/3, 1/2)`. For every `β'`, the objective is at least
`Lsummand 2 β' q + K_2(β')`, whose excess over the value at `β` is
`(4/27) (β' - β)² (3 - 2β - β')`. -/
theorem lambda_two_eq_min : ∃ q, 1 / 3 < q ∧ q < 1 / 2
    ∧ 3 * q ^ 4 + 8 * q ^ 3 + 6 * q ^ 2 - 2 = 0
    ∧ lambda 2 = 2 * (Lfun 2 ((3 * q - 1) / 2) + Kfun 2 ((3 * q - 1) / 2)) := by
  obtain ⟨q, ⟨hq1, hq2, hq⟩, -⟩ := exists_root_quartic
  refine ⟨q, hq1, hq2, hq, ?_⟩
  have hβ₀0 : 0 ≤ (3 * q - 1) / 2 := by linarith
  have hβ₀1 : (3 * q - 1) / 2 ≤ 1 := by linarith
  have hcube : 2 * ((3 * q - 1) / 2) * (1 + q) ^ 3 = 1 := by linear_combination hq
  have hL : Lfun 2 ((3 * q - 1) / 2) = Lsummand 2 ((3 * q - 1) / 2) q := by
    have := Lfun_two_eq_of_cube (c := 1 + q) (by linarith) (by linarith) hcube
    rwa [add_sub_cancel_left] at this
  unfold lambda
  congr 1
  apply IsLeast.csInf_eq
  refine ⟨⟨(3 * q - 1) / 2, ⟨hβ₀0, hβ₀1⟩, rfl⟩, ?_⟩
  rintro _ ⟨β', ⟨hβ'0, hβ'1⟩, rfl⟩
  have hle : Lsummand 2 ((3 * q - 1) / 2) q + Kfun 2 ((3 * q - 1) / 2)
      ≤ Lsummand 2 β' q + Kfun 2 β' := by
    rw [Kfun_two_eq, Kfun_two_eq]
    unfold Lsummand
    rw [Real.rpow_two, Real.rpow_two]
    have e : (β' * (1 - q) ^ 2 + 4 / 27 * (1 - β') ^ 3)
        - ((3 * q - 1) / 2 * (1 - q) ^ 2 + 4 / 27 * (1 - (3 * q - 1) / 2) ^ 3)
        = 4 / 27 * ((1 - (3 * q - 1) / 2) - (1 - β')) ^ 2
          * (2 * (1 - (3 * q - 1) / 2) + (1 - β')) := by ring
    have : 0 ≤ 4 / 27 * ((1 - (3 * q - 1) / 2) - (1 - β')) ^ 2
        * (2 * (1 - (3 * q - 1) / 2) + (1 - β')) := by
      apply mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      linarith
    linarith
  show Lfun 2 ((3 * q - 1) / 2) + Kfun 2 ((3 * q - 1) / 2) ≤ Lfun 2 β' + Kfun 2 β'
  have hq' := le_Lfun (α := 2) (β := β') (q := q) (by norm_num) hβ'0 (by linarith) (by linarith)
  rw [hL]
  linarith

/-- `λ_2 = 8 q³` at the root `q` of the quartic (`sec:optimal-coefficient-two`): with
`(3q-1)(1+q)³ = 1`, the sum `2q/(1+q)² + (3q-1)(1-q)² + (1-q)³` collapses. -/
lemma lambda_two_eq_eight_cube {q : ℝ} (hq1 : 1 / 3 < q) (hq2 : q < 1 / 2)
    (hq : 3 * q ^ 4 + 8 * q ^ 3 + 6 * q ^ 2 - 2 = 0)
    (hlam : lambda 2 = 2 * (Lfun 2 ((3 * q - 1) / 2) + Kfun 2 ((3 * q - 1) / 2))) :
    lambda 2 = 8 * q ^ 3 := by
  rw [hlam, Kfun_two_eq]
  have hcube : 2 * ((3 * q - 1) / 2) * (1 + q) ^ 3 = 1 := by linear_combination hq
  rw [Lfun_two_eq_of_cube (c := 1 + q) (by linarith) (by linarith) hcube, add_sub_cancel_left]
  unfold Lsummand
  rw [Real.rpow_two, Real.rpow_two]
  have hx : (1 + q) ^ 2 ≠ 0 := by positivity
  have e : q / (1 + q) ^ 2 = q * (3 * q - 1) * (1 + q) := by
    rw [div_eq_iff hx]
    linear_combination (-q) * hq
  rw [e]
  ring

/-- The rational bracket `0.7003 < λ_2 < 0.7004` (`sec:optimal-coefficient-two`), from
`λ_2 = 8 q³` and `44403/100000 < q < 444036/1000000`. -/
theorem lambda_two_bounds : (0.7003 : ℝ) < lambda 2 ∧ lambda 2 < 0.7004 := by
  obtain ⟨q, hq1, hq2, hq, hlam⟩ := lambda_two_eq_min
  rw [lambda_two_eq_eight_cube hq1 hq2 hq hlam]
  have hlo : 44403 / 100000 < q := by
    by_contra h
    push Not at h
    have hm := quartic_strictMonoOn.monotoneOn (Set.mem_Ici.2 (by linarith))
      (Set.mem_Ici.2 (by norm_num)) h
    have hv : (3 : ℝ) * (44403 / 100000) ^ 4 + 8 * (44403 / 100000) ^ 3
        + 6 * (44403 / 100000) ^ 2 - 2 < 0 := by norm_num
    linarith
  have hhi : q < 444036 / 1000000 := by
    by_contra h
    push Not at h
    have hm := quartic_strictMonoOn.monotoneOn (Set.mem_Ici.2 (by norm_num))
      (Set.mem_Ici.2 (by linarith)) h
    have hv : (0 : ℝ) < 3 * (444036 / 1000000) ^ 4 + 8 * (444036 / 1000000) ^ 3
        + 6 * (444036 / 1000000) ^ 2 - 2 := by norm_num
    linarith
  constructor
  · have := pow_lt_pow_left₀ hlo (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at this ⊢
    linarith
  · have := pow_lt_pow_left₀ hhi (by linarith) (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at this ⊢
    linarith

end GraphMarkovMatching.Stopped
