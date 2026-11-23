/-
論文1105『4 次元球面の 16π² は Q と W で分け合い、いちばん歪んだ皮一枚が W の取り分の床を決める』の
格上げ（芯だけ）。

日本語の一文：W^± の密度を皮の比 v の道で書いた式を入力に置くと、どの皮 t₀ で切っても、W の取り分 f は
(1 − v(t₀)²)² + 2v̇(t₀)² 以上で、f < 1/2 ならすべての皮の比は √2·sin(π/8) と √2·cos(π/8) のあいだにある。
English: Core only: taking as input the densities d± = (E ∓ G)²/(6v), E = v̈ + v³ − v, G = 3vv̇, of
∫‖W^±‖² for the SU(2)×U(1)-invariant metrics on S⁴ written along the path v(t), the difference
d₊ − d₋ is the derivative of U = −v̇² + v² − v⁴/2; hence for every t₀, f = ∫(d₊ + d₋) ≥
(1 − v(t₀)²)² + 2v̇(t₀)², and f < 1/2 forces √2 sin(π/8) < v < √2 cos(π/8) on every shell;
W ≡ 0 only for v ≡ 1.

原稿（1105_yamagishi_the_most_squashed_shell_sets_the_floor_of_w_on_the_four_sphere/…_jp.tex）は、
W^± の固有値を記号計算で出し、第 6 節で、差が全微分 U̇ になることと、任意の皮で切って左右を押さえる
ことから床の不等式を式で導いている。乱数の道 1925 本と等号の道で数値も確かめている。

ここで証明した言明（v, v̇, v̈ を道の関数として、v > 0）：
  (1) `hasDerivAt_U`：d₊ − d₋ = dU/dt（U = −v̇² + v² − v⁴/2）。
  (2) `floor`：d₊ と d₋ が実数の直線の上で積分でき、t → ±∞ で v → 1、v̇ → 0 なら、どの t₀ でも
      ∫(d₊ + d₋) ≥ (1 − v(t₀)²)² + 2v̇(t₀)²。
  (3) `wall`：∫(d₊ + d₋) < 1/2 なら、すべての t で √2·sin(π/8) < v(t) < √2·cos(π/8)。
      `below_one`：∫(d₊ + d₋) < 1 なら、すべての t で v(t) < √2。
  (4) `W_zero_iff_round`：すべての t で E = G = 0 ⇔ v ≡ 1（W が消えるのは皮がすべて丸いとき）。
足した仮定（ここが「芯だけ」の理由）：計量 g = a²(dt² + σ₁² + σ₂² + v²σ₃²) の W^± の固有値が
(E ∓ G)/(6a²v) の形であること（カルタンの計算）と体積の形から、f = ∫(d₊ + d₋) dt になることを、定義として
置いた。曲率の計算そのもの、両端が点でなめらかに閉じる条件（ここでは v → 1、v̇ → 0 だけを使う）、
積分できることは仮定である。原稿は f を 16π² で割った取り分と書いている。
形式化していないもの：等号の道（ペダーセンの計量の背中合わせ）、APS の η との関係、族の外への拡張、
第 8 節のバッハ平坦の主張、数値の確かめ。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1105

open Real Set MeasureTheory Filter Topology

variable (v v1 v2 : ℝ → ℝ)

/-- E = v̈ + v³ − v。 -/
def E (t : ℝ) : ℝ := v2 t + v t ^ 3 - v t

/-- G = 3vv̇。 -/
def G (t : ℝ) : ℝ := 3 * v t * v1 t

/-- W⁺ の密度 d₊ = (E − G)²/(6v)。 -/
noncomputable def dplus (t : ℝ) : ℝ := (E v v2 t - G v v1 t) ^ 2 / (6 * v t)

/-- W⁻ の密度 d₋ = (E + G)²/(6v)。 -/
noncomputable def dminus (t : ℝ) : ℝ := (E v v2 t + G v v1 t) ^ 2 / (6 * v t)

/-- U = −v̇² + v² − v⁴/2。 -/
noncomputable def U (t : ℝ) : ℝ := -(v1 t) ^ 2 + v t ^ 2 - v t ^ 4 / 2

variable {v v1 v2}

/-- (1) d₊ − d₋ = dU/dt。 -/
theorem hasDerivAt_U (hv : ∀ t, HasDerivAt v (v1 t) t) (hv1 : ∀ t, HasDerivAt v1 (v2 t) t)
    (hpos : ∀ t, 0 < v t) (t : ℝ) :
    HasDerivAt (U v v1) (dplus v v1 v2 t - dminus v v1 v2 t) t := by
  have h := ((((hv1 t).pow 2).neg).add ((hv t).pow 2)).sub (((hv t).pow 4).div_const 2)
  unfold U
  refine h.congr_deriv ?_
  unfold dplus dminus E G
  have := (hpos t).ne'
  field_simp
  ring

theorem dplus_nonneg (hpos : ∀ t, 0 < v t) (t : ℝ) : 0 ≤ dplus v v1 v2 t := by
  unfold dplus; have := hpos t; positivity

theorem dminus_nonneg (hpos : ∀ t, 0 < v t) (t : ℝ) : 0 ≤ dminus v v1 v2 t := by
  unfold dminus; have := hpos t; positivity

/-- 端で v → 1、v̇ → 0 なら U → 1/2。 -/
theorem U_tendsto {l : Filter ℝ} (h1 : Tendsto v l (𝓝 1)) (h2 : Tendsto v1 l (𝓝 0)) :
    Tendsto (U v v1) l (𝓝 (1 / 2)) := by
  have := (((h2.pow 2).neg).add (h1.pow 2)).sub ((h1.pow 4).div_const 2)
  unfold U
  convert this using 2
  norm_num

/-- (2) どの皮 t₀ で切っても、W の取り分は (1 − v(t₀)²)² + 2v̇(t₀)² 以上。 -/
theorem floor (hv : ∀ t, HasDerivAt v (v1 t) t) (hv1 : ∀ t, HasDerivAt v1 (v2 t) t)
    (hpos : ∀ t, 0 < v t) (hip : Integrable (dplus v v1 v2)) (him : Integrable (dminus v v1 v2))
    (hbot1 : Tendsto v atBot (𝓝 1)) (hbot2 : Tendsto v1 atBot (𝓝 0))
    (htop1 : Tendsto v atTop (𝓝 1)) (htop2 : Tendsto v1 atTop (𝓝 0)) (t₀ : ℝ) :
    (1 - v t₀ ^ 2) ^ 2 + 2 * v1 t₀ ^ 2 ≤ ∫ t, (dplus v v1 v2 t + dminus v v1 v2 t) := by
  have hd := hasDerivAt_U hv hv1 hpos
  have hint : Integrable (fun t => dplus v v1 v2 t - dminus v v1 v2 t) := hip.sub him
  have hsum : Integrable (fun t => dplus v v1 v2 t + dminus v v1 v2 t) := hip.add him
  -- 左と右の部分の差
  have hleft : ∫ t in Iic t₀, (dplus v v1 v2 t - dminus v v1 v2 t) = U v v1 t₀ - 1 / 2 :=
    integral_Iic_of_hasDerivAt_of_tendsto' (fun t _ => hd t) hint.integrableOn
      (U_tendsto hbot1 hbot2)
  have hright : ∫ t in Ioi t₀, (dplus v v1 v2 t - dminus v v1 v2 t) = 1 / 2 - U v v1 t₀ :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hd t) hint.integrableOn
      (U_tendsto htop1 htop2)
  -- 左：d₊ + d₋ ≥ −(d₊ − d₋)
  have hL : 1 / 2 - U v v1 t₀ ≤ ∫ t in Iic t₀, (dplus v v1 v2 t + dminus v v1 v2 t) := by
    have : ∫ t in Iic t₀, -(dplus v v1 v2 t - dminus v v1 v2 t) = 1 / 2 - U v v1 t₀ := by
      rw [integral_neg, hleft]; ring
    rw [← this]
    apply setIntegral_mono_on hint.neg.integrableOn hsum.integrableOn measurableSet_Iic
    intro t _
    have := dplus_nonneg (v1 := v1) (v2 := v2) hpos t
    simp only [Pi.neg_apply]
    linarith
  have hR : 1 / 2 - U v v1 t₀ ≤ ∫ t in Ioi t₀, (dplus v v1 v2 t + dminus v v1 v2 t) := by
    rw [← hright]
    apply setIntegral_mono_on hint.integrableOn hsum.integrableOn measurableSet_Ioi
    intro t _
    have := dminus_nonneg (v1 := v1) (v2 := v2) hpos t
    linarith
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := t₀) hsum.integrableOn hsum.integrableOn]
  have e : (1 - v t₀ ^ 2) ^ 2 + 2 * v1 t₀ ^ 2 = 2 * (1 / 2 - U v v1 t₀) := by unfold U; ring
  rw [e]
  linarith

/-- (3) f < 1/2 なら、すべての皮の比は √2·sin(π/8) と √2·cos(π/8) のあいだ。 -/
theorem wall (hv : ∀ t, HasDerivAt v (v1 t) t) (hv1 : ∀ t, HasDerivAt v1 (v2 t) t)
    (hpos : ∀ t, 0 < v t) (hip : Integrable (dplus v v1 v2)) (him : Integrable (dminus v v1 v2))
    (hbot1 : Tendsto v atBot (𝓝 1)) (hbot2 : Tendsto v1 atBot (𝓝 0))
    (htop1 : Tendsto v atTop (𝓝 1)) (htop2 : Tendsto v1 atTop (𝓝 0))
    (hf : ∫ t, (dplus v v1 v2 t + dminus v v1 v2 t) < 1 / 2) (t : ℝ) :
    √2 * sin (π / 8) < v t ∧ v t < √2 * cos (π / 8) := by
  have hfl := floor hv hv1 hpos hip him hbot1 hbot2 htop1 htop2 t
  have hsq : (1 - v t ^ 2) ^ 2 < 1 / 2 := by nlinarith [sq_nonneg (v1 t)]
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have hs2 : 0 < √2 := by positivity
  -- (√2 sin(π/8))² = 1 − 1/√2、(√2 cos(π/8))² = 1 + 1/√2
  have hc4 : cos (π / 4) = √2 / 2 := cos_pi_div_four
  have hsin2 : (√2 * sin (π / 8)) ^ 2 = 1 - √2 / 2 := by
    rw [mul_pow, h2, sin_sq, cos_sq, show 2 * (π / 8) = π / 4 by ring, hc4]; ring
  have hcos2 : (√2 * cos (π / 8)) ^ 2 = 1 + √2 / 2 := by
    rw [mul_pow, h2, cos_sq, show 2 * (π / 8) = π / 4 by ring, hc4]; ring
  have hsinpos : 0 < sin (π / 8) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hcospos : 0 < cos (π / 8) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  -- |1 − v²| < √2/2
  have habs : |1 - v t ^ 2| < √2 / 2 := by
    have : (√2 / 2) ^ 2 = 1 / 2 := by rw [div_pow, h2]; norm_num
    exact abs_lt_of_sq_lt_sq' (by rw [this]; exact hsq) (by positivity) |> fun h => abs_lt.mpr h
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  have hvp := hpos t
  constructor
  · have : (√2 * sin (π / 8)) ^ 2 < v t ^ 2 := by rw [hsin2]; linarith
    exact (pow_lt_pow_iff_left₀ (by positivity) hvp.le two_ne_zero).mp this
  · have : v t ^ 2 < (√2 * cos (π / 8)) ^ 2 := by rw [hcos2]; linarith
    exact (pow_lt_pow_iff_left₀ hvp.le (by positivity) two_ne_zero).mp this

/-- (3) f < 1 なら、すべての皮で v < √2。 -/
theorem below_one (hv : ∀ t, HasDerivAt v (v1 t) t) (hv1 : ∀ t, HasDerivAt v1 (v2 t) t)
    (hpos : ∀ t, 0 < v t) (hip : Integrable (dplus v v1 v2)) (him : Integrable (dminus v v1 v2))
    (hbot1 : Tendsto v atBot (𝓝 1)) (hbot2 : Tendsto v1 atBot (𝓝 0))
    (htop1 : Tendsto v atTop (𝓝 1)) (htop2 : Tendsto v1 atTop (𝓝 0))
    (hf : ∫ t, (dplus v v1 v2 t + dminus v v1 v2 t) < 1) (t : ℝ) : v t < √2 := by
  have hfl := floor hv hv1 hpos hip him hbot1 hbot2 htop1 htop2 t
  have hsq : (1 - v t ^ 2) ^ 2 < 1 := by nlinarith [sq_nonneg (v1 t)]
  have : v t ^ 2 < 2 := by nlinarith
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  exact (pow_lt_pow_iff_left₀ (hpos t).le (by positivity) two_ne_zero).mp (by rw [h2]; exact this)

/-- (4) すべての t で E = G = 0 ⇔ v ≡ 1。 -/
theorem W_zero_iff_round (hv : ∀ t, HasDerivAt v (v1 t) t) (hv1 : ∀ t, HasDerivAt v1 (v2 t) t)
    (hpos : ∀ t, 0 < v t) :
    (∀ t, E v v2 t = 0 ∧ G v v1 t = 0) ↔ ∀ t, v t = 1 := by
  constructor
  · intro h
    have hz : ∀ t, v1 t = 0 := by
      intro t
      have := (h t).2
      unfold G at this
      have hp := (hpos t).ne'
      rcases mul_eq_zero.mp this with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · norm_num at h''
        · exact absurd h'' hp
      · exact h'
    have hz2 : ∀ t, v2 t = 0 := by
      intro t
      have h0 : HasDerivAt v1 0 t := by
        have : v1 = fun _ => 0 := funext hz
        rw [this]; exact hasDerivAt_const t 0
      exact (hv1 t).unique h0
    intro t
    have := (h t).1
    unfold E at this
    rw [hz2 t, zero_add] at this
    have hp := hpos t
    have : v t * (v t - 1) * (v t + 1) = 0 := by linear_combination this
    rcases mul_eq_zero.mp this with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · linarith
      · linarith
    · linarith
  · intro h t
    have hz : ∀ t, v1 t = 0 := by
      intro t
      have h0 : HasDerivAt v 0 t := by
        have : v = fun _ => 1 := funext h
        rw [this]; exact hasDerivAt_const t 1
      exact (hv t).unique h0
    have hz2 : v2 t = 0 := by
      have h0 : HasDerivAt v1 0 t := by
        have : v1 = fun _ => 0 := funext hz
        rw [this]; exact hasDerivAt_const t 0
      exact (hv1 t).unique h0
    unfold E G
    rw [h t, hz t, hz2]
    norm_num

end Paper1105

end Yamagishi
