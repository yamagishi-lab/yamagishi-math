/-
論文02『4π 質量相殺定理』の芯を、機械に確かめさせる。

原稿（02_mass_cancellation_4pi/mass_cancellation_4pi_master_jp.tex）の
  定理1：3 次元の単位球 Ω = {x ∈ ℝ³ | |x| ≤ 1} で、密度 ρ = r^(−2) の総質量は 4π
  第5節：一般の n < 3 で m(n) = ∫_Ω r^(−n) dV = 4π/(3 − n)
  結論2：n = 2 は m が 4π（S = 1）になる唯一の指数
を、ℝ³（Mathlib の EuclideanSpace ℝ (Fin 3)）の上のルベーグ積分として書く。
球座標への置き換えは手で書かず、Mathlib の定理
  `MeasureTheory.integral_fun_norm_addHaar`（球対称な関数の積分 = 次元 × 単位球の体積 × 動径の積分）
と、単位球の体積 4π/3（`EuclideanSpace.volume_ball_fin_three`）を使った。

形式化したのは積分の値だけである。「4π は全立体角」「Zero-Tension」「4π の重なり枚数 S」という
読みは形式化していない。原点 x = 0 では Lean の約束で 0^(−n) = 0 だが、一点は体積 0 なので値に響かない。
原稿の定理1は特定の一つの定積分で、一般の n の式は第5節の計算として書かれている（定理の形には
なっていない）。ここでは両方を定理として書いた。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

open Real MeasureTheory Metric Set

/-- ℝ³（ユークリッドの距離をもつ 3 次元空間）。 -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- 動径の積分：n < 3 なら ∫₀¹ r² · r^(−n) dr = 1/(3 − n)。 -/
theorem radial_integral (n : ℝ) (hn : n < 3) :
    ∫ y in Ioi (0 : ℝ), y ^ (2 : ℕ) • (Iic (1 : ℝ)).indicator (fun r => r ^ (-n)) y
      = 1 / (3 - n) := by
  have h1 : (fun y : ℝ => y ^ (2 : ℕ) • (Iic (1 : ℝ)).indicator (fun r => r ^ (-n)) y)
      = (Iic (1 : ℝ)).indicator (fun y => y ^ (2 : ℕ) * y ^ (-n)) := by
    ext y
    by_cases hy : y ∈ Iic (1 : ℝ) <;> simp [hy, smul_eq_mul]
  rw [h1, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
    ← intervalIntegral.integral_of_le zero_le_one]
  have h2 : ∫ y in (0 : ℝ)..1, y ^ (2 : ℕ) * y ^ (-n) = ∫ y in (0 : ℝ)..1, y ^ (2 - n) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with y hy
    rw [uIoc_of_le zero_le_one] at hy
    rw [← Real.rpow_natCast, ← Real.rpow_add hy.1]
    norm_num [sub_eq_add_neg]
  rw [h2, integral_rpow (Or.inl (by linarith))]
  have h3 : (2 - n + 1) = 3 - n := by ring
  rw [h3, Real.one_rpow, Real.zero_rpow (by linarith)]
  ring

/-- 単位球の体積（実数として）は 4π/3。 -/
theorem volume_real_ball_R3 : (volume : Measure R3).real (ball 0 1) = 4 * π / 3 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal (by positivity)]
  ring

/-- 第5節の一般の式：n < 3 のとき、単位球の中の r^(−n) の積分は 4π/(3 − n)。 -/
theorem mass_general (n : ℝ) (hn : n < 3) :
    ∫ x in closedBall (0 : R3) 1, ‖x‖ ^ (-n) = 4 * π / (3 - n) := by
  rw [← integral_indicator measurableSet_closedBall]
  have h : (closedBall (0 : R3) 1).indicator (fun x => ‖x‖ ^ (-n))
      = fun x => (Iic (1 : ℝ)).indicator (fun r => r ^ (-n)) ‖x‖ := by
    ext x
    by_cases hx : ‖x‖ ≤ 1
    · simp [indicator, hx]
    · simp [indicator, hx]
  rw [h, integral_fun_norm_addHaar volume (fun r => (Iic (1 : ℝ)).indicator (fun r => r ^ (-n)) r)]
  rw [finrank_euclideanSpace_fin, volume_real_ball_R3]
  have h3 : (3 : ℕ) - 1 = 2 := rfl
  rw [h3, radial_integral n hn, nsmul_eq_mul, smul_eq_mul]
  have : (3 - n) ≠ 0 := by linarith
  field_simp
  push_cast
  ring

/-- 定理1（4π 質量相殺定理）：密度 r^(−2) の単位球の総質量は 4π。 -/
theorem mass_cancellation_4pi :
    ∫ x in closedBall (0 : R3) 1, ‖x‖ ^ (-2 : ℝ) = 4 * π := by
  rw [mass_general 2 (by norm_num)]
  norm_num

/-- 定理1を、密度を 1/r² と書いた形で。 -/
theorem mass_cancellation_4pi' :
    ∫ x in closedBall (0 : R3) 1, 1 / ‖x‖ ^ 2 = 4 * π := by
  rw [← mass_cancellation_4pi]
  apply setIntegral_congr_fun measurableSet_closedBall
  intro x _
  simp only
  rw [Real.rpow_neg (norm_nonneg x), one_div]
  norm_num

/-- 値が 0 でないので、密度 r^(−2) は単位球の上で本当に積分できる（値 4π は「積分できない
ときの約束の 0」ではない）。 -/
theorem integrableOn_inv_sq :
    IntegrableOn (fun x : R3 => ‖x‖ ^ (-2 : ℝ)) (closedBall (0 : R3) 1) := by
  apply Integrable.of_integral_ne_zero
  rw [mass_cancellation_4pi]
  positivity

/-- 結論2：n < 3 の範囲で、m(n) = 4π（重なり枚数 S = 1）になるのは n = 2 だけ。 -/
theorem mass_eq_4pi_iff (n : ℝ) (hn : n < 3) :
    ∫ x in closedBall (0 : R3) 1, ‖x‖ ^ (-n) = 4 * π ↔ n = 2 := by
  rw [mass_general n hn]
  have hpi : (4 * π : ℝ) ≠ 0 := by positivity
  have h3 : (3 - n) ≠ 0 := by linarith
  constructor
  · intro h
    rw [div_eq_iff h3] at h
    have : 4 * π * (1 - (3 - n)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hpi
    · linarith
  · rintro rfl; norm_num

/-- 第5節の表の段：m(n) が 2^k π になる n は n = 3 − 2^(2−k)（原稿の囲みの式）。
k は整数。たとえば k = 1, 2, 3, 4 で n = 1, 2, 5/2, 11/4。 -/
theorem mass_eq_two_pow_pi (k : ℤ) :
    ∫ x in closedBall (0 : R3) 1, ‖x‖ ^ (-(3 - (2 : ℝ) ^ (2 - k))) = (2 : ℝ) ^ k * π := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 - k) := by positivity
  rw [mass_general _ (by linarith)]
  have h : (3 - (3 - (2 : ℝ) ^ (2 - k))) = (2 : ℝ) ^ (2 - k) := by ring
  rw [h, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp
  norm_num

end Yamagishi
