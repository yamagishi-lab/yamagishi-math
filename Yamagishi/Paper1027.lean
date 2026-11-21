/-
論文1027『回る円板の空間の曲率は −3Ω²/c² で、速度空間の曲率とは別物である』の格上げ（一般の形）。

原稿（1027_yamagishi_rotating_disk_spatial_curvature_minus_3_omega2_over_c2_differs_from_
velocity_space/…_jp.tex）は、回転系の空間の計量 dl² = dr² + r²dφ²/(1 − Ω²r²/c²) のガウス曲率を記号計算で
−3Ω²c²/(c² − Ω²r²)² と出し、六点の数値微分（β = 0.1・0.5）と比べ、周と面積を三つの β の数値積分で
確かめている。

ここで証明した言明（k = Ω²/c² > 0、0 < r < 1/√k、縁の速さ β = ΩR/c、0 < β < 1）：
  計量 dr² + f(r)²dφ²、f(r) = r(1 − kr²)^(−1/2) と置く。
  (1) `curvature_eq`：K(r) = −f″(r)/f(r) = −3k/(1 − kr²)²（Ω, c で書けば `curvature_eq_omega`：
      −3Ω²c²/(c² − Ω²r²)²）。つねに負で、式の r = 0 での値は −3k = −3Ω²/c²。
  (2) `area_eq`：半径 R の円板の面積 ∫₀^R 2πf(r)dr = (2π/k)(1 − √(1 − kR²))。
      `area_ratio`：面積 ÷ πR² = 2/(1 + √(1 − β²))、`circ_ratio`：周 ÷ 直径 = π/√(1 − β²) = πγ。
  (3) `ratio_bounds`：1 < 2/(1 + √(1 − β²)) < 1/√(1 − β²) = γ。
定義に置いたもの：dr² + G dφ² 型の計量のガウス曲率の式 K = −(√G)″/√G（微分幾何の標準の式で、
ここでは定義として置いた。Mathlib に曲面の曲率の一般の理論は無い）と、回転系の空間の計量そのもの
（ランダウとリフシッツの式。原稿も既知と書いている）。曲がっているのは回転系の空間で、時空は平坦で
ある（物理の読みは形式化の外）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1027

open Real Set intervalIntegral

/-- 周の向きの長さの係数 f(r) = r(1 − kr²)^(−1/2)。 -/
noncomputable def f (k r : ℝ) : ℝ := r * (1 - k * r ^ 2) ^ (-(1 / 2 : ℝ))

/-- 計量 dr² + f²dφ² のガウス曲率 −f″/f（定義として置く）。 -/
noncomputable def K (k r : ℝ) : ℝ := -(deriv (deriv (f k)) r) / f k r

section

variable {k : ℝ}

theorem hasDerivAt_u (r : ℝ) : HasDerivAt (fun r => 1 - k * r ^ 2) (-(2 * k * r)) r := by
  have := ((hasDerivAt_pow 2 r).const_mul k).const_sub 1
  convert this using 1; push_cast; ring

theorem hasDerivAt_upow {r : ℝ} (hu : 0 < 1 - k * r ^ 2) (p : ℝ) :
    HasDerivAt (fun r => (1 - k * r ^ 2) ^ p) (-(2 * k * r) * p * (1 - k * r ^ 2) ^ (p - 1)) r :=
  (hasDerivAt_u r).rpow_const (Or.inl hu.ne')

/-- f′(r) = (1 − kr²)^(−3/2)。 -/
theorem hasDerivAt_f {r : ℝ} (hu : 0 < 1 - k * r ^ 2) :
    HasDerivAt (f k) ((1 - k * r ^ 2) ^ (-(3 / 2 : ℝ))) r := by
  have h := (hasDerivAt_id r).mul (hasDerivAt_upow hu (-(1 / 2 : ℝ)))
  convert h using 1
  · funext x; simp [f]
  have e1 : (1 - k * r ^ 2) ^ (-(1 / 2 : ℝ)) =
      (1 - k * r ^ 2) * (1 - k * r ^ 2) ^ (-(3 / 2 : ℝ)) := by
    rw [show (-(1 / 2 : ℝ)) = 1 + (-(3 / 2)) by norm_num, Real.rpow_add hu, Real.rpow_one]
  rw [show (-(1 / 2 : ℝ)) - 1 = -(3 / 2) by norm_num, e1]
  simp only [id]
  ring

/-- f″(r) = 3kr(1 − kr²)^(−5/2)。 -/
theorem hasDerivAt_f' {r : ℝ} (hu : 0 < 1 - k * r ^ 2) :
    HasDerivAt (fun r => (1 - k * r ^ 2) ^ (-(3 / 2 : ℝ)))
      (3 * k * r * (1 - k * r ^ 2) ^ (-(5 / 2 : ℝ))) r := by
  have h := hasDerivAt_upow hu (-(3 / 2 : ℝ))
  convert h using 1
  rw [show (-(3 / 2 : ℝ)) - 1 = -(5 / 2) by norm_num]
  ring

/-- (1) K(r) = −3k/(1 − kr²)²（0 < r、kr² < 1）。 -/
theorem curvature_eq {r : ℝ} (hr : 0 < r) (hu : 0 < 1 - k * r ^ 2) :
    K k r = -3 * k / (1 - k * r ^ 2) ^ 2 := by
  -- f′ は r の近くで (1 − kr²)^(−3/2) に等しい
  have hev : deriv (f k) =ᶠ[nhds r] fun r => (1 - k * r ^ 2) ^ (-(3 / 2 : ℝ)) := by
    have hopen : IsOpen {x : ℝ | 0 < 1 - k * x ^ 2} :=
      isOpen_lt continuous_const (continuous_const.sub (continuous_const.mul (continuous_pow 2)))
    filter_upwards [hopen.mem_nhds hu] with x hx
    exact (hasDerivAt_f hx).deriv
  unfold K
  rw [hev.deriv_eq, (hasDerivAt_f' hu).deriv]
  unfold f
  have hp : 0 < (1 - k * r ^ 2) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hu _
  have e : (1 - k * r ^ 2) ^ (-(5 / 2 : ℝ)) =
      (1 - k * r ^ 2) ^ (-(1 / 2 : ℝ)) * ((1 - k * r ^ 2) ^ 2)⁻¹ := by
    rw [show (-(5 / 2 : ℝ)) = -(1 / 2) + (-2) by norm_num, Real.rpow_add hu]
    congr 1
    rw [Real.rpow_neg hu.le, Real.rpow_two]
  rw [e]
  field_simp

/-- Ω, c で書いた形：−3Ω²c²/(c² − Ω²r²)²。 -/
theorem curvature_eq_omega {Ω c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hu : 0 < 1 - (Ω ^ 2 / c ^ 2) * r ^ 2) :
    K (Ω ^ 2 / c ^ 2) r = -3 * Ω ^ 2 * c ^ 2 / (c ^ 2 - Ω ^ 2 * r ^ 2) ^ 2 := by
  rw [curvature_eq hr hu]
  have : c ^ 2 - Ω ^ 2 * r ^ 2 = c ^ 2 * (1 - (Ω ^ 2 / c ^ 2) * r ^ 2) := by field_simp
  rw [this]
  field_simp

/-- 曲率はつねに負。 -/
theorem curvature_neg (hk : 0 < k) {r : ℝ} (hr : 0 < r) (hu : 0 < 1 - k * r ^ 2) : K k r < 0 := by
  rw [curvature_eq hr hu]
  apply div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- (2) 面積 ∫₀^R 2πf(r)dr = (2π/k)(1 − √(1 − kR²))。 -/
theorem area_eq (hk : 0 < k) {R : ℝ} (hR : 0 ≤ R) (hu : 0 < 1 - k * R ^ 2) :
    ∫ r in (0 : ℝ)..R, 2 * π * f k r = 2 * π / k * (1 - √(1 - k * R ^ 2)) := by
  have hu' : ∀ r ∈ uIcc 0 R, 0 < 1 - k * r ^ 2 := by
    intro r hr
    rw [uIcc_of_le hR] at hr
    have : r ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
    nlinarith
  set F : ℝ → ℝ := fun r => -(2 * π / k) * (1 - k * r ^ 2) ^ (1 / 2 : ℝ)
  have hF : ∀ r ∈ uIcc 0 R, HasDerivAt F (2 * π * f k r) r := by
    intro r hr
    have h := (hasDerivAt_upow (hu' r hr) (1 / 2 : ℝ)).const_mul (-(2 * π / k))
    convert h using 1
    unfold f
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
    field_simp
  have hint : IntervalIntegrable (fun r => 2 * π * f k r) MeasureTheory.volume 0 R := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul
      (fun r hr => (hasDerivAt_f (hu' r hr)).continuousAt.continuousWithinAt)
  rw [integral_eq_sub_of_hasDerivAt hF hint]
  simp only [F]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  simp
  ring

/-- 周 ÷ 直径 = π/√(1 − β²)（β² = kR²）。 -/
theorem circ_ratio {R : ℝ} (hR : 0 < R) (hu : 0 < 1 - k * R ^ 2) :
    2 * π * f k R / (2 * R) = π / √(1 - k * R ^ 2) := by
  unfold f
  rw [Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  have : 0 < √(1 - k * R ^ 2) := Real.sqrt_pos.mpr hu
  field_simp

/-- 面積 ÷ πR² = 2/(1 + √(1 − β²))（β² = kR²）。 -/
theorem area_ratio (hk : 0 < k) {R : ℝ} (hR : 0 < R) (hu : 0 < 1 - k * R ^ 2) :
    (∫ r in (0 : ℝ)..R, 2 * π * f k r) / (π * R ^ 2) = 2 / (1 + √(1 - k * R ^ 2)) := by
  rw [area_eq hk hR.le hu]
  set s := √(1 - k * R ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - k * R ^ 2 := Real.sq_sqrt hu.le
  have hkR : k * R ^ 2 = (1 - s) * (1 + s) := by nlinarith
  have hpi := Real.pi_pos
  have h1s : 0 < 1 + s := by linarith
  rw [div_eq_div_iff (by positivity) h1s.ne']
  have : 2 * π / k * (1 - s) * (1 + s) = 2 * π / k * (k * R ^ 2) := by rw [hkR]; ring
  rw [this]
  field_simp

end

/-- (3) 0 < s < 1（s = √(1 − β²)）なら 1 < 2/(1 + s) < 1/s。 -/
theorem ratio_bounds {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : 1 < 2 / (1 + s) ∧ 2 / (1 + s) < 1 / s := by
  constructor
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_div_iff₀ (by linarith) h0]; linarith

end Paper1027

end Yamagishi
