/-
論文910『平らな回転曲線は、その区間の密度と、内側の囲む質量だけを決める』の言明を、
一般の形で機械に確かめさせる（格上げ）。

原稿（910_yamagishi_a_flat_rotation_curve_fixes_the_density_and_only_the_enclosed_mass/…_jp.tex）の設定：
  球対称で、半径 r の内側の質量 M(r)、円運動の速さ v(r)：v² = GM(r)/r、dM/dr = 4πr²ρ、
  4πGr²ρ = d(rv²)/dr = v²(1 + 2s)、s = d ln v / d ln r。
原稿が示している事：
  計算 2.1：ρ = r^(−n) の五つの n（0, 1, 1.5, 2, 2.5）を数値で積み、速さの傾きが (2 − n)/2 に合い、
    平らになるのは n = 2 だけ。
  計算 3.1：芯のある密度で、回転曲線から密度を数値で戻す。
  計算 4.1・観察 4.2（本稿の芯）：半径 1 から外を ρ = 1/(4πr²) にし、内側を四つの冪で埋めた数値で、
    外の速さが 1 のままであること、内側の質量を 1 割増やすと √(1 + 0.1/r) になること。
  第5節：等温の球の線形化の固有値 (−1 ± i√7)/2。
  一行の一般の導出は書かれていない（確かめの係の指摘）。

ここで証明した一般の言明（r₁ < r₂、r₁ > 0、G > 0）：
  (1) M が [r₁, r₂] で dM/dr = 4πr²ρ を満たし、区間の密度が ρ = v₀²/(4πGr²) なら、区間の上で
      v² = v₀² + (GM(r₁) − v₀² r₁)/r。だから速さが区間で v₀ のまま ⇔ GM(r₁) = v₀² r₁。
      内側の並び方は M(r₁) という一つの数を通してしか入らない（同じ M(r₁) なら同じ速さ）。
  (2) 逆に、区間 [r₁, r₂] で v² = v₀² なら、M(r₁) = v₀² r₁/G、区間の内側で ρ = v₀²/(4πGr²)。
  (3) d(rv²)/dr = 4πGr²ρ、それを v²(1 + 2s) と書いた形（代数）。
  (4) ρ = r^(−n)（n < 3）を原点から積むと M = 4πr^(3−n)/(3−n)、v² = 4πG r^(2−n)/(3−n)、
      速さの傾き d ln v/d ln r = (2 − n)/2、速さが r によらない ⇔ n = 2（すべての n < 3）。
  (5) 等温の球の二変数の式 dz/dt = w − z、dw/dt = w(2 − z) の止まる点 (2, 2) で、
      線形化の行列の固有方程式は λ² + λ + 2 = 0、根は (−1 ± i√7)/2。
足した仮定：M は区間の各点で（両側の）微分を持つこと。(4) の冪の密度では原点から積むので n < 3。

形式化していないもの：数値積分の表、芯のある密度の例、等温の球の振動が r^(−2) に寄ることの解析
（線形化の固有値だけを示した）、特異等温球・ダークマターなどの読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper910

open Real Set

/-- (1) 区間の密度が v₀²/(4πGr²) なら、M(r) = M(r₁) + v₀²(r − r₁)/G。 -/
theorem mass_on_flat_interval (G v0 r1 r2 : ℝ) (M ρ : ℝ → ℝ) (hG : 0 < G) (hr1 : 0 < r1)
    (hM : ∀ r ∈ Icc r1 r2, HasDerivAt M (4 * π * r ^ 2 * ρ r) r)
    (hρ : ∀ r ∈ Icc r1 r2, ρ r = v0 ^ 2 / (4 * π * G * r ^ 2)) :
    ∀ r ∈ Icc r1 r2, M r = M r1 + v0 ^ 2 * (r - r1) / G := by
  set φ : ℝ → ℝ := fun r => M r - v0 ^ 2 / G * r
  have hφ : ∀ r ∈ Icc r1 r2, HasDerivAt φ 0 r := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le hr1 hr.1
    have h := (hM r hr).sub ((hasDerivAt_id' r).const_mul (v0 ^ 2 / G))
    convert h using 1
    rw [hρ r hr]; field_simp; ring
  have hcont : ContinuousOn φ (Icc r1 r2) := fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  intro r hr
  have := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hφ t (Ico_subset_Icc_self ht)).hasDerivWithinAt) r hr
  simp only [φ] at this
  field_simp
  field_simp at this
  linarith

/-- (1) 区間の上の速さ：v² = GM/r = v₀² + (GM(r₁) − v₀² r₁)/r。 -/
theorem speed_on_flat_interval (G v0 r1 r2 : ℝ) (M ρ : ℝ → ℝ) (hG : 0 < G) (hr1 : 0 < r1)
    (hM : ∀ r ∈ Icc r1 r2, HasDerivAt M (4 * π * r ^ 2 * ρ r) r)
    (hρ : ∀ r ∈ Icc r1 r2, ρ r = v0 ^ 2 / (4 * π * G * r ^ 2)) :
    ∀ r ∈ Icc r1 r2, G * M r / r = v0 ^ 2 + (G * M r1 - v0 ^ 2 * r1) / r := by
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le hr1 hr.1
  rw [mass_on_flat_interval G v0 r1 r2 M ρ hG hr1 hM hρ r hr]
  field_simp
  ring

/-- (1) 本稿の芯：区間の密度が v₀²/(4πGr²) のとき、速さが区間で v₀ のまま ⇔ GM(r₁) = v₀² r₁
（内側には囲む質量だけを課す）。r₁ < r₂ とする。 -/
theorem flat_iff_enclosed_mass (G v0 r1 r2 : ℝ) (M ρ : ℝ → ℝ) (hG : 0 < G) (hr1 : 0 < r1)
    (hr12 : r1 < r2)
    (hM : ∀ r ∈ Icc r1 r2, HasDerivAt M (4 * π * r ^ 2 * ρ r) r)
    (hρ : ∀ r ∈ Icc r1 r2, ρ r = v0 ^ 2 / (4 * π * G * r ^ 2)) :
    (∀ r ∈ Icc r1 r2, G * M r / r = v0 ^ 2) ↔ G * M r1 = v0 ^ 2 * r1 := by
  have hs := speed_on_flat_interval G v0 r1 r2 M ρ hG hr1 hM hρ
  constructor
  · intro h
    have := h r1 ⟨le_rfl, hr12.le⟩
    rw [hs r1 ⟨le_rfl, hr12.le⟩] at this
    have hr0 : r1 ≠ 0 := hr1.ne'
    field_simp at this
    linarith
  · intro h r hr
    rw [hs r hr, h, sub_self, zero_div, add_zero]

/-- (1) 内側の並び方は外の速さに現れない：同じ M(r₁) と同じ区間の密度なら、区間の速さは同じ。 -/
theorem inner_arrangement_invisible (G v0 r1 r2 : ℝ) (M M' ρ ρ' : ℝ → ℝ) (hG : 0 < G)
    (hr1 : 0 < r1)
    (hM : ∀ r ∈ Icc r1 r2, HasDerivAt M (4 * π * r ^ 2 * ρ r) r)
    (hM' : ∀ r ∈ Icc r1 r2, HasDerivAt M' (4 * π * r ^ 2 * ρ' r) r)
    (hρ : ∀ r ∈ Icc r1 r2, ρ r = v0 ^ 2 / (4 * π * G * r ^ 2))
    (hρ' : ∀ r ∈ Icc r1 r2, ρ' r = v0 ^ 2 / (4 * π * G * r ^ 2))
    (hsame : M r1 = M' r1) :
    ∀ r ∈ Icc r1 r2, G * M r / r = G * M' r / r := by
  intro r hr
  rw [speed_on_flat_interval G v0 r1 r2 M ρ hG hr1 hM hρ r hr,
    speed_on_flat_interval G v0 r1 r2 M' ρ' hG hr1 hM' hρ' r hr, hsame]

/-- 原稿の観察 4.2 の例：G = 1、v₀ = 1、r₁ = 1 で内側の質量を 1 割増やす（M(1) = 1.1）と v² = 1 + 0.1/r。 -/
theorem ten_percent_example (r2 : ℝ) (M ρ : ℝ → ℝ)
    (hM : ∀ r ∈ Icc 1 r2, HasDerivAt M (4 * π * r ^ 2 * ρ r) r)
    (hρ : ∀ r ∈ Icc 1 r2, ρ r = 1 ^ 2 / (4 * π * 1 * r ^ 2)) (h1 : M 1 = 1.1) :
    ∀ r ∈ Icc 1 r2, 1 * M r / r = 1 + 0.1 / r := by
  intro r hr
  rw [speed_on_flat_interval 1 1 1 r2 M ρ one_pos one_pos hM hρ r hr, h1]
  norm_num

/-- (2) 逆向き：区間で v² = v₀² なら、M(r₁) = v₀² r₁/G、区間の内側で ρ = v₀²/(4πGr²)。 -/
theorem flat_forces_density (G v0 r1 r2 : ℝ) (M ρ : ℝ → ℝ) (hG : 0 < G) (hr1 : 0 < r1)
    (hr12 : r1 < r2)
    (hM : ∀ r ∈ Icc r1 r2, HasDerivAt M (4 * π * r ^ 2 * ρ r) r)
    (hflat : ∀ r ∈ Icc r1 r2, G * M r / r = v0 ^ 2) :
    M r1 = v0 ^ 2 * r1 / G ∧ ∀ r ∈ Ioo r1 r2, ρ r = v0 ^ 2 / (4 * π * G * r ^ 2) := by
  have hMeq : ∀ r ∈ Icc r1 r2, M r = v0 ^ 2 / G * r := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le hr1 hr.1
    have := hflat r hr
    field_simp at this ⊢
    linarith
  refine ⟨by rw [hMeq r1 ⟨le_rfl, hr12.le⟩]; ring, fun r hr => ?_⟩
  have hr0 : 0 < r := lt_trans hr1 hr.1
  have hev : M =ᶠ[nhds r] fun y => v0 ^ 2 / G * y := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with y hy
    exact hMeq y ⟨hy.1.le, hy.2.le⟩
  have hlin : HasDerivAt (fun y => v0 ^ 2 / G * y) (v0 ^ 2 / G * 1) r :=
    (hasDerivAt_id' r).const_mul (v0 ^ 2 / G)
  have h1 := (hM r (Ioo_subset_Icc_self hr)).congr_of_eventuallyEq hev.symm
  have heq := h1.unique hlin
  have hπ : 0 < π := pi_pos
  field_simp
  field_simp at heq
  linarith

/-- (3) d(rv²)/dr = 4πGr²ρ（v² = GM/r、r > 0）。 -/
theorem flux_identity (G r : ℝ) (M ρ : ℝ → ℝ) (hr : 0 < r)
    (hM : HasDerivAt M (4 * π * r ^ 2 * ρ r) r) :
    HasDerivAt (fun r => r * (G * M r / r)) (4 * π * G * r ^ 2 * ρ r) r := by
  have hev : (fun r => r * (G * M r / r)) =ᶠ[nhds r] fun r => G * M r := by
    filter_upwards [lt_mem_nhds hr] with y hy
    field_simp
  have := hM.const_mul G
  refine (this.congr_of_eventuallyEq hev).congr_deriv ?_
  ring

/-- (3) 同じ式を v²(1 + 2s)、s = r(v²)'/(2v²) = d ln v/d ln r で書いた形（代数）。 -/
theorem flux_identity_s (u u' r : ℝ) (hu : u ≠ 0) :
    u + r * u' = u * (1 + 2 * (r * u' / (2 * u))) := by
  field_simp

/-! ### (4) 冪の密度 -/

/-- 2^x = 1 ⇔ x = 0。 -/
theorem two_rpow_eq_one_iff (x : ℝ) : (2 : ℝ) ^ x = 1 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · exact (rpow_lt_one_of_one_lt_of_neg (by norm_num) hlt).ne h
    · exact (one_lt_rpow (by norm_num) hgt).ne' h
  · rintro rfl; simp

/-- (4) ρ = r^(−n)（n < 3）を原点から積んだ M(r) = 4πr^(3−n)/(3−n) は dM/dr = 4πr²ρ を満たす。 -/
theorem power_mass (n r : ℝ) (hn : n < 3) (hr : 0 < r) :
    HasDerivAt (fun r => 4 * π * r ^ (3 - n) / (3 - n)) (4 * π * r ^ 2 * r ^ (-n)) r := by
  have h3 : (3 - n) ≠ 0 := by linarith
  have h := ((hasDerivAt_rpow_const (p := 3 - n) (Or.inl hr.ne')).const_mul (4 * π)).div_const
    (3 - n)
  convert h using 1
  have e : r ^ (3 - n - 1) = r ^ 2 * r ^ (-n) := by
    rw [show (3 - n - 1) = (2 : ℝ) + (-n) by ring, rpow_add hr]
    norm_cast
  rw [e]
  field_simp

/-- (4) 冪の密度の速さ v² = GM/r = 4πG r^(2−n)/(3−n)。 -/
theorem power_speed_sq (G n r : ℝ) (hr : 0 < r) :
    G * (4 * π * r ^ (3 - n) / (3 - n)) / r = 4 * π * G / (3 - n) * r ^ (2 - n) := by
  have e : r ^ (3 - n) = r ^ (2 - n) * r := by
    rw [show (3 - n) = (2 - n) + 1 by ring, rpow_add hr, rpow_one]
  rw [e]
  field_simp

/-- (4) 速さの傾き：v = √(4πG/(3−n)) r^((2−n)/2)、だから ln v = 定数 + ((2 − n)/2) ln r。 -/
theorem power_speed_slope (G n r : ℝ) (hG : 0 < G) (hn : n < 3) (hr : 0 < r) :
    log (√(4 * π * G / (3 - n) * r ^ (2 - n))) =
      log (√(4 * π * G / (3 - n))) + (2 - n) / 2 * log r := by
  have hc : 0 < 4 * π * G / (3 - n) := div_pos (by positivity) (by linarith)
  rw [Real.sqrt_mul hc.le, log_mul (Real.sqrt_pos.mpr hc).ne'
    (Real.sqrt_pos.mpr (rpow_pos_of_pos hr _)).ne', Real.sqrt_eq_rpow (r ^ (2 - n)),
    log_rpow (rpow_pos_of_pos hr _), log_rpow hr]
  ring

/-- (4) 冪の密度で速さが r によらない（すべての r > 0 で同じ）⇔ n = 2（n < 3 のすべての n で）。 -/
theorem power_flat_iff (G n : ℝ) (hG : 0 < G) (hn : n < 3) :
    (∀ r1 r2 : ℝ, 0 < r1 → 0 < r2 →
      G * (4 * π * r1 ^ (3 - n) / (3 - n)) / r1 = G * (4 * π * r2 ^ (3 - n) / (3 - n)) / r2) ↔
      n = 2 := by
  constructor
  · intro h
    have h12 := h 1 2 one_pos two_pos
    rw [power_speed_sq G n 1 one_pos, power_speed_sq G n 2 two_pos, one_rpow] at h12
    have hc : 4 * π * G / (3 - n) ≠ 0 := (div_pos (by positivity) (by linarith)).ne'
    have : (2 : ℝ) ^ (2 - n) = 1 := mul_left_cancel₀ hc h12.symm
    have := (two_rpow_eq_one_iff _).mp this
    linarith
  · rintro rfl r1 r2 hr1 hr2
    rw [power_speed_sq G 2 r1 hr1, power_speed_sq G 2 r2 hr2]
    norm_num

/-! ### (5) 等温の球の線形化 -/

/-- 二変数の式の右辺。 -/
def fz (z w : ℝ) : ℝ := w - z
def fw (z w : ℝ) : ℝ := w * (2 - z)

/-- (5) (2, 2) は止まる点で、偏微分は ∂fz/∂z = −1、∂fz/∂w = 1、∂fw/∂z = −w = −2、∂fw/∂w = 2 − z = 0。 -/
theorem isothermal_fixed_point :
    fz 2 2 = 0 ∧ fw 2 2 = 0 ∧
    HasDerivAt (fun z => fz z 2) (-1) 2 ∧ HasDerivAt (fun w => fz 2 w) 1 2 ∧
    HasDerivAt (fun z => fw z 2) (-2) 2 ∧ HasDerivAt (fun w => fw 2 w) 0 2 := by
  refine ⟨by norm_num [fz], by norm_num [fw], ?_, ?_, ?_, ?_⟩
  · simpa [fz] using (hasDerivAt_id' (2 : ℝ)).const_sub 2
  · simpa [fz] using (hasDerivAt_id' (2 : ℝ)).sub_const 2
  · have := ((hasDerivAt_id' (2 : ℝ)).const_sub 2).const_mul 2
    simpa [fw] using this
  · have := (hasDerivAt_id' (2 : ℝ)).mul_const (2 - 2 : ℝ)
    simpa [fw] using this

/-- (5) 線形化の行列 [[−1, 1], [−2, 0]] の固有方程式は λ² + λ + 2 = 0、根は (−1 ± i√7)/2
（振動の周期は ln ξ で 4π/√7、振幅は e^(−t/2) = ξ^(−1/2) で減る）。 -/
theorem isothermal_eigenvalues :
    (∀ l : ℂ, Matrix.det (!![(-1 : ℂ) - l, 1; -2, 0 - l]) = l ^ 2 + l + 2) ∧
    ((-1 + Complex.I * Real.sqrt 7) / 2) ^ 2 + (-1 + Complex.I * Real.sqrt 7) / 2 + 2 = 0 ∧
    ((-1 - Complex.I * Real.sqrt 7) / 2) ^ 2 + (-1 - Complex.I * Real.sqrt 7) / 2 + 2 = 0 := by
  have h7 : ((Real.sqrt 7 : ℝ) : ℂ) ^ 2 = 7 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  refine ⟨fun l => by rw [Matrix.det_fin_two_of]; ring, ?_, ?_⟩
  · ring_nf; rw [Complex.I_sq, h7]; ring
  · ring_nf; rw [Complex.I_sq, h7]; ring

end Paper910

end Yamagishi
