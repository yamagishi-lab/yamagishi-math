/-
論文1115『光の球のマス目に配った 4πc² は、場の質量が 0 ならどの皮でも同じ』の数の部分を、
一般の形で機械に確かめさせる（格上げ）。

原稿（1115_yamagishi_four_pi_c2_shared_over_the_light_sphere_cells_…/…_jp.tex）の
  第2節：フェアリンデの勘定 N = Ac³/(Għ)、A = 4πR²、k_BT = ħa/(2πc)、a = GM/R² で
    ½ N k_BT = Mc²（R は消える）。流束の形 ½ N k_BT = c²/(4πG) · (4πR² a)。
  第3節：置き方 G = 4π、ħ = 1/(4π)、M = 4π、k_B = 1 で、半径 R の皮のマス目 4πR²c³、
    一マスの温度 2/(R²c)、和 4πc²。光の球（R = c）でマス目 4πc⁵、温度 2/c³。
  第5節：湯川の形の位置のエネルギー −GMe^(−κr)/r で、加速度 GM(1+κR)e^(−κR)/R²、
    和 ÷ Mc² = (1 + κR)e^(−κR)、「和が皮の大きさによらないのは κ = 0 のときだけ」
    （原稿は κ = 1 の四つの R の数表で示す）。

ここで証明した一般の言明：
  (1) 第2節の勘定の恒等式（正の G・ħ・c・R、任意の M）。
  (2) 第3節の置き方の表（すべての R > 0、c > 0）。
  (3) 湯川の形の位置のエネルギーの微分が GM(1+κr)e^(−κr)/r²（加速度は数値微分でなく式で）。
  (4) その加速度で勘定した和 ÷ Mc² = (1 + κR)e^(−κR)。
  (5) 和がすべての皮の半径 R > 0 で同じ ⇔ κ = 0（κ は任意の実数。正でも負でも）。
      κ > 0 では和は R とともに狭義に減る（(1 + x)e^(−x) は x > 0 で狭義に減る）。
足した仮定：加速度を位置のエネルギーの r での微分（の大きさ）として置いた（原稿も数値微分で同じことをする）。
κ は実数全体で扱った（原稿は κ ≥ 0 の場合だけを考えている）。

形式化していないもの：マス目・温度・等分配・ウンルーの温度という物理の読み（勘定の式は入力として置いた）、
「残る 4π は質量の 4π」という読み、SI の数値（4.32346×10⁸⁷ など）、論文1107 との同根の判定、
E = 2TS とスマーの関係。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1115

open Real Set

/-- マス目の数 N = 4πR²c³/(Għ)。 -/
noncomputable def cells (G hbar c R : ℝ) : ℝ := 4 * π * R ^ 2 * c ^ 3 / (G * hbar)

/-- ウンルーの形の一マスの温度 k_BT = ħa/(2πc)。 -/
noncomputable def cellTemp (hbar c a : ℝ) : ℝ := hbar * a / (2 * π * c)

/-- (1) 第2節：a = GM/R² で ½ N k_BT = Mc²（R・ħ は消える）。 -/
theorem verlinde_count (G hbar c R M : ℝ) (hG : G ≠ 0) (hh : hbar ≠ 0) (hc : c ≠ 0)
    (hR : R ≠ 0) :
    (1 / 2) * cells G hbar c R * cellTemp hbar c (G * M / R ^ 2) = M * c ^ 2 := by
  unfold cells cellTemp
  field_simp
  ring

/-- (1) 第2節：流束の形 ½ N k_BT = c²/(4πG) · (4πR² a)（どの a でも）。 -/
theorem verlinde_flux (G hbar c R a : ℝ) (hG : G ≠ 0) (hh : hbar ≠ 0) (hc : c ≠ 0) :
    (1 / 2) * cells G hbar c R * cellTemp hbar c a = c ^ 2 / (4 * π * G) * (4 * π * R ^ 2 * a) := by
  unfold cells cellTemp
  field_simp
  ring

/-- (2) 第3節：G = 4π、ħ = 1/(4π)、M = 4π で、半径 R の皮のマス目 4πR²c³、一マスの温度 2/(R²c)、
和 4πc²（R によらない）。 -/
theorem patch_table (c R : ℝ) (hc : 0 < c) (hR : 0 < R) :
    cells (4 * π) (1 / (4 * π)) c R = 4 * π * R ^ 2 * c ^ 3 ∧
    cellTemp (1 / (4 * π)) c ((4 * π) * (4 * π) / R ^ 2) = 2 / (R ^ 2 * c) ∧
    (1 / 2) * cells (4 * π) (1 / (4 * π)) c R * cellTemp (1 / (4 * π)) c ((4 * π) * (4 * π) / R ^ 2)
      = 4 * π * c ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold cells; field_simp
  · unfold cellTemp; field_simp; ring
  · rw [verlinde_count _ _ _ _ _ (by positivity) (by positivity) hc.ne' hR.ne']

/-- (2) 光の球（R = c）：マス目 4πc⁵、一マスの温度 2/c³。 -/
theorem light_sphere (c : ℝ) (hc : 0 < c) :
    cells (4 * π) (1 / (4 * π)) c c = 4 * π * c ^ 5 ∧
    cellTemp (1 / (4 * π)) c ((4 * π) * (4 * π) / c ^ 2) = 2 / c ^ 3 := by
  obtain ⟨h1, h2, _⟩ := patch_table c c hc hc
  refine ⟨by rw [h1]; ring, by rw [h2]; ring⟩

/-! ### 湯川の形の場 -/

/-- 湯川の形の位置のエネルギー Φ(r) = −GM e^(−κr)/r。 -/
noncomputable def yukawa (G M κ r : ℝ) : ℝ := -(G * M * exp (-(κ * r)) / r)

/-- (3) Φ の微分（皮の上の加速度）は GM(1 + κr)e^(−κr)/r²。 -/
theorem yukawa_accel (G M κ r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (yukawa G M κ) (G * M * (1 + κ * r) * exp (-(κ * r)) / r ^ 2) r := by
  unfold yukawa
  have h1 : HasDerivAt (fun r => exp (-(κ * r))) (exp (-(κ * r)) * (-(κ * 1))) r :=
    (((hasDerivAt_id' r).const_mul κ).neg).exp
  have h2 := ((h1.const_mul (G * M)).div (hasDerivAt_id' r) hr).neg
  convert h2 using 1
  field_simp
  ring

/-- (4) その加速度で勘定した和 ÷ Mc² = (1 + κR)e^(−κR)。 -/
theorem yukawa_ratio (G hbar c R M κ : ℝ) (hG : G ≠ 0) (hh : hbar ≠ 0) (hc : c ≠ 0) (hR : R ≠ 0)
    (hM : M ≠ 0) :
    (1 / 2) * cells G hbar c R * cellTemp hbar c (G * M * (1 + κ * R) * exp (-(κ * R)) / R ^ 2)
      / (M * c ^ 2) = (1 + κ * R) * exp (-(κ * R)) := by
  unfold cells cellTemp
  field_simp
  ring

/-- f(x) = (1 + x)e^(−x)。 -/
noncomputable def f (x : ℝ) : ℝ := (1 + x) * exp (-x)

theorem f_hasDerivAt (x : ℝ) : HasDerivAt f (-(x * exp (-x))) x := by
  unfold f
  have h := ((hasDerivAt_id' x).const_add 1).mul ((hasDerivAt_neg x).exp)
  convert h using 1
  ring

theorem f_strictAntiOn : StrictAntiOn f (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact fun x _ => (f_hasDerivAt x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(f_hasDerivAt x).deriv]
    have := exp_pos (-x)
    have : 0 < x := hx
    nlinarith [mul_pos this (exp_pos (-x))]

theorem f_strictMonoOn : StrictMonoOn f (Iic 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic 0)
  · exact fun x _ => (f_hasDerivAt x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Iic] at hx
    rw [(f_hasDerivAt x).deriv]
    have : x < 0 := hx
    nlinarith [mul_pos (neg_pos.mpr this) (exp_pos (-x))]

/-- (5) κ > 0 では、和は皮の半径とともに狭義に減る。 -/
theorem ratio_decreasing (κ : ℝ) (hκ : 0 < κ) :
    StrictAntiOn (fun R => (1 + κ * R) * exp (-(κ * R))) (Ioi 0) := by
  intro R1 h1 R2 h2 h12
  have := f_strictAntiOn (a := κ * R1) (b := κ * R2) (mul_pos hκ h1).le (mul_pos hκ h2).le
    (mul_lt_mul_of_pos_left h12 hκ)
  simpa [f] using this

/-- (5) 本稿の言明：和がすべての皮の半径 R > 0 で同じ ⇔ κ = 0（κ は任意の実数）。 -/
theorem ratio_const_iff (κ : ℝ) :
    (∀ R1 R2 : ℝ, 0 < R1 → 0 < R2 →
      (1 + κ * R1) * exp (-(κ * R1)) = (1 + κ * R2) * exp (-(κ * R2))) ↔ κ = 0 := by
  constructor
  · intro h
    by_contra hκ
    have h12 := h 1 2 one_pos two_pos
    rcases lt_or_gt_of_ne hκ with hneg | hpos
    · have := f_strictMonoOn (a := κ * 2) (b := κ * 1) (Set.mem_Iic.mpr (by linarith))
        (Set.mem_Iic.mpr (by linarith)) (by linarith)
      simp only [f] at this
      linarith
    · have := f_strictAntiOn (a := κ * 1) (b := κ * 2) (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by linarith)) (by linarith)
      simp only [f] at this
      linarith
  · rintro rfl R1 R2 _ _
    simp

/-- 原稿の表の κ = 1、R = 1 の値：(1 + 1)e^(−1) = 2/e。 -/
theorem table_R_one : (1 + 1 * 1) * exp (-(1 * 1 : ℝ)) = 2 / exp 1 := by
  rw [exp_neg]; norm_num; ring

end Paper1115

end Yamagishi
