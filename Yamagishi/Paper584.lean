/-
論文584『免震層の減衰を増やすと、伝わる揺れがかえって増える側がある』の格上げ（一般の形）。

原稿（584_yamagishi_more_damping_passes_more_shaking/…_jp.tex）は、一自由度の粘性減衰の伝達率
TR = √((1 + (2ζr)²)/((1 − r²)² + (2ζr)²)) と変位の比 Z/Y = r²/√((1 − r²)² + (2ζr)²) を
r = 1, 2, 4 と ζ = 0.05, 0.20, 0.40 の表、r = √2 での四つの ζ、r = 1 での 1/(2ζ) の数で示し、
観察 3.2 で (1 − r²)² と 1 の大小から比が上がるか下がるかを言葉で説明している。

ここで証明した言明（周期比 r > 0、減衰比 ζ > 0）：
  (1) `tr_sqrt_two`：r = √2 ではすべての ζ で TR = 1。
  (2) `tr_gt_one`・`tr_anti`：0 < r < √2 では TR > 1 で、TR は ζ について狭義に減る。
  (3) `tr_lt_one`・`tr_mono`：r > √2 では TR < 1 で、TR は ζ について狭義に増える。
  (4) `resonance_disp`：共振 r = 1 で Z/Y = 1/(2ζ)。
足した仮定：線形の粘性減衰の模型の式を定義として置いた。ζ > 0 とした（ζ = 0 は r = 1 で分母が 0）。
形式化していないもの：表の値、非線形の免震ゴム・鉛の履歴、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper584

open Real

/-- 加速度の伝達率。 -/
noncomputable def TR (r ζ : ℝ) : ℝ := √((1 + (2 * ζ * r) ^ 2) / ((1 - r ^ 2) ^ 2 + (2 * ζ * r) ^ 2))

/-- 相対変位の比。 -/
noncomputable def ZY (r ζ : ℝ) : ℝ := r ^ 2 / √((1 - r ^ 2) ^ 2 + (2 * ζ * r) ^ 2)

/-- (1) r = √2 で TR = 1。 -/
theorem tr_sqrt_two (ζ : ℝ) : TR (√2) ζ = 1 := by
  unfold TR
  have : (1 - √2 ^ 2) ^ 2 = 1 := by rw [sq_sqrt (by norm_num)]; norm_num
  rw [this, div_self (by positivity), sqrt_one]

/-- 中身 (1 + x)/(A + x) と 1 の差：(1 − A)/(A + x)。 -/
theorem inner_sub_one {A x : ℝ} (h : 0 < A + x) : (1 + x) / (A + x) - 1 = (1 - A) / (A + x) := by
  field_simp; ring

theorem A_lt_one {r : ℝ} (hr : 0 < r) (hr2 : r < √2) : (1 - r ^ 2) ^ 2 < 1 := by
  have : r ^ 2 < 2 := by
    have := pow_lt_pow_left₀ hr2 hr.le (two_ne_zero); rwa [sq_sqrt (by norm_num)] at this
  have : 0 < r ^ 2 := by positivity
  nlinarith

theorem A_gt_one {r : ℝ} (hr2 : √2 < r) : 1 < (1 - r ^ 2) ^ 2 := by
  have : 2 < r ^ 2 := by
    have := pow_lt_pow_left₀ hr2 (sqrt_nonneg 2) (two_ne_zero); rwa [sq_sqrt (by norm_num)] at this
  nlinarith

theorem den_pos {r ζ : ℝ} (hr : 0 < r) (hζ : 0 < ζ) : 0 < (1 - r ^ 2) ^ 2 + (2 * ζ * r) ^ 2 := by
  positivity

/-- (2) 0 < r < √2 で TR > 1。 -/
theorem tr_gt_one {r ζ : ℝ} (hr : 0 < r) (hr2 : r < √2) (hζ : 0 < ζ) : 1 < TR r ζ := by
  unfold TR
  rw [lt_sqrt zero_le_one, one_pow, one_lt_div (den_pos hr hζ)]
  linarith [A_lt_one hr hr2]

/-- (3) r > √2 で TR < 1。 -/
theorem tr_lt_one {r ζ : ℝ} (hr2 : √2 < r) (hζ : 0 < ζ) : TR r ζ < 1 := by
  have hr : 0 < r := lt_of_le_of_lt (sqrt_nonneg 2) hr2
  unfold TR
  rw [sqrt_lt' one_pos, one_pow, div_lt_one (den_pos hr hζ)]
  linarith [A_gt_one hr2]

/-- 中身は x について、A < 1 なら減り、A > 1 なら増える。 -/
theorem inner_diff {A x y : ℝ} (hx : 0 < A + x) (hy : 0 < A + y) :
    (1 + y) / (A + y) - (1 + x) / (A + x) = (1 - A) * (x - y) / ((A + x) * (A + y)) := by
  field_simp; ring

/-- (2) 0 < r < √2 では TR は ζ について狭義に減る。 -/
theorem tr_anti {r ζ₁ ζ₂ : ℝ} (hr : 0 < r) (hr2 : r < √2) (h1 : 0 < ζ₁) (h12 : ζ₁ < ζ₂) :
    TR r ζ₂ < TR r ζ₁ := by
  have h2 : 0 < ζ₂ := h1.trans h12
  unfold TR
  apply sqrt_lt_sqrt (by have := den_pos hr h2; positivity)
  have hx := den_pos hr h1
  have hy := den_pos hr h2
  have hxy : (2 * ζ₁ * r) ^ 2 < (2 * ζ₂ * r) ^ 2 := by
    apply pow_lt_pow_left₀ (by nlinarith) (by positivity) two_ne_zero
  have := inner_diff hx hy
  have hA := A_lt_one hr hr2
  have : (1 - (1 - r ^ 2) ^ 2) * ((2 * ζ₁ * r) ^ 2 - (2 * ζ₂ * r) ^ 2) /
      (((1 - r ^ 2) ^ 2 + (2 * ζ₁ * r) ^ 2) * ((1 - r ^ 2) ^ 2 + (2 * ζ₂ * r) ^ 2)) < 0 := by
    apply div_neg_of_neg_of_pos _ (by positivity)
    apply mul_neg_of_pos_of_neg (by linarith) (by linarith)
  linarith

/-- (3) r > √2 では TR は ζ について狭義に増える。 -/
theorem tr_mono {r ζ₁ ζ₂ : ℝ} (hr2 : √2 < r) (h1 : 0 < ζ₁) (h12 : ζ₁ < ζ₂) :
    TR r ζ₁ < TR r ζ₂ := by
  have hr : 0 < r := lt_of_le_of_lt (sqrt_nonneg 2) hr2
  have h2 : 0 < ζ₂ := h1.trans h12
  unfold TR
  apply sqrt_lt_sqrt (by have := den_pos hr h1; positivity)
  have hx := den_pos hr h1
  have hy := den_pos hr h2
  have hxy : (2 * ζ₁ * r) ^ 2 < (2 * ζ₂ * r) ^ 2 := by
    apply pow_lt_pow_left₀ (by nlinarith) (by positivity) two_ne_zero
  have := inner_diff hx hy
  have hA := A_gt_one hr2
  have : 0 < (1 - (1 - r ^ 2) ^ 2) * ((2 * ζ₁ * r) ^ 2 - (2 * ζ₂ * r) ^ 2) /
      (((1 - r ^ 2) ^ 2 + (2 * ζ₁ * r) ^ 2) * ((1 - r ^ 2) ^ 2 + (2 * ζ₂ * r) ^ 2)) := by
    apply div_pos _ (by positivity)
    apply mul_pos_of_neg_of_neg (by linarith) (by linarith)
  linarith

/-- (4) 共振 r = 1 で Z/Y = 1/(2ζ)。 -/
theorem resonance_disp {ζ : ℝ} (hζ : 0 < ζ) : ZY 1 ζ = 1 / (2 * ζ) := by
  unfold ZY
  rw [show (1 - (1 : ℝ) ^ 2) ^ 2 + (2 * ζ * 1) ^ 2 = (2 * ζ) ^ 2 by ring, sqrt_sq (by positivity)]
  ring

end Paper584

end Yamagishi
