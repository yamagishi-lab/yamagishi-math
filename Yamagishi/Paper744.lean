/-
論文744『わざと当てはまりを悪くすると予測が良くなり、どれだけ縮めるかは信号の強さが決める』の格上げ（一般の形）。

原稿（744_yamagishi_fit_worse_on_purpose_predict_better/…_jp.tex）は、直交した説明変数のリッジ回帰で
予測の余分な誤差 E(λ) = (λ/(n + λ))²‖β‖² + (n/(n + λ))² dσ²/n と λ* = dσ²/‖β‖² を書き、
d = 50・n = 100・σ² = 1、信号 1 と 10、λ = 0, 5, 50, 500 の数値と格子・乱数で示す（λ* の導出は書いていない）。

ここで証明した言明（n > 0、B = ‖β‖² > 0、V = dσ²/n > 0、λ ≥ 0）：
  (1) `err_min`：E(λ) は λ* = nV/B = dσ²/‖β‖² でただ一つの最小をとる（λ ≠ λ* なら E(λ*) < E(λ)）。
  (2) `err_min_value`：最小値は BV/(B + V)、すなわち λ = 0 の値 E(0) = V の B/(B + V) 倍。
足した仮定：直交した説明変数（一律の縮め n/(n + λ)）での原稿の式を定義に置いた。
形式化していないもの：「訓練側の外れの項」の読み（確かめの係の指摘：表のその列は偏りの二乗の項で、
訓練の残差の増え方そのものではない）、数表と乱数、λ* を推定したときの話、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper744

/-- 予測の余分な誤差 E(λ)。 -/
noncomputable def E (n B V l : ℝ) : ℝ := (l / (n + l)) ^ 2 * B + (n / (n + l)) ^ 2 * V

section

variable {n B V : ℝ} (hn : 0 < n) (hB : 0 < B) (hV : 0 < V)
include hn hB hV

/-- E(λ) = (B + V)(s − s*)² + BV/(B + V)、s = n/(n + λ)、s* = B/(B + V)。 -/
theorem err_square {l : ℝ} (hl : 0 ≤ l) :
    E n B V l = (B + V) * (n / (n + l) - B / (B + V)) ^ 2 + B * V / (B + V) := by
  unfold E
  have h1 : 0 < n + l := by linarith
  have : l / (n + l) = 1 - n / (n + l) := by field_simp; ring
  rw [this]
  field_simp
  ring

/-- (2) 最小値 E(λ*) = BV/(B + V)。 -/
theorem err_min_value : E n B V (n * V / B) = B * V / (B + V) := by
  rw [err_square hn hB hV (by positivity)]
  have : n / (n + n * V / B) = B / (B + V) := by field_simp
  rw [this, sub_self]; ring

omit hB hV in
/-- E(0) = V、最小値はその B/(B + V) 倍。 -/
theorem err_zero : E n B V 0 = V := by unfold E; field_simp; ring

theorem err_min_ratio : E n B V (n * V / B) = E n B V 0 * (B / (B + V)) := by
  rw [err_min_value hn hB hV, err_zero hn]; ring

/-- (1) λ* = nV/B でただ一つの最小。 -/
theorem err_min {l : ℝ} (hl : 0 ≤ l) (hne : l ≠ n * V / B) :
    E n B V (n * V / B) < E n B V l := by
  rw [err_min_value hn hB hV, err_square hn hB hV hl]
  have h1 : 0 < n + l := by linarith
  have hs : n / (n + l) - B / (B + V) ≠ 0 := by
    intro h
    apply hne
    rw [sub_eq_zero, div_eq_div_iff (ne_of_gt h1) (by positivity)] at h
    field_simp
    linarith
  have : 0 < (B + V) * (n / (n + l) - B / (B + V)) ^ 2 := by positivity
  linarith

end

end Paper744

end Yamagishi
