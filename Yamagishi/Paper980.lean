/-
論文980『区画の中で測る本数の最良は予算によらず、二倍にしても半分にしても損は同じ』の格上げ（一般の形）。

原稿（980_yamagishi_the_best_number_of_trees_per_plot_ignores_the_budget/…_jp.tex）は、
二段抽出の平均の分散 Var(m) = S_b²/n + S_w²/(nm)、n = B/(c₁ + mc₂) と m* = √(c₁S_w²/(c₂S_b²)) を置き、
対数正規の材積の四つの組で式と総当たり（m = 1〜200）と乱数を比べる。損の式 (式 3.1) は一般の文字で書いてある。

ここで証明した言明（S_b², S_w², c₁, c₂, B > 0、m を正の実数とみる）：
  (1) `var_min`：V(m) = (S_b² + S_w²/m)(c₁ + mc₂)/B は m* = √(c₁S_w²/(c₂S_b²)) でただ一つの最小をとる
      （m ≠ m* なら V(m*) < V(m)）。m* は予算 B によらない（B は全体を割るだけ）。
  (2) `loss_formula`：a = m*c₂/c₁ と置くと、任意の k > 0 で V(km*)/V(m*) = (1 + a(k + 1/k) + a²)/(1 + a)²。
  (3) `loss_symm`：損は k と 1/k で等しい。
足した仮定：m と区画の数 n を連続の数とみた（整数に丸める所、有限母集団の補正は入れていない）。
形式化していないもの：材積の分散の値、総当たりと乱数の表、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper980

open Real

/-- 予算 B のもとでの平均の分散。 -/
noncomputable def V (Pb Pw c₁ c₂ B m : ℝ) : ℝ := (Pb + Pw / m) * (c₁ + m * c₂) / B

/-- 最良の本数 m*。 -/
noncomputable def mstar (Pb Pw c₁ c₂ : ℝ) : ℝ := √(c₁ * Pw / (c₂ * Pb))

section

variable {Pb Pw c₁ c₂ B : ℝ} (hPb : 0 < Pb) (hPw : 0 < Pw) (h1 : 0 < c₁) (h2 : 0 < c₂) (hB : 0 < B)
include hPb hPw h1 h2 hB

omit hB in
theorem mstar_pos : 0 < mstar Pb Pw c₁ c₂ := by unfold mstar; positivity

omit hB in
theorem mstar_sq : mstar Pb Pw c₁ c₂ ^ 2 = c₁ * Pw / (c₂ * Pb) := by
  unfold mstar; rw [sq_sqrt (by positivity)]

/-- (1) m* でただ一つの最小（B によらない）。 -/
theorem var_min {m : ℝ} (hm : 0 < m) (hne : m ≠ mstar Pb Pw c₁ c₂) :
    V Pb Pw c₁ c₂ B (mstar Pb Pw c₁ c₂) < V Pb Pw c₁ c₂ B m := by
  have hs := mstar_pos hPb hPw h1 h2
  have hsq := mstar_sq hPb hPw h1 h2
  set M := mstar Pb Pw c₁ c₂
  unfold V
  apply div_lt_div_of_pos_right _ hB
  -- (Pb + Pw/m)(c₁ + m c₂) = Pb c₁ + Pw c₂ + Pb c₂ m + Pw c₁/m
  have hPw' : Pw * c₁ = Pb * c₂ * M ^ 2 := by rw [hsq]; field_simp
  have e : ∀ x, 0 < x → (Pb + Pw / x) * (c₁ + x * c₂) =
      Pb * c₁ + Pw * c₂ + Pb * c₂ * (x + M ^ 2 / x) := by
    intro x hx; field_simp; linear_combination hPw'
  rw [e M hs, e m hm]
  have hk : 0 < Pb * c₂ := by positivity
  -- M + M²/M < m + M²/m ⇔ (m − M)² > 0
  have h3 : m + M ^ 2 / m - (M + M ^ 2 / M) = (m - M) ^ 2 / m := by field_simp; ring
  have hpos : 0 < (m - M) ^ 2 / m := by
    apply div_pos _ hm; have : m - M ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have key : M + M ^ 2 / M < m + M ^ 2 / m := by linarith
  have := mul_lt_mul_of_pos_left key hk
  linarith

/-- (2) 損の式。 -/
theorem loss_formula {k : ℝ} (hk : 0 < k) :
    V Pb Pw c₁ c₂ B (k * mstar Pb Pw c₁ c₂) / V Pb Pw c₁ c₂ B (mstar Pb Pw c₁ c₂) =
      (1 + (mstar Pb Pw c₁ c₂ * c₂ / c₁) * (k + 1 / k) + (mstar Pb Pw c₁ c₂ * c₂ / c₁) ^ 2) /
        (1 + mstar Pb Pw c₁ c₂ * c₂ / c₁) ^ 2 := by
  have hs := mstar_pos hPb hPw h1 h2
  have hsq := mstar_sq hPb hPw h1 h2
  set M := mstar Pb Pw c₁ c₂
  have hPw' : Pw = Pb * c₂ * M ^ 2 / c₁ := by rw [hsq]; field_simp
  unfold V
  rw [hPw']
  field_simp
  ring

/-- (3) 損は k と 1/k で等しい。 -/
theorem loss_symm {k : ℝ} (hk : 0 < k) :
    V Pb Pw c₁ c₂ B (k * mstar Pb Pw c₁ c₂) / V Pb Pw c₁ c₂ B (mstar Pb Pw c₁ c₂) =
      V Pb Pw c₁ c₂ B ((1 / k) * mstar Pb Pw c₁ c₂) / V Pb Pw c₁ c₂ B (mstar Pb Pw c₁ c₂) := by
  rw [loss_formula hPb hPw h1 h2 hB hk, loss_formula hPb hPw h1 h2 hB (by positivity)]
  congr 2; field_simp; ring

end

end Paper980

end Yamagishi
