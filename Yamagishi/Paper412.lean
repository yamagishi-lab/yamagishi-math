/-
論文412『「一番近い」は、距離を決めるまで決まらない』の格上げ（芯だけ）。

原稿（412_yamagishi_nearest_is_not_defined_until_the_distance_is/…_jp.tex）は、12 個の母点で
ユークリッド距離と碁盤目距離の割り当ての食い違い 12.96 パーセントを格子で数え、平均辺数は
n = 10, 100, 1000 で上限の式 6 − 12/n に数を入れている。観察 4.5 は「二つの距離が同じ割り当てに
なるのは特別な並びのときだけ」と述べる。

ここで証明した言明：
  (1) `avg_degree_le`：頂点 n ≥ 3 の単純グラフで辺が 3n − 6 本以下なら、平均次数 2E/n ≤ 6 − 12/n < 6
      （握手の補題から）。
  (2) `collinear_same_assignment`：母点がすべて一本の水平線 y = 0 の上にあれば、平面のどの点 p でも、
      二つの母点 s, s′ について「ユークリッド距離で s が s′ より近い（以下）」⇔「碁盤目距離で s が s′
      より近い（以下）」。したがって二つの図は同じ割り当てになる（観察 4.5 の「特別な並び」の一例）。
形式化していないもの：ボロノイ領域の隣接グラフが平面的であること（Mathlib に平面グラフと
オイラーの公式が無い）、したがって辺 ≤ 3n − 6 そのもの。碁盤目距離の退化の扱い、格子の数え上げ。
(1) は平面性を仮定に置いた形で、芯だけ。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper412

open Real

/-- (1) 辺 ≤ 3n − 6 なら平均次数 ≤ 6 − 12/n < 6。 -/
theorem avg_degree_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : 3 ≤ Fintype.card V)
    (hE : G.edgeFinset.card + 6 ≤ 3 * Fintype.card V) :
    ((∑ v, G.degree v : ℕ) : ℝ) / Fintype.card V ≤ 6 - 12 / Fintype.card V ∧
      ((∑ v, G.degree v : ℕ) : ℝ) / Fintype.card V < 6 := by
  rw [G.sum_degrees_eq_twice_card_edges]
  have hn0 : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hE' : ((G.edgeFinset.card : ℕ) : ℝ) + 6 ≤ 3 * (Fintype.card V : ℝ) := by exact_mod_cast hE
  constructor
  · rw [div_le_iff₀ hn0, sub_mul, div_mul_cancel₀ _ hn0.ne']
    push_cast; linarith
  · rw [div_lt_iff₀ hn0]
    push_cast; linarith

/-- 平面の点と距離。 -/
noncomputable def dE (p s : ℝ × ℝ) : ℝ := √((p.1 - s.1) ^ 2 + (p.2 - s.2) ^ 2)
noncomputable def d1 (p s : ℝ × ℝ) : ℝ := |p.1 - s.1| + |p.2 - s.2|

/-- (2) 母点が y = 0 の上なら、二つの距離で近さの順が同じ。 -/
theorem collinear_same_assignment (p : ℝ × ℝ) {a b : ℝ} :
    dE p (a, 0) ≤ dE p (b, 0) ↔ d1 p (a, 0) ≤ d1 p (b, 0) := by
  unfold dE d1
  simp only [sub_zero]
  rw [sqrt_le_sqrt_iff (by positivity), add_le_add_iff_right, add_le_add_iff_right,
    ← sq_abs (p.1 - a), ← sq_abs (p.1 - b)]
  exact pow_le_pow_iff_left₀ (abs_nonneg _) (abs_nonneg _) (by norm_num)

end Paper412

end Yamagishi
