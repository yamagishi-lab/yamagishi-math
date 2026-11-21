/-
論文996『足の着く時間を入れると、二重跳びには四倍より多くの高さが要る』の模型の式を、機械に確かめさせる。

原稿（996_yamagishi_with_ground_contact_time_…/…_jp.tex）の設定：
  縄を毎秒 ω 回まわし、一回の跳躍で k 回くぐり、足の着く時間を t_c とする。
  空中の時間 t = k/ω − t_c、跳ぶ高さ h = g t²/8（投げ上げ）。
  k 回のくぐりが空中に収まるには t ≥ (k − 1)/ω、つまり t_c ≤ 1/ω。
原稿の言明：
  (1) 二重÷一重 = ((2 − ω t_c)/(1 − ω t_c))²（原稿は 24 組の数値で、10⁻⁹ 以内の一致として示す）。
  (2) 足の着く時間が長いほど高さは下がり、比は上がる（四倍を超える）。
  (3) 足の着く時間が縄の一回り 1/ω より長いと跳べない。
  (4) 毎秒 2ω 回の二重と毎秒 ω 回の一重は同じ高さ。
  計算 2.1・3.1 の表の値。

書き方：模型の置き方（足の着く時間が一定・h = g t²/8・くぐりが空中に収まればよい）は原稿どおり
定義として置き、そこから出る式を、すべての正の g・ω と、跳べる範囲のすべての t_c について示した。
原稿が数値の一致で示した (1)、言葉で述べた (2)(3)(4) を、一般の式・不等式として書いた。

形式化していないもの：模型の置き方そのものの妥当さ（縄のたるみ・空気抵抗・腕の動き・足の着く時間が
高さで変わること）、実在の選手との対応、「分離子」という読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper996

/-- 空中の時間 t = k/ω − t_c。 -/
noncomputable def airTime (ω tc k : ℝ) : ℝ := k / ω - tc

/-- 跳ぶ高さ h = g t²/8。 -/
noncomputable def height (g ω tc k : ℝ) : ℝ := g * airTime ω tc k ^ 2 / 8

/-- (1) 二重と一重の高さの比は ((2 − ω t_c)/(1 − ω t_c))²（ω t_c ≠ 1、g ≠ 0、ω ≠ 0）。 -/
theorem ratio_formula (g ω tc : ℝ) (hg : g ≠ 0) (hω : ω ≠ 0) (h1 : ω * tc ≠ 1) :
    height g ω tc 2 / height g ω tc 1 = ((2 - ω * tc) / (1 - ω * tc)) ^ 2 := by
  unfold height airTime
  have h1' : 1 - ω * tc ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have e2 : 2 / ω - tc = (2 - ω * tc) / ω := by field_simp
  have e1 : 1 / ω - tc = (1 - ω * tc) / ω := by field_simp
  rw [e2, e1]
  field_simp

/-- 比を x = ω t_c の関数として見たもの。 -/
noncomputable def ratioFn (x : ℝ) : ℝ := ((2 - x) / (1 - x)) ^ 2

/-- 比は 1 + 1/(1 − x) の二乗に書ける。 -/
theorem ratioFn_eq (x : ℝ) (hx : x < 1) : ratioFn x = (1 + 1 / (1 - x)) ^ 2 := by
  unfold ratioFn
  have : 1 - x ≠ 0 := by linarith
  congr 1
  field_simp
  ring

/-- (2) 足の着く時間が無ければ比はちょうど 4（論文881）。 -/
theorem ratioFn_zero : ratioFn 0 = 4 := by norm_num [ratioFn]

/-- (2) 比は 0 ≤ x < 1 で狭義に増える（足の着く時間が長いほど比は上がる）。 -/
theorem ratioFn_strictMonoOn : StrictMonoOn ratioFn (Set.Ico 0 1) := by
  intro x hx y hy hxy
  rw [ratioFn_eq x hx.2, ratioFn_eq y hy.2]
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hy1 : 0 < 1 - y := by linarith [hy.2]
  have hlt : 1 / (1 - x) < 1 / (1 - y) := one_div_lt_one_div_of_lt hy1 (by linarith)
  have hpos : 0 < 1 + 1 / (1 - x) := by positivity
  have := pow_lt_pow_left₀ (by linarith : 1 + 1 / (1 - x) < 1 + 1 / (1 - y)) hpos.le
    (two_ne_zero)
  exact this

/-- (2) 比が四倍を超える ⇔ 足の着く時間が正（0 ≤ x < 1 の範囲で）。 -/
theorem ratio_gt_four_iff (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) : 4 < ratioFn x ↔ 0 < x := by
  constructor
  · intro h
    rcases hx0.lt_or_eq with h0 | h0
    · exact h0
    · subst h0; rw [ratioFn_zero] at h; exact absurd h (lt_irrefl 4)
  · intro h
    rw [← ratioFn_zero]
    exact ratioFn_strictMonoOn ⟨le_refl 0, by norm_num⟩ ⟨hx0, hx1⟩ h

/-- (2) 高さは、跳べる範囲 0 ≤ t_c ≤ k/ω で、足の着く時間が長いほど狭義に下がる。 -/
theorem height_strictAntiOn (g ω k : ℝ) (hg : 0 < g) :
    StrictAntiOn (fun tc => height g ω tc k) (Set.Icc 0 (k / ω)) := by
  intro x hx y hy hxy
  simp only [height, airTime]
  have h1 : 0 ≤ k / ω - y := by linarith [hy.2]
  have h2 : k / ω - y < k / ω - x := by linarith
  have := pow_lt_pow_left₀ h2 h1 two_ne_zero
  have := mul_lt_mul_of_pos_left this hg
  linarith

/-- (3) k 回のくぐりが空中に収まる条件 t ≥ (k − 1)/ω は、k によらず t_c ≤ 1/ω。 -/
theorem jump_condition (ω tc k : ℝ) (hω : 0 < ω) :
    (k - 1) / ω ≤ airTime ω tc k ↔ tc ≤ 1 / ω := by
  unfold airTime
  have : k / ω - (k - 1) / ω = 1 / ω := by field_simp; ring
  constructor <;> intro h <;> linarith

/-- (4) 毎秒 2ω 回の二重跳びの空中の時間と高さは、毎秒 ω 回の一重跳びと同じ（t_c が同じなら）。 -/
theorem double_speed_same_height (g ω tc : ℝ) (hω : ω ≠ 0) :
    airTime (2 * ω) tc 2 = airTime ω tc 1 ∧ height g (2 * ω) tc 2 = height g ω tc 1 := by
  have h : airTime (2 * ω) tc 2 = airTime ω tc 1 := by
    unfold airTime; field_simp
  exact ⟨h, by unfold height; rw [h]⟩

/-- (4) の続き（観察4.2）：同じ高さでも、跳べる足の着く時間は 1/ω から 1/(2ω) に半分になる。 -/
theorem double_speed_condition (ω tc : ℝ) (hω : 0 < ω) :
    ((2 - 1) / (2 * ω) ≤ airTime (2 * ω) tc 2 ↔ tc ≤ 1 / (2 * ω)) := by
  have := jump_condition (2 * ω) tc 2 (by positivity)
  simpa using this

/-! ### 表の値（計算 2.1・3.1） -/

/-- 計算 2.1：毎秒 2 回で足の着く時間 0・0.1・0.15・0.2・0.3 秒の比は 4・5.0625・289/49・64/9・12.25。 -/
theorem table_ratios_omega2 :
    ratioFn (2 * 0) = 4 ∧ ratioFn (2 * 0.1) = 5.0625 ∧ ratioFn (2 * 0.15) = 289 / 49 ∧
    ratioFn (2 * 0.2) = 64 / 9 ∧ ratioFn (2 * 0.3) = 12.25 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [ratioFn]

/-- 計算 3.1：毎秒 3 回・0.2 秒で 12.25、0.3 秒で 121、毎秒 4 回・0.2 秒で 36、毎秒 6 回・0.15 秒で 121。 -/
theorem table_ratios_other :
    ratioFn (3 * 0.2) = 12.25 ∧ ratioFn (3 * 0.3) = 121 ∧ ratioFn (4 * 0.2) = 36 ∧
    ratioFn (6 * 0.15) = 121 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [ratioFn]

/-- 計算 3.1：毎秒 4 回で 0.3 秒、毎秒 6 回で 0.2 秒は、一回り 1/ω より長いので跳べない。 -/
theorem table_cannot_jump :
    ¬ ((0.3 : ℝ) ≤ 1 / 4) ∧ ¬ ((0.2 : ℝ) ≤ 1 / 6) := by norm_num

/-- 計算 2.1：g = 9.81、毎秒 2 回で、足の着く時間 0 の一重 0.3065625 m、0.3 秒の一重 0.04905 m、
0 の二重 1.22625 m。 -/
theorem table_heights :
    height 9.81 2 0 1 = 0.3065625 ∧ height 9.81 2 0.3 1 = 0.04905 ∧
      height 9.81 2 0 2 = 1.22625 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [height, airTime]

end Paper996

end Yamagishi
