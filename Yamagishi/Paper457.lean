/-
論文457『風味と速さを取り替えるには、係数が二つ要る』の Q10 の模型を、一般の形で機械に確かめさせる（格上げ）。

原稿（457_yamagishi_trading_flavour_for_speed_needs_two_coefficients/…_jp.tex）の設定：
  速度 v(T) = Q₁₀^((T − T_r)/10)、T_r = 27 ℃。増殖（膨らみ）の Q₁₀ = 2.0、風味の生成の Q₁₀ = q。
  同じ膨らみに達したときの風味の量 F = t · q^((T − T_r)/10)（t はそこまでに要した時間）。
原稿が示している事：
  4 ℃ と 35 ℃ の二つの温度で、q = 1.5・2.0・2.5 の三つの値を数値で計算し、q = 1.5 なら低温が勝ち、
  2.0 なら等しく、2.5 なら高温が勝つことを示す。時間比 8.5742 が 2^3.1 と一致すること、
  時間と速度の積が 2 で保存されることも数値で示す。一般の q での一行の導出は書いていない。

ここで証明した一般の言明（増殖の係数 Q > 0、風味の係数 q > 0、基準の時間 t_r > 0、任意の温度）：
  (1) 同じ膨らみに要る時間は t(T) = t_r Q^(−(T − T_r)/10)、時間と速度の積は t_r で一定。
  (2) 二つの温度の時間比は t(T₁)/t(T₂) = Q^((T₂ − T₁)/10)（原稿の 2^3.1）。
  (3) 風味の量は F(T) = t_r (q/Q)^((T − T_r)/10)。
  (4) T₁ < T₂ のとき、低温が勝つ ⇔ q < Q、等しい ⇔ q = Q、高温が勝つ ⇔ q > Q。
      どの二つの温度でも、時間の差の大きさによらない（原稿の観察3.6）。
  (5) F が温度によらない ⇔ q = Q。
足した仮定：原稿の数値の Q = 2 を一般の Q > 0 に、三つの q を一般の q > 0 に、二つの温度を
任意の T₁ < T₂ に広げた。模型の置き方（速度が Q₁₀ の指数で書けること）は原稿のまま。

形式化していないもの：Q₁₀ = 2.0 などの値の妥当さ（原稿も仮定と明記）、「一晩に収まる」などの読み、
小数の数表（9.8492 時間など）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper457

open Real

/-- 速度 v(T) = Q^((T − T_r)/10)。 -/
noncomputable def rate (Q Tr T : ℝ) : ℝ := Q ^ ((T - Tr) / 10)

/-- 同じ膨らみに要る時間（基準温度で t_r）。 -/
noncomputable def time (Q Tr tr T : ℝ) : ℝ := tr / rate Q Tr T

/-- 同じ膨らみに達したときの風味の量 F = t · q^((T − T_r)/10)。 -/
noncomputable def flavour (Q q Tr tr T : ℝ) : ℝ := time Q Tr tr T * rate q Tr T

/-- (1) 時間と速度の積は t_r で一定（原稿の観察2.6）、基準温度で時間は t_r（観察2.2）。 -/
theorem time_mul_rate (Q Tr tr T : ℝ) (hQ : 0 < Q) :
    time Q Tr tr T * rate Q Tr T = tr ∧ time Q Tr tr Tr = tr := by
  have h : rate Q Tr T ≠ 0 := (rpow_pos_of_pos hQ _).ne'
  refine ⟨by unfold time; field_simp, by simp [time, rate]⟩

/-- (2) 二つの温度の時間比は Q^((T₂ − T₁)/10)（原稿の 2^((35−4)/10) = 2^3.1）。 -/
theorem time_ratio (Q Tr tr T1 T2 : ℝ) (hQ : 0 < Q) (htr : tr ≠ 0) :
    time Q Tr tr T1 / time Q Tr tr T2 = Q ^ ((T2 - T1) / 10) := by
  unfold time rate
  have h1 : Q ^ ((T1 - Tr) / 10) ≠ 0 := (rpow_pos_of_pos hQ _).ne'
  have h2 : Q ^ ((T2 - Tr) / 10) ≠ 0 := (rpow_pos_of_pos hQ _).ne'
  rw [show (T2 - T1) / 10 = (T2 - Tr) / 10 - (T1 - Tr) / 10 by ring, rpow_sub hQ]
  field_simp

/-- (3) 風味の量は t_r (q/Q)^((T − T_r)/10)。 -/
theorem flavour_eq (Q q Tr tr T : ℝ) (hQ : 0 < Q) (hq : 0 < q) :
    flavour Q q Tr tr T = tr * (q / Q) ^ ((T - Tr) / 10) := by
  unfold flavour time rate
  rw [div_rpow hq.le hQ.le]
  ring

/-- (4) T₁ < T₂ のとき：低温 T₁ が勝つ ⇔ q < Q。 -/
theorem low_wins_iff (Q q Tr tr T1 T2 : ℝ) (hQ : 0 < Q) (hq : 0 < q) (htr : 0 < tr)
    (hT : T1 < T2) :
    flavour Q q Tr tr T2 < flavour Q q Tr tr T1 ↔ q < Q := by
  rw [flavour_eq Q q Tr tr T1 hQ hq, flavour_eq Q q Tr tr T2 hQ hq,
    mul_lt_mul_iff_of_pos_left htr]
  have hx : (T1 - Tr) / 10 < (T2 - Tr) / 10 := by linarith
  have hb : 0 < q / Q := div_pos hq hQ
  constructor
  · intro h
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt | heq
    · have h1 : 1 < q / Q := (one_lt_div hQ).mpr hlt
      have := rpow_lt_rpow_of_exponent_lt h1 hx
      linarith
    · rw [← heq, div_self hQ.ne', one_rpow, one_rpow] at h
      exact lt_irrefl _ h
  · intro h
    have h1 : q / Q < 1 := (div_lt_one hQ).mpr h
    exact rpow_lt_rpow_of_exponent_gt hb h1 hx

/-- (4) T₁ < T₂ のとき：高温 T₂ が勝つ ⇔ q > Q。 -/
theorem high_wins_iff (Q q Tr tr T1 T2 : ℝ) (hQ : 0 < Q) (hq : 0 < q) (htr : 0 < tr)
    (hT : T1 < T2) :
    flavour Q q Tr tr T1 < flavour Q q Tr tr T2 ↔ Q < q := by
  rw [flavour_eq Q q Tr tr T1 hQ hq, flavour_eq Q q Tr tr T2 hQ hq,
    mul_lt_mul_iff_of_pos_left htr]
  have hx : (T1 - Tr) / 10 < (T2 - Tr) / 10 := by linarith
  have hb : 0 < q / Q := div_pos hq hQ
  constructor
  · intro h
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt | heq
    · have h1 : q / Q < 1 := (div_lt_one hQ).mpr hlt
      have := rpow_lt_rpow_of_exponent_gt hb h1 hx
      linarith
    · rw [heq, div_self hQ.ne', one_rpow, one_rpow] at h
      exact lt_irrefl _ h
  · intro h
    have h1 : 1 < q / Q := (one_lt_div hQ).mpr h
    exact rpow_lt_rpow_of_exponent_lt h1 hx

/-- (4) T₁ < T₂ のとき：引き分け ⇔ q = Q。 -/
theorem draw_iff (Q q Tr tr T1 T2 : ℝ) (hQ : 0 < Q) (hq : 0 < q) (htr : 0 < tr)
    (hT : T1 < T2) :
    flavour Q q Tr tr T1 = flavour Q q Tr tr T2 ↔ q = Q := by
  constructor
  · intro h
    rcases lt_trichotomy q Q with hlt | heq | hgt
    · have := (low_wins_iff Q q Tr tr T1 T2 hQ hq htr hT).mpr hlt; linarith
    · exact heq
    · have := (high_wins_iff Q q Tr tr T1 T2 hQ hq htr hT).mpr hgt; linarith
  · rintro rfl
    rw [flavour_eq _ _ Tr tr T1 hQ hQ, flavour_eq _ _ Tr tr T2 hQ hQ, div_self hQ.ne', one_rpow,
      one_rpow]

/-- (5) 風味の量が温度によらない ⇔ q = Q（時間の差がどれだけあっても、係数が等しければ同じ）。 -/
theorem flavour_const_iff (Q q Tr tr : ℝ) (hQ : 0 < Q) (hq : 0 < q) (htr : 0 < tr) :
    (∀ T1 T2, flavour Q q Tr tr T1 = flavour Q q Tr tr T2) ↔ q = Q := by
  constructor
  · intro h
    exact (draw_iff Q q Tr tr 0 1 hQ hq htr one_pos).mp (h 0 1)
  · intro h T1 T2
    rcases lt_trichotomy T1 T2 with hlt | heq | hgt
    · exact (draw_iff Q q Tr tr T1 T2 hQ hq htr hlt).mpr h
    · rw [heq]
    · exact ((draw_iff Q q Tr tr T2 T1 hQ hq htr hgt).mpr h).symm

/-- 原稿の場合：Q = 2、4 ℃ と 35 ℃。q = 1.5 なら低温、q = 2.5 なら高温が勝つ、q = 2 で引き分け。 -/
theorem paper_case (tr : ℝ) (htr : 0 < tr) :
    flavour 2 1.5 27 tr 35 < flavour 2 1.5 27 tr 4 ∧
    flavour 2 2.5 27 tr 4 < flavour 2 2.5 27 tr 35 ∧
    flavour 2 2 27 tr 4 = flavour 2 2 27 tr 35 := by
  refine ⟨(low_wins_iff 2 1.5 27 tr 4 35 (by norm_num) (by norm_num) htr (by norm_num)).mpr
      (by norm_num), (high_wins_iff 2 2.5 27 tr 4 35 (by norm_num) (by norm_num) htr
      (by norm_num)).mpr (by norm_num), (draw_iff 2 2 27 tr 4 35 (by norm_num) (by norm_num) htr
      (by norm_num)).mpr rfl⟩

end Paper457

end Yamagishi
