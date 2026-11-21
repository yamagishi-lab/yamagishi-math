/-
論文391『有義波高は、平均でもなければ最大でもない』の格上げ（一般の形・芯）。

原稿（391_yamagishi_the_significant_wave_is_neither_the_mean_nor_the_maximum/…_jp.tex）は、
H_rms = 1 のレイリー分布から 400 万個を抽出して平均・上位 1/3・上位 1/10 の値を数え、独立な N 波の
最大の期待値を漸近の式で N = 100, 1080, 3000 について出し、1080 波を 2000 回模擬している。

ここで証明した言明（すべての自然数 N ≥ 1）：
  (1) `one_sub_pow_eq`：1 − (1 − u)^N = Σ_{k=1}^{N} (−1)^(k+1) C(N, k) u^k（二項展開）。
  (2) `Emax_eq`：独立な N 波（どれも P(H ≤ h) = 1 − e^(−h²)）の最大の期待値は、厳密に
      E[H_max] = (√π/2) Σ_{k=1}^{N} (−1)^(k+1) C(N, k)/√k。
定義に置いたもの：最大の期待値を、非負の確率変数の期待値の公式 E[H_max] = ∫₀^∞ P(H_max > h) dh と、
独立性から P(H_max ≤ h) = (1 − e^(−h²))^N を使って、∫₀^∞ (1 − (1 − e^(−h²))^N) dh と置いた。
形式化していないもの：上位 1/q の平均の式（erfc を使う）、漸近の式 √(ln N) + γ/(2√(ln N))、
乱数の模擬。(2) の式の値は Lean の外で多倍長で数えた：N = 1080 で 2.740697（H_rms 単位）、
H_s = 1.41573 H_rms で割って 1.9359。同じ N の漸近の式は 2.752064（H_rms 単位）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper391

open Real MeasureTheory Finset Set

/-- (1) 二項展開。 -/
theorem one_sub_pow_eq (u : ℝ) (N : ℕ) :
    1 - (1 - u) ^ N = ∑ k ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (k + 1) * (N.choose k : ℝ) * u ^ k := by
  have h := (add_pow (-u) 1 N)
  simp only [one_pow, mul_one] at h
  rw [show (1 : ℝ) - u = -u + 1 by ring, h]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by
    ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  rw [sub_add_cancel_left, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [neg_pow, pow_succ]
  ring

/-- 最大の期待値（定義）。 -/
noncomputable def Emax (N : ℕ) : ℝ := ∫ h in Ioi (0 : ℝ), (1 - (1 - exp (-h ^ 2)) ^ N)

/-- (2) 厳密な交代和。 -/
theorem Emax_eq (N : ℕ) :
    Emax N = √π / 2 * ∑ k ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (k + 1) * (N.choose k : ℝ) / √k := by
  unfold Emax
  have hpt : ∀ h : ℝ, 1 - (1 - exp (-h ^ 2)) ^ N =
      ∑ k ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (k + 1) * (N.choose k : ℝ) * exp (-(k : ℝ) * h ^ 2) := by
    intro h
    rw [one_sub_pow_eq]
    apply Finset.sum_congr rfl
    intro k _
    rw [← exp_natCast_mul]; ring_nf
  simp_rw [hpt]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    rw [integral_const_mul, integral_gaussian_Ioi, sqrt_div pi_pos.le]
    field_simp
  · intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    exact ((integrable_exp_neg_mul_sq hkpos).const_mul _).integrableOn

end Paper391

end Yamagishi
