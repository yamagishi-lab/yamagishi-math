/-
論文141『限界が存在するのは、二つの力が同じ指数を持つからである』の格上げ（一般の形・芯）。

原稿（141_yamagishi_same_exponent_no_radius/…_jp.tex）は、状態方程式 P = Kρ^Γ と尺度の釣合い
Kρ^Γ/R ∼ GMρ/R² から、Γ = 5/3, 3/2, 4/3 の三つの値について M の R 依存性を記号計算で出し
（検算 2.1 の表）、「Γ = 4/3 では質量が半径に依存しない」と述べる。レーン＝エムデン方程式は n = 3
だけ数値積分している。

ここで証明した言明（M, R, K, G > 0、Γ は任意の実数。比例 ∼ は等号で置いた）：
  (1) `balance_log`：ρ = M/R³ で Kρ^Γ/R = GMρ/R² ⇔ (Γ − 2) ln M = ln(G/K) + (3Γ − 4) ln R。
      `balance_power`：Γ ≠ 2 なら ln M = ln(G/K)/(Γ − 2) + ((3Γ − 4)/(Γ − 2)) ln R、すなわち
      M ∝ R^((3Γ−4)/(Γ−2))。`exponent_zero_iff`：その指数が 0 ⇔ Γ = 4/3。
      `gamma_two`：Γ = 2 では釣合いが半径を ln R = ln(K/G)/2 に決め、M によらない（原稿に無い対の端）。
  (2) `exponent_in_n`：Γ = 1 + 1/n（n ≠ 0, 1）で (3Γ − 4)/(Γ − 2) = (3 − n)/(1 − n)。
  (3) `homology`：レーン＝エムデンの相似（長さの尺度 α² = c₀ρ_c^(1/n − 1)、R = αξ₁、M = 4πα³ρ_c ω₁、
      ξ₁ と ω₁ は解の定数）から、n ≠ 0, 1 なら ln M = 定数 + ((3 − n)/(1 − n)) ln R がすべての ρ_c で成り立つ。
      `homology_n_one`：n = 1 では R は ρ_c によらない。`homology_mass_const_iff`：M が ρ_c によらない
      （二つの ρ_c で等しい）⇔ n = 3。
足した仮定・定義に置いたもの：尺度の釣合いの比例を等号とした。レーン＝エムデン方程式の解の存在と
有限の零点 ξ₁（n < 5 で在る）、ω₁ = −ξ₁²θ′(ξ₁) は入力の定数とした。形式化していないもの：
レーン＝エムデン方程式そのもの、チャンドラセカール質量の数値、安定性。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper141

open Real

/-- (1) 尺度の釣合いの対数の形。 -/
theorem balance_log {K G M R Γ : ℝ} (hK : 0 < K) (hG : 0 < G) (hM : 0 < M) (hR : 0 < R) :
    K * (M / R ^ 3) ^ Γ / R = G * M * (M / R ^ 3) / R ^ 2 ↔
      (Γ - 2) * log M = log (G / K) + (3 * Γ - 4) * log R := by
  have hρ : 0 < M / R ^ 3 := by positivity
  have hL : 0 < K * (M / R ^ 3) ^ Γ / R := by positivity
  have hRt : 0 < G * M * (M / R ^ 3) / R ^ 2 := by positivity
  have key : log (K * (M / R ^ 3) ^ Γ / R) = log K + Γ * (log M - 3 * log R) - log R := by
    rw [log_div (by positivity) hR.ne', log_mul hK.ne' (by positivity), log_rpow hρ,
      log_div hM.ne' (by positivity), log_pow]; push_cast; ring
  have key2 : log (G * M * (M / R ^ 3) / R ^ 2) = log G + 2 * log M - 5 * log R := by
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) hρ.ne',
      log_mul hG.ne' hM.ne', log_div hM.ne' (by positivity), log_pow, log_pow]; push_cast; ring
  rw [log_div hG.ne' hK.ne']
  constructor
  · intro h
    have := congrArg log h
    rw [key, key2] at this
    linarith
  · intro h
    apply log_injOn_pos (Set.mem_Ioi.2 hL) (Set.mem_Ioi.2 hRt)
    rw [key, key2]
    linarith

/-- (1) Γ ≠ 2 なら冪の法則 M ∝ R^((3Γ−4)/(Γ−2))。 -/
theorem balance_power {K G M R Γ : ℝ} (hK : 0 < K) (hG : 0 < G) (hM : 0 < M) (hR : 0 < R)
    (hΓ : Γ ≠ 2) (h : K * (M / R ^ 3) ^ Γ / R = G * M * (M / R ^ 3) / R ^ 2) :
    log M = log (G / K) / (Γ - 2) + (3 * Γ - 4) / (Γ - 2) * log R := by
  have := (balance_log hK hG hM hR).1 h
  have hne : Γ - 2 ≠ 0 := sub_ne_zero.2 hΓ
  field_simp
  linarith

/-- (1) 指数が 0 ⇔ Γ = 4/3。 -/
theorem exponent_zero_iff {Γ : ℝ} (hΓ : Γ ≠ 2) : (3 * Γ - 4) / (Γ - 2) = 0 ↔ Γ = 4 / 3 := by
  have hne : Γ - 2 ≠ 0 := sub_ne_zero.2 hΓ
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hne
  · intro h; left; rw [h]; norm_num

/-- (1) Γ = 2 では釣合いが半径を決める（M によらない）。 -/
theorem gamma_two {K G M R : ℝ} (hK : 0 < K) (hG : 0 < G) (hM : 0 < M) (hR : 0 < R)
    (h : K * (M / R ^ 3) ^ (2 : ℝ) / R = G * M * (M / R ^ 3) / R ^ 2) :
    log R = log (K / G) / 2 := by
  have := (balance_log hK hG hM hR).1 h
  rw [log_div hG.ne' hK.ne'] at this
  rw [log_div hK.ne' hG.ne']
  linarith

/-- (2) n で書いた指数。 -/
theorem exponent_in_n {n : ℝ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    (3 * (1 + 1 / n) - 4) / ((1 + 1 / n) - 2) = (3 - n) / (1 - n) := by
  have h1 : 1 - n ≠ 0 := sub_ne_zero.2 (Ne.symm hn1)
  have h2 : (1 + 1 / n) - 2 ≠ 0 := by
    intro h
    have : 1 / n = 1 := by linarith
    rw [div_eq_one_iff_eq hn0] at this
    exact hn1 this.symm
  rw [div_eq_div_iff h2 h1]
  field_simp
  ring

/-- (3) レーン＝エムデンの相似から M と R の関係（定数 C は ρ_c によらない）。 -/
theorem homology {n c₀ ξ₁ ω₁ ρc α R M : ℝ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hc : 0 < c₀)
    (hξ : 0 < ξ₁) (hω : 0 < ω₁) (hρ : 0 < ρc) (hα : 0 < α)
    (hα2 : α ^ 2 = c₀ * ρc ^ (1 / n - 1)) (hR : R = α * ξ₁) (hM : M = 4 * π * α ^ 3 * ρc * ω₁) :
    log M = (log (4 * π * ω₁) - n / (1 - n) * log c₀ - (3 - n) / (1 - n) * log ξ₁) +
      (3 - n) / (1 - n) * log R := by
  have hpi := pi_pos
  have h1 : 1 - n ≠ 0 := sub_ne_zero.2 (Ne.symm hn1)
  have hlα : 2 * log α = log c₀ + (1 / n - 1) * log ρc := by
    have := congrArg log hα2
    rw [log_pow, log_mul hc.ne' (rpow_pos_of_pos hρ _).ne', log_rpow hρ] at this
    push_cast at this; linarith
  have hlR : log R = log α + log ξ₁ := by rw [hR, log_mul hα.ne' hξ.ne']
  have hlM : log M = log (4 * π * ω₁) + 3 * log α + log ρc := by
    rw [hM, show 4 * π * α ^ 3 * ρc * ω₁ = (4 * π * ω₁) * (α ^ 3 * ρc) by ring,
      log_mul (by positivity) (by positivity), log_mul (by positivity) hρ.ne', log_pow]
    push_cast; ring
  rw [hlM, hlR]
  have hnn : (1 / n - 1) * n = 1 - n := by field_simp
  have e : (1 / n - 1) * log ρc * n = (1 - n) * log ρc := by rw [mul_right_comm, hnn]
  have h3 : 2 * log α * n = log c₀ * n + (1 - n) * log ρc := by
    linear_combination n * hlα + e
  have : log ρc = n * (2 * log α - log c₀) / (1 - n) := by
    field_simp
    linarith
  rw [this]
  field_simp
  ring

/-- n = 1 なら R = √c₀ ξ₁ は ρ_c によらない。 -/
theorem homology_n_one {c₀ ξ₁ ρc α : ℝ} (hα : 0 < α)
    (hα2 : α ^ 2 = c₀ * ρc ^ (1 / (1 : ℝ) - 1)) : α * ξ₁ = √c₀ * ξ₁ := by
  have : α ^ 2 = c₀ := by rw [hα2]; norm_num
  rw [← this, sqrt_sq hα.le]

/-- 中心密度 ρ_c の関数としての質量（α = √(c₀ρ_c^(1/n − 1))）。 -/
noncomputable def Mfun (n c₀ ω₁ ρ : ℝ) : ℝ := 4 * π * (√(c₀ * ρ ^ (1 / n - 1))) ^ 3 * ρ * ω₁

theorem log_Mfun {n c₀ ω₁ ρ : ℝ} (hn : n ≠ 0) (hc : 0 < c₀) (hω : 0 < ω₁) (hρ : 0 < ρ) :
    log (Mfun n c₀ ω₁ ρ) = log (4 * π * ω₁) + 3 / 2 * log c₀ + (3 - n) / (2 * n) * log ρ := by
  have hpi := pi_pos
  have hin : 0 < c₀ * ρ ^ (1 / n - 1) := mul_pos hc (rpow_pos_of_pos hρ _)
  unfold Mfun
  rw [show 4 * π * √(c₀ * ρ ^ (1 / n - 1)) ^ 3 * ρ * ω₁ =
      (4 * π * ω₁) * (√(c₀ * ρ ^ (1 / n - 1)) ^ 3 * ρ) by ring,
    log_mul (by positivity) (by positivity), log_mul (by positivity) hρ.ne', log_pow,
    log_sqrt hin.le, log_mul hc.ne' (rpow_pos_of_pos hρ _).ne', log_rpow hρ]
  field_simp; ring

/-- (3) 質量が ρ_c によらない ⇔ n = 3（0 < n）。 -/
theorem homology_mass_const_iff {n c₀ ω₁ : ℝ} (hn : 0 < n) (hc : 0 < c₀) (hω : 0 < ω₁) :
    (∀ ρ₁ ρ₂ : ℝ, 0 < ρ₁ → 0 < ρ₂ → Mfun n c₀ ω₁ ρ₁ = Mfun n c₀ ω₁ ρ₂) ↔ n = 3 := by
  have hn0 : n ≠ 0 := hn.ne'
  constructor
  · intro h
    have h12 := congrArg log (h 1 (exp 1) one_pos (exp_pos 1))
    rw [log_Mfun hn0 hc hω one_pos, log_Mfun hn0 hc hω (exp_pos 1), log_one, log_exp] at h12
    have : (3 - n) / (2 * n) = 0 := by linarith
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · linarith
    · exfalso; exact hn0 (by linarith)
  · rintro rfl ρ₁ ρ₂ h1 h2
    have hpi := pi_pos
    apply log_injOn_pos (Set.mem_Ioi.2 (by unfold Mfun; positivity))
      (Set.mem_Ioi.2 (by unfold Mfun; positivity))
    rw [log_Mfun (by norm_num) hc hω h1, log_Mfun (by norm_num) hc hω h2]
    norm_num

end Paper141

end Yamagishi
