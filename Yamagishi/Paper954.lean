/-
論文954『当て推量は、上下法が追う水準をずらす』の格上げ（芯だけ）。

原稿（954_yamagishi_guessing_shifts_the_level_an_up_down_method_tracks/…_jp.tex）は、当て推量 γ の
観察者 p(x) = γ + (1 − γ)Φ(x) に「k 回続けて正しければ下げる」規則を当て、はい・いいえ・2 択・
4 択と k = 1〜3 の九つの組で、刺激が集まる目標の点（p^k = 1/2 となる点）の式と乱数の観察者を
数え、「目標の点が有るのは床（当て推量の水準）が目標より下のときだけ」と述べている。

ここで証明した言明（芯だけ）：Φ は連続で狭義に増え、−∞ で 0、+∞ で 1 に近づく任意の関数
（正規分布の分布関数に限らない）、0 ≤ γ < 1、k ≥ 1。
  (1) `target_exists_iff`：p(x)^k = 1/2 となる x が在る ⇔ γ^k < 1/2
      （⇔ γ < (1/2)^(1/k) = 2^(−1/k)、`pow_lt_half_iff`）。在ればただ一つ（`target_unique`）。
  (2) `floor_limit`：x → −∞ で、下がる確率 p(x)^k は γ^k に近づく（三つの場合分けの境目の量）。
形式化していないもの：刺激の位置の鎖が γ < 2^(−1/k) で正再帰、γ = 2^(−1/k) で零再帰、
γ > 2^(−1/k) で過渡的、の三つに分かれること（フォスターの判定・ラムペルティの判定が要り、
Mathlib に道具が無いため止めた）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper954

open Filter Topology Set

/-- 正しく答える確率。 -/
def p (Φ : ℝ → ℝ) (γ x : ℝ) : ℝ := γ + (1 - γ) * Φ x

variable {Φ : ℝ → ℝ} {γ : ℝ} {k : ℕ}

theorem Φ_pos (hm : StrictMono Φ) (hbot : Tendsto Φ atBot (𝓝 0)) (x : ℝ) : 0 < Φ x := by
  by_contra h
  push Not at h
  have h1 : Φ (x - 1) < Φ x := hm (by linarith)
  have h2 : (0 : ℝ) ≤ Φ (x - 1) :=
    le_of_tendsto hbot ((eventually_le_atBot (x - 1)).mono fun z hz => hm.monotone hz)
  linarith

theorem p_strictMono (hm : StrictMono Φ) (hγ1 : γ < 1) : StrictMono (p Φ γ) := by
  intro x y hxy
  unfold p
  have := hm hxy
  have : 0 < 1 - γ := by linarith
  nlinarith

theorem gamma_lt_p (hm : StrictMono Φ) (hbot : Tendsto Φ atBot (𝓝 0)) (hγ1 : γ < 1) (x : ℝ) :
    γ < p Φ γ x := by
  unfold p
  have := Φ_pos hm hbot x
  have : 0 < 1 - γ := by linarith
  nlinarith

/-- (2) x → −∞ で p(x)^k → γ^k。 -/
theorem floor_limit (hbot : Tendsto Φ atBot (𝓝 0)) :
    Tendsto (fun x => p Φ γ x ^ k) atBot (𝓝 (γ ^ k)) := by
  have : Tendsto (p Φ γ) atBot (𝓝 γ) := by
    have := (tendsto_const_nhds (x := 1 - γ)).mul hbot
    have h2 := (tendsto_const_nhds (x := γ)).add this
    simp only [mul_zero, add_zero] at h2
    exact h2
  exact this.pow k

theorem top_limit (htop : Tendsto Φ atTop (𝓝 1)) :
    Tendsto (fun x => p Φ γ x ^ k) atTop (𝓝 1) := by
  have : Tendsto (p Φ γ) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := 1 - γ)).mul htop
    have h2 := (tendsto_const_nhds (x := γ)).add this
    simp only [mul_one, add_sub_cancel] at h2
    exact h2
  simpa using this.pow k

/-- (1) 目標の点が在る ⇔ γ^k < 1/2。 -/
theorem target_exists_iff (hc : Continuous Φ) (hm : StrictMono Φ)
    (hbot : Tendsto Φ atBot (𝓝 0)) (htop : Tendsto Φ atTop (𝓝 1))
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hk : 1 ≤ k) :
    (∃ x, p Φ γ x ^ k = 1 / 2) ↔ γ ^ k < 1 / 2 := by
  constructor
  · rintro ⟨x, hx⟩
    rw [← hx]
    exact pow_lt_pow_left₀ (gamma_lt_p hm hbot hγ1 x) hγ0 (by omega)
  · intro h
    have e1 : ∀ᶠ x in atBot, p Φ γ x ^ k < 1 / 2 :=
      (floor_limit hbot).eventually (Iio_mem_nhds h)
    have e2 : ∀ᶠ x in atTop, 1 / 2 < p Φ γ x ^ k :=
      (top_limit htop).eventually (Ioi_mem_nhds (by norm_num))
    obtain ⟨x0, hx0⟩ := e1.exists
    obtain ⟨x1, hx1, hx01⟩ := (e2.and (eventually_ge_atTop x0)).exists
    have hcont : ContinuousOn (fun x => p Φ γ x ^ k) (Icc x0 x1) :=
      ((continuous_const.add (continuous_const.mul hc)).pow k).continuousOn
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc hx01 hcont ⟨hx0.le, hx1.le⟩
    exact ⟨x, hx⟩

/-- 目標の点はただ一つ。 -/
theorem target_unique (hm : StrictMono Φ) (hbot : Tendsto Φ atBot (𝓝 0))
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hk : 1 ≤ k) {x y : ℝ}
    (hx : p Φ γ x ^ k = 1 / 2) (hy : p Φ γ y ^ k = 1 / 2) : x = y := by
  have hpos : ∀ z, 0 ≤ p Φ γ z := fun z => hγ0.trans (gamma_lt_p hm hbot hγ1 z).le
  have hsm : StrictMono (fun z => p Φ γ z ^ k) := fun a b hab =>
    pow_lt_pow_left₀ (p_strictMono hm hγ1 hab) (hpos a) (by omega)
  exact hsm.injective (hx.trans hy.symm)

/-- γ^k < 1/2 ⇔ γ < (1/2)^(1/k)（= 2^(−1/k)）。 -/
theorem pow_lt_half_iff (hγ0 : 0 ≤ γ) (hk : 1 ≤ k) :
    γ ^ k < 1 / 2 ↔ γ < (1 / 2 : ℝ) ^ ((k : ℝ)⁻¹) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Real.lt_rpow_inv_iff_of_pos hγ0 (by norm_num) hk', Real.rpow_natCast]

end Paper954

end Yamagishi
