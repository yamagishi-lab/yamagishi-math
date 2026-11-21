/-
論文298『勝率 99.9999% の戦略の期待値は、ちょうど 0 である』の格上げ（一般の形）。

原稿（298_yamagishi_the_fence_is_capital_not_probability/…_jp.tex）は、公平な賭け（勝率 1/2）で
資金 2^k − 1 の倍賭けの期待値が k によらず 0 になることを代数で示し（検算 2.3）、k = 1〜40 の表、
k = 20 の標準偏差 1024、ルーレット（p = 18/37）の k = 5, 10, 20 の数値を出す。
不利な賭けの閉じた形は書いていない。

ここで証明した言明（勝率 p ≤ 1、q = 1 − p、配当 1 倍、k 回まで倍賭け）：
  (1) `ev_closed`：期待値 EV = (1 − q^k)·(+1) + q^k·(−(2^k − 1)) = 1 − (2q)^k。
  (2) `ev_zero_iff`：k ≥ 1 のとき EV = 0 ⇔ p = 1/2（一つの k でも、すべての k でも同じ）。
      `ev_zero_all_iff`：（すべての k ≥ 1 で EV = 0）⇔ p = 1/2。
  (3) `ev_tendsto_bot`：p < 1/2 なら k → ∞ で EV → −∞。
      `ev_tendsto_one`：p > 1/2 なら k → ∞ で EV → 1。
      `ev_strictAnti`：p < 1/2 なら EV は k について狭義に減る。
  (4) `var_fair`：公平な場合の分散は 2^k − 1（k = 20 で標準偏差 √(2^20 − 1) ≈ 1024）。
  (5) `roulette`：p = 18/37 で EV = 1 − (38/37)^k。
足した仮定：一回ごとの勝ち負けが独立（k 回以内に勝つ確率 1 − q^k）。模型の利得 +1 と −(2^k − 1) を定義に置いた。
形式化していないもの：表と乱数の値、資金と破滅の解釈、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper298

open Filter Topology

/-- 期待値：k 回以内に勝てば +1、k 連敗で −(2^k − 1)。 -/
noncomputable def EV (p : ℝ) (k : ℕ) : ℝ :=
    (1 - (1 - p) ^ k) * 1 + (1 - p) ^ k * (-((2 : ℝ) ^ k - 1))

/-- 利得の二乗の期待値。 -/
noncomputable def EV2 (p : ℝ) (k : ℕ) : ℝ :=
    (1 - (1 - p) ^ k) * 1 ^ 2 + (1 - p) ^ k * ((2 : ℝ) ^ k - 1) ^ 2

/-- (1) EV = 1 − (2q)^k。 -/
theorem ev_closed (p : ℝ) (k : ℕ) : EV p k = 1 - (2 * (1 - p)) ^ k := by
  unfold EV; rw [mul_pow]; ring

/-- (2) k ≥ 1 なら EV = 0 ⇔ p = 1/2（p ≤ 1 だけで足りる）。 -/
theorem ev_zero_iff {p : ℝ} (hp1 : p ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    EV p k = 0 ↔ p = 1 / 2 := by
  rw [ev_closed, sub_eq_zero, eq_comm]
  have hq : 0 ≤ 2 * (1 - p) := by linarith
  constructor
  · intro h
    have := (pow_eq_one_iff_of_nonneg hq (by omega)).mp h
    linarith
  · intro h; rw [h]; norm_num

theorem ev_zero_all_iff {p : ℝ} (hp1 : p ≤ 1) :
    (∀ k : ℕ, 1 ≤ k → EV p k = 0) ↔ p = 1 / 2 :=
  ⟨fun h => (ev_zero_iff hp1 le_rfl).mp (h 1 le_rfl),
   fun h _ hk => (ev_zero_iff hp1 hk).mpr h⟩

/-- (3) p < 1/2 なら EV → −∞。 -/
theorem ev_tendsto_bot {p : ℝ} (hp : p < 1 / 2) : Tendsto (EV p) atTop atBot := by
  have h1 : 1 < 2 * (1 - p) := by linarith
  have := tendsto_pow_atTop_atTop_of_one_lt h1
  have h2 : Tendsto (fun k : ℕ => 1 - (2 * (1 - p)) ^ k) atTop atBot :=
    tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot.comp this) |>.congr
        (fun k => by simp; ring)
  exact h2.congr (fun k => (ev_closed p k).symm)

/-- (3) p > 1/2（p ≤ 1）なら EV → 1。 -/
theorem ev_tendsto_one {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) : Tendsto (EV p) atTop (𝓝 1) := by
  have h0 : 0 ≤ 2 * (1 - p) := by linarith
  have h1 : 2 * (1 - p) < 1 := by linarith
  have := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub this
  rw [sub_zero] at h2
  exact h2.congr (fun k => (ev_closed p k).symm)

/-- (3) p < 1/2 なら EV は k について狭義に減る。 -/
theorem ev_strictAnti {p : ℝ} (hp : p < 1 / 2) : StrictAnti (EV p) := by
  have h1 : 1 < 2 * (1 - p) := by linarith
  intro a b hab
  rw [ev_closed, ev_closed]
  have := pow_lt_pow_right₀ h1 hab
  linarith

/-- (4) 公平な場合の分散は 2^k − 1。 -/
theorem var_fair (k : ℕ) : EV2 (1 / 2) k - EV (1 / 2) k ^ 2 = (2 : ℝ) ^ k - 1 := by
  have h0 : EV (1 / 2) k = 0 := by rw [ev_closed]; norm_num
  rw [h0]
  unfold EV2
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have : (1 - (1 : ℝ) / 2) ^ k = 1 / 2 ^ k := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, div_pow, one_pow]
  rw [this]
  field_simp
  ring

/-- (5) ルーレット p = 18/37：EV = 1 − (38/37)^k。 -/
theorem roulette (k : ℕ) : EV (18 / 37) k = 1 - (38 / 37 : ℝ) ^ k := by
  rw [ev_closed]; norm_num

end Paper298

end Yamagishi
