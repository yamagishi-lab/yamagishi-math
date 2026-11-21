/-
論文931『よく混ぜた箱を直列に分けると、押し出し流れに近づく』の格上げ（一般の形）。

原稿（931_yamagishi_splitting_a_mixed_vessel_into_tanks_in_series_approaches_plug_flow/…_jp.tex）は、
平均の滞在時間 τ を N 個の同じ完全混合槽に分けたときの一次反応の残り (1 + kτ/N)^(−N) を、kτ = 2 で
N = 1〜100 の数値と粒子 20000 個の乱数で見て、N を増やすほど押し出し流れの e^(−kτ) に近づく、と
数えている（式とアーラン分布は既知として書いている）。

ここで証明した言明（すべての x = kτ > 0）：残り R(N) = (1 + x/N)^(−N)（N ≥ 1）について
  (1) `remain_strictAnti`：R(N + 1) < R(N)（N について狭義に減る）。
  (2) `exp_lt_remain`：どの N でも R(N) > e^(−x)（押し出し流れより必ず多く残る）。
  (3) `remain_tendsto`：N → ∞ で R(N) → e^(−x)。
証明の筋：(1) は b/a = 1 + s（a = 1 + x/N・b = 1 + x/(N+1)・s = −x/((N+1)(N+x))）に、厳密な
ベルヌーイの不等式 (1+s)^(N+1) > 1 + (N+1)s = 1/a を使う（Mathlib の
`one_add_mul_self_lt_rpow_one_add`）。(2) は 1 + x/N < e^(x/N)。(3) は Mathlib の
`Real.tendsto_one_add_div_pow_exp`。
定義に置いたもの：完全混合槽の直列の残りの式 (1 + kτ/N)^(−N)（原稿の式）。
形式化していないもの：滞在時間の分散 τ²/N（アーラン分布）と、早く出る割合・遅く出る割合が N に
ついて減ること（下読みの AI の注意のとおり、ガンマ分布の分布関数の単調性が要り、ここでは扱わない）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper931

open Real Filter Topology

/-- N 個の箱の直列での一次反応の残り (1 + x/N)^(−N)。 -/
noncomputable def remain (x : ℝ) (N : ℕ) : ℝ := ((1 + x / N) ^ N)⁻¹

/-- (1 + x/N)^N は N について狭義に増える（N ≥ 1・x > 0）。 -/
theorem pow_lt_pow_succ {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    (1 + x / N) ^ N < (1 + x / (N + 1 : ℕ)) ^ (N + 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set a := 1 + x / N with ha
  set b := 1 + x / (N + 1 : ℕ) with hb
  have ha0 : 0 < a := by rw [ha]; positivity
  set s := -x / ((N + 1) * (N + x)) with hs
  have hs0 : s < 0 := by rw [hs]; apply div_neg_of_neg_of_pos (by linarith); positivity
  have hs1 : -1 ≤ s := by
    rw [hs, le_div_iff₀ (by positivity)]
    nlinarith
  have hba : b = a * (1 + s) := by
    rw [hb, ha, hs]; push_cast; field_simp; ring
  have hkey : 1 + ((N + 1 : ℕ) : ℝ) * s < (1 + s) ^ (N + 1) := by
    have h1 : (1 : ℝ) < ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := one_add_mul_self_lt_rpow_one_add hs1 hs0.ne h1
    rwa [Real.rpow_natCast] at this
  have hinv : 1 + ((N + 1 : ℕ) : ℝ) * s = a⁻¹ := by
    rw [hs, ha]; push_cast; field_simp; ring
  rw [hinv] at hkey
  rw [hba, mul_pow]
  calc a ^ N = a ^ (N + 1) * a⁻¹ := by rw [pow_succ]; field_simp
    _ < a ^ (N + 1) * (1 + s) ^ (N + 1) := mul_lt_mul_of_pos_left hkey (by positivity)

/-- (1) 残りは N について狭義に減る。 -/
theorem remain_strictAnti {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    remain x (N + 1) < remain x N := by
  unfold remain
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 : 0 < (1 + x / N) ^ N := by positivity
  exact inv_strictAnti₀ h0 (pow_lt_pow_succ hx hN)

/-- (2) どの N でも、残りは押し出し流れの e^(−x) より多い。 -/
theorem exp_lt_remain {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) : exp (-x) < remain x N := by
  unfold remain
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 1 + x / N < exp (x / N) := by
    have := Real.add_one_lt_exp (show x / N ≠ 0 by positivity)
    linarith
  have h2 : (1 + x / N) ^ N < exp (x / N) ^ N :=
    pow_lt_pow_left₀ h1 (by positivity) (by omega)
  rw [← Real.exp_natCast_mul, mul_div_cancel₀ _ hN0.ne'] at h2
  rw [Real.exp_neg]
  exact inv_strictAnti₀ (by positivity) h2

/-- (3) N → ∞ で残りは e^(−x) に近づく。 -/
theorem remain_tendsto (x : ℝ) : Tendsto (remain x) atTop (𝓝 (exp (-x))) := by
  have := (Real.tendsto_one_add_div_pow_exp x).inv₀ (Real.exp_pos x).ne'
  rw [Real.exp_neg]
  exact this

end Paper931

end Yamagishi
