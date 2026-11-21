/-
論文1036『光の球をよその系の同時で切ると、発光点を焦点とする離心率 β の楕円になる』の格上げ（一般の形）。

原稿（1036_yamagishi_light_sphere_cut_by_another_simultaneity_is_an_ellipse/…_jp.tex）は、
β = 0.1, 0.3, 0.5, 0.6, 0.9, 0.99 の六つで 1440 点を当てはめ、離心率 β・長半径 γ・短半径 1・
中心 βγ・焦点が発光点・極方程式 r = (1/γ)/(1 − β cos θ) を三つの数値の道で確かめている。

ここで証明した言明（0 ≤ β < 1、T > 0、c = 1）：
  点の位置を、動く向き x と、それに直交する向きの距離 ρ = |y|（d 次元なら y は d − 1 次元の
  ベクトル、ρ はその長さ）で書く。光円錐 t = √(x² + ρ²) を、動く系の同時面 t′ = γ(t − βx) = T で切る。
  (1) `on_cut_iff`：点が切り口にある ⇔ √(x² + ρ²) = T/γ + βx。
  (2) `cut_iff_ellipse`：それ ⇔ (x − βγT)²/(γT)² + ρ²/T² = 1（中心 βγT、長半径 γT、短半径 T の回転楕円体）。
  (3) `polar_form`：極座標 x = r cos θ、ρ = r sin θ（r ≥ 0）で、切り口 ⇔ r = (T/γ)/(1 − β cos θ)
      = T·D(θ)（D はドップラー因子 1/(γ(1 − β cos θ))）。
  (4) `eccentricity`：離心率 √(1 − (短半径/長半径)²) = β。`focus_at_origin`：焦点 中心 − 長半径×離心率 = 0。
  (5) `vertices`：二つの頂点の発光点からの距離は kT と T/k（k = √((1 + β)/(1 − β))）、積は T²。
足した仮定：光の速さ 1、標準的に同期した二つの系（ローレンツ変換 t′ = γ(t − βx)）。
形式化していないもの：回転楕円体の体積が半径 T の球の γ 倍であること（一つの軸だけ γ 倍に伸ばす
一次写像の行列式が γ であることから出るが、測度の像の形では書いていない）、論文1026・491 の数との照合、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1036

open Real

/-- γ = 1/√(1 − β²)。 -/
noncomputable def γ (β : ℝ) : ℝ := 1 / √(1 - β ^ 2)

section

variable {β T : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
include hβ0 hβ1

theorem sq_pos' : 0 < 1 - β ^ 2 := by nlinarith

theorem γ_pos : 0 < γ β := by unfold γ; have := sq_pos' hβ0 hβ1; positivity

theorem γ_sq : γ β ^ 2 * (1 - β ^ 2) = 1 := by
  unfold γ; have h := sq_pos' hβ0 hβ1
  rw [div_pow, sq_sqrt h.le]; field_simp

/-- (1) 切り口：t = √(x² + ρ²) かつ γ(t − βx) = T ⇔ √(x² + ρ²) = T/γ + βx。 -/
theorem on_cut_iff (x ρ : ℝ) :
    (∃ t, t = √(x ^ 2 + ρ ^ 2) ∧ γ β * (t - β * x) = T) ↔ √(x ^ 2 + ρ ^ 2) = T / γ β + β * x := by
  have hg := γ_pos hβ0 hβ1
  constructor
  · rintro ⟨t, rfl, h⟩
    rw [← h]; field_simp; ring
  · intro h
    refine ⟨_, rfl, ?_⟩
    rw [h]; field_simp; ring

/-- (2) 切り口は回転楕円体 (x − βγT)²/(γT)² + ρ²/T² = 1。 -/
theorem cut_iff_ellipse (hT : 0 < T) (x ρ : ℝ) :
    √(x ^ 2 + ρ ^ 2) = T / γ β + β * x ↔
      (x - β * γ β * T) ^ 2 / (γ β * T) ^ 2 + ρ ^ 2 / T ^ 2 = 1 := by
  have hg := γ_pos hβ0 hβ1
  have hs := γ_sq hβ0 hβ1
  have hgT : 0 < γ β * T := mul_pos hg hT
  have e : T / γ β = T * γ β * (1 - β ^ 2) := by
    field_simp; nlinarith [hs]
  rw [e, div_add_div _ _ (by positivity) (by positivity), div_eq_one_iff_eq (by positivity)]
  set g := γ β
  set u := 1 - β ^ 2 with hu
  constructor
  · intro h
    have hnn : 0 ≤ T * g * u + β * x := by rw [← h]; exact sqrt_nonneg _
    rw [sqrt_eq_iff_eq_sq (by positivity) hnn] at h
    linear_combination (T ^ 2 * g ^ 2) * h +
        (T ^ 2 * (-x ^ 2 + 2 * β * g * T * x + g ^ 2 * u * T ^ 2)) * hs
  · intro h
    have h2 : (x - β * g * T) ^ 2 ≤ (g * T) ^ 2 := by
      have h1 : (x - β * g * T) ^ 2 * T ^ 2 ≤ (g * T) ^ 2 * T ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg ρ) (sq_nonneg (g * T))]
      exact le_of_mul_le_mul_right h1 (by positivity)
    have hx : β * g * T - g * T ≤ x := by
      by_contra hc; push Not at hc
      nlinarith
    have hnn : 0 ≤ T * g * u + β * x := by
      have h1' : 0 ≤ T * g * (1 - β) := by have : 0 < 1 - β := by linarith
                                           positivity
      nlinarith [mul_le_mul_of_nonneg_left hx hβ0]
    rw [sqrt_eq_iff_eq_sq (by positivity) hnn]
    have hT2 : T ^ 2 ≠ 0 := by positivity
    have h' : (x - β * g * T) ^ 2 + ρ ^ 2 * g ^ 2 = g ^ 2 * T ^ 2 := by
      apply mul_right_cancel₀ hT2; linear_combination h
    linear_combination (1 - β ^ 2) * h' - ρ ^ 2 * hs

/-- (3) 極方程式：r ≥ 0、x = r cos θ で、r = T/γ + β r cos θ ⇔ r = (T/γ)/(1 − β cos θ)。 -/
theorem polar_form (r θ : ℝ) :
    r = T / γ β + β * (r * cos θ) ↔ r = (T / γ β) / (1 - β * cos θ) := by
  have hc : 0 < 1 - β * cos θ := by
    have := cos_le_one θ; have := neg_one_le_cos θ; nlinarith
  rw [eq_div_iff (ne_of_gt hc)]
  constructor <;> intro h <;> linarith

/-- 動径は T × ドップラー因子 1/(γ(1 − β cos θ))。 -/
theorem polar_is_doppler (θ : ℝ) :
    (T / γ β) / (1 - β * cos θ) = T * (1 / (γ β * (1 - β * cos θ))) := by
  have hc : 0 < 1 - β * cos θ := by
    have := cos_le_one θ; have := neg_one_le_cos θ; nlinarith
  have := γ_pos hβ0 hβ1
  field_simp

/-- (4) 離心率は β。 -/
theorem eccentricity (hT : 0 < T) : √(1 - (T / (γ β * T)) ^ 2) = β := by
  have hg := γ_pos hβ0 hβ1
  have hs := γ_sq hβ0 hβ1
  have : 1 - (T / (γ β * T)) ^ 2 = β ^ 2 := by
    field_simp; nlinarith [hs]
  rw [this, sqrt_sq hβ0]

omit hβ0 hβ1 in
/-- (4) 焦点の一つは発光点：中心 − 長半径 × 離心率 = 0。 -/
theorem focus_at_origin : β * γ β * T - (γ β * T) * β = 0 := by ring

/-- (5) 頂点は kT と T/k、積は T²。 -/
theorem vertices :
    γ β * T * (1 + β) = √((1 + β) / (1 - β)) * T ∧
    γ β * T * (1 - β) = T / √((1 + β) / (1 - β)) ∧
    (γ β * T * (1 + β)) * (γ β * T * (1 - β)) = T ^ 2 := by
  have hs := γ_sq hβ0 hβ1
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 + β := by linarith
  have hg := γ_pos hβ0 hβ1
  -- γ(1 + β) = √((1+β)/(1−β))
  have hk : γ β * (1 + β) = √((1 + β) / (1 - β)) := by
    rw [eq_comm, sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    have : γ β ^ 2 = 1 / ((1 - β) * (1 + β)) := by
      field_simp; nlinarith [hs]
    field_simp
    nlinarith [this, hs]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hk]; ring
  · rw [← hk]
    field_simp
    linear_combination T * hs
  · linear_combination T ^ 2 * hs

end

end Paper1036

end Yamagishi
