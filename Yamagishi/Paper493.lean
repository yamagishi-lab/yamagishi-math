/-
論文493『長さは折れ線の極限で定義できるが、面積は多面体の極限で定義できない』の格上げ（一般の形）。

原稿（493_yamagishi_length_yes_area_no/…_jp.tex）は、半径 r・高さ h の円柱に内接するシュワルツの提灯の
面積 A(m, n) = 2mn r sin(π/n) √((h/m)² + (r(1 − cos(π/n)))²) を、r = h = 1 で m = n、m = n²、m = n³ の
三つの刻み方について n = 50, 200, 800 で数え、m = n² の値を閉じた式 2π√(1 + π⁴/4) と照合している。

ここで証明した言明（r, h > 0。刻み方 m, n は任意の添字の族で、n → ∞、m > 0）：
  (1) `lantern_tendsto`：m/n² → q（0 ≤ q < ∞）なら A(m, n) → 2πr√(h² + π⁴r²q²/4)。
  (2) `lantern_tendsto_atTop`：m/n² → ∞ なら A(m, n) → ∞（発散）。
  (3) `limit_eq_area_iff`：極限が円柱の正しい面積 2πrh になる ⇔ q = 0。
  部品 `n_sin_tendsto`・`n_sq_one_sub_cos_tendsto`：n sin(π/n) → π、n²(1 − cos(π/n)) → π²/2。
形式化していないもの：m/n² に極限が無い刻み方で A に極限が無いこと、周長の収束、数表。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper493

open Real Filter Topology

/-- 提灯の面積（原稿の式）。 -/
noncomputable def A (r h m n : ℝ) : ℝ :=
  2 * m * n * r * sin (π / n) * √((h / m) ^ 2 + (r * (1 - cos (π / n))) ^ 2)

/-- m > 0 での書き換え。 -/
theorem A_eq {r h m n : ℝ} (hm : 0 < m) :
    A r h m n = 2 * r * (n * sin (π / n)) * √(h ^ 2 + r ^ 2 * (m * (1 - cos (π / n))) ^ 2) := by
  unfold A
  have : √((h / m) ^ 2 + (r * (1 - cos (π / n))) ^ 2) * m =
      √(h ^ 2 + r ^ 2 * (m * (1 - cos (π / n))) ^ 2) := by
    have key : h ^ 2 + r ^ 2 * (m * (1 - cos (π / n))) ^ 2 =
        ((h / m) ^ 2 + (r * (1 - cos (π / n))) ^ 2) * m ^ 2 := by
      field_simp
    rw [key, sqrt_mul' _ (sq_nonneg m), sqrt_sq hm.le]
  rw [← this]; ring

theorem tendsto_inv_atTop_zero' : Tendsto (fun x : ℝ => π / x) atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact tendsto_const_nhds.div_atTop tendsto_id
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact (div_pos pi_pos hx).ne'

/-- 部品：x sin(π/x) → π（x → ∞）。 -/
theorem n_sin_tendsto : Tendsto (fun x : ℝ => x * sin (π / x)) atTop (𝓝 π) := by
  have h := (continuous_sinc.tendsto 0).comp
    (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun x : ℝ => π / x) atTop (𝓝 0))
  rw [sinc_zero] at h
  have h2 := h.const_mul π
  rw [mul_one] at h2
  apply h2.congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp]
  rw [sinc_of_ne_zero (div_pos pi_pos hx).ne']
  field_simp

/-- 部品：x²(1 − cos(π/x)) → π²/2。 -/
theorem n_sq_one_sub_cos_tendsto :
    Tendsto (fun x : ℝ => x ^ 2 * (1 - cos (π / x))) atTop (𝓝 (π ^ 2 / 2)) := by
  have h := (continuous_sinc.tendsto 0).comp
    (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun x : ℝ => π / 2 / x) atTop (𝓝 0))
  rw [sinc_zero] at h
  have h2 := (h.pow 2).const_mul (π ^ 2 / 2)
  rw [one_pow, mul_one] at h2
  apply h2.congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp]
  have hne : π / 2 / x ≠ 0 := (div_pos (div_pos pi_pos two_pos) hx).ne'
  rw [sinc_of_ne_zero hne]
  have hc : 1 - cos (π / x) = 2 * sin (π / 2 / x) ^ 2 := by
    rw [show π / x = 2 * (π / 2 / x) by ring, cos_two_mul, cos_sq']; ring
  rw [hc]
  field_simp

/-- (1) m/n² → q なら A → 2πr√(h² + π⁴r²q²/4)。 -/
theorem lantern_tendsto {α : Type*} {l : Filter α} {r h q : ℝ} {m n : α → ℝ}
    (hn : Tendsto n l atTop) (hm : ∀ᶠ j in l, 0 < m j)
    (hq : Tendsto (fun j => m j / n j ^ 2) l (𝓝 q)) :
    Tendsto (fun j => A r h (m j) (n j)) l
      (𝓝 (2 * π * r * √(h ^ 2 + π ^ 4 * r ^ 2 * q ^ 2 / 4))) := by
  have h1 := n_sin_tendsto.comp hn
  have h2 := n_sq_one_sub_cos_tendsto.comp hn
  -- m(1 − cos(π/n)) = (m/n²)·n²(1 − cos(π/n)) → q π²/2
  have h3 : Tendsto (fun j => m j * (1 - cos (π / n j))) l (𝓝 (q * (π ^ 2 / 2))) := by
    apply (hq.mul h2).congr'
    filter_upwards [hn.eventually (eventually_gt_atTop 0)] with j hj
    simp only [Function.comp]
    field_simp
  have h4 : Tendsto (fun j => 2 * r * (n j * sin (π / n j)) *
      √(h ^ 2 + r ^ 2 * (m j * (1 - cos (π / n j))) ^ 2)) l
      (𝓝 (2 * r * π * √(h ^ 2 + r ^ 2 * (q * (π ^ 2 / 2)) ^ 2))) := by
    apply Tendsto.mul (tendsto_const_nhds.mul h1)
    exact (tendsto_const_nhds.add (tendsto_const_nhds.mul (h3.pow 2))).sqrt
  have hval : 2 * r * π * √(h ^ 2 + r ^ 2 * (q * (π ^ 2 / 2)) ^ 2) =
      2 * π * r * √(h ^ 2 + π ^ 4 * r ^ 2 * q ^ 2 / 4) := by
    congr 1
    · ring
    · congr 1; ring
  rw [← hval]
  apply h4.congr'
  filter_upwards [hm] with j hj
  rw [A_eq hj]

/-- (2) m/n² → ∞ なら A → ∞。 -/
theorem lantern_tendsto_atTop {α : Type*} {l : Filter α} {r h : ℝ} (hr : 0 < r) {m n : α → ℝ}
    (hn : Tendsto n l atTop) (hm : ∀ᶠ j in l, 0 < m j)
    (hq : Tendsto (fun j => m j / n j ^ 2) l atTop) :
    Tendsto (fun j => A r h (m j) (n j)) l atTop := by
  have h1 := n_sin_tendsto.comp hn
  have h2 := n_sq_one_sub_cos_tendsto.comp hn
  have h3 : Tendsto (fun j => m j * (1 - cos (π / n j))) l atTop := by
    have := hq.atTop_mul_pos (by positivity : (0 : ℝ) < π ^ 2 / 2) h2
    apply this.congr'
    filter_upwards [hn.eventually (eventually_gt_atTop 0)] with j hj
    simp only [Function.comp]
    field_simp
  -- 下から 2r·(n sin(π/n))·r·m(1 − cos(π/n)) で押さえる
  have h4 : Tendsto (fun j => (2 * r * (n j * sin (π / n j))) * (r * (m j * (1 - cos (π / n j)))))
      l atTop := by
    apply Tendsto.pos_mul_atTop (by positivity : 0 < 2 * r * π) (tendsto_const_nhds.mul h1)
    exact h3.const_mul_atTop hr
  apply tendsto_atTop_mono' l _ h4
  have hsin : ∀ᶠ j in l, 0 ≤ n j * sin (π / n j) := by
    filter_upwards [hn.eventually (eventually_gt_atTop 1)] with j hj
    apply mul_nonneg (by linarith)
    apply sin_nonneg_of_nonneg_of_le_pi (div_pos pi_pos (by linarith)).le
    rw [div_le_iff₀ (by linarith)]; nlinarith [pi_pos]
  filter_upwards [hm, hsin, h3.eventually (eventually_ge_atTop 0)] with j hj hs hc
  rw [A_eq hj]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [show r * (m j * (1 - cos (π / n j))) = √((r * (m j * (1 - cos (π / n j)))) ^ 2) by
    rw [sqrt_sq (by positivity)]]
  apply sqrt_le_sqrt
  nlinarith [sq_nonneg h]

/-- (3) 極限が正しい面積 2πrh ⇔ q = 0（r, h > 0、q ≥ 0）。 -/
theorem limit_eq_area_iff {r h q : ℝ} (hr : 0 < r) (hh : 0 < h) (hq : 0 ≤ q) :
    2 * π * r * √(h ^ 2 + π ^ 4 * r ^ 2 * q ^ 2 / 4) = 2 * π * r * h ↔ q = 0 := by
  have hpi := pi_pos
  rw [mul_right_inj' (by positivity), sqrt_eq_iff_eq_sq (by positivity) hh.le]
  constructor
  · intro heq
    have h4 : π ^ 4 * r ^ 2 * q ^ 2 = 0 := by linarith
    have hq2 : q ^ 2 = 0 := by
      rcases mul_eq_zero.1 h4 with h5 | h5
      · exfalso; have : 0 < π ^ 4 * r ^ 2 := by positivity
        linarith
      · exact h5
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hq2
  · rintro rfl; ring

end Paper493

end Yamagishi
