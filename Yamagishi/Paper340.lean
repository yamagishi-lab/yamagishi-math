/-
論文340『最短の道は、航海者が舵を切る道ではない』の格上げ（同じ緯度の二点で一般の形・芯だけ）。

原稿（340_yamagishi_the_shorter_path_is_not_the_one_a_navigator_steers/…_jp.tex）は、地球を球とし、
大圏を球面余弦定理、航程線をメルカトル図法上の直線として、東京から出る 5 航路、差が 0 になる二例
（同じ経度・赤道上）、北緯 70 度を東西に半周する一例（1.54 倍）を数えている。比の一般の式や、
比の上限は書いていない。

ここで証明した言明（単位球。半径は比で消える）：
  (1) `gc_same_lat`：同じ緯度 φ・経度差 Λ（0 ≤ Λ ≤ π）の二点の大圏距離は 2 arcsin(cos φ sin(Λ/2))。
  (2) `gc_le_rhumb_same_lat`・`gc_lt_rhumb_iff`：同じ緯度なら大圏 ≤ 航程線（緯度線の弧 Λ cos φ）で、
      0 < Λ ≤ π、|φ| < π/2 のとき、等号は φ = 0（赤道）のときだけ。
  (3) `rhumb_lt_pi_div_two_mul_gc`：同じ緯度なら、航程線 < (π/2)·大圏（arcsin x > x とジョルダンの不等式）。
  (4) `half_pi_sin_mul_gc_lt_rhumb`・`pi_div_two_best`：経度差 π（東西に半周）では
      (π/2)·sin φ·大圏 < 航程線。したがって π/2 より小さいどの定数も上限にならない（π/2 は最良）。
  (5) `meridian_eq`：同じ経度（Λ = 0）では、航程線 = 大圏 = |φ₂ − φ₁|。
定義に置いたもの：大圏距離（球面余弦定理の arccos の式）、航程線の長さ（メルカトルの緯度
ψ = ln tan(π/4 + φ/2) を使う標準の式。同じ緯度では緯度線の弧 Λ cos φ）。
形式化していないもの：一般の（緯度の違う）二点で航程線 < (π/2)·大圏（下読みの AI も数値で
確かめただけで、まだ証明が無い）、大圏が最短であること、航程線の微分幾何（測地曲率）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper340

open Real Set

/-- 単位球の大圏距離（球面余弦定理）。Λ は経度差。 -/
noncomputable def gc (φ₁ φ₂ Λ : ℝ) : ℝ :=
  arccos (sin φ₁ * sin φ₂ + cos φ₁ * cos φ₂ * cos Λ)

/-- メルカトルの緯度 ψ = ln tan(π/4 + φ/2)。 -/
noncomputable def mercator (φ : ℝ) : ℝ := log (tan (π / 4 + φ / 2))

/-- 単位球の航程線の長さ（経度差 Λ ≥ 0 の側）。同じ緯度では緯度線の弧。 -/
noncomputable def rhumb (φ₁ φ₂ Λ : ℝ) : ℝ :=
  if φ₁ = φ₂ then Λ * cos φ₁
  else |φ₂ - φ₁| * √(1 + (Λ / (mercator φ₂ - mercator φ₁)) ^ 2)

theorem rhumb_same_lat (φ Λ : ℝ) : rhumb φ φ Λ = Λ * cos φ := by simp [rhumb]

theorem cos_two_mul_arcsin {y : ℝ} (h0 : -1 ≤ y) (h1 : y ≤ 1) :
    cos (2 * arcsin y) = 1 - 2 * y ^ 2 := by
  rw [cos_two_mul, cos_sq', sin_arcsin h0 h1]; ring

/-- (1) 同じ緯度の大圏距離。 -/
theorem gc_same_lat {φ Λ : ℝ} (hφ : |φ| ≤ π / 2) (hΛ0 : 0 ≤ Λ) (hΛ1 : Λ ≤ π) :
    gc φ φ Λ = 2 * arcsin (cos φ * sin (Λ / 2)) := by
  have hc0 : 0 ≤ cos φ := cos_nonneg_of_neg_pi_div_two_le_of_le (by
    linarith [neg_abs_le φ]) (by linarith [le_abs_self φ])
  have hc1 : cos φ ≤ 1 := cos_le_one φ
  have hs0 : 0 ≤ sin (Λ / 2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs1 : sin (Λ / 2) ≤ 1 := sin_le_one _
  set y := cos φ * sin (Λ / 2) with hy
  have hy0 : 0 ≤ y := mul_nonneg hc0 hs0
  have hy1 : y ≤ 1 := by nlinarith
  have harg : sin φ * sin φ + cos φ * cos φ * cos Λ = cos (2 * arcsin y) := by
    rw [cos_two_mul_arcsin (by linarith) hy1, hy]
    have hΛ : cos Λ = 1 - 2 * sin (Λ / 2) ^ 2 := by
      rw [show Λ = 2 * (Λ / 2) by ring, cos_two_mul, cos_sq']; ring_nf
    rw [hΛ]
    nlinarith [sin_sq_add_cos_sq φ]
  unfold gc
  rw [harg, arccos_cos]
  · exact mul_nonneg (by norm_num) (arcsin_nonneg.2 hy0)
  · linarith [arcsin_le_pi_div_two y]

theorem cos_pos_of_abs_lt {φ : ℝ} (hφ : |φ| < π / 2) : 0 < cos φ :=
  cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le φ], by linarith [le_abs_self φ]⟩

/-- 鍵：0 < c < 1、0 < x ≤ π/2 なら c sin x < sin(cx)（sin の狭義の凹性）。 -/
theorem mul_sin_lt_sin_mul {c x : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hx0 : 0 < x) (hx1 : x ≤ π / 2) :
    c * sin x < sin (c * x) := by
  have := strictConcaveOn_sin_Icc.2 (x := x) (y := 0) ⟨hx0.le, by linarith [pi_pos]⟩
    ⟨le_rfl, pi_pos.le⟩ hx0.ne' hc0 (by linarith : (0:ℝ) < 1 - c) (by ring)
  simpa using this

/-- (2) 同じ緯度なら大圏 ≤ 航程線。 -/
theorem gc_le_rhumb_same_lat {φ Λ : ℝ} (hφ : |φ| < π / 2) (hΛ0 : 0 ≤ Λ) (hΛ1 : Λ ≤ π) :
    gc φ φ Λ ≤ rhumb φ φ Λ := by
  rw [gc_same_lat hφ.le hΛ0 hΛ1, rhumb_same_lat]
  have hc0 := cos_pos_of_abs_lt hφ
  have hc1 : cos φ ≤ 1 := cos_le_one φ
  have hx : cos φ * (Λ / 2) ≤ π / 2 := by nlinarith
  -- c sin x ≤ sin(cx)（凹性）、arcsin(sin(cx)) = cx
  have hle : cos φ * sin (Λ / 2) ≤ sin (cos φ * (Λ / 2)) := by
    rcases eq_or_lt_of_le hc1 with h | h
    · rw [h]; simp
    rcases eq_or_lt_of_le hΛ0 with h' | h'
    · rw [← h']; simp
    exact (mul_sin_lt_sin_mul hc0 h (by linarith) (by linarith)).le
  have hs0 : 0 ≤ sin (Λ / 2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have := arcsin_le_arcsin hle
  rw [arcsin_sin (by nlinarith) hx] at this
  linarith

/-- (2) 等号は赤道のときだけ（0 < Λ ≤ π）。 -/
theorem gc_lt_rhumb_iff {φ Λ : ℝ} (hφ : |φ| < π / 2) (hΛ0 : 0 < Λ) (hΛ1 : Λ ≤ π) :
    gc φ φ Λ < rhumb φ φ Λ ↔ φ ≠ 0 := by
  rw [gc_same_lat hφ.le hΛ0.le hΛ1, rhumb_same_lat]
  have hc0 := cos_pos_of_abs_lt hφ
  constructor
  · intro h hφ0
    rw [hφ0, cos_zero, one_mul, mul_one, arcsin_sin (by linarith [pi_pos]) (by linarith)] at h
    linarith
  · intro hφ0
    have hc1 : cos φ < 1 := by
      rcases lt_or_eq_of_le (cos_le_one φ) with h | h
      · exact h
      · exfalso
        have := (cos_eq_one_iff_of_lt_of_lt (x := φ) (by linarith [neg_abs_le φ, pi_pos])
          (by linarith [le_abs_self φ, pi_pos])).1 h
        exact hφ0 this
    have hx : cos φ * (Λ / 2) ≤ π / 2 := by nlinarith
    have hlt := mul_sin_lt_sin_mul hc0 hc1 (by linarith : 0 < Λ / 2) (by linarith)
    have hs0 : 0 ≤ sin (Λ / 2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have := arcsin_lt_arcsin (by nlinarith) hlt (sin_le_one _)
    rw [arcsin_sin (by nlinarith) hx] at this
    linarith

/-- arcsin y > y（0 < y ≤ 1）。 -/
theorem lt_arcsin_self {y : ℝ} (h0 : 0 < y) (h1 : y ≤ 1) : y < arcsin y := by
  have := sin_lt (arcsin_pos.2 h0)
  rwa [sin_arcsin (by linarith) h1] at this

/-- (3) 同じ緯度なら、航程線 < (π/2)·大圏。 -/
theorem rhumb_lt_pi_div_two_mul_gc {φ Λ : ℝ} (hφ : |φ| < π / 2) (hΛ0 : 0 < Λ) (hΛ1 : Λ ≤ π) :
    rhumb φ φ Λ < π / 2 * gc φ φ Λ := by
  rw [gc_same_lat hφ.le hΛ0.le hΛ1, rhumb_same_lat]
  have hc0 := cos_pos_of_abs_lt hφ
  have hc1 : cos φ ≤ 1 := cos_le_one φ
  have hs := mul_le_sin (by linarith : (0:ℝ) ≤ Λ / 2) (by linarith)
  have hspos : 0 < sin (Λ / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs1 : sin (Λ / 2) ≤ 1 := sin_le_one _
  have hy := lt_arcsin_self (mul_pos hc0 hspos) (by nlinarith)
  -- Λ c = π·c·(2/π)(Λ/2) ≤ π c sin(Λ/2) < π arcsin(c sin(Λ/2))
  have hpi := pi_pos
  have hΛs : Λ ≤ π * sin (Λ / 2) := by
    have := mul_le_mul_of_nonneg_left hs hpi.le
    rwa [show π * (2 / π * (Λ / 2)) = Λ by field_simp] at this
  have h1 : Λ * cos φ ≤ π * (cos φ * sin (Λ / 2)) := by
    nlinarith [mul_le_mul_of_nonneg_left hΛs hc0.le]
  nlinarith

/-- (4) 東西に半周（Λ = π）では (π/2)·sin φ·大圏 < 航程線（0 < φ < π/2）。 -/
theorem half_pi_sin_mul_gc_lt_rhumb {φ : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) :
    π / 2 * sin φ * gc φ φ π < rhumb φ φ π := by
  have hφ : |φ| < π / 2 := by rw [abs_of_pos h0]; exact h1
  rw [gc_same_lat hφ.le pi_pos.le le_rfl, rhumb_same_lat, sin_pi_div_two, mul_one]
  have hc0 := cos_pos_of_abs_lt hφ
  have hsφ : 0 < sin φ := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
  have hc1 : cos φ < 1 := by
    have := sin_sq_add_cos_sq φ
    nlinarith
  have harc : arcsin (cos φ) < π / 2 := by
    have := arcsin_lt_arcsin (by linarith) hc1 le_rfl
    rwa [arcsin_one] at this
  have htan := lt_tan (arcsin_pos.2 hc0) harc
  rw [tan_arcsin] at htan
  have hsq : √(1 - cos φ ^ 2) = sin φ := by
    rw [show 1 - cos φ ^ 2 = sin φ ^ 2 by linarith [sin_sq_add_cos_sq φ]]
    exact sqrt_sq hsφ.le
  rw [hsq, lt_div_iff₀ hsφ] at htan
  have hpi := pi_pos
  nlinarith

/-- (4) π/2 は最良：π/2 より小さいどの M にも、M·大圏 < 航程線となる同じ緯度の二点がある。 -/
theorem pi_div_two_best {M : ℝ} (hM : M < π / 2) :
    ∃ φ, 0 < φ ∧ φ < π / 2 ∧ M * gc φ φ π < rhumb φ φ π := by
  have hpi := pi_pos
  set r := (2 * M / π + 1) / 2 with hr
  by_cases hM0 : M ≤ 0
  · refine ⟨π / 4, by positivity, by linarith, ?_⟩
    have hφ : |π / 4| < π / 2 := by rw [abs_of_pos (by positivity)]; linarith
    have hg : 0 ≤ gc (π / 4) (π / 4) π := by
      rw [gc_same_lat hφ.le hpi.le le_rfl]
      exact mul_nonneg (by norm_num) (arcsin_nonneg.2
        (mul_nonneg (cos_pos_of_abs_lt hφ).le (by rw [sin_pi_div_two]; norm_num)))
    have : 0 < rhumb (π / 4) (π / 4) π := by
      rw [rhumb_same_lat]; exact mul_pos hpi (cos_pos_of_abs_lt hφ)
    nlinarith
  push Not at hM0
  have hr0 : 0 < r := by rw [hr]; positivity
  have h2M : 2 * M / π < 1 := by rw [div_lt_one hpi]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  refine ⟨arcsin r, arcsin_pos.2 hr0, ?_, ?_⟩
  · have := arcsin_lt_arcsin (by linarith) hr1 le_rfl
    rwa [arcsin_one] at this
  · have h0 := arcsin_pos.2 hr0
    have h1 : arcsin r < π / 2 := by
      have := arcsin_lt_arcsin (by linarith) hr1 le_rfl
      rwa [arcsin_one] at this
    have key := half_pi_sin_mul_gc_lt_rhumb h0 h1
    rw [sin_arcsin (by linarith) hr1.le] at key
    have hφ : |arcsin r| < π / 2 := by rw [abs_of_pos h0]; exact h1
    have hg : 0 < gc (arcsin r) (arcsin r) π := by
      rw [gc_same_lat hφ.le hpi.le le_rfl, sin_pi_div_two, mul_one]
      exact mul_pos (by norm_num) (arcsin_pos.2 (cos_pos_of_abs_lt hφ))
    have hMr : M < π / 2 * r := by
      rw [hr]; field_simp; linarith
    nlinarith

/-- (5) 同じ経度では、航程線 = 大圏 = |φ₂ − φ₁|（|φ| ≤ π/2）。 -/
theorem meridian_eq {φ₁ φ₂ : ℝ} (h1 : |φ₁| ≤ π / 2) (h2 : |φ₂| ≤ π / 2) :
    rhumb φ₁ φ₂ 0 = |φ₂ - φ₁| ∧ gc φ₁ φ₂ 0 = |φ₂ - φ₁| := by
  constructor
  · unfold rhumb
    split_ifs with h
    · simp [h]
    · simp
  · unfold gc
    rw [cos_zero, mul_one, show sin φ₁ * sin φ₂ + cos φ₁ * cos φ₂ = cos (φ₂ - φ₁) by
      rw [cos_sub]; ring, ← cos_abs, arccos_cos (abs_nonneg _)]
    have := abs_sub (φ₂) (φ₁)
    linarith [abs_nonneg φ₁, abs_nonneg φ₂]

end Paper340

end Yamagishi
