/-
論文205『最も短い囲いは、いつも円板とはかぎらない』の格上げ（芯だけ：三つの候補の比較）。

原稿（205_yamagishi_not_always_a_disc/…_jp.tex）は、平らなトーラスの上で面積 A を囲む候補として
円板・帯・穴の円板（円板の補集合）の三つだけを比べた閉形式と、しきい値の力学による数値の降下を
並べている。他の候補が無いことは示していないと明記している。

ここで証明した言明（辺 a ≤ b、ab = 1 の長方形トーラス。正方形は a = 1。0 ≤ A ≤ 1）：
  (1) `disc_le_band_iff`：円板の周長 2√(πA) ≤ 帯の周長 2a ⇔ A ≤ a²/π。
      `comp_le_band_iff`：穴の円板の周長 2√(π(1 − A)) ≤ 2a ⇔ 1 − a²/π ≤ A。
      `disc_le_comp_iff`：2√(πA) ≤ 2√(π(1 − A)) ⇔ A ≤ 1/2。
  (2) `min_candidates`：a ≤ 1 なら、三つの候補の最小は、A ≤ a²/π で円板、a²/π ≤ A ≤ 1 − a²/π で帯、
      1 − a²/π ≤ A で穴の円板。正方形（a = 1）の切り替えは A = 1/π と 1 − 1/π。
  (3) `disc_fits`：切り替えの面積までの円板の半径は a/π 以下で、a/2 より小さい（円板が自分と重ならない）。
形式化していないもの：平らなトーラスの等周領域が円板・帯・穴の円板のどれかであるという分類
（Howards–Hutchings–Morgan 1999）。したがってここで示したのは「三つの候補の中での最小」であって、
等周問題の答そのものではない（芯だけ）。降下法が境目で選べないという数値の観察も扱っていない。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper205

open Real

/-- 円板の周長。 -/
noncomputable def Pdisc (A : ℝ) : ℝ := 2 * √(π * A)
/-- 帯の周長（短い辺 a の向きに巻く二本の線）。 -/
def Pband (a : ℝ) : ℝ := 2 * a
/-- 穴の円板（円板の補集合）の周長。 -/
noncomputable def Pcomp (A : ℝ) : ℝ := 2 * √(π * (1 - A))

theorem two_sqrt_le_iff {y a : ℝ} (ha : 0 ≤ a) : 2 * √y ≤ 2 * a ↔ y ≤ a ^ 2 := by
  rw [mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2), sqrt_le_left ha]

/-- (1) 円板と帯。 -/
theorem disc_le_band_iff {A a : ℝ} (ha : 0 ≤ a) : Pdisc A ≤ Pband a ↔ A ≤ a ^ 2 / π := by
  have hpi := pi_pos
  unfold Pdisc Pband
  rw [two_sqrt_le_iff ha, le_div_iff₀ hpi, mul_comm]

/-- (1) 穴の円板と帯。 -/
theorem comp_le_band_iff {A a : ℝ} (ha : 0 ≤ a) : Pcomp A ≤ Pband a ↔ 1 - a ^ 2 / π ≤ A := by
  have hpi := pi_pos
  unfold Pcomp Pband
  rw [two_sqrt_le_iff ha, sub_le_comm, le_div_iff₀ hpi]
  constructor <;> intro h <;> nlinarith

/-- (1) 円板と穴の円板。 -/
theorem disc_le_comp_iff {A : ℝ} (h1 : A ≤ 1) :
    Pdisc A ≤ Pcomp A ↔ A ≤ 1 / 2 := by
  have hpi := pi_pos
  unfold Pdisc Pcomp
  rw [mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2),
    sqrt_le_sqrt_iff (by nlinarith), mul_le_mul_iff_right₀ hpi]
  constructor <;> intro h <;> linarith

theorem band_le_disc_iff {A a : ℝ} (ha : 0 ≤ a) (h0 : 0 ≤ A) :
    Pband a ≤ Pdisc A ↔ a ^ 2 / π ≤ A := by
  have hpi := pi_pos
  unfold Pdisc Pband
  rw [mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2), le_sqrt ha (by positivity),
    div_le_iff₀ hpi, mul_comm]

theorem band_le_comp_iff {A a : ℝ} (ha : 0 ≤ a) (h1 : A ≤ 1) :
    Pband a ≤ Pcomp A ↔ A ≤ 1 - a ^ 2 / π := by
  have hpi := pi_pos
  unfold Pcomp Pband
  rw [mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2),
    le_sqrt ha (mul_nonneg hpi.le (by linarith)), le_sub_comm,
    div_le_iff₀ hpi]
  constructor <;> intro h <;> nlinarith

/-- (2) 三つの候補の最小（a ≤ 1）。 -/
theorem min_candidates {A a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (h0 : 0 ≤ A) (h1 : A ≤ 1) :
    min (min (Pdisc A) (Pband a)) (Pcomp A) =
      if A ≤ a ^ 2 / π then Pdisc A else if A ≤ 1 - a ^ 2 / π then Pband a else Pcomp A := by
  have hpi := pi_pos
  have hpi3 : 3 < π := pi_gt_three
  have hq : a ^ 2 / π < 1 / 2 := by
    rw [div_lt_iff₀ hpi]; nlinarith
  split_ifs with hA hB
  · -- 円板
    have h1' := (disc_le_band_iff ha0.le).2 hA
    have h2' := (disc_le_comp_iff h1).2 (by linarith)
    rw [min_eq_left h1', min_eq_left h2']
  · -- 帯
    push Not at hA
    have h1' := (band_le_disc_iff ha0.le h0).2 hA.le
    have h2' := (band_le_comp_iff ha0.le h1).2 hB
    rw [min_eq_right h1', min_eq_left h2']
  · -- 穴の円板
    push Not at hA hB
    have h1' := (comp_le_band_iff ha0.le).2 hB.le
    have h2' : Pcomp A ≤ Pdisc A := by
      by_contra h; push Not at h
      have := (disc_le_comp_iff h1).1 h.le
      linarith
    rw [min_eq_right (le_min h2' h1')]

/-- (3) 切り替えまでの円板は自分と重ならない：半径 √(A/π) ≤ a/π < a/2。 -/
theorem disc_fits {A a : ℝ} (ha : 0 < a) (hA : A ≤ a ^ 2 / π) :
    √(A / π) ≤ a / π ∧ a / π < a / 2 := by
  have hpi := pi_pos
  have hpi3 : 3 < π := pi_gt_three
  constructor
  · rw [sqrt_le_left (by positivity), div_pow]
    calc A / π ≤ a ^ 2 / π / π := by gcongr
      _ = a ^ 2 / π ^ 2 := by ring
  · rw [div_lt_div_iff₀ hpi (by norm_num)]; nlinarith

end Paper205

end Yamagishi
