/-
論文924『マインスイーパの五分五分は見えている数字だけでは決まらず、盤に残る地雷の密度で傾く』の格上げ（一般の形）。

原稿（924_yamagishi_a_minesweeper_fifty_fifty_tilts_with_the_density_of_mines_left/…_jp.tex）は、
制約 x₁ + x₂ = 1、x₂ + x₃ = 1 の外に未知のますが U 個、残りの地雷が M 個のとき
P(x₂) = C(U, M−1)/(C(U, M−1) + C(U, M−2)) と比 (U − M + 2)/(M − 1) を式で書き、
五組の総当たりと七つの組の表で、端 x₁ と盤の残りの一ますが同じ確率になることを数値で示す。

ここで証明した言明（すべての配置が同じ重み。M = m + 2、0 ≤ m ≤ U）：
  (1) `prob_middle`：P(x₂) = (U − M + 2)/(U + 1)。
  (2) `prob_edge`：P(x₁) = 1 − P(x₂) = (M − 1)/(U + 1)。
  (3) `prob_outside`：M ≥ 3、U ≥ 1 のとき、盤の残りの一ますが地雷である確率
      （(C(U−1, M−2) + C(U−1, M−3)) ÷ (C(U, M−1) + C(U, M−2))）も (M − 1)/(U + 1) で、端と等しい
      （パスカルの等式 C(U−1, M−2) + C(U−1, M−3) = C(U, M−2)）。
  (4) `half_iff`：P(x₂) = 1/2 ⇔ U = 2M − 3。
足した仮定：二つの解 {x₂}・{x₁, x₃} と、残りの地雷を残りのますに置く置き方の数で重みを付ける
（原稿の式そのまま）。(3) は M ≥ 3 で示した（M = 2 では二個の解の側の数が 0 で、式は別に一行で確かめられる）。
形式化していないもの：総当たりの表、一般の盤（別の制約が重なる場合）、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper924

open Nat

/-- 真ん中 x₂ が地雷である確率（M = m + 2）。 -/
noncomputable def Pmid (U m : ℕ) : ℝ :=
  (U.choose (m + 1) : ℝ) / ((U.choose (m + 1) : ℝ) + (U.choose m : ℝ))

/-- 端 x₁ が地雷である確率（二個の解の側）。 -/
noncomputable def Pedge (U m : ℕ) : ℝ :=
  (U.choose m : ℝ) / ((U.choose (m + 1) : ℝ) + (U.choose m : ℝ))

theorem denom_eq (U m : ℕ) :
    (U.choose (m + 1) : ℝ) + (U.choose m : ℝ) = ((U + 1).choose (m + 1) : ℝ) := by
  rw [choose_succ_succ]; push_cast; ring

/-- (1) P(x₂) = (U − M + 2)/(U + 1) = (U − m)/(U + 1)。 -/
theorem prob_middle {U m : ℕ} (hm : m ≤ U) : Pmid U m = ((U : ℝ) - m) / (U + 1) := by
  unfold Pmid
  rw [denom_eq]
  have h1 : (U.choose (m + 1) : ℝ) * (m + 1) = (U.choose m : ℝ) * ((U : ℝ) - m) := by
    have := choose_succ_right_eq U m
    have h' : ((U.choose (m + 1) * (m + 1) : ℕ) : ℝ) = ((U.choose m * (U - m) : ℕ) : ℝ) := by
      rw [this]
    push_cast [hm] at h'; linarith
  have h2 : ((U : ℝ) + 1) * (U.choose m : ℝ) = ((U + 1).choose (m + 1) : ℝ) * (m + 1) := by
    have := add_one_mul_choose_eq U m
    have h' : (((U + 1) * U.choose m : ℕ) : ℝ) = (((U + 1).choose (m + 1) * (m + 1) : ℕ) : ℝ) := by
      rw [this]
    push_cast at h'; linarith
  have hc : (0 : ℝ) < U.choose m := by exact_mod_cast choose_pos hm
  have hc1 : (0 : ℝ) < (U + 1).choose (m + 1) := by exact_mod_cast choose_pos (by omega)
  rw [div_eq_div_iff (ne_of_gt hc1) (by positivity)]
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  apply mul_right_cancel₀ (ne_of_gt hm1)
  nlinarith [h1, h2]

/-- (2) P(x₁) = 1 − P(x₂) = (M − 1)/(U + 1) = (m + 1)/(U + 1)。 -/
theorem prob_edge {U m : ℕ} (hm : m ≤ U) : Pedge U m = ((m : ℝ) + 1) / (U + 1) := by
  have hsum : Pedge U m = 1 - Pmid U m := by
    unfold Pedge Pmid
    have hc : (0 : ℝ) < U.choose m := by exact_mod_cast choose_pos hm
    have : (0 : ℝ) < (U.choose (m + 1) : ℝ) + (U.choose m : ℝ) := by positivity
    field_simp; ring
  rw [hsum, prob_middle hm]
  field_simp; ring

/-- (3) 盤の残りの一ます（U = u + 1、M = m + 3）が地雷である確率は端と同じ。 -/
theorem prob_outside (u m : ℕ) :
    ((u.choose (m + 1) : ℝ) + (u.choose m : ℝ)) /
        (((u + 1).choose (m + 2) : ℝ) + ((u + 1).choose (m + 1) : ℝ)) = Pedge (u + 1) (m + 1) := by
  unfold Pedge
  congr 1
  rw [choose_succ_succ u m]; push_cast; ring

/-- (3) の値：(M − 1)/(U + 1)（U = u + 1、M = m + 3、M ≤ U + 2）。 -/
theorem prob_outside_value {u m : ℕ} (hm : m + 1 ≤ u + 1) :
    ((u.choose (m + 1) : ℝ) + (u.choose m : ℝ)) /
        (((u + 1).choose (m + 2) : ℝ) + ((u + 1).choose (m + 1) : ℝ)) =
            ((m : ℝ) + 2) / (u + 2) := by
  rw [prob_outside, prob_edge hm]; push_cast; ring

/-- (4) P(x₂) = 1/2 ⇔ U = 2M − 3（M = m + 2 なので U = 2m + 1）。 -/
theorem half_iff {U m : ℕ} (hm : m ≤ U) : Pmid U m = 1 / 2 ↔ U = 2 * m + 1 := by
  rw [prob_middle hm, div_eq_div_iff (by positivity) (by norm_num)]
  constructor
  · intro h
    have : (U : ℝ) = 2 * m + 1 := by linarith
    exact_mod_cast this
  · intro h; subst h; push_cast; ring

/-- 原稿の表の五つ（U・M）：6・2 → 6/7、6・4 → 4/7、8・3 → 7/9、10・6 → 6/11、12・4 → 10/13。 -/
theorem table_values :
    Pmid 6 0 = 6 / 7 ∧ Pmid 6 2 = 4 / 7 ∧ Pmid 8 1 = 7 / 9 ∧
        Pmid 10 4 = 6 / 11 ∧ Pmid 12 2 = 10 / 13 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [prob_middle (by norm_num)] <;> norm_num

end Paper924

end Yamagishi
