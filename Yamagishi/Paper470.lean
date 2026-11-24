/-
論文470『精度九十九パーセントの検査でも、陽性の九割は外れることがある』の格上げ（一般の形）。

原稿（470_yamagishi_ninety_nine_per_cent_accurate_wrong_nine_in_ten/…_jp.tex）は、
陽性的中率 PPV = p·se/(p·se + (1 − p)(1 − sp)) を se = sp = 0.99 で四つの有病率について数え、
有病率 0.001 で感度だけ・特異度だけを 0.999 にした比較（0.090909 と 0.497738）と、
的中率が 0.5 になる有病率の閉じた式 (1 − sp)/((1 − sp) + se) を示している。
「直すべきは特異度」は、この一組の数で見ただけ。

ここで証明した言明（0 < p < 1、se > 0、増分 Δ > 0、sp + Δ ≤ 1）：
  (1) `spec_beats_sens_iff`：特異度を Δ 上げたときの PPV が、感度を Δ 上げたときより大きい
      ⇔ se + sp + Δ > 1。`spec_eq_sens_iff`：等しい ⇔ se + sp + Δ = 1。
      `sens_beats_spec_iff`：小さい ⇔ se + sp + Δ < 1。どれも条件に有病率 p が入らない。
  (2) `npv_sens_beats_spec_iff`：対になって、陰性的中率は同じ条件で感度を上げるほうが大きい
      （NPV(p, se, sp) = PPV(1 − p, sp, se) という入れ替えから）。
  (3) `ppv_odds`：事後オッズ = 事前オッズ × 陽性尤度比 se/(1 − sp)。
      `ppv_strictMono_lr`：p を決めると PPV は尤度比について狭義に増える。
  (4) `ppv_eq_half_iff`：PPV = 1/2 ⇔ p = (1 − sp)/((1 − sp) + se)。
  (5) `paper_values`：原稿の三つの値は分数でちょうど 11/122、1/11、110/221。
      特異度を上げた値と感度を上げた値の比は 1210/221 = 5.4751…、元の値との比は 13420/2431 = 5.5203…。
足した仮定：感度と特異度は有病率によらない（模型の仮定）。sp + Δ ≤ 1（上げた特異度が 1 を越えない）。
形式化していないもの：医学の読み、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）

For any prevalence, raising specificity by Δ gives a higher positive predictive value than
raising sensitivity by Δ exactly when se + sp + Δ > 1; the direction does not depend on the
prevalence, and the negative predictive value behaves the other way round under the same condition.
-/
import Mathlib

namespace Yamagishi

namespace Paper470

/-- 陽性的中率。 -/
noncomputable def ppv (p se sp : ℝ) : ℝ := p * se / (p * se + (1 - p) * (1 - sp))

/-- 陰性的中率。 -/
noncomputable def npv (p se sp : ℝ) : ℝ := (1 - p) * sp / ((1 - p) * sp + p * (1 - se))

/-- 芯：二つの PPV の差は p(1 − p)Δ(se + sp + Δ − 1) を正の分母で割ったもの。 -/
theorem ppv_diff {p se sp Δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hse : 0 < se) (hΔ : 0 < Δ)
    (hsp : sp + Δ ≤ 1) :
    ppv p se (sp + Δ) - ppv p (se + Δ) sp =
      p * (1 - p) * Δ * (se + sp + Δ - 1) /
        ((p * se + (1 - p) * (1 - (sp + Δ))) * (p * (se + Δ) + (1 - p) * (1 - sp))) := by
  have h1 : 0 < p * se + (1 - p) * (1 - (sp + Δ)) := by
    have := mul_pos hp0 hse
    have := mul_nonneg (sub_pos.mpr hp1).le (sub_nonneg.mpr hsp); linarith
  have h2 : 0 < p * (se + Δ) + (1 - p) * (1 - sp) := by
    have := mul_pos hp0 (add_pos hse hΔ)
    have := mul_pos (sub_pos.mpr hp1) (show 0 < 1 - sp by linarith); linarith
  unfold ppv
  rw [div_sub_div _ _ h1.ne' h2.ne']
  congr 1
  ring

/-- 二つの分母は正。 -/
theorem den_pos {p se sp Δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hse : 0 < se) (hΔ : 0 < Δ)
    (hsp : sp + Δ ≤ 1) :
    0 < (p * se + (1 - p) * (1 - (sp + Δ))) * (p * (se + Δ) + (1 - p) * (1 - sp)) := by
  have h1 : 0 < p * se + (1 - p) * (1 - (sp + Δ)) := by
    have := mul_pos hp0 hse
    have := mul_nonneg (sub_pos.mpr hp1).le (sub_nonneg.mpr hsp); linarith
  have h2 : 0 < p * (se + Δ) + (1 - p) * (1 - sp) := by
    have := mul_pos hp0 (add_pos hse hΔ)
    have := mul_pos (sub_pos.mpr hp1) (show 0 < 1 - sp by linarith); linarith
  exact mul_pos h1 h2

/-- (1) 特異度を上げるほうが PPV が大きい ⇔ se + sp + Δ > 1（有病率 p によらない）。 -/
theorem spec_beats_sens_iff {p se sp Δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hse : 0 < se)
    (hΔ : 0 < Δ) (hsp : sp + Δ ≤ 1) :
    ppv p (se + Δ) sp < ppv p se (sp + Δ) ↔ 1 < se + sp + Δ := by
  have hk : 0 < p * (1 - p) * Δ := mul_pos (mul_pos hp0 (sub_pos.mpr hp1)) hΔ
  rw [← sub_pos, ppv_diff hp0 hp1 hse hΔ hsp,
    div_pos_iff_of_pos_right (den_pos hp0 hp1 hse hΔ hsp), mul_pos_iff_of_pos_left hk, sub_pos]

/-- (1) 等しい ⇔ se + sp + Δ = 1。 -/
theorem spec_eq_sens_iff {p se sp Δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hse : 0 < se)
    (hΔ : 0 < Δ) (hsp : sp + Δ ≤ 1) :
    ppv p se (sp + Δ) = ppv p (se + Δ) sp ↔ se + sp + Δ = 1 := by
  have hk : 0 < p * (1 - p) * Δ := mul_pos (mul_pos hp0 (sub_pos.mpr hp1)) hΔ
  rw [← sub_eq_zero, ppv_diff hp0 hp1 hse hΔ hsp,
    div_eq_zero_iff, or_iff_left (den_pos hp0 hp1 hse hΔ hsp).ne', mul_eq_zero,
    or_iff_right hk.ne', sub_eq_zero]

/-- (1) 感度を上げるほうが PPV が大きい ⇔ se + sp + Δ < 1（偶然より悪い検査）。 -/
theorem sens_beats_spec_iff {p se sp Δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hse : 0 < se)
    (hΔ : 0 < Δ) (hsp : sp + Δ ≤ 1) :
    ppv p se (sp + Δ) < ppv p (se + Δ) sp ↔ se + sp + Δ < 1 := by
  have hk : 0 < p * (1 - p) * Δ := mul_pos (mul_pos hp0 (sub_pos.mpr hp1)) hΔ
  rw [← sub_neg, ppv_diff hp0 hp1 hse hΔ hsp, div_lt_iff₀ (den_pos hp0 hp1 hse hΔ hsp), zero_mul]
  constructor
  · intro h; by_contra hc; have hc' : 1 ≤ se + sp + Δ := le_of_not_gt hc; nlinarith
  · intro h; exact mul_neg_of_pos_of_neg hk (by linarith)

/-- 陰性的中率は、有病率と感度・特異度を入れ替えた陽性的中率。 -/
theorem npv_eq_ppv (p se sp : ℝ) : npv p se sp = ppv (1 - p) sp se := by
  unfold npv ppv; congr 1; ring

/-- (2) 陰性的中率は、同じ条件 se + sp + Δ > 1 のときに限り、感度を上げるほうが大きい。 -/
theorem npv_sens_beats_spec_iff {p se sp Δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hsp : 0 < sp)
    (hΔ : 0 < Δ) (hse : se + Δ ≤ 1) :
    npv p se (sp + Δ) < npv p (se + Δ) sp ↔ 1 < se + sp + Δ := by
  rw [npv_eq_ppv, npv_eq_ppv]
  have := spec_beats_sens_iff (p := 1 - p) (se := sp) (sp := se) (by linarith) (by linarith)
    hsp hΔ hse
  rw [this]
  constructor <;> intro h <;> linarith

/-- (3) オッズの形：PPV/(1 − PPV) = (p/(1 − p))·(se/(1 − sp))。 -/
theorem ppv_odds {p se sp : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hse : 0 < se) (hsp : sp < 1) :
    ppv p se sp / (1 - ppv p se sp) = p / (1 - p) * (se / (1 - sp)) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hf : 0 < 1 - sp := sub_pos.mpr hsp
  have hD : 0 < p * se + (1 - p) * (1 - sp) := by positivity
  unfold ppv
  have : 1 - p * se / (p * se + (1 - p) * (1 - sp)) =
      (1 - p) * (1 - sp) / (p * se + (1 - p) * (1 - sp)) := by
    field_simp; ring
  rw [this]
  field_simp

/-- PPV を尤度比 ℓ = se/(1 − sp) で書く：PPV = pℓ/(pℓ + 1 − p)。 -/
noncomputable def ppvLR (p ℓ : ℝ) : ℝ := p * ℓ / (p * ℓ + (1 - p))

theorem ppv_eq_ppvLR {p se sp : ℝ} (hsp : sp < 1) : ppv p se sp = ppvLR p (se / (1 - sp)) := by
  have hf : (1 - sp) ≠ 0 := (sub_pos.mpr hsp).ne'
  unfold ppv ppvLR
  field_simp

/-- (3) p を決めると、PPV は尤度比について狭義に増える。 -/
theorem ppv_strictMono_lr {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictMonoOn (ppvLR p) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  unfold ppvLR
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hp0 hq]

/-- (4) PPV = 1/2 ⇔ p = (1 − sp)/((1 − sp) + se)。 -/
theorem ppv_eq_half_iff {p se sp : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hse : 0 < se) (hsp : sp < 1) :
    ppv p se sp = 1 / 2 ↔ p = (1 - sp) / ((1 - sp) + se) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hf : 0 < 1 - sp := sub_pos.mpr hsp
  have hD : 0 < p * se + (1 - p) * (1 - sp) := by positivity
  unfold ppv
  rw [div_eq_iff hD.ne', eq_div_iff (by positivity : (1 - sp) + se ≠ 0)]
  constructor <;> intro h <;> linarith

/-- (5) 原稿の三つの値（有病率 0.001）：元 11/122、感度だけ上げて 1/11、特異度だけ上げて 110/221。
比は 1210/221 と 13420/2431。 -/
theorem paper_values :
    ppv 0.001 0.99 0.99 = 11 / 122 ∧ ppv 0.001 0.999 0.99 = 1 / 11 ∧
    ppv 0.001 0.99 0.999 = 110 / 221 ∧
    (110 / 221 : ℝ) / (1 / 11) = 1210 / 221 ∧ (110 / 221 : ℝ) / (11 / 122) = 13420 / 2431 ∧
    (5.4751 : ℝ) < 1210 / 221 ∧ (1210 / 221 : ℝ) < 5.4752 := by
  unfold ppv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end Paper470

end Yamagishi
