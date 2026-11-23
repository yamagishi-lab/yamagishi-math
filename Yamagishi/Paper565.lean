/-
論文565『寿命を決めているのは最初のきずで、終わりの大きさではない』の格上げ（一般の形）。

日本語：パリス則で伸びるき裂では、初期きずを小さくする効きと終端を大きくする効きの比が
(c·a_f/a_i)^(m/2 − 1) という閉じた式になり、初期の側が勝つのは指数 m が 2 より大きいときだけである。
English: Under the Paris law, the gain from shrinking the initial flaw divided by the gain from
enlarging the final size is (c·a_f/a_i)^(m/2 − 1), so the initial flaw wins exactly when m > 2.

原稿（565_yamagishi_the_initial_flaw_not_the_final_size/…_jp.tex）は、m = 3、a_i = 0.5 mm、
a_f = 25 mm の一配置で、終端 2 倍の 1.048244 倍と初期半分の 1.482441 倍、効きの比 10 が √(2a_f/a_i)
に一致すること、終端無限大の上限 1.164716 倍、きずが 2 倍になるまでに寿命の 0.341137 が過ぎること
を数値で示す。m > 2 が境目であることは観察 4.1 で言葉で述べるだけ。

ここで証明した言明（0 < a_i < a_f、倍率 c > 1、指数 m は任意の実数）：
  (0) `paris_integrand`：パリス則 da/dN = C(YΔσ√(πa))^m から dN/da = K·a^(−m/2)、
      K = 1/(C(YΔσ√π)^m)。比と大小は K によらないので、寿命を life m a_i a_f = ∫_{a_i}^{a_f} a^(−m/2) da
      と置く（`life`）。
  (1) `life_closed`・`life_two`：m ≠ 2 で (a_f^(1−m/2) − a_i^(1−m/2))/(1 − m/2)、m = 2 で ln(a_f/a_i)。
  (2) `gain_ratio`：初期きずを 1/c にして得る増分 G_i と、終端を c 倍にして得る増分 G_f の比は
      G_i/G_f = (c·a_f/a_i)^(m/2 − 1)（m = 2 も含めて一つの式）。
  (3) `final_lt_initial_iff`・`initial_eq_final_iff`・`initial_lt_final_iff`：配置と倍率によらず、
      G_f < G_i ⇔ m > 2、G_i = G_f ⇔ m = 2、G_i < G_f ⇔ m < 2。
  (4) `integrableOn_iff`：終端を無限大にしても寿命が有限（a^(−m/2) が (a_i, ∞) で積分できる）⇔ m > 2。
      `life_tendsto`：m > 2 なら life → a_i^(1−m/2)/(m/2 − 1)、`life_tendsto_atTop`：m ≤ 2 なら発散。
      `limit_over_life`：上限は基準の寿命の 1/(1 − (a_i/a_f)^(m/2−1)) 倍。
  (5) `doubling_share`：きずが 2 倍になるまでに使う寿命の割合は (1 − 2^(−β))/(1 − (a_i/a_f)^β)、
      β = m/2 − 1（m ≠ 2）。
  (6) `ratio_three`・`ratio_paper`：m = 3 で比は √(2a_f/a_i)、a_f = 50a_i で 10（原稿の数）。
足した仮定：形状係数 Y 一定、下限界なし、終端 a_f を初期きずと独立に置く（原稿と同じ模型）。
形式化していないもの：実部材の寿命の値、き裂閉口・過大荷重、靭性の読み、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper565

open Real Set Filter Topology MeasureTheory intervalIntegral

/-- (0) パリス則の積分の中身：1/(C(YΔσ√(πa))^m) = K·a^(−m/2)、K = 1/(C(YΔσ√π)^m)。 -/
theorem paris_integrand {C Y Δσ m a : ℝ} (hY : 0 < Y) (hσ : 0 < Δσ) (ha : 0 < a) :
    1 / (C * (Y * Δσ * √(π * a)) ^ m) = 1 / (C * (Y * Δσ * √π) ^ m) * a ^ (-(m / 2)) := by
  have hs : √(π * a) = √π * √a := sqrt_mul pi_pos.le a
  have hpa : (√a) ^ m = a ^ (m / 2) := by
    rw [sqrt_eq_rpow, ← rpow_mul ha.le]; ring_nf
  rw [hs, ← mul_assoc, mul_rpow (by positivity) (sqrt_nonneg _), hpa, rpow_neg ha.le]
  field_simp

/-- 寿命（定数 K を除く）：life m a_i a_f = ∫_{a_i}^{a_f} a^(−m/2) da。 -/
noncomputable def life (m ai af : ℝ) : ℝ := ∫ a in ai..af, a ^ (-(m / 2))

/-- (1) m ≠ 2 の閉じた式。 -/
theorem life_closed {m ai af : ℝ} (hm : m ≠ 2) (hi : 0 < ai) (hf : 0 < af) :
    life m ai af = (af ^ (1 - m / 2) - ai ^ (1 - m / 2)) / (1 - m / 2) := by
  unfold life
  have hr : -(m / 2) ≠ -1 := by intro h; apply hm; linarith
  rw [integral_rpow (Or.inr ⟨hr, notMem_uIcc_of_lt hi hf⟩)]
  have e : -(m / 2) + 1 = 1 - m / 2 := by ring
  rw [e]

/-- (1) m = 2 の閉じた式。 -/
theorem life_two {ai af : ℝ} (hi : 0 < ai) (hf : 0 < af) : life 2 ai af = log (af / ai) := by
  unfold life
  have e : ∀ x : ℝ, x ^ (-((2 : ℝ) / 2)) = x⁻¹ := fun x => by norm_num [rpow_neg_one]
  simp_rw [e]
  exact integral_inv_of_pos hi hf

/-- 寿命は区間についてたし算になる。 -/
theorem life_add {m a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    life m a b + life m b c = life m a c := by
  by_cases hm : m = 2
  · subst hm
    rw [life_two ha hb, life_two hb hc, life_two ha hc, ← log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  · rw [life_closed hm ha hb, life_closed hm hb hc, life_closed hm ha hc]
    have : (1 : ℝ) - m / 2 ≠ 0 := by intro h; apply hm; linarith
    field_simp; ring

/-- 尺度を変えると λ^(1 − m/2) 倍になる。 -/
theorem life_scale {m a b l : ℝ} (ha : 0 < a) (hb : 0 < b) (hl : 0 < l) :
    life m (l * a) (l * b) = l ^ (1 - m / 2) * life m a b := by
  by_cases hm : m = 2
  · subst hm
    rw [life_two (by positivity) (by positivity), life_two ha hb]
    norm_num
    congr 1; field_simp
  · rw [life_closed hm (by positivity) (by positivity), life_closed hm ha hb,
      mul_rpow hl.le hb.le, mul_rpow hl.le ha.le]
    ring

/-- 0 < a < b なら寿命は正。 -/
theorem life_pos {m a b : ℝ} (ha : 0 < a) (hab : a < b) : 0 < life m a b := by
  have hb : 0 < b := ha.trans hab
  rcases lt_trichotomy m 2 with hm | hm | hm
  · rw [life_closed (ne_of_lt hm) ha hb]
    apply div_pos _ (by linarith)
    have := rpow_lt_rpow ha.le hab (show (0 : ℝ) < 1 - m / 2 by linarith)
    linarith
  · subst hm; rw [life_two ha hb]
    exact log_pos ((one_lt_div ha).mpr hab)
  · rw [life_closed (ne_of_gt hm) ha hb]
    apply div_pos_of_neg_of_neg _ (by linarith)
    have := rpow_lt_rpow_of_neg ha hab (show 1 - m / 2 < 0 by linarith)
    linarith

/-! ### 初期を 1/c にする効きと、終端を c 倍にする効き -/

/-- 初期きずを 1/c にして得る寿命の増分。 -/
noncomputable def gainInitial (m ai af c : ℝ) : ℝ := life m (ai / c) af - life m ai af

/-- 終端を c 倍にして得る寿命の増分。 -/
noncomputable def gainFinal (m ai af c : ℝ) : ℝ := life m ai (c * af) - life m ai af

theorem gainInitial_eq {m ai af c : ℝ} (hi : 0 < ai) (hf : 0 < af) (hc : 0 < c) :
    gainInitial m ai af c = life m (ai / c) ai := by
  unfold gainInitial
  rw [← life_add (b := ai) (by positivity) hi hf]; ring

theorem gainFinal_eq {m ai af c : ℝ} (hi : 0 < ai) (hf : 0 < af) (hc : 0 < c) :
    gainFinal m ai af c = life m af (c * af) := by
  unfold gainFinal
  rw [← life_add (b := af) hi hf (by positivity)]; ring

/-- G_f = (c a_f/a_i)^(1 − m/2) · G_i（尺度 λ = c a_f/a_i で [a_i/c, a_i] が [a_f, c a_f] に移る）。 -/
theorem gain_relation {m ai af c : ℝ} (hi : 0 < ai) (hf : 0 < af) (hc : 0 < c) :
    gainFinal m ai af c = (c * af / ai) ^ (1 - m / 2) * gainInitial m ai af c := by
  rw [gainFinal_eq hi hf hc, gainInitial_eq hi hf hc, ← life_scale (by positivity) hi
    (by positivity)]
  congr 1
  · field_simp
  · field_simp

theorem gainInitial_pos {m ai af c : ℝ} (hi : 0 < ai) (hf : 0 < af) (hc : 1 < c) :
    0 < gainInitial m ai af c := by
  rw [gainInitial_eq hi hf (by linarith)]
  exact life_pos (by positivity) (div_lt_self hi hc)

/-- (2) 効きの比 G_i/G_f = (c a_f/a_i)^(m/2 − 1)。 -/
theorem gain_ratio {m ai af c : ℝ} (hi : 0 < ai) (hf : 0 < af) (hc : 1 < c) :
    gainInitial m ai af c / gainFinal m ai af c = (c * af / ai) ^ (m / 2 - 1) := by
  have hG := gainInitial_pos (m := m) hi hf hc
  have hl : 0 < c * af / ai := by have : (0 : ℝ) < c := by linarith
                                  positivity
  rw [gain_relation hi hf (by linarith)]
  have hp : 0 < (c * af / ai) ^ (1 - m / 2) := rpow_pos_of_pos hl _
  rw [show m / 2 - 1 = -(1 - m / 2) by ring, rpow_neg hl.le]
  field_simp

theorem scale_gt_one {ai af c : ℝ} (hi : 0 < ai) (hif : ai < af) (hc : 1 < c) :
    1 < c * af / ai := by
  rw [one_lt_div hi]; nlinarith

/-- (3) G_f < G_i ⇔ m > 2。 -/
theorem final_lt_initial_iff {m ai af c : ℝ} (hi : 0 < ai) (hif : ai < af) (hc : 1 < c) :
    gainFinal m ai af c < gainInitial m ai af c ↔ 2 < m := by
  have hf : 0 < af := hi.trans hif
  have hG := gainInitial_pos (m := m) hi hf hc
  have hl := scale_gt_one hi hif hc
  rw [gain_relation hi hf (by linarith)]
  constructor
  · intro h
    by_contra hm
    push Not at hm
    have : 1 ≤ (c * af / ai) ^ (1 - m / 2) := one_le_rpow hl.le (by linarith)
    nlinarith
  · intro hm
    have : (c * af / ai) ^ (1 - m / 2) < 1 := rpow_lt_one_of_one_lt_of_neg hl (by linarith)
    nlinarith

/-- (3) G_i < G_f ⇔ m < 2。 -/
theorem initial_lt_final_iff {m ai af c : ℝ} (hi : 0 < ai) (hif : ai < af) (hc : 1 < c) :
    gainInitial m ai af c < gainFinal m ai af c ↔ m < 2 := by
  have hf : 0 < af := hi.trans hif
  have hG := gainInitial_pos (m := m) hi hf hc
  have hl := scale_gt_one hi hif hc
  rw [gain_relation hi hf (by linarith)]
  constructor
  · intro h
    by_contra hm
    push Not at hm
    have : (c * af / ai) ^ (1 - m / 2) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hl.le (by linarith)
    nlinarith
  · intro hm
    have : 1 < (c * af / ai) ^ (1 - m / 2) := one_lt_rpow hl (by linarith)
    nlinarith

/-- (3) G_i = G_f ⇔ m = 2。 -/
theorem initial_eq_final_iff {m ai af c : ℝ} (hi : 0 < ai) (hif : ai < af) (hc : 1 < c) :
    gainInitial m ai af c = gainFinal m ai af c ↔ m = 2 := by
  have h1 := final_lt_initial_iff (m := m) hi hif hc
  have h2 := initial_lt_final_iff (m := m) hi hif hc
  constructor
  · intro h
    rcases lt_trichotomy m 2 with hm | hm | hm
    · exact absurd (h2.mpr hm) (by rw [h]; exact lt_irrefl _)
    · exact hm
    · exact absurd (h1.mpr hm) (by rw [h]; exact lt_irrefl _)
  · intro hm
    have hf : 0 < af := hi.trans hif
    rw [gain_relation hi hf (by linarith), hm]; norm_num

/-! ### 終端を無限大にしたとき -/

/-- (4) a^(−m/2) が (a_i, ∞) で積分できる ⇔ m > 2。 -/
theorem integrableOn_iff {m ai : ℝ} (hi : 0 < ai) :
    IntegrableOn (fun a : ℝ => a ^ (-(m / 2))) (Ioi ai) ↔ 2 < m := by
  rw [integrableOn_Ioi_rpow_iff hi]
  constructor <;> intro h <;> linarith

/-- (4) m > 2 なら、終端 → ∞ で寿命は a_i^(1−m/2)/(m/2 − 1) に近づく。 -/
theorem life_tendsto {m ai : ℝ} (hm : 2 < m) (hi : 0 < ai) :
    Tendsto (fun af => life m ai af) atTop (𝓝 (ai ^ (1 - m / 2) / (m / 2 - 1))) := by
  have hm' : m ≠ 2 := ne_of_gt hm
  have hev : (fun af => (af ^ (-(m / 2 - 1)) - ai ^ (1 - m / 2)) / (1 - m / 2)) =ᶠ[atTop]
      fun af => life m ai af := by
    filter_upwards [eventually_gt_atTop 0] with af hf
    rw [life_closed hm' hi hf]; ring_nf
  refine Tendsto.congr' hev ?_
  have h0 := tendsto_rpow_neg_atTop (show 0 < m / 2 - 1 by linarith)
  have := (h0.sub_const (ai ^ (1 - m / 2))).div_const (1 - m / 2)
  convert this using 2
  have : (1 : ℝ) - m / 2 ≠ 0 := by intro h; linarith
  field_simp; ring

/-- (4) m ≤ 2 なら、終端 → ∞ で寿命は限りなく大きくなる。 -/
theorem life_tendsto_atTop {m ai : ℝ} (hm : m ≤ 2) (hi : 0 < ai) :
    Tendsto (fun af => life m ai af) atTop atTop := by
  rcases lt_or_eq_of_le hm with hm | hm
  · have hev : (fun af => (af ^ (1 - m / 2) - ai ^ (1 - m / 2)) / (1 - m / 2)) =ᶠ[atTop]
        fun af => life m ai af := by
      filter_upwards [eventually_gt_atTop 0] with af hf
      rw [life_closed (ne_of_lt hm) hi hf]
    refine Tendsto.congr' hev ?_
    have h1 : Tendsto (fun af : ℝ => af ^ (1 - m / 2) + -(ai ^ (1 - m / 2))) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_rpow_atTop (by linarith))
    have h2 := h1.atTop_div_const (show (0 : ℝ) < 1 - m / 2 by linarith)
    exact h2.congr (fun x => by ring)
  · subst hm
    have hev : (fun af => log (af / ai)) =ᶠ[atTop] fun af => life 2 ai af := by
      filter_upwards [eventually_gt_atTop 0] with af hf
      rw [life_two hi hf]
    exact Tendsto.congr' hev (tendsto_log_atTop.comp (tendsto_id.atTop_div_const hi))

/-- (4) 上限と基準の寿命の比：1/(1 − (a_i/a_f)^(m/2−1))。 -/
theorem limit_over_life {m ai af : ℝ} (hm : 2 < m) (hi : 0 < ai) (hif : ai < af) :
    (ai ^ (1 - m / 2) / (m / 2 - 1)) / life m ai af = 1 / (1 - (ai / af) ^ (m / 2 - 1)) := by
  have hf : 0 < af := hi.trans hif
  rw [life_closed (ne_of_gt hm) hi hf]
  have hb : 0 < m / 2 - 1 := by linarith
  have e1 : (ai / af) ^ (m / 2 - 1) = af ^ (1 - m / 2) / ai ^ (1 - m / 2) := by
    rw [div_rpow hi.le hf.le, show m / 2 - 1 = -(1 - m / 2) by ring, rpow_neg hi.le,
      rpow_neg hf.le]
    field_simp
  rw [e1]
  have hA : 0 < ai ^ (1 - m / 2) := rpow_pos_of_pos hi _
  have hlt : af ^ (1 - m / 2) < ai ^ (1 - m / 2) := rpow_lt_rpow_of_neg hi hif (by linarith)
  have h2 : (1 : ℝ) - m / 2 ≠ 0 := by linarith
  have h3 : m / 2 - 1 ≠ 0 := by linarith
  generalize ai ^ (1 - m / 2) = A at *
  generalize af ^ (1 - m / 2) = B at *
  have h1 : B - A ≠ 0 := by linarith
  have h1' : A - B ≠ 0 := by linarith
  have h4 : 1 - B / A ≠ 0 := by
    rw [show 1 - B / A = (A - B) / A by field_simp]; exact div_ne_zero h1' hA.ne'
  rw [show (1 : ℝ) - m / 2 = -(m / 2 - 1) by ring, show 1 - B / A = (A - B) / A by field_simp,
    one_div_div]
  field_simp
  ring

/-- (5) きずが 2 倍になるまでに使う寿命の割合（m ≠ 2、β = m/2 − 1）。 -/
theorem doubling_share {m ai af : ℝ} (hm : m ≠ 2) (hi : 0 < ai) (hif : ai < af) :
    life m ai (2 * ai) / life m ai af =
      (1 - 2 ^ (-(m / 2 - 1))) / (1 - (ai / af) ^ (m / 2 - 1)) := by
  have hf : 0 < af := hi.trans hif
  rw [life_closed hm hi (by positivity), life_closed hm hi hf]
  have h2 : (1 : ℝ) - m / 2 ≠ 0 := by intro h; apply hm; linarith
  have hA : 0 < ai ^ (1 - m / 2) := rpow_pos_of_pos hi _
  have e0 : (2 * ai) ^ (1 - m / 2) = 2 ^ (1 - m / 2) * ai ^ (1 - m / 2) :=
    mul_rpow (by norm_num) hi.le
  have e1 : (ai / af) ^ (m / 2 - 1) = af ^ (1 - m / 2) / ai ^ (1 - m / 2) := by
    rw [div_rpow hi.le hf.le, show m / 2 - 1 = -(1 - m / 2) by ring, rpow_neg hi.le,
      rpow_neg hf.le]
    field_simp
  have e2 : (2 : ℝ) ^ (-(m / 2 - 1)) = 2 ^ (1 - m / 2) := by ring_nf
  rw [e0, e1, e2]
  have hne : af ^ (1 - m / 2) ≠ ai ^ (1 - m / 2) := by
    rcases lt_or_gt_of_ne hm with h | h
    · exact ne_of_gt (rpow_lt_rpow hi.le hif (by linarith))
    · exact ne_of_lt (rpow_lt_rpow_of_neg hi hif (by linarith))
  generalize ai ^ (1 - m / 2) = A at *
  generalize af ^ (1 - m / 2) = B at *
  generalize (2 : ℝ) ^ (1 - m / 2) = T
  have h5 : B - A ≠ 0 := sub_ne_zero.mpr hne
  have h5' : A - B ≠ 0 := sub_ne_zero.mpr hne.symm
  have h4 : 1 - B / A ≠ 0 := by
    rw [show 1 - B / A = (A - B) / A by field_simp]; exact div_ne_zero h5' hA.ne'
  rw [div_eq_div_iff (div_ne_zero h5 h2) h4]
  field_simp
  ring

/-- (6) m = 3 で効きの比は √(c a_f/a_i)（原稿の c = 2 で √(2a_f/a_i)）。 -/
theorem ratio_three {ai af c : ℝ} (hi : 0 < ai) (hf : 0 < af) (hc : 1 < c) :
    gainInitial 3 ai af c / gainFinal 3 ai af c = √(c * af / ai) := by
  rw [gain_ratio hi hf hc, sqrt_eq_rpow]; norm_num

/-- (6) 原稿の配置 a_f = 50 a_i、c = 2 で比はちょうど 10。 -/
theorem ratio_paper {ai : ℝ} (hi : 0 < ai) :
    gainInitial 3 ai (50 * ai) 2 / gainFinal 3 ai (50 * ai) 2 = 10 := by
  rw [ratio_three hi (by positivity) (by norm_num)]
  have : 2 * (50 * ai) / ai = 10 ^ 2 := by field_simp; norm_num
  rw [this, sqrt_sq (by norm_num)]

end Paper565

end Yamagishi
