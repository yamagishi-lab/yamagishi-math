/-
論文342『同じ二材料を同じ割合で混ぜて、剛性が 16.93 倍ひらく』の格上げ（一般の形）。

原稿（342_yamagishi_the_same_two_materials_differ_seventeenfold_by_direction/…_jp.tex）は、
繊維と母材の二相で、ボイト（並列）E_V = v E_f + (1 − v) E_m とロイス（直列）1/E_R = v/E_f + (1 − v)/E_m の
比の閉じた式・対称性・v = 1/2 での最大（R_max = 1/2 + (1/4)(E_f/E_m + E_m/E_f)）を代数で示し、
体積分率 0.01 刻みと三組の材料で検算している。

ここで証明した言明：
  (1) `ratio_two_phase`：二相（a, b > 0、u ∈ [0, 1]）で E_V/E_R = 1 + u(1 − u)(√(a/b) − √(b/a))²
      = 1 + u(1 − u)(a/b + b/a − 2)。`ratio_symm`：R(u) = R(1 − u)。
  (2) `ratio_max`：R(u) ≤ R(1/2) = (a + b)²/(4ab)、等号は a ≠ b なら u = 1/2 のときだけ（`ratio_max_iff`）。
      原稿の R_max = 1/2 + (1/4)(a/b + b/a) と同じ（`rmax_manuscript`）。
  (3) `kantorovich`：多相（重み v_i ≥ 0、Σv_i = 1、弾性率 a_i ∈ [B, A]、B > 0）でも
      (Σ v_i a_i)(Σ v_i/a_i) ≤ (A + B)²/(4AB)（カントロビッチの不等式）。
      比の上限は最大と最小の弾性率だけで決まる。
足した仮定：ボイトとロイスの式そのもの（ひずみが共通・応力が共通）は定義として置いた。
形式化していないもの：材料の数値、十七倍の数、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper342

open Real Finset

/-- ボイト ÷ ロイス の比：(u a + (1 − u) b)(u/a + (1 − u)/b)。 -/
noncomputable def R (a b u : ℝ) : ℝ := (u * a + (1 - u) * b) * (u / a + (1 - u) / b)

/-- (1) 二相の閉じた式。 -/
theorem ratio_two_phase {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : ℝ) :
    R a b u = 1 + u * (1 - u) * (a / b + b / a - 2) := by
  unfold R; field_simp; ring

theorem ratio_two_phase_sqrt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : ℝ) :
    R a b u = 1 + u * (1 - u) * (√(a / b) - √(b / a)) ^ 2 := by
  rw [ratio_two_phase ha hb]
  have h1 : √(a / b) ^ 2 = a / b := sq_sqrt (by positivity)
  have h2 : √(b / a) ^ 2 = b / a := sq_sqrt (by positivity)
  have h3 : √(a / b) * √(b / a) = 1 := by
    rw [← sqrt_mul (by positivity)]; field_simp; simp
  congr 2; nlinarith [h1, h2, h3]

theorem ratio_symm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : ℝ) : R a b u = R a b (1 - u) := by
  rw [ratio_two_phase ha hb, ratio_two_phase ha hb]; ring

theorem ratio_half {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    R a b (1 / 2) = (a + b) ^ 2 / (4 * a * b) := by
  unfold R; field_simp; ring

/-- 原稿の R_max = 1/2 + (1/4)(a/b + b/a) と同じ。 -/
theorem rmax_manuscript {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) ^ 2 / (4 * a * b) = 1 / 2 + 1 / 4 * (a / b + b / a) := by
  field_simp; ring

theorem gap_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ a / b + b / a - 2 := by
  have : a / b + b / a - 2 = (a - b) ^ 2 / (a * b) := by field_simp; ring
  rw [this]; positivity

/-- (2) 最大は u = 1/2。 -/
theorem ratio_max {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : ℝ) : R a b u ≤ R a b (1 / 2) := by
  rw [ratio_two_phase ha hb, ratio_two_phase ha hb]
  have := gap_nonneg ha hb
  have : u * (1 - u) ≤ 1 / 2 * (1 - 1 / 2) := by nlinarith [sq_nonneg (u - 1 / 2)]
  nlinarith

theorem ratio_max_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (u : ℝ) :
    R a b u = R a b (1 / 2) ↔ u = 1 / 2 := by
  rw [ratio_two_phase ha hb, ratio_two_phase ha hb]
  have hg : 0 < a / b + b / a - 2 := by
    have : a / b + b / a - 2 = (a - b) ^ 2 / (a * b) := by field_simp; ring
    rw [this]; have : (a - b) ^ 2 > 0 := by positivity
    positivity
  constructor
  · intro h
    have : (u - 1 / 2) ^ 2 * (a / b + b / a - 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h1 | h1
    · nlinarith [sq_nonneg (u - 1 / 2)]
    · linarith
  · intro h; rw [h]

/-- (3) カントロビッチの不等式。 -/
theorem kantorovich {ι : Type*} (s : Finset ι) (v x : ι → ℝ) {A B : ℝ} (hB : 0 < B)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hsum : ∑ i ∈ s, v i = 1) (hx : ∀ i ∈ s, B ≤ x i ∧ x i ≤ A) :
    (∑ i ∈ s, v i * x i) * (∑ i ∈ s, v i / x i) ≤ (A + B) ^ 2 / (4 * A * B) := by
  have hA : 0 < A := by
    obtain ⟨i, hi⟩ : s.Nonempty := by
      by_contra h; rw [not_nonempty_iff_eq_empty] at h; rw [h, sum_empty] at hsum; norm_num at hsum
    linarith [(hx i hi).1, (hx i hi).2]
  -- 各点：x + AB/x ≤ A + B
  have hpt : ∀ i ∈ s, v i * x i + A * B * (v i / x i) ≤ v i * (A + B) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hx i hi
    have hxi : 0 < x i := by linarith
    have : x i + A * B / x i ≤ A + B := by
      rw [← sub_nonneg]
      have : A + B - (x i + A * B / x i) = (A - x i) * (x i - B) / x i := by field_simp; ring
      rw [this]; apply div_nonneg _ hxi.le; nlinarith
    have := mul_le_mul_of_nonneg_left this (hv i hi)
    calc v i * x i + A * B * (v i / x i) = v i * (x i + A * B / x i) := by field_simp
      _ ≤ v i * (A + B) := this
  have hsum2 : (∑ i ∈ s, v i * x i) + A * B * (∑ i ∈ s, v i / x i) ≤ A + B := by
    rw [mul_sum, ← sum_add_distrib]
    calc ∑ i ∈ s, (v i * x i + A * B * (v i / x i)) ≤ ∑ i ∈ s, v i * (A + B) := sum_le_sum hpt
      _ = A + B := by rw [← sum_mul, hsum, one_mul]
  set P := ∑ i ∈ s, v i * x i
  set H := ∑ i ∈ s, v i / x i
  have hP : 0 ≤ P := sum_nonneg (fun i hi => mul_nonneg (hv i hi) (by linarith [(hx i hi).1]))
  have hH : 0 ≤ H := sum_nonneg (fun i hi => div_nonneg (hv i hi) (by linarith [(hx i hi).1]))
  -- 相加相乗：4 P (AB H) ≤ (P + AB H)² ≤ (A + B)²
  have h4 : 4 * (P * (A * B * H)) ≤ (A + B) ^ 2 := by
    have : 0 ≤ P + A * B * H := by positivity
    nlinarith [sq_nonneg (P - A * B * H)]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [h4]

end Paper342

end Yamagishi
