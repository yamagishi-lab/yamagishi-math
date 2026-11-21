/-
論文1098『指数が次元に等しい格子の和では、形は縁までの距離の対数の平均として入る』の芯（格上げの一部）。

原稿（1098_yamagishi_shape_enters_a_border_lattice_sum_as_the_mean_log_distance_to_the_edge/…_jp.tex）は、
Σ_{n ∈ Z^d ∩ RS, n ≠ 0} K(n/|n|)/|n|^d = (∫K dΩ) ln R + F_d[K] + ∫K ln ρ_S dΩ + O(1/R) という分け方を
1〜8 次元の数値（テータ関数の道・平方の和の道・格子で直接足した数）で確かめ、K = 1 では
同じ体積の形のうち球のときだけ和の定数が最大になると述べる。

ここで証明した言明（芯だけ：「同じ体積なら球が最大」のイェンセンの一歩）：
  (1) `mean_log_le_log_mean`：全体の重さ c > 0 の有限の測度と、正で積分できる g（log g も積分できる）で
      ∫ log g ≤ c·log((∫ g)/c)（対数の凹性。接線 log y ≤ log m + y/m − 1 を積分して示した）。
      `mean_log_eq_iff`：等号 ⇔ g がほとんどいたるところ定数 (∫ g)/c。
  (2) `ball_maximizes`：向きの測度（球面の面積の測度など、全体の重さ c）の上で、縁までの距離 ρ > 0 の
      形の体積を Vol = (1/d)∫ρ^d dΩ とし、同じ体積の球の半径を r_V（c·r_V^d/d = Vol）とすると
      ∫ ln ρ dΩ ≤ c·ln r_V、等号 ⇔ ρ = r_V（ほとんどいたるところ）（`ball_maximizes_eq_iff`）。
      したがって、和の定数の形の項 ∫ ln ρ_S dΩ（K = 1）は、同じ体積なら原点を中心とする球で最大、
      それも球のときだけ。
足した仮定：体積の極座標の式 Vol = (1/d)∫ρ^d dΩ、格子の 1 点あたりの体積を 1 にそろえること、
和の分け方そのもの（定数 = F_d + ∫ ln ρ_S dΩ）は入力として置いた（漸近の分け方と O(1/R) の評価は形式化していない）。
形式化していないもの：格子の和の漸近の式と誤差の評価、F_d の値、cos4θ・cos6θ の閉じた形、
楕円・立方体の数値、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1098

open Real MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- 各点の接線：log y ≤ log m + y/m − 1（y, m > 0）。 -/
theorem log_tangent {y m : ℝ} (hy : 0 < y) (hm : 0 < m) : log y ≤ log m + y / m - 1 := by
  have := log_le_sub_one_of_pos (div_pos hy hm)
  rw [log_div (ne_of_gt hy) (ne_of_gt hm)] at this
  linarith

omit [IsFiniteMeasure μ] in
theorem integral_pos_of_pos' {g : X → ℝ} (hc : 0 < μ.real Set.univ) (hg : ∀ x, 0 < g x)
    (hgi : Integrable g μ) : 0 < ∫ x, g x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (hg x).le) hgi]
  have : Function.support g = Set.univ := by
    ext x; simp only [Function.mem_support, Set.mem_univ, iff_true]; exact ne_of_gt (hg x)
  rw [this]
  have : μ Set.univ ≠ 0 := by
    intro h; rw [measureReal_def, h] at hc; simp at hc
  exact pos_iff_ne_zero.mpr this

/-- (1) ∫ log g ≤ c·log((∫ g)/c)。 -/
theorem mean_log_le_log_mean {g : X → ℝ} (hc : 0 < μ.real Set.univ) (hg : ∀ x, 0 < g x)
    (hgi : Integrable g μ) (hlog : Integrable (fun x => log (g x)) μ) :
    ∫ x, log (g x) ∂μ ≤ μ.real Set.univ * log ((∫ x, g x ∂μ) / μ.real Set.univ) := by
  set c := μ.real Set.univ
  have hI := integral_pos_of_pos' μ hc hg hgi
  set m := (∫ x, g x ∂μ) / c
  have hm : 0 < m := div_pos hI hc
  have hrhs : Integrable (fun x => log m + g x / m - 1) μ :=
    ((integrable_const _).add (hgi.div_const m)).sub (integrable_const _)
  calc ∫ x, log (g x) ∂μ ≤ ∫ x, (log m + g x / m - 1) ∂μ :=
        integral_mono hlog hrhs (fun x => log_tangent (hg x) hm)
    _ = c * log m := by
        have hA : Integrable (fun x => log m + g x / m) μ :=
            (integrable_const _).add (hgi.div_const m)
        have hB : Integrable (fun _ : X => (1 : ℝ)) μ := integrable_const _
        have hC : Integrable (fun _ : X => log m) μ := integrable_const _
        have hD : Integrable (fun x => g x / m) μ := hgi.div_const m
        rw [integral_sub hA hB, integral_add hC hD, integral_const, integral_const, integral_div]
        simp only [smul_eq_mul]
        have : (∫ x, g x ∂μ) / m = c := by simp only [m]; field_simp
        rw [this]; ring

/-- (1) 等号 ⇔ g = (∫ g)/c（ほとんどいたるところ）。 -/
theorem mean_log_eq_iff {g : X → ℝ} (hc : 0 < μ.real Set.univ) (hg : ∀ x, 0 < g x)
    (hgi : Integrable g μ) (hlog : Integrable (fun x => log (g x)) μ) :
    ∫ x, log (g x) ∂μ = μ.real Set.univ * log ((∫ x, g x ∂μ) / μ.real Set.univ) ↔
      ∀ᵐ x ∂μ, g x = (∫ x, g x ∂μ) / μ.real Set.univ := by
  set c := μ.real Set.univ
  have hI := integral_pos_of_pos' μ hc hg hgi
  set m := (∫ x, g x ∂μ) / c
  have hm : 0 < m := div_pos hI hc
  -- h = log m + g/m − 1 − log g ≥ 0、∫ h = c log m − ∫ log g
  set h : X → ℝ := fun x => log m + g x / m - 1 - log (g x)
  have hh0 : ∀ x, 0 ≤ h x := fun x => by have := log_tangent (hg x) hm; simp only [h]; linarith
  have hhi : Integrable h μ :=
    (((integrable_const _).add (hgi.div_const m)).sub (integrable_const _)).sub hlog
  have hint : ∫ x, h x ∂μ = c * log m - ∫ x, log (g x) ∂μ := by
    simp only [h]
    have hA : Integrable (fun x => log m + g x / m) μ := (integrable_const _).add (hgi.div_const m)
    have hB : Integrable (fun _ : X => (1 : ℝ)) μ := integrable_const _
    have hC : Integrable (fun _ : X => log m) μ := integrable_const _
    have hD : Integrable (fun x => g x / m) μ := hgi.div_const m
    have hE : Integrable (fun x => log m + g x / m - 1) μ := hA.sub hB
    rw [integral_sub hE hlog, integral_sub hA hB,
        integral_add hC hD, integral_const, integral_const,
      integral_div]
    simp only [smul_eq_mul]
    have : (∫ x, g x ∂μ) / m = c := by simp only [m]; field_simp
    rw [this]; ring
  constructor
  · intro heq
    have h0 : ∫ x, h x ∂μ = 0 := by rw [hint, heq]; ring
    have hae := (integral_eq_zero_iff_of_nonneg hh0 hhi).mp h0
    filter_upwards [hae] with x hx
    simp only [h, Pi.zero_apply] at hx
    -- log(g/m) = g/m − 1 ⇒ g/m = 1
    by_contra hne
    have hne' : g x / m ≠ 1 := by
      intro h1; apply hne; field_simp at h1; linarith
    have := log_lt_sub_one_of_pos (div_pos (hg x) hm) hne'
    rw [log_div (ne_of_gt (hg x)) (ne_of_gt hm)] at this
    linarith
  · intro hae
    have hh : ∀ᵐ x ∂μ, h x = 0 := by
      filter_upwards [hae] with x hx
      simp only [h]; rw [hx]; field_simp; ring
    have : ∫ x, h x ∂μ = 0 := by rw [integral_congr_ae hh]; simp
    linarith

/-- (2) 同じ体積なら球が最大：∫ ln ρ ≤ c·ln r_V（c·r_V^d/d = Vol = (1/d)∫ρ^d）。 -/
theorem ball_maximizes {ρ : X → ℝ} {d : ℕ} (hd : 0 < d) (hc : 0 < μ.real Set.univ)
    (hρ : ∀ x, 0 < ρ x) (hi : Integrable (fun x => ρ x ^ d) μ)
        (hl : Integrable (fun x => log (ρ x)) μ)
    {rV : ℝ} (hvol : μ.real Set.univ * rV ^ d / d = (1 / d) * ∫ x, ρ x ^ d ∂μ) :
    ∫ x, log (ρ x) ∂μ ≤ μ.real Set.univ * log rV := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog' : Integrable (fun x => log (ρ x ^ d)) μ := by
    have : (fun x => log (ρ x ^ d)) = fun x => (d : ℝ) * log (ρ x) := by ext x; rw [log_pow]
    rw [this]; exact hl.const_mul _
  have key := mean_log_le_log_mean μ hc (fun x => pow_pos (hρ x) d) hi hlog'
  have hm : (∫ x, ρ x ^ d ∂μ) / μ.real Set.univ = rV ^ d := by
    field_simp at hvol ⊢; linarith
  rw [hm, log_pow] at key
  have : ∫ x, log (ρ x ^ d) ∂μ = d * ∫ x, log (ρ x) ∂μ := by
    rw [← integral_const_mul]; congr 1; ext x; rw [log_pow]
  rw [this] at key
  nlinarith

/-- (2) 等号 ⇔ ρ = r_V（ほとんどいたるところ）、すなわち球のときだけ。 -/
theorem ball_maximizes_eq_iff {ρ : X → ℝ} {d : ℕ} (hd : 0 < d) (hc : 0 < μ.real Set.univ)
    (hρ : ∀ x, 0 < ρ x) (hi : Integrable (fun x => ρ x ^ d) μ)
        (hl : Integrable (fun x => log (ρ x)) μ)
    {rV : ℝ} (hrV : 0 < rV) (hvol : μ.real Set.univ * rV ^ d / d = (1 / d) * ∫ x, ρ x ^ d ∂μ) :
    ∫ x, log (ρ x) ∂μ = μ.real Set.univ * log rV ↔ ∀ᵐ x ∂μ, ρ x = rV := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog' : Integrable (fun x => log (ρ x ^ d)) μ := by
    have : (fun x => log (ρ x ^ d)) = fun x => (d : ℝ) * log (ρ x) := by ext x; rw [log_pow]
    rw [this]; exact hl.const_mul _
  have key := mean_log_eq_iff μ hc (fun x => pow_pos (hρ x) d) hi hlog'
  have hm : (∫ x, ρ x ^ d ∂μ) / μ.real Set.univ = rV ^ d := by
    field_simp at hvol ⊢; linarith
  rw [hm, log_pow] at key
  have : ∫ x, log (ρ x ^ d) ∂μ = d * ∫ x, log (ρ x) ∂μ := by
    rw [← integral_const_mul]; congr 1; ext x; rw [log_pow]
  rw [this] at key
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd'
  constructor
  · intro h
    have := key.mp (by rw [h]; ring)
    filter_upwards [this] with x hx
    exact (pow_left_inj₀ (hρ x).le hrV.le (by omega : d ≠ 0)).mp hx
  · intro h
    have := key.mpr (by filter_upwards [h] with x hx; rw [hx])
    apply mul_left_cancel₀ hdne
    linarith

end Paper1098

end Yamagishi
