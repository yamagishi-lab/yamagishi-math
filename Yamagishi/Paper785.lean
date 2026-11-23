/-
論文785『堆積の速さは測る時間の長さで変わり、窓一年では長い目の 80.152928 倍に見える』の格上げ
（一般の形）。

日本語の一文：毎年の増減が平均 μ・ばらつき σ の正規分布のとき、厚みが残った窓だけで測る速さ r(D) は、
μ が正でも 0 でも負でも窓の長さ D について狭義に減り、長い窓で max(μ, 0) に近づき、μ = 0 ならちょうど
σ√(2/π)/√D である。
English: If yearly changes are N(μ, σ²), the rate measured on windows that kept a positive
thickness, r(D) = E[ΔH | ΔH > 0]/D with ΔH ~ N(μD, σ²D), equals μ + σ²/J(D) with
J(D) = ∫₀^∞ exp(μx/σ² − x²/(2σ²D)) dx; hence r is strictly decreasing in D for every real μ,
r(D) → max(μ, 0) as D → ∞, r(D)√D → σ√(2/π) as D → 0+, and r(D) = σ√(2/π)/√D when μ = 0.

原稿（785_yamagishi_deposition_rate_depends_on_measuring_span/…_jp.tex）は、μ = 0.02 mm・σ = 2 mm の
一組で、切断した正規分布の平均の式から窓 1〜10⁸ 年の九つの値と残る割合を出し、100 万年の乱数の歩みと
比べている。短い窓で σ/√D の形、長い窓で μ に近づくことは言葉で述べるだけ。

ここで証明した言明（σ > 0、D > 0、μ は任意の実数）：
  (1) `r_eq`：r(D) = μ + σ²/J(D)（原稿の式 μ + (σ/√D)φ(z)/Φ(z) の言い換え。ミルズ比を使わない形）。
  (2) `J_strictMonoOn`：J は D について狭義に増える。`r_strictAntiOn`：よって r は (0, ∞) で狭義に減る
      （μ の符号によらない）。
  (3) `r_mu_zero`：μ = 0 なら r(D) = σ√(2/π)/√D（短い窓の傾き −1/2 が厳密になる場合）。
  (4) `r_tendsto_nonneg`：μ ≥ 0 なら D → ∞ で r → μ。`r_tendsto_neg`：μ < 0 なら r → 0。
      すなわち長い窓で r → max(μ, 0)。
  (5) `r_sqrt_tendsto`：どの μ でも D → 0+ で r(D)·√D → σ√(2/π)（短い窓は σ/√D の形）。
足した仮定：増減の正規分布という模型を、密度の形 exp(−(x − μD)²/(2σ²D)) として置いた（条件つき期待値は
二つの積分の比なので、正規化の定数は書いていない）。各窓を別々に見ており、後の侵食は数えていない（原稿と同じ）。
形式化していないもの：μ < 0 で r·D → σ²/|μ| の速さ、残る割合 Φ(z)、数表と乱数の歩み、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper785

open Real Set MeasureTheory Filter Topology

/-- 窓 D の増減 ΔH ~ N(μD, σ²D) の密度の形 g(x) = exp(−(x − μD)²/(2σ²D))（定数を除く）。 -/
noncomputable def g (μ σ D x : ℝ) : ℝ := exp (-(x - μ * D) ^ 2 / (2 * (σ ^ 2 * D)))

/-- 厚みが残った窓だけで測る速さ r(D) = E[ΔH | ΔH > 0]/D。 -/
noncomputable def r (μ σ D : ℝ) : ℝ :=
  (∫ x in Ioi 0, x * g μ σ D x) / (∫ x in Ioi 0, g μ σ D x) / D

/-- J(D) = ∫₀^∞ exp(μx/σ² − x²/(2σ²D)) dx。 -/
noncomputable def J (μ σ D : ℝ) : ℝ :=
  ∫ x in Ioi 0, exp (μ / σ ^ 2 * x - x ^ 2 / (2 * (σ ^ 2 * D)))

section integrability

variable {μ σ D : ℝ}

theorem g_eq (x : ℝ) :
    g μ σ D x = exp (-(1 / (2 * (σ ^ 2 * D))) * (x - μ * D) ^ 2) := by
  unfold g; congr 1; ring

theorem g_integrable (hσ : 0 < σ) (hD : 0 < D) : Integrable (g μ σ D) := by
  have hb : 0 < 1 / (2 * (σ ^ 2 * D)) := by positivity
  have := (integrable_exp_neg_mul_sq hb).comp_sub_right (μ * D)
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [g_eq]

theorem g_mul_integrable (hσ : 0 < σ) (hD : 0 < D) :
    Integrable (fun x => (x - μ * D) * g μ σ D x) := by
  have hb : 0 < 1 / (2 * (σ ^ 2 * D)) := by positivity
  have := (integrable_mul_exp_neg_mul_sq hb).comp_sub_right (μ * D)
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [g_eq]

theorem x_g_integrable (hσ : 0 < σ) (hD : 0 < D) : Integrable (fun x => x * g μ σ D x) := by
  have := (g_mul_integrable (μ := μ) hσ hD).add ((g_integrable (μ := μ) hσ hD).const_mul (μ * D))
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]; ring

end integrability

/-- g の微分：d/dx[−σ²D·g(x)] = (x − μD)·g(x)。 -/
theorem hasDerivAt_g (μ σ D x : ℝ) (hσ : 0 < σ) (hD : 0 < D) :
    HasDerivAt (fun x => -(σ ^ 2 * D) * g μ σ D x) ((x - μ * D) * g μ σ D x) x := by
  unfold g
  have h1 : HasDerivAt (fun x => -(x - μ * D) ^ 2 / (2 * (σ ^ 2 * D)))
      (-(2 * (x - μ * D) ^ 1 * 1) / (2 * (σ ^ 2 * D))) x :=
    (((hasDerivAt_id' x).sub_const (μ * D)).pow 2).neg.div_const _
  have := (h1.exp).const_mul (-(σ ^ 2 * D))
  refine this.congr_deriv ?_
  field_simp

theorem g_tendsto_zero (μ σ D : ℝ) (hσ : 0 < σ) (hD : 0 < D) :
    Tendsto (g μ σ D) atTop (𝓝 0) := by
  have hb : 0 < 1 / (2 * (σ ^ 2 * D)) := by positivity
  have h1 : Tendsto (fun x : ℝ => (x - μ * D) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ (-(μ * D)) tendsto_id)
  have h2 := (h1.const_mul_atTop hb)
  have h3 := tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h2)
  refine h3.congr (fun x => ?_)
  simp only [Function.comp, g_eq]
  congr 1; ring

/-- ∫₀^∞ (x − μD) g = σ²D·g(0)。 -/
theorem integral_shift (μ σ D : ℝ) (hσ : 0 < σ) (hD : 0 < D) :
    ∫ x in Ioi 0, (x - μ * D) * g μ σ D x = σ ^ 2 * D * g μ σ D 0 := by
  have := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (m := 0)
    (f := fun x => -(σ ^ 2 * D) * g μ σ D x)
    (fun x _ => hasDerivAt_g μ σ D x hσ hD) (g_mul_integrable hσ hD).integrableOn
    (by simpa using (g_tendsto_zero μ σ D hσ hD).const_mul (-(σ ^ 2 * D)))
  rw [this]; ring

/-- g(x) = g(0)·exp(μx/σ² − x²/(2σ²D))。 -/
theorem g_factor (μ σ D x : ℝ) (hσ : 0 < σ) (hD : 0 < D) :
    g μ σ D x = g μ σ D 0 * exp (μ / σ ^ 2 * x - x ^ 2 / (2 * (σ ^ 2 * D))) := by
  unfold g
  rw [← exp_add]
  congr 1
  field_simp
  ring

theorem J_integrand_integrable (μ : ℝ) {σ D : ℝ} (hσ : 0 < σ) (hD : 0 < D) :
    Integrable (fun x => exp (μ / σ ^ 2 * x - x ^ 2 / (2 * (σ ^ 2 * D)))) := by
  have h0 : g μ σ D 0 ≠ 0 := (exp_pos _).ne'
  have := (g_integrable (μ := μ) hσ hD).const_mul (g μ σ D 0)⁻¹
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [g_factor μ σ D x hσ hD]
  field_simp

theorem J_pos (μ : ℝ) {σ D : ℝ} (hσ : 0 < σ) (hD : 0 < D) : 0 < J μ σ D := by
  unfold J
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun x => (exp_pos _).le)
    (J_integrand_integrable μ hσ hD).integrableOn]
  have : (Function.support fun x => exp (μ / σ ^ 2 * x - x ^ 2 / (2 * (σ ^ 2 * D)))) ∩ Ioi 0 =
      Ioi 0 := by
    ext x; simp [(exp_pos _).ne']
  rw [this]
  simp

/-- (1) r(D) = μ + σ²/J(D)。 -/
theorem r_eq (μ : ℝ) {σ D : ℝ} (hσ : 0 < σ) (hD : 0 < D) :
    r μ σ D = μ + σ ^ 2 / J μ σ D := by
  have hJ := J_pos μ hσ hD
  have h0 : 0 < g μ σ D 0 := exp_pos _
  have hint : ∫ x in Ioi 0, g μ σ D x = g μ σ D 0 * J μ σ D := by
    unfold J
    rw [← integral_const_mul]
    congr 1; ext x; exact g_factor μ σ D x hσ hD
  have hx : ∫ x in Ioi 0, x * g μ σ D x =
      μ * D * (∫ x in Ioi 0, g μ σ D x) + σ ^ 2 * D * g μ σ D 0 := by
    have hs := integral_shift μ σ D hσ hD
    have e : (fun x => x * g μ σ D x) =
        fun x => (x - μ * D) * g μ σ D x + μ * D * g μ σ D x := by ext x; ring
    rw [e, integral_add (g_mul_integrable hσ hD).integrableOn
      ((g_integrable hσ hD).const_mul (μ * D)).integrableOn, integral_const_mul, hs]
    ring
  unfold r
  rw [hx, hint]
  field_simp

/-! ### 単調性 -/

/-- (2) J は D について狭義に増える。 -/
theorem J_strictMonoOn (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) : StrictMonoOn (J μ σ) (Ioi 0) := by
  intro D1 hD1 D2 hD2 h12
  have hD1' : 0 < D1 := hD1
  have hD2' : 0 < D2 := hD2
  set f1 := fun x => exp (μ / σ ^ 2 * x - x ^ 2 / (2 * (σ ^ 2 * D1)))
  set f2 := fun x => exp (μ / σ ^ 2 * x - x ^ 2 / (2 * (σ ^ 2 * D2)))
  have i1 : IntegrableOn f1 (Ioi 0) := (J_integrand_integrable μ hσ hD1').integrableOn
  have i2 : IntegrableOn f2 (Ioi 0) := (J_integrand_integrable μ hσ hD2').integrableOn
  have hlt : ∀ x ∈ Ioi (0 : ℝ), f1 x < f2 x := by
    intro x hx
    have hx' : 0 < x := hx
    simp only [f1, f2]
    apply exp_lt_exp.mpr
    have : x ^ 2 / (2 * (σ ^ 2 * D2)) < x ^ 2 / (2 * (σ ^ 2 * D1)) :=
      div_lt_div_of_pos_left (by positivity) (by positivity) (by nlinarith [sq_pos_of_pos hσ])
    linarith
  rw [← sub_pos]
  show 0 < (∫ x in Ioi 0, f2 x) - ∫ x in Ioi 0, f1 x
  rw [← integral_sub i2 i1]
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx =>
      (sub_pos.mpr (hlt x hx)).le)) (i2.sub i1)]
  have hsupp : (Function.support fun x => f2 x - f1 x) ∩ Ioi 0 = Ioi 0 := by
    ext x
    simp only [mem_inter_iff, Function.mem_support, and_iff_right_iff_imp]
    intro hx
    exact (sub_pos.mpr (hlt x hx)).ne'
  rw [hsupp]
  simp

/-- (2) r は (0, ∞) で狭義に減る（μ の符号によらない）。 -/
theorem r_strictAntiOn (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) : StrictAntiOn (r μ σ) (Ioi 0) := by
  intro D1 hD1 D2 hD2 h12
  rw [r_eq μ hσ hD1, r_eq μ hσ hD2]
  have hJ := J_strictMonoOn μ hσ hD1 hD2 h12
  have h1 := J_pos μ hσ (show 0 < D1 from hD1)
  have : σ ^ 2 / J μ σ D2 < σ ^ 2 / J μ σ D1 := div_lt_div_of_pos_left (by positivity) h1 hJ
  linarith

/-! ### μ = 0 の厳密な形 -/

theorem J_zero {σ D : ℝ} (hσ : 0 < σ) (hD : 0 < D) :
    J 0 σ D = √(2 * π * σ ^ 2 * D) / 2 := by
  unfold J
  have e : (fun x : ℝ => exp (0 / σ ^ 2 * x - x ^ 2 / (2 * (σ ^ 2 * D)))) =
      fun x => exp (-(1 / (2 * (σ ^ 2 * D))) * x ^ 2) := by
    ext x; congr 1; ring
  rw [e, integral_gaussian_Ioi]
  congr 2
  field_simp

/-- (3) μ = 0 なら r(D) = σ√(2/π)/√D。 -/
theorem r_mu_zero {σ D : ℝ} (hσ : 0 < σ) (hD : 0 < D) :
    r 0 σ D = σ * √(2 / π) / √D := by
  rw [r_eq 0 hσ hD, J_zero hσ hD, zero_add]
  have hA : 0 < √(2 * π * σ ^ 2 * D) := sqrt_pos.mpr (by positivity)
  have hB : 0 < √(2 / π) := sqrt_pos.mpr (by positivity)
  have hC : 0 < √D := sqrt_pos.mpr hD
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  simp only [div_pow, mul_pow]
  rw [sq_sqrt (by positivity), sq_sqrt (by positivity), sq_sqrt (by positivity)]
  field_simp

/-! ### 長い窓の極限 -/

/-- (4) μ ≥ 0 なら D → ∞ で r → μ。 -/
theorem r_tendsto_nonneg {μ σ : ℝ} (hμ : 0 ≤ μ) (hσ : 0 < σ) :
    Tendsto (r μ σ) atTop (𝓝 μ) := by
  have hupper : ∀ D, 0 < D → σ ^ 2 / J μ σ D ≤ σ * √(2 / π) / √D := by
    intro D hD
    rw [← r_mu_zero hσ hD, r_eq 0 hσ hD, zero_add]
    apply div_le_div_of_nonneg_left (by positivity) (J_pos 0 hσ hD)
    unfold J
    apply setIntegral_mono_on (J_integrand_integrable 0 hσ hD).integrableOn
      (J_integrand_integrable μ hσ hD).integrableOn measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    apply exp_le_exp.mpr
    have : 0 ≤ μ / σ ^ 2 * x := by positivity
    simp only [zero_div, zero_mul]
    linarith
  have hlim : Tendsto (fun D => σ * √(2 / π) / √D) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_sqrt_atTop
  have hpart : Tendsto (fun D => σ ^ 2 / J μ σ D) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with D hD
      exact (div_pos (by positivity) (J_pos μ hσ hD)).le
    · filter_upwards [eventually_gt_atTop 0] with D hD
      exact hupper D hD
  have := hpart.const_add μ
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with D hD
  rw [r_eq μ hσ hD]

/-- J(D) → σ²/|μ|（μ < 0、D → ∞）。 -/
theorem J_tendsto_neg {μ σ : ℝ} (hμ : μ < 0) (hσ : 0 < σ) :
    Tendsto (J μ σ) atTop (𝓝 (-(σ ^ 2) / μ)) := by
  have hc : μ / σ ^ 2 < 0 := div_neg_of_neg_of_pos hμ (by positivity)
  have hval : ∫ x in Ioi (0 : ℝ), exp (μ / σ ^ 2 * x) = -(σ ^ 2) / μ := by
    rw [integral_exp_mul_Ioi hc, mul_zero, exp_zero]
    field_simp
  rw [← hval]
  unfold J
  apply tendsto_integral_filter_of_dominated_convergence (fun x => exp (μ / σ ^ 2 * x))
  · exact Eventually.of_forall fun D => (by fun_prop : Continuous
      fun x => exp (μ / σ ^ 2 * x - x ^ 2 / (2 * (σ ^ 2 * D)))).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with D hD
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    have : 0 ≤ x ^ 2 / (2 * (σ ^ 2 * D)) := by positivity
    linarith
  · exact integrableOn_exp_mul_Ioi hc 0
  · refine Eventually.of_forall fun x => ?_
    have h1 : Tendsto (fun D : ℝ => x ^ 2 / (2 * (σ ^ 2 * D))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < σ ^ 2)).const_mul_atTop
          (by norm_num : (0 : ℝ) < 2))
    have h2 := (Real.continuous_exp.tendsto _).comp
      ((tendsto_const_nhds (x := μ / σ ^ 2 * x)).sub h1)
    rw [sub_zero] at h2
    exact h2

/-- (4) μ < 0 なら D → ∞ で r → 0。 -/
theorem r_tendsto_neg {μ σ : ℝ} (hμ : μ < 0) (hσ : 0 < σ) :
    Tendsto (r μ σ) atTop (𝓝 0) := by
  have hJ := J_tendsto_neg hμ hσ
  have hne : -(σ ^ 2) / μ ≠ 0 := div_ne_zero (by have := sq_pos_of_pos hσ; linarith) hμ.ne
  have := (hJ.inv₀ hne).const_mul (σ ^ 2) |>.const_add μ
  have e : μ + σ ^ 2 * (-(σ ^ 2) / μ)⁻¹ = 0 := by
    have : σ ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [e] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with D hD
  rw [r_eq μ hσ hD, div_eq_mul_inv]

/-! ### 短い窓の極限 -/

/-- L(t) = ∫₀^∞ exp(μ t w/σ² − w²/(2σ²)) dw（x = √D·w と置き直した J）。 -/
noncomputable def L (μ σ t : ℝ) : ℝ :=
  ∫ w in Ioi 0, exp (μ / σ ^ 2 * (t * w) - w ^ 2 / (2 * (σ ^ 2 * 1)))

theorem J_eq_sqrt_mul_L (μ : ℝ) {σ D : ℝ} (hσ : 0 < σ) (hD : 0 < D) :
    J μ σ D = √D * L μ σ (√D) := by
  have hs : 0 < √D := sqrt_pos.mpr hD
  have h := integral_comp_mul_left_Ioi
    (fun x => exp (μ / σ ^ 2 * x - x ^ 2 / (2 * (σ ^ 2 * D)))) 0 hs
  rw [mul_zero, smul_eq_mul] at h
  have e : (fun w => exp (μ / σ ^ 2 * (√D * w) - (√D * w) ^ 2 / (2 * (σ ^ 2 * D)))) =
      fun w => exp (μ / σ ^ 2 * (√D * w) - w ^ 2 / (2 * (σ ^ 2 * 1))) := by
    ext w; congr 2; rw [mul_pow, sq_sqrt hD.le]; field_simp
  rw [e] at h
  unfold J L
  rw [h]
  field_simp

theorem L_zero (μ σ : ℝ) : L μ σ 0 = J 0 σ 1 := by
  unfold L J; congr 1; ext w; simp

theorem L_tendsto (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) : Tendsto (L μ σ) (𝓝 0) (𝓝 (L μ σ 0)) := by
  unfold L
  apply tendsto_integral_filter_of_dominated_convergence
    (fun w => exp (|μ| / σ ^ 2 * w - w ^ 2 / (2 * (σ ^ 2 * 1))))
  · exact Eventually.of_forall fun t => (by fun_prop : Continuous
      fun w => exp (μ / σ ^ 2 * (t * w) - w ^ 2 / (2 * (σ ^ 2 * 1)))).aestronglyMeasurable
  · filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
    have ht' : |t| ≤ 1 := by simpa [Real.dist_eq] using ht
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun w hw => ?_
    have hw' : 0 < w := hw
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    have h1 : μ * t ≤ |μ| := (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) ht')
    have h2 : μ / σ ^ 2 * (t * w) ≤ |μ| / σ ^ 2 * w := by
      rw [show μ / σ ^ 2 * (t * w) = (μ * t) * w / σ ^ 2 by ring,
        show |μ| / σ ^ 2 * w = |μ| * w / σ ^ 2 by ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hw'.le) (by positivity)
    linarith
  · exact (J_integrand_integrable |μ| hσ one_pos).integrableOn
  · refine Eventually.of_forall fun w => ?_
    exact ((by fun_prop : Continuous
      fun t => exp (μ / σ ^ 2 * (t * w) - w ^ 2 / (2 * (σ ^ 2 * 1))))).tendsto 0

/-- 短い窓の極限：D → 0+ で r(D)·√D → σ√(2/π)（どの μ でも）。 -/
theorem r_sqrt_tendsto (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun D => r μ σ D * √D) (𝓝[>] 0) (𝓝 (σ * √(2 / π))) := by
  have hs : Tendsto (fun D : ℝ => √D) (𝓝[>] 0) (𝓝 0) := by
    have := (continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hL := (L_tendsto μ hσ).comp hs
  have hL0 : 0 < L μ σ 0 := by rw [L_zero μ σ]; exact J_pos 0 hσ one_pos
  have hval : σ ^ 2 / L μ σ 0 = σ * √(2 / π) := by
    rw [L_zero μ σ]
    have := r_mu_zero hσ one_pos
    rw [r_eq 0 hσ one_pos, zero_add, sqrt_one, div_one] at this
    exact this
  have hlim := (hs.const_mul μ).add ((tendsto_const_nhds (x := σ ^ 2)).div hL hL0.ne')
  rw [mul_zero, zero_add, hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with D hD
  have hD' : 0 < D := hD
  have hsD : 0 < √D := sqrt_pos.mpr hD'
  have hLpos : 0 < L μ σ (√D) := by
    have := J_pos μ hσ hD'
    rw [J_eq_sqrt_mul_L μ hσ hD'] at this
    exact pos_of_mul_pos_right this hsD.le
  show μ * √D + σ ^ 2 / L μ σ (√D) = r μ σ D * √D
  rw [r_eq μ hσ hD', J_eq_sqrt_mul_L μ hσ hD']
  field_simp

end Paper785

end Yamagishi
