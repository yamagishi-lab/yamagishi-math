/-
論文488『等時であることから曲線を逆に決めると、残るのは一つだけである』の格上げ（芯だけ：等時になる向き）。

原稿（488_yamagishi_solve_the_fall_time_backwards/…_jp.tex）は、落下時間
T(h) = (1/√(2g)) ∫₀^h f′(y)/√(h − y) dy（f は高さ y までの弧長）について、サイクロイドの四つの出発角、
円弧の対照、f′ = 1（鉛直落下）の T ∝ √h、f′ = 1/√y で h = 0.5, 1, 2 の T が同じ値になることを数値で
示している。一意性は証明しないと明言している。

ここで証明した言明（g > 0）：
  (1) `integral_inv_sqrt_mul`：h > 0 で ∫₀^h dy/(√y √(h − y)) = π（原始関数 arcsin(2y/h − 1)）。
  (2) `isochrone`：f′(y) = c/√y なら、すべての h > 0 で T(h) = cπ/√(2g)（高さによらない。等時）。
  (3) `vertical_fall`：f′ = 1 なら T(h) = 2√h/√(2g) = √(2h/g)（T ∝ √h）。
  (4) `planar_range`：c > 0 で f′(y) = c/√y ≥ 1 ⇔ y ≤ c²（弧長の傾きが 1 以上でないと平面の曲線に
      ならないので、等時の範囲には高さの上限 c² がある）。
形式化していないもの：一意性（T が一定なら f′ = c/√y がほとんどいたる所で成り立つ。アーベルの反転と
フビニの定理が要る）。これが格上げの本体なので、ここでは芯だけ。f′ = c/√y がサイクロイドで
あることも扱っていない。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper488

open Real Set intervalIntegral

/-- 落下時間（原稿の式）。 -/
noncomputable def T (g : ℝ) (f' : ℝ → ℝ) (h : ℝ) : ℝ :=
  1 / √(2 * g) * ∫ y in (0 : ℝ)..h, f' y / √(h - y)

/-- 原始関数 arcsin(2y/h − 1) の導関数。 -/
theorem hasDerivAt_F {h y : ℝ} (hh : 0 < h) (hy0 : 0 < y) (hyh : y < h) :
    HasDerivAt (fun y => arcsin (2 * y / h - 1)) (1 / (√y * √(h - y))) y := by
  have hx1 : 2 * y / h - 1 ≠ -1 := by
    intro e; have : 2 * y / h = 0 := by linarith
    rw [div_eq_zero_iff] at this; rcases this with h1 | h1 <;> linarith
  have hx2 : 2 * y / h - 1 ≠ 1 := by
    intro e; have : 2 * y / h = 2 := by linarith
    rw [div_eq_iff hh.ne'] at this; linarith
  have hlin : HasDerivAt (fun y => 2 * y / h - 1) (2 / h) y := by
    have := ((hasDerivAt_id y).const_mul 2).div_const h |>.sub_const 1
    simpa using this
  have := (hasDerivAt_arcsin hx1 hx2).comp y hlin
  refine this.congr_deriv ?_
  have hin : 1 - (2 * y / h - 1) ^ 2 = 4 * (y * (h - y)) / h ^ 2 := by field_simp; ring
  rw [hin, sqrt_div' _ (sq_nonneg h), sqrt_sq hh.le, show (4 : ℝ) * (y * (h - y)) =
    2 ^ 2 * (y * (h - y)) by norm_num, sqrt_mul' _ (by nlinarith), sqrt_sq (by norm_num),
    sqrt_mul hy0.le]
  have : 0 < √y := sqrt_pos.2 hy0
  have : 0 < √(h - y) := sqrt_pos.2 (by linarith)
  field_simp

/-- (1) ∫₀^h dy/(√y √(h − y)) = π。 -/
theorem integral_inv_sqrt_mul {h : ℝ} (hh : 0 < h) :
    ∫ y in (0 : ℝ)..h, 1 / (√y * √(h - y)) = π := by
  have hcont : ContinuousOn (fun y => arcsin (2 * y / h - 1)) (Icc 0 h) :=
    (continuous_arcsin.comp (by fun_prop)).continuousOn
  have hderiv : ∀ y ∈ Ioo 0 h, HasDerivAt (fun y => arcsin (2 * y / h - 1))
      (1 / (√y * √(h - y))) y := fun y hy => hasDerivAt_F hh hy.1 hy.2
  have hint : IntervalIntegrable (fun y => 1 / (√y * √(h - y))) MeasureTheory.volume 0 h := by
    apply intervalIntegrable_deriv_of_nonneg (g := fun y => arcsin (2 * y / h - 1))
    · rw [uIcc_of_le hh.le]; exact hcont
    · intro y hy
      rw [min_eq_left hh.le, max_eq_right hh.le] at hy
      exact hderiv y hy
    · intro y _; positivity
  rw [integral_eq_sub_of_hasDerivAt_of_le hh.le hcont hderiv hint]
  rw [show 2 * h / h - 1 = 1 by field_simp; ring, show 2 * 0 / h - 1 = -1 by ring, arcsin_one,
    arcsin_neg_one]
  ring

/-- (2) f′(y) = c/√y なら等時：T(h) = cπ/√(2g)。 -/
theorem isochrone (g c : ℝ) {h : ℝ} (hh : 0 < h) :
    T g (fun y => c / √y) h = c * π / √(2 * g) := by
  unfold T
  have : (fun y => c / √y / √(h - y)) = fun y => c * (1 / (√y * √(h - y))) := by
    funext y; rw [div_div]; ring
  rw [this, integral_const_mul, integral_inv_sqrt_mul hh]
  ring

/-- (3) 鉛直落下 f′ = 1 では T(h) = 2√h/√(2g)。 -/
theorem vertical_fall (g : ℝ) {h : ℝ} (hh : 0 < h) :
    T g (fun _ => 1) h = 2 * √h / √(2 * g) := by
  unfold T
  have hcont : ContinuousOn (fun y => -(2 * √(h - y))) (Icc 0 h) := by fun_prop
  have hderiv : ∀ y ∈ Ioo 0 h, HasDerivAt (fun y => -(2 * √(h - y))) (1 / √(h - y)) y := by
    intro y hy
    have hpos : 0 < h - y := by linarith [hy.2]
    have := (((hasDerivAt_id' y).const_sub h).sqrt hpos.ne').const_mul 2 |>.neg
    refine this.congr_deriv ?_
    have : 0 < √(h - y) := sqrt_pos.2 hpos
    field_simp
  have hint : IntervalIntegrable (fun y => 1 / √(h - y)) MeasureTheory.volume 0 h := by
    apply intervalIntegrable_deriv_of_nonneg (g := fun y => -(2 * √(h - y)))
    · rw [uIcc_of_le hh.le]; exact hcont
    · intro y hy
      rw [min_eq_left hh.le, max_eq_right hh.le] at hy
      exact hderiv y hy
    · intro y _; positivity
  rw [integral_eq_sub_of_hasDerivAt_of_le hh.le hcont hderiv hint]
  simp
  ring

/-- (4) 平面の曲線になる範囲：c/√y ≥ 1 ⇔ y ≤ c²（c > 0、y > 0）。 -/
theorem planar_range {c y : ℝ} (hc : 0 < c) (hy : 0 < y) : 1 ≤ c / √y ↔ y ≤ c ^ 2 := by
  have : 0 < √y := sqrt_pos.2 hy
  rw [le_div_iff₀ this, one_mul, sqrt_le_left hc.le]

end Paper488

end Yamagishi
