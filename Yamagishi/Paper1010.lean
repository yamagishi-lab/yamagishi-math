/-
論文1010『太陽から見た月の道はいつも凸で、凸が崩れる半径は地球と太陽の引きが釣り合う点とほぼ重なる』の
格上げ（一般の形）。

日本語の一文：同じ向きに回る二つの円運動を重ねた道では、曲がりの最小は (aΩ − rω)(aΩ² − rω²) で、
曲がりの向きが入れ替わらないのはこれが正のときに限り、ケプラーの法則を入れると、そのときは
r > a√(m/M)（凸）か r < a·m/M（ループ）のどちらかである。
English: For the sum of two co-rotating circular motions z(t) = a e^(iΩt) + r e^(iωt), the cross
product v × a equals a²Ω³ + r²ω³ + arΩω(Ω + ω)cos((ω − Ω)t), its minimum is
(aΩ − rω)(aΩ² − rω²), and
the path never changes its sense of turning exactly when this product is positive; with Kepler's
law this means r > a√(m/M) (convex) or r < a·m/M (loops).

原稿（1010_yamagishi_moon_path_around_sun_always_convex_boundary_near_equal_pull_point/…_jp.tex）は、
二つの円の重ね合わせで曲がりの最小が 0 になる半径を数値で探し、260850.966 km（式）と
260850.980 km（二分法）、もう一つの符号が変わる半径 454.841 km を出している。三体の積分の境
259214.846 km も数値。因数分解とループの側の境の式は書いていない。

ここで証明した言明（a, r, Ω, ω > 0）：
  (1) `hasDerivAt_px` ほか：位置 (a cos Ωt + r cos ωt, a sin Ωt + r sin ωt) の速度と加速度。
      `cross_eq`：v × a = a²Ω³ + r²ω³ + arΩω(Ω + ω) cos((ω − Ω)t)。
  (2) `cross_ge`：どの t でも v × a ≥ (aΩ − rω)(aΩ² − rω²)。
      `cross_attained`：ω ≠ Ω なら t = π/(ω − Ω)（新月の位置）でちょうどその値をとる。
  (3) `cross_pos_iff`：ω ≠ Ω なら、すべての t で v × a > 0 ⇔ (aΩ − rω)(aΩ² − rω²) > 0。
      `sign_change`：積が負なら、v × a は正の時刻と負の時刻の両方をもつ（曲がりの向きが入れ替わる）。
  (4) `kepler_iff`：Ω²a³ = GM、ω²r³ = Gm、0 < m < M なら、積が正 ⇔ a²m < r²M か rM < am
      （r > a√(m/M) か r < a·m/M）。`convex_iff_kepler`：ω = Ω の場合も含めて、
      すべての t で v × a > 0 ⇔ a²m < r²M か rM < am。
      `loop_ratio`：ループの境 a·m/M を a で割った値は、凸の境 a√(m/M) を a で割った値の二乗。
  (5) `paper_radii`：原稿の定数で、ループの境は 454.840 km と 454.841 km のあいだ、凸の境は
      260850.965 km と 260850.966 km のあいだ（原稿の 454.841 km と 260850.966 km）。
曲がり κ = (v × a)/|v|³ の符号は、速さが 0 でない所では v × a の符号と同じなので、v × a で述べた。
足した仮定：二つの円の模型（地球と月の重心は太陽の周りを半径 a の円で、月は重心の周りを半径 r の円で、
同じ向きに回る）を定義として置いた。ケプラーの法則は仮定として置いた。
形式化していないもの：三体の積分の境 259214.846 km、重力が等しくなる点との近さ、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1010

open Real

/-- 位置の x 成分 a cos Ωt + r cos ωt。 -/
noncomputable def px (a r Ω ω t : ℝ) : ℝ := a * cos (Ω * t) + r * cos (ω * t)
/-- 位置の y 成分 a sin Ωt + r sin ωt。 -/
noncomputable def py (a r Ω ω t : ℝ) : ℝ := a * sin (Ω * t) + r * sin (ω * t)
/-- 速度の x 成分。 -/
noncomputable def vx (a r Ω ω t : ℝ) : ℝ := -(a * Ω * sin (Ω * t)) - r * ω * sin (ω * t)
/-- 速度の y 成分。 -/
noncomputable def vy (a r Ω ω t : ℝ) : ℝ := a * Ω * cos (Ω * t) + r * ω * cos (ω * t)
/-- 加速度の x 成分。 -/
noncomputable def ax (a r Ω ω t : ℝ) : ℝ := -(a * Ω ^ 2 * cos (Ω * t)) - r * ω ^ 2 * cos (ω * t)
/-- 加速度の y 成分。 -/
noncomputable def ay (a r Ω ω t : ℝ) : ℝ := -(a * Ω ^ 2 * sin (Ω * t)) - r * ω ^ 2 * sin (ω * t)

/-- 速度と加速度の外積 v × a。 -/
noncomputable def cross (a r Ω ω t : ℝ) : ℝ :=
  vx a r Ω ω t * ay a r Ω ω t - vy a r Ω ω t * ax a r Ω ω t

theorem hasDerivAt_cos_mul (c t : ℝ) :
    HasDerivAt (fun s => cos (c * s)) (-(c * sin (c * t))) t := by
  have := ((hasDerivAt_id t).const_mul c).cos
  simp only [id, mul_one] at this
  convert this using 1; ring

theorem hasDerivAt_sin_mul (c t : ℝ) :
    HasDerivAt (fun s => sin (c * s)) (c * cos (c * t)) t := by
  have := ((hasDerivAt_id t).const_mul c).sin
  simp only [id, mul_one] at this
  convert this using 1; ring

theorem hasDerivAt_px (a r Ω ω t : ℝ) : HasDerivAt (px a r Ω ω) (vx a r Ω ω t) t := by
  have := ((hasDerivAt_cos_mul Ω t).const_mul a).add ((hasDerivAt_cos_mul ω t).const_mul r)
  unfold px vx
  convert this using 1; ring

theorem hasDerivAt_py (a r Ω ω t : ℝ) : HasDerivAt (py a r Ω ω) (vy a r Ω ω t) t := by
  have := ((hasDerivAt_sin_mul Ω t).const_mul a).add ((hasDerivAt_sin_mul ω t).const_mul r)
  unfold py vy
  convert this using 1; ring

theorem hasDerivAt_vx (a r Ω ω t : ℝ) : HasDerivAt (vx a r Ω ω) (ax a r Ω ω t) t := by
  have := (((hasDerivAt_sin_mul Ω t).const_mul (a * Ω)).neg).sub
    ((hasDerivAt_sin_mul ω t).const_mul (r * ω))
  unfold vx ax
  convert this using 1
  ring

theorem hasDerivAt_vy (a r Ω ω t : ℝ) : HasDerivAt (vy a r Ω ω) (ay a r Ω ω t) t := by
  have := ((hasDerivAt_cos_mul Ω t).const_mul (a * Ω)).add
    ((hasDerivAt_cos_mul ω t).const_mul (r * ω))
  unfold vy ay
  convert this using 1
  ring

/-- (1) 外積の閉じた形。 -/
theorem cross_eq (a r Ω ω t : ℝ) :
    cross a r Ω ω t =
      a ^ 2 * Ω ^ 3 + r ^ 2 * ω ^ 3 + a * r * Ω * ω * (Ω + ω) * cos ((ω - Ω) * t) := by
  unfold cross vx vy ax ay
  rw [show (ω - Ω) * t = ω * t - Ω * t by ring, cos_sub]
  have h1 := sin_sq_add_cos_sq (Ω * t)
  have h2 := sin_sq_add_cos_sq (ω * t)
  linear_combination (a ^ 2 * Ω ^ 3) * h1 + (r ^ 2 * ω ^ 3) * h2

/-- 最小の値の因数分解。 -/
theorem min_factor (a r Ω ω : ℝ) :
    a ^ 2 * Ω ^ 3 + r ^ 2 * ω ^ 3 - a * r * Ω * ω * (Ω + ω) =
      (a * Ω - r * ω) * (a * Ω ^ 2 - r * ω ^ 2) := by ring

/-- (2) どの時刻でも v × a ≥ (aΩ − rω)(aΩ² − rω²)。 -/
theorem cross_ge {a r Ω ω : ℝ} (ha : 0 < a) (hr : 0 < r) (hΩ : 0 < Ω) (hω : 0 < ω) (t : ℝ) :
    (a * Ω - r * ω) * (a * Ω ^ 2 - r * ω ^ 2) ≤ cross a r Ω ω t := by
  rw [cross_eq, ← min_factor]
  have hc := neg_one_le_cos ((ω - Ω) * t)
  have hk : 0 < a * r * Ω * ω * (Ω + ω) := by positivity
  nlinarith

/-- (2) ω ≠ Ω なら、新月の位置 t = π/(ω − Ω) で最小の値をとる。 -/
theorem cross_attained {a r Ω ω : ℝ} (hne : ω ≠ Ω) :
    cross a r Ω ω (π / (ω - Ω)) = (a * Ω - r * ω) * (a * Ω ^ 2 - r * ω ^ 2) := by
  have h : ω - Ω ≠ 0 := sub_ne_zero.mpr hne
  rw [cross_eq, ← min_factor, show (ω - Ω) * (π / (ω - Ω)) = π by field_simp, cos_pi]
  ring

/-- (3) 曲がりの向きが一つにそろう ⇔ 積が正。 -/
theorem cross_pos_iff {a r Ω ω : ℝ} (ha : 0 < a) (hr : 0 < r) (hΩ : 0 < Ω) (hω : 0 < ω)
    (hne : ω ≠ Ω) :
    (∀ t, 0 < cross a r Ω ω t) ↔ 0 < (a * Ω - r * ω) * (a * Ω ^ 2 - r * ω ^ 2) := by
  constructor
  · intro h
    have := h (π / (ω - Ω))
    rwa [cross_attained hne] at this
  · intro h t
    exact lt_of_lt_of_le h (cross_ge ha hr hΩ hω t)

/-- 時刻 0（満月の位置）では v × a はいつも正。 -/
theorem cross_zero_pos {a r Ω ω : ℝ} (ha : 0 < a) (hr : 0 < r) (hΩ : 0 < Ω) (hω : 0 < ω) :
    0 < cross a r Ω ω 0 := by
  rw [cross_eq, mul_zero, cos_zero]
  positivity

/-- (3) 積が負なら、v × a は正の時刻と負の時刻の両方をもつ。 -/
theorem sign_change {a r Ω ω : ℝ} (ha : 0 < a) (hr : 0 < r) (hΩ : 0 < Ω) (hω : 0 < ω)
    (hneg : (a * Ω - r * ω) * (a * Ω ^ 2 - r * ω ^ 2) < 0) :
    ∃ t₁ t₂, cross a r Ω ω t₁ < 0 ∧ 0 < cross a r Ω ω t₂ := by
  have hne : ω ≠ Ω := by
    rintro rfl
    nlinarith [sq_nonneg (a - r), mul_pos hω (mul_pos hω hω)]
  exact ⟨π / (ω - Ω), 0, by rw [cross_attained hne]; exact hneg, cross_zero_pos ha hr hΩ hω⟩

/-- 加速度の差の符号：aΩ² − rω² に a²r² を掛けると G(Mr² − ma²)。 -/
theorem accel_identity {a r Ω ω G m M : ℝ} (hΩ2 : Ω ^ 2 * a ^ 3 = G * M)
    (hω2 : ω ^ 2 * r ^ 3 = G * m) :
    (a * Ω ^ 2 - r * ω ^ 2) * (a ^ 2 * r ^ 2) = G * (M * r ^ 2 - m * a ^ 2) := by
  linear_combination r ^ 2 * hΩ2 - a ^ 2 * hω2

/-- 速さの差の符号：aΩ − rω に (aΩ + rω)·ar を掛けると G(Mr − ma)。 -/
theorem speed_identity {a r Ω ω G m M : ℝ} (hΩ2 : Ω ^ 2 * a ^ 3 = G * M)
    (hω2 : ω ^ 2 * r ^ 3 = G * m) :
    (a * Ω - r * ω) * ((a * Ω + r * ω) * (a * r)) = G * (M * r - m * a) := by
  linear_combination r * hΩ2 - a * hω2

/-- (4) ケプラーの法則を入れた境：積が正 ⇔ a²m < r²M か rM < am。 -/
theorem kepler_iff {a r Ω ω G m M : ℝ} (ha : 0 < a) (hr : 0 < r) (hΩ : 0 < Ω) (hω : 0 < ω)
    (hG : 0 < G) (hm : 0 < m) (hmM : m < M) (hΩ2 : Ω ^ 2 * a ^ 3 = G * M)
    (hω2 : ω ^ 2 * r ^ 3 = G * m) :
    0 < (a * Ω - r * ω) * (a * Ω ^ 2 - r * ω ^ 2) ↔ (a ^ 2 * m < r ^ 2 * M ∨ r * M < a * m) := by
  have hB := accel_identity hΩ2 hω2
  have hA := speed_identity hΩ2 hω2
  have har : 0 < a ^ 2 * r ^ 2 := by positivity
  have hs : 0 < (a * Ω + r * ω) * (a * r) := by positivity
  -- B の符号と A の符号
  have hBpos : 0 < a * Ω ^ 2 - r * ω ^ 2 ↔ a ^ 2 * m < r ^ 2 * M := by
    constructor
    · intro h
      have : 0 < G * (M * r ^ 2 - m * a ^ 2) := by rw [← hB]; positivity
      have := (pos_iff_pos_of_mul_pos this).mp hG
      linarith
    · intro h
      have : 0 < G * (M * r ^ 2 - m * a ^ 2) := mul_pos hG (by linarith)
      rw [← hB] at this
      exact (pos_iff_pos_of_mul_pos this).mpr har
  have hBneg : a * Ω ^ 2 - r * ω ^ 2 < 0 ↔ r ^ 2 * M < a ^ 2 * m := by
    constructor
    · intro h
      have : G * (M * r ^ 2 - m * a ^ 2) < 0 := by rw [← hB]; exact mul_neg_of_neg_of_pos h har
      by_contra hc
      push Not at hc
      nlinarith
    · intro h
      have : G * (M * r ^ 2 - m * a ^ 2) < 0 := mul_neg_of_pos_of_neg hG (by linarith)
      rw [← hB] at this
      by_contra hc
      push Not at hc
      nlinarith
  have hApos : 0 < a * Ω - r * ω ↔ a * m < r * M := by
    constructor
    · intro h
      have : 0 < G * (M * r - m * a) := by rw [← hA]; positivity
      have := (pos_iff_pos_of_mul_pos this).mp hG
      linarith
    · intro h
      have : 0 < G * (M * r - m * a) := mul_pos hG (by linarith)
      rw [← hA] at this
      exact (pos_iff_pos_of_mul_pos this).mpr hs
  have hAneg : a * Ω - r * ω < 0 ↔ r * M < a * m := by
    constructor
    · intro h
      have : G * (M * r - m * a) < 0 := by rw [← hA]; exact mul_neg_of_neg_of_pos h hs
      by_contra hc
      push Not at hc
      nlinarith
    · intro h
      have : G * (M * r - m * a) < 0 := mul_neg_of_pos_of_neg hG (by linarith)
      rw [← hA] at this
      by_contra hc
      push Not at hc
      nlinarith
  -- m < M のもとで、凸の側は速さの側を含み、ループの側は加速度の側に含まれる
  have conv_to_speed : a ^ 2 * m < r ^ 2 * M → a * m < r * M := by
    intro h
    by_contra hc
    push Not at hc
    have hra : r < a := by nlinarith
    have e1 := mul_le_mul_of_nonneg_left hc hr.le
    have e2 := mul_lt_mul_of_pos_right hra (mul_pos ha hm)
    nlinarith
  have loop_to_accel : r * M < a * m → r ^ 2 * M < a ^ 2 * m := by
    intro h
    have hra : r < a := by nlinarith
    have e1 := mul_lt_mul_of_pos_left h hr
    have e2 := mul_lt_mul_of_pos_right hra (mul_pos ha hm)
    nlinarith
  constructor
  · intro h
    rcases (mul_pos_iff.mp h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (hBpos.mp h2)
    · exact Or.inr (hAneg.mp h1)
  · rintro (h | h)
    · exact mul_pos (hApos.mpr (conv_to_speed h)) (hBpos.mpr h)
    · exact mul_pos_of_neg_of_neg (hAneg.mpr h) (hBneg.mpr (loop_to_accel h))

/-- (4) ω = Ω の場合も含めて：曲がりの向きがそろう ⇔ a²m < r²M か rM < am。 -/
theorem convex_iff_kepler {a r Ω ω G m M : ℝ} (ha : 0 < a) (hr : 0 < r) (hΩ : 0 < Ω)
    (hω : 0 < ω) (hG : 0 < G) (hm : 0 < m) (hmM : m < M) (hΩ2 : Ω ^ 2 * a ^ 3 = G * M)
    (hω2 : ω ^ 2 * r ^ 3 = G * m) :
    (∀ t, 0 < cross a r Ω ω t) ↔ (a ^ 2 * m < r ^ 2 * M ∨ r * M < a * m) := by
  by_cases hne : ω = Ω
  · subst hne
    -- 角速度が等しいとき：外積は一定で正、右辺も成り立つ
    have hmr : m * a ^ 3 = M * r ^ 3 := by
      have h1 : G * (m * a ^ 3) = G * (M * r ^ 3) := by
        linear_combination (-a ^ 3) * hω2 + r ^ 3 * hΩ2
      exact mul_left_cancel₀ (ne_of_gt hG) h1
    have hra : r < a := by
      by_contra hc
      push Not at hc
      have : a ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ ha.le hc 3
      nlinarith [pow_pos ha 3]
    constructor
    · intro _
      left
      have h3 : a * (a ^ 2 * m) < a * (r ^ 2 * M) := by
        have : a * (r ^ 2 * M) - a * (a ^ 2 * m) = r ^ 2 * M * (a - r) := by
          linear_combination (-1 : ℝ) * hmr
        nlinarith [mul_pos (mul_pos (pow_pos hr 2) (hm.trans hmM)) (sub_pos.mpr hra)]
      exact lt_of_mul_lt_mul_left h3 ha.le
    · intro _ t
      rw [cross_eq, sub_self, zero_mul, cos_zero]
      positivity
  · rw [cross_pos_iff ha hr hΩ hω hne]
    exact kepler_iff ha hr hΩ hω hG hm hmM hΩ2 hω2

/-- ループの境 a·m/M を a で割った値は、凸の境 a√(m/M) を a で割った値の二乗。 -/
theorem loop_ratio {a m M : ℝ} (ha : 0 < a) (hm : 0 ≤ m) (hM : 0 < M) :
    (a * (m / M)) / a = ((a * √(m / M)) / a) ^ 2 := by
  have : 0 ≤ m / M := div_nonneg hm hM.le
  rw [mul_div_cancel_left₀ _ (ne_of_gt ha), mul_div_cancel_left₀ _ (ne_of_gt ha),
    sq_sqrt this]

/-- (5) 原稿の定数（GM の値、m³/s²）で、二つの境（km）。 -/
theorem paper_radii :
    let a : ℝ := 1.495978707e11
    let m : ℝ := 3.986004418e14 + 4.9028e12
    let M : ℝ := 1.32712440018e20 + 3.986004418e14 + 4.9028e12
    (454.840 < a * (m / M) / 1000 ∧ a * (m / M) / 1000 < 454.841) ∧
    (260850.965 < a * √(m / M) / 1000 ∧ a * √(m / M) / 1000 < 260850.966) := by
  intro a m M
  have ha : (0 : ℝ) < a := by norm_num [a]
  refine ⟨⟨by norm_num [a, m, M], by norm_num [a, m, M]⟩, ?_, ?_⟩
  · have h1 : 260850.965 * 1000 / a < √(m / M) := by
      rw [Real.lt_sqrt (by positivity)]
      norm_num [a, m, M]
    rw [lt_div_iff₀ (by norm_num)]
    exact (div_lt_iff₀' ha).mp h1
  · have h1 : √(m / M) < 260850.966 * 1000 / a := by
      rw [Real.sqrt_lt' (by positivity)]
      norm_num [a, m, M]
    rw [div_lt_iff₀ (by norm_num)]
    exact (lt_div_iff₀' ha).mp h1

end Paper1010

end Yamagishi
