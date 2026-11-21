/-
論文208『曲率は、次元と同じ仕事をする』の格上げ（一般の形・評価の形）。

原稿（208_yamagishi_curvature_does_the_work_of_dimension/…_jp.tex）は、三次元（曲率 −1）の双曲空間で、
半径 r の測地球のうち外側の厚さ 1 の殻が占める割合を r = 2〜20 の 6 点で数え、1 − e^(−2) と照合し、
平らな m 次元で同じ割合になる次元を r = 3〜50 の 5 点で数えて「半径の二倍」と述べている。

ここで証明した言明（曲率 −κ²、κ > 0、次元 n は自然数。球の体積は V(r) = ∫₀^r sinh(κs)^(n−1) ds に
比例する）：
  (1) `sinh_shift_le`：s ≥ t ≥ 0 で sinh(κ(s − t)) ≤ e^(−κt) sinh(κs)。
  (2) `volume_ratio_le`：すべての r ≥ t ≥ 0 で V(r − t) ≤ e^(−(n−1)κt) V(r)。したがって
      `shell_fraction_ge`：V(r) > 0 なら、厚さ t の殻の割合 1 − V(r − t)/V(r) は 1 − e^(−(n−1)κt) 以上。
      極限 r → ∞ だけでなく、どの半径でもこの下限を超える（極限の値はこの下限に等しいと下読みの AI は
      述べるが、極限そのものはここでは示していない）。曲率と次元は積 (n − 1)κ でしか効かない。
  (3) `flat_dim_eq`・`flat_dim_bounds`：平らな m 次元で厚さ 1 の殻の割合 1 − (1 − 1/r)^m を 1 − e^(−2) に
      合わせる次元は m = −2/ln(1 − 1/r) で、r > 1 なら 2r − 2 ≤ m ≤ 2r（「半径の二倍」の正確な幅）。
形式化していないもの：r → ∞ での割合の極限と、表面積÷体積 → (n − 1)κ（ロピタルの定理の ∞/∞ 型が
要る）、m = 2r − 1 − 1/(6r) + … の展開、球の体積の公式そのもの（被積分関数として定義に置いた）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper208

open Real Set intervalIntegral

/-- 体積の被積分関数 sinh(κs)^(n−1)。 -/
noncomputable def w (κ : ℝ) (n : ℕ) (s : ℝ) : ℝ := sinh (κ * s) ^ (n - 1)

/-- 半径 r の球の体積（定数倍を除く）。 -/
noncomputable def V (κ : ℝ) (n : ℕ) (r : ℝ) : ℝ := ∫ s in (0 : ℝ)..r, w κ n s

/-- (1) sinh(κ(s − t)) ≤ e^(−κt) sinh(κs)。 -/
theorem sinh_shift_le {κ s t : ℝ} (hκ : 0 < κ) (ht : 0 ≤ t) :
    sinh (κ * (s - t)) ≤ exp (-(κ * t)) * sinh (κ * s) := by
  rw [sinh_eq, sinh_eq]
  have h1 : exp (-(κ * t)) * exp (κ * s) = exp (κ * (s - t)) := by rw [← exp_add]; ring_nf
  have h2 : exp (-(κ * t)) * exp (-(κ * s)) ≤ exp (-(κ * (s - t))) := by
    rw [← exp_add]; apply exp_le_exp.2; nlinarith
  nlinarith

theorem w_nonneg {κ : ℝ} (hκ : 0 < κ) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ w κ n s := by
  unfold w
  exact pow_nonneg (sinh_nonneg_iff.2 (by positivity)) _

theorem w_shift_le {κ : ℝ} (hκ : 0 < κ) (n : ℕ) {s t : ℝ} (ht : 0 ≤ t) (hst : t ≤ s) :
    w κ n (s - t) ≤ exp (-((n - 1 : ℕ) * κ * t)) * w κ n s := by
  unfold w
  have h0 : 0 ≤ sinh (κ * (s - t)) := sinh_nonneg_iff.2 (by nlinarith)
  have := pow_le_pow_left₀ h0 (sinh_shift_le (s := s) hκ ht) (n - 1)
  rw [show -(((n - 1 : ℕ) : ℝ) * κ * t) = ((n - 1 : ℕ) : ℝ) * -(κ * t) by ring, exp_natCast_mul,
    ← mul_pow]
  exact this

theorem continuous_w (κ : ℝ) (n : ℕ) : Continuous (w κ n) := by unfold w; fun_prop

/-- (2) V(r − t) ≤ e^(−(n−1)κt) V(r)。 -/
theorem volume_ratio_le {κ : ℝ} (hκ : 0 < κ) (n : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : t ≤ r) :
    V κ n (r - t) ≤ exp (-((n - 1 : ℕ) * κ * t)) * V κ n r := by
  set c := exp (-((n - 1 : ℕ) * κ * t))
  have hc : 0 ≤ c := (exp_pos _).le
  have hwc := continuous_w κ n
  -- V(r − t) = ∫_t^r w(s − t) ds
  have h1 : V κ n (r - t) = ∫ s in t..r, w κ n (s - t) := by
    have := intervalIntegral.integral_comp_sub_right (w κ n) (a := t) (b := r) t
    rw [sub_self] at this
    unfold V
    exact this.symm
  -- ∫_t^r w(s − t) ≤ c ∫_t^r w(s)
  have h2 : ∫ s in t..r, w κ n (s - t) ≤ ∫ s in t..r, c * w κ n s := by
    apply integral_mono_on hr
    · exact (hwc.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
    · exact (continuous_const.mul hwc).intervalIntegrable _ _
    · intro s hs
      exact w_shift_le hκ n ht hs.1
  -- ∫_t^r w ≤ ∫_0^r w
  have h3 : ∫ s in t..r, w κ n s ≤ V κ n r := by
    unfold V
    have hadd := integral_add_adjacent_intervals (a := 0) (b := t) (c := r)
      (hwc.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
      (hwc.intervalIntegrable (μ := MeasureTheory.volume) t r)
    have : 0 ≤ ∫ s in (0 : ℝ)..t, w κ n s :=
      integral_nonneg ht (fun s hs => w_nonneg hκ n hs.1)
    linarith
  rw [h1]
  calc ∫ s in t..r, w κ n (s - t) ≤ ∫ s in t..r, c * w κ n s := h2
    _ = c * ∫ s in t..r, w κ n s := integral_const_mul _ _
    _ ≤ c * V κ n r := mul_le_mul_of_nonneg_left h3 hc

/-- (2) 殻の割合は 1 − e^(−(n−1)κt) 以上。 -/
theorem shell_fraction_ge {κ : ℝ} (hκ : 0 < κ) (n : ℕ) {r t : ℝ} (ht : 0 ≤ t) (hr : t ≤ r)
    (hV : 0 < V κ n r) :
    1 - exp (-((n - 1 : ℕ) * κ * t)) ≤ 1 - V κ n (r - t) / V κ n r := by
  have := volume_ratio_le hκ n ht hr
  have : V κ n (r - t) / V κ n r ≤ exp (-((n - 1 : ℕ) * κ * t)) := by
    rw [div_le_iff₀ hV]; exact this
  linarith

/-- 平らな側で合わせる次元。 -/
noncomputable def flatDim (r : ℝ) : ℝ := -2 / log (1 - 1 / r)

/-- (3) (1 − 1/r)^m = e^(−2) ⇔ m = −2/ln(1 − 1/r)（r > 1）。 -/
theorem flat_dim_eq {r m : ℝ} (hr : 1 < r) :
    (1 - 1 / r) ^ m = exp (-2) ↔ m = flatDim r := by
  have hx0 : 0 < 1 - 1 / r := by
    have : 1 / r < 1 := by rw [div_lt_one (by linarith)]; exact hr
    linarith
  have hx1 : 1 - 1 / r < 1 := by
    have : 0 < 1 / r := by positivity
    linarith
  have hl : log (1 - 1 / r) < 0 := log_neg hx0 hx1
  rw [rpow_def_of_pos hx0, exp_eq_exp, flatDim]
  set L := log (1 - 1 / r)
  constructor
  · intro h; rw [eq_div_iff hl.ne]; linarith
  · intro h; rw [h]; field_simp; rw [div_self hl.ne]

/-- (3) 2r − 2 ≤ m ≤ 2r。 -/
theorem flat_dim_bounds {r : ℝ} (hr : 1 < r) : 2 * r - 2 ≤ flatDim r ∧ flatDim r ≤ 2 * r := by
  have hr0 : 0 < r := by linarith
  have hx0 : 0 < 1 - 1 / r := by
    have : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
    linarith
  have hx1 : 1 - 1 / r < 1 := by
    have : 0 < 1 / r := by positivity
    linarith
  have hl : log (1 - 1 / r) < 0 := log_neg hx0 hx1
  -- ln(1 − x) ≤ −x、ln(1 − x) ≥ 1 − 1/(1 − x) = −1/(r − 1)
  have hup : log (1 - 1 / r) ≤ -(1 / r) := by
    have := log_le_sub_one_of_pos hx0; linarith
  have hinv : (1 - 1 / r)⁻¹ = r / (r - 1) := by
    rw [show 1 - 1 / r = (r - 1) / r by field_simp, inv_div]
  have hlow : -(1 / (r - 1)) ≤ log (1 - 1 / r) := by
    have := one_sub_inv_le_log_of_pos hx0
    rw [hinv] at this
    have e : 1 - r / (r - 1) = -(1 / (r - 1)) := by
      have : r - 1 ≠ 0 := by linarith
      field_simp; ring
    linarith
  unfold flatDim
  set L := log (1 - 1 / r)
  have e1 : (2 * r - 2) * (1 / (r - 1)) = 2 := by
    have : r - 1 ≠ 0 := by linarith
    field_simp
  have e2 : 2 * r * (1 / r) = 2 := by field_simp
  constructor
  · rw [le_div_iff_of_neg hl]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r - 2)
      (by linarith : 0 ≤ L + 1 / (r - 1))]
  · rw [div_le_iff_of_neg hl]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r) (by linarith : 0 ≤ -(1 / r) - L)]

end Paper208

end Yamagishi
