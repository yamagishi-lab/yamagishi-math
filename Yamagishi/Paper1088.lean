/-
論文1088『プラズマ振動数とベーテの式の二つの 4π/m は、出どころが違う』の格上げ（一般の形）。

日本語の一文：d 次元でまっすぐ通り過ぎる近似の止める力の係数は K_d = S_{d−1}·I_d/2 で、I_d は d について
狭義に減るので、プラズマ振動数の係数 S_{d−1} と等しいのは d = 3 のときだけであり、比 K_d/S_{d−1} は
d − 2 次元の球が外接する円柱に占める割合 V_{d−2}/(2V_{d−3}) に等しい。
English: With I_d = ∫_ℝ (1 + u²)^(−d/2) du, the substitution u = tan t gives I_d = ∫₀^π sinᵈ⁻² t dt,
so I_d = S_{d−1}/S_{d−2} (S_n the area of the unit n-sphere); the impulse-approximation stopping
coefficient K_d = S_{d−2} I_d²/2 equals S_{d−1} I_d/2, equals the plasma coefficient S_{d−1} only
for d = 3, and K_d/S_{d−1} = V_{d−2}/(2V_{d−3}); the impact-parameter integral over [b, λb] does
not depend on b only for d = 3.

原稿（1088_yamagishi_two_four_pi_over_m_plasma_frequency_and_stopping_power/…_jp.tex）は、d = 3〜6 で
I_d、K_d、S_{d−1} と比 1、π/4、2/3、3π/16 を数値で出し、I_d = S_{d−1}/S_{d−2} と、比が球と円柱の割合と
一致することを数値で確かめている。d = 3 だけで一致することの一般の証明は無い。

ここで証明した言明（d は 2 以上の自然数）：
  (1) `W_closed`：ワリスの積分 W_n = ∫₀^π sinⁿ t dt = √π·Γ((n + 1)/2)/Γ(n/2 + 1)。
      `W_strictAnti`：W_n は n について狭義に減る。`W_values`：W₁ = 2、W₂ = π/2、W₃ = 4/3、W₄ = 3π/8。
  (2) `I_eq_W`：I_d = ∫_ℝ (1 + u²)^(−d/2) du = W_{d−2}（u = tan t の置き換え）。
      `impulse`：渡す運動量の積分 ∫ b(b² + v²t²)^(−d/2) dt = I_d/(v·b^(d−2))（b, v > 0）。
  (3) `S_mul_W`：S_n·W_n = S_{n+1}（S_n = 2π^((n+1)/2)/Γ((n+1)/2) は単位 n 次元球面の面積）。
      `I_eq_ratio`：よって I_d = S_{d−1}/S_{d−2}。`S_eq_V`：S_n = (n + 1)·V_{n+1}。
      `V_eq_volume`：V_n = √π^n/Γ(n/2 + 1) は Mathlib の n 次元の単位球の体積そのもの。
  (4) `K_eq`：K_d = S_{d−2}·I_d²/2 = S_{d−1}·I_d/2。
      `K_eq_plasma_iff`：K_d = S_{d−1} ⇔ d = 3。
      `ratio_values`：K_d/S_{d−1} は d = 3・4・5・6 で 1、π/4、2/3、3π/16。
      `ratio_cylinder`：d ≥ 3 で K_d/S_{d−1} = V_{d−2}/(2V_{d−3})（外接する円柱に占める割合）。
  (5) `log_only_three`：λ > 1 で、すべての b > 0 で ∫_b^{λb} x^(−k) dx が b によらない ⇔ k = 1
      （k = d − 2、つまり d = 3 だけで衝突径数の積分は対数になる）。
足した仮定：力 e²/r^(d−1) とまっすぐ通り過ぎる近似（電子が受け取るエネルギー (Δp)²/2m、半径 b の殻の
広さ S_{d−2}b^(d−2)）から K_d = S_{d−2}I_d²/2 とする組み立てを、原稿のとおり定義として置いた。
プラズマ振動数の係数が S_{d−1}（ガウスの法則の立体角）であることも定義として置いた。
形式化していないもの：近い衝突と対数の中身、電荷の面の場の数値の積分、軌道の数値解、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1088

open Real Set MeasureTheory intervalIntegral

/-! ### ワリスの積分 -/

/-- W_n = ∫₀^π sinⁿ t dt。 -/
noncomputable def W (n : ℕ) : ℝ := ∫ x in (0 : ℝ)..π, sin x ^ n

theorem W_zero : W 0 = π := by simp [W]

theorem W_one : W 1 = 2 := by
  simp only [W, pow_one, integral_sin, cos_zero, cos_pi]; norm_num

theorem W_add_two (n : ℕ) : W (n + 2) = (n + 1) / (n + 2) * W n := by
  unfold W
  rw [integral_sin_pow]
  simp

/-- (1) W_n の閉じた形。 -/
theorem W_closed (n : ℕ) : W n = √π * Gamma ((n + 1) / 2) / Gamma (n / 2 + 1) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [W_zero]
    simp only [Nat.cast_zero, zero_add, zero_div, Gamma_one, div_one]
    rw [Gamma_one_half_eq, mul_self_sqrt pi_pos.le]
  | one =>
    rw [W_one]
    simp only [Nat.cast_one]
    rw [show ((1 : ℝ) + 1) / 2 = 1 by norm_num, Gamma_one, Gamma_add_one (by norm_num),
      Gamma_one_half_eq]
    have := sqrt_pos.mpr pi_pos
    field_simp
  | more n ih _ =>
    rw [W_add_two, ih]
    push_cast
    have g1 : Gamma ((n + 1) / 2 + 1) = (n + 1) / 2 * Gamma ((n + 1) / 2) :=
      Gamma_add_one (by positivity)
    have g2 : Gamma ((n / 2 + 1) + 1) = (n / 2 + 1) * Gamma (n / 2 + 1) :=
      Gamma_add_one (by positivity)
    rw [show ((n : ℝ) + 2 + 1) / 2 = (n + 1) / 2 + 1 by ring,
      show ((n : ℝ) + 2) / 2 + 1 = (n / 2 + 1) + 1 by ring, g1, g2]
    have h1 : 0 < Gamma ((n + 1) / 2) := Gamma_pos_of_pos (by positivity)
    have h2 : 0 < Gamma (n / 2 + 1) := Gamma_pos_of_pos (by positivity)
    field_simp

theorem W_pos (n : ℕ) : 0 < W n := by unfold W; exact integral_sin_pow_pos n

/-- (1) W_{n+1} < W_n。 -/
theorem W_succ_lt (n : ℕ) : W (n + 1) < W n := by
  unfold W
  apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt pi_pos
    (by fun_prop) (by fun_prop)
  · intro x hx
    have h0 : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx.1.le hx.2
    have h1 : sin x ≤ 1 := sin_le_one x
    calc sin x ^ (n + 1) = sin x ^ n * sin x := pow_succ _ _
      _ ≤ sin x ^ n * 1 := mul_le_mul_of_nonneg_left h1 (pow_nonneg h0 n)
      _ = sin x ^ n := mul_one _
  · refine ⟨π / 6, ⟨by positivity, by linarith [pi_pos]⟩, ?_⟩
    rw [sin_pi_div_six, pow_succ]
    have : (0 : ℝ) < (1 / 2) ^ n := by positivity
    linarith

theorem W_strictAnti : StrictAnti W := strictAnti_nat_of_succ_lt W_succ_lt

theorem W_values : W 1 = 2 ∧ W 2 = π / 2 ∧ W 3 = 4 / 3 ∧ W 4 = 3 * π / 8 := by
  have h2 : W 2 = π / 2 := by rw [W_add_two, W_zero]; norm_num; ring
  have h3 : W 3 = 4 / 3 := by rw [W_add_two, W_one]; norm_num
  have h4 : W 4 = 3 * π / 8 := by rw [W_add_two, h2]; norm_num; ring
  exact ⟨W_one, h2, h3, h4⟩

/-! ### I_d と u = tan t -/

/-- I_d = ∫_ℝ (1 + u²)^(−d/2) du。 -/
noncomputable def I (d : ℕ) : ℝ := ∫ u : ℝ, (1 + u ^ 2) ^ (-(d : ℝ) / 2)

theorem integrand_tan {d : ℕ} (hd : 2 ≤ d) {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    |1 / cos x ^ 2| • (1 + tan x ^ 2) ^ (-(d : ℝ) / 2) = cos x ^ (d - 2) := by
  have hc : 0 < cos x := cos_pos_of_mem_Ioo hx
  have h1 : 1 + tan x ^ 2 = (cos x ^ 2)⁻¹ := by
    rw [← inv_one_add_tan_sq (ne_of_gt hc), inv_inv]
  rw [h1, smul_eq_mul, abs_of_pos (by positivity), inv_rpow (by positivity), ← rpow_neg
    (by positivity), neg_div, neg_neg, ← rpow_natCast (cos x) 2, ← rpow_mul hc.le,
    show ((2 : ℕ) : ℝ) * ((d : ℝ) / 2) = (d : ℝ) by push_cast; ring, rpow_natCast]
  have : cos x ^ d = cos x ^ (d - 2) * cos x ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  rw [rpow_natCast, this]
  field_simp

/-- (2) I_d = W_{d−2}（u = tan t）。 -/
theorem I_eq_W {d : ℕ} (hd : 2 ≤ d) : I d = W (d - 2) := by
  unfold I W
  rw [← setIntegral_univ, ← image_tan_Ioo,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun x hx => (hasDerivAt_tan (ne_of_gt (cos_pos_of_mem_Ioo hx))).hasDerivWithinAt) injOn_tan,
    setIntegral_congr_fun measurableSet_Ioo (fun x hx => integrand_tan hd hx),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  have := intervalIntegral.integral_comp_sub_right (fun x => cos x ^ (d - 2)) (a := 0) (b := π)
    (π / 2)
  simp only [cos_sub_pi_div_two] at this
  rw [this]
  congr 1 <;> ring

/-- (2) 渡す運動量の積分：∫ b(b² + v²t²)^(−d/2) dt = I_d/(v·b^(d−2))。 -/
theorem impulse {d : ℕ} (hd : 2 ≤ d) {b v : ℝ} (hb : 0 < b) (hv : 0 < v) :
    ∫ t : ℝ, b * (b ^ 2 + v ^ 2 * t ^ 2) ^ (-(d : ℝ) / 2) = I d / (v * b ^ (d - 2)) := by
  have hpt : ∀ t : ℝ, b * (b ^ 2 + v ^ 2 * t ^ 2) ^ (-(d : ℝ) / 2) =
      b * (b ^ 2) ^ (-(d : ℝ) / 2) * (1 + (v / b * t) ^ 2) ^ (-(d : ℝ) / 2) := by
    intro t
    rw [show b ^ 2 + v ^ 2 * t ^ 2 = b ^ 2 * (1 + (v / b * t) ^ 2) by field_simp,
      mul_rpow (by positivity) (by positivity)]
    ring
  simp_rw [hpt]
  rw [MeasureTheory.integral_const_mul, Measure.integral_comp_mul_left
    (fun u => (1 + u ^ 2) ^ (-(d : ℝ) / 2)) (v / b)]
  unfold I
  rw [smul_eq_mul, abs_of_pos (by positivity)]
  have hb2 : (b ^ 2) ^ (-(d : ℝ) / 2) = (b ^ d)⁻¹ := by
    rw [← rpow_natCast b 2, ← rpow_mul hb.le, show ((2 : ℕ) : ℝ) * (-(d : ℝ) / 2) = -(d : ℝ) by
      push_cast; ring, rpow_neg hb.le, rpow_natCast]
  rw [hb2]
  have hbd : b ^ d = b ^ (d - 2) * b ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hd]
  rw [hbd]
  have : b ^ (d - 2) ≠ 0 := by positivity
  field_simp

/-! ### 球面の面積と球の体積 -/

/-- 単位 n 次元球面（ℝ^(n+1) の中）の面積 S_n = 2√π^(n+1)/Γ((n + 1)/2)。 -/
noncomputable def S (n : ℕ) : ℝ := 2 * √π ^ (n + 1) / Gamma ((n + 1) / 2)

/-- 単位 n 次元球の体積 V_n = √π^n/Γ(n/2 + 1)。 -/
noncomputable def V (n : ℕ) : ℝ := √π ^ n / Gamma (n / 2 + 1)

theorem S_pos (n : ℕ) : 0 < S n := by
  unfold S
  have := Gamma_pos_of_pos (show (0 : ℝ) < (n + 1) / 2 by positivity)
  have := sqrt_pos.mpr pi_pos
  positivity

theorem V_pos (n : ℕ) : 0 < V n := by
  unfold V
  have := Gamma_pos_of_pos (show (0 : ℝ) < n / 2 + 1 by positivity)
  have := sqrt_pos.mpr pi_pos
  positivity

/-- (3) S_n·W_n = S_{n+1}。 -/
theorem S_mul_W (n : ℕ) : S n * W n = S (n + 1) := by
  rw [W_closed]
  unfold S
  push_cast
  rw [show ((n : ℝ) + 1 + 1) / 2 = n / 2 + 1 by ring]
  have h1 : 0 < Gamma ((n + 1) / 2) := Gamma_pos_of_pos (by positivity)
  have h2 : 0 < Gamma (n / 2 + 1) := Gamma_pos_of_pos (by positivity)
  field_simp
  ring

/-- (3) S_n = (n + 1)·V_{n+1}。 -/
theorem S_eq_V (n : ℕ) : S n = (n + 1) * V (n + 1) := by
  unfold S V
  push_cast
  have g1 : Gamma ((n + 1) / 2 + 1) = (n + 1) / 2 * Gamma ((n + 1) / 2) :=
    Gamma_add_one (by positivity)
  rw [g1]
  have h1 : 0 < Gamma ((n + 1) / 2) := Gamma_pos_of_pos (by positivity)
  field_simp

/-- (3) V_{n+1}/V_n = W_{n+1}。 -/
theorem V_ratio (n : ℕ) : V (n + 1) / V n = W (n + 1) := by
  rw [W_closed]
  unfold V
  push_cast
  rw [show ((n : ℝ) + 1 + 1) / 2 = n / 2 + 1 by ring]
  have h1 : 0 < Gamma ((n + 1) / 2 + 1) := Gamma_pos_of_pos (by positivity)
  have h2 : 0 < Gamma (n / 2 + 1) := Gamma_pos_of_pos (by positivity)
  have := sqrt_pos.mpr pi_pos
  field_simp
  ring

/-- (3) V_n は Mathlib の n 次元ユークリッド空間の単位球の体積。 -/
theorem V_eq_volume (n : ℕ) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).toReal = V (n + 1) := by
  rw [EuclideanSpace.volume_ball, ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin,
    ENNReal.toReal_ofReal]
  · unfold V; push_cast; rfl
  · have := Gamma_pos_of_pos (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / 2 + 1 by positivity)
    positivity

/-- (3) I_d = S_{d−1}/S_{d−2}。 -/
theorem I_eq_ratio {d : ℕ} (hd : 2 ≤ d) : I d = S (d - 1) / S (d - 2) := by
  rw [I_eq_W hd, show d - 1 = d - 2 + 1 by omega, ← S_mul_W]
  have := S_pos (d - 2)
  field_simp

/-! ### 二つの係数 -/

/-- 止める力の係数 K_d = S_{d−2}·I_d²/2（まっすぐ通り過ぎる近似の組み立て）。 -/
noncomputable def K (d : ℕ) : ℝ := S (d - 2) * I d ^ 2 / 2

/-- (4) K_d = S_{d−1}·I_d/2。 -/
theorem K_eq {d : ℕ} (hd : 2 ≤ d) : K d = S (d - 1) * I d / 2 := by
  unfold K
  rw [show d - 1 = d - 2 + 1 by omega, ← S_mul_W, I_eq_W hd]
  ring

/-- (4) 止める力の係数がプラズマの係数 S_{d−1} に等しい ⇔ d = 3。 -/
theorem K_eq_plasma_iff {d : ℕ} (hd : 2 ≤ d) : K d = S (d - 1) ↔ d = 3 := by
  rw [K_eq hd, I_eq_W hd]
  have hS := S_pos (d - 1)
  constructor
  · intro h
    have hW : W (d - 2) = W 1 := by
      rw [W_one]
      field_simp at h
      linarith
    have := W_strictAnti.injective hW
    omega
  · intro h
    subst h
    simp only [show 3 - 2 = 1 from rfl, W_one]
    ring

/-- (4) 比 K_d/S_{d−1} は d = 3・4・5・6 で 1、π/4、2/3、3π/16。 -/
theorem ratio_values :
    K 3 / S 2 = 1 ∧ K 4 / S 3 = π / 4 ∧ K 5 / S 4 = 2 / 3 ∧ K 6 / S 5 = 3 * π / 16 := by
  obtain ⟨h1, h2, h3, h4⟩ := W_values
  have e : ∀ d : ℕ, 2 ≤ d → K d / S (d - 1) = W (d - 2) / 2 := by
    intro d hd
    rw [K_eq hd, I_eq_W hd]
    have := S_pos (d - 1)
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := e 3 (by norm_num); simp only [show 3 - 1 = 2 from rfl, show 3 - 2 = 1 from rfl] at this
    rw [this, h1]; norm_num
  · have := e 4 (by norm_num); simp only [show 4 - 1 = 3 from rfl, show 4 - 2 = 2 from rfl] at this
    rw [this, h2]; ring
  · have := e 5 (by norm_num); simp only [show 5 - 1 = 4 from rfl, show 5 - 2 = 3 from rfl] at this
    rw [this, h3]; norm_num
  · have := e 6 (by norm_num); simp only [show 6 - 1 = 5 from rfl, show 6 - 2 = 4 from rfl] at this
    rw [this, h4]; ring

/-- (4) d ≥ 3 で K_d/S_{d−1} = V_{d−2}/(2V_{d−3})（d − 2 次元の球が外接する円柱に占める割合）。 -/
theorem ratio_cylinder {d : ℕ} (hd : 3 ≤ d) : K d / S (d - 1) = V (d - 2) / (2 * V (d - 3)) := by
  rw [K_eq (by omega), I_eq_W (by omega)]
  have hS := S_pos (d - 1)
  have hV := V_pos (d - 3)
  have hr := V_ratio (d - 3)
  rw [show d - 3 + 1 = d - 2 by omega] at hr
  rw [← hr]
  field_simp

/-! ### 衝突径数の積分 -/

theorem integral_scale {k b lam : ℝ} (hb : 0 < b) (hl : 1 < lam) :
    ∫ x in b..lam * b, x ^ (-k) = b ^ (1 - k) * ∫ x in (1 : ℝ)..lam, x ^ (-k) := by
  have h := intervalIntegral.integral_comp_mul_left (fun x => x ^ (-k)) (c := b) (a := 1) (b := lam)
    (ne_of_gt hb)
  simp only [mul_one, smul_eq_mul] at h
  rw [show b * lam = lam * b by ring] at h
  have hcongr : ∫ x in (1 : ℝ)..lam, (b * x) ^ (-k) = b ^ (-k) * ∫ x in (1 : ℝ)..lam, x ^ (-k) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro x hx
    rw [uIcc_of_le hl.le] at hx
    simp only
    rw [mul_rpow hb.le (by linarith [hx.1])]
  rw [hcongr] at h
  have hb0 : b ≠ 0 := ne_of_gt hb
  rw [show (1 : ℝ) - k = 1 + -k by ring, rpow_add hb, rpow_one]
  field_simp at h ⊢
  linarith

/-- (5) すべての b > 0 で ∫_b^{λb} x^(−k) dx が b によらない ⇔ k = 1（d = 3）。 -/
theorem log_only_three {k lam : ℝ} (hl : 1 < lam) :
    (∀ b > 0, ∫ x in b..lam * b, x ^ (-k) = ∫ x in (1 : ℝ)..lam, x ^ (-k)) ↔ k = 1 := by
  have hpos : 0 < ∫ x in (1 : ℝ)..lam, x ^ (-k) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      rw [uIcc_of_le hl.le] at hx
      exact (continuousAt_rpow_const x (-k) (Or.inl (by linarith [hx.1]))).continuousWithinAt
    · intro x hx; exact rpow_pos_of_pos (by linarith [hx.1]) _
    · exact hl
  constructor
  · intro h
    have h2 := h 2 (by norm_num)
    rw [integral_scale (by norm_num) hl] at h2
    have : (2 : ℝ) ^ (1 - k) = 1 := by
      have := mul_right_cancel₀ (ne_of_gt hpos) (h2.trans (one_mul _).symm)
      exact this
    have h3 : (1 - k) * log 2 = 0 := by
      have := congrArg log this
      rwa [log_rpow (by norm_num), log_one] at this
    have : log 2 ≠ 0 := ne_of_gt (log_pos (by norm_num))
    have := (mul_eq_zero.mp h3).resolve_right this
    linarith
  · intro hk b hb
    rw [integral_scale hb hl, hk, sub_self, rpow_zero, one_mul]

end Paper1088

end Yamagishi
