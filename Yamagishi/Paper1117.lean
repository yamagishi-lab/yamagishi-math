/-
論文1117『気体の速さは運動量の球の影で、縮むのは壁の所』の閉じた式のうち、尖り 3n/(n+2) を
すべての n で機械に確かめさせる（格上げの一部）。

原稿（1117_yamagishi_gas_velocity_is_a_shadow_of_the_momentum_sphere_…/…_jp.tex）の
  第3節：半径 √n の n 次元の球の上の一様な点の一つの成分の濃さ（影）は
    f_n(x) ∝ (1 − x²/n)^((n−3)/2)、|x| ≤ √n。
  第4節：影の二乗平均は 1、尖り（四乗平均 ÷ 二乗平均の二乗）はちょうど 3n/(n+2)
    （「記号の計算」と書き、9 つの n で求積と 10⁻¹⁵ の内で一致したとする）。
    正規分布との全変動距離の n 倍が E|He₄(Z)|/8 = 0.350075 に近づく（n = 3000 までの数値）。

ここで証明した言明（n ≥ 3 の自然数）：
  (1) 濃さ (1 − x²/n)^((n−3)/2) の [−√n, √n] での二乗平均はちょうど 1、四乗平均は 3n/(n+2)、
      尖りは 3n/(n+2)（すべての n ≥ 3）。
      x = √n cos θ と置き換えて、Mathlib の sin の冪の積分の漸化式から示した。
  (2) n = 3 では濃さは平ら（定数 1）。
足した仮定：影の濃さの形 (1 − x²/n)^((n−3)/2) は原稿の式を入力として置いた（球の上の一様な測度から
この形が出ること＝ポアンカレ＝ボレルの補題の側は形式化していない）。

形式化していないもの（止めた所）：全変動距離の 1/n の係数 E|He₄(Z)|/8 の極限。原稿も証明を書かず
n = 3000 までの数値で確かめている。比の 1/n 展開を全変動距離へ持ち込む所（裾での一様な収束と誤差の評価）
を書くには、正規分布の積分と極限の交換の道具を大きく組む必要があり、今回は扱わない。
位置の濃さ (E − V)^((n−2)/2)、囲いが閉じる条件、4π の読み、分離子も扱っていない。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1117

open Real intervalIntegral

/-- I_m = ∫₀^π sin^m θ dθ。 -/
noncomputable def I (m : ℕ) : ℝ := ∫ x in (0 : ℝ)..π, sin x ^ m

theorem I_pos (m : ℕ) : 0 < I m := integral_sin_pow_pos m

theorem I_rec (m : ℕ) : I (m + 2) = ((m : ℝ) + 1) / ((m : ℝ) + 2) * I m := by
  unfold I
  rw [integral_sin_pow]
  simp

/-- ∫₀^π cos²θ sin^m θ dθ = I_m/(m+2)。 -/
theorem J1 (m : ℕ) : ∫ x in (0 : ℝ)..π, cos x ^ 2 * sin x ^ m = I m / ((m : ℝ) + 2) := by
  have e : (fun x => cos x ^ 2 * sin x ^ m) = fun x => sin x ^ m - sin x ^ (m + 2) := by
    ext x; rw [cos_sq', pow_add]; ring
  rw [e, integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  change I m - I (m + 2) = _
  rw [I_rec]
  have : (m : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- ∫₀^π cos⁴θ sin^m θ dθ = 3 I_m/((m+2)(m+4))。 -/
theorem J2 (m : ℕ) :
    ∫ x in (0 : ℝ)..π, cos x ^ 4 * sin x ^ m = 3 * I m / (((m : ℝ) + 2) * ((m : ℝ) + 4)) := by
  have e : (fun x => cos x ^ 4 * sin x ^ m) =
      fun x => (sin x ^ m - 2 * sin x ^ (m + 2)) + sin x ^ (m + 4) := by
    ext x
    have : cos x ^ 4 = (1 - sin x ^ 2) ^ 2 := by rw [← cos_sq']; ring
    rw [this]; ring
  rw [e, integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul]
  change I m - 2 * I (m + 2) + I (m + 2 + 2) = _
  rw [I_rec (m + 2), I_rec m]
  have h2 : (m : ℝ) + 2 ≠ 0 := by positivity
  have h4 : (m : ℝ) + 4 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- 影の濃さ (1 − x²/n)^((n−3)/2)。 -/
noncomputable def shadow (n : ℕ) (x : ℝ) : ℝ := (1 - x ^ 2 / n) ^ (((n : ℝ) - 3) / 2)

/-- 置き換え x = √n cos θ：
∫_{−√n}^{√n} x^(2j) (1 − x²/n)^((n−3)/2) dx = n^j √n ∫₀^π cos^(2j)θ sin^(n−2)θ dθ。 -/
theorem moment_subst (n j : ℕ) (hn : 3 ≤ n) :
    ∫ x in -√(n : ℝ)..√(n : ℝ), x ^ (2 * j) * shadow n x =
      (n : ℝ) ^ j * √(n : ℝ) * ∫ θ in (0 : ℝ)..π, cos θ ^ (2 * j) * sin θ ^ (n - 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hexp : (0 : ℝ) ≤ ((n : ℝ) - 3) / 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set g : ℝ → ℝ := fun x => x ^ (2 * j) * shadow n x
  have hg : Continuous g := by
    unfold g shadow
    exact (continuous_pow _).mul ((Real.continuous_rpow_const hexp).comp (by fun_prop))
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := π)
    (f := fun θ => √(n : ℝ) * cos θ) (f' := fun θ => -(√(n : ℝ) * sin θ)) (g := g)
    (fun x _ => by simpa using (hasDerivAt_cos x).const_mul (√(n : ℝ))) (by fun_prop) hg
  simp only [Function.comp, cos_zero, cos_pi, mul_one, mul_neg] at hsub
  rw [intervalIntegral.integral_symm, ← hsub, ← intervalIntegral.integral_neg,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [Set.uIcc_of_le pi_pos.le] at hθ
  have hs : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  simp only [g, shadow]
  have h1 : 1 - (√(n : ℝ) * cos θ) ^ 2 / n = sin θ ^ 2 := by
    rw [mul_pow, hsq]; field_simp; rw [← sin_sq_add_cos_sq θ]; ring
  rw [h1]
  have h2 : (sin θ ^ 2) ^ (((n : ℝ) - 3) / 2) = sin θ ^ (n - 3) := by
    rw [← Real.rpow_natCast (sin θ) 2, ← Real.rpow_mul hs]
    rw [show ((2 : ℕ) : ℝ) * (((n : ℝ) - 3) / 2) = ((n - 3 : ℕ) : ℝ) by
      rw [Nat.cast_sub hn]; push_cast; ring, Real.rpow_natCast]
  rw [h2]
  have h3 : sin θ ^ (n - 2) = sin θ ^ (n - 3) * sin θ := by
    rw [← pow_succ]; congr 1; omega
  rw [h3, mul_pow, pow_mul, pow_mul, hsq]
  ring

/-- (1) 二乗平均は 1、四乗平均は 3n/(n+2)（すべての n ≥ 3）。 -/
theorem shadow_moments (n : ℕ) (hn : 3 ≤ n) :
    (∫ x in -√(n : ℝ)..√(n : ℝ), x ^ 2 * shadow n x) /
        (∫ x in -√(n : ℝ)..√(n : ℝ), shadow n x) = 1 ∧
    (∫ x in -√(n : ℝ)..√(n : ℝ), x ^ 4 * shadow n x) /
        (∫ x in -√(n : ℝ)..√(n : ℝ), shadow n x) = 3 * n / (n + 2) := by
  have h0 := moment_subst n 0 hn
  have h1 := moment_subst n 1 hn
  have h2 := moment_subst n 2 hn
  simp only [mul_zero, pow_zero, one_mul] at h0
  simp only [mul_one, pow_one] at h1
  rw [show 2 * 2 = 4 from rfl] at h2
  rw [show (∫ θ in (0 : ℝ)..π, sin θ ^ (n - 2)) = I (n - 2) from rfl] at h0
  rw [J1] at h1
  rw [J2] at h2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hI := I_pos (n - 2)
  have hcast : ((n - 2 : ℕ) : ℝ) = n - 2 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hn' : (n : ℝ) ≠ 0 := hn0.ne'
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · rw [h1, h0, hcast, show (n : ℝ) - 2 + 2 = n by ring]
    field_simp
  · rw [h2, h0, hcast, show (n : ℝ) - 2 + 2 = n by ring, show (n : ℝ) - 2 + 4 = n + 2 by ring]
    field_simp

/-- (1) 尖り（四乗平均 ÷ 二乗平均の二乗）は 3n/(n+2)。n が増えると 3（正規分布の尖り）に近づく。 -/
theorem shadow_kurtosis (n : ℕ) (hn : 3 ≤ n) :
    let N0 := ∫ x in -√(n : ℝ)..√(n : ℝ), shadow n x
    let N2 := ∫ x in -√(n : ℝ)..√(n : ℝ), x ^ 2 * shadow n x
    let N4 := ∫ x in -√(n : ℝ)..√(n : ℝ), x ^ 4 * shadow n x
    (N4 / N0) / (N2 / N0) ^ 2 = 3 * n / (n + 2) := by
  intro N0 N2 N4
  obtain ⟨h2, h4⟩ := shadow_moments n hn
  simp only [N0, N2, N4]
  rw [h2, h4]; ring

/-- (2) n = 3 では影は平ら（アルキメデスの帯）。 -/
theorem shadow_three_flat (x : ℝ) : shadow 3 x = 1 := by
  simp [shadow]

end Paper1117

end Yamagishi
