/-
論文1111『逆二乗は中を隠し、こだまを歪めずに運ぶ』の中の、切り出せば一般の定理になる二つの部分を、
機械に確かめさせる（格上げ）。芯の「崖となだらか」（特異値の数え上げ）は数値の結果なので扱わない。

原稿（1111_yamagishi_inverse_square_hides_the_interior_and_carries_the_echo_undistorted/…_jp.tex）の
  第6節：木村らの式 (2-5) [¼Δ₅² − (ik)²∂ₓ² − (∂_{y₁}²+∂_{z₁}²)(∂_{y₂}²+∂_{z₂}²)] G = 0 は、
    一回の跳ね返りの核で近似なしに成り立つ。理由：x を x₁, x₂ に分け、往き A が
    (∂_{x₁}² + ∂_{y₁}² + ∂_{z₁}² + k²)A = 0、帰り B も同じ形を満たすので、
    ∂_{y₁}²+∂_{z₁}² を −(k² + ∂_{x₁}²) に置き換えると
    (∂_{x₁}∂_{x₂} − k²)² + k²(∂_{x₁}+∂_{x₂})² − (k²+∂_{x₁}²)(k²+∂_{x₂}²) = 0 で恒等的に消える。
    （40 桁の数値でも確かめている。）
  第8節：u = r^(−(d−1)/2) f(t − r) を波の式に入れると
    u_rr + (d−1)/r u_r − u_tt = (d−1)(3−d)/4 · r^(−(d+3)/2) f(t − r)、0 になるのは d = 1 と 3 だけ。
    一般の g(r) f(t − r) では、f' の係数 2g' + (d−1)g/r と f の係数 g'' + (d−1)g'/r が両方 0 でなければならない。

ここで証明した言明：
  (A) 作用素の記号（定数係数の微分作用素を、∂ を文字に置き換えた多項式）の恒等式：
      X₁ = ∂_{x₁}、X₂ = ∂_{x₂}、T₁ = ∂_{y₁}²+∂_{z₁}²、T₂ = ∂_{y₂}²+∂_{z₂}²、i² = −1 として、
      4·[(2-5) の作用素] = a(a − 2b + 4X₁X₂ + 4X₂²) + b(b + 4X₁X₂ + 4X₁²)、
      a = T₁ + k² + X₁²（往きのヘルムホルツの作用素）、b = T₂ + k² + X₂²（帰り）。
      つまり (2-5) の作用素は、往きと帰りの二つの作用素の「倍数の和」にちょうど書ける。
      原稿の一行の恒等式も別に示した。平面波（分散の関係を満たす波数）での記号が 0 になることも示した。
  (B) 一般の g(r) f(t − r) について、波の式の残りが (g'' + (d−1)g'/r) f − (2g' + (d−1)g/r) f' であること。
      g = r^(−(d−1)/2) で残りが (d−1)(3−d)/4 · r^(−(d+3)/2) f(t − r) であること（d は任意の実数、r > 0）。
      すべての f で残りが 0 ⇔ d = 1 または d = 3。
      さらに、二つの係数が r > 0 で 0 になる g は C r^(−(d−1)/2) の形しかなく、C ≠ 0 なら d = 1 か 3。
足した仮定・形式化の線：(A) は記号の多項式の恒等式として示した。そこから「核に作用素を当てると 0」へ進む
一歩（定数係数の微分作用素は互いに交換し、記号の多項式の積・和がそのまま作用素の積・和になること、
x₁ = x₂ = x と置くと ∂ₓ が ∂_{x₁} + ∂_{x₂} になること）は、Mathlib に定数係数の微分作用素の代数が
まだ無いので形式化していない。D₁ = 0・D₂ = 0 の点を除く、という原稿の断りもこの外にある。
(B) の f は何度でも微分できる一変数の関数で、導関数を f'・f'' と名付けて仮定に置いた。

形式化していないもの：特異値の数え上げ（崖となだらか）、多周波数の一意性、こだまの強さ (4π)²D₁D₂、
ホイヘンスの原理との関係、5 次元の相関 0.688416 などの数値、近似が働く深さそろえの段 (2-12)〜(2-14)。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1111

open Real

/-! ### (A) 木村らの式 (2-5) の記号の恒等式 -/

/-- (A) 原稿の一行の恒等式：(X₁X₂ − k²)² + k²(X₁+X₂)² − (k²+X₁²)(k²+X₂²) = 0（可換環で）。 -/
theorem paper_identity {R : Type*} [CommRing R] (k X1 X2 : R) :
    (X1 * X2 - k ^ 2) ^ 2 + k ^ 2 * (X1 + X2) ^ 2 - (k ^ 2 + X1 ^ 2) * (k ^ 2 + X2 ^ 2) = 0 := by
  ring

/-- (A) (2-5) の作用素の 4 倍は、往き a = T₁ + k² + X₁² と帰り b = T₂ + k² + X₂² の倍数の和。
Δ₅ の記号は (X₁ + X₂)² + T₁ + T₂（x を共有するので ∂ₓ = ∂_{x₁} + ∂_{x₂}）。 -/
theorem kimura_operator_in_ideal {R : Type*} [CommRing R] (i k X1 X2 T1 T2 : R) (hi : i ^ 2 = -1) :
    ((X1 + X2) ^ 2 + T1 + T2) ^ 2 - 4 * (i * k) ^ 2 * (X1 + X2) ^ 2 - 4 * (T1 * T2) =
      (T1 + k ^ 2 + X1 ^ 2) *
        ((T1 + k ^ 2 + X1 ^ 2) - 2 * (T2 + k ^ 2 + X2 ^ 2) + 4 * X1 * X2 + 4 * X2 ^ 2) +
      (T2 + k ^ 2 + X2 ^ 2) * ((T2 + k ^ 2 + X2 ^ 2) + 4 * X1 * X2 + 4 * X1 ^ 2) := by
  linear_combination (-4 * k ^ 2 * (X1 + X2) ^ 2) * hi

/-- (A) 平面波での確かめ：往きの波数 (α₁, β₁, γ₁)、帰りの (α₂, β₂, γ₂) がどちらも α² + β² + γ² = k² を
満たせば、(2-5) の記号は 0（∂ を i·波数 に置き換えたもの）。 -/
theorem kimura_plane_waves (k α1 β1 γ1 α2 β2 γ2 : ℝ)
    (h1 : α1 ^ 2 + β1 ^ 2 + γ1 ^ 2 = k ^ 2) (h2 : α2 ^ 2 + β2 ^ 2 + γ2 ^ 2 = k ^ 2) :
    let Δ5 : ℂ := -(((α1 + α2) ^ 2 + β1 ^ 2 + γ1 ^ 2 + β2 ^ 2 + γ2 ^ 2 : ℝ) : ℂ)
    let dx2 : ℂ := -(((α1 + α2) ^ 2 : ℝ) : ℂ)
    let T1 : ℂ := -((β1 ^ 2 + γ1 ^ 2 : ℝ) : ℂ)
    let T2 : ℂ := -((β2 ^ 2 + γ2 ^ 2 : ℝ) : ℂ)
    (1 / 4) * Δ5 ^ 2 - (Complex.I * k) ^ 2 * dx2 - T1 * T2 = 0 := by
  intro Δ5 dx2 T1 T2
  have hb1 : β1 ^ 2 + γ1 ^ 2 = k ^ 2 - α1 ^ 2 := by linarith
  have hb2 : β2 ^ 2 + γ2 ^ 2 = k ^ 2 - α2 ^ 2 := by linarith
  have e5 : ((α1 + α2) ^ 2 + β1 ^ 2 + γ1 ^ 2 + β2 ^ 2 + γ2 ^ 2 : ℝ) = 2 * (α1 * α2 + k ^ 2) := by
    nlinarith [hb1, hb2]
  simp only [Δ5, dx2, T1, T2]
  rw [e5, hb1, hb2]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### (B) 形を保つ球面波 -/

/-- (B) 一般の g(r) f(t − r) の微分（r についての一回・二回、t についての二回）。 -/
theorem wave_derivs (t r : ℝ) (g g1 g2 f f1 f2 : ℝ → ℝ)
    (hg : ∀ s, 0 < s → HasDerivAt g (g1 s) s) (hg1 : HasDerivAt g1 (g2 r) r) (hr : 0 < r)
    (hf : ∀ s, HasDerivAt f (f1 s) s) (hf1 : ∀ s, HasDerivAt f1 (f2 s) s) :
    HasDerivAt (fun r => g r * f (t - r)) (g1 r * f (t - r) - g r * f1 (t - r)) r ∧
    HasDerivAt (fun r => g1 r * f (t - r) - g r * f1 (t - r))
      (g2 r * f (t - r) - 2 * g1 r * f1 (t - r) + g r * f2 (t - r)) r ∧
    HasDerivAt (fun t => g r * f (t - r)) (g r * f1 (t - r)) t ∧
    HasDerivAt (fun t => g r * f1 (t - r)) (g r * f2 (t - r)) t := by
  have hs : HasDerivAt (fun r : ℝ => t - r) (-1) r := by
    simpa using (hasDerivAt_id' r).const_sub t
  have ht : HasDerivAt (fun t : ℝ => t - r) 1 t := by
    simpa using (hasDerivAt_id' t).sub_const r
  have hfr := (hf (t - r)).comp r hs
  have hf1r := (hf1 (t - r)).comp r hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (hg r hr).mul hfr
    convert this using 1
    · ext y; simp only [Pi.mul_apply, Function.comp_apply]
    · simp only [Function.comp_apply]; ring
  · have := (hg1.mul hfr).sub ((hg r hr).mul hf1r)
    convert this using 1
    · ext y; simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
    · simp only [Function.comp_apply]; ring
  · have := ((hf (t - r)).comp t ht).const_mul (g r)
    convert this using 1 <;> simp
  · have := ((hf1 (t - r)).comp t ht).const_mul (g r)
    convert this using 1 <;> simp

/-- (B) 波の式の残り u_rr + (d−1)/r u_r − u_tt は (g'' + (d−1)g'/r) f − (2g' + (d−1)g/r) f'。 -/
theorem wave_residual (d r : ℝ) (G G1 G2 F F1 F2 : ℝ) :
    (G2 * F - 2 * G1 * F1 + G * F2) + (d - 1) / r * (G1 * F - G * F1) - G * F2 =
      (G2 + (d - 1) / r * G1) * F - (2 * G1 + (d - 1) / r * G) * F1 := by
  ring

/-- (B) g = r^a（a = −(d−1)/2）では、f' の係数 2g' + (d−1)g/r が 0、f の係数 g'' + (d−1)g'/r が
(d−1)(3−d)/4 · r^(−(d+3)/2)。ここで g' = a r^(a−1)、g'' = a(a−1) r^(a−2)。 -/
theorem power_coefficients (d r : ℝ) (hr : 0 < r) :
    let a := -(d - 1) / 2
    2 * (a * r ^ (a - 1)) + (d - 1) / r * r ^ a = 0 ∧
    a * (a - 1) * r ^ (a - 2) + (d - 1) / r * (a * r ^ (a - 1)) =
      (d - 1) * (3 - d) / 4 * r ^ (-(d + 3) / 2) := by
  intro a
  have e1 : r ^ (a - 1) = r ^ a / r := by rw [rpow_sub hr, rpow_one]
  have e2 : r ^ (a - 2) = r ^ (a - 1) / r := by
    rw [show a - 2 = (a - 1) - 1 by ring, rpow_sub hr, rpow_one]
  have e3 : (-(d + 3) / 2) = a - 2 := by simp only [a]; ring
  constructor
  · rw [e1]; simp only [a]; field_simp; ring
  · rw [e3, e2]; simp only [a]; field_simp; ring

/-- (B) g = r^(−(d−1)/2) は r > 0 で微分を持つ（g' = a r^(a−1)、g'' = a(a−1) r^(a−2)）。 -/
theorem power_derivs (d s : ℝ) (hs : 0 < s) :
    let a := -(d - 1) / 2
    HasDerivAt (fun r : ℝ => r ^ a) (a * s ^ (a - 1)) s ∧
    HasDerivAt (fun r : ℝ => a * r ^ (a - 1)) (a * (a - 1) * s ^ (a - 2)) s := by
  intro a
  refine ⟨hasDerivAt_rpow_const (Or.inl hs.ne'), ?_⟩
  have := (hasDerivAt_rpow_const (p := a - 1) (Or.inl hs.ne')).const_mul a
  convert this using 1
  rw [show a - 1 - 1 = a - 2 by ring]; ring

/-- (B) 弱まりながら形を保つ球面波 u = r^(−(d−1)/2) f(t − r) が、すべての f で波の式を満たす ⇔ d = 1 または 3。
（すべての f、すべての r > 0、t で残りが 0 になること。f ≡ 1 で確かめれば十分。） -/
theorem shape_preserving_iff (d : ℝ) :
    (∀ r : ℝ, 0 < r → ∀ F F1 : ℝ,
      (-(d - 1) / 2 * (-(d - 1) / 2 - 1) * r ^ (-(d - 1) / 2 - 2) +
          (d - 1) / r * (-(d - 1) / 2 * r ^ (-(d - 1) / 2 - 1))) * F -
        (2 * (-(d - 1) / 2 * r ^ (-(d - 1) / 2 - 1)) + (d - 1) / r * r ^ (-(d - 1) / 2)) * F1 = 0) ↔
      d = 1 ∨ d = 3 := by
  constructor
  · intro h
    have h1 := h 1 one_pos 1 0
    obtain ⟨c1, c2⟩ := power_coefficients d 1 one_pos
    rw [c2] at h1
    simp only [one_rpow, mul_one, mul_zero, sub_zero] at h1
    have : (d - 1) * (3 - d) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · left; linarith
    · right; linarith
  · intro hd r hr F F1
    obtain ⟨c1, c2⟩ := power_coefficients d r hr
    rw [c1, c2]
    rcases hd with rfl | rfl <;> ring

/-- (B) 逆に、f' の係数が r > 0 で 0 になる g は C r^(−(d−1)/2) の形だけ。 -/
theorem flux_preserving_form (d : ℝ) (g g1 : ℝ → ℝ) (hg : ∀ s, 0 < s → HasDerivAt g (g1 s) s)
    (h : ∀ s, 0 < s → 2 * g1 s + (d - 1) / s * g s = 0) :
    ∀ r, 0 < r → g r = g 1 * r ^ (-(d - 1) / 2) := by
  set b := (d - 1) / 2
  have hφ : ∀ s, 0 < s → HasDerivAt (fun s => g s * s ^ b) 0 s := by
    intro s hs
    have h2 := (hg s hs).mul (hasDerivAt_rpow_const (p := b) (Or.inl hs.ne'))
    convert h2 using 1
    have e : s ^ (b - 1) = s ^ b / s := by rw [rpow_sub hs, rpow_one]
    rw [e]
    have := h s hs
    have hs' : s ≠ 0 := hs.ne'
    field_simp
    field_simp at this
    simp only [b]
    linear_combination (-(s ^ ((d - 1) / 2)) / 2) * this
  -- 一定であること
  have hconst : ∀ r, 0 < r → g r * r ^ b = g 1 * 1 ^ b := by
    intro r hr
    have key : ∀ x y, 0 < x → x ≤ y → g y * y ^ b = g x * x ^ b := by
      intro x y hx hxy
      have hcont : ContinuousOn (fun s => g s * s ^ b) (Set.Icc x y) := fun t ht =>
        (hφ t (by linarith [ht.1])).continuousAt.continuousWithinAt
      exact constant_of_has_deriv_right_zero hcont
        (fun t ht => (hφ t (by linarith [ht.1])).hasDerivWithinAt) y ⟨hxy, le_rfl⟩
    rcases le_total 1 r with h1 | h1
    · exact key 1 r one_pos h1
    · exact (key r 1 hr h1).symm
  intro r hr
  have := hconst r hr
  rw [one_rpow, mul_one] at this
  have hpos : 0 < r ^ b := rpow_pos_of_pos hr b
  have e : r ^ (-(d - 1) / 2) = (r ^ b)⁻¹ := by
    rw [show -(d - 1) / 2 = -b by simp only [b]; ring, rpow_neg hr.le]
  rw [e]
  field_simp
  linarith

end Paper1111

end Yamagishi
