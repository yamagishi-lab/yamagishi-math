/-
論文1110『四面体の角は数え方で、力の法則では動かない』の、対称に釣り合う二つずつの形の曲線
（原稿のとおり）。

日本語の一文：単位球面に電荷 1 の二点と電荷 q の二点を直交する面に向かい合わせた形で、エネルギー
Σ qᵢqⱼ|xᵢ − xⱼ|^(−s) が停留するなら、s と q によらず、同じ電荷どうしの距離の積は違う電荷の間の
距離の二乗に等しい。
English: On the unit sphere, put two charges 1 at (±sin α, 0, cos α) and two charges q at
(0, ±sin β, −cos β); if the energy Σ qᵢqⱼ|xᵢ − xⱼ|^(−s) is stationary in α and β, then for every
power s ∉ {0, −2} and every q > 0, d_BB·d_LL = d_BL², i.e.
2 sin(θ/2) sin(φ/2) = 1 + cos(θ/2)cos(φ/2).

原稿（1110_yamagishi_tetrahedral_angle_is_counting_and_does_not_move_with_the_force_law/…_jp.tex）は、
電荷 1 の点と電荷 q の点の接線方向の釣り合いの式を掛けて電荷を消し、冪の力なら d_BB·d_LL = d_BL² に
なることを本文で導き、s = 1・2・6・12 と q の 16 通りの最小化で確かめている。

ここで証明した言明（α = θ/2、β = φ/2 は (0, π/2) の中、q > 0）：
  (1) `dist_BB`・`dist_LL`・`dist_BL`：上の座標で d_BB = 2 sin α、d_LL = 2 sin β、
      d_BL² = 2 + 2 cos α cos β（四本とも等しい）。
  (2) `hasDerivAt_E_α`・`hasDerivAt_E_β`：対称な形のエネルギー
      E(α, β) = (2 sin α)^(−s) + q²(2 sin β)^(−s) + 4q(2 + 2 cos α cos β)^(−s/2) の α と β での微分。
  (3) `balance_B`・`balance_L`：E が α で停留 ⇔ 電荷 1 の点の釣り合い cos α·d_BB^p = q cos β·d_BL^p、
      β で停留 ⇔ 電荷 q の点の釣り合い q cos β·d_LL^p = cos α·d_BL^p（p = −s − 2）。
  (4) `stationary_curve`：s ≠ 0、s ≠ −2 で E が α と β の両方で停留するなら、d_BB·d_LL = d_BL²。
      `stationary_curve_angles`：同じことを角で書くと 2 sin(θ/2) sin(φ/2) = 1 + cos(θ/2) cos(φ/2)。
  (5) `tetrahedral_on_curve`：cos²(θ/2) = cos²(φ/2) = 1/3（正四面体、cos θ = −1/3）は曲線の上にある。
足した条件：s ≠ 0。s = 0 ではエネルギーが定数（1 + q² + 4q）で、どの形も停留点になり、曲線の式は
成り立たない（原稿の g(r) = s r^(−s−2) が 0 になる場合）。s = −2 では二つの釣り合いの式が同じ一本
cos α = q cos β になり、曲線は決まらない。停留は対称な形の二つの角についての停留として扱った
（全体の停留点ならこれをみたすので、仮定は弱い側にある）。
形式化していないもの：最小の形がいつもこの対称な形になること、水やアンモニアの角の数値、
正単体・交差多面体の二面角、混ぜた部屋の重み、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1110

open Real

/-! ### 座標と距離 -/

/-- 三次元の点の距離の二乗。 -/
def dist2 (x y : ℝ × ℝ × ℝ) : ℝ :=
  (x.1 - y.1) ^ 2 + (x.2.1 - y.2.1) ^ 2 + (x.2.2 - y.2.2) ^ 2

/-- 電荷 1 の二点 (±sin α, 0, cos α)。 -/
noncomputable def B (σ α : ℝ) : ℝ × ℝ × ℝ := (σ * sin α, 0, cos α)
/-- 電荷 q の二点 (0, ±sin β, −cos β)。 -/
noncomputable def L (σ β : ℝ) : ℝ × ℝ × ℝ := (0, σ * sin β, -cos β)

theorem dist_BB (α : ℝ) : dist2 (B 1 α) (B (-1) α) = (2 * sin α) ^ 2 := by
  unfold dist2 B; ring

theorem dist_LL (β : ℝ) : dist2 (L 1 β) (L (-1) β) = (2 * sin β) ^ 2 := by
  unfold dist2 L; ring

/-- 違う電荷の間の距離の二乗は、四本とも 2 + 2 cos α cos β。 -/
theorem dist_BL (α β σ τ : ℝ) (hσ : σ ^ 2 = 1) (hτ : τ ^ 2 = 1) :
    dist2 (B σ α) (L τ β) = 2 + 2 * cos α * cos β := by
  unfold dist2 B L
  simp only
  have h1 := sin_sq_add_cos_sq α
  have h2 := sin_sq_add_cos_sq β
  linear_combination sin α ^ 2 * hσ + h1 + sin β ^ 2 * hτ + h2

/-! ### 対称な形のエネルギー -/

/-- 違う電荷の間の距離の二乗 D = 2 + 2 cos α cos β。 -/
noncomputable def D (α β : ℝ) : ℝ := 2 + 2 * cos α * cos β

/-- 対称な形のエネルギー (2 sin α)^(−s) + q²(2 sin β)^(−s) + 4q D^(−s/2)。 -/
noncomputable def E (s q α β : ℝ) : ℝ :=
  (2 * sin α) ^ (-s) + q ^ 2 * (2 * sin β) ^ (-s) + 4 * q * D α β ^ (-s / 2)

theorem D_pos {α β : ℝ} (hα : 0 < α) (hα' : α < π / 2) (hβ : 0 < β) (hβ' : β < π / 2) :
    0 < D α β := by
  unfold D
  have := cos_pos_of_mem_Ioo ⟨by linarith, hα'⟩
  have := cos_pos_of_mem_Ioo ⟨by linarith, hβ'⟩
  positivity

theorem sin_pos_half {α : ℝ} (hα : 0 < α) (hα' : α < π / 2) : 0 < sin α :=
  sin_pos_of_pos_of_lt_pi hα (by linarith [pi_pos])

theorem cos_pos_half {α : ℝ} (hα : 0 < α) (hα' : α < π / 2) : 0 < cos α :=
  cos_pos_of_mem_Ioo ⟨by linarith, hα'⟩

/-- (2) α での微分。 -/
theorem hasDerivAt_E_α (s q : ℝ) {α β : ℝ} (hα : 0 < α) (hα' : α < π / 2) (hβ : 0 < β)
    (hβ' : β < π / 2) :
    HasDerivAt (fun x => E s q x β)
      (2 * cos α * (-s) * (2 * sin α) ^ (-s - 1) +
        4 * q * ((-(2 * sin α * cos β)) * (-s / 2) * D α β ^ (-s / 2 - 1))) α := by
  have hs : 0 < 2 * sin α := by have := sin_pos_half hα hα'; linarith
  have h1 : HasDerivAt (fun x => 2 * sin x) (2 * cos α) α := (hasDerivAt_sin α).const_mul 2
  have h1' := h1.rpow_const (p := -s) (Or.inl (ne_of_gt hs))
  have h2 : HasDerivAt (fun x => D x β) (-(2 * sin α * cos β)) α := by
    have := (((hasDerivAt_cos α).const_mul 2).mul_const (cos β)).const_add 2
    unfold D
    convert this using 1; ring
  have h2' := (h2.rpow_const (p := -s / 2) (Or.inl (ne_of_gt (D_pos hα hα' hβ hβ')))).const_mul
    (4 * q)
  have := (h1'.add_const (q ^ 2 * (2 * sin β) ^ (-s))).add h2'
  unfold E
  convert this using 1

/-- (2) β での微分。 -/
theorem hasDerivAt_E_β (s q : ℝ) {α β : ℝ} (hα : 0 < α) (hα' : α < π / 2) (hβ : 0 < β)
    (hβ' : β < π / 2) :
    HasDerivAt (fun y => E s q α y)
      (q ^ 2 * (2 * cos β * (-s) * (2 * sin β) ^ (-s - 1)) +
        4 * q * ((-(2 * cos α * sin β)) * (-s / 2) * D α β ^ (-s / 2 - 1))) β := by
  have hs : 0 < 2 * sin β := by have := sin_pos_half hβ hβ'; linarith
  have h1 : HasDerivAt (fun y => 2 * sin y) (2 * cos β) β := (hasDerivAt_sin β).const_mul 2
  have h1' := (h1.rpow_const (p := -s) (Or.inl (ne_of_gt hs))).const_mul (q ^ 2)
  have h2 : HasDerivAt (fun y => D α y) (-(2 * cos α * sin β)) β := by
    have := ((hasDerivAt_cos β).const_mul (2 * cos α)).const_add 2
    unfold D
    convert this using 1
    ring
  have h2' := (h2.rpow_const (p := -s / 2) (Or.inl (ne_of_gt (D_pos hα hα' hβ hβ')))).const_mul
    (4 * q)
  have := (h1'.const_add ((2 * sin α) ^ (-s))).add h2'
  unfold E
  convert this using 1

/-- 指数のつなぎ：X^(−s−1) = X^p·X、D^(−s/2−1) = D^(p/2)（p = −s − 2）。 -/
theorem rpow_shift {X s : ℝ} (hX : 0 < X) : X ^ (-s - 1) = X ^ (-s - 2) * X := by
  rw [show -s - 1 = (-s - 2) + 1 by ring, rpow_add_one (ne_of_gt hX)]

/-- (3) α での停留 ⇔ 電荷 1 の点の釣り合い。 -/
theorem balance_B {s q α β : ℝ} (hs0 : s ≠ 0) (hα : 0 < α) (hα' : α < π / 2) (hβ : 0 < β)
    (hβ' : β < π / 2) :
    HasDerivAt (fun x => E s q x β) 0 α ↔
      cos α * (2 * sin α) ^ (-s - 2) = q * cos β * D α β ^ ((-s - 2) / 2) := by
  have hd := hasDerivAt_E_α s q hα hα' hβ hβ'
  have hsin := sin_pos_half hα hα'
  have hX : 0 < 2 * sin α := by linarith
  have key : 2 * cos α * (-s) * (2 * sin α) ^ (-s - 1) +
      4 * q * ((-(2 * sin α * cos β)) * (-s / 2) * D α β ^ (-s / 2 - 1)) =
      4 * s * sin α * (q * cos β * D α β ^ ((-s - 2) / 2) - cos α * (2 * sin α) ^ (-s - 2)) := by
    rw [rpow_shift hX, show -s / 2 - 1 = (-s - 2) / 2 by ring]
    ring
  constructor
  · intro h
    have h0 := hd.unique h
    rw [key] at h0
    have hne : 4 * s * sin α ≠ 0 := by
      have : 0 < sin α := hsin
      positivity
    have := (mul_eq_zero.mp h0).resolve_left hne
    linarith
  · intro h
    have : 4 * s * sin α * (q * cos β * D α β ^ ((-s - 2) / 2) -
        cos α * (2 * sin α) ^ (-s - 2)) = 0 := by rw [h]; ring
    rw [← key] at this
    rwa [this] at hd

/-- (3) β での停留 ⇔ 電荷 q の点の釣り合い。 -/
theorem balance_L {s q α β : ℝ} (hs0 : s ≠ 0) (hq : 0 < q) (hα : 0 < α) (hα' : α < π / 2)
    (hβ : 0 < β) (hβ' : β < π / 2) :
    HasDerivAt (fun y => E s q α y) 0 β ↔
      q * cos β * (2 * sin β) ^ (-s - 2) = cos α * D α β ^ ((-s - 2) / 2) := by
  have hd := hasDerivAt_E_β s q hα hα' hβ hβ'
  have hsin := sin_pos_half hβ hβ'
  have hY : 0 < 2 * sin β := by linarith
  have key : q ^ 2 * (2 * cos β * (-s) * (2 * sin β) ^ (-s - 1)) +
      4 * q * ((-(2 * cos α * sin β)) * (-s / 2) * D α β ^ (-s / 2 - 1)) =
      4 * q * s * sin β *
        (cos α * D α β ^ ((-s - 2) / 2) - q * cos β * (2 * sin β) ^ (-s - 2)) := by
    rw [rpow_shift hY, show -s / 2 - 1 = (-s - 2) / 2 by ring]
    ring
  constructor
  · intro h
    have h0 := hd.unique h
    rw [key] at h0
    have hne : 4 * q * s * sin β ≠ 0 := by
      have : 0 < sin β := hsin
      have : q ≠ 0 := ne_of_gt hq
      positivity
    have := (mul_eq_zero.mp h0).resolve_left hne
    linarith
  · intro h
    have : 4 * q * s * sin β * (cos α * D α β ^ ((-s - 2) / 2) -
        q * cos β * (2 * sin β) ^ (-s - 2)) = 0 := by rw [h]; ring
    rw [← key] at this
    rwa [this] at hd

/-- (4) 停留点なら d_BB·d_LL = d_BL²（s ≠ 0、s ≠ −2、q > 0）。 -/
theorem stationary_curve {s q α β : ℝ} (hs0 : s ≠ 0) (hs2 : s ≠ -2) (hq : 0 < q)
    (hα : 0 < α) (hα' : α < π / 2) (hβ : 0 < β) (hβ' : β < π / 2)
    (h1 : HasDerivAt (fun x => E s q x β) 0 α) (h2 : HasDerivAt (fun y => E s q α y) 0 β) :
    (2 * sin α) * (2 * sin β) = D α β := by
  have e1 := (balance_B hs0 hα hα' hβ hβ').mp h1
  have e2 := (balance_L hs0 hq hα hα' hβ hβ').mp h2
  set p := -s - 2 with hp
  have hp0 : p ≠ 0 := by intro h; apply hs2; linarith
  have hX : 0 < 2 * sin α := by have := sin_pos_half hα hα'; linarith
  have hY : 0 < 2 * sin β := by have := sin_pos_half hβ hβ'; linarith
  have hDp := D_pos hα hα' hβ hβ'
  have hca := cos_pos_half hα hα'
  have hcb := cos_pos_half hβ hβ'
  -- 二つの釣り合いを掛けて電荷と余弦を消す
  have hmul : (q * cos α * cos β) * ((2 * sin α) ^ p * (2 * sin β) ^ p) =
      (q * cos α * cos β) * (D α β ^ (p / 2) * D α β ^ (p / 2)) := by
    have := congrArg₂ (· * ·) e1 e2
    linear_combination this
  have hk : q * cos α * cos β ≠ 0 := by positivity
  have h3 := mul_left_cancel₀ hk hmul
  rw [← mul_rpow hX.le hY.le, ← rpow_add hDp, add_halves] at h3
  -- 指数 p ≠ 0 の冪は正の数の上で一対一
  have := congrArg (fun z => z ^ (1 / p)) h3
  beta_reduce at this
  rwa [← rpow_mul (by positivity), ← rpow_mul hDp.le, mul_one_div_cancel hp0, rpow_one,
    rpow_one] at this

/-- (4) 角で書いた曲線：2 sin(θ/2) sin(φ/2) = 1 + cos(θ/2) cos(φ/2)。 -/
theorem stationary_curve_angles {s q θ φ : ℝ} (hs0 : s ≠ 0) (hs2 : s ≠ -2) (hq : 0 < q)
    (hθ : 0 < θ) (hθ' : θ < π) (hφ : 0 < φ) (hφ' : φ < π)
    (h1 : HasDerivAt (fun x => E s q x (φ / 2)) 0 (θ / 2))
    (h2 : HasDerivAt (fun y => E s q (θ / 2) y) 0 (φ / 2)) :
    2 * sin (θ / 2) * sin (φ / 2) = 1 + cos (θ / 2) * cos (φ / 2) := by
  have := stationary_curve hs0 hs2 hq (by linarith) (by linarith) (by linarith) (by linarith) h1 h2
  unfold D at this
  linarith

/-- s = 0 ではエネルギーは定数で、どの形も停留点になる（条件 s ≠ 0 が要る理由）。 -/
theorem E_zero_const (q α β : ℝ) : E 0 q α β = 1 + q ^ 2 + 4 * q := by
  unfold E; simp

/-- (5) 正四面体の点（cos²(θ/2) = 1/3）は曲線の上にあり、cos θ = −1/3。 -/
theorem tetrahedral_on_curve {α : ℝ} (h : cos α ^ 2 = 1 / 3) :
    2 * sin α * sin α = 1 + cos α * cos α ∧ cos (2 * α) = -1 / 3 := by
  constructor
  · have := sin_sq_add_cos_sq α
    nlinarith
  · rw [cos_two_mul, h]; norm_num

end Paper1110

end Yamagishi
