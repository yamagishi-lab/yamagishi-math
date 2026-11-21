/-
論文1040『動く光源の明るさに現れる 4 乗は、立体角の d−1 とエネルギーの 1 と間隔の 1 の和である』の格上げ（一般の形）。

原稿（1040_yamagishi_brightness_exponent_is_solid_angle_plus_energy_plus_spacing/…_jp.tex）は、
d = 2, 3, 4 と β = 0.5 で、立体角の比 dΩ/dΩ′ = 1/D^(d−1) を数値微分で確かめ、
全天平均 ⟨D^p⟩ を p = d − 2, d − 1, d, d + 1 で数値積分し（計算 2.3）、「p = d − 1 のときだけ 1」
と述べ、d = 3 だけで閉じた式 γ²(1 + β²/3) と照らしている。

定義に置いたもの（球面上の積分を一次元の積分に落とした形）：
  μ = cos θ と置くと、d 次元の空の上の向きの平均は、重み w(μ) = (1 − μ²)^((d−3)/2) を付けた
  (−1, 1) の上の積分になる（球面の測度を μ に押し出した形。ここは定義として置き、球面上の測度から
  この重みが出ることは形式化していない）。観測者の系のドップラー因子 D(μ) = 1/(γ(1 − βμ))、
  源の系の D′(μ′) = γ(1 + βμ′)、光行差の写像 μ = φ(μ′) = (μ′ + β)/(1 + βμ′)。
  N(p) = ∫_{(−1,1)} D(μ)^p w(μ) dμ、F(p) = N(p)/N(0)（全天平均 ⟨D^p⟩）。

ここで証明した言明（0 ≤ β < 1、d は実数）：
  (1) `aberration_D`・`aberration_weight`・`aberration_deriv`：光行差の写像で D(φ(μ′)) = D′(μ′)、
      1 − φ² = (1 − μ′²)/D′²、dφ/dμ′ = 1/D′²。したがって w(μ)dμ = D′^(−(d−1)) w(μ′)dμ′
      （立体角の冪 d − 1、原稿の計算 2.1 の一般の形）。
  (2) `N_source_frame`：N(p) = ∫ D′(μ′)^(p−(d−1)) w(μ′) dμ′（すべての実数 d, p で、積分の置き換え）。
  (3) `N_symm`・`F_symm`：N(p) = N(d − 1 − p)、F(p) = F(d − 1 − p)（すべての実数 d）。
  (4) d ≥ 3 で：`F_d`：F(d) = γ、`F_d_succ`：F(d + 1) = γ²(1 + β²/d)。
  (5) d ≥ 3, 0 < β < 1 で：`F_lt_one`：0 < p < d − 1 なら F(p) < 1、
      `F_gt_one`：p < 0 または p > d − 1 なら F(p) > 1、
      `F_eq_one_iff`：F(p) = 1 ⇔ p = 0 または p = d − 1。
足した仮定：(4)(5) は d ≥ 3（重みの冪 (d − 3)/2 ≥ 0 で、重みが [−1, 1] で連続になる範囲）。
d = 2（重み (1 − μ²)^(−1/2)、端で発散するが積分できる）は (1)〜(3) には入るが、(4)(5) は形式化していない。
確かめの係の案との違い：係は「F は p について狭義の対数凸」を挙げたが、ここでは対数凸性そのものは示さず、
exp の凸性を各点で使って (5) を直接出した。原稿の「p = d − 1 のときだけ 1」は p = 0 でも自明に 1 に
なるので「p = 0 と p = d − 1 だけ」が正しい（係の指摘のとおり、機械でも確かめた）。
形式化していないもの：乱数の値、半分の光子が入る角、届く間隔の幾何、宇宙背景放射の数、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1040

open Real Set MeasureTheory intervalIntegral

/-- ローレンツ因子 γ = 1/√(1 − β²)。 -/
noncomputable def γ (β : ℝ) : ℝ := 1 / √(1 - β ^ 2)

/-- 観測者の系のドップラー因子 D(μ) = 1/(γ(1 − βμ))。 -/
noncomputable def Dobs (β μ : ℝ) : ℝ := 1 / (γ β * (1 - β * μ))

/-- 源の系のドップラー因子 D′(μ′) = γ(1 + βμ′)。 -/
noncomputable def Dsrc (β μ : ℝ) : ℝ := γ β * (1 + β * μ)

/-- 向きの重み w(μ) = (1 − μ²)^a、a = (d − 3)/2。 -/
noncomputable def w (a μ : ℝ) : ℝ := (1 - μ ^ 2) ^ a

/-- 光行差の写像 μ = (μ′ + β)/(1 + βμ′)。 -/
noncomputable def φ (β μ : ℝ) : ℝ := (μ + β) / (1 + β * μ)

/-- N(p) = ∫_{(−1,1)} D(μ)^p w(μ) dμ。 -/
noncomputable def N (d β p : ℝ) : ℝ := ∫ μ in Ioo (-1) 1, Dobs β μ ^ p * w ((d - 3) / 2) μ

/-- 全天平均 F(p) = ⟨D^p⟩ = N(p)/N(0)。 -/
noncomputable def F (d β p : ℝ) : ℝ := N d β p / N d β 0

section basic

variable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
include hβ0 hβ1

theorem one_sub_sq_pos : 0 < 1 - β ^ 2 := by nlinarith

theorem γ_pos : 0 < γ β := by
  unfold γ; have := one_sub_sq_pos hβ0 hβ1; positivity

theorem γ_sq : γ β ^ 2 * (1 - β ^ 2) = 1 := by
  unfold γ
  have h := one_sub_sq_pos hβ0 hβ1
  rw [div_pow, sq_sqrt h.le]; field_simp

theorem one_add_pos {μ : ℝ} (hμ : μ ∈ Icc (-1 : ℝ) 1) : 0 < 1 + β * μ := by
  have := hμ.1; nlinarith

theorem one_sub_pos {μ : ℝ} (hμ : μ ∈ Icc (-1 : ℝ) 1) : 0 < 1 - β * μ := by
  have := hμ.2; nlinarith

theorem Dsrc_pos {μ : ℝ} (hμ : μ ∈ Icc (-1 : ℝ) 1) : 0 < Dsrc β μ :=
  mul_pos (γ_pos hβ0 hβ1) (one_add_pos hβ0 hβ1 hμ)

theorem Dobs_pos {μ : ℝ} (hμ : μ ∈ Icc (-1 : ℝ) 1) : 0 < Dobs β μ := by
  unfold Dobs; have := γ_pos hβ0 hβ1; have := one_sub_pos hβ0 hβ1 hμ; positivity

/-- (1) 光行差の写像で、観測者の D は源の D′ になる。 -/
theorem aberration_D {μ : ℝ} (hμ : μ ∈ Icc (-1 : ℝ) 1) : Dobs β (φ β μ) = Dsrc β μ := by
  have h1 := one_add_pos hβ0 hβ1 hμ
  have hg := γ_pos hβ0 hβ1
  have hs := γ_sq hβ0 hβ1
  unfold Dobs Dsrc φ
  have : 1 - β * ((μ + β) / (1 + β * μ)) = (1 - β ^ 2) / (1 + β * μ) := by field_simp; ring
  rw [this]
  have h2 := one_sub_sq_pos hβ0 hβ1
  field_simp
  nlinarith [hs]

/-- (1) 1 − φ² = (1 − μ′²)/D′²。 -/
theorem aberration_weight {μ : ℝ} (hμ : μ ∈ Icc (-1 : ℝ) 1) :
    1 - φ β μ ^ 2 = (1 - μ ^ 2) / Dsrc β μ ^ 2 := by
  have h1 := one_add_pos hβ0 hβ1 hμ
  have hg := γ_pos hβ0 hβ1
  have hs := γ_sq hβ0 hβ1
  unfold φ Dsrc
  have h2 : (1 - β ^ 2) = 1 / γ β ^ 2 := by field_simp; linarith
  have h1' : 1 + β * μ ≠ 0 := ne_of_gt h1
  have key : 1 - ((μ + β) / (1 + β * μ)) ^ 2 = (1 - β ^ 2) * (1 - μ ^ 2) / (1 + β * μ) ^ 2 := by
    rw [div_pow, eq_div_iff (pow_ne_zero 2 h1'), sub_mul,
        div_mul_cancel₀ _ (pow_ne_zero 2 h1')]; ring
  rw [key, h2]; field_simp

/-- (1) dφ/dμ′ = 1/D′²。 -/
theorem aberration_deriv {μ : ℝ} (hμ : μ ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt (φ β) (1 / Dsrc β μ ^ 2) μ := by
  have h1 := one_add_pos hβ0 hβ1 hμ
  have hg := γ_pos hβ0 hβ1
  have hs := γ_sq hβ0 hβ1
  have := ((hasDerivAt_id' μ).add_const β).div (
      (hasDerivAt_const μ 1).add ((hasDerivAt_id' μ).const_mul β))
    (ne_of_gt h1)
  unfold φ
  refine this.congr_deriv ?_
  simp only [Pi.add_apply]
  unfold Dsrc
  have h2 : (1 - β ^ 2) = 1 / γ β ^ 2 := by field_simp; linarith
  rw [show 1 * (1 + β * μ) - (μ + β) * (0 + β * 1) = 1 - β ^ 2 by ring, h2]
  field_simp

theorem φ_image : φ β '' Ioo (-1) 1 = Ioo (-1) 1 := by
  ext x
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    have h1 := one_add_pos hβ0 hβ1 (Ioo_subset_Icc_self hμ)
    unfold φ
    constructor
    · rw [lt_div_iff₀ h1]; nlinarith [hμ.1]
    · rw [div_lt_iff₀ h1]; nlinarith [hμ.2]
  · intro hx
    have h1 : 0 < 1 - β * x := one_sub_pos hβ0 hβ1 (Ioo_subset_Icc_self hx)
    refine ⟨(x - β) / (1 - β * x), ⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ h1]; nlinarith [hx.1]
    · rw [div_lt_iff₀ h1]; nlinarith [hx.2]
    · unfold φ
      have : 1 + β * ((x - β) / (1 - β * x)) = (1 - β ^ 2) / (1 - β * x) := by field_simp; ring
      have h1' : 1 - β * x ≠ 0 := ne_of_gt h1
      have hn : (x - β) / (1 - β * x) + β = x * (1 - β ^ 2) / (1 - β * x) := by
        rw [eq_div_iff h1', add_mul, div_mul_cancel₀ _ h1']; ring
      have h2 := one_sub_sq_pos hβ0 hβ1
      rw [this, hn, div_div_div_cancel_right₀ h1', mul_div_assoc, div_self (ne_of_gt h2), mul_one]

theorem φ_injOn : InjOn (φ β) (Ioo (-1) 1) := by
  intro x hx y hy hxy
  have h1 := one_add_pos hβ0 hβ1 (Ioo_subset_Icc_self hx)
  have h2 := one_add_pos hβ0 hβ1 (Ioo_subset_Icc_self hy)
  have h3 := one_sub_sq_pos hβ0 hβ1
  unfold φ at hxy
  rw [div_eq_div_iff (ne_of_gt h1) (ne_of_gt h2)] at hxy
  have : (1 - β ^ 2) * (x - y) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · linarith

/-- 被積分関数の置き換え：|φ′|·D(φ)^p·w(φ) = D′^(p−(d−1))·w。 -/
theorem integrand_transform (d p : ℝ) {μ : ℝ} (hμ : μ ∈ Ioo (-1 : ℝ) 1) :
    |1 / Dsrc β μ ^ 2| * (Dobs β (φ β μ) ^ p * w ((d - 3) / 2) (φ β μ)) =
      Dsrc β μ ^ (p - (d - 1)) * w ((d - 3) / 2) μ := by
  have hμ' := Ioo_subset_Icc_self hμ
  have hD := Dsrc_pos hβ0 hβ1 hμ'
  have hw : 0 ≤ 1 - μ ^ 2 := by nlinarith [hμ.1, hμ.2]
  rw [aberration_D hβ0 hβ1 hμ', w, w, aberration_weight hβ0 hβ1 hμ',
    abs_of_pos (by positivity), div_rpow hw (by positivity)]
  rw [show Dsrc β μ ^ 2 = Dsrc β μ ^ (2 : ℝ) by norm_cast, ← rpow_mul hD.le]
  have e : p - (d - 1) = p - 2 * ((d - 3) / 2) - 2 := by ring
  rw [e, rpow_sub hD, rpow_sub hD]
  have : 0 < Dsrc β μ ^ (2 * ((d - 3) / 2)) := rpow_pos_of_pos hD _
  have : 0 < Dsrc β μ ^ (2 : ℝ) := rpow_pos_of_pos hD _
  field_simp

/-- (2) 源の系で書いた N。 -/
theorem N_source_frame (d p : ℝ) :
    N d β p = ∫ μ in Ioo (-1) 1, Dsrc β μ ^ (p - (d - 1)) * w ((d - 3) / 2) μ := by
  unfold N
  conv_lhs => rw [← φ_image hβ0 hβ1]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x hx => (aberration_deriv hβ0 hβ1 (Ioo_subset_Icc_self hx)).hasDerivWithinAt)
    (φ_injOn hβ0 hβ1)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro μ hμ
  simp only [smul_eq_mul]
  exact integrand_transform hβ0 hβ1 d p hμ

omit hβ0 hβ1 in
/-- 反転 μ ↦ −μ で (−1, 1) の上の積分は変わらない。 -/
theorem integral_neg_Ioo (f : ℝ → ℝ) :
    ∫ μ in Ioo (-1 : ℝ) 1, f μ = ∫ μ in Ioo (-1 : ℝ) 1, f (-μ) := by
  have himg : (fun x : ℝ => -x) '' Ioo (-1) 1 = Ioo (-1) 1 := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
    · intro hx; exact ⟨-x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, neg_neg x⟩
  conv_lhs => rw [← himg]
  rw [integral_image_eq_integral_abs_deriv_smul (f' := fun _ => -1) measurableSet_Ioo
    (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt) (fun x _ y _ h => neg_injective h)]
  simp

/-- (3) N(p) = N(d − 1 − p)。 -/
theorem N_symm (d p : ℝ) : N d β p = N d β (d - 1 - p) := by
  rw [N_source_frame hβ0 hβ1, integral_neg_Ioo]
  unfold N
  apply setIntegral_congr_fun measurableSet_Ioo
  intro μ hμ
  have hμ' := Ioo_subset_Icc_self hμ
  have hneg : Dsrc β (-μ) = (Dobs β μ)⁻¹ := by
    unfold Dsrc Dobs; rw [one_div, inv_inv]; ring
  have hw : w ((d - 3) / 2) (-μ) = w ((d - 3) / 2) μ := by unfold w; ring_nf
  simp only
  rw [hneg, hw, inv_rpow (Dobs_pos hβ0 hβ1 hμ').le, ← rpow_neg (Dobs_pos hβ0 hβ1 hμ').le]
  congr 2; ring

/-- (3) F(p) = F(d − 1 − p)。 -/
theorem F_symm (d p : ℝ) : F d β p = F d β (d - 1 - p) := by
  unfold F; rw [N_symm hβ0 hβ1 d p]

end basic

section moments

/-- 集合の上の積分を区間の積分に直す。 -/
theorem setIntegral_Ioo_eq (f : ℝ → ℝ) :
    ∫ μ in Ioo (-1 : ℝ) 1, f μ = ∫ μ in (-1 : ℝ)..1, f μ := by
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]

variable {a : ℝ} (ha : 0 ≤ a)
include ha

theorem w_cont : Continuous (w a) := by
  unfold w; fun_prop

omit ha in
theorem w_nonneg {μ : ℝ} (hμ : μ ∈ Icc (-1 : ℝ) 1) : 0 ≤ w a μ := by
  unfold w; apply rpow_nonneg; nlinarith [hμ.1, hμ.2]

omit ha in
/-- ∫ μ w = 0（奇関数）。 -/
theorem moment_one : ∫ μ in (-1 : ℝ)..1, μ * w a μ = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) (fun μ => μ * w a μ)
  simp only [neg_neg] at h
  have hw : ∀ μ : ℝ, -μ * w a (-μ) = -(μ * w a μ) := by intro μ; unfold w; ring_nf
  simp only [hw, intervalIntegral.integral_neg] at h
  linarith

/-- ∫ μ² w = (1/(2a + 3)) ∫ w（部分積分）。 -/
theorem moment_two : (2 * a + 3) * ∫ μ in (-1 : ℝ)..1, μ ^ 2 * w a μ =
    ∫ μ in (-1 : ℝ)..1, w a μ := by
  -- v = (1 − μ²)^(a+1)、v′ = −2(a + 1)μ(1 − μ²)^a
  have hv : ∀ x, HasDerivAt (fun μ : ℝ => (1 - μ ^ 2) ^ (a + 1))
      ((0 - 2 * x) * (a + 1) * (1 - x ^ 2) ^ (a + 1 - 1)) x := by
    intro x
    have h0 : HasDerivAt (fun μ : ℝ => 1 - μ ^ 2) (0 - 2 * x) x :=
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).congr_deriv (by norm_num)
    exact h0.rpow_const (Or.inr (by linarith))
  have hcont_v : Continuous (fun μ : ℝ => (1 - μ ^ 2) ^ (a + 1)) := by
    have : 0 ≤ a + 1 := by linarith
    fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun μ => μ) (u' := fun _ => 1) (a := (-1 : ℝ)) (b := 1)
    (v := fun μ : ℝ => (1 - μ ^ 2) ^ (a + 1))
    (v' := fun x => (0 - 2 * x) * (a + 1) * (1 - x ^ 2) ^ (a + 1 - 1))
    continuous_id.continuousOn hcont_v.continuousOn
    (fun x _ => hasDerivAt_id' x) (fun x _ => hv x)
    intervalIntegrable_const (by
      apply Continuous.intervalIntegrable
      have : a + 1 - 1 = a := by ring
      simp only [this]; fun_prop)
  have e1 : (a + 1 - 1) = a := by ring
  simp only [e1] at hibp
  have hz : ((1 : ℝ) - 1 ^ 2) ^ (a + 1) = 0 := by norm_num; exact zero_rpow (by linarith)
  have hz' : ((1 : ℝ) - (-1) ^ 2) ^ (a + 1) = 0 := by norm_num; exact zero_rpow (by linarith)
  rw [hz, hz', mul_zero, mul_zero, sub_zero, zero_sub] at hibp
  simp only [one_mul] at hibp
  -- 左辺：∫ μ·(−2μ)(a+1) w = −2(a+1) ∫ μ² w
  have hL : ∫ x in (-1 : ℝ)..1, x * ((0 - 2 * x) * (a + 1) * (1 - x ^ 2) ^ a) =
      -(2 * (a + 1)) * ∫ x in (-1 : ℝ)..1, x ^ 2 * w a x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext x; unfold w; ring
  -- 右辺：(1 − μ²)^(a+1) = w − μ² w
  have hR : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ (a + 1) =
      (∫ x in (-1 : ℝ)..1, w a x) - ∫ x in (-1 : ℝ)..1, x ^ 2 * w a x := by
    rw [← intervalIntegral.integral_sub (Continuous.intervalIntegrable (w_cont ha) _ _)
      (Continuous.intervalIntegrable (by have := w_cont ha; fun_prop) _ _)]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    simp only [w]
    have hb : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    rw [rpow_add' hb (by linarith), rpow_one]; ring
  rw [hL, hR] at hibp
  linarith

end moments

section strict

variable {d β : ℝ} (hd : 3 ≤ d) (hβ0 : 0 < β) (hβ1 : β < 1)
include hd hβ0 hβ1

omit hβ0 hβ1 in
theorem a_nonneg : 0 ≤ (d - 3) / 2 := by linarith

omit hd in
theorem Dobs_contOn (p : ℝ) : ContinuousOn (fun μ => Dobs β μ ^ p) (Icc (-1) 1) := by
  intro μ hμ
  have h := Dobs_pos hβ0.le hβ1 hμ
  have h1 := one_sub_pos hβ0.le hβ1 hμ
  have hg := γ_pos hβ0.le hβ1
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.rpow_const _ (Or.inl (ne_of_gt h))
  exact ContinuousAt.div continuousAt_const
    (continuousAt_const.mul (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)))
    (ne_of_gt (mul_pos hg h1))

theorem integrand_contOn (p : ℝ) :
    ContinuousOn (fun μ => Dobs β μ ^ p * w ((d - 3) / 2) μ) (Icc (-1) 1) :=
  (Dobs_contOn hβ0 hβ1 p).mul (w_cont (a_nonneg hd)).continuousOn

omit hd hβ0 hβ1 in
theorem N_eq_interval (p : ℝ) :
    N d β p = ∫ μ in (-1 : ℝ)..1, Dobs β μ ^ p * w ((d - 3) / 2) μ := by
  unfold N; rw [setIntegral_Ioo_eq]

omit hd hβ0 hβ1 in
theorem N_zero_eq : N d β 0 = ∫ μ in (-1 : ℝ)..1, w ((d - 3) / 2) μ := by
  rw [N_eq_interval]; simp

omit hβ0 hβ1 in
theorem N_zero_pos : 0 < N d β 0 := by
  rw [N_zero_eq]
  have ha := a_nonneg hd
  have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (a := -1) (b := 1)
    (f := fun _ => (0 : ℝ)) (g := w ((d - 3) / 2)) (by norm_num) continuousOn_const
    (w_cont ha).continuousOn (fun x hx => w_nonneg (Ioc_subset_Icc_self hx))
    ⟨0, by norm_num, by simp [w]⟩
  simpa using this

/-- (4) F(d) = γ。 -/
theorem F_d : F d β d = γ β := by
  have ha := a_nonneg hd
  have hN0 := N_zero_pos (β := β) hd
  unfold F
  rw [N_symm hβ0.le hβ1 d d, show d - 1 - d = -1 by ring, N_eq_interval]
  have hc : ∀ μ ∈ uIcc (-1 : ℝ) 1, Dobs β μ ^ (-1 : ℝ) * w ((d - 3) / 2) μ =
      γ β * w ((d - 3) / 2) μ - γ β * β * (μ * w ((d - 3) / 2) μ) := by
    intro μ hμ
    rw [uIcc_of_le (by norm_num)] at hμ
    rw [rpow_neg_one]; unfold Dobs; rw [one_div, inv_inv]; ring
  rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_sub
    ((w_cont ha).intervalIntegrable _ _ |>.const_mul _)
    ((by have := w_cont ha; fun_prop :
        Continuous fun μ => μ * w ((d - 3) / 2) μ).intervalIntegrable _ _
      |>.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, moment_one,
    ← N_zero_eq]
  field_simp; ring

/-- (4) F(d + 1) = γ²(1 + β²/d)。 -/
theorem F_d_succ : F d β (d + 1) = γ β ^ 2 * (1 + β ^ 2 / d) := by
  have ha := a_nonneg hd
  have hN0 := N_zero_pos (β := β) hd
  have hd0 : 0 < d := by linarith
  unfold F
  rw [N_symm hβ0.le hβ1 d (d + 1), show d - 1 - (d + 1) = -2 by ring, N_eq_interval]
  have hc : ∀ μ ∈ uIcc (-1 : ℝ) 1, Dobs β μ ^ (-2 : ℝ) * w ((d - 3) / 2) μ =
      γ β ^ 2 * w ((d - 3) / 2) μ - 2 * γ β ^ 2 * β * (μ * w ((d - 3) / 2) μ)
        + γ β ^ 2 * β ^ 2 * (μ ^ 2 * w ((d - 3) / 2) μ) := by
    intro μ hμ
    rw [uIcc_of_le (by norm_num)] at hμ
    have hD := Dobs_pos hβ0.le hβ1 hμ
    rw [rpow_neg hD.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
    unfold Dobs; rw [one_div, inv_pow, inv_inv]; ring
  have hw1 := (w_cont ha).intervalIntegrable (μ := volume) (-1) 1
  have hw2 := (by have := w_cont ha; fun_prop :
      Continuous fun μ => μ * w ((d - 3) / 2) μ).intervalIntegrable
    (μ := volume) (-1) 1
  have hw3 := (by have := w_cont ha; fun_prop :
      Continuous fun μ => μ ^ 2 * w ((d - 3) / 2) μ).intervalIntegrable
    (μ := volume) (-1) 1
  rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_add
    ((hw1.const_mul _).sub (hw2.const_mul _)) (hw3.const_mul _),
    intervalIntegral.integral_sub (hw1.const_mul _) (hw2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, moment_one]
  have hm2 := moment_two ha
  have e : 2 * ((d - 3) / 2) + 3 = d := by ring
  rw [e] at hm2
  have : ∫ μ in (-1 : ℝ)..1, μ ^ 2 * w ((d - 3) / 2) μ =
      (∫ μ in (-1 : ℝ)..1, w ((d - 3) / 2) μ) / d := by
    field_simp; linarith
  rw [this, ← N_zero_eq]
  field_simp; ring

omit hd hβ0 hβ1 in
/-- 各点の凸性：t ∈ (0,1)、x ≠ 0 なら e^(t·s·x) < (1 − t) + t·e^(s·x)。 -/
theorem pointwise_convex {t s x : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hs : s ≠ 0) (hx : x ≠ 0) :
    exp (t * (s * x)) < (1 - t) + t * exp (s * x) := by
  have := strictConvexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (s * x)) (by
    intro h; exact mul_ne_zero hs hx h.symm) (show (0 : ℝ) < 1 - t by linarith) ht0 (by ring)
  simpa [smul_eq_mul] using this

omit hd hβ0 hβ1 in
theorem pointwise_convex_le {t s x : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    exp (t * (s * x)) ≤ (1 - t) + t * exp (s * x) := by
  have := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (s * x))
      (show (0 : ℝ) ≤ 1 - t by linarith) ht0.le
    (by ring)
  simpa [smul_eq_mul] using this

omit hd in
theorem γ_gt_one : 1 < γ β := by
  unfold γ
  have h := one_sub_sq_pos hβ0.le hβ1
  rw [one_lt_div (sqrt_pos.mpr h), sqrt_lt' one_pos]; nlinarith

/-- 主な一歩：s ≠ 0、0 < t < 1 で N(t·s) < (1 − t)N(0) + t·N(s)。 -/
theorem N_convex_strict {t s : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hs : s ≠ 0) :
    N d β (t * s) < (1 - t) * N d β 0 + t * N d β s := by
  have ha := a_nonneg hd
  rw [N_eq_interval, N_zero_eq, N_eq_interval,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((w_cont ha).intervalIntegrable _ _ |>.const_mul _)
      ((integrand_contOn hd hβ0 hβ1 s).intervalIntegrable_of_Icc (by norm_num) |>.const_mul _)]
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num)
    (integrand_contOn hd hβ0 hβ1 (t * s))
  · exact (continuousOn_const.mul (w_cont ha).continuousOn).add
      (continuousOn_const.mul (integrand_contOn hd hβ0 hβ1 s))
  · intro μ hμ
    have hμ' := Ioc_subset_Icc_self hμ
    have hD := Dobs_pos hβ0.le hβ1 hμ'
    have hw := w_nonneg (a := (d - 3) / 2) hμ'
    rw [rpow_def_of_pos hD, rpow_def_of_pos hD]
    have := pointwise_convex_le (s := s) (x := log (Dobs β μ)) ht0 ht1
    have e : log (Dobs β μ) * (t * s) = t * (s * log (Dobs β μ)) := by ring
    have e2 : log (Dobs β μ) * s = s * log (Dobs β μ) := by ring
    rw [e, e2]
    nlinarith
  · refine ⟨0, by norm_num, ?_⟩
    have h0 : (0 : ℝ) ∈ Icc (-1) 1 := by norm_num
    have hD := Dobs_pos hβ0.le hβ1 h0
    have hw0 : w ((d - 3) / 2) 0 = 1 := by simp [w]
    rw [hw0, rpow_def_of_pos hD, rpow_def_of_pos hD]
    have hlog : log (Dobs β 0) ≠ 0 := by
      unfold Dobs; simp only [mul_zero, sub_zero, mul_one, one_div, log_inv, neg_ne_zero]
      exact ne_of_gt (log_pos (γ_gt_one hβ0 hβ1))
    have := pointwise_convex (s := s) ht0 ht1 hs hlog
    have e : log (Dobs β 0) * (t * s) = t * (s * log (Dobs β 0)) := by ring
    have e2 : log (Dobs β 0) * s = s * log (Dobs β 0) := by ring
    rw [e, e2]; linarith

/-- (5) 0 < p < d − 1 なら F(p) < 1。 -/
theorem F_lt_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < d - 1) : F d β p < 1 := by
  have hN0 := N_zero_pos (β := β) hd
  have hs : d - 1 ≠ 0 := by linarith
  set t := p / (d - 1)
  have ht0 : 0 < t := div_pos hp0 (by linarith)
  have ht1 : t < 1 := (div_lt_one (by linarith)).mpr hp1
  have key := N_convex_strict hd hβ0 hβ1 ht0 ht1 hs
  have e : t * (d - 1) = p := by simp only [t]; field_simp
  have hsym : N d β (d - 1) = N d β 0 := by rw [N_symm hβ0.le hβ1 d 0]; ring_nf
  rw [e, hsym] at key
  unfold F; rw [div_lt_one hN0]; linarith

/-- (5) p > d − 1 なら F(p) > 1。 -/
theorem F_gt_one_of_gt {p : ℝ} (hp : d - 1 < p) : 1 < F d β p := by
  have hN0 := N_zero_pos (β := β) hd
  have hpp : 0 < p := by linarith
  set t := (d - 1) / p
  have ht0 : 0 < t := div_pos (by linarith) hpp
  have ht1 : t < 1 := (div_lt_one hpp).mpr hp
  have key := N_convex_strict hd hβ0 hβ1 ht0 ht1 (ne_of_gt hpp)
  have e : t * p = d - 1 := by simp only [t]; field_simp
  have hsym : N d β (d - 1) = N d β 0 := by rw [N_symm hβ0.le hβ1 d 0]; ring_nf
  rw [e, hsym] at key
  unfold F; rw [one_lt_div hN0]; nlinarith

/-- (5) p < 0 または p > d − 1 なら F(p) > 1。 -/
theorem F_gt_one {p : ℝ} (hp : p < 0 ∨ d - 1 < p) : 1 < F d β p := by
  rcases hp with hp | hp
  · rw [F_symm hβ0.le hβ1 d p]; exact F_gt_one_of_gt hd hβ0 hβ1 (by linarith)
  · exact F_gt_one_of_gt hd hβ0 hβ1 hp

/-- (5) F(p) = 1 ⇔ p = 0 または p = d − 1。 -/
theorem F_eq_one_iff (p : ℝ) : F d β p = 1 ↔ p = 0 ∨ p = d - 1 := by
  have hN0 := N_zero_pos (β := β) hd
  constructor
  · intro h
    by_contra hne
    push Not at hne
    rcases lt_trichotomy p 0 with h1 | h1 | h1
    · linarith [F_gt_one hd hβ0 hβ1 (Or.inl h1)]
    · exact hne.1 h1
    · rcases lt_trichotomy p (d - 1) with h2 | h2 | h2
      · linarith [F_lt_one hd hβ0 hβ1 h1 h2]
      · exact hne.2 h2
      · linarith [F_gt_one hd hβ0 hβ1 (Or.inr h2)]
  · rintro (h | h)
    · rw [h]; unfold F; exact div_self (ne_of_gt hN0)
    · rw [h, F_symm hβ0.le hβ1 d (d - 1), show d - 1 - (d - 1) = 0 by ring]
      unfold F; exact div_self (ne_of_gt hN0)

end strict

end Paper1040

end Yamagishi
