/-
論文837『二点弁別の閾には限りが二つある。受容野を細くしても、受容器の間隔より下がらない』の格上げ
（一般の形）。

日本語の一文：ガウスの受容野と間隔 d の受容器の並びで、谷が両側の山の θ 倍（θ ≤ 1）より低いときに
二点と判定するなら、どの幅 σ・間隔 d・位相 φ・θ でも、判定される二点の隔たり s は 2σ と d の両方より大きい。
English: With Gaussian receptive fields of width σ, receptors at i·d + φ, and the rule
"some receptor between two others responds less than θ times each of them" (0 < θ ≤ 1),
any detected separation s satisfies s > 2σ and s > d, for every σ, d, φ and θ.

原稿（837_yamagishi_two_point_discrimination_has_two_limits/…_jp.tex）は、判定 0.95・位相 24 通りで、
密な並びの閾/σ = 2.286668、谷の約束を緩めても 2σ を割らないこと、d = 2 で σ を細くすると閾が 3.000513 で
止まること、位相で間隔の 1.0037〜2.0003 倍に動くことを数表で示す。下からの床の一般の証明は無い。

ここで証明した言明（応答 f(x) = g(x + s/2) + g(x − s/2)、g(y) = exp(−y²/(2σ²))、σ > 0、s > 0）：
  (1) `f_strictAntiOn_of_le`：s ≤ 2σ なら f は [0, ∞) で狭義に減る（山は一つ）。
  (2) `quasi_concave`：どの s でも、0 ≤ u < v < w で f(v) ≥ min(f(u), f(w))（[0, ∞) で谷を作らない）。
  (3) `valley_bounds`：実数 L < M < R で f(M) < f(L)、f(M) < f(R)（谷）なら |L|, |R| < s。
  (4) `two_sigma_floor`：谷が在れば s > 2σ。
  (5) `floor`：受容器 x_i = i d + φ（i は整数、d > 0）で二点と判定されれば s > 2σ かつ s > d。
足した仮定：原稿の「谷が山の 0.95 倍より低い」を「添字が l < m < r の受容器で、v_m が v_l と v_r の
どちらの θ 倍よりも低い（0 < θ ≤ 1）」と読んだ。二点は ±s/2 に置き s > 0 とした。
形式化していないもの：床が極限で届くこと、上からの限り（閾がおよそ c(θ)σ と 2d の大きいほう）、
密な極限の比 2.2866 の値、数表、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper837

open Real Set

/-- 受容野 g(y) = exp(−y²/(2σ²))。 -/
noncomputable def g (σ y : ℝ) : ℝ := exp (-(y ^ 2) / (2 * σ ^ 2))

/-- 二点（±a、a = s/2）への応答 f(x) = g(x + a) + g(x − a)。 -/
noncomputable def f (σ a x : ℝ) : ℝ := g σ (x + a) + g σ (x - a)

theorem g_pos (σ y : ℝ) : 0 < g σ y := exp_pos _

theorem f_pos (σ a x : ℝ) : 0 < f σ a x := add_pos (g_pos _ _) (g_pos _ _)

theorem g_neg (σ y : ℝ) : g σ (-y) = g σ y := by unfold g; ring_nf

theorem f_even (σ a x : ℝ) : f σ a (-x) = f σ a x := by
  unfold f
  rw [show -x + a = -(x - a) by ring, show -x - a = -(x + a) by ring, g_neg, g_neg, add_comm]

/-- g は 0 ≤ |y| ≤ |z| で減る。 -/
theorem g_le_of_sq_le {σ y z : ℝ} (h : y ^ 2 ≤ z ^ 2) : g σ z ≤ g σ y := by
  unfold g
  apply exp_le_exp.mpr
  apply div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem g_lt_of_sq_lt {σ y z : ℝ} (hσ : 0 < σ) (h : y ^ 2 < z ^ 2) : g σ z < g σ y := by
  unfold g
  apply exp_lt_exp.mpr
  apply div_lt_div_of_pos_right (by linarith) (by positivity)

/-! ### 微分と、その符号を決める q(x) = x cosh(ax/σ²) − a sinh(ax/σ²) -/

theorem hasDerivAt_g_shift (σ c x : ℝ) :
    HasDerivAt (fun x => g σ (x + c)) (-(x + c) / σ ^ 2 * g σ (x + c)) x := by
  unfold g
  have h1 : HasDerivAt (fun x => -((x + c) ^ 2) / (2 * σ ^ 2))
      (-(2 * (x + c) ^ 1 * 1) / (2 * σ ^ 2)) x :=
    (((hasDerivAt_id' x).add_const c).pow 2).neg.div_const _
  have := h1.exp
  refine this.congr_deriv ?_
  by_cases hσ : σ = 0
  · simp [hσ]
  field_simp

noncomputable def q (σ a x : ℝ) : ℝ := x * cosh (a * x / σ ^ 2) - a * sinh (a * x / σ ^ 2)

theorem hasDerivAt_f (σ a x : ℝ) (hσ : 0 < σ) :
    HasDerivAt (f σ a)
      (-(2 * exp (-(x ^ 2 + a ^ 2) / (2 * σ ^ 2)) / σ ^ 2) * q σ a x) x := by
  have h := (hasDerivAt_g_shift σ a x).add (hasDerivAt_g_shift σ (-a) x)
  simp only [← sub_eq_add_neg] at h
  refine h.congr_deriv ?_
  unfold g q
  rw [cosh_eq, sinh_eq]
  have e1 : exp (-((x + a) ^ 2) / (2 * σ ^ 2)) =
      exp (-(x ^ 2 + a ^ 2) / (2 * σ ^ 2)) * exp (-(a * x / σ ^ 2)) := by
    rw [← exp_add]; congr 1; field_simp; ring
  have e2 : exp (-((x - a) ^ 2) / (2 * σ ^ 2)) =
      exp (-(x ^ 2 + a ^ 2) / (2 * σ ^ 2)) * exp (a * x / σ ^ 2) := by
    rw [← exp_add]; congr 1; field_simp; ring
  rw [e1, e2]
  field_simp
  ring

/-- t > 0 で t cosh t > sinh t。 -/
theorem sinh_lt_mul_cosh {t : ℝ} (ht : 0 < t) : sinh t < t * cosh t := by
  let h : ℝ → ℝ := fun t => t * cosh t - sinh t
  have hd : ∀ t, HasDerivAt h (t * sinh t) t := by
    intro t
    have := ((hasDerivAt_id' t).mul (hasDerivAt_cosh t)).sub (hasDerivAt_sinh t)
    refine this.congr_deriv ?_
    ring
  have hmono : StrictMonoOn h (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hd t).deriv]
      exact mul_pos ht (sinh_pos_iff.mpr ht)
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr (le_of_lt ht)) ht
  simp [h] at this
  linarith

/-- G(t) = t cosh t / sinh t は (0, ∞) で狭義に増える。 -/
theorem G_strictMonoOn : StrictMonoOn (fun t => t * cosh t / sinh t) (Ioi 0) := by
  have hd : ∀ t, 0 < t → HasDerivAt (fun t => t * cosh t / sinh t)
      ((sinh t * cosh t - t) / sinh t ^ 2) t := by
    intro t ht
    have hs : sinh t ≠ 0 := ne_of_gt (sinh_pos_iff.mpr ht)
    have := ((hasDerivAt_id' t).mul (hasDerivAt_cosh t)).div (hasDerivAt_sinh t) hs
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply]
    have hc := cosh_sq t
    field_simp
    linear_combination (-t) * hc
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    have ht' : 0 < t := ht
    rw [(hd t ht).deriv]
    apply div_pos _ (by have := sinh_pos_iff.mpr ht'; positivity)
    have h2 := (self_lt_sinh_iff (x := 2 * t)).mpr (by linarith)
    rw [sinh_two_mul] at h2
    linarith

/-- x > 0 で q(x) > 0 ⇔ G(ax/σ²) > a²/σ²（a > 0）。 -/
theorem q_pos_iff {σ a x : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hx : 0 < x) :
    0 < q σ a x ↔
      a ^ 2 / σ ^ 2 < (a * x / σ ^ 2) * cosh (a * x / σ ^ 2) / sinh (a * x / σ ^ 2) := by
  have ht : 0 < a * x / σ ^ 2 := by positivity
  have hs : 0 < sinh (a * x / σ ^ 2) := sinh_pos_iff.mpr ht
  unfold q
  rw [lt_div_iff₀ hs]
  set S := sinh (a * x / σ ^ 2)
  set C := cosh (a * x / σ ^ 2)
  have e : a * x / σ ^ 2 * C = (a / σ ^ 2) * (x * C) := by ring
  rw [e]
  constructor
  · intro h
    have : a ^ 2 / σ ^ 2 * S = (a / σ ^ 2) * (a * S) := by ring
    rw [this]
    exact mul_lt_mul_of_pos_left (by linarith) (by positivity)
  · intro h
    have : a ^ 2 / σ ^ 2 * S = (a / σ ^ 2) * (a * S) := by ring
    rw [this] at h
    have := lt_of_mul_lt_mul_left h (by positivity)
    linarith

/-- q の符号は一度だけ − から + へ変わる：0 < x < y で q(x) > 0 なら q(y) > 0。 -/
theorem q_pos_mono {σ a x y : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hx : 0 < x) (hxy : x < y)
    (hq : 0 < q σ a x) : 0 < q σ a y := by
  have hy : 0 < y := hx.trans hxy
  rw [q_pos_iff hσ ha hx] at hq
  rw [q_pos_iff hσ ha hy]
  have h1 : a * x / σ ^ 2 < a * y / σ ^ 2 := by
    apply div_lt_div_of_pos_right _ (by positivity); nlinarith
  exact hq.trans (G_strictMonoOn (show 0 < a * x / σ ^ 2 by positivity)
    (show 0 < a * y / σ ^ 2 by positivity) h1)

/-! ### 山が一つになる場合と、[0, ∞) で谷を作らないこと -/

/-- (1) a ≤ σ（s ≤ 2σ）なら x > 0 で q(x) > 0。 -/
theorem q_pos_of_le {σ a x : ℝ} (hσ : 0 < σ) (ha : 0 < a) (haσ : a ≤ σ) (hx : 0 < x) :
    0 < q σ a x := by
  unfold q
  set t := a * x / σ ^ 2 with ht_def
  have ht : 0 < t := by positivity
  have hx' : x = σ ^ 2 / a * t := by rw [ht_def]; field_simp
  have hs : 0 < sinh t := sinh_pos_iff.mpr ht
  have key := sinh_lt_mul_cosh ht
  have hxc : x * cosh t = σ ^ 2 / a * t * cosh t := by rw [hx']
  rw [hxc]
  have hσa : a ≤ σ ^ 2 / a := by rw [le_div_iff₀ ha]; nlinarith
  have : σ ^ 2 / a * t * cosh t > σ ^ 2 / a * sinh t := by
    rw [mul_assoc]; exact mul_lt_mul_of_pos_left key (by positivity)
  nlinarith

/-- (1) s ≤ 2σ なら f は [0, ∞) で狭義に減る。 -/
theorem f_strictAntiOn_of_le {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) (haσ : a ≤ σ) :
    StrictAntiOn (f σ a) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact fun x _ => (hasDerivAt_f σ a x hσ).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_f σ a x hσ).deriv]
    have := q_pos_of_le hσ ha haσ hx
    have : 0 < 2 * exp (-(x ^ 2 + a ^ 2) / (2 * σ ^ 2)) / σ ^ 2 := by positivity
    nlinarith

/-- (2) どの a > 0 でも、0 ≤ u < v < w で f(v) < f(u) かつ f(v) < f(w) にはならない。 -/
theorem quasi_concave {σ a u v w : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hu : 0 ≤ u) (huv : u < v)
    (hvw : v < w) : ¬ (f σ a v < f σ a u ∧ f σ a v < f σ a w) := by
  rintro ⟨h1, h2⟩
  have hdiff : ∀ x, HasDerivAt (f σ a) _ x := fun x => hasDerivAt_f σ a x hσ
  obtain ⟨ξ₁, hξ₁, hs₁⟩ := exists_hasDerivAt_eq_slope (f σ a) _ huv
    (fun x _ => (hdiff x).continuousAt.continuousWithinAt) (fun x _ => hdiff x)
  obtain ⟨ξ₂, hξ₂, hs₂⟩ := exists_hasDerivAt_eq_slope (f σ a) _ hvw
    (fun x _ => (hdiff x).continuousAt.continuousWithinAt) (fun x _ => hdiff x)
  have hE : ∀ x, 0 < 2 * exp (-(x ^ 2 + a ^ 2) / (2 * σ ^ 2)) / σ ^ 2 := fun x => by positivity
  have hneg : 0 < q σ a ξ₁ := by
    have : (f σ a v - f σ a u) / (v - u) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
    rw [← hs₁] at this
    have := hE ξ₁
    nlinarith
  have hpos : q σ a ξ₂ < 0 := by
    have : 0 < (f σ a w - f σ a v) / (w - v) := div_pos (by linarith) (by linarith)
    rw [← hs₂] at this
    have := hE ξ₂
    nlinarith
  have := q_pos_mono (x := ξ₁) (y := ξ₂) hσ ha (by linarith [hξ₁.1])
    (by linarith [hξ₁.2, hξ₂.1]) hneg
  linarith

/-- y ≥ 2a なら f(y) < f(0)。 -/
theorem f_lt_f_zero {σ a y : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hy : 2 * a ≤ y) :
    f σ a y < f σ a 0 := by
  unfold f
  have h1 : g σ (y + a) < g σ (0 + a) := g_lt_of_sq_lt hσ (by nlinarith)
  have h2 : g σ (y - a) ≤ g σ (0 - a) := g_le_of_sq_le (by nlinarith)
  linarith

/-- 谷の中心が 0 以上のとき、両端は (−2a, 2a) に入る。 -/
theorem valley_bounds_nonneg {σ a L M R : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hM : 0 ≤ M)
    (hMR : M < R) (hL : f σ a M < f σ a L) (hR : f σ a M < f σ a R) :
    |L| < 2 * a ∧ |R| < 2 * a := by
  have h0 : f σ a 0 ≤ f σ a M := by
    rcases eq_or_lt_of_le hM with he | hlt
    · rw [he]
    · by_contra hc
      push Not at hc
      exact quasi_concave hσ ha le_rfl hlt hMR ⟨hc, hR⟩
  have hbound : ∀ x, f σ a 0 < f σ a x → |x| < 2 * a := by
    intro x hx
    by_contra hc
    push Not at hc
    rcases le_total 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0] at hc; linarith [f_lt_f_zero hσ ha hc]
    · rw [abs_of_nonpos hx0] at hc
      have := f_lt_f_zero hσ ha hc
      rw [f_even] at this
      linarith
  exact ⟨hbound L (by linarith), hbound R (by linarith)⟩

/-- (3) 谷 L < M < R が在れば |L|, |R| < 2a = s。 -/
theorem valley_bounds {σ a L M R : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (hLM : L < M) (hMR : M < R) (hL : f σ a M < f σ a L) (hR : f σ a M < f σ a R) :
    |L| < 2 * a ∧ |R| < 2 * a := by
  rcases le_total 0 M with hM | hM
  · exact valley_bounds_nonneg hσ ha hM hMR hL hR
  · have h := valley_bounds_nonneg (L := -R) (M := -M) (R := -L) hσ ha (by linarith)
      (by linarith) (by rw [f_even, f_even]; exact hR)
      (by rw [f_even, f_even]; exact hL)
    rw [abs_neg, abs_neg] at h
    exact ⟨h.2, h.1⟩

/-- (4) 谷が在れば a > σ（s > 2σ）。 -/
theorem two_sigma_floor {σ a L M R : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (hLM : L < M) (hMR : M < R) (hL : f σ a M < f σ a L) (hR : f σ a M < f σ a R) :
    σ < a := by
  by_contra hc
  push Not at hc
  have hanti := f_strictAntiOn_of_le hσ ha hc
  rcases le_total 0 M with hM | hM
  · have := hanti (mem_Ici.mpr hM) (mem_Ici.mpr (by linarith)) hMR
    linarith
  · have := hanti (mem_Ici.mpr (by linarith : (0 : ℝ) ≤ -M)) (mem_Ici.mpr (by linarith))
      (show -M < -L by linarith)
    rw [f_even, f_even] at this
    linarith

/-! ### 受容器の並びと判定 -/

/-- 受容器の位置 x_i = i d + φ。 -/
def pos (d φ : ℝ) (i : ℤ) : ℝ := i * d + φ

/-- 二点と判定される：添字 l < m < r の受容器で、谷 v_m が両側の v_l、v_r の θ 倍より低い。 -/
def Detect (σ s d φ θ : ℝ) : Prop :=
  ∃ l m r : ℤ, l < m ∧ m < r ∧
    f σ (s / 2) (pos d φ m) < θ * f σ (s / 2) (pos d φ l) ∧
    f σ (s / 2) (pos d φ m) < θ * f σ (s / 2) (pos d φ r)

/-- (5) どの σ, d, φ, θ ∈ (0, 1] でも、二点と判定されれば s > 2σ かつ s > d。 -/
theorem floor {σ s d φ θ : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hd : 0 < d) (hθ1 : θ ≤ 1)
    (hdet : Detect σ s d φ θ) : 2 * σ < s ∧ d < s := by
  obtain ⟨l, m, r, hlm, hmr, hL, hR⟩ := hdet
  have ha : 0 < s / 2 := by linarith
  have hL' : f σ (s / 2) (pos d φ m) < f σ (s / 2) (pos d φ l) := by
    have := f_pos σ (s / 2) (pos d φ l)
    nlinarith
  have hR' : f σ (s / 2) (pos d φ m) < f σ (s / 2) (pos d φ r) := by
    have := f_pos σ (s / 2) (pos d φ r)
    nlinarith
  have hlm' : pos d φ l < pos d φ m := by
    unfold pos
    have : (l : ℝ) < m := by exact_mod_cast hlm
    nlinarith
  have hmr' : pos d φ m < pos d φ r := by
    unfold pos
    have : (m : ℝ) < r := by exact_mod_cast hmr
    nlinarith
  refine ⟨by linarith [two_sigma_floor hσ ha hlm' hmr' hL' hR'], ?_⟩
  obtain ⟨hbL, hbR⟩ := valley_bounds hσ ha hlm' hmr' hL' hR'
  have hgap : 2 * d ≤ pos d φ r - pos d φ l := by
    unfold pos
    have h2 : (l : ℝ) + 2 ≤ r := by exact_mod_cast (show l + 2 ≤ r by omega)
    nlinarith
  have := abs_lt.mp hbL
  have := abs_lt.mp hbR
  linarith

end Paper837

end Yamagishi
