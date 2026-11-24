/-
論文587『天窓が壁の窓の二倍明るいのは、曇りの空の話である』の格上げ（一般の形）。

原稿（587_yamagishi_the_skylight_wins_under_cloud/…_jp.tex）は、空の輝度 L から水平な天窓と鉛直な壁の窓
の照度を E_h = ∫L sinγ dΩ、E_v = ∫L cosγ cosφ dΩ と置き、一様な空（比ちょうど 2）と CIE 標準曇天空
L = (1 + 2 sinγ)/3（比 2.524124）の二つの空だけを数える。直射は比 cot h と、北緯 35.7 度の三つの南中。

ここで証明した言明（輝度 L が高度 γ ∈ [0, π/2] だけの関数で、前の半球だけを見る・照り返しなしのとき、
比は E_h/E_v = π∫L sinγ cosγ dγ / ∫L cos²γ dγ。分子の ∫ を N(L)、分母の ∫ を D(L) と書く）：
  (1) `phi_integral`：φ(γ) = sinγ cosγ − (2/π)cos²γ は ∫₀^{π/2} φ = 0 で、`phi_nonneg_iff`：
      [0, π/2] で φ ≥ 0 ⇔ γ ≥ γ₀ = arctan(2/π)（符号が一度だけ変わる）。
  (2) `two_le_of_monotone`：L が高度について非減少なら 2·D(L) ≤ π·N(L)（比は 2 以上）。
      `le_two_of_antitone`：非増加なら π·N(L) ≤ 2·D(L)（比は 2 以下）。
      `two_lt_of_monotone`：非減少で、(0, π/2) の中の二点で値が違えば、真に 2·D(L) < π·N(L)。
  (3) `uniform_sky`：一様な空ではちょうど π·N = 2·D。
      `cie_overcast`：CIE 標準曇天空では π·N/D = 14π/(3π + 8)（≈ 2.5241）。
  (4) `direct_ratio`：直射だけなら比は sin h/cos h = tan h で、`direct_eq_iff`：等しい ⇔ h = 45°。
足した仮定：L は [0, π/2] で単調（可積分と非負は単調から足りる所だけを使った）。照度の式を高度の
一重積分に直す所（方位の積分）は原稿のとおりとして、比を一重積分の形で定義に置いた。
形式化していないもの：輝度が方位に依る空（成り立たない）、照り返し、逆向き（比が 2 以上でも L は単調とは
限らない）、緯度と南中の数値、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）

If the sky luminance depends only on altitude and is non-decreasing in it, a horizontal skylight
receives at least twice the illuminance of a vertical window, and at most twice if it is
non-increasing, with equality for a uniform sky; the proof uses that sinγcosγ − (2/π)cos²γ
integrates to zero and changes sign once, at arctan(2/π).
-/
import Mathlib

namespace Yamagishi

namespace Paper587

open Real Set intervalIntegral

/-- 重みの差 φ(γ) = sinγ cosγ − (2/π)cos²γ。 -/
noncomputable def phi (γ : ℝ) : ℝ := sin γ * cos γ - 2 / π * cos γ ^ 2

/-- 符号の変わる高度 γ₀ = arctan(2/π)。 -/
noncomputable def γ₀ : ℝ := arctan (2 / π)

/-- 天窓の側の積分 N(L) = ∫₀^{π/2} L sinγ cosγ dγ。 -/
noncomputable def Nint (L : ℝ → ℝ) : ℝ := ∫ γ in (0 : ℝ)..(π / 2), L γ * (sin γ * cos γ)

/-- 壁の窓の側の積分 D(L) = ∫₀^{π/2} L cos²γ dγ。 -/
noncomputable def Dint (L : ℝ → ℝ) : ℝ := ∫ γ in (0 : ℝ)..(π / 2), L γ * cos γ ^ 2

theorem int_sin_cos : ∫ γ in (0 : ℝ)..(π / 2), sin γ * cos γ = 1 / 2 := by
  rw [integral_sin_mul_cos₁]; simp

theorem int_cos_sq : ∫ γ in (0 : ℝ)..(π / 2), cos γ ^ 2 = π / 4 := by
  rw [integral_cos_sq]; simp; ring

/-- (1) ∫₀^{π/2} φ = 0。 -/
theorem phi_integral : ∫ γ in (0 : ℝ)..(π / 2), phi γ = 0 := by
  unfold phi
  rw [integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), integral_const_mul, int_sin_cos, int_cos_sq]
  field_simp
  ring

theorem γ₀_mem : 0 < γ₀ ∧ γ₀ < π / 2 :=
  ⟨arctan_pos.mpr (by positivity), arctan_lt_pi_div_two _⟩

/-- sinγ − (2/π)cosγ は [0, π/2] で狭義に増える。 -/
theorem psi_strictMonoOn : StrictMonoOn (fun γ => sin γ - 2 / π * cos γ) (Icc 0 (π / 2)) := by
  intro x hx y hy hxy
  simp only
  have h1 : sin x < sin y := strictMonoOn_sin ⟨by linarith [hx.1, pi_pos], hx.2⟩
    ⟨by linarith [hy.1, pi_pos], hy.2⟩ hxy
  have h2 : cos y < cos x := strictAntiOn_cos ⟨hx.1, by linarith [hx.2, pi_pos]⟩
    ⟨hy.1, by linarith [hy.2, pi_pos]⟩ hxy
  have : 0 < 2 / π := by positivity
  nlinarith

theorem psi_γ₀ : sin γ₀ - 2 / π * cos γ₀ = 0 := by
  unfold γ₀
  rw [sin_arctan, cos_arctan]
  field_simp
  ring

/-- (1) [0, π/2] で φ ≥ 0 ⇔ γ ≥ γ₀。φ < 0 ⇔ γ < γ₀（γ < π/2 のとき）。 -/
theorem phi_eq (γ : ℝ) : phi γ = cos γ * (sin γ - 2 / π * cos γ) := by unfold phi; ring

theorem phi_nonneg_of_ge {γ : ℝ} (h : γ ∈ Icc 0 (π / 2)) (hg : γ₀ ≤ γ) : 0 ≤ phi γ := by
  rw [phi_eq]
  have hc : 0 ≤ cos γ := cos_nonneg_of_mem_Icc ⟨by linarith [h.1, pi_pos], h.2⟩
  have hm : γ₀ ∈ Icc 0 (π / 2) := ⟨γ₀_mem.1.le, γ₀_mem.2.le⟩
  have : 0 ≤ sin γ - 2 / π * cos γ := by
    rw [← psi_γ₀]; exact psi_strictMonoOn.monotoneOn hm h hg
  positivity

theorem phi_nonpos_of_le {γ : ℝ} (h : γ ∈ Icc 0 (π / 2)) (hg : γ ≤ γ₀) : phi γ ≤ 0 := by
  rw [phi_eq]
  have hc : 0 ≤ cos γ := cos_nonneg_of_mem_Icc ⟨by linarith [h.1, pi_pos], h.2⟩
  have hm : γ₀ ∈ Icc 0 (π / 2) := ⟨γ₀_mem.1.le, γ₀_mem.2.le⟩
  have : sin γ - 2 / π * cos γ ≤ 0 := by
    rw [← psi_γ₀]; exact psi_strictMonoOn.monotoneOn h hm hg
  exact mul_nonpos_of_nonneg_of_nonpos hc this

theorem phi_pos_of_gt {γ : ℝ} (h : γ ∈ Ioo 0 (π / 2)) (hg : γ₀ < γ) : 0 < phi γ := by
  rw [phi_eq]
  have hc : 0 < cos γ := cos_pos_of_mem_Ioo ⟨by linarith [h.1, pi_pos], h.2⟩
  have hm : γ₀ ∈ Icc 0 (π / 2) := ⟨γ₀_mem.1.le, γ₀_mem.2.le⟩
  have : 0 < sin γ - 2 / π * cos γ := by
    rw [← psi_γ₀]; exact psi_strictMonoOn hm ⟨h.1.le, h.2.le⟩ hg
  positivity

theorem phi_neg_of_lt {γ : ℝ} (h : γ ∈ Ioo 0 (π / 2)) (hg : γ < γ₀) : phi γ < 0 := by
  rw [phi_eq]
  have hc : 0 < cos γ := cos_pos_of_mem_Ioo ⟨by linarith [h.1, pi_pos], h.2⟩
  have hm : γ₀ ∈ Icc 0 (π / 2) := ⟨γ₀_mem.1.le, γ₀_mem.2.le⟩
  have : sin γ - 2 / π * cos γ < 0 := by
    rw [← psi_γ₀]; exact psi_strictMonoOn ⟨h.1.le, h.2.le⟩ hm hg
  exact mul_neg_of_pos_of_neg hc this

theorem phi_nonneg_iff {γ : ℝ} (h : γ ∈ Ioo 0 (π / 2)) : 0 ≤ phi γ ↔ γ₀ ≤ γ := by
  constructor
  · intro hp; by_contra hc; have := phi_neg_of_lt h (lt_of_not_ge hc); linarith
  · intro hg; exact phi_nonneg_of_ge ⟨h.1.le, h.2.le⟩ hg

/-- π·N(L) − 2·D(L) = π·∫ L·φ。 -/
theorem key_eq {L : ℝ → ℝ} (hL : IntervalIntegrable L MeasureTheory.volume 0 (π / 2)) :
    π * Nint L - 2 * Dint L = π * ∫ γ in (0 : ℝ)..(π / 2), L γ * phi γ := by
  have i1 : IntervalIntegrable (fun γ => L γ * (sin γ * cos γ)) MeasureTheory.volume 0 (π / 2) :=
    hL.mul_continuousOn (by fun_prop)
  have i2 : IntervalIntegrable (fun γ => L γ * cos γ ^ 2) MeasureTheory.volume 0 (π / 2) :=
    hL.mul_continuousOn (by fun_prop)
  have e : (fun γ => L γ * phi γ) = fun γ => L γ * (sin γ * cos γ) - 2 / π * (L γ * cos γ ^ 2) := by
    funext γ; unfold phi; ring
  rw [e, integral_sub i1 (i2.const_mul _), integral_const_mul]
  unfold Nint Dint
  field_simp

/-- 単調な L について ∫ L·φ = ∫ (L − L(γ₀))·φ ≥ 0。 -/
theorem int_L_phi_eq {L : ℝ → ℝ} (hL : IntervalIntegrable L MeasureTheory.volume 0 (π / 2)) :
    ∫ γ in (0 : ℝ)..(π / 2), L γ * phi γ =
      ∫ γ in (0 : ℝ)..(π / 2), (L γ - L γ₀) * phi γ := by
  have i0 : IntervalIntegrable phi MeasureTheory.volume 0 (π / 2) := by
    apply Continuous.intervalIntegrable; unfold phi; fun_prop
  have i1 : IntervalIntegrable (fun γ => L γ * phi γ) MeasureTheory.volume 0 (π / 2) :=
    hL.mul_continuousOn (by unfold phi; fun_prop)
  have e : (fun γ => (L γ - L γ₀) * phi γ) = fun γ => L γ * phi γ - L γ₀ * phi γ := by
    funext γ; ring
  rw [e, integral_sub i1 (i0.const_mul _), integral_const_mul, phi_integral]
  ring

theorem integrand_nonneg {L : ℝ → ℝ} (hmono : MonotoneOn L (Icc 0 (π / 2))) {γ : ℝ}
    (h : γ ∈ Icc 0 (π / 2)) : 0 ≤ (L γ - L γ₀) * phi γ := by
  have hm : γ₀ ∈ Icc 0 (π / 2) := ⟨γ₀_mem.1.le, γ₀_mem.2.le⟩
  rcases le_total γ₀ γ with hg | hg
  · exact mul_nonneg (sub_nonneg.mpr (hmono hm h hg)) (phi_nonneg_of_ge h hg)
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hmono h hm hg)) (phi_nonpos_of_le h hg)

/-- 単調な関数は [0, π/2] で可積分。 -/
theorem mono_integrable {L : ℝ → ℝ} (hmono : MonotoneOn L (Icc 0 (π / 2))) :
    IntervalIntegrable L MeasureTheory.volume 0 (π / 2) := by
  apply MonotoneOn.intervalIntegrable
  rwa [uIcc_of_le (by linarith [pi_pos])]

/-- (2) L が非減少なら 2·D(L) ≤ π·N(L)。 -/
theorem two_le_of_monotone {L : ℝ → ℝ} (hmono : MonotoneOn L (Icc 0 (π / 2))) :
    2 * Dint L ≤ π * Nint L := by
  have hL := mono_integrable hmono
  have := key_eq hL
  rw [int_L_phi_eq hL] at this
  have h0 : 0 ≤ ∫ γ in (0 : ℝ)..(π / 2), (L γ - L γ₀) * phi γ :=
    integral_nonneg (by linarith [pi_pos]) (fun γ hγ => integrand_nonneg hmono hγ)
  have := mul_nonneg pi_pos.le h0
  linarith

/-- (2) L が非増加なら π·N(L) ≤ 2·D(L)。 -/
theorem le_two_of_antitone {L : ℝ → ℝ} (hanti : AntitoneOn L (Icc 0 (π / 2))) :
    π * Nint L ≤ 2 * Dint L := by
  have hm : MonotoneOn (fun γ => -L γ) (Icc 0 (π / 2)) := fun x hx y hy hxy => by
    simp only [neg_le_neg_iff]; exact hanti hx hy hxy
  have h := two_le_of_monotone hm
  unfold Nint Dint at h ⊢
  simp only [neg_mul, integral_neg] at h
  linarith

/-- (2) 非減少で、(0, π/2) の中の二点で値が違えば、真に 2·D(L) < π·N(L)。 -/
theorem two_lt_of_monotone {L : ℝ → ℝ} (hmono : MonotoneOn L (Icc 0 (π / 2)))
    {x y : ℝ} (hx : x ∈ Ioo 0 (π / 2)) (hy : y ∈ Ioo 0 (π / 2)) (hxy : L x < L y) :
    2 * Dint L < π * Nint L := by
  have hL := mono_integrable hmono
  have hk := key_eq hL
  rw [int_L_phi_eq hL] at hk
  have hm : γ₀ ∈ Icc 0 (π / 2) := ⟨γ₀_mem.1.le, γ₀_mem.2.le⟩
  set g := fun γ => (L γ - L γ₀) * phi γ with hg
  have hgi : IntervalIntegrable g MeasureTheory.volume 0 (π / 2) :=
    (hL.sub intervalIntegrable_const).mul_continuousOn (by unfold phi; fun_prop)
  have hpos : 0 < ∫ γ in (0 : ℝ)..(π / 2), g γ := by
    have hpi := pi_pos
    -- L(y) > L(γ₀) か L(x) < L(γ₀) のどちらか
    rcases lt_or_ge (L γ₀) (L y) with h1 | h1
    · -- y > γ₀。[y, π/2] で g ≥ (L y − L γ₀)·φ > 0
      have hyg : γ₀ < y := by
        by_contra hc
        have := hmono ⟨hy.1.le, hy.2.le⟩ hm (le_of_not_gt hc); linarith
      have s1 : IntervalIntegrable g MeasureTheory.volume 0 y :=
        hgi.mono_set (by rw [uIcc_of_le hy.1.le, uIcc_of_le (by linarith)];
                          exact Icc_subset_Icc le_rfl hy.2.le)
      have s2 : IntervalIntegrable g MeasureTheory.volume y (π / 2) :=
        hgi.mono_set (by rw [uIcc_of_le hy.2.le, uIcc_of_le (by linarith)];
                          exact Icc_subset_Icc hy.1.le le_rfl)
      rw [← integral_add_adjacent_intervals s1 s2]
      have a1 : 0 ≤ ∫ γ in (0 : ℝ)..y, g γ :=
        integral_nonneg hy.1.le
          (fun γ hγ => integrand_nonneg hmono ⟨hγ.1, by linarith [hγ.2, hy.2]⟩)
      have a2 : 0 < ∫ γ in y..(π / 2), g γ := by
        apply intervalIntegral_pos_of_pos_on s2 _ hy.2
        intro γ hγ
        have hγ' : γ ∈ Ioo 0 (π / 2) := ⟨by linarith [hγ.1, hy.1], hγ.2⟩
        have hp := phi_pos_of_gt hγ' (by linarith [hγ.1])
        have hLγ : L y ≤ L γ := hmono ⟨hy.1.le, hy.2.le⟩ ⟨hγ'.1.le, hγ'.2.le⟩ hγ.1.le
        simp only [hg]
        exact mul_pos (by linarith) hp
      linarith
    · -- L x < L γ₀、x < γ₀。[0, x] で g > 0
      have h2 : L x < L γ₀ := by linarith
      have hxg : x < γ₀ := by
        by_contra hc
        have := hmono hm ⟨hx.1.le, hx.2.le⟩ (le_of_not_gt hc); linarith
      have s1 : IntervalIntegrable g MeasureTheory.volume 0 x :=
        hgi.mono_set (by rw [uIcc_of_le hx.1.le, uIcc_of_le (by linarith)];
                          exact Icc_subset_Icc le_rfl hx.2.le)
      have s2 : IntervalIntegrable g MeasureTheory.volume x (π / 2) :=
        hgi.mono_set (by rw [uIcc_of_le hx.2.le, uIcc_of_le (by linarith)];
                          exact Icc_subset_Icc hx.1.le le_rfl)
      rw [← integral_add_adjacent_intervals s1 s2]
      have a2 : 0 ≤ ∫ γ in x..(π / 2), g γ :=
        integral_nonneg hx.2.le
          (fun γ hγ => integrand_nonneg hmono ⟨by linarith [hγ.1, hx.1], hγ.2⟩)
      have a1 : 0 < ∫ γ in (0 : ℝ)..x, g γ := by
        apply intervalIntegral_pos_of_pos_on s1 _ hx.1
        intro γ hγ
        have hγ' : γ ∈ Ioo 0 (π / 2) := ⟨hγ.1, by linarith [hγ.2, hx.2]⟩
        have hp := phi_neg_of_lt hγ' (by linarith [hγ.2])
        have hLγ : L γ ≤ L x := hmono ⟨hγ'.1.le, hγ'.2.le⟩ ⟨hx.1.le, hx.2.le⟩ hγ.2.le
        simp only [hg]
        exact mul_pos_of_neg_of_neg (by linarith) hp
      linarith
  have := mul_pos pi_pos hpos
  linarith

/-- (3) 一様な空ではちょうど π·N = 2·D（比 2）。 -/
theorem uniform_sky (c : ℝ) : π * Nint (fun _ => c) = 2 * Dint (fun _ => c) := by
  unfold Nint Dint
  rw [integral_const_mul, integral_const_mul, int_sin_cos, int_cos_sq]
  ring

/-- (3) CIE 標準曇天空 L = (1 + 2 sinγ)/3 では π·N/D = 14π/(3π + 8)。 -/
theorem cie_overcast :
    π * Nint (fun γ => (1 + 2 * sin γ) / 3) / Dint (fun γ => (1 + 2 * sin γ) / 3) =
      14 * π / (3 * π + 8) := by
  have hN : Nint (fun γ => (1 + 2 * sin γ) / 3) = 7 / 18 := by
    unfold Nint
    have e : (fun γ => (1 + 2 * sin γ) / 3 * (sin γ * cos γ)) =
        fun γ => 1 / 3 * (sin γ * cos γ) + 2 / 3 * (sin γ ^ 2 * cos γ) := by funext γ; ring
    rw [e, integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), integral_const_mul, integral_const_mul,
      int_sin_cos, integral_sin_sq_mul_cos]
    simp; norm_num
  have hD : Dint (fun γ => (1 + 2 * sin γ) / 3) = (π / 4 + 2 / 3) / 3 := by
    unfold Dint
    have e : (fun γ => (1 + 2 * sin γ) / 3 * cos γ ^ 2) =
        fun γ => 1 / 3 * cos γ ^ 2 + 2 / 3 * (sin γ * cos γ ^ 2) := by funext γ; ring
    rw [e, integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), integral_const_mul, integral_const_mul,
      int_cos_sq, integral_sin_mul_cos_sq]
    simp; ring
  rw [hN, hD]
  have : 0 < 3 * π + 8 := by positivity
  field_simp
  ring

/-- (4) 直射だけなら、比は sin h/cos h = tan h。 -/
theorem direct_ratio (h : ℝ) : sin h / cos h = tan h := (tan_eq_sin_div_cos h).symm

/-- (4) 0 < h < 90° で、天窓と壁の窓が等しい ⇔ h = 45°。 -/
theorem direct_eq_iff {h : ℝ} (h0 : 0 < h) (h1 : h < π / 2) : tan h = 1 ↔ h = π / 4 := by
  constructor
  · intro ht
    have hm : StrictMonoOn tan (Ioo (-(π / 2)) (π / 2)) := strictMonoOn_tan
    have a : h ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], h1⟩
    have b : π / 4 ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    exact hm.injOn a b (by rw [ht, tan_pi_div_four])
  · intro e; rw [e, tan_pi_div_four]

end Paper587

end Yamagishi
