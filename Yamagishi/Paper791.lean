/-
論文791『腕が届く仕方は 0・1・2 通りか、幅になる』の格上げ（一般の形）。

原稿（791_yamagishi_an_arm_reaches_in_zero_one_two_ways_or_a_range/…_jp.tex）は、長さ L₁ = 0.5・
L₂ = 0.3 の平面の二関節の腕で、根元から距離 r = 0.1・0.2・0.5・0.8・0.9 の目標に届く関節の角度の
組の数を、余弦定理の式とニュートン法で数え（2・1・2・1・0 通り）、外縁の近くで関節の速さが大きく
なることを数値で見ている。

ここで証明した言明（L₁, L₂ > 0、目標 z ∈ ℂ、r = |z| > 0、角度は (−π, π] で数える）：
  手先の位置 L₁e^(iθ₁) + L₂e^(i(θ₁+θ₂)) = z となる組 (θ₁, θ₂) の数は
  (1) `count_two`：|L₁ − L₂| < r < L₁ + L₂ なら 2。
  (2) `count_one_outer`：r = L₁ + L₂ なら 1。`count_one_inner`：r = |L₁ − L₂|（> 0）なら 1。
  (3) `count_zero`：r > L₁ + L₂ または r < |L₁ − L₂| なら 0。
  あわせて `reach_area`：届く範囲（円環）の面積 π((L₁+L₂)² − (L₁−L₂)²) = 4πL₁L₂。
証明の筋：手先は e^(iθ₁)(L₁ + L₂e^(iθ₂)) と書け、|L₁ + L₂e^(iθ₂)|² = L₁² + L₂² + 2L₁L₂cos θ₂
（`norm_sq_elbow`）。よって θ₂ は cos θ₂ = (r² − L₁² − L₂²)/(2L₁L₂) の解で、各 θ₂ に θ₁ が
ただ一つ決まる（`shoulder_unique`）。cos θ = c の (−π, π] の解は |c| < 1 で 2 個、|c| = 1 で 1 個、
|c| > 1 で 0 個（`cos_count_two` など）。
差：r = 0（L₁ = L₂ のときだけ届く）では θ₁ が任意になり、数は無限（下読みの AI の注意のとおり）。
ここでは r > 0 を仮定した。
形式化していないもの：外縁に近づくと関節の速さが縁までの距離の −1/2 乗で発散すること、三関節以上の
解の集まりの形、関節の可動域。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper791

open Complex Set

local notation "π" => Real.pi

/-- 手先の位置。 -/
noncomputable def hand (L1 L2 θ1 θ2 : ℝ) : ℂ :=
  L1 * exp (θ1 * I) + L2 * exp ((θ1 + θ2) * I)

/-- 届く組の集まり（角度は (−π, π]）。 -/
def sols (L1 L2 : ℝ) (z : ℂ) : Set (ℝ × ℝ) :=
  {q | q.1 ∈ Ioc (-π) π ∧ q.2 ∈ Ioc (-π) π ∧ hand L1 L2 q.1 q.2 = z}

/-- 肘の角度の集まり：cos θ₂ = c。 -/
def elbows (c : ℝ) : Set ℝ := {θ | θ ∈ Ioc (-π) π ∧ Real.cos θ = c}

theorem hand_eq (L1 L2 θ1 θ2 : ℝ) :
    hand L1 L2 θ1 θ2 = exp (θ1 * I) * (L1 + L2 * exp (θ2 * I)) := by
  unfold hand
  rw [show ((θ1 : ℂ) + θ2) * I = θ1 * I + θ2 * I by ring, Complex.exp_add]
  ring

theorem norm_sq_elbow (L1 L2 θ : ℝ) :
    ‖(L1 : ℂ) + L2 * exp (θ * I)‖ ^ 2 = L1 ^ 2 + L2 ^ 2 + 2 * L1 * L2 * Real.cos θ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero, zero_add]
  nlinarith [Real.cos_sq_add_sin_sq θ]

theorem exp_inj {a b : ℝ} (ha : a ∈ Ioc (-π) π) (hb : b ∈ Ioc (-π) π)
    (h : exp (a * I) = exp (b * I)) : a = b := by
  have e1 := arg_cos_add_sin_mul_I ha
  have e2 := arg_cos_add_sin_mul_I hb
  rw [← e1, ← e2, ← exp_mul_I, ← exp_mul_I, h]

/-- 肘が決まれば、肩の角度は (−π, π] にただ一つ。 -/
theorem shoulder_unique {w z : ℂ} (hw : w ≠ 0) (hn : ‖w‖ = ‖z‖) :
    ∃! θ1, θ1 ∈ Ioc (-π) π ∧ exp (θ1 * I) * w = z := by
  have hz : z ≠ 0 := by
    intro h; rw [h, norm_zero, norm_eq_zero] at hn; exact hw hn
  set u := z / w
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_div, hn]; exact div_self (norm_ne_zero_iff.mpr hz)
  have hex : exp (arg u * I) = u := by
    have := norm_mul_exp_arg_mul_I u
    rwa [hu, ofReal_one, one_mul] at this
  refine ⟨arg u, ⟨⟨neg_pi_lt_arg u, arg_le_pi u⟩, ?_⟩, ?_⟩
  · rw [hex]; simp only [u]; field_simp
  · rintro θ ⟨hθ, he⟩
    apply exp_inj hθ ⟨neg_pi_lt_arg u, arg_le_pi u⟩
    rw [hex]; simp only [u]; rw [← he]; field_simp

/-- 組の数 = 肘の角度の数。 -/
theorem ncard_sols {L1 L2 : ℝ} (h1 : 0 < L1) (h2 : 0 < L2) {z : ℂ} (hz : 0 < ‖z‖) :
    (sols L1 L2 z).ncard = (elbows ((‖z‖ ^ 2 - L1 ^ 2 - L2 ^ 2) / (2 * L1 * L2))).ncard := by
  set c := (‖z‖ ^ 2 - L1 ^ 2 - L2 ^ 2) / (2 * L1 * L2)
  have hc : ∀ θ, Real.cos θ = c ↔ ‖(L1 : ℂ) + L2 * exp (θ * I)‖ = ‖z‖ := by
    intro θ
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_elbow]
    simp only [c]
    constructor
    · intro h; rw [h]; field_simp; ring
    · intro h; field_simp; linarith
  apply Set.ncard_congr (fun q _ => q.2)
  · rintro ⟨θ1, θ2⟩ ⟨_, hθ2, he⟩
    refine ⟨hθ2, (hc θ2).mpr ?_⟩
    rw [← he, hand_eq, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  · rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨ha1, ha2, hea⟩ ⟨hb1, hb2, heb⟩ h
    simp only at h
    subst h
    have hw : (L1 : ℂ) + L2 * exp (a2 * I) ≠ 0 := by
      intro h0
      have : ‖z‖ = 0 := by rw [← hea, hand_eq, h0, mul_zero, norm_zero]
      linarith
    have hn : ‖(L1 : ℂ) + L2 * exp (a2 * I)‖ = ‖z‖ := by
      rw [← hea, hand_eq, norm_mul, norm_exp_ofReal_mul_I, one_mul]
    obtain ⟨θ, _, huniq⟩ := shoulder_unique hw hn
    have e1 := huniq a1 ⟨ha1, by rw [← hand_eq]; exact hea⟩
    have e2 := huniq b1 ⟨hb1, by rw [← hand_eq]; exact heb⟩
    rw [e1, e2]
  · rintro θ2 ⟨hθ2, hcos⟩
    have hn := (hc θ2).mp hcos
    have hw : (L1 : ℂ) + L2 * exp (θ2 * I) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hn; linarith
    obtain ⟨θ1, ⟨hθ1, he⟩, _⟩ := shoulder_unique hw hn
    exact ⟨(θ1, θ2), ⟨hθ1, hθ2, by rw [hand_eq]; exact he⟩, rfl⟩

/-! ## cos θ = c の (−π, π] の解の数 -/

theorem cos_count_two {c : ℝ} (h1 : -1 < c) (h2 : c < 1) : (elbows c).ncard = 2 := by
  have ha0 : 0 < Real.arccos c := Real.arccos_pos.mpr h2
  have haπ : Real.arccos c < π := Real.arccos_lt_pi.mpr h1
  have : elbows c = {Real.arccos c, -Real.arccos c} := by
    ext θ
    simp only [elbows, mem_ofPred_eq, mem_Ioc, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hl, hr⟩, hcos⟩
      rcases le_total 0 θ with h | h
      · left; rw [← hcos, Real.arccos_cos h hr]
      · right
        have : Real.arccos (Real.cos (-θ)) = -θ := Real.arccos_cos (by linarith) (by linarith)
        rw [Real.cos_neg, hcos] at this; linarith
    · rintro (rfl | rfl)
      · exact ⟨⟨by linarith, haπ.le⟩, Real.cos_arccos h1.le h2.le⟩
      · exact ⟨⟨by linarith, by linarith⟩, by rw [Real.cos_neg, Real.cos_arccos h1.le h2.le]⟩
  rw [this, Set.ncard_pair (by linarith)]

theorem cos_count_one_top : (elbows 1).ncard = 1 := by
  have : elbows 1 = {0} := by
    ext θ
    simp only [elbows, mem_ofPred_eq, mem_Ioc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hl, hr⟩, hcos⟩
      rcases le_total 0 θ with h | h
      · have := Real.arccos_cos h hr; rw [hcos, Real.arccos_one] at this; linarith
      · have := Real.arccos_cos (show 0 ≤ -θ by linarith) (by linarith)
        rw [Real.cos_neg, hcos, Real.arccos_one] at this; linarith
    · rintro rfl; exact ⟨⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩, Real.cos_zero⟩
  rw [this, Set.ncard_singleton]

theorem cos_count_one_bot : (elbows (-1)).ncard = 1 := by
  have : elbows (-1) = {π} := by
    ext θ
    simp only [elbows, mem_ofPred_eq, mem_Ioc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hl, hr⟩, hcos⟩
      rcases le_total 0 θ with h | h
      · have := Real.arccos_cos h hr; rw [hcos, Real.arccos_neg_one] at this; linarith
      · have := Real.arccos_cos (show 0 ≤ -θ by linarith) (by linarith)
        rw [Real.cos_neg, hcos, Real.arccos_neg_one] at this; linarith
    · rintro rfl; exact ⟨⟨by linarith [Real.pi_pos], le_rfl⟩, Real.cos_pi⟩
  rw [this, Set.ncard_singleton]

theorem cos_count_zero {c : ℝ} (h : 1 < |c|) : (elbows c).ncard = 0 := by
  have : elbows c = ∅ := by
    ext θ
    simp only [elbows, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro _ hcos
    have := Real.abs_cos_le_one θ
    rw [hcos] at this; linarith
  rw [this, Set.ncard_empty]

/-! ## まとめ：r で場合分け -/

section

variable {L1 L2 : ℝ} (h1 : 0 < L1) (h2 : 0 < L2) {z : ℂ} (hz : 0 < ‖z‖)
include h1 h2 hz

/-- (1) |L₁ − L₂| < r < L₁ + L₂ なら 2 通り。 -/
theorem count_two (hlo : |L1 - L2| < ‖z‖) (hhi : ‖z‖ < L1 + L2) : (sols L1 L2 z).ncard = 2 := by
  rw [ncard_sols h1 h2 hz]
  have hd : 0 < 2 * L1 * L2 := by positivity
  apply cos_count_two
  · rw [lt_div_iff₀ hd]
    have hsq : (L1 - L2) ^ 2 < ‖z‖ ^ 2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ hlo (abs_nonneg _) (by norm_num)
    nlinarith
  · rw [div_lt_one hd]
    have : ‖z‖ ^ 2 < (L1 + L2) ^ 2 := pow_lt_pow_left₀ hhi hz.le (by norm_num)
    nlinarith

/-- (2) r = L₁ + L₂ なら 1 通り。 -/
theorem count_one_outer (h : ‖z‖ = L1 + L2) : (sols L1 L2 z).ncard = 1 := by
  rw [ncard_sols h1 h2 hz, h]
  have : ((L1 + L2) ^ 2 - L1 ^ 2 - L2 ^ 2) / (2 * L1 * L2) = 1 := by
    field_simp; ring
  rw [this]; exact cos_count_one_top

/-- (2) r = |L₁ − L₂|（> 0）なら 1 通り。 -/
theorem count_one_inner (h : ‖z‖ = |L1 - L2|) : (sols L1 L2 z).ncard = 1 := by
  rw [ncard_sols h1 h2 hz, h, sq_abs]
  have : ((L1 - L2) ^ 2 - L1 ^ 2 - L2 ^ 2) / (2 * L1 * L2) = -1 := by
    field_simp; ring
  rw [this]; exact cos_count_one_bot

/-- (3) r > L₁ + L₂ または r < |L₁ − L₂| なら 0 通り。 -/
theorem count_zero (h : L1 + L2 < ‖z‖ ∨ ‖z‖ < |L1 - L2|) : (sols L1 L2 z).ncard = 0 := by
  rw [ncard_sols h1 h2 hz]
  have hd : 0 < 2 * L1 * L2 := by positivity
  apply cos_count_zero
  rcases h with h | h
  · have : (L1 + L2) ^ 2 < ‖z‖ ^ 2 := pow_lt_pow_left₀ h (by positivity) (by norm_num)
    have hc : 1 < (‖z‖ ^ 2 - L1 ^ 2 - L2 ^ 2) / (2 * L1 * L2) := by
      rw [lt_div_iff₀ hd]; nlinarith
    exact lt_of_lt_of_le hc (le_abs_self _)
  · have : ‖z‖ ^ 2 < (L1 - L2) ^ 2 := by
      rw [← sq_abs (L1 - L2)]; exact pow_lt_pow_left₀ h hz.le (by norm_num)
    have hc : (‖z‖ ^ 2 - L1 ^ 2 - L2 ^ 2) / (2 * L1 * L2) < -1 := by
      rw [div_lt_iff₀ hd]; nlinarith
    rw [abs_of_neg (by linarith)]; linarith

end

/-- 届く範囲（円環）の面積 = 4πL₁L₂。 -/
theorem reach_area (L1 L2 : ℝ) : π * ((L1 + L2) ^ 2 - (L1 - L2) ^ 2) = 4 * π * L1 * L2 := by
  ring

end Paper791

end Yamagishi
