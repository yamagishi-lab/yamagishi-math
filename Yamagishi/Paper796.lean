/-
論文796『放射平衡そのものは年代を与えず、平衡からのずれだけが時計になる』の格上げ（一般の形）。

日本語の一文：娘と親の放射能の比 R = 1 − e^(−λt) を一定の誤差 σ で測って一次の誤差の伝わり方で年代を
読むと、年代に対する誤差の割合はどの λ・σ でも t = 1/λ でただ一度だけ最小の e·σ をとり、割合が ε 以下で
読める年代は一つの閉じた区間で、それが空でないのは ε ≥ e·σ のときに限る。
English: Reading the age from the activity ratio R = 1 − e^(−λt) measured with a fixed error σ, the
first-order relative age error σ e^(λt)/(λt) has, for every λ and σ, a unique minimum e·σ at
t = 1/λ; the ages readable within a relative error ε form one closed interval, nonempty iff ε ≥ e·σ.

原稿（796_yamagishi_equilibrium_gives_no_age_only_departure_keeps_time/…_jp.tex）は、娘の半減期
75600 年・比の誤差 0.005 の一組で、1・3・5・7 半減期の年代の誤差、最小の時刻 1/λ（半減期の 1.442695 倍）
と最小の割合 0.013591（σ e）、1 割の範囲の上の端 6.491775 半減期を、式と乱数で出している。
1/λ と σ e は式で書いてあるが、最小であることの証明は無い。

ここで証明した言明（λ > 0、σ > 0、t > 0）：
  (1) `age_ratio`：比 R(t) から読む年代 −ln(1 − R)/λ は t に戻る。
      `hasDerivAt_age`：読む年代の R についての微分は 1/(λ(1 − R))（一次の誤差の伝わり方の係数）。
      `relErr_eq`：年代に対する誤差の割合 σ_t/t は σ e^(λt)/(λt)。
  (2) `relErr_ge`：割合はいつも e·σ 以上。`relErr_eq_min_iff`：等号 ⇔ t = 1/λ（位置は σ によらない）。
  (3) `readable_iff`：ε > 0 で、割合 ≤ ε ⇔ σ/ε ≤ λt·e^(−λt)。
      `readable_exists_iff`：割合 ≤ ε で読める年代が在る ⇔ e·σ ≤ ε。
      `readable_interval`：e·σ < ε なら、0 < t₁ < 1/λ < t₂ があって、読める年代の集まりはちょうど
      閉じた区間 [t₁, t₂]（原稿は上の端しか書いていないが、下の端もある）。
      `readable_single`：e·σ = ε なら、読める年代は t = 1/λ の一点だけ。
  (4) `paper_numbers`：1/ln 2 は 1.442695 と 1.442696 のあいだ、e·0.005 は 0.013591 と 0.013592 のあいだ。
足した仮定：はじめに娘が無い・閉じた系・親がずっと長生き（R = 1 − e^(−λt)）と、一次の誤差の伝わり方
σ_t = σ/(λ(1 − R)) を定義として置いた（原稿と同じ）。
形式化していないもの：1 − R が σ に並ぶと一次の式が崩れること（乱数の 1.232339 倍）、上の端
6.491775 半減期の数値、過渡平衡の比、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper796

open Real Set

/-- 娘と親の放射能の比 R(t) = 1 − e^(−λt)。 -/
noncomputable def ratio (lam t : ℝ) : ℝ := 1 - exp (-(lam * t))

/-- 比 R から読む年代 −ln(1 − R)/λ。 -/
noncomputable def age (lam R : ℝ) : ℝ := -log (1 - R) / lam

/-- 一次の誤差の伝わり方による年代の誤差 σ_t = σ/(λ(1 − R))。 -/
noncomputable def sigmaAge (lam σ R : ℝ) : ℝ := σ / (lam * (1 - R))

/-- 年代に対する誤差の割合 σ_t/t。 -/
noncomputable def relErr (lam σ t : ℝ) : ℝ := sigmaAge lam σ (ratio lam t) / t

/-- (1) 比から読む年代は、もとの年代に戻る。 -/
theorem age_ratio {lam : ℝ} (hlam : 0 < lam) (t : ℝ) : age lam (ratio lam t) = t := by
  unfold age ratio
  rw [sub_sub_cancel, log_exp]
  field_simp

/-- (1) 読む年代の微分は 1/(λ(1 − R))。 -/
theorem hasDerivAt_age {lam R : ℝ} (hlam : 0 < lam) (hR : R < 1) :
    HasDerivAt (age lam) (1 / (lam * (1 - R))) R := by
  have h1 : HasDerivAt (fun r : ℝ => 1 - r) (-1) R := (hasDerivAt_id' R).const_sub 1
  have h2 := (h1.log (by linarith)).neg.div_const lam
  unfold age
  convert h2 using 1
  field_simp

/-- (1) 割合は σ e^(λt)/(λt)。 -/
theorem relErr_eq (lam σ t : ℝ) : relErr lam σ t = σ * exp (lam * t) / (lam * t) := by
  unfold relErr sigmaAge ratio
  rw [sub_sub_cancel, exp_neg]
  by_cases h : lam * t = 0
  · have : lam = 0 ∨ t = 0 := mul_eq_zero.mp h
    rcases this with h0 | h0 <;> simp [h0]
  · have ht : t ≠ 0 := right_ne_zero_of_mul h
    have hl : lam ≠ 0 := left_ne_zero_of_mul h
    field_simp

/-- 芯：x > 0 で x ≤ e^(x − 1)、等号は x = 1 だけ。 -/
theorem le_exp_sub_one (x : ℝ) : x ≤ exp (x - 1) := by
  have := add_one_le_exp (x - 1); linarith

theorem lt_exp_sub_one {x : ℝ} (hx : x ≠ 1) : x < exp (x - 1) := by
  have := add_one_lt_exp (x := x - 1) (sub_ne_zero.mpr hx); linarith

/-- e·x ≤ e^x。 -/
theorem e_mul_le_exp (x : ℝ) : exp 1 * x ≤ exp x := by
  have h := le_exp_sub_one x
  have : exp x = exp 1 * exp (x - 1) := by rw [← exp_add]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_left h (exp_pos 1).le

theorem e_mul_lt_exp {x : ℝ} (hx : x ≠ 1) : exp 1 * x < exp x := by
  have h := lt_exp_sub_one hx
  have : exp x = exp 1 * exp (x - 1) := by rw [← exp_add]; ring_nf
  rw [this]
  exact mul_lt_mul_of_pos_left h (exp_pos 1)

/-- (2) 割合はいつも e·σ 以上。 -/
theorem relErr_ge {lam σ t : ℝ} (hlam : 0 < lam) (hσ : 0 < σ) (ht : 0 < t) :
    exp 1 * σ ≤ relErr lam σ t := by
  rw [relErr_eq]
  have hx : 0 < lam * t := mul_pos hlam ht
  rw [le_div_iff₀ hx]
  have := e_mul_le_exp (lam * t)
  nlinarith

/-- (2) 等号は t = 1/λ のときだけ。 -/
theorem relErr_eq_min_iff {lam σ t : ℝ} (hlam : 0 < lam) (hσ : 0 < σ) (ht : 0 < t) :
    relErr lam σ t = exp 1 * σ ↔ t = 1 / lam := by
  rw [relErr_eq]
  have hx : 0 < lam * t := mul_pos hlam ht
  constructor
  · intro h
    by_contra hne
    have h1 : lam * t ≠ 1 := by
      intro h1; apply hne; field_simp; linarith
    have := e_mul_lt_exp h1
    rw [div_eq_iff (ne_of_gt hx)] at h
    nlinarith
  · intro h
    have h1 : lam * t = 1 := by rw [h]; field_simp
    rw [h1]; simp; ring

/-- (3) 割合 ≤ ε ⇔ σ/ε ≤ λt·e^(−λt)。 -/
theorem readable_iff {lam σ ε t : ℝ} (hlam : 0 < lam) (hε : 0 < ε) (ht : 0 < t) :
    relErr lam σ t ≤ ε ↔ σ / ε ≤ lam * t * exp (-(lam * t)) := by
  rw [relErr_eq]
  have hx : 0 < lam * t := mul_pos hlam ht
  rw [div_le_iff₀ hx, div_le_iff₀ hε, exp_neg]
  have he := exp_pos (lam * t)
  constructor
  · intro h
    have : σ ≤ lam * t * ε * (exp (lam * t))⁻¹ := by
      rw [le_mul_inv_iff₀ he]; linarith
    linarith
  · intro h
    have : σ * exp (lam * t) ≤ lam * t * (exp (lam * t))⁻¹ * ε * exp (lam * t) :=
      mul_le_mul_of_nonneg_right h he.le
    rw [show lam * t * (exp (lam * t))⁻¹ * ε * exp (lam * t) = lam * t * ε by field_simp] at this
    linarith

/-! ### f(x) = x e^(−x) の形 -/

/-- f(x) = x e^(−x)。 -/
noncomputable def f (x : ℝ) : ℝ := x * exp (-x)

theorem hasDerivAt_f (x : ℝ) : HasDerivAt f ((1 - x) * exp (-x)) x := by
  have h := (hasDerivAt_id' x).mul ((hasDerivAt_neg x).exp)
  unfold f
  convert h using 1
  ring

theorem f_le (x : ℝ) : f x ≤ exp (-1) := by
  unfold f
  have h := e_mul_le_exp x
  have : x * exp (-x) = (exp 1 * x) * exp (-1) * exp (-x) := by
    rw [mul_comm (exp 1) x, mul_assoc x, ← exp_add]; simp
  rw [this]
  calc exp 1 * x * exp (-1) * exp (-x) ≤ exp x * exp (-1) * exp (-x) := by
        gcongr
    _ = exp (-1) := by rw [mul_comm (exp x), mul_assoc, ← exp_add]; simp

theorem f_lt {x : ℝ} (hx : x ≠ 1) : f x < exp (-1) := by
  unfold f
  have h := e_mul_lt_exp hx
  have : x * exp (-x) = (exp 1 * x) * exp (-1) * exp (-x) := by
    rw [mul_comm (exp 1) x, mul_assoc x, ← exp_add]; simp
  rw [this]
  calc exp 1 * x * exp (-1) * exp (-x) < exp x * exp (-1) * exp (-x) := by
        gcongr
    _ = exp (-1) := by rw [mul_comm (exp x), mul_assoc, ← exp_add]; simp

theorem f_strictMonoOn : StrictMonoOn f (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · exact (continuous_id.mul (continuous_neg.rexp)).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_f x).deriv]
    exact mul_pos (by linarith [hx.2]) (exp_pos _)

theorem f_strictAntiOn : StrictAntiOn f (Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1)
  · exact (continuous_id.mul (continuous_neg.rexp)).continuousOn
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_f x).deriv]
    exact mul_neg_of_neg_of_pos (by linarith [mem_Ioi.mp hx]) (exp_pos _)

theorem f_continuous : Continuous f := continuous_id.mul (continuous_neg.rexp)

/-- 0 < c < 1/e なら、f(x) = c の根が 0 < x₁ < 1 < x₂ に一つずつあり、
x > 0 で c ≤ f(x) ⇔ x₁ ≤ x ≤ x₂。 -/
theorem f_superlevel {c : ℝ} (hc0 : 0 < c) (hc : c < exp (-1)) :
    ∃ x₁ x₂, 0 < x₁ ∧ x₁ < 1 ∧ 1 < x₂ ∧
      ∀ x, 0 < x → (c ≤ f x ↔ x₁ ≤ x ∧ x ≤ x₂) := by
  have f1 : f 1 = exp (-1) := by simp [f]
  have f0 : f 0 = 0 := by simp [f]
  -- [0, 1] での根
  obtain ⟨x₁, hx₁I, hx₁⟩ := intermediate_value_Icc (zero_le_one) f_continuous.continuousOn
    (show c ∈ Icc (f 0) (f 1) by rw [f0, f1]; exact ⟨hc0.le, hc.le⟩)
  have hx₁0 : 0 < x₁ := by
    rcases eq_or_lt_of_le hx₁I.1 with h | h
    · rw [← h, f0] at hx₁; linarith
    · exact h
  have hx₁1 : x₁ < 1 := by
    rcases eq_or_lt_of_le hx₁I.2 with h | h
    · rw [h, f1] at hx₁; linarith
    · exact h
  -- 大きな X で f(X) < c
  set X := 2 / c + 1 with hX
  have hX1 : 1 < X := by have : 0 < 2 / c := by positivity
                         linarith
  have hfX : f X < c := by
    unfold f
    have hX0 : 0 < X := by linarith
    have hq := quadratic_le_exp_of_nonneg hX0.le
    have : X * exp (-X) = X / exp X := by rw [exp_neg]; ring
    rw [this, div_lt_iff₀ (exp_pos X)]
    have : X < c * (1 + X + X ^ 2 / 2) := by
      have hcX : 2 < c * X := by
        rw [hX, mul_add, mul_div_cancel₀ _ (ne_of_gt hc0)]; linarith
      nlinarith
    nlinarith
  obtain ⟨x₂, hx₂I, hx₂⟩ := intermediate_value_Icc' hX1.le f_continuous.continuousOn
    (show c ∈ Icc (f X) (f 1) by rw [f1]; exact ⟨hfX.le, hc.le⟩)
  have hx₂1 : 1 < x₂ := by
    rcases eq_or_lt_of_le hx₂I.1 with h | h
    · rw [← h, f1] at hx₂; linarith
    · exact h
  refine ⟨x₁, x₂, hx₁0, hx₁1, hx₂1, fun x hx => ?_⟩
  constructor
  · intro h
    constructor
    · by_contra hlt
      push Not at hlt
      have : f x < f x₁ := f_strictMonoOn ⟨hx.le, by linarith⟩ ⟨hx₁0.le, hx₁1.le⟩ hlt
      linarith
    · by_contra hlt
      push Not at hlt
      have : f x < f x₂ := f_strictAntiOn (mem_Ici.mpr hx₂1.le)
        (mem_Ici.mpr (by linarith)) hlt
      linarith
  · rintro ⟨h1, h2⟩
    rcases le_total x 1 with hx1 | hx1
    · rw [← hx₁]
      exact f_strictMonoOn.monotoneOn ⟨hx₁0.le, hx₁1.le⟩ ⟨hx.le, hx1⟩ h1
    · rw [← hx₂]
      exact f_strictAntiOn.antitoneOn (mem_Ici.mpr hx1) (mem_Ici.mpr hx₂1.le) h2

/-- (3) 読める年代が在る ⇔ e·σ ≤ ε。 -/
theorem readable_exists_iff {lam σ ε : ℝ} (hlam : 0 < lam) (hσ : 0 < σ) :
    (∃ t, 0 < t ∧ relErr lam σ t ≤ ε) ↔ exp 1 * σ ≤ ε := by
  constructor
  · rintro ⟨t, ht, h⟩
    exact (relErr_ge hlam hσ ht).trans h
  · intro h
    refine ⟨1 / lam, by positivity, ?_⟩
    rw [(relErr_eq_min_iff hlam hσ (by positivity)).mpr rfl]
    exact h

/-- (3) e·σ < ε なら、読める年代は閉じた区間 [t₁, t₂]（0 < t₁ < 1/λ < t₂）。 -/
theorem readable_interval {lam σ ε : ℝ} (hlam : 0 < lam) (hσ : 0 < σ) (hε : 0 < ε)
    (h : exp 1 * σ < ε) :
    ∃ t₁ t₂, 0 < t₁ ∧ t₁ < 1 / lam ∧ 1 / lam < t₂ ∧
      ∀ t, 0 < t → (relErr lam σ t ≤ ε ↔ t₁ ≤ t ∧ t ≤ t₂) := by
  have hc0 : 0 < σ / ε := div_pos hσ hε
  have hc : σ / ε < exp (-1) := by
    rw [div_lt_iff₀ hε, exp_neg]
    have he := exp_pos 1
    rw [inv_mul_eq_div, lt_div_iff₀ he]; linarith
  obtain ⟨x₁, x₂, hx₁0, hx₁1, hx₂1, hiff⟩ := f_superlevel hc0 hc
  refine ⟨x₁ / lam, x₂ / lam, div_pos hx₁0 hlam, div_lt_div_of_pos_right hx₁1 hlam,
    div_lt_div_of_pos_right hx₂1 hlam, fun t ht => ?_⟩
  rw [readable_iff hlam hε ht]
  have := hiff (lam * t) (mul_pos hlam ht)
  unfold f at this
  rw [this, div_le_iff₀ hlam, le_div_iff₀ hlam, mul_comm t lam]

/-- (3) e·σ = ε なら、読める年代は t = 1/λ だけ。 -/
theorem readable_single {lam σ ε t : ℝ} (hlam : 0 < lam) (hσ : 0 < σ) (ht : 0 < t)
    (h : exp 1 * σ = ε) : relErr lam σ t ≤ ε ↔ t = 1 / lam := by
  rw [← h]
  constructor
  · intro hle
    exact (relErr_eq_min_iff hlam hσ ht).mp (le_antisymm hle (relErr_ge hlam hσ ht))
  · intro he
    exact ((relErr_eq_min_iff hlam hσ ht).mpr he).le

/-- (4) 原稿の数：最小の時刻は半減期の 1/ln 2 倍（1.442695 と 1.442696 のあいだ）、
最小の割合 e·0.005 は 0.013591 と 0.013592 のあいだ。 -/
theorem paper_numbers :
    (1.442695 : ℝ) < 1 / log 2 ∧ 1 / log 2 < 1.442696 ∧
      (0.013591 : ℝ) < exp 1 * 0.005 ∧ exp 1 * 0.005 < 0.013592 := by
  have h1 := log_two_gt_d9
  have h2 := log_two_lt_d9
  have h3 := exp_one_gt_d9
  have h4 := exp_one_lt_d9
  have hl : 0 < log 2 := by linarith
  refine ⟨?_, ?_, by linarith, by linarith⟩
  · rw [lt_div_iff₀ hl]; nlinarith
  · rw [div_lt_iff₀ hl]; nlinarith


end Paper796

end Yamagishi
