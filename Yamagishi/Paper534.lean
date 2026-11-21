/-
論文534『最初の絶対温度は対数目盛であり、そこでは絶対零度が定義から到達不能だった』の格上げ（一般の形）。

原稿（534_yamagishi_the_first_scale_was_logarithmic/…_jp.tex）は、1848 年の要求「熱の単位が θ から
θ − 1 へ落ちるとき、θ によらず同じ仕事を与える」から目盛 θ(T) = A ln(T/273.15)、
A = 100/ln(373.15/273.15) が出ると一行で述べ（計算 2.1）、T = 1000, 300, 30, 3 で一度下がる仕事が
0.0031147330 で一定であることを数で示している。要求からこの形しか出ないことは示していない。

ここで証明した言明（目盛 θ ↦ 絶対温度 τ(θ) を、実数全体の上の正で狭義に増える関数とする）：
  (1) `log_scale_unique`：どの刻み δ > 0 でもカルノーの仕事 1 − τ(θ − δ)/τ(θ) が θ によらず、
      τ(0) = 273.15、τ(100) = 373.15 なら、すべての θ で θ = A ln(τ(θ)/273.15)。
  (2) `log_scale_work`：逆に対数目盛では、刻み δ の仕事は 1 − e^(−δ/A) で、θ によらない。
  (3) `one_step_not_enough`：刻み δ = 1 だけを要求すると一意でない。
      τ₁(θ) = 273.15·exp(θ/A + sin(2πθ)/(4πA)) は正・狭義に増加・二つの定点を通り、
      一刻みの仕事は θ によらないが、対数目盛ではない（θ = 1/4 で食い違う）。
  部品 `additive_monotone_linear`：実数上の加法的で単調な関数は一次関数（コーシーの関数方程式）。
足した仮定：目盛 θ が実数全体を動くこと（対数目盛では絶対零度が −∞ にあり、θ は実数全体を動く）。
形式化していないもの：カルノーの理論そのもの（仕事の式 1 − T′/T は定義に置いた）、到達不能の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper534

open Real

/-- 目盛の定数 A = 100/ln(373.15/273.15)。 -/
noncomputable def A : ℝ := 100 / log (373.15 / 273.15)

/-- 熱の単位が θ から θ − δ へ落ちるときのカルノーの仕事（熱の単位あたり）。 -/
noncomputable def work (τ : ℝ → ℝ) (θ δ : ℝ) : ℝ := 1 - τ (θ - δ) / τ θ

theorem log_ratio_pos : 0 < log (373.15 / 273.15 : ℝ) := log_pos (by norm_num)

theorem A_pos : 0 < A := div_pos (by norm_num) log_ratio_pos

/-- 部品：加法的で単調な関数は一次関数。 -/
theorem additive_monotone_linear {φ : ℝ → ℝ} (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hmono : Monotone φ) (x : ℝ) : φ x = φ 1 * x := by
  let f : ℝ →+ ℝ := ⟨⟨φ, by simpa using hadd 0 0⟩, hadd⟩
  have hq : ∀ q : ℚ, φ q = φ 1 * q := by
    intro q
    have := map_ratCast_smul f ℝ ℝ q 1
    simpa [f, mul_comm] using this
  have h0 : φ 0 = 0 := by simpa using hadd 0 0
  have hk : 0 ≤ φ 1 := by rw [← h0]; exact hmono zero_le_one
  apply le_antisymm
  · -- φ x ≤ k x
    by_contra hc
    push Not at hc
    rcases eq_or_lt_of_le hk with hk0 | hk0
    · obtain ⟨q, hq1⟩ := exists_rat_gt x
      have := hmono hq1.le
      rw [hq, ← hk0] at this
      rw [← hk0] at hc
      linarith
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < φ x / φ 1 by
        rw [lt_div_iff₀ hk0]; linarith)
      have := hmono hq1.le
      rw [hq] at this
      rw [lt_div_iff₀ hk0] at hq2
      linarith
  · by_contra hc
    push Not at hc
    rcases eq_or_lt_of_le hk with hk0 | hk0
    · obtain ⟨q, hq1⟩ := exists_rat_lt x
      have := hmono hq1.le
      rw [hq, ← hk0] at this
      rw [← hk0] at hc
      linarith
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show φ x / φ 1 < x by
        rw [div_lt_iff₀ hk0]; linarith)
      have := hmono hq2.le
      rw [hq] at this
      rw [div_lt_iff₀ hk0] at hq1
      linarith

/-- (1) どの刻みでも仕事が θ によらないなら、対数目盛に限る。 -/
theorem log_scale_unique {τ : ℝ → ℝ} (hpos : ∀ θ, 0 < τ θ) (hmono : StrictMono τ)
    (hreq : ∀ δ > 0, ∀ θ₁ θ₂, work τ θ₁ δ = work τ θ₂ δ)
    (h0 : τ 0 = 273.15) (h100 : τ 100 = 373.15) :
    ∀ θ, θ = A * log (τ θ / 273.15) := by
  set ψ : ℝ → ℝ := fun θ => log (τ θ) with hψ
  -- ψ(θ) − ψ(θ − δ) = ψ(δ) − ψ(0)
  have hstep : ∀ δ > 0, ∀ θ, ψ θ - ψ (θ - δ) = ψ δ - ψ 0 := by
    intro δ hδ θ
    have h := hreq δ hδ θ δ
    simp only [work, sub_self] at h
    have h' : τ (θ - δ) / τ θ = τ 0 / τ δ := by linarith
    simp only [hψ]
    rw [← log_div (hpos θ).ne' (hpos _).ne', ← log_div (hpos δ).ne' (hpos 0).ne']
    congr 1
    have := hpos θ; have := hpos δ; have := hpos (θ - δ); have := hpos 0
    field_simp at h' ⊢
    linarith
  set φ : ℝ → ℝ := fun x => ψ x - ψ 0 with hφ
  have hneg : ∀ δ > 0, φ (-δ) = -φ δ := by
    intro δ hδ
    have := hstep δ hδ 0
    simp only [hφ, zero_sub] at this ⊢
    linarith
  have hadd : ∀ x y, φ (x + y) = φ x + φ y := by
    intro x y
    rcases lt_trichotomy y 0 with hy | hy | hy
    · have := hstep (-y) (by linarith) x
      have h2 := hneg (-y) (by linarith)
      simp only [neg_neg] at h2
      simp only [hφ, sub_neg_eq_add] at this h2 ⊢
      linarith
    · subst hy; simp [hφ]
    · have := hstep y hy (x + y)
      simp only [hφ, add_sub_cancel_right] at this ⊢
      linarith
  have hφmono : Monotone φ := by
    intro a b hab
    simp only [hφ]
    have : log (τ a) ≤ log (τ b) := log_le_log (hpos a) (hmono.monotone hab)
    simp only [hψ]; linarith
  have hlin := additive_monotone_linear hadd hφmono
  set k := φ 1
  -- ψ θ = ψ 0 + kθ、ψ 100 − ψ 0 = ln(373.15/273.15)
  have hk100 : k * 100 = log (373.15 / 273.15) := by
    have := hlin 100
    simp only [hφ, hψ, h0, h100] at this
    rw [log_div (by norm_num) (by norm_num)]
    linarith
  intro θ
  have hθ := hlin θ
  simp only [hφ, hψ, h0] at hθ
  have hlog : log (τ θ / 273.15) = k * θ := by
    rw [log_div (hpos θ).ne' (by norm_num)]; linarith
  rw [hlog, A]
  have hL := log_ratio_pos
  rw [← hk100]
  have hkpos : 0 < k := by nlinarith
  field_simp

/-- 対数目盛 τ(θ) = 273.15·e^(θ/A)。 -/
noncomputable def logScale (θ : ℝ) : ℝ := 273.15 * exp (θ / A)

/-- (2) 対数目盛では、刻み δ の仕事は 1 − e^(−δ/A) で θ によらない。 -/
theorem log_scale_work (θ δ : ℝ) : work logScale θ δ = 1 - exp (-(δ / A)) := by
  unfold work logScale
  congr 1
  rw [mul_div_mul_left _ _ (by norm_num), ← exp_sub]
  congr 1
  ring

theorem logScale_fixed : logScale 0 = 273.15 ∧ logScale 100 = 373.15 := by
  constructor
  · simp [logScale]
  · unfold logScale
    rw [show (100 : ℝ) / A = log (373.15 / 273.15) by
      rw [A]; field_simp [log_ratio_pos.ne'], exp_log (by norm_num)]
    norm_num

/-- 一刻みだけを満たす別の目盛 τ₁。 -/
noncomputable def τ₁ (θ : ℝ) : ℝ := 273.15 * exp (θ / A + sin (2 * π * θ) / (4 * π * A))

theorem hasDerivAt_exponent (θ : ℝ) :
    HasDerivAt (fun θ => θ / A + sin (2 * π * θ) / (4 * π * A))
      (1 / A + cos (2 * π * θ) * (2 * π) / (4 * π * A)) θ := by
  have h1 := (hasDerivAt_id θ).div_const A
  have h2 := (((hasDerivAt_id θ).const_mul (2 * π)).sin).div_const (4 * π * A)
  convert h1.add h2 using 1
  · funext x; simp
  · simp

/-- (3) 一刻みの要求だけでは目盛は決まらない。 -/
theorem one_step_not_enough :
    (∀ θ, 0 < τ₁ θ) ∧ StrictMono τ₁ ∧ τ₁ 0 = 273.15 ∧ τ₁ 100 = 373.15 ∧
      (∀ θ₁ θ₂, work τ₁ θ₁ 1 = work τ₁ θ₂ 1) ∧ τ₁ (1 / 4) ≠ logScale (1 / 4) := by
  have hA := A_pos
  have hπ := pi_pos
  refine ⟨fun θ => by unfold τ₁; positivity, ?_, ?_, ?_, ?_, ?_⟩
  · -- 指数の部分が狭義に増える
    have hmono : StrictMono (fun θ => θ / A + sin (2 * π * θ) / (4 * π * A)) := by
      apply strictMono_of_deriv_pos
      intro x
      rw [(hasDerivAt_exponent x).deriv]
      have hc := neg_one_le_cos (2 * π * x)
      have : cos (2 * π * x) * (2 * π) / (4 * π * A) = cos (2 * π * x) / (2 * A) := by
        field_simp; ring
      rw [this]
      have : 1 / A + cos (2 * π * x) / (2 * A) = (2 + cos (2 * π * x)) / (2 * A) := by
        field_simp
      rw [this]
      apply div_pos (by linarith) (by positivity)
    intro a b hab
    unfold τ₁
    have := exp_lt_exp.2 (hmono hab)
    nlinarith
  · simp [τ₁]
  · unfold τ₁
    have hs : sin (2 * π * 100) = 0 := by
      rw [show 2 * π * 100 = ((200 : ℕ) : ℝ) * π by push_cast; ring]
      exact sin_nat_mul_pi 200
    rw [hs, zero_div, add_zero, show (100 : ℝ) / A = log (373.15 / 273.15) by
      rw [A]; field_simp [log_ratio_pos.ne'], exp_log (by norm_num)]
    norm_num
  · intro θ₁ θ₂
    have key : ∀ θ, τ₁ (θ - 1) / τ₁ θ = exp (-(1 / A)) := by
      intro θ
      unfold τ₁
      have hs : sin (2 * π * (θ - 1)) = sin (2 * π * θ) := by
        rw [show 2 * π * (θ - 1) = 2 * π * θ - 2 * π by ring, sin_sub_two_pi]
      rw [hs, mul_div_mul_left _ _ (by norm_num), ← exp_sub]
      congr 1
      ring
    simp only [work, key]
  · unfold τ₁ logScale
    intro h
    have h' := mul_left_cancel₀ (by norm_num : (273.15 : ℝ) ≠ 0) h
    have := exp_injective h'
    rw [show 2 * π * (1 / 4) = π / 2 by ring, sin_pi_div_two] at this
    have : 1 / (4 * π * A) = 0 := by linarith
    have : 0 < 1 / (4 * π * A) := by positivity
    linarith

end Paper534

end Yamagishi
