/-
論文1081『球の断面積は πa² の 1・2・4・8 倍の四つあり、4 が出るのは 3 次元だけである』の格上げ（芯だけ）。

日本語の一文：d 次元の固い球の長い波長の断面積は、s 波の位相のずれの漸近と高い部分波が劣ることを
入力に置くと σ_d(k) ≈ C_d·S_{d−1}·a^(2d−4)·k^(d−3)、C_d = π/(2^(d−3)Γ((d−2)/2)²) になり、
k → 0 で有限の 0 でない値に落ち着くのは d = 3 だけで、その値は 4πa² である。
English: Core only: taking as input the s-wave threshold law sin²δ₀ ~ A k^(2d−4),
A = (π(a/2)^(d−2)/(Γ(ν)Γ(ν+1)))², ν = (d − 2)/2, and that higher partial waves are negligible,
the d-dimensional hard-sphere cross section satisfies σ_d(k)/k^(d−3) → C_d S_{d−1} a^(2d−4) with
C_d = π/(2^(d−3)Γ(ν)²) (C₃ = 1, C₄ = π/2, C₅ = 1, C₆ = π/8); a finite nonzero long-wavelength limit
occurs only for d = 3, where it is 4πa², and identical bosons give twice the distinguishable value.

原稿（1081_yamagishi_hard_sphere_four_cross_sections_and_the_four_only_in_three_dimensions/…_jp.tex）は、
d = 2〜6 で ka = 0.1・0.01・0.001 の部分波の和の数値から冪 d − 3 と 4 次元の係数 π/2 を測り、
「波長によらない数に落ち着くのは 3 次元だけ」と数値で述べる。C_d の閉じた形は無い。

ここで証明した言明（d は 3 以上の自然数、a > 0）：
  (1) `coeff_identity`：部分波の式の前の因子 4(2π)^(d−1)/S_{d−1} と s 波の係数 A の積は
      C_d·S_{d−1}·a^(2d−4)（S_{d−1} = 2√π^d/Γ(d/2) を使うガンマ関数の恒等式）。
  (2) `core_limit`：入力 (i) sin²δ₀(k)/(A k^(2d−4)) → 1、(ii) 高い部分波の和 ÷ sin²δ₀ → 0（k → 0⁺）から、
      σ_d(k)/k^(d−3) → C_d·S_{d−1}·a^(2d−4)。
  (3) `limit_three`：d = 3 では σ → 4πa²（C₃ = 1、S₂ = 4π）。`limit_high`：d ≥ 4 では σ → 0。
      `finite_nonzero_iff`：σ が 0 でない有限の値に近づく ⇔ d = 3。
  (4) `C_values`：C₃ = 1、C₄ = π/2、C₅ = 1、C₆ = π/8。`degeneracy_zero`：N(d, 0) = 1。
  (5) `bose_ratio`：同種のボース粒子（偶数の l だけが 2 倍で残る）の断面積 ÷ 区別できる粒の断面積 → 2。
足した仮定（ここが「芯だけ」の理由）：Mathlib にベッセル関数 J_ν、Y_ν の小さい引数の漸近が無いので、
s 波の位相のずれの漸近 sin²δ₀ ~ (π(ka/2)^(2ν)/(Γ(ν)Γ(ν+1)))² と、高い部分波の和が sin²δ₀ に比べて
劣ること（部分波の和の尾の一様な押さえ）を、名指しの仮定として置いた。d 次元の部分波の式
σ = 4(2π)^(d−1)/(S_{d−1}k^(d−1))·Σ N(d, l) sin²δ_l は原稿のとおり定義として置いた。
形式化していないもの：d = 2 の対数の場合、短い波長の 2πa²（影の散乱）、数値の部分波の和、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1081

open Real Filter Topology

/-- ℝ^d の単位球面の面積 S_{d−1} = 2√π^d/Γ(d/2)。 -/
noncomputable def Sph (d : ℕ) : ℝ := 2 * √π ^ d / Gamma (d / 2)

/-- ν = (d − 2)/2。 -/
noncomputable def ν (d : ℕ) : ℝ := ((d : ℝ) - 2) / 2

/-- s 波の係数 A = (π(a/2)^(d−2)/(Γ(ν)Γ(ν + 1)))²。 -/
noncomputable def A (d : ℕ) (a : ℝ) : ℝ :=
  (π * (a / 2) ^ (d - 2) / (Gamma (ν d) * Gamma (ν d + 1))) ^ 2

/-- C_d = π/(2^(d−3)Γ(ν)²)。 -/
noncomputable def C (d : ℕ) : ℝ := π / (2 ^ (d - 3) * Gamma (ν d) ^ 2)

/-- 部分波の式の前の因子 4(2π)^(d−1)/(S_{d−1}k^(d−1))。 -/
noncomputable def pref (d : ℕ) (k : ℝ) : ℝ := 4 * (2 * π) ^ (d - 1) / (Sph d * k ^ (d - 1))

/-- 角運動量 l の状態の数 N(d, l) = (2l + d − 2)(l + d − 3)!/(l!(d − 2)!)。 -/
def N (d l : ℕ) : ℚ :=
  (2 * l + d - 2 : ℚ) * (l + d - 3).factorial / (l.factorial * (d - 2).factorial)

theorem degeneracy_zero {d : ℕ} (hd : 3 ≤ d) : N d 0 = 1 := by
  unfold N
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
  simp only [Nat.cast_zero, mul_zero, zero_add, Nat.factorial_zero, Nat.cast_one, one_mul,
    show m + 3 - 3 = m from by omega, show m + 3 - 2 = m + 1 from by omega,
    Nat.factorial_succ]
  push_cast
  have : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem ν_pos {d : ℕ} (hd : 3 ≤ d) : 0 < ν d := by
  unfold ν
  have : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

theorem Sph_pos (d : ℕ) (hd : 3 ≤ d) : 0 < Sph d := by
  unfold Sph
  have : (0 : ℝ) < d / 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have := Gamma_pos_of_pos this
  have := sqrt_pos.mpr pi_pos
  positivity

/-- (1) 前の因子と s 波の係数の積は C_d·S_{d−1}·a^(2d−4)。 -/
theorem coeff_identity {d : ℕ} (hd : 3 ≤ d) (a : ℝ) :
    4 * (2 * π) ^ (d - 1) / Sph d * A d a = C d * Sph d * a ^ (2 * d - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
  have hν : ν (m + 3) + 1 = ((m + 3 : ℕ) : ℝ) / 2 := by unfold ν; push_cast; ring
  have hG1 : 0 < Gamma (ν (m + 3)) := Gamma_pos_of_pos (ν_pos (by omega))
  have hG2 : 0 < Gamma (((m + 3 : ℕ) : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  have hs := sqrt_pos.mpr pi_pos
  have hsq : √π ^ 2 = π := sq_sqrt pi_pos.le
  unfold A C Sph
  rw [hν]
  simp only [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega,
    show m + 3 - 3 = m from by omega, show 2 * (m + 3) - 4 = 2 * m + 2 from by omega]
  rw [div_pow a 2 (m + 1)]
  set r := √π with hr
  rw [show π = r ^ 2 from hsq.symm]
  field_simp
  ring

/-- (2) 芯の極限：σ_d(k)/k^(d−3) → C_d·S_{d−1}·a^(2d−4)。 -/
theorem core_limit {d : ℕ} (hd : 3 ≤ d) {a : ℝ} (ha : 0 < a) (s₀ tail : ℝ → ℝ)
    (hs₀ : Tendsto (fun k => s₀ k / (A d a * k ^ (2 * d - 4))) (𝓝[>] 0) (𝓝 1))
    (htail : Tendsto (fun k => tail k / s₀ k) (𝓝[>] 0) (𝓝 0))
    (hne : ∀ᶠ k in 𝓝[>] (0 : ℝ), s₀ k ≠ 0) :
    Tendsto (fun k => pref d k * (s₀ k + tail k) / k ^ (d - 3)) (𝓝[>] 0)
      (𝓝 (C d * Sph d * a ^ (2 * d - 4))) := by
  have hlim := (hs₀.mul (htail.const_add 1)).const_mul (4 * (2 * π) ^ (d - 1) / Sph d * A d a)
  rw [add_zero, mul_one, mul_one] at hlim
  rw [← coeff_identity hd a]
  refine hlim.congr' ?_
  have hA : A d a ≠ 0 := by
    unfold A
    have hG1 : 0 < Gamma (ν d) := Gamma_pos_of_pos (ν_pos hd)
    have hG2 : 0 < Gamma (ν d + 1) := Gamma_pos_of_pos (by linarith [ν_pos hd])
    have := pi_pos
    positivity
  have hS := Sph_pos d hd
  filter_upwards [hne, self_mem_nhdsWithin] with k hk hk0
  have hk0 : (0 : ℝ) < k := hk0
  unfold pref
  have e : k ^ (2 * d - 4) = k ^ (d - 1) * k ^ (d - 3) := by rw [← pow_add]; congr 1; omega
  rw [e]
  have : k ^ (d - 1) ≠ 0 := by positivity
  have : k ^ (d - 3) ≠ 0 := by positivity
  field_simp

/-- S₂ = 4π（ℝ³ の単位球面）。 -/
theorem Sph_three : Sph 3 = 4 * π := by
  unfold Sph
  have h : ((3 : ℕ) : ℝ) / 2 = 1 / 2 + 1 := by norm_num
  rw [h, Gamma_add_one (by norm_num), Gamma_one_half_eq]
  have hs := sqrt_pos.mpr pi_pos
  have hsq : √π ^ 2 = π := sq_sqrt pi_pos.le
  rw [show √π ^ 3 = √π ^ 2 * √π by ring, hsq]
  field_simp
  ring

theorem C_three : C 3 = 1 := by
  unfold C ν
  norm_num
  rw [Gamma_one_half_eq, sq_sqrt pi_pos.le, div_self (ne_of_gt pi_pos)]

/-- (3) d = 3 では σ → 4πa²。 -/
theorem limit_three {a : ℝ} (ha : 0 < a) (s₀ tail : ℝ → ℝ)
    (hs₀ : Tendsto (fun k => s₀ k / (A 3 a * k ^ (2 * 3 - 4))) (𝓝[>] 0) (𝓝 1))
    (htail : Tendsto (fun k => tail k / s₀ k) (𝓝[>] 0) (𝓝 0))
    (hne : ∀ᶠ k in 𝓝[>] (0 : ℝ), s₀ k ≠ 0) :
    Tendsto (fun k => pref 3 k * (s₀ k + tail k)) (𝓝[>] 0) (𝓝 (4 * π * a ^ 2)) := by
  have := core_limit (le_refl 3) ha s₀ tail hs₀ htail hne
  simp only [show 3 - 3 = 0 from rfl, pow_zero, div_one, C_three, one_mul, Sph_three,
    show 2 * 3 - 4 = 2 from rfl] at this
  exact this

/-- (3) d ≥ 4 では σ → 0。 -/
theorem limit_high {d : ℕ} (hd : 4 ≤ d) {a : ℝ} (ha : 0 < a) (s₀ tail : ℝ → ℝ)
    (hs₀ : Tendsto (fun k => s₀ k / (A d a * k ^ (2 * d - 4))) (𝓝[>] 0) (𝓝 1))
    (htail : Tendsto (fun k => tail k / s₀ k) (𝓝[>] 0) (𝓝 0))
    (hne : ∀ᶠ k in 𝓝[>] (0 : ℝ), s₀ k ≠ 0) :
    Tendsto (fun k => pref d k * (s₀ k + tail k)) (𝓝[>] 0) (𝓝 0) := by
  have h1 := core_limit (by omega) ha s₀ tail hs₀ htail hne
  have h2 : Tendsto (fun k : ℝ => k ^ (d - 3)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun k : ℝ => k ^ (d - 3)) (𝓝 0) (𝓝 (0 ^ (d - 3))) :=
      (continuous_pow (d - 3)).tendsto 0
    rw [zero_pow (by omega)] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := h1.mul h2
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hk : (0 : ℝ) < k := hk
  have : k ^ (d - 3) ≠ 0 := by positivity
  field_simp

/-- (3) 0 でない有限の値に落ち着く ⇔ d = 3。 -/
theorem finite_nonzero_iff {d : ℕ} (hd : 3 ≤ d) {a : ℝ} (ha : 0 < a) (s₀ tail : ℝ → ℝ)
    (hs₀ : Tendsto (fun k => s₀ k / (A d a * k ^ (2 * d - 4))) (𝓝[>] 0) (𝓝 1))
    (htail : Tendsto (fun k => tail k / s₀ k) (𝓝[>] 0) (𝓝 0))
    (hne : ∀ᶠ k in 𝓝[>] (0 : ℝ), s₀ k ≠ 0) :
    (∃ L ≠ 0, Tendsto (fun k => pref d k * (s₀ k + tail k)) (𝓝[>] 0) (𝓝 L)) ↔ d = 3 := by
  constructor
  · rintro ⟨L, hL, hlim⟩
    by_contra h3
    have h0 := limit_high (by omega) ha s₀ tail hs₀ htail hne
    exact hL (tendsto_nhds_unique hlim h0)
  · intro h3
    subst h3
    refine ⟨4 * π * a ^ 2, by positivity, limit_three ha s₀ tail hs₀ htail hne⟩

/-- (4) C₃ = 1、C₄ = π/2、C₅ = 1、C₆ = π/8。 -/
theorem C_values : C 3 = 1 ∧ C 4 = π / 2 ∧ C 5 = 1 ∧ C 6 = π / 8 := by
  have g32 : Gamma (3 / 2) = √π / 2 := by
    rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Gamma_add_one (by norm_num), Gamma_one_half_eq]
    ring
  have hsq : √π ^ 2 = π := sq_sqrt pi_pos.le
  refine ⟨C_three, ?_, ?_, ?_⟩
  · unfold C ν; norm_num
  · unfold C ν; norm_num
    rw [g32, div_pow, hsq]
    have := pi_pos
    field_simp
    norm_num
  · unfold C ν; norm_num

/-- (5) 同種のボース粒子：σ_B/σ → 2（偶数の l の尾 ÷ sin²δ₀ → 0 のとき）。 -/
theorem bose_ratio {d : ℕ} (s₀ tail tailEven : ℝ → ℝ) (k₀ : ℝ)
    (htail : Tendsto (fun k => tail k / s₀ k) (𝓝[>] k₀) (𝓝 0))
    (heven : Tendsto (fun k => tailEven k / s₀ k) (𝓝[>] k₀) (𝓝 0))
    (hne : ∀ᶠ k in 𝓝[>] k₀, s₀ k ≠ 0) (hpref : ∀ᶠ k in 𝓝[>] k₀, pref d k ≠ 0) :
    Tendsto (fun k => (pref d k * (2 * (s₀ k + tailEven k))) / (pref d k * (s₀ k + tail k)))
      (𝓝[>] k₀) (𝓝 2) := by
  have h := ((heven.const_add 1).const_mul 2).div (htail.const_add 1) (by norm_num)
  simp only [add_zero, mul_one, div_one] at h
  refine h.congr' ?_
  have hev : ∀ᶠ k in 𝓝[>] k₀, 1 + tail k / s₀ k ≠ 0 :=
    (htail.const_add 1).eventually_ne (by norm_num : (1 : ℝ) + 0 ≠ 0)
  filter_upwards [hne, hpref, hev] with k hk hp hv
  have hsum : s₀ k + tail k ≠ 0 := by
    intro h0
    apply hv
    rw [show 1 + tail k / s₀ k = (s₀ k + tail k) / s₀ k by field_simp, h0, zero_div]
  simp only [Pi.div_apply]
  field_simp

end Paper1081

end Yamagishi
