/-
論文945『合法な碁の局面の割合は、一点ごとに一定の比で減る』の格上げ（芯だけ）。

原稿（945_yamagishi_the_share_of_legal_go_positions_shrinks_by_a_fixed_ratio_per_point/…_jp.tex）は、
幅 1〜4 の転送行列で、高さを一行足すごとの合法な局面の数の比（2.769292354・8.533652512・
25.445014706・75.709341135）を数値で出し、一点あたりの比が幅とともに増える（四つの値）と観察して
いる。

ここで証明した言明（芯だけ）：
  (1) `lambda_supermul`：幅 w・高さ n の合法な局面の数 L(w, n) が L(w₁+w₂, n) ≥ L(w₁, n)·L(w₂, n)
      を満たし、各 w で L(w, n)^(1/n) → λ_w なら、λ_(w₁+w₂) ≥ λ_w₁·λ_w₂（極限で不等式が残る）。
  (2) `fekete_sup`（フェケテの補題）：正の数列 λ が λ_(a+b) ≥ λ_a λ_b を満たし、ある C で
      λ_w ≤ C^w なら、一点あたりの比 λ_w^(1/w) は w → ∞ で収束し、その極限はすべての
      λ_w^(1/w) 以上（すなわち上限）である。Mathlib の `Submultiplicative.tendsto_lim` を 1/λ に使った。
  (3) `not_monotone`：超乗法性だけからは、一点あたりの比が幅について増えることは出ない。
      反例 λ_w = 2^(w − (w mod 2)) は超乗法的で λ_w ≤ 2^w だが、λ₂^(1/2) = 2 > 2^(2/3) = λ₃^(1/3)。
      （下読みの AI の注意のとおり、原稿の「幅とともに増える」は四つの値の観察で、一般には未解決。）
仮定として置いたもの：碁の盤を横に並べても合法のままであること（並べた盤の各石の塊は元の盤の塊の
和で、元の呼吸点がそのまま残る、という一行の議論）は (1) の仮定 L(w₁+w₂, n) ≥ L(w₁, n)L(w₂, n) に
置いた。碁の合法性そのもの、転送行列とペロン・フロベニウスによる L(w, n)^(1/n) → λ_w は形式化して
いない。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper945

open Filter Topology Real

/-- (1) 個数の超乗法性は、極限の比 λ に残る。 -/
theorem lambda_supermul {a b c : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hc : ∀ n, a n * b n ≤ c n) {x y z : ℝ}
    (hx : Tendsto (fun n : ℕ => a n ^ (n : ℝ)⁻¹) atTop (𝓝 x))
    (hy : Tendsto (fun n : ℕ => b n ^ (n : ℝ)⁻¹) atTop (𝓝 y))
    (hz : Tendsto (fun n : ℕ => c n ^ (n : ℝ)⁻¹) atTop (𝓝 z)) : x * y ≤ z := by
  have hxy := hx.mul hy
  apply le_of_tendsto_of_tendsto' hxy hz
  intro n
  rw [← Real.mul_rpow (ha n) (hb n)]
  exact Real.rpow_le_rpow (mul_nonneg (ha n) (hb n)) (hc n) (by positivity)

/-- (2) フェケテの補題：一点あたりの比は収束し、極限はすべての λ_w^(1/w) 以上。 -/
theorem fekete_sup {lam : ℕ → ℝ} (hpos : ∀ n, 0 < lam n)
    (hsup : ∀ m n, lam m * lam n ≤ lam (m + n)) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ n, lam n ≤ C ^ n) :
    ∃ L, Tendsto (fun n : ℕ => lam n ^ (n : ℝ)⁻¹) atTop (𝓝 L) ∧
      ∀ n, n ≠ 0 → lam n ^ (n : ℝ)⁻¹ ≤ L := by
  set u : ℕ → ℝ := fun n => (lam n)⁻¹ with hu
  have hsub : Submultiplicative u := by
    intro m n
    simp only [hu]
    rw [← mul_inv]
    exact inv_anti₀ (mul_pos (hpos m) (hpos n)) (hsup m n)
  have hu0 : ∀ n, 0 ≤ u n := fun n => (inv_pos.mpr (hpos n)).le
  have hlim := hsub.tendsto_lim hu0
  -- u_n^(1/n) ≥ 1/C なので極限は正
  have hlow : ∀ n, n ≠ 0 → C⁻¹ ≤ u n ^ (n : ℝ)⁻¹ := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have : (C ^ n)⁻¹ ≤ u n := inv_anti₀ (hpos n) (hbound n)
    have h2 := Real.rpow_le_rpow (by positivity) this (inv_nonneg.mpr hn'.le)
    rwa [← inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hC.le),
      mul_inv_cancel₀ hn'.ne', Real.rpow_one] at h2
  have hlimpos : 0 < hsub.lim := by
    have : C⁻¹ ≤ hsub.lim :=
      ge_of_tendsto hlim ((eventually_ne_atTop 0).mono fun n hn => hlow n hn)
    exact lt_of_lt_of_le (inv_pos.mpr hC) this
  refine ⟨(hsub.lim)⁻¹, ?_, ?_⟩
  · have := hlim.inv₀ hlimpos.ne'
    refine this.congr (fun n => ?_)
    simp only [hu]
    rw [Real.inv_rpow (hpos n).le, inv_inv]
  · intro n hn
    have h1 := hsub.lim_le_rpow hu0 hn
    simp only [hu] at h1
    rw [Real.inv_rpow (hpos n).le] at h1
    have hp : 0 < lam n ^ (n : ℝ)⁻¹ := Real.rpow_pos_of_pos (hpos n) _
    rw [le_inv_comm₀ hlimpos hp] at h1
    exact h1

/-! ## (3) 超乗法性だけでは単調にならない -/

/-- 反例の数列 λ_w = 2^(w − (w mod 2))。 -/
noncomputable def lamEx (w : ℕ) : ℝ := 2 ^ (w - w % 2)

theorem lamEx_supermul (m n : ℕ) : lamEx m * lamEx n ≤ lamEx (m + n) := by
  unfold lamEx
  rw [← pow_add]
  apply pow_le_pow_right₀ (by norm_num)
  omega

theorem lamEx_bound (n : ℕ) : lamEx n ≤ 2 ^ n := by
  unfold lamEx
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- λ₂^(1/2) = 2 > 2^(2/3) = λ₃^(1/3)：一点あたりの比は幅について増えるとは限らない。 -/
theorem not_monotone : lamEx 3 ^ ((3 : ℕ) : ℝ)⁻¹ < lamEx 2 ^ ((2 : ℕ) : ℝ)⁻¹ := by
  unfold lamEx
  have e3 : (2 : ℝ) ^ (3 - 3 % 2) = 4 := by norm_num
  rw [e3]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)

end Paper945

end Yamagishi
