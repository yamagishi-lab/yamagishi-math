/-
論文257『「速さ」を変えても「行き先」は変わらない』の格上げ（一般の形）。

原稿（257_yamagishi_speed_is_not_destination/…_jp.tex）は、触媒が正逆の速度定数を同じ倍率 exp(δ/RT)
で動かすので K = k_f/k_r が動かないことを示し、N₂ + 3H₂ ⇌ 2NH₃ で H₂ = 3 mol に N₂ を足していくと
NH₃ がいったん増えてから減ること、その頂点で x(N₂) = 0.5000 になることを、K と H₂ の量の 7 通りで
二分法で数えている。一般の反応や仕込みの比の形は書いていない。

ここで証明した言明（一定の T・P の理想気体の反応 aA + bB ⇌ cC、a, b, c > 0、C は初め 0、
反応進行度 ξ、n_C = cξ、N = n_A + n_B + (c − a − b)ξ）：
  (0) `catalyst_K`：正逆の速度定数を同じ倍率で動かしても K = k_f/k_r は変わらない。
  (1) `F_eq_log`：平衡の条件 F(ξ, n_A) = 0 は x_C^c/(x_A^a x_B^b) = K の対数の形。
  (2) `F_strictMonoOn`：F は ξ について狭義に増える（∂F/∂ξ = c/ξ + a²/n_A′ + b²/n_B′ − Δν²/N > 0、
      コーシー＝シュワルツの形）。`equilibrium_unique`：平衡の ξ はただ一つ。
  (3) `hasDerivAt_F_nA`：ξ を決めると ∂F/∂n_A = −(a·n_B − (b − c)·n_A)/(n_A′·N)。分子に ξ も K も入らない。
  (4) `yield_increases`・`yield_decreases`：仕込み n₁ < n₂ の平衡 ξ₁, ξ₂ について、(n₁, n₂) で
      a·n_B − (b − c)t > 0 なら ξ₁ < ξ₂（C が増える）、< 0 なら ξ₁ > ξ₂（C が減る）。
      `yield_increases_of_le`：b ≤ c なら、足すほど必ず増える。
      `yield_unimodal`：b > c なら、n_A ≤ a·n_B/(b − c) で増え、n_A ≥ a·n_B/(b − c) で減る。
  (5) `xA_at_peak`：頂点 n_A = a·n_B/(b − c) では、どの ξ でも x_A = a/(a + b − c)。
      `ammonia_peak`：アンモニア合成（a = 1, b = 3, c = 2）では頂点は n_N₂ = n_H₂、x_N₂ = 1/2。
どれも K と P によらない。
足した仮定：a, b, c > 0、n_B > 0、K > 0、理想気体（活量係数 1）、一定の T・P。
形式化していないもの：平衡の ξ がある（存在する）こと（ここでは平衡の ξ が与えられたとして比べた）、
一定の T・V の場合、初めに C を含む場合、表の数値、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）

For an ideal-gas reaction aA + bB ⇌ cC at fixed T and P started without C, the equilibrium amount of
C rises with the charge of A where a·n_B > (b − c)·n_A and falls where a·n_B < (b − c)·n_A, whatever
K and P; at the turning point x_A = a/(a + b − c) (one half for ammonia synthesis).
-/
import Mathlib

namespace Yamagishi

namespace Paper257

open Real Set

/-- (0) 触媒は二つの速度定数を同じ倍率 m で動かし、比 K は変わらない。 -/
theorem catalyst_K {kf kr m : ℝ} (hm : m ≠ 0) : (m * kf) / (m * kr) = kf / kr :=
  mul_div_mul_left kf kr hm

/-- 平衡の条件の対数の形 F(ξ, n_A)。Δν = c − a − b。 -/
noncomputable def F (a b c K nB nA ξ : ℝ) : ℝ :=
  c * log (c * ξ) - a * log (nA - a * ξ) - b * log (nB - b * ξ)
    - (c - a - b) * log (nA + nB + (c - a - b) * ξ) - log K

/-- 全体の物質量 N は三つの量の和。 -/
theorem N_eq (a b c nA nB ξ : ℝ) :
    nA + nB + (c - a - b) * ξ = (nA - a * ξ) + (nB - b * ξ) + c * ξ := by ring

/-- (1) F = log(x_C^c/(x_A^a x_B^b)) − log K（x_j = n_j/N）。 -/
theorem F_eq_log {a b c K nA nB ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (hA : a * ξ < nA)
    (hB : b * ξ < nB) :
    F a b c K nB nA ξ =
      log ((c * ξ / (nA + nB + (c - a - b) * ξ)) ^ c /
        (((nA - a * ξ) / (nA + nB + (c - a - b) * ξ)) ^ a *
          ((nB - b * ξ) / (nA + nB + (c - a - b) * ξ)) ^ b)) - log K := by
  have p1 : 0 < c * ξ := mul_pos hc hξ
  have p2 : 0 < nA - a * ξ := by linarith
  have p3 : 0 < nB - b * ξ := by linarith
  have pN : 0 < nA + nB + (c - a - b) * ξ := by rw [N_eq]; linarith
  unfold F
  conv_rhs => rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_rpow (by positivity), log_rpow (by positivity), log_rpow (by positivity),
    log_div p1.ne' pN.ne', log_div p2.ne' pN.ne', log_div p3.ne' pN.ne']
  ring

/-- ∂F/∂ξ の式。 -/
theorem hasDerivAt_F_xi {a b c K nA nB ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (hA : a * ξ < nA)
    (hB : b * ξ < nB) :
    HasDerivAt (fun x => F a b c K nB nA x)
      (c / ξ + a ^ 2 / (nA - a * ξ) + b ^ 2 / (nB - b * ξ)
        - (c - a - b) ^ 2 / (nA + nB + (c - a - b) * ξ)) ξ := by
  have p1 : c * ξ ≠ 0 := (mul_pos hc hξ).ne'
  have p2 : nA - a * ξ ≠ 0 := by linarith
  have p3 : nB - b * ξ ≠ 0 := by linarith
  have pN : nA + nB + (c - a - b) * ξ ≠ 0 := by
    rw [N_eq]; have := mul_pos hc hξ; linarith
  have h1 := ((hasDerivAt_id' ξ).const_mul c).log p1
  have h2 := (((hasDerivAt_id' ξ).const_mul a).const_sub nA).log p2
  have h3 := (((hasDerivAt_id' ξ).const_mul b).const_sub nB).log p3
  have h4 := (((hasDerivAt_id' ξ).const_mul (c - a - b)).const_add (nA + nB)).log pN
  have h := ((((h1.const_mul c).sub (h2.const_mul a)).sub (h3.const_mul b)).sub
    (h4.const_mul (c - a - b))).sub_const (log K)
  unfold F
  convert h using 1
  field_simp
  ring

/-- 芯：コーシー＝シュワルツの形 c/ξ + a²/p + b²/q > (c − a − b)²/(p + q + cξ)。 -/
theorem titu {a b c ξ p q : ℝ} (ha : 0 < a) (hc : 0 < c) (hξ : 0 < ξ) (hp : 0 < p) (hq : 0 < q) :
    (c - a - b) ^ 2 / (p + q + c * ξ) < c / ξ + a ^ 2 / p + b ^ 2 / q := by
  have hr : 0 < c * ξ := mul_pos hc hξ
  set r := c * ξ
  have hS : 0 < p + q + r := by linarith
  have e : c / ξ = c ^ 2 / r := by simp only [r]; field_simp
  rw [e, div_lt_iff₀ hS]
  -- S·Σ ν²/n − (Σ ν)² = Σ_{i<j} (ν_i n_j − ν_j n_i)²/(n_i n_j)
  have key : (c ^ 2 / r + a ^ 2 / p + b ^ 2 / q) * (p + q + r) - (c - a - b) ^ 2 =
      ((-a) * q - (-b) * p) ^ 2 / (p * q) + ((-a) * r - c * p) ^ 2 / (p * r) +
        ((-b) * r - c * q) ^ 2 / (q * r) := by
    field_simp; ring
  have t1 : 0 ≤ ((-a) * q - (-b) * p) ^ 2 / (p * q) := by positivity
  have t2 : 0 < ((-a) * r - c * p) ^ 2 / (p * r) := by
    apply div_pos _ (by positivity)
    have : (-a) * r - c * p < 0 := by nlinarith
    rw [show ((-a) * r - c * p) ^ 2 = (c * p - (-a) * r) ^ 2 by ring]
    exact pow_pos (by linarith) 2
  have t3 : 0 ≤ ((-b) * r - c * q) ^ 2 / (q * r) := by positivity
  nlinarith

/-- (2) F は ξ について狭義に増える（可能な範囲 0 < ξ、aξ < n_A、bξ < n_B で）。 -/
theorem F_strictMonoOn {a b c K nA nB : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    StrictMonoOn (fun x => F a b c K nB nA x) {x | 0 < x ∧ a * x < nA ∧ b * x < nB} := by
  have hconv : Convex ℝ {x : ℝ | 0 < x ∧ a * x < nA ∧ b * x < nB} := by
    have : {x : ℝ | 0 < x ∧ a * x < nA ∧ b * x < nB} = Ioo 0 (min (nA / a) (nB / b)) := by
      ext x
      simp only [mem_ofPred_eq, mem_Ioo, lt_min_iff, lt_div_iff₀ ha, lt_div_iff₀ hb]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
    rw [this]; exact convex_Ioo _ _
  apply strictMonoOn_of_hasDerivWithinAt_pos hconv
  · intro x hx
    exact (hasDerivAt_F_xi hc hx.1 hx.2.1 hx.2.2).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact (hasDerivAt_F_xi hc hx'.1 hx'.2.1 hx'.2.2).hasDerivWithinAt
  · intro x hx
    have hx' := interior_subset hx
    obtain ⟨h1, h2, h3⟩ := hx'
    have hp : 0 < nA - a * x := by linarith
    have hq : 0 < nB - b * x := by linarith
    have := titu (b := b) ha hc h1 hp hq
    rw [N_eq]
    linarith

/-- (2) 平衡の ξ はただ一つ。 -/
theorem equilibrium_unique {a b c K nA nB ξ₁ ξ₂ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h₁ : 0 < ξ₁ ∧ a * ξ₁ < nA ∧ b * ξ₁ < nB) (h₂ : 0 < ξ₂ ∧ a * ξ₂ < nA ∧ b * ξ₂ < nB)
    (e₁ : F a b c K nB nA ξ₁ = 0) (e₂ : F a b c K nB nA ξ₂ = 0) : ξ₁ = ξ₂ :=
  (F_strictMonoOn (K := K) ha hb hc).injOn h₁ h₂ (e₁.trans e₂.symm)

/-- (3) ξ を決めたときの ∂F/∂n_A。分子 a·n_B − (b − c)·n_A に ξ も K も入らない。 -/
theorem hasDerivAt_F_nA {a b c K nB t ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (hA : a * ξ < t)
    (hB : b * ξ < nB) :
    HasDerivAt (fun s => F a b c K nB s ξ)
      (-(a * nB - (b - c) * t) / ((t - a * ξ) * (t + nB + (c - a - b) * ξ))) t := by
  have p2 : t - a * ξ ≠ 0 := by linarith
  have pN : t + nB + (c - a - b) * ξ ≠ 0 := by
    have : t + nB + (c - a - b) * ξ = (t - a * ξ) + (nB - b * ξ) + c * ξ := by ring
    rw [this]; have := mul_pos hc hξ; linarith
  have h2 := ((hasDerivAt_id' t).sub_const (a * ξ)).log p2
  have h4 := (((hasDerivAt_id' t).add_const nB).add_const ((c - a - b) * ξ)).log pN
  have hf : (fun s => F a b c K nB s ξ) = fun s =>
      (c * log (c * ξ) - b * log (nB - b * ξ) - log K) - a * log (s - a * ξ)
        - (c - a - b) * log (s + nB + (c - a - b) * ξ) := by
    funext s; unfold F; ring
  rw [hf]
  have h := ((h2.const_mul a).const_sub (c * log (c * ξ) - b * log (nB - b * ξ) - log K)).sub
    (h4.const_mul (c - a - b))
  convert h using 1
  set N := t + nB + (c - a - b) * ξ with hN
  field_simp
  rw [hN]
  ring

/-- ξ を決めると、t ↦ F(ξ, t) は、分子 a·n_B − (b − c)t の符号に応じて狭義に減る／増える。 -/
theorem F_nA_anti {a b c K nB n₁ n₂ ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (hA : a * ξ < n₁)
    (hB : b * ξ < nB) (h12 : n₁ < n₂) (hsign : ∀ t ∈ Ioo n₁ n₂, 0 < a * nB - (b - c) * t) :
    F a b c K nB n₂ ξ < F a b c K nB n₁ ξ := by
  have hd : ∀ t ∈ Icc n₁ n₂, HasDerivAt (fun s => F a b c K nB s ξ)
      (-(a * nB - (b - c) * t) / ((t - a * ξ) * (t + nB + (c - a - b) * ξ))) t :=
    fun t ht => hasDerivAt_F_nA hc hξ (by linarith [ht.1]) hB
  have hanti := strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc n₁ n₂)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (by
      intro t ht
      rw [interior_Icc] at ht
      have h1 : 0 < t - a * ξ := by linarith [ht.1]
      have h2 : 0 < t + nB + (c - a - b) * ξ := by
        have : t + nB + (c - a - b) * ξ = (t - a * ξ) + (nB - b * ξ) + c * ξ := by ring
        rw [this]; have := mul_pos hc hξ; linarith
      apply div_neg_of_neg_of_pos (by linarith [hsign t ht]) (mul_pos h1 h2))
  exact hanti ⟨le_refl _, h12.le⟩ ⟨h12.le, le_refl _⟩ h12

theorem F_nA_mono {a b c K nB n₁ n₂ ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (hA : a * ξ < n₁)
    (hB : b * ξ < nB) (h12 : n₁ < n₂) (hsign : ∀ t ∈ Ioo n₁ n₂, a * nB - (b - c) * t < 0) :
    F a b c K nB n₁ ξ < F a b c K nB n₂ ξ := by
  have hd : ∀ t ∈ Icc n₁ n₂, HasDerivAt (fun s => F a b c K nB s ξ)
      (-(a * nB - (b - c) * t) / ((t - a * ξ) * (t + nB + (c - a - b) * ξ))) t :=
    fun t ht => hasDerivAt_F_nA hc hξ (by linarith [ht.1]) hB
  have hmono := strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc n₁ n₂)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (by
      intro t ht
      rw [interior_Icc] at ht
      have h1 : 0 < t - a * ξ := by linarith [ht.1]
      have h2 : 0 < t + nB + (c - a - b) * ξ := by
        have : t + nB + (c - a - b) * ξ = (t - a * ξ) + (nB - b * ξ) + c * ξ := by ring
        rw [this]; have := mul_pos hc hξ; linarith
      apply div_pos (by linarith [hsign t ht]) (mul_pos h1 h2))
  exact hmono ⟨le_refl _, h12.le⟩ ⟨h12.le, le_refl _⟩ h12

/-- (4) 分子が正の範囲では、A を足すほど平衡の C が増える。 -/
theorem yield_increases {a b c K nB n₁ n₂ ξ₁ ξ₂ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h12 : n₁ < n₂) (h₁ : 0 < ξ₁ ∧ a * ξ₁ < n₁ ∧ b * ξ₁ < nB)
    (h₂ : 0 < ξ₂ ∧ a * ξ₂ < n₂ ∧ b * ξ₂ < nB)
    (e₁ : F a b c K nB n₁ ξ₁ = 0) (e₂ : F a b c K nB n₂ ξ₂ = 0)
    (hsign : ∀ t ∈ Ioo n₁ n₂, 0 < a * nB - (b - c) * t) : ξ₁ < ξ₂ := by
  have hlt := F_nA_anti (K := K) hc h₁.1 h₁.2.1 h₁.2.2 h12 hsign
  rw [e₁] at hlt
  by_contra h
  have h' : ξ₂ ≤ ξ₁ := le_of_not_gt h
  have hmem₁ : 0 < ξ₁ ∧ a * ξ₁ < n₂ ∧ b * ξ₁ < nB := ⟨h₁.1, by linarith [h₁.2.1], h₁.2.2⟩
  have := (F_strictMonoOn (K := K) (nA := n₂) ha hb hc).monotoneOn h₂ hmem₁ h'
  linarith

/-- (4) 分子が負の範囲では、A を足すほど平衡の C が減る。 -/
theorem yield_decreases {a b c K nB n₁ n₂ ξ₁ ξ₂ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h12 : n₁ < n₂) (h₁ : 0 < ξ₁ ∧ a * ξ₁ < n₁ ∧ b * ξ₁ < nB)
    (h₂ : 0 < ξ₂ ∧ a * ξ₂ < n₂ ∧ b * ξ₂ < nB)
    (e₁ : F a b c K nB n₁ ξ₁ = 0) (e₂ : F a b c K nB n₂ ξ₂ = 0)
    (hsign : ∀ t ∈ Ioo n₁ n₂, a * nB - (b - c) * t < 0) : ξ₂ < ξ₁ := by
  have hgt := F_nA_mono (K := K) hc h₁.1 h₁.2.1 h₁.2.2 h12 hsign
  rw [e₁] at hgt
  have hmem₁ : 0 < ξ₁ ∧ a * ξ₁ < n₂ ∧ b * ξ₁ < nB := ⟨h₁.1, by linarith [h₁.2.1], h₁.2.2⟩
  by_contra h
  have h' : ξ₁ ≤ ξ₂ := le_of_not_gt h
  have := (F_strictMonoOn (K := K) (nA := n₂) ha hb hc).monotoneOn hmem₁ h₂ h'
  linarith

/-- (4) b ≤ c なら、足すほど必ず増える。 -/
theorem yield_increases_of_le {a b c K nB n₁ n₂ ξ₁ ξ₂ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hbc : b ≤ c) (hnB : 0 < nB) (hn₁ : 0 < n₁)
    (h12 : n₁ < n₂) (h₁ : 0 < ξ₁ ∧ a * ξ₁ < n₁ ∧ b * ξ₁ < nB)
    (h₂ : 0 < ξ₂ ∧ a * ξ₂ < n₂ ∧ b * ξ₂ < nB)
    (e₁ : F a b c K nB n₁ ξ₁ = 0) (e₂ : F a b c K nB n₂ ξ₂ = 0) : ξ₁ < ξ₂ := by
  apply yield_increases ha hb hc h12 h₁ h₂ e₁ e₂
  intro t ht
  have ht0 : 0 < t := hn₁.trans ht.1
  have : (b - c) * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le
  have := mul_pos ha hnB
  linarith

/-- (4) b > c なら、頂点 a·n_B/(b − c) の手前で増え、先で減る。 -/
theorem yield_unimodal {a b c K nB n₁ n₂ ξ₁ ξ₂ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hbc : c < b) (h12 : n₁ < n₂) (h₁ : 0 < ξ₁ ∧ a * ξ₁ < n₁ ∧ b * ξ₁ < nB)
    (h₂ : 0 < ξ₂ ∧ a * ξ₂ < n₂ ∧ b * ξ₂ < nB)
    (e₁ : F a b c K nB n₁ ξ₁ = 0) (e₂ : F a b c K nB n₂ ξ₂ = 0) :
    (n₂ ≤ a * nB / (b - c) → ξ₁ < ξ₂) ∧ (a * nB / (b - c) ≤ n₁ → ξ₂ < ξ₁) := by
  have hd : 0 < b - c := by linarith
  constructor
  · intro hn
    apply yield_increases ha hb hc h12 h₁ h₂ e₁ e₂
    intro t ht
    have : t < a * nB / (b - c) := lt_of_lt_of_le ht.2 hn
    rw [lt_div_iff₀ hd] at this
    linarith
  · intro hn
    apply yield_decreases ha hb hc h12 h₁ h₂ e₁ e₂
    intro t ht
    have : a * nB / (b - c) < t := lt_of_le_of_lt hn ht.1
    rw [div_lt_iff₀ hd] at this
    linarith

/-- (5) 恒等式 a·N + Δν·n_A′ = a·n_B − (b − c)·n_A（ξ によらない）。 -/
theorem key_identity (a b c nA nB ξ : ℝ) :
    a * (nA + nB + (c - a - b) * ξ) + (c - a - b) * (nA - a * ξ) = a * nB - (b - c) * nA := by
  ring

/-- (5) 頂点 n_A = a·n_B/(b − c) では、どの ξ でも x_A = a/(a + b − c)。 -/
theorem xA_at_peak {a b c nB ξ : ℝ} (ha : 0 < a) (hbc : c < b)
    (hN : 0 < a * nB / (b - c) + nB + (c - a - b) * ξ) :
    (a * nB / (b - c) - a * ξ) / (a * nB / (b - c) + nB + (c - a - b) * ξ) = a / (a + b - c) := by
  have hd : 0 < b - c := by linarith
  have hs : 0 < a + b - c := by linarith
  have h0 := key_identity a b c (a * nB / (b - c)) nB ξ
  have hz : a * nB - (b - c) * (a * nB / (b - c)) = 0 := by field_simp; ring
  rw [hz] at h0
  rw [div_eq_div_iff hN.ne' hs.ne']
  linarith

/-- (5) アンモニア合成 N₂ + 3H₂ ⇌ 2NH₃：頂点は n_N₂ = n_H₂、x_N₂ = 1/2。 -/
theorem ammonia_peak (nH : ℝ) : (1 : ℝ) * nH / (3 - 2) = nH ∧ (1 : ℝ) / (1 + 3 - 2) = 1 / 2 := by
  constructor <;> norm_num

end Paper257

end Yamagishi
