/-
論文28『山岸・ケプラー方程式』の格上げ（一般の形）。

原稿（28_yamagishi_kepler_rendering_lag/…_jp.tex）は、§4.1 で円軌道に限り、引力 F ∝ r^n の向心力の
釣合いから周期 T ∝ a^((1−n)/2) を導き、数値積分（8 軌道・離心率 0〜0.6）は n = −2（ケプラー）の
場合だけで確かめている。d 次元の力 n = −(d − 1) は表で n = −1, −3, +1 を並べている。

ここで証明した言明（n は任意の実数、k > 0）：
  (1) `similarity`（力学的相似）：ノルムのある実の空間で r″ = −k‖r‖^(n−1) r（大きさ k‖r‖^n の引力）の
      解 r があれば、どの λ > 0 についても R(t) = λ r(μt)、μ = λ^((n−1)/2) も同じ方程式の解。
      `similarity_period`：r が周期 T をもてば R は周期 T/μ = T λ^((1−n)/2) をもつ。円軌道に限らず、
      相似な軌道どうしの周期は T ∝ a^((1−n)/2)。
  (2) `circular_period`：半径 a、角速度 ω の円運動で a ω² = k aⁿ ⇔ 周期 2π/ω = (2π/√k) a^((1−n)/2)。
  (3) `circular_stable_iff`：角運動量 ℓ の円軌道（ℓ² = k r₀^(n+3)）で、有効な動径の力
      F(r) = ℓ²/r³ − k rⁿ の傾き F′(r₀) = −k(n + 3) r₀^(n−1)。安定（F′(r₀) < 0）⇔ n > −3。
  (4) `gauss_exponent`：d 次元のガウスの力 n = −(d − 1) では周期の指数は d/2、円軌道が安定 ⇔ d < 4。
Lean の中では λ を s と書いた（λ は Lean の予約語）。
形式化していないもの：楕円軌道が閉じるかどうか（ベルトラン）、数値積分、描画の遅れの読み。
円軌道の安定は、有効な動径の力の傾きの符号として定義に置いた（摂動の方程式は扱っていない）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper28

open Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 運動方程式 r′ = v、v′ = −k‖r‖^(n−1) r（原点を通らない解）。 -/
def IsSolution (k n : ℝ) (r v : ℝ → E) : Prop :=
  ∀ t, r t ≠ 0 ∧ HasDerivAt r (v t) t ∧ HasDerivAt v (-(k * ‖r t‖ ^ (n - 1)) • r t) t

/-- (1) 力学的相似。 -/
theorem similarity {k n : ℝ} {r v : ℝ → E} (hs : IsSolution k n r v) {s : ℝ} (hs0 : 0 < s) :
    let μ := s ^ ((n - 1) / 2)
    IsSolution k n (fun t => s • r (μ * t)) (fun t => (s * μ) • v (μ * t)) := by
  intro μ t
  have hμ : 0 < μ := rpow_pos_of_pos hs0 _
  have hμ2 : μ * μ = s ^ (n - 1) := by
    rw [← rpow_add hs0]; congr 1; ring
  obtain ⟨hr0, hr, hv⟩ := hs (μ * t)
  have hlin : HasDerivAt (fun t : ℝ => μ * t) μ t := by
    simpa using (hasDerivAt_id t).const_mul μ
  refine ⟨smul_ne_zero hs0.ne' hr0, ?_, ?_⟩
  · have := (hr.scomp t hlin).const_smul s
    convert this using 1
    · funext x; rfl
    · rw [smul_smul]
  · have := (hv.scomp t hlin).const_smul (s * μ)
    convert this using 1
    · funext x; rfl
    · rw [smul_smul, smul_smul, norm_smul, Real.norm_of_nonneg hs0.le,
        mul_rpow hs0.le (norm_nonneg _), smul_smul]
      congr 1
      rw [mul_assoc s μ μ, hμ2]; ring

/-- (1) 周期は T/μ = T λ^((1−n)/2) になる。 -/
theorem similarity_period {r : ℝ → E} {T : ℝ} (hT : ∀ t, r (t + T) = r t) {s n : ℝ}
    (hs0 : 0 < s) :
    let μ := s ^ ((n - 1) / 2)
    (∀ t, s • r (μ * (t + T / μ)) = s • r (μ * t)) ∧ T / μ = T * s ^ ((1 - n) / 2) := by
  intro μ
  have hμ : 0 < μ := rpow_pos_of_pos hs0 _
  constructor
  · intro t
    rw [mul_add, mul_div_cancel₀ _ hμ.ne', hT]
  · rw [div_eq_mul_inv, ← rpow_neg hs0.le]; congr 2; ring

/-- (2) 円軌道の周期。 -/
theorem circular_period {a k ω n : ℝ} (ha : 0 < a) (hk : 0 < k) (hω : 0 < ω) :
    a * ω ^ 2 = k * a ^ n ↔ 2 * π / ω = 2 * π / √k * a ^ ((1 - n) / 2) := by
  have hpi := pi_pos
  have hsk : 0 < √k := sqrt_pos.2 hk
  have han : 0 < a ^ ((1 - n) / 2) := rpow_pos_of_pos ha _
  -- a ω² = k aⁿ ⇔ ω = √k a^((n−1)/2)
  have hsq : (√k * a ^ ((n - 1) / 2)) ^ 2 = k * a ^ (n - 1) := by
    rw [mul_pow, sq_sqrt hk.le, ← rpow_natCast, ← rpow_mul ha.le]; norm_num
  have hinv : a ^ ((1 - n) / 2) * a ^ ((n - 1) / 2) = 1 := by
    rw [← rpow_add ha, show (1 - n) / 2 + (n - 1) / 2 = 0 by ring, rpow_zero]
  have hapow : a * a ^ (n - 1) = a ^ n := by
    rw [mul_comm, ← rpow_add_one ha.ne']; congr 1; ring
  constructor
  · intro h
    have hω' : ω = √k * a ^ ((n - 1) / 2) := by
      have h2 : ω ^ 2 = (√k * a ^ ((n - 1) / 2)) ^ 2 := by
        rw [hsq]; apply mul_left_cancel₀ ha.ne'; rw [h, ← hapow]; ring
      have hpos : 0 < √k * a ^ ((n - 1) / 2) := mul_pos hsk (rpow_pos_of_pos ha _)
      nlinarith [sq_nonneg (ω - √k * a ^ ((n - 1) / 2)), sq_nonneg (ω + √k * a ^ ((n - 1) / 2))]
    rw [hω']
    field_simp
    nlinarith [hinv]
  · intro h
    have hω' : ω = √k * a ^ ((n - 1) / 2) := by
      have : ω * (a ^ ((1 - n) / 2)) = √k := by
        field_simp at h
        nlinarith
      have h2 : ω = ω * (a ^ ((1 - n) / 2) * a ^ ((n - 1) / 2)) := by rw [hinv, mul_one]
      rw [← mul_assoc, this] at h2; linarith
    rw [hω', mul_pow, sq_sqrt hk.le, ← rpow_natCast, ← rpow_mul ha.le, ← hapow]
    norm_num; ring

/-- 有効な動径の力 F(r) = ℓ²/r³ − k rⁿ。 -/
noncomputable def Feff (ℓ k n r : ℝ) : ℝ := ℓ ^ 2 / r ^ 3 - k * r ^ n

theorem hasDerivAt_Feff (ℓ k n : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (Feff ℓ k n) (-(3 * ℓ ^ 2 / r ^ 4) - k * (n * r ^ (n - 1))) r := by
  have h1 : HasDerivAt (fun r : ℝ => ℓ ^ 2 / r ^ 3) (-(3 * ℓ ^ 2 / r ^ 4)) r := by
    have := ((hasDerivAt_pow 3 r).inv (pow_ne_zero 3 hr.ne')).const_mul (ℓ ^ 2)
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp; ring
  have h2 := (hasDerivAt_rpow_const (p := n) (Or.inl hr.ne')).const_mul k
  exact h1.sub h2

/-- (3) 円軌道の傾きと安定の条件。 -/
theorem circular_stable_iff {ℓ k n r₀ : ℝ} (hk : 0 < k) (hr : 0 < r₀)
    (hcirc : ℓ ^ 2 = k * r₀ ^ (n + 3)) :
    Feff ℓ k n r₀ = 0 ∧ deriv (Feff ℓ k n) r₀ = -(k * (n + 3) * r₀ ^ (n - 1)) ∧
      (deriv (Feff ℓ k n) r₀ < 0 ↔ -3 < n) := by
  have h3 : r₀ ^ (n + 3) = r₀ ^ n * r₀ ^ 3 := by
    rw [rpow_add hr]; norm_cast
  have h4 : r₀ ^ (n + 3) = r₀ ^ (n - 1) * r₀ ^ 4 := by
    rw [← rpow_natCast, ← rpow_add hr]; congr 1; push_cast; ring
  have hp := rpow_pos_of_pos hr (n - 1)
  have hderiv : deriv (Feff ℓ k n) r₀ = -(k * (n + 3) * r₀ ^ (n - 1)) := by
    rw [(hasDerivAt_Feff ℓ k n hr).deriv, hcirc, h4]
    field_simp
    ring
  refine ⟨?_, hderiv, ?_⟩
  · unfold Feff
    rw [hcirc, h3]
    field_simp
    ring
  · rw [hderiv]
    constructor
    · intro h
      by_contra hc; push Not at hc
      have : k * (n + 3) * r₀ ^ (n - 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hk.le (by linarith)) hp.le
      linarith
    · intro h
      have : 0 < k * (n + 3) * r₀ ^ (n - 1) := mul_pos (mul_pos hk (by linarith)) hp
      linarith

/-- (4) d 次元のガウスの力 n = −(d − 1)。 -/
theorem gauss_exponent (d : ℝ) : (1 - (-(d - 1))) / 2 = d / 2 ∧ (-3 < -(d - 1) ↔ d < 4) := by
  constructor
  · ring
  · constructor <;> intro h <;> linarith

end Paper28

end Yamagishi
