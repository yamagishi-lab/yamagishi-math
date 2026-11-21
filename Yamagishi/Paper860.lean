/-
論文860『引いて切ると、刃の角は小さく見える』の格上げ（一般の形）。

原稿（860_yamagishi_slicing_makes_the_angle_look_smaller/…_jp.tex）は、片側の角 θ のくさびの刃を、
刃先に垂直に押す速さ 1 に対して刃先に沿って速さ λ で動かすとき、動く向きと横の向きが張る面で
くさびを切った断面の角 θ_eff を、θ = 10 度・λ = 0・0.5・1・2・3・5 で数値で出し、面の法線の外積から
出した跡の角と 10^(−13) 以下で一致すること、λ = √3 で正接が半分になることを確かめている。

ここで証明した言明（すべての θ と λ）：刃先を x 軸、押す向きを −z、片側の面を x 軸と
u = (0, sin θ, cos θ) が張る面（法線 n₁ = (0, −cos θ, sin θ)）、刃に対する動きの向きを
m = (λ, 0, −1)、横の向きを y = (0, 1, 0)、断面を m と y が張る面（法線 n₂ = (1, 0, λ)）とする。
  (1) `d_perp`：d = n₁ × n₂ = (−λ cos θ, sin θ, cos θ) は n₁ にも n₂ にも直交する（面と断面の交わり
      の向き）。`d_decomp`：d = sin θ·y − cos θ·m（断面の中での分け方）。
  (2) `tan_eff`：断面の中で、動きの向きと逆の単位ベクトル −m/|m| に対する d の角 θ_eff は
      tan θ_eff = sin θ /(cos θ·√(1+λ²)) = tan θ/√(1+λ²)（0 < θ < π/2）。
  (3) `eff_le`：0 < θ_eff ≤ θ で、等号は λ = 0 のときだけ（`eff_lt`）。`tan_half`：λ = √3 で
      正接はちょうど半分。
定義に置いたもの：くさびと動きの幾何の置き方（上の座標）と、θ_eff を
arctan(横の成分 / 動きと逆の向きの成分) で定めたこと。刃先の丸み・摩擦・刃の曲がりは扱わない。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper860

open Real Matrix

/-- 面の法線 n₁ = e₁ × u。 -/
noncomputable def n1 (θ : ℝ) : Fin 3 → ℝ := ![0, -cos θ, sin θ]
/-- 断面の法線 n₂ = m × y。 -/
def n2 (l : ℝ) : Fin 3 → ℝ := ![1, 0, l]
/-- 刃に対する動きの向き。 -/
def m (l : ℝ) : Fin 3 → ℝ := ![l, 0, -1]
/-- 横の向き。 -/
def y : Fin 3 → ℝ := ![0, 1, 0]
/-- 交わりの向き d = n₁ × n₂。 -/
noncomputable def d (θ l : ℝ) : Fin 3 → ℝ := ![-(l * cos θ), sin θ, cos θ]

theorem n1_eq (θ : ℝ) : n1 θ = crossProduct ![1, 0, 0] ![0, sin θ, cos θ] := by
  ext i; fin_cases i <;> simp [n1, cross_apply]

theorem n2_eq (l : ℝ) : n2 l = crossProduct (m l) y := by
  ext i; fin_cases i <;> simp [n2, m, y, cross_apply]

theorem d_eq (θ l : ℝ) : d θ l = crossProduct (n1 θ) (n2 l) := by
  ext i; fin_cases i <;> simp [d, n1, n2, cross_apply]; ring

/-- (1) d は二つの法線に直交する。 -/
theorem d_perp (θ l : ℝ) : d θ l ⬝ᵥ n1 θ = 0 ∧ d θ l ⬝ᵥ n2 l = 0 := by
  constructor <;> simp [d, n1, n2, dotProduct, Fin.sum_univ_three] <;> ring

/-- d = sin θ·y − cos θ·m。 -/
theorem d_decomp (θ l : ℝ) : d θ l = sin θ • y - cos θ • m l := by
  ext i; fin_cases i <;> simp [d, y, m]; ring

/-- 断面の中での見かけの角：横の成分 sin θ と、動きと逆の単位ベクトルの向きの成分
cos θ·|m| = cos θ·√(1+λ²) の比の逆正接。 -/
noncomputable def eff (θ l : ℝ) : ℝ := arctan (sin θ / (cos θ * √(1 + l ^ 2)))

theorem norm_m (l : ℝ) : √(m l ⬝ᵥ m l) = √(1 + l ^ 2) := by
  congr 1; simp [m, dotProduct, Fin.sum_univ_three]; ring

/-- d の −m/|m| の向きの成分は cos θ·√(1+λ²)、y の向きの成分は sin θ。 -/
theorem components (θ l : ℝ) :
    d θ l ⬝ᵥ (-(1 / √(1 + l ^ 2)) • m l) = cos θ * √(1 + l ^ 2) ∧ d θ l ⬝ᵥ y = sin θ := by
  have hs : 0 < √(1 + l ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsq : √(1 + l ^ 2) ^ 2 = 1 + l ^ 2 := Real.sq_sqrt (by positivity)
  constructor
  · simp [d, m, dotProduct, Fin.sum_univ_three]
    field_simp
    rw [hsq]
  · simp [d, y, dotProduct, Fin.sum_univ_three]

/-- (2) tan θ_eff = tan θ/√(1+λ²)。 -/
theorem tan_eff {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) (l : ℝ) :
    tan (eff θ l) = tan θ / √(1 + l ^ 2) := by
  unfold eff
  rw [tan_arctan, tan_eq_sin_div_cos]
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have hs : 0 < √(1 + l ^ 2) := Real.sqrt_pos.mpr (by positivity)
  field_simp

theorem sqrt_ge_one (l : ℝ) : 1 ≤ √(1 + l ^ 2) := by
  rw [Real.le_sqrt' (by norm_num)]
  nlinarith [sq_nonneg l]

/-- (3) 0 < θ_eff ≤ θ。 -/
theorem eff_le {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) (l : ℝ) : 0 < eff θ l ∧ eff θ l ≤ θ := by
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have hsn : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hs := sqrt_ge_one l
  unfold eff
  constructor
  · exact arctan_pos.mpr (by positivity)
  · have hθ : θ = arctan (tan θ) := (arctan_tan (by linarith) h1).symm
    conv_rhs => rw [hθ]
    apply arctan_strictMono.monotone
    rw [tan_eq_sin_div_cos, div_le_div_iff₀ (by positivity) hc]
    have := mul_pos hsn hc
    nlinarith

/-- λ ≠ 0 なら θ_eff < θ（引いて切ると角は小さく見える）。 -/
theorem eff_lt {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) {l : ℝ} (hl : l ≠ 0) : eff θ l < θ := by
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have hsn : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hs : 1 < √(1 + l ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    have := pow_pos (abs_pos.mpr hl) 2
    nlinarith [sq_abs l]
  unfold eff
  have hθ : θ = arctan (tan θ) := (arctan_tan (by linarith) h1).symm
  conv_rhs => rw [hθ]
  apply arctan_strictMono
  rw [tan_eq_sin_div_cos, div_lt_div_iff₀ (by positivity) hc]
  have := mul_pos hsn hc
  nlinarith

/-- λ = 0 なら θ_eff = θ。 -/
theorem eff_zero {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) : eff θ 0 = θ := by
  unfold eff
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Real.sqrt_one,
    mul_one]
  rw [← tan_eq_sin_div_cos, arctan_tan (by linarith) h1]

/-- λ = √3 で正接はちょうど半分。 -/
theorem tan_half {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) : tan (eff θ √3) = tan θ / 2 := by
  rw [tan_eff h0 h1, Real.sq_sqrt (by norm_num)]
  congr 1
  rw [show (1 : ℝ) + 3 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

end Paper860

end Yamagishi
