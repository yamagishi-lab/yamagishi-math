/-
論文44『c¹ から c⁶ の次元の階層』（第3版）の芯「4π の冪は質量次元である」を、機械に確かめさせる。

原稿（44_yamagishi_c1_to_c6_dimensional_hierarchy/…_jp.tex）の
  第2節の表：G = a、ħ = 1/a（a > 0 は任意、山岸パッチは a = 4π）の下で、九つのプランク量は
    l_P = c^(−3/2)、t_P = c^(−5/2)、m_P = √c/a、E_P = c^(5/2)/a、T_P = c^(5/2)/a、
    F_P = c⁴/a、パワー = c⁵/a、ρ_P = c⁵/a、P_Pl = c⁷/a
    で、a の冪（1/a の冪で数えた ε）は質量次元 μ に一致する（長さ・時間は 0、ほかは 1）。
  定理3.1（ε ≥ 2 の量は存在する）：ħG = 1（ε = 0）、ħG² = a（ε = −1）、ħ/G = a^(−2)（ε = 2）。
  定理4.1：ε₀ = c、ħ = 1/a の下で、SI の q_P = √(4π ε₀ ħ c) = 2√π c/√a は a = 4π のときだけ
    c の純粋な冪、ガウスの q_P = √(ħc) = √c/√a は a = 1 のときだけ純粋な冪。
  第5節：8πG/c⁴ は一般に 8πa/c⁴ で、a = 4π のときだけ 32π²/c⁴ = 2(4π)²/c⁴。
  定理6.1（二つの種からの生成）：F_P = E_P/l_P = c⁴/a、パワー = E_P/t_P = c⁵/a、P_Pl = E_P/l_P³ = c⁷/a。

書き方：九つの量は、教科書の定義 l_P = √(ħG/c³)、t_P = √(ħG/c⁵)、m_P = √(ħc/G)、E_P = m_P c²、
F_P = c⁴/G、パワー = c⁵/G、ρ_P = c⁵/(ħG²)、P_Pl = c⁷/(ħG²) で置き、G = a、ħ = 1/a を入れた値を
正の実数の計算として導いた。T_P は原稿の表どおり k_B = 1 と置いて E_P と同じ値とした（T_P = E_P/k_B）。
定理6.1 の生成の式（E_P/l_P = F_P など）は、ħ・G・c の値によらない恒等式として示した
（原稿の「これは次元解析であって階層の証拠ではない」に当たる）。
質量次元 μ は、各量の (p, q, N)（X = ħ^p G^q c^N）から μ = p − q として数えた（ħ の質量次元 1、G の −1）。

形式化していないもの：「幾何量／物質量」という名、「4π は電磁単位の規約」という判断、
32π² を論文32・48 の量と同一視しないという判断、c の指数を空間次元と読まないこと、宇宙OS の読み。
プランク電荷の項目(x)は原稿で保留とされているが、定理4.1 の計算そのものは書いた（保留の判断は形式化していない）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper44

open Real

/-! ### 九つのプランク量（教科書の定義） -/

noncomputable def lP (hbar G c : ℝ) : ℝ := √(hbar * G / c ^ 3)
noncomputable def tP (hbar G c : ℝ) : ℝ := √(hbar * G / c ^ 5)
noncomputable def mP (hbar G c : ℝ) : ℝ := √(hbar * c / G)
noncomputable def EP (hbar G c : ℝ) : ℝ := mP hbar G c * c ^ 2
/-- プランク温度（k_B = 1 と置く）。 -/
noncomputable def TP (hbar G c : ℝ) : ℝ := EP hbar G c / 1
noncomputable def FP (G c : ℝ) : ℝ := c ^ 4 / G
noncomputable def powerP (G c : ℝ) : ℝ := c ^ 5 / G
noncomputable def rhoP (hbar G c : ℝ) : ℝ := c ^ 5 / (hbar * G ^ 2)
noncomputable def pressP (hbar G c : ℝ) : ℝ := c ^ 7 / (hbar * G ^ 2)

/-- 補題：s > 0 のとき (s²)^(k/2) = s^k（k は整数）。c = s² と置いて半整数の冪を扱う。 -/
theorem sq_rpow_half (s : ℝ) (hs : 0 < s) (k : ℤ) : (s ^ 2) ^ ((k : ℝ) / 2) = s ^ k := by
  rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le]
  push_cast
  rw [show (2 : ℝ) * (k / 2) = k by ring, Real.rpow_intCast]

/-- 九つの量の値（G = a、ħ = 1/a、a > 0、c > 0）。 -/
theorem nine_quantities (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    lP (1 / a) a c = c ^ ((-3 : ℝ) / 2) ∧
    tP (1 / a) a c = c ^ ((-5 : ℝ) / 2) ∧
    mP (1 / a) a c = c ^ ((1 : ℝ) / 2) / a ∧
    EP (1 / a) a c = c ^ ((5 : ℝ) / 2) / a ∧
    TP (1 / a) a c = c ^ ((5 : ℝ) / 2) / a ∧
    FP a c = c ^ 4 / a ∧
    powerP a c = c ^ 5 / a ∧
    rhoP (1 / a) a c = c ^ 5 / a ∧
    pressP (1 / a) a c = c ^ 7 / a := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ c = s ^ 2 :=
    ⟨√c, Real.sqrt_pos.mpr hc, (Real.sq_sqrt hc.le).symm⟩
  have e3 := sq_rpow_half s hs (-3)
  have e5 := sq_rpow_half s hs (-5)
  have e1 := sq_rpow_half s hs 1
  have e5' := sq_rpow_half s hs 5
  push_cast at e3 e5 e1 e5'
  have hsq : ∀ x : ℝ, 0 ≤ x → √(x ^ 2) = x := fun x hx => Real.sqrt_sq hx
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · rw [lP, e3, show 1 / a * a / (s ^ 2) ^ 3 = (s ^ (-3 : ℤ)) ^ 2 by
      field_simp]
    exact hsq _ (by positivity)
  · rw [tP, e5, show 1 / a * a / (s ^ 2) ^ 5 = (s ^ (-5 : ℤ)) ^ 2 by
      field_simp]
    exact hsq _ (by positivity)
  · rw [mP, e1, show 1 / a * s ^ 2 / a = (s ^ (1 : ℤ) / a) ^ 2 by field_simp]
    exact hsq _ (by positivity)
  · rw [EP, mP, e5', show 1 / a * s ^ 2 / a = (s / a) ^ 2 by field_simp,
      hsq _ (by positivity)]
    simp; ring
  · rw [TP, EP, mP, e5', show 1 / a * s ^ 2 / a = (s / a) ^ 2 by field_simp,
      hsq _ (by positivity)]
    simp; ring
  · rw [rhoP]; field_simp
  · rw [pressP]; field_simp

/-- 各量の (p, q, N)（X = ħ^p G^q c^N）と質量次元 μ = p − q。
長さ・時間は μ = 0、質量からプランク圧力までは μ = 1。 -/
def table : List (String × ℚ × ℚ × ℚ) :=
  [("l_P", 1/2, 1/2, -3/2), ("t_P", 1/2, 1/2, -5/2), ("m_P", 1/2, -1/2, 1/2),
   ("E_P", 1/2, -1/2, 5/2), ("T_P", 1/2, -1/2, 5/2), ("F_P", 0, -1, 4),
   ("パワー", 0, -1, 5), ("ρ_P", -1, -2, 5), ("P_Pl", -1, -2, 7)]

theorem table_mass_dims :
    table.map (fun x => x.2.1 - x.2.2.1) = [0, 0, 1, 1, 1, 1, 1, 1, 1] := by
  simp [table]; norm_num

/-- ε = μ の一般形（論文116 の定理5.1）：G = a、ħ = 1/a の下で ħ^p G^q c^N = c^N / a^(p−q)。
上の九つの値の a の冪と c の冪は、表の μ と N に一致している（ここは見比べで、
九つの値そのものは `nine_quantities` で、μ は `table_mass_dims` で別々に証明した）。 -/
theorem eps_eq_mu (a c p q N : ℝ) (ha : 0 < a) :
    (1 / a) ^ p * a ^ q * c ^ N = c ^ N / a ^ (p - q) := by
  rw [one_div, Real.inv_rpow ha.le, Real.rpow_sub ha]
  field_simp

/-! ### 定理3.1：ε ≥ 2 の量は存在する -/

/-- ħG = 1（ε = 0）、ħG² = a（ε = −1）、ħ/G = 1/a²（ε = 2）。a = 4π で ħ/G = 1/(16π²)。 -/
theorem eps_two_exists (a : ℝ) (ha : 0 < a) :
    (1 / a) * a = 1 ∧ (1 / a) * a ^ 2 = a ∧ (1 / a) / a = 1 / a ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

theorem hbar_over_G_patch : (1 / (4 * π)) / (4 * π) = 1 / (16 * π ^ 2) := by
  have : π ≠ 0 := Real.pi_ne_zero
  field_simp; ring

/-! ### 定理4.1：どの a が「強制」に見えるかは電磁単位に依存する -/

/-- SI（有理化）：ε₀ = c、ħ = 1/a のとき q_P = √(4π ε₀ ħ c) = 2√π · c/√a。 -/
theorem planck_charge_SI_value (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    √(4 * π * c * (1 / a) * c) = 2 * √π * c / √a := by
  have h : 4 * π * c * (1 / a) * c = (2 * √π * c / √a) ^ 2 := by
    have := Real.sq_sqrt (Real.pi_pos.le)
    have := Real.sq_sqrt ha.le
    have : √a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
    field_simp
    nlinarith [Real.sq_sqrt (Real.pi_pos.le), Real.sq_sqrt ha.le]
  rw [h, Real.sqrt_sq]
  have : 0 < √a := Real.sqrt_pos.mpr ha
  positivity

/-- SI：2√π · c/√a が c の純粋な冪（係数 1）になるのは a = 4π のときだけ。 -/
theorem planck_charge_SI_pure (a : ℝ) (ha : 0 < a) :
    (∃ k : ℝ, ∀ c : ℝ, 0 < c → 2 * √π * c / √a = c ^ k) ↔ a = 4 * π := by
  have hsa : 0 < √a := Real.sqrt_pos.mpr ha
  constructor
  · rintro ⟨k, hk⟩
    have h1 := hk 1 one_pos
    rw [Real.one_rpow, mul_one, div_eq_one_iff_eq (ne_of_gt hsa)] at h1
    have h2 := congrArg (· ^ 2) h1
    simp only [mul_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt ha.le] at h2
    linarith
  · rintro rfl
    refine ⟨1, fun c _ => ?_⟩
    rw [Real.rpow_one, Real.sqrt_mul (by norm_num), show √4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
    field_simp

/-- ガウス：q_P = √(ħc) = √(c/a) が c の純粋な冪になるのは a = 1 のときだけ。 -/
theorem planck_charge_Gauss_pure (a : ℝ) (ha : 0 < a) :
    (∃ k : ℝ, ∀ c : ℝ, 0 < c → √((1 / a) * c) = c ^ k) ↔ a = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    have h1 := hk 1 one_pos
    rw [Real.one_rpow, mul_one, Real.sqrt_eq_one, one_div, inv_eq_one] at h1
    exact h1
  · rintro rfl
    exact ⟨1 / 2, fun c _ => by rw [div_one, one_mul, Real.sqrt_eq_rpow]⟩

/-! ### 第5節：8πG/c⁴ は事実と規約の積 -/

/-- 一般には 8πG/c⁴ = 8πa/c⁴。a = 4π のとき 32π²/c⁴ = 2(4π)²/c⁴。 -/
theorem einstein_coupling (c : ℝ) :
    8 * π * (4 * π) / c ^ 4 = 32 * π ^ 2 / c ^ 4 ∧ 32 * π ^ 2 = 2 * (4 * π) ^ 2 := by
  constructor <;> ring

/-- 8πa/c⁴ = 32π²/c⁴ となるのは a = 4π のときだけ（c ≠ 0）。 -/
theorem einstein_coupling_iff (a c : ℝ) (hc : c ≠ 0) :
    8 * π * a / c ^ 4 = 32 * π ^ 2 / c ^ 4 ↔ a = 4 * π := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hc4 : c ^ 4 ≠ 0 := pow_ne_zero 4 hc
  constructor
  · intro h
    rw [div_left_inj₀ hc4] at h
    have : 8 * π * (a - 4 * π) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exfalso; have := Real.pi_pos; linarith
    · linarith
  · rintro rfl; ring_nf

/-! ### 定理6.1：二つの種からの生成（ħ・G・c の値によらない恒等式） -/

theorem generation (hbar G c : ℝ) (hh : 0 < hbar) (hG : 0 < G) (hc : 0 < c) :
    EP hbar G c / lP hbar G c = FP G c ∧
    EP hbar G c / tP hbar G c = powerP G c ∧
    EP hbar G c / lP hbar G c ^ 3 = pressP hbar G c := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ c = s ^ 2 :=
    ⟨√c, Real.sqrt_pos.mpr hc, (Real.sq_sqrt hc.le).symm⟩
  obtain ⟨h, hh', rfl⟩ : ∃ h, 0 < h ∧ hbar = h ^ 2 :=
    ⟨√hbar, Real.sqrt_pos.mpr hh, (Real.sq_sqrt hh.le).symm⟩
  obtain ⟨g, hg, rfl⟩ : ∃ g, 0 < g ∧ G = g ^ 2 :=
    ⟨√G, Real.sqrt_pos.mpr hG, (Real.sq_sqrt hG.le).symm⟩
  have hl : lP (h ^ 2) (g ^ 2) (s ^ 2) = h * g / s ^ 3 := by
    rw [lP, show h ^ 2 * g ^ 2 / (s ^ 2) ^ 3 = (h * g / s ^ 3) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have ht : tP (h ^ 2) (g ^ 2) (s ^ 2) = h * g / s ^ 5 := by
    rw [tP, show h ^ 2 * g ^ 2 / (s ^ 2) ^ 5 = (h * g / s ^ 5) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have hm : mP (h ^ 2) (g ^ 2) (s ^ 2) = h * s / g := by
    rw [mP, show h ^ 2 * s ^ 2 / g ^ 2 = (h * s / g) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · rw [EP, hm, hl, FP]; field_simp
  · rw [EP, hm, ht, powerP]; field_simp
  · rw [EP, hm, hl, pressP]; field_simp

end Paper44

end Yamagishi
