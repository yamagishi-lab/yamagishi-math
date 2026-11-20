/-
論文1128『質量に速さを掛けた型は、プランク単位で c ずつ上り、4π は一つ』の数学の芯を、
機械に確かめさせる。

原稿（1128_…/…_jp.tex）の第3節〜第6節：
  型 k yk := kg·(m/s)^k、次元 (μ, λ, τ) = (1, k, −k)（k = 0, 1, 2, 3）。
  梯子の一段：×(m/s) は (μ, λ, τ) ↦ (μ, λ+1, τ−1)。
  数の顔：X = ħ^p G^q c^N と書くと、四つの型は (p, q, N) = (1/2, −1/2, k + 1/2)、
    m_P c^k = √(ħ/G) · c^(k+1/2)。
  一段の比が c になる理由：次元を Δ だけ動かす段の指数の動きは
    Δp = (Δμ+Δλ+Δτ)/2、Δq = (−Δμ+Δλ+Δτ)/2、ΔN = (Δμ−3Δλ−5Δτ)/2 で、
    Δp = Δq = 0 の段は速さの冪 (m/s)^j だけ（そのとき ΔN = j、比は c^j）。
  パッチ G = a、ħ = 1/a の下で：ħG = 1、ħ/G = a^(−2)、√(ħ/G) = 1/a、m_P c^k = c^((2k+1)/2)/a。
    c = 1 なら四つの型はどれも 1/a。
  第5節：1 yk/t_P = c⁴/a、2 yk/t_P = c⁵/a、2 yk · t_P = 1 yk · l_P = ħ（= 1/a）。
    長さだけを足す梯子 kg·m^k/s² の指数は ((k−1)/2, (k−3)/2, (11−3k)/2)。
    パッチを h に置く（h = 1/a、G = a）と ħG = 1/(2π)、l_P = c^(−3/2)/√(2π)、
    h で作ったプランク質量は m_P の √(2π) 倍。

書き方：(p, q, N) は次元の照合（質量・長さ・時間の三元一次の連立、行列式 −2）の解として置き、
値は正の実数 ħ・G・c と実数の冪で計算した。k は 0〜3 に限らず、任意の実数で成り立つ形で書いた。

形式化していないもの：点・線・皮・肉という型の名と、論文12 の「線・皮・肉の形」の読み、
「k を空間の次元と読まない」という判断、第6節の幾何の顔（ガウス＝ボネ・シュタイナーの公式との並び）、
CODATA 2022 の数値と不確かさの勘定（常用対数 8.476821 など）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1128

open Real

/-- 次元（質量 μ・長さ λ・時間 τ の冪）。 -/
structure Dim where
  mu : ℝ
  lam : ℝ
  tau : ℝ

/-- 型 k yk = kg·(m/s)^k の次元 (1, k, −k)。 -/
def yk (k : ℝ) : Dim := ⟨1, k, -k⟩

/-- 速さを一回掛ける段。 -/
def timesSpeed (d : Dim) : Dim := ⟨d.mu, d.lam + 1, d.tau - 1⟩

/-- 梯子の一段：k yk に速さを掛けると (k+1) yk。 -/
theorem ladder_step (k : ℝ) : timesSpeed (yk k) = yk (k + 1) := by
  simp [timesSpeed, yk]; ring

/-- 次元の照合（3 次元）：ħ^p G^q c^N の次元が (μ, λ, τ)。ħ = (1, 2, −1)、G = (−1, 3, −2)、
c = (0, 1, −1)。 -/
def Matches (d : Dim) (p q N : ℝ) : Prop :=
  p - q = d.mu ∧ 2 * p + 3 * q + N = d.lam ∧ -p - 2 * q - N = d.tau

/-- 連立の係数行列（行 M・L・T、列 ħ・G・c）の行列式は −2。 -/
theorem det_minus_two :
    (!![1, -1, 0; 2, 3, 1; -1, -2, -1] : Matrix (Fin 3) (Fin 3) ℝ).det = -2 := by
  simp [Matrix.det_fin_three]; norm_num

/-- 解はただ一つ：q = (λ+τ−μ)/2、p = μ + q、N = −(μ+τ) − 3q（論文116 の d = 3）。 -/
theorem matches_iff (d : Dim) (p q N : ℝ) :
    Matches d p q N ↔ (q = (d.lam + d.tau - d.mu) / 2 ∧ p = d.mu + q ∧
      N = -(d.mu + d.tau) - 3 * q) := by
  unfold Matches
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; refine ⟨by linarith, by linarith, by linarith⟩

/-- 四つの型の指数は (1/2, −1/2, k + 1/2)（どの実数 k でも）。 -/
theorem yk_exponents (k p q N : ℝ) :
    Matches (yk k) p q N ↔ (p = 1/2 ∧ q = -1/2 ∧ N = k + 1/2) := by
  rw [matches_iff]
  simp only [yk]
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; refine ⟨by linarith, by linarith, by linarith⟩

/-- 段の指数の動き：Δ だけ動かす段の (Δp, Δq, ΔN)。 -/
theorem step_exponents (Δ : Dim) :
    Matches Δ ((Δ.mu + Δ.lam + Δ.tau) / 2) ((-Δ.mu + Δ.lam + Δ.tau) / 2)
      ((Δ.mu - 3 * Δ.lam - 5 * Δ.tau) / 2) := by
  unfold Matches; refine ⟨by ring, by ring, by ring⟩

/-- Δp = Δq = 0 の段は速さの冪 (m/s)^j だけで、そのとき ΔN = j。 -/
theorem speed_only_direction (Δ : Dim) (N : ℝ) :
    Matches Δ 0 0 N ↔ (Δ.mu = 0 ∧ Δ.lam = N ∧ Δ.tau = -N) := by
  unfold Matches
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; refine ⟨by linarith, by linarith, by linarith⟩

/-- 長さだけを足す梯子 kg·m^k/s² の指数は ((k−1)/2, (k−3)/2, (11−3k)/2)。 -/
theorem length_ladder_exponents (k : ℝ) :
    Matches ⟨1, k, -2⟩ ((k - 1) / 2) ((k - 3) / 2) ((11 - 3 * k) / 2) := by
  unfold Matches; refine ⟨by ring, by ring, by ring⟩

/-! ### 値：m_P c^k = √(ħ/G) · c^(k+1/2) -/

/-- プランク質量 m_P = √(ħc/G)。 -/
noncomputable def mP (hbar G c : ℝ) : ℝ := √(hbar * c / G)

/-- 四つの型のプランクの量は m_P c^k = √(ħ/G) · c^(k+1/2)（正の ħ・G・c、実数 k）。 -/
theorem mP_mul_c_pow (hbar G c k : ℝ) (hh : 0 < hbar) (hG : 0 < G) (hc : 0 < c) :
    mP hbar G c * c ^ k = √(hbar / G) * c ^ (k + 1 / 2) := by
  rw [mP, show hbar * c / G = (hbar / G) * c by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_eq_rpow c, Real.rpow_add hc]
  ring

/-- 隣り合う型の比はちょうど c（ħ と G によらない）。 -/
theorem adjacent_ratio (hbar G c k : ℝ) (hh : 0 < hbar) (hG : 0 < G) (hc : 0 < c) :
    (mP hbar G c * c ^ (k + 1)) / (mP hbar G c * c ^ k) = c := by
  have hm : 0 < mP hbar G c := Real.sqrt_pos.mpr (by positivity)
  rw [Real.rpow_add hc, Real.rpow_one]
  have : 0 < c ^ k := Real.rpow_pos_of_pos hc k
  field_simp

/-- パッチの下（G = a、ħ = 1/a）：ħG = 1、ħ/G = a^(−2)、√(ħ/G) = 1/a。 -/
theorem patch_basics (a : ℝ) (ha : 0 < a) :
    (1 / a) * a = 1 ∧ (1 / a) / a = a ^ (-2 : ℤ) ∧ √((1 / a) / a) = 1 / a := by
  refine ⟨by field_simp, ?_, ?_⟩
  · rw [zpow_neg]; field_simp
  · rw [show (1 / a) / a = (1 / a) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)

/-- パッチの下で、型 k のプランクの量は c^((2k+1)/2)/a。 -/
theorem patch_types (a c k : ℝ) (ha : 0 < a) (hc : 0 < c) :
    mP (1 / a) a c * c ^ k = c ^ ((2 * k + 1) / 2) / a := by
  rw [mP_mul_c_pow _ _ _ _ (by positivity) ha hc, (patch_basics a ha).2.2]
  rw [show k + 1 / 2 = (2 * k + 1) / 2 by ring]
  ring

/-- c = 1 なら四つの型はどれも 1/a（数の顔の段差が消える）。 -/
theorem patch_types_c_one (a k : ℝ) (ha : 0 < a) :
    mP (1 / a) a 1 * (1 : ℝ) ^ k = 1 / a := by
  rw [patch_types a 1 k ha one_pos, Real.one_rpow]

/-! ### 第5節：プランク時間・長さとの席 -/

noncomputable def lP (hbar G c : ℝ) : ℝ := √(hbar * G / c ^ 3)
noncomputable def tP (hbar G c : ℝ) : ℝ := √(hbar * G / c ^ 5)

/-- 2 yk · t_P = 1 yk · l_P = ħ は、正の ħ・G・c のどんな値でも成り立つ（パッチを使わない）。 -/
theorem planck_action (hbar G c : ℝ) (hh : 0 < hbar) (hG : 0 < G) (hc : 0 < c) :
    mP hbar G c * c ^ 2 * tP hbar G c = hbar ∧ mP hbar G c * c * lP hbar G c = hbar := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ c = s ^ 2 :=
    ⟨√c, Real.sqrt_pos.mpr hc, (Real.sq_sqrt hc.le).symm⟩
  obtain ⟨h, hh', rfl⟩ : ∃ h, 0 < h ∧ hbar = h ^ 2 :=
    ⟨√hbar, Real.sqrt_pos.mpr hh, (Real.sq_sqrt hh.le).symm⟩
  obtain ⟨g, hg, rfl⟩ : ∃ g, 0 < g ∧ G = g ^ 2 :=
    ⟨√G, Real.sqrt_pos.mpr hG, (Real.sq_sqrt hG.le).symm⟩
  have hm : mP (h ^ 2) (g ^ 2) (s ^ 2) = h * s / g := by
    rw [mP, show h ^ 2 * s ^ 2 / g ^ 2 = (h * s / g) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have hl : lP (h ^ 2) (g ^ 2) (s ^ 2) = h * g / s ^ 3 := by
    rw [lP, show h ^ 2 * g ^ 2 / (s ^ 2) ^ 3 = (h * g / s ^ 3) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have ht : tP (h ^ 2) (g ^ 2) (s ^ 2) = h * g / s ^ 5 := by
    rw [tP, show h ^ 2 * g ^ 2 / (s ^ 2) ^ 5 = (h * g / s ^ 5) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  constructor
  · rw [hm, ht]; field_simp
  · rw [hm, hl]; field_simp

/-- パッチの下：1 yk/t_P = c⁴/a、2 yk/t_P = c⁵/a（ħ = 1/a は `planck_action` に ħ = 1/a を入れたもの）。 -/
theorem patch_seats (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    mP (1 / a) a c * c / tP (1 / a) a c = c ^ 4 / a ∧
    mP (1 / a) a c * c ^ 2 / tP (1 / a) a c = c ^ 5 / a := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ c = s ^ 2 :=
    ⟨√c, Real.sqrt_pos.mpr hc, (Real.sq_sqrt hc.le).symm⟩
  have hm : mP (1 / a) a (s ^ 2) = s / a := by
    rw [mP, show 1 / a * s ^ 2 / a = (s / a) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have ht : tP (1 / a) a (s ^ 2) = 1 / s ^ 5 := by
    rw [tP, show 1 / a * a / (s ^ 2) ^ 5 = (1 / s ^ 5) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  constructor
  · rw [hm, ht]; field_simp
  · rw [hm, ht]; field_simp

/-! ### パッチを h に置いたとき -/

/-- h = 1/a、G = a（ħ = h/(2π)）なら ħG = 1/(2π)、l_P = c^(−3/2)/√(2π)、
h で作ったプランク質量 √(hc/G) は m_P = √(ħc/G) の √(2π) 倍。 -/
theorem patch_on_h (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (1 / a) / (2 * π) * a = 1 / (2 * π) ∧
    lP ((1 / a) / (2 * π)) a c = √(1 / c ^ 3) / √(2 * π) ∧
    √((1 / a) * c / a) = √(2 * π) * mP ((1 / a) / (2 * π)) a c := by
  have hpi : 0 < π := Real.pi_pos
  refine ⟨by field_simp, ?_, ?_⟩
  · rw [lP, ← Real.sqrt_div' _ (by positivity : (0:ℝ) ≤ 2 * π)]
    congr 1; field_simp
  · rw [mP, ← Real.sqrt_mul (by positivity)]
    congr 1; field_simp

end Paper1128

end Yamagishi
