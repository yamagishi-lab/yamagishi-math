/-
論文1132『パッチは、プランク単位の質量の単位だけを 4π 倍にしたもの』の定理と系を、
機械に確かめさせる。

原稿（1132_…/…_jp.tex）の第2節〜第4節：
  第2節（取り直しの規則・Bridgman 1922）：質量の単位を x 倍、長さを y 倍、時間を z 倍にすると、
    次元 M^μ L^λ T^τ の量の数は x^(−μ) y^(−λ) z^(−τ) 倍になる。
  定理：c の数を同じに保ったまま、G と ħ の数を (1, 1) から (4π, 1/(4π)) へ移す取り直しは、
    質量の単位を 4π 倍にし、長さと時間の単位を動かさないもの、ただ一通り（倍率は正）。
  同じ計算：(G, ħ) を (1, 1) から一般の (a, b) へ移す取り直しは x = √(a/b)、y = z = 1/√(ab)。
    長さと時間が動かないのは ab = 1 のときだけ。
  系1：X_Pl = (4π)^μ X_patch。
  系2：X_patch に立つ 4π の冪が ε なら、X_Pl に立つ 4π の冪は ε + μ。
  系3：G・ħ・c のプランク単位の数は 1・1・c。
  系4：プランク単位の数の π の冪は 2r + u + ρ（論文1130 の帳簿の式）。

書き方：取り直しの倍率を、次元の指数（有理数）を実数の冪に入れた式として定義し、
G・ħ・c の倍率が原稿の x z²/y³、z/(x y²)、z/y になることは補題として導いた。
定理は「正の倍率 x, y, z について、三つの条件 ⇔ x = 4π, y = z = 1」の同値として書いた。

形式化していないもの：「新しい単位 = 倍率 × 古い単位」という物理の約束そのもの（取り直しの規則は
入力として置いた）、π の冪を数えるときの約束（値に立つ π は置き方・置いた質量・置かない質量・
じかの 4π からしか来ない、ほかの π は数えない）。系4 はこの約束を因子の表として置いたうえでの
勘定である。系2 の「π の冪」は、(4π) の冪で書いた形の冪として扱った（ある実数がどの π の冪を
「持つ」かという一意性は形式化していない）。CODATA の数値（2.734988(30)×10⁻⁷ kg）は扱っていない。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1132

open Real

/-- 次元（質量・長さ・時間の冪）。 -/
structure Dim where
  M : ℚ
  L : ℚ
  T : ℚ

def dimG : Dim := ⟨-1, 3, -2⟩
def dimHbar : Dim := ⟨1, 2, -1⟩
def dimC : Dim := ⟨0, 1, -1⟩

/-- 取り直しの規則：質量の単位 x 倍・長さ y 倍・時間 z 倍で、次元 d の量の数は
x^(−μ) y^(−λ) z^(−τ) 倍になる。 -/
noncomputable def rescale (x y z : ℝ) (d : Dim) : ℝ :=
  x ^ (-(d.M : ℝ)) * y ^ (-(d.L : ℝ)) * z ^ (-(d.T : ℝ))

theorem rescale_G (x y z : ℝ) (hy : 0 < y) :
    rescale x y z dimG = x * z ^ 2 / y ^ 3 := by
  simp only [rescale, dimG]
  push_cast
  norm_num
  field_simp

theorem rescale_hbar (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) :
    rescale x y z dimHbar = z / (x * y ^ 2) := by
  simp only [rescale, dimHbar]
  push_cast
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

theorem rescale_c (x y z : ℝ) (hy : 0 < y) :
    rescale x y z dimC = z / y := by
  simp only [rescale, dimC]
  push_cast
  norm_num
  rw [Real.rpow_neg hy.le]
  norm_num [div_eq_mul_inv, mul_comm]

/-- 定理：正の倍率 x, y, z について、c の数を保ち（倍率 1）、G の数を 1 から 4π へ、
ħ の数を 1 から 1/(4π) へ移す取り直しは、x = 4π、y = z = 1 ただ一通り。 -/
theorem patch_is_mass_unit_times_4pi (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (rescale x y z dimC = 1 ∧ 1 * rescale x y z dimG = 4 * π ∧
        1 * rescale x y z dimHbar = 1 / (4 * π))
      ↔ (x = 4 * π ∧ y = 1 ∧ z = 1) := by
  rw [rescale_c x y z hy, rescale_G x y z hy, rescale_hbar x y z hx hy]
  have hpi : 0 < π := Real.pi_pos
  constructor
  · rintro ⟨hc, hG, hh⟩
    have hzy : z = y := by
      rw [div_eq_one_iff_eq (ne_of_gt hy)] at hc; exact hc
    subst hzy
    have hG' : x = 4 * π * z := by
      rw [one_mul] at hG
      field_simp at hG
      linarith
    have hh' : x * z = 4 * π := by
      rw [one_mul] at hh
      field_simp at hh
      nlinarith
    have hz1 : z = 1 := by
      rw [hG'] at hh'
      have h2 : 4 * π * (z * z - 1) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h | h
      · linarith
      · nlinarith
    subst hz1
    exact ⟨by linarith, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨by norm_num, by norm_num, by field_simp⟩

/-- 一般の (a, b)：c の数を保ち (G, ħ) を (1, 1) から (a, b) へ移す取り直しは、
x = √(a/b)、y = z = 1/√(ab) ただ一通り。 -/
theorem general_rescale (a b x y z : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (rescale x y z dimC = 1 ∧ rescale x y z dimG = a ∧ rescale x y z dimHbar = b)
      ↔ (x = √(a / b) ∧ y = 1 / √(a * b) ∧ z = 1 / √(a * b)) := by
  rw [rescale_c x y z hy, rescale_G x y z hy, rescale_hbar x y z hx hy]
  constructor
  · rintro ⟨hc, hG, hh⟩
    have hzy : z = y := by
      rw [div_eq_one_iff_eq (ne_of_gt hy)] at hc; exact hc
    subst hzy
    have hG' : x = a * z := by field_simp at hG; linarith
    have hh' : 1 = b * (x * z) := by field_simp at hh; linarith
    have hz2 : z ^ 2 = 1 / (a * b) := by
      rw [hG'] at hh'
      field_simp
      nlinarith
    have hzs : z = 1 / √(a * b) := by
      have hab : 0 < a * b := mul_pos ha hb
      rw [one_div, ← Real.sqrt_inv]
      rw [← one_div, ← hz2, Real.sqrt_sq hz.le]
    refine ⟨?_, hzs, hzs⟩
    rw [hG', hzs]
    rw [Real.sqrt_div ha.le, Real.sqrt_mul ha.le]
    have h1 : 0 < √a := Real.sqrt_pos.mpr ha
    have h2 : 0 < √b := Real.sqrt_pos.mpr hb
    field_simp
    rw [Real.sq_sqrt ha.le]
  · rintro ⟨hx', hy', hz'⟩
    have hab : 0 < a * b := mul_pos ha hb
    have hs : 0 < √(a * b) := Real.sqrt_pos.mpr hab
    have h1 : 0 < √a := Real.sqrt_pos.mpr ha
    have h2 : 0 < √b := Real.sqrt_pos.mpr hb
    rw [hx', hy', hz']
    rw [Real.sqrt_div ha.le, Real.sqrt_mul ha.le]
    refine ⟨?_, ?_, ?_⟩
    · field_simp
    · field_simp
      rw [Real.sq_sqrt ha.le]
    · field_simp
      rw [Real.sq_sqrt hb.le]

/-- 長さと時間の単位が動かない（y = 1）のは ab = 1 のときだけ（論文116 の G = a・ħ = 1/a の族）。 -/
theorem length_unchanged_iff (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / √(a * b) = 1 ↔ a * b = 1 := by
  have hab : 0 < a * b := mul_pos ha hb
  have hs : 0 < √(a * b) := Real.sqrt_pos.mpr hab
  constructor
  · intro h
    have : √(a * b) = 1 := by field_simp at h; linarith
    have := congrArg (· ^ 2) this
    simp only [Real.sq_sqrt hab.le, one_pow] at this
    exact this
  · intro h; rw [h]; simp

/-! ### 系 -/

/-- 系1：パッチの取り直し（x = 4π、y = z = 1）では、次元 d の量の数は (4π)^(−μ) 倍になる。
すなわち X_patch = (4π)^(−μ) X_Pl、言い換えて X_Pl = (4π)^μ X_patch。 -/
theorem cor1_rescale (d : Dim) : rescale (4 * π) 1 1 d = (4 * π) ^ (-(d.M : ℝ)) := by
  simp [rescale]

theorem cor1 (d : Dim) (XPl Xpatch : ℝ) (h : Xpatch = rescale (4 * π) 1 1 d * XPl) :
    XPl = (4 * π) ^ (d.M : ℝ) * Xpatch := by
  rw [h, cor1_rescale, ← mul_assoc, ← Real.rpow_add (by positivity)]
  simp

/-- 系2：パッチの数が (4π)^ε · K なら、プランク単位の数は (4π)^(ε + μ) · K。 -/
theorem cor2 (d : Dim) (ε K XPl : ℝ)
    (h : (4 * π) ^ ε * K = rescale (4 * π) 1 1 d * XPl) :
    XPl = (4 * π) ^ (ε + d.M) * K := by
  have := cor1 d XPl _ h
  rw [this, ← mul_assoc, ← Real.rpow_add (by positivity), add_comm]

/-- 系3：パッチの数 G = 4π、ħ = 1/(4π)、c = c から戻すと、プランク単位の数は 1・1・c。 -/
theorem cor3 (cv : ℝ) :
    (4 * π) ^ (dimG.M : ℝ) * (4 * π) = 1 ∧
    (4 * π) ^ (dimHbar.M : ℝ) * (1 / (4 * π)) = 1 ∧
    (4 * π) ^ (dimC.M : ℝ) * cv = cv := by
  have hpi : 0 < π := Real.pi_pos
  refine ⟨?_, ?_, ?_⟩
  · simp [dimG, Real.rpow_neg_one]; field_simp
  · simp [dimHbar]; field_simp
  · simp [dimC]

/-- 置いた質量（パッチの数 4π・質量次元 1）のプランク単位の数は 16π²、
置かない質量 M は 4πM。 -/
theorem planck_number_of_masses (M : ℝ) :
    (4 * π) ^ (1 : ℝ) * (4 * π) = 16 * π ^ 2 ∧ (4 * π) ^ (1 : ℝ) * M = 4 * π * M := by
  constructor
  · rw [Real.rpow_one]; ring
  · rw [Real.rpow_one]

/-- 系4（因子ごと）：プランク単位の数の π の冪（4π の冪で数える）は、因子ごとに
（パッチの数の冪 ε）＋（質量次元 μ）。ħ: −1+1 = 0、G: 1−1 = 0、c: 0、置いた質量: 1+1 = 2、
置かない質量: 0+1 = 1、じかの 4π: 1+0 = 1。 -/
def epsPatch : Fin 6 → ℚ := ![-1, 1, 0, 1, 0, 1]
def muF : Fin 6 → ℚ := ![1, -1, 0, 1, 1, 0]
def piPowerPlanck : Fin 6 → ℚ := ![0, 0, 0, 2, 1, 1]

theorem cor4_each : ∀ i, piPowerPlanck i = epsPatch i + muF i := by
  intro i; fin_cases i <;> norm_num [piPowerPlanck, epsPatch, muF]

/-- 系4：指数 (p, q, N, r, u, ρ) の量のプランク単位の数の π の冪は 2r + u + ρ で、
それはパッチの数の ε と質量次元 μ の和に等しい。 -/
theorem cor4 (p q N r u ρ : ℚ) :
    let e : Fin 6 → ℚ := ![p, q, N, r, u, ρ]
    (∑ i, e i * piPowerPlanck i = 2 * r + u + ρ) ∧
    (∑ i, e i * piPowerPlanck i = (∑ i, e i * epsPatch i) + (∑ i, e i * muF i)) := by
  intro e
  constructor
  · simp [e, Fin.sum_univ_succ, piPowerPlanck]; ring
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [cor4_each i]; ring

end Paper1132

end Yamagishi
