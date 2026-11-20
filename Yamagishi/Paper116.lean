/-
論文116『c の指数は何を数えるか』の定理と系を、機械に確かめさせる。

原稿（116_yamagishi_c_as_dimension_route/yamagishi_what_c_counts_jp.tex）の
  確立された事実2.1：[ħ] = M L² T⁻¹、[G_d] = L^d M⁻¹ T⁻²、[c] = L T⁻¹
  定理2.1（指数公式）：[X] = L^λ M^μ T^τ のとき、X = ħ^p G_d^q c^N を満たす実数の組 (p, q, N) は
    d ≠ 1 のとき一意に存在し、n = d − 1 として q = (λ+τ−μ)/n、p = μ + q、N = −(μ+τ) − 3q。
    連立系の行列式は 1 − d。
  系3.1：ℓ_P の指数は (1/n, 1/n, −3/n)、ℓ_P = (ħ G_d / c³)^(1/n)。
  観察：プランクパワーの N は d = 3, 4, 5, 6, 7 で 5, 4, 7/2, 16/5, 3。d = 3 で密度とパワーはどちらも N = 5。
  系4.1：d は N に 1/n としてのみ入る。
  定理5.1（ε = μ）：G = a、ħ = 1/a（a > 0）の下で ħ^p G^q c^N = a^(q−p) c^N = a^(−μ) c^N。
  系5.2：二分法（μ = 0 ⇔ a が付かない、μ = 1 ⇔ a が一つ付く）。
  系6.1：d = 3 で μ = 0 かつ N = 0 となる次元は (λ, μ, τ) ∝ (5, 0, −3) に限り、その量は ħG。
  観察6.2：二つの量が同じ (N, ε) に潰れるのは、次元の差が (5, 0, −3) の倍のときに限る。
  定理7.1（非一意性）と「唯一の例外」：SI の q_P = c√(4π/a) は a = 4π のときだけ c の純粋な冪、
    ガウス単位の q_P = √(c/a) は a = 1 のときだけ純粋な冪。

書き方：次元の照合を三元一次の連立方程式として書き、指数公式は「連立の解 ⇔ 公式の値」の同値として
証明した（一意性と存在を同時に含む）。行列式は Mathlib の 3×3 の行列式の公式で計算した。
d = 1 では行列式が 0 になり、解があるのは λ + τ = μ のときだけ（あれば無数）であることも書いた。
ε = μ は、正の実数 a, c と実数の冪で、値そのものの等式として証明した。

形式化していないもの：「3 は時間の重み」「次元は分母 n に座っていた」「n は論文01 の n = 2」という読み、
[G_d] の次元が F = G_d M m / r^(d−1) から来るという物理の定義（次元の表は入力として置いた）、
「c の指数を空間次元と読まない」という判断。「純粋な冪」は「ある実数 k があって、すべての c > 0 で
q_P = c^k」と定式化した（係数が 1 であること）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper116

open Real

/-- 次元の照合（質量・長さ・時間）：ħ^p G_d^q c^N の次元が L^λ M^μ T^τ に等しい。 -/
def Matches (d lam mu tau p q N : ℝ) : Prop :=
  p - q = mu ∧ 2 * p + d * q + N = lam ∧ -p - 2 * q - N = tau

/-- 定理2.1（指数公式）：d ≠ 1 なら、連立の解であることと、公式の値であることは同値。
したがって解はちょうど一つある。 -/
theorem exponent_formula (d lam mu tau p q N : ℝ) (hd : d ≠ 1) :
    Matches d lam mu tau p q N ↔
      (q = (lam + tau - mu) / (d - 1) ∧ p = mu + q ∧ N = -(mu + tau) - 3 * q) := by
  have hn : d - 1 ≠ 0 := sub_ne_zero.mpr hd
  unfold Matches
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hq : q * (d - 1) = lam + tau - mu := by nlinarith
    refine ⟨?_, by linarith, by linarith⟩
    rw [eq_div_iff hn]; exact hq
  · rintro ⟨hq, hp, hN⟩
    have hq' : q * (d - 1) = lam + tau - mu := by rw [hq]; field_simp
    refine ⟨by linarith, ?_, by linarith⟩
    nlinarith

/-- 一意な存在の形。 -/
theorem exponent_exists_unique (d lam mu tau : ℝ) (hd : d ≠ 1) :
    ∃! e : ℝ × ℝ × ℝ, Matches d lam mu tau e.1 e.2.1 e.2.2 := by
  set q := (lam + tau - mu) / (d - 1)
  refine ⟨(mu + q, q, -(mu + tau) - 3 * q), ?_, ?_⟩
  · exact (exponent_formula d lam mu tau _ _ _ hd).mpr ⟨rfl, rfl, rfl⟩
  · rintro ⟨p', q', N'⟩ h
    obtain ⟨h1, h2, h3⟩ := (exponent_formula d lam mu tau p' q' N' hd).mp h
    simp only [Prod.mk.injEq]
    subst h1
    exact ⟨h2, rfl, h3⟩

/-- 連立系の係数行列（行は M・L・T、列は ħ・G_d・c）。 -/
def A (d : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, -1, 0; 2, d, 1; -1, -2, -1]

/-- 行列式は 1 − d（= −n）。 -/
theorem det_A (d : ℝ) : (A d).det = 1 - d := by
  simp [A, Matrix.det_fin_three]; ring

/-- d = 1 では還元が破れる：解があるのは λ + τ = μ のときだけ。 -/
theorem d_eq_one_solvable_iff (lam mu tau : ℝ) :
    (∃ p q N : ℝ, Matches 1 lam mu tau p q N) ↔ lam + tau = mu := by
  unfold Matches
  constructor
  · rintro ⟨p, q, N, h1, h2, h3⟩; linarith
  · intro h
    exact ⟨mu, 0, lam - 2 * mu, by ring, by ring, by linarith⟩

/-- d = 1 で解があるときは、一つではない（q を自由に動かせる）。 -/
theorem d_eq_one_not_unique (lam mu tau : ℝ) (h : lam + tau = mu) (q : ℝ) :
    Matches 1 lam mu tau (mu + q) q (lam - 2 * mu - 3 * q) := by
  unfold Matches; refine ⟨by ring, by ring, by linarith⟩

/-- 系3.1：プランク長（次元 L）の指数は (1/n, 1/n, −3/n)。 -/
theorem planck_length_exponents (d : ℝ) (hd : d ≠ 1) :
    Matches d 1 0 0 (1 / (d - 1)) (1 / (d - 1)) (-3 / (d - 1)) := by
  rw [exponent_formula _ _ _ _ _ _ _ hd]
  refine ⟨by ring, by ring, by ring⟩

/-- 系3.1 の値の形：正の ħ, G, c と n > 0 で、ħ^(1/n) G^(1/n) c^(−3/n) = (ħ G / c³)^(1/n)。 -/
theorem planck_length_value (hbar G c n : ℝ) (hh : 0 < hbar) (hG : 0 < G) (hc : 0 < c) :
    hbar ^ (1 / n) * G ^ (1 / n) * c ^ (-3 / n) = (hbar * G / c ^ 3) ^ (1 / n) := by
  have h3 : (c ^ 3) ^ (1 / n) = c ^ (3 / n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; ring_nf
  have h4 : c ^ (-3 / n) = (c ^ (3 / n))⁻¹ := by
    rw [← Real.rpow_neg hc.le]; ring_nf
  rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow hh.le hG.le, h3, h4]
  ring

/-- 観察：プランクパワー（次元 L² M T⁻³）の N を d = 3, 4, 5, 6, 7 で計算すると
5, 4, 7/2, 16/5, 3（整数でない値をとる）。 -/
theorem planck_power_N :
    (-(1 + -3) - 3 * ((2 + -3 - 1) / ((3 : ℝ) - 1)) = 5) ∧
    (-(1 + -3) - 3 * ((2 + -3 - 1) / ((4 : ℝ) - 1)) = 4) ∧
    (-(1 + -3) - 3 * ((2 + -3 - 1) / ((5 : ℝ) - 1)) = 7 / 2) ∧
    (-(1 + -3) - 3 * ((2 + -3 - 1) / ((6 : ℝ) - 1)) = 16 / 5) ∧
    (-(1 + -3) - 3 * ((2 + -3 - 1) / ((7 : ℝ) - 1)) = 3) := by
  norm_num

/-- 観察：d = 3 で、プランク密度（L⁻³ M）とプランクパワー（L² M T⁻³）はどちらも N = 5。 -/
theorem density_and_power_same_N :
    Matches 3 (-3) 1 0 (-1) (-2) 5 ∧ Matches 3 2 1 (-3) 0 (-1) 5 := by
  unfold Matches; norm_num

/-- 系4.1：N を次元で書くと N = −(μ + τ) − 3(λ + τ − μ)/n。d は 1/n としてのみ入る。 -/
theorem N_formula (d lam mu tau p q N : ℝ) (hd : d ≠ 1) (h : Matches d lam mu tau p q N) :
    N = -(mu + tau) - 3 * (lam + tau - mu) * (1 / (d - 1)) := by
  obtain ⟨hq, -, hN⟩ := (exponent_formula d lam mu tau p q N hd).mp h
  rw [hN, hq]; ring

/-- d = 3 の表（論文44 の表の再現）：八つの量の (p, q, N)。 -/
theorem table_d3 :
    Matches 3 1 0 0 (1/2) (1/2) (-3/2) ∧      -- プランク長
    Matches 3 0 0 1 (1/2) (1/2) (-5/2) ∧      -- プランク時間
    Matches 3 0 1 0 (1/2) (-1/2) (1/2) ∧      -- プランク質量
    Matches 3 2 1 (-2) (1/2) (-1/2) (5/2) ∧   -- プランクエネルギー
    Matches 3 1 1 (-2) 0 (-1) 4 ∧             -- プランク力
    Matches 3 2 1 (-3) 0 (-1) 5 ∧             -- プランクパワー
    Matches 3 (-3) 1 0 (-1) (-2) 5 ∧          -- プランク密度
    Matches 3 (-1) 1 (-2) (-1) (-2) 7 := by   -- プランク圧力
  unfold Matches; norm_num

/-! ### ε = μ -/

/-- 定理5.1（ε = μ）：G = a、ħ = 1/a（a > 0）の下で ħ^p G^q c^N = a^(q−p) c^N。 -/
theorem patch_value (a c p q N : ℝ) (ha : 0 < a) :
    (1 / a) ^ p * a ^ q * c ^ N = a ^ (q - p) * c ^ N := by
  rw [one_div, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]
  ring_nf

/-- 定理5.1 を次元で：次元の照合が成り立つ (p, q, N) について、a の冪は −μ。 -/
theorem eps_eq_mu (d lam mu tau p q N a c : ℝ) (ha : 0 < a)
    (h : Matches d lam mu tau p q N) :
    (1 / a) ^ p * a ^ q * c ^ N = a ^ (-mu) * c ^ N := by
  rw [patch_value a c p q N ha]
  obtain ⟨h1, -, -⟩ := h
  congr 2; linarith

/-- 系5.2（二分法）：μ = 0 の量には a が付かず、μ = 1 の量には a が一つ（分母に）付く。 -/
theorem dichotomy (d lam tau p q N a c : ℝ) (ha : 0 < a) :
    (Matches d lam 0 tau p q N → (1 / a) ^ p * a ^ q * c ^ N = c ^ N) ∧
    (Matches d lam 1 tau p q N → (1 / a) ^ p * a ^ q * c ^ N = c ^ N / a) := by
  constructor
  · intro h; rw [eps_eq_mu d lam 0 tau p q N a c ha h]; simp
  · intro h; rw [eps_eq_mu d lam 1 tau p q N a c ha h, Real.rpow_neg_one]; ring

/-! ### 還元の核 -/

/-- 系6.1：d = 3 で、μ = 0 かつ N = 0 となる次元は (λ, μ, τ) = k(5, 0, −3) に限り、
そのとき (p, q, N) = (k, k, 0)、すなわち (ħG)^k。 -/
theorem kernel (lam tau p q : ℝ) :
    Matches 3 lam 0 tau p q 0 ↔ ∃ k : ℝ, lam = 5 * k ∧ tau = -3 * k ∧ p = k ∧ q = k := by
  unfold Matches
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨p, by linarith, by linarith, rfl, by linarith⟩
  · rintro ⟨k, rfl, rfl, rfl, rfl⟩
    refine ⟨by ring, by ring, by ring⟩

/-- 観察6.2（潰れる条件）：d = 3 で、二つの量の (N, μ) が同じであることと、次元の差が
(5, 0, −3) の倍であることは同値。 -/
theorem collapse_iff (l1 m1 t1 l2 m2 t2 : ℝ) :
    (-(m1 + t1) - 3 * ((l1 + t1 - m1) / (3 - 1)) = -(m2 + t2) - 3 * ((l2 + t2 - m2) / (3 - 1))
      ∧ m1 = m2) ↔ ∃ k : ℝ, l1 - l2 = 5 * k ∧ m1 = m2 ∧ t1 - t2 = -3 * k := by
  constructor
  · rintro ⟨hN, hm⟩
    subst hm
    exact ⟨(l1 - l2 + t1 - t2) / 2, by linarith, rfl, by linarith⟩
  · rintro ⟨k, hl, hm, ht⟩
    subst hm
    refine ⟨by linarith, rfl⟩

/-! ### 4π は選ばれていない：プランク電荷 -/

/-- SI（有理化）のプランク電荷 q_P = c√(4π/a) が c の純粋な冪になるのは a = 4π のときだけ。 -/
theorem planck_charge_SI (a : ℝ) (ha : 0 < a) :
    (∃ k : ℝ, ∀ c : ℝ, 0 < c → c * √(4 * π / a) = c ^ k) ↔ a = 4 * π := by
  constructor
  · rintro ⟨k, hk⟩
    have h1 := hk 1 one_pos
    rw [Real.one_rpow, one_mul, Real.sqrt_eq_one] at h1
    rw [div_eq_one_iff_eq (ne_of_gt ha)] at h1
    exact h1.symm
  · rintro rfl
    refine ⟨1, fun c _ => ?_⟩
    rw [div_self (by positivity), Real.sqrt_one, Real.rpow_one, mul_one]

/-- ガウス単位のプランク電荷 q_P = √(c/a) が c の純粋な冪になるのは a = 1 のときだけ。 -/
theorem planck_charge_Gauss (a : ℝ) (ha : 0 < a) :
    (∃ k : ℝ, ∀ c : ℝ, 0 < c → √(c / a) = c ^ k) ↔ a = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    have h1 := hk 1 one_pos
    rw [Real.one_rpow, Real.sqrt_eq_one, div_eq_one_iff_eq (ne_of_gt ha)] at h1
    exact h1.symm
  · rintro rfl
    exact ⟨1 / 2, fun c hc => by rw [div_one, Real.sqrt_eq_rpow]⟩

/-- SI の式の計算：ε₀ = c、ħ = 1/a のとき √(4π ε₀ ħ c) = c√(4π/a)。 -/
theorem planck_charge_SI_value (a c : ℝ) (hc : 0 < c) :
    √(4 * π * c * (1 / a) * c) = c * √(4 * π / a) := by
  have : 4 * π * c * (1 / a) * c = c ^ 2 * (4 * π / a) := by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]

end Paper116

end Yamagishi
