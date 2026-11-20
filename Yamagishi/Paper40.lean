/-
論文40『プランク単位の完全な展開』（第3版）の定理と事実を、機械に確かめさせる。

原稿（40_yamagishi_planck_unit_complete_unpacking/…_jp.tex）の
  定理2.1：l_p = √(ħG/c³)、t_p = √(ħG/c⁵)、m_p = √(ħc/G)、E_p = m_p c² とすると、
    ħ と G の値によらず l_p/t_p = c、E_p t_p = ħ（恒等式）。
  観察2.3：パッチを崩すと（G を 1.3 倍、ħ を 2 倍）四量の形は壊れるが、l_p/t_p = c は壊れない。
  事実3.1（論文116）：G = a、ħ = 1/a（a > 0 は任意）で四量は
    l_p = c^(−3/2)、t_p = c^(−5/2)、m_p = √c/a、E_p = c^(5/2)/a。
  観察3.2：ħ = 1/G なら ħ/G = 1/G²、m_p = √c/G（m_p の 4π は G の 4π を二乗して平方根に戻したもの）。
  事実4.1（論文116 の ε = μ）と表：四量の a の冪は質量次元（0, 0, 1, 1）。
  第5節：(ħ, G, c) の次元行列（行 L・M・T、列 ħ・G・c）の行列式は 2。
  定理5.1：指数 (p, q, N) は、分母 det A の有理数として一意に定まる。四量の 12 個の指数の分母はちょうど 2。

書き方：四量は教科書の定義（平方根）で置き、値は正の実数の計算として導いた。
観察2.3 は、数値の揺らし（c = 3.7 での確かめ）の代わりに、すべての c > 0 について
「l_p = c^(−3/2) が成り立つ ⇔ ħG = 1」という同値として示し、G を 1.3 倍・ħ を 2 倍にすると
どの c でも四量の形が壊れることを導いた。定理5.1 は、次元の指数 λ, μ, τ が整数なら
2p, 2q, 2N が整数になる（分母は 2 を割る）、という形で書いた。

形式化していないもの：「破れうるものだけが検算に値する」という検算の規律、「4π は名前の選択であって
結果ではない」「立体角としての意味は出てこない」という判断、SI の数値による照合（相対誤差 1.52×10⁻¹⁶ など）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper40

open Real

noncomputable def lp (hbar G c : ℝ) : ℝ := √(hbar * G / c ^ 3)
noncomputable def tp (hbar G c : ℝ) : ℝ := √(hbar * G / c ^ 5)
noncomputable def mp (hbar G c : ℝ) : ℝ := √(hbar * c / G)
noncomputable def Ep (hbar G c : ℝ) : ℝ := mp hbar G c * c ^ 2

/-- 正の数を二乗の形に書き直すための補題。 -/
theorem exists_sq (x : ℝ) (hx : 0 < x) : ∃ s, 0 < s ∧ x = s ^ 2 :=
  ⟨√x, Real.sqrt_pos.mpr hx, (Real.sq_sqrt hx.le).symm⟩

/-- s > 0 のとき (s²)^(k/2) = s^k（k は整数）。 -/
theorem sq_rpow_half (s : ℝ) (hs : 0 < s) (k : ℤ) : (s ^ 2) ^ ((k : ℝ) / 2) = s ^ k := by
  rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le]
  push_cast
  rw [show (2 : ℝ) * (k / 2) = k by ring, Real.rpow_intCast]

/-! ### 定理2.1：二つの恒等式 -/

/-- l_p/t_p = c と E_p t_p = ħ は、正の ħ・G・c のどんな値でも成り立つ。 -/
theorem two_identities (hbar G c : ℝ) (hh : 0 < hbar) (hG : 0 < G) (hc : 0 < c) :
    lp hbar G c / tp hbar G c = c ∧ Ep hbar G c * tp hbar G c = hbar := by
  obtain ⟨s, hs, rfl⟩ := exists_sq c hc
  obtain ⟨h, hh', rfl⟩ := exists_sq hbar hh
  obtain ⟨g, hg, rfl⟩ := exists_sq G hG
  have hl : lp (h ^ 2) (g ^ 2) (s ^ 2) = h * g / s ^ 3 := by
    rw [lp, show h ^ 2 * g ^ 2 / (s ^ 2) ^ 3 = (h * g / s ^ 3) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have ht : tp (h ^ 2) (g ^ 2) (s ^ 2) = h * g / s ^ 5 := by
    rw [tp, show h ^ 2 * g ^ 2 / (s ^ 2) ^ 5 = (h * g / s ^ 5) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have hm : mp (h ^ 2) (g ^ 2) (s ^ 2) = h * s / g := by
    rw [mp, show h ^ 2 * s ^ 2 / g ^ 2 = (h * s / g) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  constructor
  · rw [hl, ht]; field_simp
  · rw [Ep, hm, ht]; field_simp

/-! ### 事実3.1：パッチの下の四量（任意の a > 0） -/

theorem four_quantities (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    lp (1 / a) a c = c ^ ((-3 : ℝ) / 2) ∧
    tp (1 / a) a c = c ^ ((-5 : ℝ) / 2) ∧
    mp (1 / a) a c = √c / a ∧
    Ep (1 / a) a c = c ^ ((5 : ℝ) / 2) / a := by
  obtain ⟨s, hs, rfl⟩ := exists_sq c hc
  have e3 := sq_rpow_half s hs (-3)
  have e5 := sq_rpow_half s hs (-5)
  have e5' := sq_rpow_half s hs 5
  push_cast at e3 e5 e5'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lp, e3, show 1 / a * a / (s ^ 2) ^ 3 = (s ^ (-3 : ℤ)) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  · rw [tp, e5, show 1 / a * a / (s ^ 2) ^ 5 = (s ^ (-5 : ℤ)) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  · rw [mp, Real.sqrt_sq hs.le, show 1 / a * s ^ 2 / a = (s / a) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  · rw [Ep, mp, e5', show 1 / a * s ^ 2 / a = (s / a) ^ 2 by field_simp,
      Real.sqrt_sq (by positivity)]
    simp; ring

/-! ### 観察3.2：m_p の 4π は二つ目の 4π ではない -/

/-- ħ = 1/G なら ħ/G = 1/G² で、m_p = √c/G。 -/
theorem mp_of_hbar_inv_G (G c : ℝ) (hG : 0 < G) (hc : 0 < c) :
    (1 / G) / G = 1 / G ^ 2 ∧ mp (1 / G) G c = √c / G := by
  constructor
  · field_simp
  · rw [mp, show 1 / G * c / G = (√c / G) ^ 2 by
      rw [div_pow, Real.sq_sqrt hc.le]; field_simp]
    exact Real.sqrt_sq (by positivity)

/-! ### 観察2.3：パッチを崩すと、四量の形は壊れ、恒等式は壊れない -/

/-- l_p = c^(−3/2) が成り立つことと ħG = 1 は同値（どの c > 0 でも）。 -/
theorem lp_form_iff (hbar G c : ℝ) (hh : 0 < hbar) (hG : 0 < G) (hc : 0 < c) :
    lp hbar G c = c ^ ((-3 : ℝ) / 2) ↔ hbar * G = 1 := by
  obtain ⟨s, hs, rfl⟩ := exists_sq c hc
  have e3 := sq_rpow_half s hs (-3)
  push_cast at e3
  rw [lp, e3]
  have hpos : 0 < hbar * G := mul_pos hh hG
  constructor
  · intro h
    have h2 := congrArg (· ^ 2) h
    simp only [Real.sq_sqrt (by positivity : 0 ≤ hbar * G / (s ^ 2) ^ 3)] at h2
    have key : (s ^ (-3 : ℤ)) ^ 2 = 1 / (s ^ 2) ^ 3 := by field_simp
    rw [key, div_left_inj₀ (by positivity)] at h2
    exact h2
  · intro h
    rw [h, show 1 / (s ^ 2) ^ 3 = (s ^ (-3 : ℤ)) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)

/-- t_p = c^(−5/2) が成り立つことと ħG = 1 は同値。 -/
theorem tp_form_iff (hbar G c : ℝ) (hh : 0 < hbar) (hG : 0 < G) (hc : 0 < c) :
    tp hbar G c = c ^ ((-5 : ℝ) / 2) ↔ hbar * G = 1 := by
  obtain ⟨s, hs, rfl⟩ := exists_sq c hc
  have e5 := sq_rpow_half s hs (-5)
  push_cast at e5
  rw [tp, e5]
  constructor
  · intro h
    have h2 := congrArg (· ^ 2) h
    simp only [Real.sq_sqrt (by positivity : 0 ≤ hbar * G / (s ^ 2) ^ 5)] at h2
    have key : (s ^ (-5 : ℤ)) ^ 2 = 1 / (s ^ 2) ^ 5 := by field_simp
    rw [key, div_left_inj₀ (by positivity)] at h2
    exact h2
  · intro h
    rw [h, show 1 / (s ^ 2) ^ 5 = (s ^ (-5 : ℤ)) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)

/-- G を 1.3 倍、または ħ を 2 倍にすると、どの c > 0 でも l_p = c^(−3/2) と t_p = c^(−5/2) は
壊れ、l_p/t_p = c は壊れない。 -/
theorem perturbation (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (lp (1 / a) (1.3 * a) c ≠ c ^ ((-3 : ℝ) / 2) ∧
      tp (1 / a) (1.3 * a) c ≠ c ^ ((-5 : ℝ) / 2) ∧
      lp (1 / a) (1.3 * a) c / tp (1 / a) (1.3 * a) c = c) ∧
    (lp (2 * (1 / a)) a c ≠ c ^ ((-3 : ℝ) / 2) ∧
      tp (2 * (1 / a)) a c ≠ c ^ ((-5 : ℝ) / 2) ∧
      lp (2 * (1 / a)) a c / tp (2 * (1 / a)) a c = c) := by
  have h1 : (1 / a) * (1.3 * a) ≠ 1 := by field_simp; norm_num
  have h2 : (2 * (1 / a)) * a ≠ 1 := by field_simp; norm_num
  have p1 : 0 < 1 / a := by positivity
  have p2 : 0 < 1.3 * a := by positivity
  have p3 : 0 < 2 * (1 / a) := by positivity
  refine ⟨⟨?_, ?_, (two_identities _ _ _ p1 p2 hc).1⟩, ⟨?_, ?_, (two_identities _ _ _ p3 ha hc).1⟩⟩
  · rw [Ne, lp_form_iff _ _ _ p1 p2 hc]; exact h1
  · rw [Ne, tp_form_iff _ _ _ p1 p2 hc]; exact h1
  · rw [Ne, lp_form_iff _ _ _ p3 ha hc]; exact h2
  · rw [Ne, tp_form_iff _ _ _ p3 ha hc]; exact h2

/-- 同じ揺らしで m_p = √c/a の形も壊れる。 -/
theorem perturbation_mp (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    mp (1 / a) (1.3 * a) c ≠ √c / a ∧ mp (2 * (1 / a)) a c ≠ √c / a := by
  have hsc : 0 < √c := Real.sqrt_pos.mpr hc
  constructor
  · intro h
    have h2 := congrArg (· ^ 2) h
    rw [mp, Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt hc.le] at h2
    field_simp at h2
    nlinarith [h2]
  · intro h
    have h2 := congrArg (· ^ 2) h
    rw [mp, Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt hc.le] at h2
    field_simp at h2
    nlinarith [h2]

/-! ### 事実4.1 と第5節：ε = μ と、行列式 2 -/

/-- ε = μ（論文116）：G = a、ħ = 1/a の下で ħ^p G^q c^N = c^N / a^(p−q)。 -/
theorem eps_eq_mu (a c p q N : ℝ) (ha : 0 < a) :
    (1 / a) ^ p * a ^ q * c ^ N = c ^ N / a ^ (p - q) := by
  rw [one_div, Real.inv_rpow ha.le, Real.rpow_sub ha]
  field_simp

/-- 次元行列（行 L・M・T、列 ħ・G・c）。 -/
def A : Matrix (Fin 3) (Fin 3) ℚ := !![2, 3, 1; 1, -1, 0; -1, -2, -1]

theorem det_A : A.det = 2 := by
  simp [A, Matrix.det_fin_three]; norm_num

/-- 次元の照合（L・M・T の順）。 -/
def Matches (lam mu tau p q N : ℚ) : Prop :=
  2 * p + 3 * q + N = lam ∧ p - q = mu ∧ -p - 2 * q - N = tau

/-- 定理5.1：解は一意で、q = (λ+τ−μ)/2、p = μ + q、N = −(μ+τ) − 3q。 -/
theorem solution_unique (lam mu tau p q N : ℚ) :
    Matches lam mu tau p q N ↔
      (q = (lam + tau - mu) / 2 ∧ p = mu + q ∧ N = -(mu + tau) - 3 * q) := by
  unfold Matches
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; refine ⟨by linarith, by linarith, by linarith⟩

/-- 定理5.1（分母）：λ, μ, τ が整数なら、2p, 2q, 2N は整数（指数の分母は det A = 2 を割る）。 -/
theorem denominators_divide_two (lam mu tau : ℤ) (p q N : ℚ)
    (h : Matches lam mu tau p q N) :
    ∃ P Q M : ℤ, 2 * p = P ∧ 2 * q = Q ∧ 2 * N = M := by
  obtain ⟨hq, hp, hN⟩ := (solution_unique _ _ _ p q N).mp h
  refine ⟨2 * mu + (lam + tau - mu), lam + tau - mu, -2 * (mu + tau) - 3 * (lam + tau - mu),
    ?_, ?_, ?_⟩
  · rw [hp, hq]; push_cast; ring
  · rw [hq]; push_cast; ring
  · rw [hN, hq]; push_cast; ring

/-- 四量の指数（l_p、t_p、m_p、E_p）が次元の照合を満たすこと。 -/
theorem four_exponents :
    Matches 1 0 0 (1/2) (1/2) (-3/2) ∧ Matches 0 0 1 (1/2) (1/2) (-5/2) ∧
    Matches 0 1 0 (1/2) (-1/2) (1/2) ∧ Matches 2 1 (-2) (1/2) (-1/2) (5/2) := by
  unfold Matches; norm_num

/-- 12 個の指数の分母がちょうど 2 であること：どれも 2 倍すると奇数の整数になる
（整数ではなく、2 倍で整数になるので、既約分数の分母は 2）。 -/
theorem four_exponents_den :
    ([1/2, 1/2, -3/2, 1/2, 1/2, -5/2, 1/2, -1/2, 1/2, 1/2, -1/2, 5/2] : List ℚ).map (2 * ·)
      = [1, 1, -3, 1, 1, -5, 1, -1, 1, 1, -1, 5] := by
  norm_num

/-- 表：四量の質量次元 μ = p − q は (0, 0, 1, 1)。 -/
theorem four_mass_dims :
    ((1:ℚ)/2 - 1/2, (1:ℚ)/2 - 1/2, (1:ℚ)/2 - (-1/2), (1:ℚ)/2 - (-1/2)) = (0, 0, 1, 1) := by
  norm_num

end Paper40

end Yamagishi
