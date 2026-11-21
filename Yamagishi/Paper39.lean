/-
論文39『山岸・プランク長 l_p = c^(−3/2) 幾何解凍理論』（第4版）の定理と事実を、機械に確かめさせる。

原稿（39_yamagishi_planck_length_pixel/…_jp.tex）の
  定理2.1：G = 4π、ħ = 1/(4π) で ħG = 1、l_p = √(ħG/c³) = c^(−3/2)。
  事実3.1：ħ・G・c・m の次元（M, L, T の指数）から三つを選ぶ四通りの行列式の絶対値は 2・1・1・1。
  系3.2：四つ目は規約ではない（基本次元は三つ）。
  観察3.3：c = 1 なら l_p = 1。
  第4.1節：l_p = ħ^a G^b c^d の (a, b, d) は (1/2, 1/2, −3/2) ただ一通り。四量の表。
  定理4.2：|det A| = 2、A⁻¹ の分母は 2 を割る、不変因子は (1, 1, 2)、
    A⁻¹ の行は (1/2, −1/2, 1/2)・(1/2, 1/2, −3/2)・(1/2, 1/2, −5/2)。diag(2,2) の反例。
  観察4.3：基底 (G, m, c) では行列式 1、指数は整数（Gm/c²・Gm/c³・m・mc²）。
  第6節：ħG = 1 を望めば ħ = 1/(4π) しかない。h = 2πħ = 1/2。

書き方：
・次元の行列 R は「行が量（ħ, G, c）、列が次元（M, L, T）」で置いた。原稿の事実3.1 の並べ方
  （ħ:(1,2,−1) …）をそのまま行にしたもの。この向きでは、量 ħ^a G^b c^d の次元は
  行ベクトルの積 (a, b, d)·R で、次元 D の量の指数は D·R⁻¹、つまり R⁻¹ の「行」が質量・長さ・時間の
  指数になる（原稿の「行」はこの向きで正しい）。行列を転置して「列が量」で置くと、同じ三つは
  逆行列の「列」になる。両方を定理として書いた（`inv_rows`・`inv_cols_of_transpose`）。
・「四つ目は主張になる」は、四つの次元の間に整数の関係がただ一つ（定数倍を除いて）あり、
  無次元の組 ħc/(Gm²) が単位の取り直しで動かない、という形で書いた（単位の取り直しで数がどう動くかは
  論文1132 と同じ Bridgman の規則を入力として置いた）。
・不変因子 (1, 1, 2) は、行列式 ±1 の整数行列 P, Q で P R Q = diag(1, 1, 2) となる組を具体的に示す形
  （スミス標準形の証明書）で書いた。分母がちょうど 2 であることは、
  「どの整数の次元でも指数を 2 倍すれば整数」「質量の次元は整数の指数では作れない」の二つで書いた。

形式化していないもの：ケプラーの 3/2 との区別（第5節）、惑星の表と残差の読み、「最小の長さではない」
「モジュールの境界」（第7節）、「4π は G の逆数にすぎず立体角の 4π と無関係」という読み
（数の上で ħ = 1/G であることだけは書いた）。スミス標準形の一意性（Mathlib の一般論）には頼らず、
具体的な P, Q を示すにとどめた。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper39

open Real

/-! ### 定理2.1：ħG = 1 の相殺と l_p = c^(−3/2) -/

noncomputable def lp (hbar G c : ℝ) : ℝ := √(hbar * G / c ^ 3)

/-- 定理2.1：G = 4π、ħ = 1/(4π) のもとで ħG = 1、そして c > 0 なら l_p = c^(−3/2)。 -/
theorem thm_cancel (c : ℝ) (hc : 0 < c) :
    (1 / (4 * π)) * (4 * π) = 1 ∧ lp (1 / (4 * π)) (4 * π) c = c ^ (-(3 : ℝ) / 2) := by
  have h1 : (1 / (4 * π)) * (4 * π) = 1 := by
    field_simp
  refine ⟨h1, ?_⟩
  have hpos : 0 < c ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hc _
  rw [lp, h1, ← Real.sqrt_sq hpos.le]
  congr 1
  rw [← Real.rpow_natCast (c ^ (-(3 : ℝ) / 2)) 2, ← Real.rpow_mul hc.le]
  norm_num

/-- 観察3.3：残る一つを c = 1 に使えば l_p = 1（プランク長が長さの単位になる）。 -/
theorem lp_at_c_one : lp (1 / (4 * π)) (4 * π) 1 = 1 := by
  rw [(thm_cancel 1 one_pos).2, Real.one_rpow]

/-- 第6節：G = 4π と決めたあと ħG = 1 を望めば、ħ は 1/(4π) 以外にない（ħ は G の逆数）。 -/
theorem hbar_forced (hbar : ℝ) (h : hbar * (4 * π) = 1) : hbar = 1 / (4 * π) := by
  have : (4 * π) ≠ 0 := by positivity
  field_simp
  linarith

/-- 第6節：この置き方で h = 2πħ = 1/2。 -/
theorem planck_h : 2 * π * (1 / (4 * π)) = 1 / 2 := by
  field_simp
  ring

/-! ### 事実3.1：四つの三つ組の行列式

次元の指数は (M, L, T) の順：ħ = (1, 2, −1)、G = (−1, 3, −2)、c = (0, 1, −1)、m = (1, 0, 0)。
行列は「行が量」で置く。 -/

def dimHbar : Fin 3 → ℚ := ![1, 2, -1]
def dimG : Fin 3 → ℚ := ![-1, 3, -2]
def dimC : Fin 3 → ℚ := ![0, 1, -1]
def dimM : Fin 3 → ℚ := ![1, 0, 0]

/-- (ħ, G, c) の次元の行列（行が量、列が M・L・T）。 -/
def R : Matrix (Fin 3) (Fin 3) ℚ := !![1, 2, -1; -1, 3, -2; 0, 1, -1]
/-- (ħ, G, m) -/
def R_hGm : Matrix (Fin 3) (Fin 3) ℚ := !![1, 2, -1; -1, 3, -2; 1, 0, 0]
/-- (ħ, c, m) -/
def R_hcm : Matrix (Fin 3) (Fin 3) ℚ := !![1, 2, -1; 0, 1, -1; 1, 0, 0]
/-- (G, c, m)：論文38 の基底 -/
def R_Gcm : Matrix (Fin 3) (Fin 3) ℚ := !![-1, 3, -2; 0, 1, -1; 1, 0, 0]

/-- 事実3.1 の表：行列式は −2・−1・−1・−1（絶対値 2・1・1・1）。どれも 0 でない。 -/
theorem four_triples_det :
    R.det = -2 ∧ R_hGm.det = -1 ∧ R_hcm.det = -1 ∧ R_Gcm.det = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [R, R_hGm, R_hcm, R_Gcm, Matrix.det_fin_three] <;> norm_num

/-- 事実3.1 の結び：行列式が 0 でないので、どの三つ組でも、単位の取り直し（の対数）を一通りに選んで
三つの数を任意の値へ同時に動かせる。対数の形で「どの b にも、R v = b となる v がただ一つある」。 -/
theorem triple_independent (b : Fin 3 → ℚ) :
    (∃! v : Fin 3 → ℚ, R.mulVec v = b) ∧ (∃! v : Fin 3 → ℚ, R_hGm.mulVec v = b) ∧
    (∃! v : Fin 3 → ℚ, R_hcm.mulVec v = b) ∧ (∃! v : Fin 3 → ℚ, R_Gcm.mulVec v = b) := by
  obtain ⟨h1, h2, h3, h4⟩ := four_triples_det
  have key : ∀ A : Matrix (Fin 3) (Fin 3) ℚ, A.det ≠ 0 → ∃! v, A.mulVec v = b := by
    intro A hA
    have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    refine ⟨A⁻¹.mulVec b, ?_, ?_⟩
    · simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu]
    · intro v hv
      rw [← hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  refine ⟨key _ ?_, key _ ?_, key _ ?_, key _ ?_⟩ <;> simp [h1, h2, h3, h4]

/-! ### 系3.2：四つ目は規約ではない -/

/-- 四つの次元の間の整数（有理数）の関係は、(1, −1, 1, −2) の定数倍だけ：
a·[ħ] + b·[G] + e·[c] + f·[m] = 0 ⇔ (a, b, e, f) = t (1, −1, 1, −2)。
つまり ħc/(Gm²) だけが無次元の組で、四つを独立には動かせない。 -/
theorem four_dims_relation (a b e f : ℚ) :
    (∀ i, a * dimHbar i + b * dimG i + e * dimC i + f * dimM i = 0) ↔
      (b = -a ∧ e = a ∧ f = -2 * a) := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp [dimHbar, dimG, dimC, dimM] at h0 h1 h2
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hb, he, hf⟩ i
    subst hb he hf
    fin_cases i <;> simp [dimHbar, dimG, dimC, dimM] <;> ring

/-- 単位の取り直し（質量 x 倍・長さ y 倍・時間 z 倍）で、次元 M^μ L^λ T^τ の量の数は
x^(−μ) y^(−λ) z^(−τ) 倍になる（Bridgman の規則。論文1132 と同じく入力として置く）。 -/
noncomputable def factor (x y z mu lam tau : ℝ) : ℝ := x ^ (-mu) * y ^ (-lam) * z ^ (-tau)

/-- 系3.2：ħc/(Gm²) の数は、どの取り直しでも動かない。だから (ħ, G, c) の三つで単位を決めたあと、
m に値を課すことは単位の選択ではなく、この無次元の数についての主張になる。 -/
theorem dimensionless_invariant (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    factor x y z 1 2 (-1) * factor x y z 0 1 (-1) /
      (factor x y z (-1) 3 (-2) * factor x y z 1 0 0 ^ 2) = 1 := by
  unfold factor
  simp only [neg_neg, neg_zero, Real.rpow_zero, mul_one]
  have ex : ∀ (w : ℝ) (_ : 0 < w), w ^ (-(1:ℝ)) * w ^ (1:ℝ) = 1 := by
    intro w hw
    rw [← Real.rpow_add hw]; norm_num
  have hx1 : x ^ (-(1:ℝ)) = x⁻¹ := by rw [Real.rpow_neg_one]
  have hy2 : y ^ (-(2:ℝ)) = (y ^ 2)⁻¹ := by rw [Real.rpow_neg hy.le]; norm_cast
  have hy1 : y ^ (-(1:ℝ)) = y⁻¹ := by rw [Real.rpow_neg_one]
  have hy3 : y ^ (-(3:ℝ)) = (y ^ 3)⁻¹ := by rw [Real.rpow_neg hy.le]; norm_cast
  have hz2 : z ^ (2:ℝ) = z ^ 2 := by norm_cast
  simp only [Real.rpow_one, hx1, hy2, hy1, hy3, hz2]
  field_simp

/-! ### 第4.1節：指数 3/2 は次元方程式の唯一解 -/

/-- 量 ħ^a G^b c^d が次元 (μ, λ, τ) を持つ条件（成分ごと）。 -/
def Matches (mu lam tau a b d : ℚ) : Prop :=
  a - b = mu ∧ 2 * a + 3 * b + d = lam ∧ -a - 2 * b - d = tau

/-- 一般の解：M から a − b = μ、L と T を足して a + b = λ + τ。ただ一通りに決まる。 -/
theorem exponents_unique (mu lam tau a b d : ℚ) :
    Matches mu lam tau a b d ↔
      (a = (mu + lam + tau) / 2 ∧ b = (lam + tau - mu) / 2 ∧ d = (mu - 3 * lam - 5 * tau) / 2) := by
  unfold Matches
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, by linarith, by linarith⟩

/-- 第4.1節：長さ (0, 1, 0) の指数は (1/2, 1/2, −3/2) ただ一通り。 -/
theorem length_exponents (a b d : ℚ) : Matches 0 1 0 a b d ↔ (a = 1/2 ∧ b = 1/2 ∧ d = -3/2) := by
  unfold Matches
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- 第4.1節の表：長さ・時間・質量・エネルギーの指数。 -/
theorem four_table :
    Matches 0 1 0 (1/2) (1/2) (-3/2) ∧ Matches 0 0 1 (1/2) (1/2) (-5/2) ∧
    Matches 1 0 0 (1/2) (-1/2) (1/2) ∧ Matches 1 2 (-2) (1/2) (-1/2) (5/2) := by
  unfold Matches; norm_num

/-! ### 定理4.2：半整数の出どころ -/

/-- R の逆行列。行は（上から）質量・長さ・時間の指数 (a, b, d)。 -/
def Rinv : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1/2, -1/2, 1/2; 1/2, 1/2, -3/2; 1/2, 1/2, -5/2]

theorem Rinv_mul_R : Rinv * R = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Rinv, R, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem R_mul_Rinv : R * Rinv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Rinv, R, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem R_inv_eq : R⁻¹ = Rinv := Matrix.inv_eq_left_inv Rinv_mul_R

/-- 定理4.2：行が量の向きで置くと、R⁻¹ の行は (1/2, −1/2, 1/2)、(1/2, 1/2, −3/2)、(1/2, 1/2, −5/2)、
そしてそれぞれ質量・長さ・時間の指数（行ベクトル (a, b, d)·R が次元になる）。 -/
theorem inv_rows :
    R⁻¹ 0 = ![1/2, -1/2, 1/2] ∧ R⁻¹ 1 = ![1/2, 1/2, -3/2] ∧ R⁻¹ 2 = ![1/2, 1/2, -5/2] ∧
    Matrix.vecMul (R⁻¹ 0) R = ![1, 0, 0] ∧ Matrix.vecMul (R⁻¹ 1) R = ![0, 1, 0] ∧
    Matrix.vecMul (R⁻¹ 2) R = ![0, 0, 1] := by
  rw [R_inv_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext j; fin_cases j <;>
      simp [Rinv, R, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> norm_num)

/-- 同じ行列を転置して「列が量」で置くと、三つは逆行列の「列」になる。 -/
theorem inv_cols_of_transpose :
    (fun i => (R.transpose)⁻¹ i 0) = ![1/2, -1/2, 1/2] ∧
    (fun i => (R.transpose)⁻¹ i 1) = ![1/2, 1/2, -3/2] ∧
    (fun i => (R.transpose)⁻¹ i 2) = ![1/2, 1/2, -5/2] := by
  rw [← Matrix.transpose_nonsing_inv, R_inv_eq]
  refine ⟨?_, ?_, ?_⟩ <;> (ext j; fin_cases j <;> simp [Rinv])

/-- 定理4.2（上界）：A⁻¹ = adj(A)/det A なので、分母は |det A| = 2 を割る：2·R⁻¹ は整数の行列。 -/
theorem two_inv_integer : ∀ i j, ∃ n : ℤ, 2 * R⁻¹ i j = n := by
  rw [R_inv_eq]
  intro i j
  refine ⟨(!![1, -1, 1; 1, 1, -3; 1, 1, -5] : Matrix (Fin 3) (Fin 3) ℤ) i j, ?_⟩
  fin_cases i <;> fin_cases j <;> norm_num [Rinv]

/-- 定理4.2（分母は 2 より小さくならない）：質量の次元 (1, 0, 0) は、整数の指数では作れない。 -/
theorem mass_not_integer (a b d : ℤ) : ¬ Matches 1 0 0 a b d := by
  unfold Matches
  rintro ⟨h1, h2, h3⟩
  have : (2 : ℚ) * a = 1 := by linarith
  have h' : (2 : ℤ) * a = 1 := by exact_mod_cast this
  omega

/-- 整数の次元なら、指数を 2 倍すれば整数（四量に限らず、すべての量で）。 -/
theorem all_denominators_divide_two (mu lam tau : ℤ) (a b d : ℚ) (h : Matches mu lam tau a b d) :
    ∃ A B D : ℤ, 2 * a = A ∧ 2 * b = B ∧ 2 * d = D := by
  unfold Matches at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨mu + lam + tau, lam + tau - mu, mu - 3 * lam - 5 * tau, ?_, ?_, ?_⟩ <;>
    push_cast <;> linarith

/-- スミス標準形の証明書：行列式 ±1 の整数行列 P, Q で P R Q = diag(1, 1, 2)（det P = 1、det Q = −1）。
したがって不変因子は (1, 1, 2)、余核は ℤ/2。 -/
def P : Matrix (Fin 3) (Fin 3) ℤ := !![-1, -1, 0; -1, 0, -1; -1, -1, -1]
def Q : Matrix (Fin 3) (Fin 3) ℤ := !![0, -1, 1; -2, 0, 3; -3, 0, 5]
def RZ : Matrix (Fin 3) (Fin 3) ℤ := !![1, 2, -1; -1, 3, -2; 0, 1, -1]

theorem smith_certificate :
    P * RZ * Q = Matrix.diagonal ![1, 1, 2] ∧ P.det = 1 ∧ Q.det = -1 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · simp [P, Matrix.det_fin_three]
  · simp [Q, Matrix.det_fin_three]

/-- 論文149 の反例：diag(2, 2) は行列式 4 だが、逆行列の成分は 1/2 と 0 だけ（分母は 2）。 -/
theorem diag_two_two :
    (Matrix.diagonal ![(2 : ℚ), 2]).det = 4 ∧
    (Matrix.diagonal ![(2 : ℚ), 2])⁻¹ = Matrix.diagonal ![1/2, 1/2] := by
  constructor
  · simp [Matrix.det_diagonal, Fin.prod_univ_two]; norm_num
  · apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

/-! ### 観察4.3：基底 (G, m, c) では指数が整数 -/

/-- (G, m, c) の行列（行が量）。 -/
def S : Matrix (Fin 3) (Fin 3) ℚ := !![-1, 3, -2; 1, 0, 0; 0, 1, -1]
/-- その逆行列（整数）。行は質量・長さ・時間の指数。 -/
def Sinv : Matrix (Fin 3) (Fin 3) ℚ := !![0, 1, 0; 1, 1, -2; 1, 1, -3]

theorem S_det : S.det = 1 := by simp [S, Matrix.det_fin_three]; norm_num

theorem S_inv_eq : S⁻¹ = Sinv := by
  apply Matrix.inv_eq_left_inv
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Sinv, S, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-- 観察4.3 の表：長さ Gm/c²、時間 Gm/c³、質量 m、エネルギー mc²（指数は整数）。 -/
theorem Gmc_table :
    Matrix.vecMul ![1, 1, -2] S = ![0, 1, 0] ∧ Matrix.vecMul ![1, 1, -3] S = ![0, 0, 1] ∧
    Matrix.vecMul ![0, 1, 0] S = ![1, 0, 0] ∧ Matrix.vecMul ![0, 1, 2] S = ![1, 2, -2] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext j; fin_cases j <;> norm_num [S, Matrix.vecMul, dotProduct, Fin.sum_univ_three])

end Paper39

end Yamagishi
