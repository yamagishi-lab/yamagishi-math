/-
論文1130『山岸の 4π-質量次元パリティ則（Yamagishi 4π-Mass Invariant）』の定理を、
帳簿（指数の組）の言葉で機械に確かめさせる。

原稿（1130_…/…_jp.tex）の第2節〜第5節：
  量 X = (4π)^ρ ħ^p G^q c^N m^r M^u Z（m は 4π と置いた質量、M は置かない質量、
  Z は長さ・時間・速さ・個数のように 4π も質量も持たない量）。冪は整数でも分数でもよい。
  置き方は G = a、ħ = 1/a、置いた質量 m = a、じかの 4π = a（a = 4π を文字として扱う）。
  ε = 置き方を入れた値に立つ a の冪（分子を正に数える）、μ = 標準の式の次元の質量の冪。
  定理（一）ε + μ = 2r + u + ρ
      （二）G を一つ掛けると (ε, μ) が (+1, −1)、ħ は (−1, +1)、c は (0, 0) 動き、
            ε + μ は G・ħ・c を何度掛けても割っても変わらない。和を変えるのは
            置いた質量（一つで 2）、置かない質量（1）、じかの 4π（1）だけ。
      （三）r・u・ρ が整数なら、ε + μ と u + ρ は偶奇が同じ。
  第4節：両端（パッチだけなら ε = −μ、置いた質量と c だけなら ε = +μ）、
         ε − μ = 2(q − p) − u + ρ、u = ρ = 0 のときの読み戻し。
  第5節：置かない定数 Y（重み μ_Y）へ広げた ε + μ = 2r + u + ρ + U、偶奇の広がり、
         質量次元 μ_Y の定数を (4π)^s と置いた重み s + μ_Y が 0 になるのは s = −μ_Y だけ。

書き方：因子ごとの（a の冪、質量次元）を原稿の表のとおり入力として置き、
ε と μ は「因子ごとの冪に指数を掛けて足したもの」と定義した（原稿の証明の一行目そのもの）。
帳簿の式 ε = ρ − p + q + r などは定義ではなく、そこから導いた補題である。
さらに、置き方を入れた実数の値 (1/a)^p a^q c^N a^r M^u a^ρ が a^ε c^N M^u に等しいことを、
任意の正の a・c・M について実数の冪の計算として確かめた（`value_eq`）。
因子の表の質量次元は、ħ = M L² T⁻¹、G = M⁻¹ L³ T⁻²、c = L T⁻¹ の M の冪として、
三つの次元（質量・長さ・時間）のまま置いた。

形式化していないもの：どの式のどの 4π を ρ・r・u のどれに数えるかという割り振り（読み）、
第6節の点呼（既刊の 30 本と 26 か所への当てはめ）、ε₀ の扱い（SI の読みでの質量次元 −1 は
置かない定数の一つとして入力すれば扱えるが、その読みの正しさは形式化していない）、
「4π は立体角」などの物理の読み。Z（長さ・時間・速さ・個数）は ε にも μ にも 0 を足すので、
長さと時間の冪だけを持つ因子として入れた。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1130

/-- 次元（質量・長さ・時間の冪）。 -/
structure Dim where
  M : ℚ
  L : ℚ
  T : ℚ
deriving DecidableEq

/-- 帳簿の因子。 -/
inductive Factor
  | hbar        -- ħ（置き方 1/a）
  | G           -- G（置き方 a）
  | c           -- c（置かない・質量次元 0）
  | placedMass  -- 4π と置いた質量 m（置き方 a）
  | freeMass    -- 置かない質量 M
  | fourPi      -- 式にじかに立つ 4π（a）
  | length      -- Z の長さ
  | time        -- Z の時間
deriving DecidableEq

open Factor

/-- 原稿の表の「ε」列：置き方を入れた因子の値に立つ a（= 4π）の冪。 -/
def epsOf : Factor → ℚ
  | hbar => -1
  | G => 1
  | c => 0
  | placedMass => 1
  | freeMass => 0
  | fourPi => 1
  | length => 0
  | time => 0

/-- 標準の式の次元。 -/
def dimOf : Factor → Dim
  | hbar => ⟨1, 2, -1⟩
  | G => ⟨-1, 3, -2⟩
  | c => ⟨0, 1, -1⟩
  | placedMass => ⟨1, 0, 0⟩
  | freeMass => ⟨1, 0, 0⟩
  | fourPi => ⟨0, 0, 0⟩
  | length => ⟨0, 1, 0⟩
  | time => ⟨0, 0, 1⟩

/-- 原稿の表の「μ」列：因子の質量次元。 -/
def muOf (f : Factor) : ℚ := (dimOf f).M

/-- 量 X = (4π)^ρ ħ^p G^q c^N m^r M^u Z の指数の組（Z は長さの冪 zL と時間の冪 zT）。 -/
structure Ledger where
  ρ : ℚ
  p : ℚ
  q : ℚ
  N : ℚ
  r : ℚ
  u : ℚ
  zL : ℚ := 0
  zT : ℚ := 0

/-- 因子ごとの指数。 -/
def Ledger.exp (X : Ledger) : Factor → ℚ
  | hbar => X.p
  | G => X.q
  | c => X.N
  | placedMass => X.r
  | freeMass => X.u
  | fourPi => X.ρ
  | length => X.zL
  | time => X.zT

/-- 因子の一覧。 -/
def factors : List Factor := [hbar, G, c, placedMass, freeMass, fourPi, length, time]

/-- 値の a の冪 ε：因子ごとの冪に指数を掛けて足したもの。 -/
def eps (X : Ledger) : ℚ := (factors.map fun f => X.exp f * epsOf f).sum

/-- 質量次元 μ：因子ごとの質量次元に指数を掛けて足したもの。 -/
def mu (X : Ledger) : ℚ := (factors.map fun f => X.exp f * muOf f).sum

/-- 量の積（指数の和）。 -/
instance : Mul Ledger where
  mul X Y := ⟨X.ρ + Y.ρ, X.p + Y.p, X.q + Y.q, X.N + Y.N, X.r + Y.r, X.u + Y.u,
    X.zL + Y.zL, X.zT + Y.zT⟩

/-- 量の逆数（指数の符号を変える）。 -/
instance : Inv Ledger where
  inv X := ⟨-X.ρ, -X.p, -X.q, -X.N, -X.r, -X.u, -X.zL, -X.zT⟩

/-- 一つの因子だけの量。 -/
def single (f : Factor) (k : ℚ) : Ledger :=
  match f with
  | hbar => ⟨0, k, 0, 0, 0, 0, 0, 0⟩
  | G => ⟨0, 0, k, 0, 0, 0, 0, 0⟩
  | c => ⟨0, 0, 0, k, 0, 0, 0, 0⟩
  | placedMass => ⟨0, 0, 0, 0, k, 0, 0, 0⟩
  | freeMass => ⟨0, 0, 0, 0, 0, k, 0, 0⟩
  | fourPi => ⟨k, 0, 0, 0, 0, 0, 0, 0⟩
  | length => ⟨0, 0, 0, 0, 0, 0, k, 0⟩
  | time => ⟨0, 0, 0, 0, 0, 0, 0, k⟩

/-! ### 因子の表から出る、ε と μ の式（原稿の証明の一行目） -/

theorem eps_formula (X : Ledger) : eps X = X.ρ - X.p + X.q + X.r := by
  simp [eps, factors, Ledger.exp, epsOf]; ring

theorem mu_formula (X : Ledger) : mu X = X.p - X.q + X.r + X.u := by
  simp [mu, factors, Ledger.exp, muOf, dimOf]; ring

/-- 値は因子の値の積なので、ε も μ も積で足し算になる。 -/
theorem eps_mul (X Y : Ledger) : eps (X * Y) = eps X + eps Y := by
  simp only [eps_formula]; show (X.ρ + Y.ρ) - (X.p + Y.p) + (X.q + Y.q) + (X.r + Y.r) = _; ring

theorem mu_mul (X Y : Ledger) : mu (X * Y) = mu X + mu Y := by
  simp only [mu_formula]; show (X.p + Y.p) - (X.q + Y.q) + (X.r + Y.r) + (X.u + Y.u) = _; ring

theorem eps_inv (X : Ledger) : eps X⁻¹ = - eps X := by
  simp only [eps_formula]; show -X.ρ - -X.p + -X.q + -X.r = _; ring

theorem mu_inv (X : Ledger) : mu X⁻¹ = - mu X := by
  simp only [mu_formula]; show -X.p - -X.q + -X.r + -X.u = _; ring

/-! ### 定理（一）帳簿の式 -/

/-- 定理（一）：ε + μ = 2r + u + ρ。 -/
theorem ledger_identity (X : Ledger) : eps X + mu X = 2 * X.r + X.u + X.ρ := by
  rw [eps_formula, mu_formula]; ring

/-! ### 定理（二）不変 -/

/-- G を一つ掛けると (ε, μ) は (+1, −1) 動く。 -/
theorem mul_G (X : Ledger) :
    eps (X * single G 1) = eps X + 1 ∧ mu (X * single G 1) = mu X - 1 := by
  constructor
  · rw [eps_mul]; simp [eps_formula, single]
  · rw [mu_mul]; simp [mu_formula, single]; ring

/-- ħ を一つ掛けると (ε, μ) は (−1, +1) 動く。 -/
theorem mul_hbar (X : Ledger) :
    eps (X * single hbar 1) = eps X - 1 ∧ mu (X * single hbar 1) = mu X + 1 := by
  constructor
  · rw [eps_mul]; simp [eps_formula, single]; ring
  · rw [mu_mul]; simp [mu_formula, single]

/-- c を掛けても (ε, μ) は動かない。 -/
theorem mul_c (X : Ledger) :
    eps (X * single c 1) = eps X ∧ mu (X * single c 1) = mu X := by
  constructor
  · rw [eps_mul]; simp [eps_formula, single]
  · rw [mu_mul]; simp [mu_formula, single]

/-- 定理（二）：G・ħ・c を何度掛けても割っても（冪が分数でも）ε + μ は変わらない。 -/
theorem invariant_under_G_hbar_c (X : Ledger) (kG kh kc : ℚ) :
    eps (X * single G kG * single hbar kh * single c kc)
      + mu (X * single G kG * single hbar kh * single c kc) = eps X + mu X := by
  simp only [eps_mul, mu_mul]
  simp [eps_formula, mu_formula, single]; ring

/-- 和を変えるのは、置いた質量（一つで 2）、置かない質量（1）、じかの 4π（1）だけ。 -/
theorem weight_placedMass (X : Ledger) :
    eps (X * single placedMass 1) + mu (X * single placedMass 1) = eps X + mu X + 2 := by
  simp only [eps_mul, mu_mul]; simp [eps_formula, mu_formula, single]; ring

theorem weight_freeMass (X : Ledger) :
    eps (X * single freeMass 1) + mu (X * single freeMass 1) = eps X + mu X + 1 := by
  simp only [eps_mul, mu_mul]; simp [eps_formula, mu_formula, single]; ring

theorem weight_fourPi (X : Ledger) :
    eps (X * single fourPi 1) + mu (X * single fourPi 1) = eps X + mu X + 1 := by
  simp only [eps_mul, mu_mul]; simp [eps_formula, mu_formula, single]; ring

/-- Z（長さ・時間）は和を動かさない。 -/
theorem weight_length_time (X : Ledger) (kL kT : ℚ) :
    eps (X * single length kL * single time kT) + mu (X * single length kL * single time kT)
      = eps X + mu X := by
  simp only [eps_mul, mu_mul]; simp [eps_formula, mu_formula, single]

/-- 割れば同じだけ減る。 -/
theorem weight_inv_placedMass (X : Ledger) :
    eps (X * (single placedMass 1)⁻¹) + mu (X * (single placedMass 1)⁻¹) = eps X + mu X - 2 := by
  simp only [eps_mul, mu_mul, eps_inv, mu_inv]; simp [eps_formula, mu_formula, single]; ring

/-! ### 定理（三）パリティ -/

/-- 定理（三）：r・u・ρ が整数なら、ε + μ は整数で、u + ρ と偶奇が同じ。 -/
theorem parity (X : Ledger) (r u ρ : ℤ) (hr : X.r = r) (hu : X.u = u) (hρ : X.ρ = ρ) :
    eps X + mu X = ((2 * r + u + ρ : ℤ) : ℚ) ∧ (2 * r + u + ρ) % 2 = (u + ρ) % 2 := by
  refine ⟨?_, ?_⟩
  · rw [ledger_identity, hr, hu, hρ]; push_cast; ring
  · omega

/-- 第7節の使い方：質量が整数乗で入り、置かない質量が無い（u = 0）なら、
ε + μ が奇数であることと、じかの 4π の冪 ρ が奇数であることは同値。 -/
theorem odd_weight_iff_odd_rho (X : Ledger) (r ρ : ℤ) (hr : X.r = r) (hu : X.u = 0)
    (hρ : X.ρ = ρ) : eps X + mu X = ((2 * r + ρ : ℤ) : ℚ) ∧ (Odd (2 * r + ρ) ↔ Odd ρ) := by
  refine ⟨?_, ?_⟩
  · rw [ledger_identity, hr, hu, hρ]; push_cast; ring
  · rw [Int.odd_add']
    simp

/-! ### 第4節：両端と、対になる量 -/

/-- パッチだけの量（r = u = ρ = 0）では ε = −μ。 -/
theorem patch_end (X : Ledger) (hr : X.r = 0) (hu : X.u = 0) (hρ : X.ρ = 0) :
    eps X = - mu X := by
  have := ledger_identity X; rw [hr, hu, hρ] at this; linarith

/-- 置いた質量と c（と Z）だけの量（p = q = u = ρ = 0）では ε = r = μ。 -/
theorem mass_end (X : Ledger) (hp : X.p = 0) (hq : X.q = 0) (hu : X.u = 0) (hρ : X.ρ = 0) :
    eps X = X.r ∧ mu X = X.r := by
  rw [eps_formula, mu_formula, hp, hq, hu, hρ]; constructor <;> ring

/-- 対になる量：ε − μ = 2(q − p) − u + ρ（置いた質量の冪 r を含まない）。 -/
theorem dual_identity (X : Ledger) : eps X - mu X = 2 * (X.q - X.p) - X.u + X.ρ := by
  rw [eps_formula, mu_formula]; ring

/-- 読み戻し：u = ρ = 0 なら r = (ε + μ)/2、q − p = (ε − μ)/2。 -/
theorem read_back (X : Ledger) (hu : X.u = 0) (hρ : X.ρ = 0) :
    X.r = (eps X + mu X) / 2 ∧ X.q - X.p = (eps X - mu X) / 2 := by
  rw [eps_formula, mu_formula, hu, hρ]; constructor <;> ring

/-! ### 第5節：置かない定数へ広げる -/

/-- 置かない定数 Y の族（添字 ι）をもつ量：Y は値に a を持ち込まず、質量次元 μY だけを運ぶ。 -/
structure LedgerY (ι : Type) [Fintype ι] where
  base : Ledger
  nY : ι → ℚ      -- Y の冪
  muY : ι → ℚ     -- Y の質量次元

variable {ι : Type} [Fintype ι]

/-- 置かない定数は値の a の冪に 0 を足す。 -/
def LedgerY.eps (X : LedgerY ι) : ℚ := Paper1130.eps X.base + ∑ i, X.nY i * 0

/-- 置かない定数は、自分の質量次元に冪を掛けた分を質量次元に足す。 -/
def LedgerY.mu (X : LedgerY ι) : ℚ := Paper1130.mu X.base + ∑ i, X.nY i * X.muY i

/-- 広げた帳簿の式：ε + μ = 2r + u + ρ + U、U = Σ n_Y μ_Y。 -/
theorem ledger_identity_Y (X : LedgerY ι) :
    X.eps + X.mu = 2 * X.base.r + X.base.u + X.base.ρ + ∑ i, X.nY i * X.muY i := by
  unfold LedgerY.eps LedgerY.mu
  have := ledger_identity X.base
  simp only [mul_zero, Finset.sum_const_zero, add_zero]
  linarith

/-- 広げた偶奇：r・u・ρ・U が整数なら、ε + μ と u + ρ + U は偶奇が同じ。 -/
theorem parity_Y (X : LedgerY ι) (r u ρ U : ℤ) (hr : X.base.r = r) (hu : X.base.u = u)
    (hρ : X.base.ρ = ρ) (hU : ∑ i, X.nY i * X.muY i = U) :
    X.eps + X.mu = ((2 * r + u + ρ + U : ℤ) : ℚ) ∧
      (2 * r + u + ρ + U) % 2 = (u + ρ + U) % 2 := by
  refine ⟨?_, ?_⟩
  · rw [ledger_identity_Y, hr, hu, hρ, hU]; push_cast; ring
  · omega

/-- 質量次元 μY の定数を (4π)^s と置いたときの重みは s + μY で、
それが 0 になるのは s = −μY（パッチの規則）のときだけ。 -/
theorem placement_weight_zero_iff (s μY : ℚ) : s + μY = 0 ↔ s = -μY := by
  constructor <;> intro h <;> linarith

/-- ħ と G の置き方は、この規則（s = −μ）に当たる。c は質量次元 0 なので置かなくても重み 0。 -/
theorem hbar_G_c_follow_patch_rule :
    epsOf hbar = - muOf hbar ∧ epsOf G = - muOf G ∧ epsOf c + muOf c = 0 := by
  simp [epsOf, muOf, dimOf]

/-! ### 置き方を入れた実数の値：値に立つ a の冪は ε である -/

open Real

/-- 置き方を入れた因子の実数の値：ħ = 1/a、G = a、置いた質量 = a、じかの 4π = a、
c・置かない質量 M・長さ ℓ・時間 t は文字のまま。 -/
noncomputable def placedVal (a cv Mv ℓ t : ℝ) : Factor → ℝ
  | hbar => 1 / a
  | G => a
  | c => cv
  | placedMass => a
  | freeMass => Mv
  | fourPi => a
  | length => ℓ
  | time => t

/-- 置き方を入れた量の値：因子の値を指数乗して掛けたもの。 -/
noncomputable def value (a cv Mv ℓ t : ℝ) (X : Ledger) : ℝ :=
  (factors.map fun f => placedVal a cv Mv ℓ t f ^ (X.exp f : ℝ)).prod

/-- 任意の正の a について、値は a^ε · c^N · M^u · ℓ^zL · t^zT になる
（値に立つ a = 4π の冪が ε であること）。 -/
theorem value_eq (a cv Mv ℓ t : ℝ) (ha : 0 < a) (X : Ledger) :
    value a cv Mv ℓ t X
      = a ^ ((eps X : ℚ) : ℝ) * cv ^ (X.N : ℝ) * Mv ^ (X.u : ℝ) * ℓ ^ (X.zL : ℝ)
          * t ^ (X.zT : ℝ) := by
  simp only [value, factors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    placedVal, Ledger.exp, mul_one]
  rw [eps_formula]
  push_cast
  rw [one_div, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
  rw [Real.rpow_add ha, Real.rpow_add ha, Real.rpow_sub ha]
  rw [Real.rpow_neg ha.le]
  field_simp

/-! ### 原稿の例（第4節） -/

/-- GM（M を置いた質量 m とした G m）は (ε, μ) = (2, 0)。 -/
example : eps ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ = 2 ∧ mu ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ = 0 := by
  simp [eps_formula, mu_formula]; norm_num

/-- ħ²/(2m) は (ε, μ) = (−3, 1)。 -/
example : eps ⟨0, 2, 0, 0, -1, 0, 0, 0⟩ = -3 ∧ mu ⟨0, 2, 0, 0, -1, 0, 0, 0⟩ = 1 := by
  simp [eps_formula, mu_formula]; norm_num

/-- a = 4π を数として入れると、ħ²/(2m) = (1/(4π))² / (2 · 4π) = 1/(128π³)。 -/
example : (1 / (4 * π)) ^ 2 / (2 * (4 * π)) = 1 / (128 * π ^ 3) := by
  have : π ≠ 0 := Real.pi_ne_zero
  field_simp; ring

/-- プランク質量 √(ħc/G)（p = 1/2、q = −1/2、N = 1/2）は (ε, μ) = (−1, 1)。 -/
example : eps ⟨0, 1/2, -1/2, 1/2, 0, 0, 0, 0⟩ = -1 ∧ mu ⟨0, 1/2, -1/2, 1/2, 0, 0, 0, 0⟩ = 1 := by
  simp [eps_formula, mu_formula]; norm_num

end Paper1130

end Yamagishi
