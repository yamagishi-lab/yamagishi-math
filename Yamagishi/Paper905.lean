/-
論文905『ラーモアの公式の 2/3 と c³ の 3 は、どちらも空間次元である』の数学の中身を、機械に確かめさせる。

原稿（905_yamagishi_larmor_two_thirds_and_c_cubed_count_the_dimension/…_jp.tex）の
  第1節：d 次元で q² の単位は M L^d T^(−2)、加速度の (k−1) 階微分 a^(k−1)（部分 k）の単位は L T^(−(k+1))。
    q²・部分 k₁…k_n の積・c^m が仕事率 M L² T^(−3) になる条件は k₁+…+k_n = d − 1、m = 2 − d − n。
    すなわち形は d − 1 の分割に一対一で対応する。
  第2節：因子を二つに限れば c の指数は −d。
  第3節（本稿の芯）：因子二つの形 a^(j−1)·a^(k−1)（j + k = d − 1）を一周期で積分すると、
    d が奇数なら部分積分で ±∫(a^((d−3)/2))² の一つの形に帰着し（符号は (−1)^((k−j)/2)）、
    d が偶数なら時間の全微分で 0。
  第4節：角分布 sin²θ を S^(d−1) の測度 sin^(d−2)θ dθ で平均すると 1 − 1/d。
    d = 3 で ∫ sin²θ dΩ = 8π/3 = 4π × 2/3。

書き方：
・第1節は、部分の多重集合 s（正の整数）と整数 m について「仕事率の単位になる ⇔ Σk = d − 1 かつ
  m = 2 − d − (部分の数)」を示し、さらに「仕事率になる形 ⇔ d − 1 の分割（Mathlib の `Nat.Partition`）が
  ただ一つあって、その部分がちょうど s」と書いた。
・第3節は、原稿の x(t) = sin t + 0.3 sin 3t の一例ではなく、何度でも微分できて周期の両端で値が
  そろう関数の列 g₀, g₁, g₂, …（g_{n+1} が g_n の導関数）について一般に示した。
  加速度 a = g₀ とすれば g_n = a^(n)。「周期の両端で値がそろう」は周期関数の導関数がすべて満たす。
・第4節は、Mathlib の sin の冪の積分の漸化式から、すべての d ≥ 2 について示した。

形式化していないもの：表の形の数 1・2・3・5・7・11・15・22 が分割の数であること（分割の数そのものは
数えていない。一対一の対応だけを示した）、計算 3.1 の数値（±209.261487 など）、
「c³ の 3 は空間次元」「2/3 の 3 も空間次元」という読み、d ≠ 3 の放射の式、論文247・64 との関係。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper905

open Real intervalIntegral

/-! ### 第1節：単位が許す形は d − 1 の分割 -/

/-- 単項式 q²·(部分 s の積)·c^m の L の指数と T の指数（M の指数は q² の 1 だけ）。
q² = M L^d T^(−2)、部分 k = L T^(−(k+1))、c = L T^(−1)。 -/
def lenExp (d : ℤ) (s : Multiset ℕ) (m : ℤ) : ℤ := d + s.card + m
def timeExp (s : Multiset ℕ) (m : ℤ) : ℤ := -2 - (s.map (fun k : ℕ => (k : ℤ) + 1)).sum - m

/-- 第1節：仕事率 M L² T^(−3) になる ⇔ Σk = d − 1 かつ m = 2 − d − n（n は部分の数）。 -/
theorem power_condition (d : ℤ) (s : Multiset ℕ) (m : ℤ) :
    (lenExp d s m = 2 ∧ timeExp s m = -3) ↔
      ((s.map (fun k : ℕ => (k : ℤ))).sum = d - 1 ∧ m = 2 - d - s.card) := by
  have hsum : (s.map (fun k : ℕ => (k : ℤ) + 1)).sum =
      (s.map (fun k : ℕ => (k : ℤ))).sum + s.card := by
    rw [Multiset.sum_map_add]
    simp
  unfold lenExp timeExp
  rw [hsum]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- 第1節：仕事率になる形は、d − 1 の分割と一対一。正の部分の多重集合 s と整数 m が仕事率の単位を
与える ⇔ 部分がちょうど s である d − 1 の分割がただ一つあり、m = 2 − d − (部分の数)。 -/
theorem forms_are_partitions (D : ℕ) (s : Multiset ℕ) (hs : ∀ k ∈ s, 0 < k) (m : ℤ) :
    (lenExp (D + 1) s m = 2 ∧ timeExp s m = -3) ↔
      ((∃! p : Nat.Partition D, p.parts = s) ∧ m = 2 - (D + 1) - s.card) := by
  rw [power_condition]
  have hcast : (s.map (fun k : ℕ => (k : ℤ))).sum = ((s.sum : ℕ) : ℤ) :=
    (Nat.cast_multiset_sum s).symm
  rw [hcast]
  constructor
  · rintro ⟨h1, h2⟩
    have hD : s.sum = D := by omega
    refine ⟨⟨⟨s, fun {k} hk => hs k hk, hD⟩, rfl, ?_⟩, h2⟩
    intro p hp
    cases p
    simp only at hp
    subst hp
    rfl
  · rintro ⟨⟨p, hp, _⟩, h2⟩
    refine ⟨?_, h2⟩
    rw [← hp, p.parts_sum]
    ring

/-- 第2節：因子を二つに限れば c の指数は −d（c³ の 3 は d = 3 の d）。 -/
theorem two_factors_c_exponent (d : ℤ) (j k : ℕ) (m : ℤ)
    (h : lenExp d {j, k} m = 2 ∧ timeExp {j, k} m = -3) : m = -d ∧ (j : ℤ) + k = d - 1 := by
  rw [power_condition] at h
  obtain ⟨h1, h2⟩ := h
  simp at h1 h2
  constructor <;> linarith

/-! ### 第3節（芯）：一周期の積分は次元の偶奇で分かれる

g n は加速度の n 階微分 a^(n) の役。`HasDerivAt (g n) (g (n+1) t) t` がすべての n, t で成り立ち、
周期の両端 0, T で値がそろう（`g n 0 = g n T`）とする。 -/

variable (g : ℕ → ℝ → ℝ) (T : ℝ)

/-- 二つの微分の積の一周期の積分 I(p, q) = ∫₀^T a^(p) a^(q) dt。 -/
noncomputable def I (p q : ℕ) : ℝ := ∫ t in (0 : ℝ)..T, g p t * g q t

variable {g T}

theorem I_comm (p q : ℕ) : I g T p q = I g T q p := by
  unfold I; congr 1; ext t; ring

/-- 部分積分の一歩：I(p+1, q) = −I(p, q+1)（境界の項は周期で消える）。 -/
theorem I_step (hd : ∀ n t, HasDerivAt (g n) (g (n + 1) t) t) (hp : ∀ n, g n 0 = g n T)
    (p q : ℕ) : I g T (p + 1) q = -I g T p (q + 1) := by
  have hc : ∀ n, Continuous (g n) := fun n =>
    continuous_iff_continuousAt.mpr fun t => (hd n t).continuousAt
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T)
    (u := g q) (v := g p) (u' := g (q + 1)) (v' := g (p + 1))
    (fun x _ => hd q x) (fun x _ => hd p x)
    ((hc (q + 1)).intervalIntegrable _ _) ((hc (p + 1)).intervalIntegrable _ _)
  unfold I
  rw [hp q, hp p] at h
  have e1 : (∫ t in (0 : ℝ)..T, g (p + 1) t * g q t) = ∫ t in (0 : ℝ)..T, g q t * g (p + 1) t := by
    congr 1; ext t; ring
  have e2 : (∫ t in (0 : ℝ)..T, g p t * g (q + 1) t) = ∫ t in (0 : ℝ)..T, g (q + 1) t * g p t := by
    congr 1; ext t; ring
  rw [e1, e2, h]
  ring

/-- 一歩を j 回：I(p + j, q) = (−1)^j I(p, q + j)。 -/
theorem I_shift (hd : ∀ n t, HasDerivAt (g n) (g (n + 1) t) t) (hp : ∀ n, g n 0 = g n T)
    (j : ℕ) : ∀ p q, I g T (p + j) q = (-1) ^ j * I g T p (q + j) := by
  induction j with
  | zero => intro p q; simp
  | succ j ih =>
    intro p q
    rw [show p + (j + 1) = (p + j) + 1 by ring, I_step hd hp, ih p (q + 1)]
    rw [show q + 1 + j = q + (j + 1) by ring]
    ring

/-- 隣り合う階数の積は一周期で消える：∫ a^(m) a^(m+1) = 0（二乗の時間微分の半分だから）。 -/
theorem I_adjacent_zero (hd : ∀ n t, HasDerivAt (g n) (g (n + 1) t) t) (hp : ∀ n, g n 0 = g n T)
    (m : ℕ) : I g T m (m + 1) = 0 := by
  have h := I_step hd hp m m
  rw [I_comm (m + 1) m] at h
  linarith

/-- 本稿の芯（奇数次元の側）：p ≤ q、p + q = 2m なら、I(p, q) = (−1)^(m − p) ∫ (a^(m))²。
一つの形の積分に符号を付けたものしか残らない。 -/
theorem I_even_reduce (hd : ∀ n t, HasDerivAt (g n) (g (n + 1) t) t) (hp : ∀ n, g n 0 = g n T)
    (p q m : ℕ) (hpq : p ≤ q) (hsum : p + q = 2 * m) :
    I g T p q = (-1) ^ (m - p) * I g T m m := by
  have hpm : p ≤ m := by omega
  have h := I_shift hd hp (m - p) p m
  rw [show p + (m - p) = m by omega, show m + (m - p) = q by omega] at h
  rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- 本稿の芯（偶数次元の側）：p + q が奇数なら、I(p, q) = 0。 -/
theorem I_odd_zero (hd : ∀ n t, HasDerivAt (g n) (g (n + 1) t) t) (hp : ∀ n, g n 0 = g n T)
    (p q : ℕ) (hodd : Odd (p + q)) : I g T p q = 0 := by
  -- p ≤ q の場合に帰着
  have key : ∀ p q, p ≤ q → Odd (p + q) → I g T p q = 0 := by
    intro p q hpq ho
    obtain ⟨m, hm⟩ := ho
    have h := I_shift hd hp (m - p) p (m + 1)
    rw [show p + (m - p) = m by omega, show m + 1 + (m - p) = q by omega,
      I_adjacent_zero hd hp m] at h
    have hs : ((-1 : ℝ) ^ (m - p)) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.mp h.symm).resolve_left hs
  rcases le_total p q with h | h
  · exact key p q h hodd
  · rw [I_comm]; exact key q p h (by rwa [add_comm])

/-- 原稿の言い方に合わせて：部分の対 [j, k]（j, k ≥ 1、j + k = d − 1）の形 a^(j−1)·a^(k−1) の一周期の積分は、
d が奇数（d = 2m + 3）で j ≤ k なら (−1)^((k−j)/2) ∫ (a^(m))²、d が偶数なら 0。 -/
theorem pair_integral (hd : ∀ n t, HasDerivAt (g n) (g (n + 1) t) t) (hp : ∀ n, g n 0 = g n T)
    (j k d : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (hjk : j + k = d - 1) (hd2 : 2 ≤ d) :
    (Odd d → j ≤ k →
      I g T (j - 1) (k - 1) = (-1) ^ ((k - j) / 2) * I g T ((d - 3) / 2) ((d - 3) / 2)) ∧
    (Even d → I g T (j - 1) (k - 1) = 0) := by
  constructor
  · rintro ⟨m, hm⟩ hle
    have := I_even_reduce hd hp (j - 1) (k - 1) ((d - 3) / 2) (by omega) (by omega)
    rw [this, show (d - 3) / 2 - (j - 1) = (k - j) / 2 by omega]
  · rintro ⟨m, hm⟩
    exact I_odd_zero hd hp _ _ ⟨m - 2, by omega⟩

/-! ### 第4節：2/3 の 3 -/

/-- 角分布 sin²θ を S^(d−1) の測度 sin^(d−2)θ dθ で平均すると 1 − 1/d（すべての d ≥ 2）。 -/
theorem mean_sin_sq (n : ℕ) :
    (∫ x in (0 : ℝ)..π, sin x ^ (n + 2)) / (∫ x in (0 : ℝ)..π, sin x ^ n) =
      1 - 1 / ((n + 2 : ℕ) : ℝ) := by
  have hpos := integral_sin_pow_pos (n := n)
  rw [integral_sin_pow]
  simp only [sin_zero, sin_pi, ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, zero_mul, sub_self, zero_div, zero_add]
  push_cast
  field_simp
  ring

/-- d = 3 では平均 2/3、∫ sin²θ dΩ = 2π ∫₀^π sin³θ dθ = 8π/3 = 4π × 2/3。 -/
theorem larmor_two_thirds :
    (∫ x in (0 : ℝ)..π, sin x ^ 3) / (∫ x in (0 : ℝ)..π, sin x ^ 1) = 2 / 3 ∧
    2 * π * (∫ x in (0 : ℝ)..π, sin x ^ 3) = 8 * π / 3 ∧ 8 * π / 3 = 4 * π * (2 / 3) := by
  have h1 : (∫ x in (0 : ℝ)..π, sin x ^ 1) = 2 := by
    simp only [pow_one, integral_sin, cos_zero, cos_pi]; norm_num
  have h3 : (∫ x in (0 : ℝ)..π, sin x ^ 3) = 4 / 3 := by
    have := integral_sin_pow (a := 0) (b := π) (n := 1)
    simp only [sin_zero, sin_pi] at this
    rw [this, h1]; norm_num
  refine ⟨?_, ?_, by ring⟩
  · rw [h1, h3]; norm_num
  · rw [h3]; ring

end Paper905

end Yamagishi
