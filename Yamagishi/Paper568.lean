/-
論文568『要る鎖の長さは、水深に比例しない』の格上げ（一般の形）。

日本語：錨のところで鎖を水平に引かせる最短の長さは √(d² + 2da) で、荷重を 2 倍にすると 1 倍と √2 倍の
あいだ、水深を 2 倍にすると √2 倍と 2 倍のあいだ、両方を 2 倍にするとちょうど 2 倍になる。
English: The shortest chain that pulls the anchor horizontally is √(d² + 2da); doubling the load
multiplies it by a factor in (1, √2), doubling the depth by a factor in (√2, 2), and doubling both
by exactly 2.

原稿（568_yamagishi_the_chain_needed_is_not_proportional/…_jp.tex）は、懸垂線から L = √(d² + 2da)、
スコープ L/d = √(1 + 2a/d) を書き、a/d = 1・5・12・24・50 の表、a = 50 m で水深五段、水深 10 m で
荷重四段（倍で 1.381699）、鎖を短くしたときの錨の角度、重さの無い索の角度を数値で出す。
比の上下の限界や単調性は数表から読むだけ。

ここで証明した言明（一様で伸びない鎖・平らな海底の懸垂線の模型。d は水深、a = H/w > 0）：
  (1) `hasDerivAt_catenary`・`arc_length`：懸垂線 y = a(cosh(x/a) − 1) の傾きは sinh(x/a) で、
      錨（頂点）から水平距離 X までの弧長 ∫₀^X √(1 + y′²) dx は a·sinh(X/a)。
  (2) `exists_fairlead`：どの d ≥ 0 にも y(X) = d となる X ≥ 0 がある。`length_eq`：そのとき弧長は
      √(d² + 2da)（＝ L(d, a)）。`depth_from_length`：逆に d = √(a² + L²) − a。
  (3) `load_double`：L(d, a) < L(d, 2a) < √2·L(d, a)。`depth_double`：√2·L(d, a) < L(2d, a) < 2L(d, a)。
      `both_double`：L(2d, 2a) = 2L(d, a)（`L_homog`：一次同次）。
  (4) `scope_eq`：L/d = √(1 + 2a/d)。`scope_strictAnti_depth`：同じ荷重なら水深について狭義に減る。
      `scope_strictMono_load`：同じ水深なら荷重について狭義に増える。
  (5) `scope_le_iff`：L ≤ k·d ⇔ 2a ≤ (k² − 1)d（k ≥ 0）。とくに 5 倍で足りる ⇔ a ≤ 12d、7 倍 ⇔ a ≤ 24d。
      `paper_five_metres`：a = 50 m・水深 5 m では要るのは √21·5 で 5 倍より短い（5 倍で足りる）。
      `paper_four_metres`：水深 4 m では √26·4 が要り、5 倍では足りない。
足した仮定：原稿と同じ模型（弾性・海底の傾き・波の動的な張力・舷の高さは入れない）。
形式化していないもの：鎖を短くしたときの錨の角度の表、重さの無い索の角度、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper568

open Real intervalIntegral

/-! ### (1) 懸垂線と弧長 -/

/-- 錨を頂点に置いた懸垂線 y(x) = a(cosh(x/a) − 1)。 -/
noncomputable def catenary (a x : ℝ) : ℝ := a * (cosh (x / a) - 1)

theorem hasDerivAt_catenary {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (catenary a) (sinh (x / a)) x := by
  have h := ((((hasDerivAt_id' x).div_const a).cosh).sub_const 1).const_mul a
  unfold catenary
  convert h using 1
  field_simp

/-- (1) 弧長 ∫₀^X √(1 + y′²) dx = a sinh(X/a)。 -/
theorem arc_length {a : ℝ} (ha : 0 < a) (X : ℝ) :
    ∫ x in (0 : ℝ)..X, √(1 + sinh (x / a) ^ 2) = a * sinh (X / a) := by
  have e : ∀ x : ℝ, √(1 + sinh (x / a) ^ 2) = cosh (x / a) := by
    intro x
    rw [← cosh_sq', sqrt_sq (cosh_pos _).le]
  simp_rw [e]
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) X,
      HasDerivAt (fun x => a * sinh (x / a)) (cosh (x / a)) x := by
    intro x _
    have h := (((hasDerivAt_id' x).div_const a).sinh).const_mul a
    convert h using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hd (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp

/-! ### (2) 要る長さ -/

/-- 要る長さ L(d, a) = √(d² + 2da)。 -/
noncomputable def L (d a : ℝ) : ℝ := √(d ^ 2 + 2 * d * a)

/-- (2) 高さ d に届く点がある。 -/
theorem exists_fairlead {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
    ∃ X, 0 ≤ X ∧ catenary a X = d := by
  refine ⟨a * arsinh (√(d ^ 2 + 2 * d * a) / a), ?_, ?_⟩
  · apply mul_nonneg ha.le
    rw [arsinh_nonneg_iff]; positivity
  · unfold catenary
    rw [mul_div_cancel_left₀ _ ha.ne', cosh_arsinh, div_pow,
      sq_sqrt (by positivity)]
    have : 1 + (d ^ 2 + 2 * d * a) / a ^ 2 = ((a + d) / a) ^ 2 := by field_simp; ring
    rw [this, sqrt_sq (by positivity)]
    field_simp; ring

/-- (2) 高さ d の点までの弧長は √(d² + 2da)。 -/
theorem length_eq {a d X : ℝ} (ha : 0 < a) (hX : 0 ≤ X) (hd : catenary a X = d) :
    a * sinh (X / a) = L d a := by
  unfold L
  rw [← hd]
  unfold catenary
  have hs : 0 ≤ a * sinh (X / a) := mul_nonneg ha.le (sinh_nonneg_iff.mpr (by positivity))
  rw [← sqrt_sq hs]
  congr 1
  linear_combination (-a ^ 2) * cosh_sq (X / a)

/-- (2) 逆算：d = √(a² + L²) − a。 -/
theorem depth_from_length {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
    d = √(a ^ 2 + L d a ^ 2) - a := by
  unfold L
  rw [sq_sqrt (by positivity)]
  have : a ^ 2 + (d ^ 2 + 2 * d * a) = (d + a) ^ 2 := by ring
  rw [this, sqrt_sq (by positivity)]; ring

/-! ### (3) 倍にしたとき -/

theorem L_pos {d a : ℝ} (hd : 0 < d) (ha : 0 < a) : 0 < L d a := by
  unfold L; positivity

/-- (3) 一次同次：L(td, ta) = t L(d, a)。 -/
theorem L_homog {d a t : ℝ} (ht : 0 ≤ t) : L (t * d) (t * a) = t * L d a := by
  unfold L
  rw [show (t * d) ^ 2 + 2 * (t * d) * (t * a) = t ^ 2 * (d ^ 2 + 2 * d * a) by ring,
    sqrt_mul (sq_nonneg _), sqrt_sq ht]

/-- (3) 両方を 2 倍にすると、ちょうど 2 倍。 -/
theorem both_double (d a : ℝ) : L (2 * d) (2 * a) = 2 * L d a := L_homog (by norm_num)

theorem sqrt_lt_mul_sqrt {x y k : ℝ} (hx : 0 ≤ x) (hk : 0 ≤ k) (h : x < k ^ 2 * y) :
    √x < k * √y := by
  have hy : 0 ≤ y := by
    by_contra hy; push Not at hy; nlinarith [sq_nonneg k]
  rw [← sqrt_sq hk, ← sqrt_mul (sq_nonneg _)]
  exact sqrt_lt_sqrt hx h

theorem mul_sqrt_lt_sqrt {x y k : ℝ} (hx : 0 ≤ x) (hk : 0 ≤ k) (h : k ^ 2 * x < y) :
    k * √x < √y := by
  rw [← sqrt_sq hk, ← sqrt_mul (sq_nonneg _)]
  exact sqrt_lt_sqrt (by positivity) h

/-- (3) 荷重を 2 倍：1 倍より大きく √2 倍より小さい。 -/
theorem load_double {d a : ℝ} (hd : 0 < d) (ha : 0 < a) :
    L d a < L d (2 * a) ∧ L d (2 * a) < √2 * L d a := by
  unfold L
  constructor
  · exact sqrt_lt_sqrt (by positivity) (by nlinarith)
  · apply sqrt_lt_mul_sqrt (by positivity) (sqrt_nonneg _)
    rw [sq_sqrt (by norm_num)]; nlinarith

/-- (3) 水深を 2 倍：√2 倍より大きく 2 倍より小さい。 -/
theorem depth_double {d a : ℝ} (hd : 0 < d) (ha : 0 < a) :
    √2 * L d a < L (2 * d) a ∧ L (2 * d) a < 2 * L d a := by
  unfold L
  constructor
  · apply mul_sqrt_lt_sqrt (by positivity) (sqrt_nonneg _)
    rw [sq_sqrt (by norm_num)]; nlinarith
  · apply sqrt_lt_mul_sqrt (by positivity) (by norm_num)
    nlinarith

/-! ### (4)(5) スコープ -/

/-- (4) スコープ L/d = √(1 + 2a/d)。 -/
theorem scope_eq {d a : ℝ} (hd : 0 < d) : L d a / d = √(1 + 2 * a / d) := by
  unfold L
  rw [eq_comm, ← sqrt_sq hd.le, ← sqrt_div' _ (sq_nonneg d), sqrt_sq hd.le]
  congr 1
  field_simp

/-- (4) 同じ荷重なら、スコープは水深について狭義に減る。 -/
theorem scope_strictAnti_depth {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (fun d => L d a / d) (Set.Ioi 0) := by
  intro d₁ h₁ d₂ h₂ h12
  simp only [Set.mem_Ioi] at h₁ h₂
  simp only [scope_eq h₁, scope_eq h₂]
  apply sqrt_lt_sqrt (by positivity)
  have : 2 * a / d₂ < 2 * a / d₁ := div_lt_div_of_pos_left (by positivity) h₁ h12
  linarith

/-- (4) 同じ水深なら、スコープは荷重について狭義に増える。 -/
theorem scope_strictMono_load {d : ℝ} (hd : 0 < d) :
    StrictMonoOn (fun a => L d a / d) (Set.Ici 0) := by
  intro a₁ h₁ a₂ _ h12
  simp only [Set.mem_Ici] at h₁
  simp only [scope_eq hd]
  apply sqrt_lt_sqrt (by positivity)
  have : 2 * a₁ / d < 2 * a₂ / d := div_lt_div_of_pos_right (by linarith) hd
  linarith

/-- (5) L ≤ k d ⇔ 2a ≤ (k² − 1) d。 -/
theorem scope_le_iff {d a k : ℝ} (hd : 0 < d) (hk : 0 ≤ k) :
    L d a ≤ k * d ↔ 2 * a ≤ (k ^ 2 - 1) * d := by
  unfold L
  rw [sqrt_le_left (by positivity)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- (5) 5 倍で足りる ⇔ a ≤ 12 d。 -/
theorem scope_five {d a : ℝ} (hd : 0 < d) : L d a ≤ 5 * d ↔ a ≤ 12 * d := by
  rw [scope_le_iff hd (by norm_num)]; constructor <;> intro h <;> nlinarith

/-- (5) 7 倍で足りる ⇔ a ≤ 24 d。 -/
theorem scope_seven {d a : ℝ} (hd : 0 < d) : L d a ≤ 7 * d ↔ a ≤ 24 * d := by
  rw [scope_le_iff hd (by norm_num)]; constructor <;> intro h <;> nlinarith

/-- (5) 原稿の例：a = 50 m・水深 5 m で要るのは √21 × 5 m で、5 倍より短い（5 倍で足りる）。 -/
theorem paper_five_metres : L 5 50 = 5 * √21 ∧ L 5 50 < 5 * 5 := by
  constructor
  · unfold L
    rw [show (5 : ℝ) ^ 2 + 2 * 5 * 50 = 5 ^ 2 * 21 by norm_num, sqrt_mul (by norm_num),
      sqrt_sq (by norm_num)]
  · rw [show (5 : ℝ) * 5 = 25 by norm_num]
    unfold L
    rw [show (25 : ℝ) = √(25 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- (5) a = 50 m・水深 4 m では 5 倍では足りない（√26 × 4 m が要る）。 -/
theorem paper_four_metres : 5 * 4 < L 4 50 := by
  have : ¬ (L 4 50 ≤ 5 * 4) := by
    rw [scope_five (by norm_num)]; norm_num
  push Not at this; exact this

end Paper568

end Yamagishi
