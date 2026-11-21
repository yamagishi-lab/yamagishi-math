/-
論文936『見かけの協同は、形の偏りと結合の強さが釣り合う所で山になる』の格上げ（一般の形）。

原稿（936_yamagishi_apparent_cooperativity_peaks_where_shape_bias_balances_binding_strength/…_jp.tex）
は、結合場所 n = 4 の MWC 模型
  Y = [α(1+α)^(n−1) + Lcα(1+cα)^(n−1)] / [(1+α)^n + L(1+cα)^n]
で、Y = 1/2 での見かけのヒル係数 d ln[Y/(1−Y)]/d ln α を、c = 0・0.01・0.1・1 と L = 1〜10^10 の
格子で数値で出し、上限が n を超えないことを既知として書いている。

ここで証明した言明（結合場所 n ≥ 2 は任意、α > 0・L > 0・c ≥ 0、どの濃さ α でも）：
  二つの形の重み w = (1+α)^n / [(1+α)^n + L(1+cα)^n]、一場所あたりの結合の割合
  p = α/(1+α)（R の形）・q = cα/(1+cα)（T の形）、その混ぜ合わせの分散 V = w(1−w)(p−q)² と置く。
  (1) `Y_eq_mix`：Y = wp + (1−w)q。
  (2) `alpha_deriv`：α·dY/dα = Y(1−Y) + (n−1)V（微分を実際に計算して示した）。
  (3) `hill_formula`：見かけのヒル係数 n_H = α Y′/(Y(1−Y)) は n_H = 1 + (n−1)V/(Y(1−Y))。
  (4) `hill_bounds`：c ≠ 1 なら 1 < n_H < n。`hill_eq_one`：c = 1 なら（L によらず）n_H = 1。
原稿との差：原稿は Y = 1/2 の一点のヒル係数を数値で見ているが、(3)(4) はどの濃さでも成り立つ。
c > 1 でも同じ不等式が成り立つ（c ≠ 1 だけが要る）。
形式化していないもの：山の位置 L = c^(−n/2) と、L ↔ 1/(Lc^n) の入れ替えの対称（下読みの AI の注意の
とおり、山の位置は対称だけでは言えず、山が一つであることを別に示す必要がある）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper936

/-- 結合している場所の割合（結合場所 n = k + 2）。 -/
noncomputable def Y (k : ℕ) (L c α : ℝ) : ℝ :=
  (α * (1 + α) ^ (k + 1) + L * c * α * (1 + c * α) ^ (k + 1)) /
    ((1 + α) ^ (k + 2) + L * (1 + c * α) ^ (k + 2))

/-- R の形の重み。 -/
noncomputable def w (k : ℕ) (L c α : ℝ) : ℝ :=
  (1 + α) ^ (k + 2) / ((1 + α) ^ (k + 2) + L * (1 + c * α) ^ (k + 2))

/-- 一場所あたりの結合の割合（R の形・T の形）。 -/
noncomputable def p (α : ℝ) : ℝ := α / (1 + α)
noncomputable def q (c α : ℝ) : ℝ := c * α / (1 + c * α)

/-- 混ぜ合わせた割合の分散。 -/
noncomputable def V (k : ℕ) (L c α : ℝ) : ℝ :=
  w k L c α * (1 - w k L c α) * (p α - q c α) ^ 2

/-- 見かけのヒル係数 d ln[Y/(1−Y)]/d ln α = α Y′/(Y(1−Y))。 -/
noncomputable def hill (k : ℕ) (L c α : ℝ) : ℝ :=
  α * deriv (Y k L c) α / (Y k L c α * (1 - Y k L c α))

section

variable {k : ℕ} {L c α : ℝ}

theorem Dpos (hL : 0 < L) (hc : 0 ≤ c) (hα : 0 < α) :
    0 < (1 + α) ^ (k + 2) + L * (1 + c * α) ^ (k + 2) := by
  have : 0 < 1 + c * α := by positivity
  positivity

/-- (1) Y は二つの形の割合の混ぜ合わせ。 -/
theorem Y_eq_mix (hL : 0 < L) (hc : 0 ≤ c) (hα : 0 < α) :
    Y k L c α = w k L c α * p α + (1 - w k L c α) * q c α := by
  have hD := Dpos (k := k) hL hc hα
  have ha : 0 < 1 + α := by linarith
  have hb : 0 < 1 + c * α := by positivity
  unfold Y w p q
  field_simp
  ring

/-- 分子と分母とその微分。 -/
noncomputable def Nf (k : ℕ) (L c x : ℝ) : ℝ :=
  x * (1 + x) ^ (k + 1) + L * c * x * (1 + c * x) ^ (k + 1)
noncomputable def Df (k : ℕ) (L c x : ℝ) : ℝ := (1 + x) ^ (k + 2) + L * (1 + c * x) ^ (k + 2)
noncomputable def Nd (k : ℕ) (L c x : ℝ) : ℝ :=
  ((1 + x) ^ (k + 1) + x * ((k + 1) * (1 + x) ^ k)) +
    L * c * ((1 + c * x) ^ (k + 1) + x * ((k + 1) * (1 + c * x) ^ k * c))
noncomputable def Dd (k : ℕ) (L c x : ℝ) : ℝ :=
  (k + 2) * (1 + x) ^ (k + 1) + L * ((k + 2) * (1 + c * x) ^ (k + 1) * c)

/-- Y の微分（具体的な式）。 -/
theorem hasDerivAt_Y (hL : 0 < L) (hc : 0 ≤ c) (hα : 0 < α) :
    HasDerivAt (Y k L c)
      ((Nd k L c α * Df k L c α - Nf k L c α * Dd k L c α) / Df k L c α ^ 2) α := by
  have hD := Dpos (k := k) hL hc hα
  have ha : HasDerivAt (fun x : ℝ => 1 + x) 1 α := (hasDerivAt_id α).const_add 1
  have hb : HasDerivAt (fun x : ℝ => 1 + c * x) c α := by
    simpa using ((hasDerivAt_id α).const_mul c).const_add 1
  have hN : HasDerivAt (Nf k L c) (Nd k L c α) α := by
    have h1 := (hasDerivAt_id α).mul (ha.pow (k + 1))
    have h2 := (((hasDerivAt_id α).mul (hb.pow (k + 1))).const_mul (L * c))
    convert h1.add h2 using 1
    · funext x; simp [Nf]; ring
    · simp [Nd]
  have hDd : HasDerivAt (Df k L c) (Dd k L c α) α := by
    convert (ha.pow (k + 2)).add ((hb.pow (k + 2)).const_mul L) using 1
    · funext x; simp [Df]
    · simp [Dd]
  have := hN.div hDd hD.ne'
  convert this using 1
  funext x; simp [Y, Nf, Df]

/-- (2) α·dY/dα = Y(1−Y) + (n−1)V（n = k + 2）。 -/
theorem alpha_deriv (hL : 0 < L) (hc : 0 ≤ c) (hα : 0 < α) :
    α * deriv (Y k L c) α = Y k L c α * (1 - Y k L c α) + (k + 1) * V k L c α := by
  rw [(hasDerivAt_Y hL hc hα).deriv]
  have hD := Dpos (k := k) hL hc hα
  have ha : 0 < 1 + α := by linarith
  have hb : 0 < 1 + c * α := by positivity
  unfold Y V w p q Nf Df Nd Dd
  field_simp
  ring

theorem Y_pos (hL : 0 < L) (hc : 0 ≤ c) (hα : 0 < α) : 0 < Y k L c α := by
  have hD := Dpos (k := k) hL hc hα
  unfold Y
  have : 0 < 1 + c * α := by positivity
  apply div_pos _ hD
  have : 0 ≤ L * c * α * (1 + c * α) ^ (k + 1) := by positivity
  have : 0 < α * (1 + α) ^ (k + 1) := by positivity
  linarith

/-- Y(1−Y) − V = w p(1−p) + (1−w) q(1−q)（割合の分散の分け方）。 -/
theorem YY_sub_V (hL : 0 < L) (hc : 0 ≤ c) (hα : 0 < α) :
    Y k L c α * (1 - Y k L c α) - V k L c α =
      w k L c α * (p α * (1 - p α)) + (1 - w k L c α) * (q c α * (1 - q c α)) := by
  rw [Y_eq_mix hL hc hα]; unfold V; ring

theorem w_mem (hL : 0 < L) (hc : 0 ≤ c) (hα : 0 < α) : 0 < w k L c α ∧ w k L c α < 1 := by
  have hD := Dpos (k := k) hL hc hα
  have hb : 0 < 1 + c * α := by positivity
  unfold w
  constructor
  · positivity
  · rw [div_lt_one hD]
    have : 0 < L * (1 + c * α) ^ (k + 2) := by positivity
    linarith

theorem V_lt (hL : 0 < L) (hc : 0 ≤ c) (hα : 0 < α) :
    V k L c α < Y k L c α * (1 - Y k L c α) := by
  have h := YY_sub_V (k := k) hL hc hα
  obtain ⟨hw0, hw1⟩ := w_mem (k := k) hL hc hα
  have hp : 0 < p α * (1 - p α) := by
    unfold p
    have : 0 < 1 + α := by linarith
    have : α / (1 + α) < 1 := by rw [div_lt_one this]; linarith
    have : 0 < α / (1 + α) := by positivity
    nlinarith
  have hq : 0 ≤ q c α * (1 - q c α) := by
    unfold q
    have hb : 0 < 1 + c * α := by positivity
    have : c * α / (1 + c * α) ≤ 1 := by rw [div_le_one hb]; linarith
    have : 0 ≤ c * α / (1 + c * α) := by positivity
    nlinarith
  have : 0 < w k L c α * (p α * (1 - p α)) + (1 - w k L c α) * (q c α * (1 - q c α)) := by
    have := mul_pos hw0 hp
    have := mul_nonneg (by linarith : 0 ≤ 1 - w k L c α) hq
    linarith
  linarith

/-- (3) ヒル係数の式 n_H = 1 + (n−1)V/(Y(1−Y))。 -/
theorem hill_formula (hL : 0 < L) (hc : 0 ≤ c) (hα : 0 < α) :
    hill k L c α = 1 + (k + 1) * V k L c α / (Y k L c α * (1 - Y k L c α)) := by
  have hY := Y_pos (k := k) hL hc hα
  have hV0 : 0 ≤ V k L c α := by
    obtain ⟨hw0, hw1⟩ := w_mem (k := k) hL hc hα
    unfold V; have := sq_nonneg (p α - q c α)
    have : 0 ≤ w k L c α * (1 - w k L c α) := mul_nonneg hw0.le (by linarith)
    positivity
  have hYY : 0 < Y k L c α * (1 - Y k L c α) := by linarith [V_lt (k := k) hL hc hα]
  unfold hill
  rw [alpha_deriv hL hc hα, add_div, div_self hYY.ne']

theorem p_sub_q (hc : 0 ≤ c) (hα : 0 < α) :
    p α - q c α = α * (1 - c) / ((1 + α) * (1 + c * α)) := by
  have ha : 0 < 1 + α := by linarith
  have hb : 0 < 1 + c * α := by positivity
  unfold p q; field_simp; ring

/-- (4) c ≠ 1 なら 1 < n_H < n（n = k + 2）。 -/
theorem hill_bounds (hL : 0 < L) (hc : 0 ≤ c) (hc1 : c ≠ 1) (hα : 0 < α) :
    1 < hill k L c α ∧ hill k L c α < k + 2 := by
  rw [hill_formula hL hc hα]
  have hVlt := V_lt (k := k) hL hc hα
  obtain ⟨hw0, hw1⟩ := w_mem (k := k) hL hc hα
  have hV : 0 < V k L c α := by
    unfold V
    have hpq : p α - q c α ≠ 0 := by
      rw [p_sub_q hc hα]
      have ha : 0 < 1 + α := by linarith
      have hb : 0 < 1 + c * α := by positivity
      have : 1 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
      positivity
    have := pow_pos (abs_pos.mpr hpq) 2
    rw [sq_abs] at this
    have : 0 < w k L c α * (1 - w k L c α) := mul_pos hw0 (by linarith)
    positivity
  have hYY : 0 < Y k L c α * (1 - Y k L c α) := by linarith
  have hk : (0 : ℝ) < k + 1 := by positivity
  constructor
  · have : 0 < (k + 1) * V k L c α / (Y k L c α * (1 - Y k L c α)) := by positivity
    linarith
  · have : (k + 1) * V k L c α / (Y k L c α * (1 - Y k L c α)) < k + 1 := by
      rw [div_lt_iff₀ hYY]; nlinarith
    linarith

/-- c = 1 なら、L によらず n_H = 1（協同は消える）。 -/
theorem hill_eq_one (hL : 0 < L) (hα : 0 < α) : hill k L 1 α = 1 := by
  rw [hill_formula hL zero_le_one hα]
  have : V k L 1 α = 0 := by
    unfold V; rw [p_sub_q zero_le_one hα]; simp
  rw [this]; simp

end

end Paper936

end Yamagishi
