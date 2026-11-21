/-
論文710『儲けは規模に比例し、コストは規模の 1.5 乗で増える——だから最適な大きさが必ずある』の格上げ（一般の形）。

原稿（710_yamagishi_return_grows_with_size_and_cost_grows_faster/…_jp.tex）は、
Π(Q) = aQ − βQ^(3/2) の一組（p = 1.5・a = 0.1・β = 0.01）で最適 Q* = (2a/(3β))² と、正味がゼロに
戻る規模 Q₀ = (a/β)² を出し、比 Q₀/Q* = 2.25 = (3/2)² が係数によらないことを
「折り返しの形は、係数ではなく冪の差が決めている」と述べる（観察 3.4）。

ここで証明した言明（a, β > 0、コストの冪 p > 1、収益の冪 1）：
  (1) `profit_max`：Π(Q) = aQ − βQ^p は Q ≥ 0 で Q* = (a/(pβ))^(1/(p−1)) でただ一つの最大をとる
      （Q ≠ Q* なら Π(Q) < Π(Q*)）。ベルヌーイの不等式から。
  (2) `profit_zero`：Π(Q₀) = 0、Q₀ = (a/β)^(1/(p−1))。
  (3) `ratio_eq`：Q₀/Q* = p^(1/(p−1))（a, β によらない）。`ratio_bounds`：1 < p^(1/(p−1)) < e。
  (4) 収益の冪を q（0 < q < p）にした一般の形：
      `critical_iff`：Q > 0 で qaQ^(q−1) = pβQ^(p−1) ⇔ Q = (qa/(pβ))^(1/(p−q))、
      `zero_iff`：aQ^q = βQ^p ⇔ Q = (a/β)^(1/(p−q))、
      `ratio_general`：その比は (p/q)^(1/(p−q))。
      `not_only_difference`：冪の差が同じ 1/2 でも、(q, p) = (1, 3/2) で比 9/4、(2, 5/2) で比 25/16。
確かめの係の案のとおり、原稿の「冪の差だけで決まる」は、収益の冪を 1 に固定したときに限る
（一般には (p/q)^(1/(p−q)) で、差だけでは決まらない）。機械でもこの反例を確かめた。
形式化していないもの：年間コスト 0.252 と要る粗のシャープレシオの数、p → 1 で比 → e の極限、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper710

open Real

/-- 正味 Π(Q) = aQ − βQ^p。 -/
noncomputable def profit (a β p Q : ℝ) : ℝ := a * Q - β * Q ^ p

/-- 最適 Q* = (a/(pβ))^(1/(p−1))。 -/
noncomputable def Qstar (a β p : ℝ) : ℝ := (a / (p * β)) ^ (1 / (p - 1))

/-- ゼロに戻る規模 Q₀ = (a/β)^(1/(p−1))。 -/
noncomputable def Q0 (a β p : ℝ) : ℝ := (a / β) ^ (1 / (p - 1))

section

variable {a β p : ℝ} (ha : 0 < a) (hb : 0 < β) (hp : 1 < p)
include ha hb hp

theorem Qstar_pos : 0 < Qstar a β p := by
  unfold Qstar; apply rpow_pos_of_pos; have : 0 < p := by linarith
  positivity

theorem Qstar_pow : Qstar a β p ^ (p - 1) = a / (p * β) := by
  unfold Qstar
  have : 0 < p := by linarith
  rw [← rpow_mul (by positivity), one_div, inv_mul_cancel₀ (by linarith), rpow_one]

/-- Π(Q) = βQ*^p (p t − t^p)、t = Q/Q*。 -/
theorem profit_scaled {Q : ℝ} (hQ : 0 ≤ Q) :
    profit a β p Q = β * Qstar a β p ^ p * (p * (Q / Qstar a β p) - (Q / Qstar a β p) ^ p) := by
  have hs := Qstar_pos ha hb hp
  have hsp := Qstar_pow ha hb hp
  have hp0 : 0 < p := by linarith
  unfold profit
  rw [div_rpow hQ hs.le]
  have e : Qstar a β p ^ p = Qstar a β p ^ (p - 1) * Qstar a β p := by
    rw [← rpow_add_one (ne_of_gt hs)]; ring_nf
  have hpos : 0 < Qstar a β p ^ p := rpow_pos_of_pos hs p
  field_simp
  rw [e, hsp]
  field_simp

/-- (1) 最大はただ一つ Q* で。 -/
theorem profit_max {Q : ℝ} (hQ : 0 ≤ Q) (hne : Q ≠ Qstar a β p) :
    profit a β p Q < profit a β p (Qstar a β p) := by
  have hs := Qstar_pos ha hb hp
  rw [profit_scaled ha hb hp hQ, profit_scaled ha hb hp hs.le, div_self (ne_of_gt hs), one_rpow]
  have hK : 0 < β * Qstar a β p ^ p := mul_pos hb (rpow_pos_of_pos hs p)
  apply mul_lt_mul_of_pos_left _ hK
  set t := Q / Qstar a β p
  have ht : 0 ≤ t := div_nonneg hQ hs.le
  have ht1 : t ≠ 1 := by
    intro h; apply hne; simp only [t] at h; rw [div_eq_one_iff_eq (ne_of_gt hs)] at h; exact h
  have hb' := one_add_mul_self_lt_rpow_one_add (s := t - 1) (by linarith) (sub_ne_zero.mpr ht1) hp
  rw [show 1 + (t - 1) = t by ring] at hb'
  linarith

/-- (2) Π(Q₀) = 0。 -/
theorem profit_zero : profit a β p (Q0 a β p) = 0 := by
  unfold profit Q0
  have hab : 0 < a / β := div_pos ha hb
  have e : ((a / β) ^ (1 / (p - 1))) ^ p = (a / β) ^ (1 / (p - 1)) * (a / β) := by
    rw [← rpow_mul hab.le, ← rpow_add_one (ne_of_gt hab).symm.symm]
    · congr 1; field_simp; ring
  rw [e]; field_simp; ring

/-- (3) Q₀/Q* = p^(1/(p−1))。 -/
theorem ratio_eq : Q0 a β p / Qstar a β p = p ^ (1 / (p - 1)) := by
  unfold Q0 Qstar
  have hp0 : 0 < p := by linarith
  rw [← div_rpow (by positivity) (by positivity)]
  congr 1; field_simp

omit ha hb in
/-- (3) 1 < p^(1/(p−1)) < e。 -/
theorem ratio_bounds : 1 < p ^ (1 / (p - 1)) ∧ p ^ (1 / (p - 1)) < exp 1 := by
  have hp0 : 0 < p := by linarith
  have hlog : 0 < log p := log_pos hp
  have hlog2 : log p < p - 1 := log_lt_sub_one_of_pos hp0 (ne_of_gt hp)
  rw [rpow_def_of_pos hp0]
  constructor
  · calc (1 : ℝ) = exp 0 := exp_zero.symm
      _ < exp (log p * (1 / (p - 1))) :=
          exp_lt_exp.mpr (mul_pos hlog (div_pos one_pos (by linarith)))
  · apply exp_lt_exp.mpr
    rw [mul_one_div, div_lt_one (by linarith)]; exact hlog2

end

/-! ### 収益の冪を q にした一般の形 -/

section general

variable {a β p q : ℝ} (ha : 0 < a) (hb : 0 < β) (hq : 0 < q) (hqp : q < p)
include ha hb hq hqp

omit ha hb hq in
/-- Q > 0 で Q^(p−q) = c ⇔ Q = c^(1/(p−q))（c > 0）。 -/
theorem pow_eq_iff {Q c : ℝ} (hQ : 0 < Q) (hc : 0 < c) :
    Q ^ (p - q) = c ↔ Q = c ^ (1 / (p - q)) := by
  have hd : p - q ≠ 0 := by linarith
  constructor
  · intro h; rw [← h, ← rpow_mul hQ.le, mul_one_div_cancel hd, rpow_one]
  · intro h; rw [h, ← rpow_mul hc.le, one_div_mul_cancel hd, rpow_one]

/-- (4) 内点の停留点：qaQ^(q−1) = pβQ^(p−1) ⇔ Q = (qa/(pβ))^(1/(p−q))。 -/
theorem critical_iff {Q : ℝ} (hQ : 0 < Q) :
    q * a * Q ^ (q - 1) = p * β * Q ^ (p - 1) ↔ Q = (q * a / (p * β)) ^ (1 / (p - q)) := by
  have hp0 : 0 < p := by linarith
  rw [← pow_eq_iff hqp hQ (by positivity)]
  have e : Q ^ (p - 1) = Q ^ (q - 1) * Q ^ (p - q) := by
    rw [← rpow_add hQ]; ring_nf
  rw [e]
  have h1 : 0 < Q ^ (q - 1) := rpow_pos_of_pos hQ _
  constructor
  · intro h; field_simp; nlinarith [h]
  · intro h; rw [h]; field_simp

omit hq in
/-- (4) ゼロに戻る：aQ^q = βQ^p ⇔ Q = (a/β)^(1/(p−q))。 -/
theorem zero_iff {Q : ℝ} (hQ : 0 < Q) :
    a * Q ^ q = β * Q ^ p ↔ Q = (a / β) ^ (1 / (p - q)) := by
  rw [← pow_eq_iff hqp hQ (by positivity)]
  have e : Q ^ p = Q ^ q * Q ^ (p - q) := by rw [← rpow_add hQ]; ring_nf
  rw [e]
  have h1 : 0 < Q ^ q := rpow_pos_of_pos hQ _
  constructor
  · intro h; field_simp; nlinarith [h]
  · intro h; rw [h]; field_simp

/-- (4) 比は (p/q)^(1/(p−q))。 -/
theorem ratio_general :
    (a / β) ^ (1 / (p - q)) / (q * a / (p * β)) ^ (1 / (p - q)) = (p / q) ^ (1 / (p - q)) := by
  have hp0 : 0 < p := by linarith
  rw [← div_rpow (by positivity) (by positivity)]
  congr 1; field_simp

end general

/-- (4) 冪の差が同じ 1/2 でも、比は 9/4 と 25/16 で異なる。 -/
theorem not_only_difference :
    ((3 / 2 : ℝ) / 1) ^ (1 / ((3 / 2 : ℝ) - 1)) = 9 / 4 ∧
    ((5 / 2 : ℝ) / 2) ^ (1 / ((5 / 2 : ℝ) - 2)) = 25 / 16 := by
  constructor
  · rw [show (1 : ℝ) / ((3 / 2 : ℝ) - 1) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num
  · rw [show (1 : ℝ) / ((5 / 2 : ℝ) - 2) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num

end Paper710

end Yamagishi
