/-
論文505『「勢力圏」は三つあり、質量比を 1000 分の 1 にすると別々に縮む』の格上げ（一般の形）。

原稿（505_yamagishi_sphere_of_influence_is_three/…_jp.tex）は、
ヒル半径 r_H = a(q/3)^(1/3)、ラプラスの作用圏 r_S = a·q^(2/5)、重力が等しくなる点
r_E/(a − r_E) = √q の三つを、地球と太陽（q = 3.002735×10⁻⁶）の一点で数え、q を 1/1000 にしたときの
縮み方を出している。「q が小さいとき、ヒル > 作用圏 > 釣り合い点」とだけ書いている。

ここで証明した言明（a > 0、q > 0 のどの値でも）：
  (1) `rE_spec`：r_E = a√q/(1 + √q) は r_E/(a − r_E) = √q を満たす。
  (2) `rE_lt_rS`・`rE_lt_rH`：どの q でも r_E < r_S かつ r_E < r_H。
  (3) `rS_lt_rH_iff`・`rH_eq_rS_iff`・`rH_lt_rS_iff`：r_H > r_S ⇔ q < 1/243 = 3⁻⁵、等しい ⇔ q = 1/243、
      q > 1/243 では順序が逆。
  (4) `ratio_ge`・`ratio_eq_min_iff`：r_H/r_E ≥ (3/2)^(2/3)、等号 ⇔ q = 1/4。
      `ratio_strictAntiOn`：r_H/r_E は 0 < q ≤ 1/4 で q について狭義に減る（q が小さいほどひらきが大きい）。
  (5) `shrink_rH`・`shrink_rS`・`shrink_rE_lt`：q を 1/k 倍（k > 1）にすると、r_H はちょうど k^(1/3) 分の 1、
      r_S は k^(2/5) 分の 1、r_E は √k 分の 1 より少なく縮む。
足した所：原稿は順序を「q が小さいとき」とだけ書く。その境目が q = 1/243 であること（月と地球の
q ≈ 0.0123 は境目より大きいので、模型の式の上でもヒル半径が作用圏より小さい）。
形式化していないもの：三つの式を力学から導く所（定義として置いた）、地球の数値。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）

For every mass ratio q > 0 the equal-gravity point lies inside both the Hill sphere and the
Laplace sphere of influence; the Hill radius exceeds the Laplace radius exactly when q < 1/243,
and the ratio of the Hill radius to the equal-gravity radius is at least (3/2)^(2/3), with
equality only at q = 1/4.
-/
import Mathlib

namespace Yamagishi

namespace Paper505

open Real Set

/-- ヒル半径。 -/
noncomputable def rH (a q : ℝ) : ℝ := a * (q / 3) ^ ((1 : ℝ) / 3)

/-- ラプラスの作用圏。 -/
noncomputable def rS (a q : ℝ) : ℝ := a * q ^ ((2 : ℝ) / 5)

/-- 重力が等しくなる点。 -/
noncomputable def rE (a q : ℝ) : ℝ := a * (√q / (1 + √q))

theorem rpow_pow_eq {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℕ) : (x ^ y) ^ n = x ^ (y * n) := by
  rw [← rpow_natCast, ← rpow_mul hx]

/-- (1) r_E/(a − r_E) = √q。 -/
theorem rE_spec {a : ℝ} (q : ℝ) (ha : 0 < a) : rE a q / (a - rE a q) = √q := by
  have hs := sqrt_nonneg q
  have h1 : 0 < 1 + √q := by linarith
  unfold rE
  have : a - a * (√q / (1 + √q)) = a / (1 + √q) := by field_simp; ring
  rw [this]
  field_simp

/-- c = 3^(1/3) の三乗は 3。 -/
theorem cbrt3_cube : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 3 := by
  rw [rpow_pow_eq (by norm_num)]; norm_num

/-- s = q^(1/6) と置いた形：√q = s³、q^(1/3) = s²。 -/
theorem sixth_root {q : ℝ} (hq : 0 ≤ q) :
    (q ^ ((1 : ℝ) / 6)) ^ 3 = √q ∧ (q ^ ((1 : ℝ) / 6)) ^ 2 = q ^ ((1 : ℝ) / 3) ∧
    (q ^ ((1 : ℝ) / 6)) ^ 6 = q := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rpow_pow_eq hq, sqrt_eq_rpow]; norm_num
  · rw [rpow_pow_eq hq]; norm_num
  · rw [rpow_pow_eq hq]; norm_num

/-- s = q^(1/15) と置いた形：q^(1/3) = s⁵、q^(2/5) = s⁶、q = s¹⁵。 -/
theorem fifteenth_root {q : ℝ} (hq : 0 ≤ q) :
    (q ^ ((1 : ℝ) / 15)) ^ 5 = q ^ ((1 : ℝ) / 3) ∧ (q ^ ((1 : ℝ) / 15)) ^ 6 = q ^ ((2 : ℝ) / 5) ∧
    (q ^ ((1 : ℝ) / 15)) ^ 15 = q := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rpow_pow_eq hq]; norm_num
  · rw [rpow_pow_eq hq]; norm_num
  · rw [rpow_pow_eq hq]; norm_num

/-- (q/3)^(1/3) = q^(1/3)/c。 -/
theorem div3_rpow {q : ℝ} (hq : 0 ≤ q) :
    (q / 3) ^ ((1 : ℝ) / 3) = q ^ ((1 : ℝ) / 3) / (3 : ℝ) ^ ((1 : ℝ) / 3) :=
  div_rpow hq (by norm_num) _

/-- (2) どの q > 0 でも r_E < r_S。 -/
theorem rE_lt_rS {a q : ℝ} (ha : 0 < a) (hq : 0 < q) : rE a q < rS a q := by
  unfold rE rS
  apply mul_lt_mul_of_pos_left _ ha
  set s := q ^ ((1 : ℝ) / 10) with hs
  have hs0 : 0 < s := rpow_pos_of_pos hq _
  have h5 : s ^ 5 = √q := by rw [hs, rpow_pow_eq hq.le, sqrt_eq_rpow]; norm_num
  have h4 : s ^ 4 = q ^ ((2 : ℝ) / 5) := by rw [hs, rpow_pow_eq hq.le]; norm_num
  rw [← h5, ← h4, div_lt_iff₀ (by positivity)]
  -- s⁵ < s⁴(1 + s⁵) ⇔ s < 1 + s⁵
  have key : s < 1 + s ^ 5 := by
    rcases le_or_gt s 1 with h | h
    · have := pow_pos hs0 5; linarith
    · have : s ≤ s ^ 5 := by
        calc s = s ^ 1 := (pow_one s).symm
          _ ≤ s ^ 5 := pow_le_pow_right₀ h.le (by norm_num)
      linarith
  have h4p : 0 < s ^ 4 := pow_pos hs0 4
  nlinarith

/-- (2) どの q > 0 でも r_E < r_H。芯は u > 0 で u³ − 3u + 3 = (u − 1)²(u + 2) + 1 > 0。 -/
theorem rE_lt_rH {a q : ℝ} (ha : 0 < a) (hq : 0 < q) : rE a q < rH a q := by
  unfold rE rH
  apply mul_lt_mul_of_pos_left _ ha
  obtain ⟨h3, h2, -⟩ := sixth_root hq.le
  set s := q ^ ((1 : ℝ) / 6) with hs
  set c := (3 : ℝ) ^ ((1 : ℝ) / 3) with hc
  have hs0 : 0 < s := rpow_pos_of_pos hq _
  have hc0 : 0 < c := rpow_pos_of_pos (by norm_num) _
  have hc3 : c ^ 3 = 3 := cbrt3_cube
  rw [div3_rpow hq.le, ← h3, ← h2, ← hc]
  rw [div_lt_div_iff₀ (by positivity) hc0]
  -- s³·c < s²(1 + s³) ⇔ c·s < 1 + s³；u = c·s で 3u < 3 + u³
  have key : c * s < 1 + s ^ 3 := by
    set u := c * s
    have hu : 0 < u := mul_pos hc0 hs0
    have hu3 : u ^ 3 = 3 * s ^ 3 := by simp only [u]; rw [mul_pow, hc3]
    nlinarith [sq_nonneg (u - 1)]
  have h2p : 0 < s ^ 2 := pow_pos hs0 2
  nlinarith

/-- 芯：c·q^(1/15) < 1 ⇔ q < 1/243。 -/
theorem cs_lt_one_iff {q : ℝ} (hq : 0 < q) :
    (3 : ℝ) ^ ((1 : ℝ) / 3) * q ^ ((1 : ℝ) / 15) < 1 ↔ q < 1 / 243 := by
  obtain ⟨-, -, h15⟩ := fifteenth_root hq.le
  have hc0 : 0 < (3 : ℝ) ^ ((1 : ℝ) / 3) := rpow_pos_of_pos (by norm_num) _
  have hs0 : 0 < q ^ ((1 : ℝ) / 15) := rpow_pos_of_pos hq _
  have hpow : ((3 : ℝ) ^ ((1 : ℝ) / 3) * q ^ ((1 : ℝ) / 15)) ^ 15 = 243 * q := by
    rw [mul_pow, h15, show (15 : ℕ) = 3 * 5 by norm_num, pow_mul, cbrt3_cube]; norm_num
  rw [← pow_lt_one_iff_of_nonneg (by positivity) (by norm_num : (15 : ℕ) ≠ 0), hpow]
  constructor <;> intro h <;> linarith

/-- r_H と r_S の比べ方を c·s と 1 の比べ方に直す。 -/
theorem rH_rS_form (a : ℝ) {q : ℝ} (hq : 0 < q) :
    rH a q = a * ((q ^ ((1 : ℝ) / 15)) ^ 5 / (3 : ℝ) ^ ((1 : ℝ) / 3)) ∧
    rS a q = a * (q ^ ((1 : ℝ) / 15)) ^ 6 := by
  obtain ⟨h5, h6, -⟩ := fifteenth_root hq.le
  unfold rH rS
  rw [div3_rpow hq.le, h5, h6]
  exact ⟨rfl, rfl⟩

/-- (3) r_S < r_H ⇔ q < 1/243。 -/
theorem rS_lt_rH_iff {a q : ℝ} (ha : 0 < a) (hq : 0 < q) : rS a q < rH a q ↔ q < 1 / 243 := by
  obtain ⟨eH, eS⟩ := rH_rS_form a hq
  rw [eH, eS, mul_lt_mul_iff_right₀ ha, ← cs_lt_one_iff hq]
  set s := q ^ ((1 : ℝ) / 15)
  set c := (3 : ℝ) ^ ((1 : ℝ) / 3)
  have hc0 : 0 < c := rpow_pos_of_pos (by norm_num) _
  have hs0 : 0 < s := rpow_pos_of_pos hq _
  rw [lt_div_iff₀ hc0, show s ^ 6 * c = (c * s) * s ^ 5 by ring]
  constructor
  · intro h; by_contra h'
    have h'' : 1 ≤ c * s := le_of_not_gt h'
    nlinarith [pow_pos hs0 5]
  · intro h; nlinarith [pow_pos hs0 5]

/-- (3) r_H = r_S ⇔ q = 1/243。 -/
theorem rH_eq_rS_iff {a q : ℝ} (ha : 0 < a) (hq : 0 < q) : rH a q = rS a q ↔ q = 1 / 243 := by
  obtain ⟨eH, eS⟩ := rH_rS_form a hq
  obtain ⟨-, -, h15⟩ := fifteenth_root hq.le
  rw [eH, eS, mul_right_inj' ha.ne']
  set s := q ^ ((1 : ℝ) / 15)
  set c := (3 : ℝ) ^ ((1 : ℝ) / 3)
  have hc0 : 0 < c := rpow_pos_of_pos (by norm_num) _
  have hs0 : 0 < s := rpow_pos_of_pos hq _
  have hc3 : c ^ 3 = 3 := cbrt3_cube
  rw [div_eq_iff hc0.ne']
  have e1 : s ^ 5 = s ^ 6 * c ↔ c * s = 1 := by
    constructor
    · intro h
      have h5 : 0 < s ^ 5 := pow_pos hs0 5
      have : s ^ 5 * (c * s) = s ^ 5 * 1 := by
        rw [show s ^ 5 * (c * s) = s ^ 6 * c by ring, mul_one]; exact h.symm
      exact mul_left_cancel₀ h5.ne' this
    · intro h; calc s ^ 5 = s ^ 5 * (c * s) := by rw [h, mul_one]
        _ = s ^ 6 * c := by ring
  rw [e1]
  have hpow : (c * s) ^ 15 = 243 * q := by
    rw [mul_pow, h15, show (15 : ℕ) = 3 * 5 by norm_num, pow_mul, hc3]; norm_num
  constructor
  · intro h; rw [h, one_pow] at hpow; linarith
  · intro h
    rw [h] at hpow
    have h1 : (c * s) ^ 15 = 1 ^ 15 := by rw [hpow]; norm_num
    exact (pow_left_inj₀ (by positivity) zero_le_one (by norm_num : (15 : ℕ) ≠ 0)).mp h1

/-- (3) r_H < r_S ⇔ q > 1/243。 -/
theorem rH_lt_rS_iff {a q : ℝ} (ha : 0 < a) (hq : 0 < q) : rH a q < rS a q ↔ 1 / 243 < q := by
  constructor
  · intro h
    rcases lt_trichotomy q (1 / 243) with h1 | h1 | h1
    · exact absurd ((rS_lt_rH_iff ha hq).mpr h1) (lt_asymm h)
    · exact absurd ((rH_eq_rS_iff ha hq).mpr h1) (ne_of_lt h)
    · exact h1
  · intro h
    rcases lt_trichotomy (rH a q) (rS a q) with h1 | h1 | h1
    · exact h1
    · exact absurd ((rH_eq_rS_iff ha hq).mp h1) (ne_of_gt h)
    · exact absurd ((rS_lt_rH_iff ha hq).mp h1) (lt_asymm h)

/-- r_H/r_E を s = q^(1/6) で書く：(1/s + s²)/c。 -/
theorem ratio_form {a q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    rH a q / rE a q =
      (1 / q ^ ((1 : ℝ) / 6) + (q ^ ((1 : ℝ) / 6)) ^ 2) / (3 : ℝ) ^ ((1 : ℝ) / 3) := by
  obtain ⟨h3, h2, -⟩ := sixth_root hq.le
  unfold rH rE
  rw [div3_rpow hq.le, ← h3, ← h2]
  set s := q ^ ((1 : ℝ) / 6)
  have hs0 : 0 < s := rpow_pos_of_pos hq _
  have hc0 : 0 < (3 : ℝ) ^ ((1 : ℝ) / 3) := rpow_pos_of_pos (by norm_num) _
  field_simp

/-- 最小値の形：3·2^(−2/3)/3^(1/3) = (3/2)^(2/3)。 -/
theorem min_value_eq :
    3 * ((2 : ℝ) ^ (-((1 : ℝ) / 3))) ^ 2 / (3 : ℝ) ^ ((1 : ℝ) / 3) =
      (3 / 2 : ℝ) ^ ((2 : ℝ) / 3) := by
  rw [rpow_pow_eq (by norm_num), div_rpow (by norm_num) (by norm_num)]
  have hc0 : 0 < (3 : ℝ) ^ ((1 : ℝ) / 3) := rpow_pos_of_pos (by norm_num) _
  have h3 : (3 : ℝ) / 3 ^ ((1 : ℝ) / 3) = 3 ^ ((2 : ℝ) / 3) := by
    rw [div_eq_iff hc0.ne', ← rpow_add (by norm_num)]; norm_num
  have h2 : (2 : ℝ) ^ (-((1 : ℝ) / 3) * ((2 : ℕ) : ℝ)) = ((2 : ℝ) ^ ((2 : ℝ) / 3))⁻¹ := by
    rw [← rpow_neg (by norm_num)]; norm_num
  rw [h2, show (3 : ℝ) * ((2 : ℝ) ^ ((2 : ℝ) / 3))⁻¹ / 3 ^ ((1 : ℝ) / 3)
      = (3 / 3 ^ ((1 : ℝ) / 3)) * ((2 : ℝ) ^ ((2 : ℝ) / 3))⁻¹ by ring, h3]
  exact (div_eq_mul_inv _ _).symm

/-- 芯：m = 2^(−1/3)（m³ = 1/2）について、s > 0 で 1/s + s² ≥ 3m²、等号 ⇔ s = m。
s³ − 3m²s + 2m³ = (s − m)²(s + 2m)。 -/
theorem amgm_core {s : ℝ} (hs : 0 < s) :
    3 * ((2 : ℝ) ^ (-((1 : ℝ) / 3))) ^ 2 ≤ 1 / s + s ^ 2 ∧
    (1 / s + s ^ 2 = 3 * ((2 : ℝ) ^ (-((1 : ℝ) / 3))) ^ 2 ↔ s = (2 : ℝ) ^ (-((1 : ℝ) / 3))) := by
  set m := (2 : ℝ) ^ (-((1 : ℝ) / 3))
  have hm0 : 0 < m := rpow_pos_of_pos (by norm_num) _
  have hm3 : m ^ 3 = 1 / 2 := by simp only [m]; rw [rpow_pow_eq (by norm_num)]; norm_num
  have hid : s * (1 / s + s ^ 2 - 3 * m ^ 2) = (s - m) ^ 2 * (s + 2 * m) := by
    field_simp; nlinarith [hm3]
  constructor
  · have h0 : 0 ≤ s * (1 / s + s ^ 2 - 3 * m ^ 2) := by rw [hid]; positivity
    by_contra hneg
    have := mul_neg_of_pos_of_neg hs (by linarith [lt_of_not_ge hneg] :
      1 / s + s ^ 2 - 3 * m ^ 2 < 0)
    linarith
  · constructor
    · intro h
      have : (s - m) ^ 2 * (s + 2 * m) = 0 := by rw [← hid, h]; ring
      rcases mul_eq_zero.mp this with h1 | h1
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1; linarith
      · linarith
    · intro h
      have : s * (1 / s + s ^ 2 - 3 * m ^ 2) = 0 := by rw [hid, h]; ring
      rcases mul_eq_zero.mp this with h1 | h1
      · linarith
      · linarith

/-- (4) r_H/r_E ≥ (3/2)^(2/3)。 -/
theorem ratio_ge {a q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    (3 / 2 : ℝ) ^ ((2 : ℝ) / 3) ≤ rH a q / rE a q := by
  rw [ratio_form ha hq, ← min_value_eq]
  have hc0 : 0 < (3 : ℝ) ^ ((1 : ℝ) / 3) := rpow_pos_of_pos (by norm_num) _
  exact div_le_div_of_nonneg_right (amgm_core (rpow_pos_of_pos hq _)).1 hc0.le

/-- (4) 等号 ⇔ q = 1/4。 -/
theorem ratio_eq_min_iff {a q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    rH a q / rE a q = (3 / 2 : ℝ) ^ ((2 : ℝ) / 3) ↔ q = 1 / 4 := by
  rw [ratio_form ha hq, ← min_value_eq]
  have hc0 : 0 < (3 : ℝ) ^ ((1 : ℝ) / 3) := rpow_pos_of_pos (by norm_num) _
  rw [div_left_inj₀ hc0.ne', (amgm_core (rpow_pos_of_pos hq _)).2]
  obtain ⟨-, -, h6⟩ := sixth_root hq.le
  have hm6 : ((2 : ℝ) ^ (-((1 : ℝ) / 3))) ^ 6 = 1 / 4 := by
    rw [rpow_pow_eq (by norm_num)]; norm_num
  constructor
  · intro h; rw [← h6, h, hm6]
  · intro h
    have e : (q ^ ((1 : ℝ) / 6)) ^ 6 = ((2 : ℝ) ^ (-((1 : ℝ) / 3))) ^ 6 := by rw [h6, hm6, h]
    exact (pow_left_inj₀ (rpow_pos_of_pos hq _).le (rpow_pos_of_pos (by norm_num) _).le
      (by norm_num : (6 : ℕ) ≠ 0)).mp e

/-- (4) r_H/r_E は 0 < q ≤ 1/4 で狭義に減る。 -/
theorem ratio_strictAntiOn {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (fun q => rH a q / rE a q) (Ioc 0 (1 / 4)) := by
  intro x hx y hy hxy
  simp only
  rw [ratio_form ha hx.1, ratio_form ha hy.1]
  have hc0 : 0 < (3 : ℝ) ^ ((1 : ℝ) / 3) := rpow_pos_of_pos (by norm_num) _
  apply div_lt_div_of_pos_right _ hc0
  set s := x ^ ((1 : ℝ) / 6)
  set t := y ^ ((1 : ℝ) / 6)
  have hs0 : 0 < s := rpow_pos_of_pos hx.1 _
  have hst : s < t := rpow_lt_rpow hx.1.le hxy (by norm_num)
  -- t ≤ m、m³ = 1/2
  have ht6 : t ^ 6 ≤ 1 / 4 := by obtain ⟨-, -, h6⟩ := sixth_root hy.1.le; rw [h6]; exact hy.2
  have ht3 : t ^ 3 ≤ 1 / 2 := by nlinarith [pow_pos (hs0.trans hst) 3]
  have ht0 : 0 < t := hs0.trans hst
  -- (1/s + s²) − (1/t + t²) = (t − s)(1 − st(s + t))/(st)
  have hprod : s * t * (s + t) < 1 := by
    have h1 : s * t * (s + t) < t * t * (t + t) := by
      have : s * t < t * t := mul_lt_mul_of_pos_right hst ht0
      have : s + t < t + t := by linarith
      nlinarith [mul_pos hs0 ht0]
    nlinarith
  rw [div_add' _ _ _ hs0.ne', div_add' _ _ _ ht0.ne', div_lt_div_iff₀ ht0 hs0]
  nlinarith [mul_pos hs0 ht0, sub_pos.mpr hst]

/-- (5) q を 1/k 倍にすると、r_H はちょうど k^(1/3) 分の 1。 -/
theorem shrink_rH {a q k : ℝ} (hq : 0 ≤ q) (hk : 0 < k) :
    rH a q = k ^ ((1 : ℝ) / 3) * rH a (q / k) := by
  unfold rH
  rw [div_div, mul_comm k 3, ← div_div, div_rpow (by positivity) hk.le]
  have : 0 < k ^ ((1 : ℝ) / 3) := rpow_pos_of_pos hk _
  field_simp

/-- (5) r_S はちょうど k^(2/5) 分の 1。 -/
theorem shrink_rS {a q k : ℝ} (hq : 0 ≤ q) (hk : 0 < k) :
    rS a q = k ^ ((2 : ℝ) / 5) * rS a (q / k) := by
  unfold rS
  rw [div_rpow hq hk.le]
  have : 0 < k ^ ((2 : ℝ) / 5) := rpow_pos_of_pos hk _
  field_simp

/-- (5) r_E は √k 分の 1 より少なく縮む（k > 1）。 -/
theorem shrink_rE_lt {a q k : ℝ} (ha : 0 < a) (hq : 0 < q) (hk : 1 < k) :
    rE a q < √k * rE a (q / k) := by
  unfold rE
  have hk0 : 0 < k := by linarith
  have hsq : 0 < √q := sqrt_pos.mpr hq
  have hsk : 1 < √k := by rw [show (1 : ℝ) = √1 by simp]; exact sqrt_lt_sqrt (by norm_num) hk
  rw [sqrt_div hq.le]
  set u := √q
  set v := √k
  have hv0 : 0 < v := by linarith
  rw [show v * (a * (u / v / (1 + u / v))) = a * (u / (1 + u / v)) by field_simp]
  apply mul_lt_mul_of_pos_left _ ha
  apply div_lt_div_of_pos_left hsq (by positivity)
  have : u / v < u := div_lt_self hsq hsk
  linarith

end Paper505

end Yamagishi
