/-
論文327『二つの曲線は 0.083 パーセントしか違わず、それでも別物である』の格上げ（一部だけ）。

原稿（327_yamagishi_two_curves_agree_to_within_a_tenth_of_a_percent_and_are_not_the_same/…_jp.tex）は、
懸垂線 y = a(cosh(x/a) − 1) と放物線を、a = 1 での六点の差（表 2.1）と、半スパン 1 での六つのたるみ
f = 0.02〜0.5 の最大差（表 4.1）で比べている。cosh の展開で差が x⁴/(24a³) から出ることは一般の a で書く。

ここで証明した言明（同じ支点 (±L, f) と同じ最下点（原点）を持つ二曲線、a > 0、L > 0、
f = a(cosh(L/a) − 1)、放物線 y = f x²/L²）：
  (1) `k_strictMonoOn`：k(y) = (cosh y − 1)/y² は y > 0 で狭義に増える
      （y cosh y − sinh y > 0 と y sinh y − 2(cosh y − 1) > 0 を導関数の符号から順に出した）。
  (2) `parabola_above`：どの f > 0 でも、0 < |x| < L で放物線は懸垂線より真に上にある。
  (3) `catenary_through_supports`：懸垂線は (±L, f) と原点を通る（放物線も同じ）。
止めた所：最大の差が f³/(12L²) より真に小さいこと、f/L → 0 でその値に漸近し位置が L/√2 に寄ること。
証明には差の冪級数と f³/12 の冪級数を係数ごとに比べる手間が要り、今回は形式化していない。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）

A catenary and a parabola through the same supports (±L, f) and the same lowest point never meet in
between: for every sag f > 0 the parabola lies strictly above the catenary for 0 < |x| < L, because
(cosh y − 1)/y² is strictly increasing. The bound f³/(12L²) on the largest gap is not formalized.
-/
import Mathlib

namespace Yamagishi

namespace Paper327

open Real Set

/-- n(y) = y cosh y − sinh y は y > 0 で正。 -/
theorem n_pos {y : ℝ} (hy : 0 < y) : 0 < y * cosh y - sinh y := by
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun t => t * cosh t - sinh t) (t * sinh t) t := by
    intro t _
    have h := ((hasDerivAt_id' t).mul (hasDerivAt_cosh t)).sub (hasDerivAt_sinh t)
    convert h using 1; ring
  have hm := strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (by
      intro t ht
      rw [interior_Ici] at ht
      exact mul_pos ht (sinh_pos_iff.mpr ht))
  have := hm (mem_Ici.mpr (le_refl (0 : ℝ))) (show y ∈ Ici (0 : ℝ) from hy.le) hy
  simpa using this

/-- m(y) = y sinh y − 2(cosh y − 1) は y > 0 で正。 -/
theorem m_pos {y : ℝ} (hy : 0 < y) : 0 < y * sinh y - 2 * (cosh y - 1) := by
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun t => t * sinh t - 2 * (cosh t - 1))
      (t * cosh t - sinh t) t := by
    intro t _
    have h := ((hasDerivAt_id' t).mul (hasDerivAt_sinh t)).sub
      (((hasDerivAt_cosh t).sub_const 1).const_mul 2)
    convert h using 1; ring
  have hm := strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (by
      intro t ht
      rw [interior_Ici] at ht
      exact n_pos ht)
  have := hm (mem_Ici.mpr (le_refl (0 : ℝ))) (show y ∈ Ici (0 : ℝ) from hy.le) hy
  simpa using this

/-- (1) k(y) = (cosh y − 1)/y² は y > 0 で狭義に増える。 -/
theorem k_strictMonoOn : StrictMonoOn (fun y => (cosh y - 1) / y ^ 2) (Ioi 0) := by
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun y => (cosh y - 1) / y ^ 2)
      ((t * sinh t - 2 * (cosh t - 1)) / t ^ 3) t := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h := ((hasDerivAt_cosh t).sub_const 1).div (hasDerivAt_pow 2 t) (pow_pos ht' 2).ne'
    convert h using 1
    field_simp
    ring
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioi 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
  intro t ht
  rw [interior_Ioi] at ht
  have ht' : (0 : ℝ) < t := ht
  exact div_pos (m_pos ht') (by positivity)

/-- (3) 懸垂線は (±L, f) と原点を通る。 -/
theorem catenary_through_supports (a L : ℝ) :
    a * (cosh (L / a) - 1) = a * (cosh (L / a) - 1) ∧
    a * (cosh (-L / a) - 1) = a * (cosh (L / a) - 1) ∧ a * (cosh (0 / a) - 1) = 0 := by
  refine ⟨rfl, ?_, by simp⟩
  rw [neg_div, cosh_neg]

/-- (2) 0 < |x| < L で、同じ支点の放物線 f x²/L² は懸垂線 a(cosh(x/a) − 1) より真に上にある。 -/
theorem parabola_above {a L x : ℝ} (ha : 0 < a) (hL : 0 < L) (hx0 : 0 < |x|) (hxL : |x| < L) :
    a * (cosh (x / a) - 1) < a * (cosh (L / a) - 1) * x ^ 2 / L ^ 2 := by
  set u := |x| / a with hu
  set U := L / a with hU
  have hu0 : 0 < u := div_pos hx0 ha
  have huU : u < U := div_lt_div_of_pos_right hxL ha
  have hk := k_strictMonoOn (show u ∈ Ioi (0 : ℝ) from hu0)
    (show U ∈ Ioi (0 : ℝ) from hu0.trans huU) huU
  simp only at hk
  have hcx : cosh (x / a) = cosh u := by
    rw [hu, ← cosh_abs, abs_div, abs_of_pos ha]
  rw [hcx]
  have hx2 : x ^ 2 = (a * u) ^ 2 := by
    rw [hu, mul_div_cancel₀ _ ha.ne', sq_abs]
  have hL2 : L ^ 2 = (a * U) ^ 2 := by rw [hU, mul_div_cancel₀ _ ha.ne']
  rw [hx2, hL2]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hk
  rw [lt_div_iff₀ (by positivity)]
  have hU0 : 0 < U := hu0.trans huU
  have : 0 < a ^ 3 := by positivity
  nlinarith [mul_lt_mul_of_pos_left hk this]

end Paper327

end Yamagishi
