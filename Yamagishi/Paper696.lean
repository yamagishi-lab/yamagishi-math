/-
論文696『個体群が戻れなくなる線』の格上げ（一般の形・芯）。

原稿（696_yamagishi_the_line_a_population_cannot_return_from/…_jp.tex）は、強いアレー効果の模型
dN/dt = rN(N/A − 1)(1 − N/K) を、r = 0.5・A = 100・K = 1000 の一組で、N = 99 と 101 の増減の符号、
いくつかの N の値、60 年後の値を数値で出している。

ここで証明した言明（すべての r > 0、0 < A < K、任意の時間の長さ T > 0）：
  f(N) = rN(N/A − 1)(1 − N/K) と置き、x を [0, T] の上の解（x′ = f(x)）とする。
  (1) `f_neg_low`・`f_pos_mid`・`f_neg_high`：f は (0, A) で負、(A, K) で正、(K, ∞) で負。
      0・A・K は釣り合いの点。
  (2) `no_hit`：解が釣り合いの点 e に時刻 t₁ ∈ [0, T] で着くなら、最初から e にいた
      （解の一意性から。特に、0 < x(0) なら有限の時間で 0 にならない＝有限時間の絶滅は無い）。
  (3) `stays_low`：x(0) ∈ (0, A) なら、[0, T] でずっと (0, A) にいて、狭義に減る。
      `stays_mid`：x(0) ∈ (A, K) ならずっと (A, K) にいて、狭義に増える。
      `stays_high`：x(0) > K ならずっと K より上にいて、狭義に減る。
  (4) `not_faster_lower`（原稿の要旨の第三への反例）：r = 0.5・A = 100・K = 1000 で、N = 10 での減る
      速さ 4.455 は N = 50 での 11.875 より小さい。「下がるほど速く減る」は A より下の全域では
      成り立たない（下読みの AI の指摘を確かめた）。
定義に置いたもの：強いアレー効果の式（原稿の式）。解の存在は仮定とした（解を与えられたものとして
その性質を示す）。
形式化していないもの：x(t) → 0（(0, A) から）・x(t) → K（A より上から）の極限、絶滅までの時間
60.837 年（下読みの AI の注意のとおり、解は有限の時間で 0 にならないので、この値は閾値の置き方で
決まり、原稿には閾値が書かれていない）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper696

open Set

/-- 強いアレー効果の増え方。 -/
noncomputable def f (r A K N : ℝ) : ℝ := r * N * (N / A - 1) * (1 - N / K)

variable {r A K : ℝ}

theorem f_neg_low (hr : 0 < r) (hA : 0 < A) (hAK : A < K) {N : ℝ} (h0 : 0 < N) (h1 : N < A) :
    f r A K N < 0 := by
  unfold f
  have hK : 0 < K := by linarith
  have a : N / A - 1 < 0 := by rw [div_sub_one hA.ne']; exact div_neg_of_neg_of_pos (by linarith) hA
  have b : 0 < 1 - N / K := by rw [sub_pos, div_lt_one hK]; linarith
  have := mul_pos hr h0
  have := mul_neg_of_pos_of_neg this a
  exact mul_neg_of_neg_of_pos this b

theorem f_pos_mid (hr : 0 < r) (hA : 0 < A) {N : ℝ} (h0 : A < N) (h1 : N < K) :
    0 < f r A K N := by
  unfold f
  have hK : 0 < K := by linarith
  have a : 0 < N / A - 1 := by rw [sub_pos, one_lt_div hA]; exact h0
  have b : 0 < 1 - N / K := by rw [sub_pos, div_lt_one hK]; exact h1
  have : 0 < N := by linarith
  positivity

theorem f_neg_high (hr : 0 < r) (hA : 0 < A) (hAK : A < K) {N : ℝ} (h0 : K < N) :
    f r A K N < 0 := by
  unfold f
  have hK : 0 < K := by linarith
  have a : 0 < N / A - 1 := by rw [sub_pos, one_lt_div hA]; linarith
  have b : 1 - N / K < 0 := by rw [sub_neg, one_lt_div hK]; exact h0
  have : 0 < N := by linarith
  have := mul_pos (mul_pos hr this) a
  exact mul_neg_of_pos_of_neg this b

theorem f_zero : f r A K 0 = 0 := by simp [f]
theorem f_A (hA : A ≠ 0) : f r A K A = 0 := by simp [f, div_self hA]
theorem f_K (hK : K ≠ 0) : f r A K K = 0 := by simp [f, div_self hK]

/-- f は有界な区間の上でリプシッツ。 -/
theorem f_lip (hA : 0 < A) (hK : 0 < K) (hr : 0 < r) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : NNReal, LipschitzOnWith C (f r A K) (Icc (-B) B) := by
  set C : ℝ := r * (3 * B ^ 2 / (A * K) + 2 * B * (1 / A + 1 / K) + 1) with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨⟨C, hC0⟩, LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_⟩
  show dist (f r A K u) (f r A K v) ≤ C * dist u v
  rw [Real.dist_eq, Real.dist_eq]
  have hfac : f r A K u - f r A K v = (u - v) *
      (r * (-(u ^ 2 + u * v + v ^ 2) / (A * K) + (u + v) * (1 / A + 1 / K) - 1)) := by
    unfold f; field_simp; ring
  rw [hfac, abs_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have hu' : |u| ≤ B := abs_le.mpr ⟨hu.1, hu.2⟩
  have hv' : |v| ≤ B := abs_le.mpr ⟨hv.1, hv.2⟩
  rw [abs_mul, abs_of_pos hr, hC]
  apply mul_le_mul_of_nonneg_left _ hr.le
  have h1 : |-(u ^ 2 + u * v + v ^ 2) / (A * K)| ≤ 3 * B ^ 2 / (A * K) := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < A * K)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc |u ^ 2 + u * v + v ^ 2| ≤ |u ^ 2 + u * v| + |v ^ 2| := abs_add_le _ _
      _ ≤ |u ^ 2| + |u * v| + |v ^ 2| := by linarith [abs_add_le (u ^ 2) (u * v)]
      _ = |u| ^ 2 + |u| * |v| + |v| ^ 2 := by rw [abs_pow, abs_mul, abs_pow]
      _ ≤ 3 * B ^ 2 := by nlinarith [abs_nonneg u, abs_nonneg v]
  have h2 : |(u + v) * (1 / A + 1 / K)| ≤ 2 * B * (1 / A + 1 / K) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / A + 1 / K)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc |u + v| ≤ |u| + |v| := abs_add_le _ _
      _ ≤ 2 * B := by linarith
  calc |-(u ^ 2 + u * v + v ^ 2) / (A * K) + (u + v) * (1 / A + 1 / K) - 1|
      ≤ |-(u ^ 2 + u * v + v ^ 2) / (A * K) + (u + v) * (1 / A + 1 / K)| + |(1 : ℝ)| :=
        abs_sub _ _
    _ ≤ |-(u ^ 2 + u * v + v ^ 2) / (A * K)| + |(u + v) * (1 / A + 1 / K)| + 1 := by
        rw [abs_one]; linarith [abs_add_le (-(u ^ 2 + u * v + v ^ 2) / (A * K))
          ((u + v) * (1 / A + 1 / K))]
    _ ≤ _ := by linarith

/-- 解であること：[0, T] で連続、(0, T] の各点で x′ = f(x)。 -/
structure IsSol (r A K T : ℝ) (x : ℝ → ℝ) : Prop where
  cont : ContinuousOn x (Icc 0 T)
  deriv : ∀ t ∈ Ioc 0 T, HasDerivAt x (f r A K (x t)) t

/-- (2) 解が釣り合いの点 e に時刻 t₁ で着くなら、最初から e にいた。 -/
theorem no_hit (hr : 0 < r) (hA : 0 < A) (hAK : A < K) {T : ℝ} {x : ℝ → ℝ} (hx : IsSol r A K T x)
    {e : ℝ} (he : f r A K e = 0) {t1 : ℝ} (ht1 : t1 ∈ Icc 0 T) (hxe : x t1 = e) : x 0 = e := by
  have hK : 0 < K := by linarith
  -- [0, t₁] で x と e を囲む有界な区間
  obtain ⟨B0, hB0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t1)).exists_bound_of_continuousOn
    (hx.cont.mono (Icc_subset_Icc_right ht1.2))
  set B := max (max B0 |e|) 0
  have hB : 0 ≤ B := le_max_right _ _
  obtain ⟨C, hC⟩ := f_lip hA hK hr B hB
  have hmem : ∀ y, |y| ≤ B → y ∈ Icc (-B) B := fun y hy => ⟨by linarith [neg_abs_le y],
    by linarith [le_abs_self y]⟩
  have hsol := ODE_solution_unique_of_mem_Icc_left (v := fun _ => f r A K)
    (s := fun _ => Icc (-B) B) (K := C) (a := 0) (b := t1) (f := x) (g := fun _ => e)
    (fun _ _ => hC) (hx.cont.mono (Icc_subset_Icc_right ht1.2))
    (fun t ht => (hx.deriv t ⟨ht.1, ht.2.trans ht1.2⟩).hasDerivWithinAt)
    (fun t ht => hmem _ (by
      have := hB0 t ⟨ht.1.le, ht.2⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans ((le_max_left _ _).trans (le_max_left _ _))))
    continuousOn_const
    (fun t _ => by simpa [he] using (hasDerivWithinAt_const t (Iic t) e))
    (fun t _ => hmem _ ((le_max_right _ _).trans (le_max_left _ _)))
    hxe
  exact hsol ⟨le_rfl, ht1.1⟩

/-- (3) x(0) ∈ (a, b)（a, b は釣り合いの点）なら、[0, T] でずっと (a, b) にいる。 -/
theorem stays_between (hr : 0 < r) (hA : 0 < A) (hAK : A < K) {T : ℝ} (_hT : 0 ≤ T)
    {x : ℝ → ℝ} (hx : IsSol r A K T x) {a b : ℝ} (ha : f r A K a = 0) (hb : f r A K b = 0)
    (h0 : x 0 ∈ Ioo a b) : ∀ t ∈ Icc 0 T, x t ∈ Ioo a b := by
  intro t ht
  by_contra hn
  simp only [mem_Ioo, not_and_or, not_lt] at hn
  have hcont : ContinuousOn x (Icc 0 t) := hx.cont.mono (Icc_subset_Icc_right ht.2)
  rcases hn with h | h
  · obtain ⟨s, hs, hxs⟩ := intermediate_value_Icc' ht.1 hcont ⟨h, h0.1.le⟩
    have := no_hit hr hA hAK hx ha ⟨hs.1, hs.2.trans ht.2⟩ hxs
    linarith [h0.1]
  · obtain ⟨s, hs, hxs⟩ := intermediate_value_Icc ht.1 hcont ⟨h0.2.le, h⟩
    have := no_hit hr hA hAK hx hb ⟨hs.1, hs.2.trans ht.2⟩ hxs
    linarith [h0.2]

theorem stays_above (hr : 0 < r) (hA : 0 < A) (hAK : A < K) {T : ℝ} (_hT : 0 ≤ T)
    {x : ℝ → ℝ} (hx : IsSol r A K T x) (h0 : K < x 0) : ∀ t ∈ Icc 0 T, K < x t := by
  intro t ht
  by_contra hn
  push Not at hn
  have hcont : ContinuousOn x (Icc 0 t) := hx.cont.mono (Icc_subset_Icc_right ht.2)
  obtain ⟨s, hs, hxs⟩ := intermediate_value_Icc' ht.1 hcont ⟨hn, h0.le⟩
  have := no_hit hr hA hAK hx (f_K (by linarith)) ⟨hs.1, hs.2.trans ht.2⟩ hxs
  linarith

theorem interior_deriv {T : ℝ} {x : ℝ → ℝ} (hx : IsSol r A K T x) :
    ∀ t ∈ interior (Icc 0 T), HasDerivWithinAt x (f r A K (x t)) (interior (Icc 0 T)) t := by
  intro t ht
  rw [interior_Icc] at ht
  exact (hx.deriv t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt

/-- x(0) ∈ (0, A) なら、ずっと (0, A) にいて、狭義に減る（有限の時間で 0 にならない）。 -/
theorem stays_low (hr : 0 < r) (hA : 0 < A) (hAK : A < K) {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → ℝ} (hx : IsSol r A K T x) (h0 : x 0 ∈ Ioo 0 A) :
    (∀ t ∈ Icc 0 T, x t ∈ Ioo 0 A) ∧ StrictAntiOn x (Icc 0 T) := by
  have hin := stays_between hr hA hAK hT hx f_zero (f_A hA.ne') h0
  refine ⟨hin, ?_⟩
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 T) hx.cont (interior_deriv hx)
  intro t ht
  rw [interior_Icc] at ht
  have := hin t ⟨ht.1.le, ht.2.le⟩
  exact f_neg_low hr hA hAK this.1 this.2

/-- x(0) ∈ (A, K) なら、ずっと (A, K) にいて、狭義に増える。 -/
theorem stays_mid (hr : 0 < r) (hA : 0 < A) (hAK : A < K) {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → ℝ} (hx : IsSol r A K T x) (h0 : x 0 ∈ Ioo A K) :
    (∀ t ∈ Icc 0 T, x t ∈ Ioo A K) ∧ StrictMonoOn x (Icc 0 T) := by
  have hin := stays_between hr hA hAK hT hx (f_A hA.ne') (f_K (by linarith)) h0
  refine ⟨hin, ?_⟩
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 T) hx.cont (interior_deriv hx)
  intro t ht
  rw [interior_Icc] at ht
  have := hin t ⟨ht.1.le, ht.2.le⟩
  exact f_pos_mid hr hA this.1 this.2

/-- x(0) > K なら、ずっと K より上にいて、狭義に減る。 -/
theorem stays_high (hr : 0 < r) (hA : 0 < A) (hAK : A < K) {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → ℝ} (hx : IsSol r A K T x) (h0 : K < x 0) :
    (∀ t ∈ Icc 0 T, K < x t) ∧ StrictAntiOn x (Icc 0 T) := by
  have hin := stays_above hr hA hAK hT hx h0
  refine ⟨hin, ?_⟩
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 T) hx.cont (interior_deriv hx)
  intro t ht
  rw [interior_Icc] at ht
  exact f_neg_high hr hA hAK (hin t ⟨ht.1.le, ht.2.le⟩)

/-- (4) 「下がるほど速く減る」への反例：N = 10 での減る速さは N = 50 より小さい。 -/
theorem not_faster_lower : f 0.5 100 1000 10 = -4.455 ∧ f 0.5 100 1000 50 = -11.875 ∧
    |f 0.5 100 1000 10| < |f 0.5 100 1000 50| := by
  refine ⟨by norm_num [f], by norm_num [f], ?_⟩
  norm_num [f, abs_of_neg]

end Paper696

end Yamagishi
