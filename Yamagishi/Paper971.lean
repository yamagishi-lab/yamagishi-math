/-
論文971『二つの箱の最小の組は、二次の反応で小さい箱を先に置く』の格上げ（一般の形）。

原稿（971_yamagishi_smallest_pair_of_tanks_puts_smaller_first_for_second_order/…_jp.tex）は、入口の
濃さ 1・反応の速さ c^n の反応を二つの完全混合槽の直列で出口 r にするとき、合計の滞在時間を最小に
する分け方を、n = 0.5・1・2 と r = 0.1・0.01 の六つの組で数値の最適化で求め、n = 2 では一つ目が
小さく、n = 0.5 では大きく、n = 1 では同じだった、と数えている（観察 2.2・4.1）。

ここで証明した言明（すべての n > 0、0 < r < 1）：中間の濃さを t（r < t < 1）とすると、
一つ目の滞在時間 τ₁(t) = (1 − t)t^(−n)、二つ目 τ₂(t) = (t − r)r^(−n)、合計 f(t) = τ₁ + τ₂。
  (1) `exists_unique_stationary`：f′(t) = 0 となる t は (r, 1) にただ一つ在る。
  (2) `isMin_at_stationary`：その t で f は [r, 1] の上の最小をとり、ほかの点では真に大きい
      （最小はただ一つ）。
  (3) `order_at_stationary`：その t で、n > 1 なら τ₁ < τ₂（小さい箱が先）、n = 1 なら τ₁ = τ₂、
      0 < n < 1 なら τ₁ > τ₂（大きい箱が先）。
定義に置いたもの：完全混合槽の釣り合い τ = (c_in − c_out)/c_out^n（原稿の設定の式）と、
停留の条件 f′(t) = r^(−n) − t^(−n) − n(1 − t)t^(−n−1) = 0（`deriv_f` でこれが f の微分であることも
示した）。n = 0（合計が分け方によらない）と n < 0 は扱わない。
証明の筋：f′(t) = r^(−n) − g(t)、g(t) = t^(−n) + n(1 − t)t^(−n−1) は (0, 1) で狭義に減る
（g′(t) = −2n t^(−n−1) − n(n+1)(1 − t)t^(−n−2) < 0）。f′(r) < 0 < f′(1) から零点はただ一つ。
順の比較は、z = 1 + n(1 − t)/t・w = 1/z と置くと、τ₂ − τ₁ の符号が 1 − w^(1/n) − (1 − w)/n の符号
になり、実数の冪のベルヌーイの不等式（Mathlib の `rpow_one_add_lt_one_add_mul_self` と
`one_add_mul_self_lt_rpow_one_add`）で、1/n が 1 より小さいか大きいかで決まる。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper971

open Real Set

/-- 一つ目の箱の滞在時間（入口 1 → 中間 t）。 -/
noncomputable def tau1 (n t : ℝ) : ℝ := (1 - t) * t ^ (-n)

/-- 二つ目の箱の滞在時間（中間 t → 出口 r）。 -/
noncomputable def tau2 (n r t : ℝ) : ℝ := (t - r) * r ^ (-n)

/-- 合計の滞在時間。 -/
noncomputable def f (n r t : ℝ) : ℝ := tau1 n t + tau2 n r t

/-- 停留の条件に出る関数 g(t) = t^(−n) + n(1 − t)t^(−n−1)。f′ = r^(−n) − g。 -/
noncomputable def g (n t : ℝ) : ℝ := t ^ (-n) + n * (1 - t) * t ^ (-n - 1)

theorem hasDerivAt_f (n r : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (f n r) (r ^ (-n) - g n t) t := by
  have h1 := (Real.hasDerivAt_rpow_const (p := -n) (Or.inl ht.ne'))
  have h2 : HasDerivAt (fun t => (1 - t) * t ^ (-n))
      ((-1) * t ^ (-n) + (1 - t) * (-n * t ^ (-n - 1))) t :=
    ((hasDerivAt_id t).const_sub 1).mul h1 |>.congr_deriv (by simp)
  have h3 : HasDerivAt (fun t => (t - r) * r ^ (-n)) (1 * r ^ (-n)) t :=
    ((hasDerivAt_id t).sub_const r).mul_const _
  have := h2.add h3
  unfold f tau1 tau2 g
  convert this using 1
  ring

theorem deriv_f (n r : ℝ) {t : ℝ} (ht : 0 < t) : deriv (f n r) t = r ^ (-n) - g n t :=
  (hasDerivAt_f n r ht).deriv

theorem hasDerivAt_g (n : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (g n) (-2 * n * t ^ (-n - 1) - n * (n + 1) * (1 - t) * t ^ (-n - 2)) t := by
  have h1 := Real.hasDerivAt_rpow_const (p := -n) (Or.inl ht.ne')
  have h2 := Real.hasDerivAt_rpow_const (p := -n - 1) (Or.inl ht.ne')
  have h3 : HasDerivAt (fun t => n * (1 - t) * t ^ (-n - 1))
      (n * (-1) * t ^ (-n - 1) + n * (1 - t) * ((-n - 1) * t ^ (-n - 1 - 1))) t := by
    have := (((hasDerivAt_id t).const_sub 1).const_mul n).mul h2
    convert this using 1
    · funext x; simp [Pi.mul_apply]
    · simp
  have := h1.add h3
  unfold g
  convert this using 1
  rw [show -n - 1 - 1 = -n - 2 by ring]
  ring

/-- g は (0, 1) で狭義に減る。 -/
theorem g_strictAntiOn {n : ℝ} (hn : 0 < n) : StrictAntiOn (g n) (Ioo 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro t ht
    exact (hasDerivAt_g n ht.1).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(hasDerivAt_g n ht.1).deriv]
    have a := Real.rpow_pos_of_pos ht.1 (-n - 1)
    have b := Real.rpow_pos_of_pos ht.1 (-n - 2)
    have c : 0 < 1 - t := by linarith [ht.2]
    have : 0 < n * (n + 1) * (1 - t) * t ^ (-n - 2) := by positivity
    nlinarith

theorem g_at (n t : ℝ) (ht : 0 < t) : g n t = t ^ (-n) * (1 + n * ((1 - t) / t)) := by
  unfold g
  rw [Real.rpow_sub_one ht.ne']
  field_simp

/-- (1) 停留点は (r, 1) にただ一つ在る。 -/
theorem exists_unique_stationary {n r : ℝ} (hn : 0 < n) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃! t, t ∈ Ioo r 1 ∧ g n t = r ^ (-n) := by
  have hcont : ContinuousOn (g n) (Icc r 1) := fun t ht =>
    (hasDerivAt_g n (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hgr : r ^ (-n) < g n r := by
    unfold g
    have : 0 < n * (1 - r) * r ^ (-n - 1) := by
      have := Real.rpow_pos_of_pos hr0 (-n - 1); have : 0 < 1 - r := by linarith
      positivity
    linarith
  have hg1 : g n 1 < r ^ (-n) := by
    unfold g
    simp only [Real.one_rpow, sub_self, mul_zero, zero_mul, add_zero]
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hr0 hr1 (by linarith)
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' hr1.le hcont ⟨hg1.le, hgr.le⟩
  have ht' : t ∈ Ioo r 1 := by
    refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
    · rintro rfl; linarith
    · rintro rfl; linarith
  refine ⟨t, ⟨ht', hgt⟩, ?_⟩
  rintro t' ⟨ht'', hgt'⟩
  by_contra hne
  have hA := g_strictAntiOn hn
  have m1 : t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht'.1], ht'.2⟩
  have m2 : t' ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht''.1], ht''.2⟩
  rcases lt_or_gt_of_ne hne with h | h
  · have := hA m2 m1 h; linarith
  · have := hA m1 m2 h; linarith

/-- (2) 停留点で f は [r, 1] の上のただ一つの最小をとる。 -/
theorem isMin_at_stationary {n r t : ℝ} (hn : 0 < n) (hr0 : 0 < r) (ht : t ∈ Ioo r 1)
    (hst : g n t = r ^ (-n)) : ∀ s ∈ Icc r 1, s ≠ t → f n r t < f n r s := by
  have hcont : ∀ a b, 0 < a → ContinuousOn (f n r) (Icc a b) := fun a b ha s hs =>
    (hasDerivAt_f n r (by linarith [hs.1])).continuousAt.continuousWithinAt
  have hA := g_strictAntiOn hn
  intro s hs hne
  rcases lt_or_gt_of_ne hne with h | h
  · -- s < t：[s, t] で f′ < 0
    have : StrictAntiOn (f n r) (Icc s t) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc s t) (hcont s t (by linarith [hs.1]))
      intro x hx
      rw [interior_Icc] at hx
      rw [deriv_f n r (by linarith [hx.1, hs.1])]
      have := hA ⟨by linarith [hx.1, hs.1], by linarith [hx.2, ht.2]⟩ ⟨by linarith [ht.1], ht.2⟩
        hx.2
      linarith
    exact this ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h
  · -- t < s：[t, s] で f′ > 0
    have : StrictMonoOn (f n r) (Icc t s) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc t s) (hcont t s (by linarith [ht.1]))
      intro x hx
      rw [interior_Icc] at hx
      rw [deriv_f n r (by linarith [hx.1, ht.1])]
      have := hA ⟨by linarith [ht.1], ht.2⟩ ⟨by linarith [hx.1, ht.1], by linarith [hx.2, hs.2]⟩
        hx.1
      linarith
    exact this ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h

/-- (3) 停留点での順：n > 1 なら τ₁ < τ₂、n = 1 なら等しい、n < 1 なら τ₁ > τ₂。 -/
theorem order_at_stationary {n r t : ℝ} (hn : 0 < n) (hr0 : 0 < r) (ht : t ∈ Ioo r 1)
    (hst : g n t = r ^ (-n)) :
    (1 < n → tau1 n t < tau2 n r t) ∧ (n = 1 → tau1 n t = tau2 n r t) ∧
    (n < 1 → tau2 n r t < tau1 n t) := by
  have ht0 : 0 < t := by linarith [ht.1]
  set u := (1 - t) / t with hu
  have hu0 : 0 < u := div_pos (by linarith [ht.2]) ht0
  set z := 1 + n * u with hz
  have hz1 : 1 < z := by have := mul_pos hn hu0; linarith
  have hz0 : 0 < z := by linarith
  -- r^(−n) = t^(−n)·z
  have hrz : r ^ (-n) = t ^ (-n) * z := by rw [← hst, g_at n t ht0]
  -- r = t·z^(−1/n)
  have hr : r = t * z ^ (-(1 / n)) := by
    have e1 : r = (r ^ (-n)) ^ (-(1 / n)) := by
      rw [← Real.rpow_mul hr0.le]; field_simp; simp
    rw [e1, hrz, Real.mul_rpow (Real.rpow_nonneg ht0.le _) hz0.le, ← Real.rpow_mul ht0.le]
    field_simp; simp
  set w := z⁻¹ with hw
  have hw0 : 0 < w := inv_pos.mpr hz0
  have hw1 : w < 1 := inv_lt_one_of_one_lt₀ hz1
  set p := 1 / n with hp
  have hzp : z ^ (-p) = w ^ p := by
    rw [hw, Real.inv_rpow hz0.le, Real.rpow_neg hz0.le]
  -- τ₂ − τ₁ = t·t^(−n)·z·((1 − w^p) − p(1 − w))·n ... を符号で比べる
  have htn : 0 < t ^ (-n) := Real.rpow_pos_of_pos ht0 _
  have hdiff : tau2 n r t - tau1 n t = t * t ^ (-n) * z * ((1 - w ^ p) - p * (1 - w)) := by
    unfold tau1 tau2
    rw [hrz, hr, hzp]
    have hzw : z * w = 1 := by rw [hw]; field_simp
    have : 1 - t = t * u := by rw [hu]; field_simp
    rw [this]
    have hun : u = (z - 1) / n := by rw [hz]; field_simp; ring
    rw [hun, hp]
    field_simp
    have : w = 1 / z := by rw [hw]; simp
    rw [this]
    field_simp
  have hpos : 0 < t * t ^ (-n) * z := by positivity
  -- ベルヌーイ：s = w − 1 ∈ (−1, 0)
  have hs1 : -1 ≤ w - 1 := by linarith
  have hs0 : w - 1 ≠ 0 := by linarith
  have hw' : 1 + (w - 1) = w := by ring
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · -- n > 1：0 < p < 1 で w^p < 1 + p(w − 1)
    have hp0 : 0 < p := by rw [hp]; positivity
    have hp1 : p < 1 := by rw [hp, div_lt_one hn]; exact h1
    have := rpow_one_add_lt_one_add_mul_self hs1 hs0 hp0 hp1
    rw [hw'] at this
    have : 0 < (1 - w ^ p) - p * (1 - w) := by linarith
    have := mul_pos hpos this
    linarith
  · subst h1
    have : p = 1 := by rw [hp]; norm_num
    rw [this, Real.rpow_one] at hdiff
    linarith [show (1 - w) - 1 * (1 - w) = 0 by ring, hdiff]
  · -- n < 1：p > 1 で w^p > 1 + p(w − 1)
    have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hn]; linarith
    have := one_add_mul_self_lt_rpow_one_add hs1 hs0 hp1
    rw [hw'] at this
    have : (1 - w ^ p) - p * (1 - w) < 0 := by linarith
    have := mul_neg_of_pos_of_neg hpos this
    linarith

end Paper971

end Yamagishi
