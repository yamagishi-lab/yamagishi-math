/-
論文788『入る光と出る光は 4.245712 μm で分かれ、この分かれ目は変数の選び方に依らない』の格上げ
（一般の形）。

日本語の一文：温度の違う二つの黒体の分布を同じ規格の形 C a³/(T⁴(e^(a/T) − 1))（a = c₂/λ）で書くと、
どの二つの温度でもただ一点で交わり、熱いほうは交わる点より短い波長の側で大きく、交わる点と重なり
∫min は波長でも振動数でも同じで、温度比だけで決まる。
English: Writing two blackbody distributions in the common normalized form C a³/(T⁴(e^(a/T) − 1))
(a = c₂/λ), any two temperatures cross at exactly one point, the hotter one dominating on the
short-wavelength side; the crossing and the overlap ∫min are the same in wavelength and in
frequency, and depend only on the temperature ratio.

原稿（788_yamagishi_incoming_and_outgoing_light_part_at_one_wavelength/…_jp.tex）は、太陽 5772 K と
地球 288 K の一組で、交わる波長 4.245712 μm と重なり 1.081347e−2 を二通りで出し、変数による不変を
数値で確かめている。ただ一点で交わることと温度比だけで決まることの証明は無い。

ここで証明した言明（T₁ > T₂ > 0、C > 0。a = c₂/λ の変数での分布を q_T(a) と書く）：
  (1) `q_ratio`：q_{T₁}/q_{T₂} = (T₂/T₁)⁴·F_k(a/T₁)、F_k(s) = (e^(ks) − 1)/(e^s − 1)、k = T₁/T₂。
      `F_strictMono`：k > 1 で F_k は (0, ∞) で狭義に増える（芯は (1 − e^(−y))/y が狭義に減ること、
      `psi_strictAnti`）。
  (2) `crossing_exists_unique`：q_{T₁}(a) = q_{T₂}(a) となる a > 0 はちょうど一つ。
      `crossing_sign`：その点 a* より小さい a（長い波長）では q_{T₁} < q_{T₂}、大きい a では
      q_{T₁} > q_{T₂}（符号の変わりは一回）。
      `crossing_ratio_only`：交わる点の a*/T₂ は温度比 T₁/T₂ だけで決まる。
  (3) `wavelength_cross_iff`：波長あたりの分布 p_T(λ) = q_T(c₂/λ)·c₂/λ² でも、交わる点は同じ
      （p_{T₁}(λ) = p_{T₂}(λ) ⇔ q_{T₁}(c₂/λ) = q_{T₂}(c₂/λ)）。
      `overlap_wavelength`：重なり ∫min(p_{T₁}, p_{T₂}) dλ は ∫min(q_{T₁}, q_{T₂}) da に等しい。
      `overlap_ratio_only`：重なりは温度比だけで決まる（∫min(q_{T₁}, q_{T₂}) = ∫min(q_{T₁/T₂}, q_1)）。
足した仮定：理想の黒体の分布の形を定義に置いた。規格の定数 C は二つの温度で共通の正の数ならよく
（C = 15/π⁴ で全体が 1 になるが、その積分の値は形式化していない）、交わる点が在ることの証明は
規格の積分を使わず、両端での比の大きさだけから出した。
形式化していないもの：原稿の数（4.245712 μm・1.081347e−2・山の位置）、重なりが温度比について
減ること（下読みの AI も数値で見ただけ）、温度比が 1 に近いときの交わる点の極限 3.92069、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper788

open Real Set MeasureTheory

/-- a = c₂/λ の変数での黒体の分布 q_T(a) = C a³/(T⁴(e^(a/T) − 1))。 -/
noncomputable def q (C T a : ℝ) : ℝ := C * a ^ 3 / (T ^ 4 * (exp (a / T) - 1))

/-- F_k(s) = (e^(ks) − 1)/(e^s − 1)。 -/
noncomputable def F (k s : ℝ) : ℝ := (exp (k * s) - 1) / (exp s - 1)

theorem exp_sub_one_pos {x : ℝ} (hx : 0 < x) : 0 < exp x - 1 := by
  have := add_one_lt_exp (ne_of_gt hx); linarith

theorem q_pos {C T a : ℝ} (hC : 0 < C) (hT : 0 < T) (ha : 0 < a) : 0 < q C T a := by
  unfold q
  have := exp_sub_one_pos (div_pos ha hT)
  exact div_pos (by positivity) (mul_pos (by positivity) this)

/-- (1) 比の形。 -/
theorem q_ratio {C T1 T2 a : ℝ} (hC : 0 < C) (hT1 : 0 < T1) (hT2 : 0 < T2) (ha : 0 < a) :
    q C T1 a / q C T2 a = (T2 / T1) ^ 4 * F (T1 / T2) (a / T1) := by
  unfold q F
  have h1 := exp_sub_one_pos (div_pos ha hT1)
  have h2 := exp_sub_one_pos (div_pos ha hT2)
  have e : T1 / T2 * (a / T1) = a / T2 := by field_simp
  rw [e]
  field_simp

/-- (1 + y)e^(−y) < 1（y > 0）。 -/
theorem one_add_mul_exp_lt {y : ℝ} (hy : 0 < y) : (1 + y) * exp (-y) < 1 := by
  have h := add_one_lt_exp (x := y) (ne_of_gt hy)
  have he : exp y * exp (-y) = 1 := by rw [← exp_add]; simp
  have := exp_pos (-y)
  nlinarith

/-- 芯：ψ(y) = (1 − e^(−y))/y は (0, ∞) で狭義に減る。 -/
theorem psi_strictAnti : StrictAntiOn (fun y => (1 - exp (-y)) / y) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro y hy
    exact ((continuous_const.sub continuous_neg.rexp).continuousAt.div continuousAt_id
      (ne_of_gt hy)).continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    have hd : HasDerivAt (fun y => (1 - exp (-y)) / y)
        (((0 - exp (-y) * (-1)) * y - (1 - exp (-y)) * 1) / y ^ 2) y :=
      ((hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_neg y).exp)).div (hasDerivAt_id' y)
        (ne_of_gt hy)
    rw [hd.deriv]
    have hy' : 0 < y := hy
    apply div_neg_of_neg_of_pos _ (by positivity)
    have := one_add_mul_exp_lt hy'
    nlinarith

/-- (1) k > 1 で F_k は (0, ∞) で狭義に増える。 -/
theorem F_strictMono {k : ℝ} (hk : 1 < k) : StrictMonoOn (F k) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro s hs
    exact ((((continuous_const.mul continuous_id).rexp.sub continuous_const).continuousAt).div
      ((continuous_exp.sub continuous_const).continuousAt)
      (ne_of_gt (exp_sub_one_pos hs))).continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    have hs' : 0 < s := hs
    have h1 := exp_sub_one_pos hs
    have hd : HasDerivAt (F k)
        (((exp (k * s) * (k * 1)) * (exp s - 1) - (exp (k * s) - 1) * exp s) / (exp s - 1) ^ 2) s :=
      ((((hasDerivAt_id' s).const_mul k).exp).sub_const 1).div ((hasDerivAt_exp s).sub_const 1)
        (ne_of_gt h1)
    rw [hd.deriv]
    apply div_pos _ (by positivity)
    -- ψ(ks) < ψ(s)
    have hks : 0 < k * s := by nlinarith
    have hlt : k * s ∈ Ioi (0 : ℝ) := hks
    have hψ := psi_strictAnti (mem_Ioi.mpr hs) hlt (by nlinarith)
    simp only at hψ
    rw [div_lt_div_iff₀ hks hs] at hψ
    -- (1 − e^(−ks))·s < (1 − e^(−s))·(ks) ⇒ 1 − e^(−ks) < k(1 − e^(−s))
    have hA : 1 - exp (-(k * s)) < k * (1 - exp (-s)) := by nlinarith
    have e1 : exp (k * s) * exp (-(k * s)) = 1 := by rw [← exp_add]; simp
    have e2 : exp s * exp (-s) = 1 := by rw [← exp_add]; simp
    have hpos : 0 < exp (k * s) * exp s := by positivity
    have := mul_lt_mul_of_pos_left hA hpos
    have l1 : exp (k * s) * exp s * (1 - exp (-(k * s))) = exp (k * s) * exp s - exp s := by
      linear_combination (-(exp s)) * e1
    have l2 : exp (k * s) * exp s * (k * (1 - exp (-s))) =
        k * exp (k * s) * exp s - k * exp (k * s) := by
      linear_combination (-(k * exp (k * s))) * e2
    rw [l1, l2] at this
    nlinarith

theorem F_continuousOn (k : ℝ) : ContinuousOn (F k) (Ioi 0) := by
  intro s hs
  exact ((((continuous_const.mul continuous_id).rexp.sub continuous_const).continuousAt).div
    ((continuous_exp.sub continuous_const).continuousAt)
    (ne_of_gt (exp_sub_one_pos hs))).continuousWithinAt

/-- 小さい側の点：s₀ = ln k/k で F_k(s₀) < k⁴。 -/
theorem F_low {k : ℝ} (hk : 1 < k) : F k (log k / k) < k ^ 4 := by
  have hk0 : 0 < k := by linarith
  have hl : 0 < log k := log_pos hk
  have hs0 : 0 < log k / k := div_pos hl hk0
  unfold F
  have e : exp (k * (log k / k)) = k := by
    rw [show k * (log k / k) = log k by field_simp, exp_log hk0]
  rw [e]
  have hden := exp_sub_one_pos hs0
  have hge : log k / k ≤ exp (log k / k) - 1 := by linarith [add_one_le_exp (log k / k)]
  have hlog : 1 - k⁻¹ ≤ log k := one_sub_inv_le_log_of_pos hk0
  rw [div_lt_iff₀ hden]
  -- k − 1 ≤ k·log k ≤ k²·(e^(s₀) − 1) < k⁴(e^(s₀) − 1)
  have h1 : k - 1 ≤ k * log k := by
    have : k * (1 - k⁻¹) = k - 1 := by field_simp
    nlinarith
  have h2 : k * log k = k ^ 2 * (log k / k) := by field_simp
  have h3 : k ^ 2 * (log k / k) ≤ k ^ 2 * (exp (log k / k) - 1) :=
    mul_le_mul_of_nonneg_left hge (by positivity)
  have h4 : k ^ 2 * (exp (log k / k) - 1) < k ^ 4 * (exp (log k / k) - 1) := by
    apply mul_lt_mul_of_pos_right _ hden
    have : 1 < k ^ 2 := by nlinarith
    nlinarith
  linarith

/-- 大きい側の点：s₁ = ln(k⁴ + 1)/(k − 1) で F_k(s₁) > k⁴。 -/
theorem F_high {k : ℝ} (hk : 1 < k) : k ^ 4 < F k (log (k ^ 4 + 1) / (k - 1)) := by
  set s := log (k ^ 4 + 1) / (k - 1) with hs
  have hk1 : 0 < k - 1 := by linarith
  have hl : 0 < log (k ^ 4 + 1) := log_pos (by nlinarith [pow_pos (by linarith : (0:ℝ) < k) 4])
  have hs0 : 0 < s := div_pos hl hk1
  have e : exp ((k - 1) * s) = k ^ 4 + 1 := by
    rw [hs, show (k - 1) * (log (k ^ 4 + 1) / (k - 1)) = log (k ^ 4 + 1) by field_simp,
      exp_log (by positivity)]
  have hden := exp_sub_one_pos hs0
  unfold F
  rw [lt_div_iff₀ hden]
  have hsplit : exp (k * s) = exp ((k - 1) * s) * exp s := by rw [← exp_add]; ring_nf
  rw [hsplit, e]
  have : 1 < exp s := by have := add_one_lt_exp (ne_of_gt hs0); linarith
  have e2 : (k ^ 4 + 1) * exp s - 1 - k ^ 4 * (exp s - 1) = exp s - 1 + k ^ 4 := by ring
  have : 0 < k ^ 4 := by positivity
  linarith

/-- (2) 交わる点はちょうど一つ。 -/
theorem crossing_exists_unique {C T1 T2 : ℝ} (hC : 0 < C) (hT2 : 0 < T2) (hT : T2 < T1) :
    ∃! a, 0 < a ∧ q C T1 a = q C T2 a := by
  have hT1 : 0 < T1 := hT2.trans hT
  set k := T1 / T2 with hk
  have hk1 : 1 < k := by rw [hk, one_lt_div hT2]; exact hT
  have hk0 : 0 < k := by linarith
  -- q₁ = q₂ ⇔ F_k(a/T₁) = k⁴
  have hiff : ∀ a, 0 < a → (q C T1 a = q C T2 a ↔ F k (a / T1) = k ^ 4) := by
    intro a ha
    have hq2 := q_pos hC hT2 ha
    rw [← div_eq_one_iff_eq (ne_of_gt hq2), q_ratio hC hT1 hT2 ha]
    have e : (T2 / T1) ^ 4 = (k ^ 4)⁻¹ := by rw [hk, ← inv_pow, inv_div]
    rw [e, inv_mul_eq_one₀ (by positivity)]
    exact eq_comm
  set s0 := log k / k
  set s1 := log (k ^ 4 + 1) / (k - 1)
  have hs0 : 0 < s0 := div_pos (log_pos hk1) hk0
  have hlow := F_low hk1
  have hhigh := F_high hk1
  have hs1 : 0 < s1 := div_pos (log_pos (by nlinarith [pow_pos hk0 4])) (by linarith)
  have hs01 : s0 < s1 := by
    by_contra hc; push Not at hc
    have := (F_strictMono hk1).monotoneOn (mem_Ioi.mpr hs1) (mem_Ioi.mpr hs0) hc
    linarith
  obtain ⟨s, hsI, hsv⟩ := intermediate_value_Icc hs01.le
    ((F_continuousOn k).mono (fun x hx => mem_Ioi.mpr (lt_of_lt_of_le hs0 hx.1)))
    (show k ^ 4 ∈ Icc (F k s0) (F k s1) from ⟨hlow.le, hhigh.le⟩)
  have hspos : 0 < s := lt_of_lt_of_le hs0 hsI.1
  refine ⟨T1 * s, ⟨by positivity, ?_⟩, ?_⟩
  · rw [hiff _ (by positivity), show T1 * s / T1 = s by field_simp]; exact hsv
  · rintro b ⟨hb, hbq⟩
    rw [hiff b hb] at hbq
    have := (F_strictMono hk1).injOn (mem_Ioi.mpr (div_pos hb hT1)) (mem_Ioi.mpr hspos)
      (hbq.trans hsv.symm)
    rw [← this]; field_simp

/-- (2) 符号の変わりは一回：交わる点 a* の手前では q₁ < q₂、先では q₁ > q₂。 -/
theorem crossing_sign {C T1 T2 a0 : ℝ} (hC : 0 < C) (hT2 : 0 < T2) (hT : T2 < T1)
    (ha0 : 0 < a0) (h0 : q C T1 a0 = q C T2 a0) {a : ℝ} (ha : 0 < a) :
    (a < a0 → q C T1 a < q C T2 a) ∧ (a0 < a → q C T2 a < q C T1 a) := by
  have hT1 : 0 < T1 := hT2.trans hT
  have hk1 : 1 < T1 / T2 := by rw [one_lt_div hT2]; exact hT
  have hq2 := q_pos hC hT2 ha
  have hq20 := q_pos hC hT2 ha0
  have hr0 : q C T1 a0 / q C T2 a0 = 1 := by rw [h0, div_self (ne_of_gt hq20)]
  rw [q_ratio hC hT1 hT2 ha0] at hr0
  have hK : 0 < (T2 / T1) ^ 4 := by positivity
  constructor
  · intro hlt
    have hm := (F_strictMono hk1) (mem_Ioi.mpr (div_pos ha hT1)) (mem_Ioi.mpr (div_pos ha0 hT1))
      (div_lt_div_of_pos_right hlt hT1)
    have : q C T1 a / q C T2 a < 1 := by
      rw [q_ratio hC hT1 hT2 ha, ← hr0]
      exact mul_lt_mul_of_pos_left hm hK
    rwa [div_lt_one hq2] at this
  · intro hlt
    have hm := (F_strictMono hk1) (mem_Ioi.mpr (div_pos ha0 hT1)) (mem_Ioi.mpr (div_pos ha hT1))
      (div_lt_div_of_pos_right hlt hT1)
    have : 1 < q C T1 a / q C T2 a := by
      rw [q_ratio hC hT1 hT2 ha, ← hr0]
      exact mul_lt_mul_of_pos_left hm hK
    rwa [one_lt_div hq2] at this

/-- 尺度の性質：T₂·q_T(T₂x) = q_{T/T₂}(x)。 -/
theorem q_scale {C T T2 x : ℝ} (hT2 : 0 < T2) (hT : 0 < T) :
    T2 * q C T (T2 * x) = q C (T / T2) x := by
  unfold q
  rw [show T2 * x / T = x / (T / T2) by field_simp]
  field_simp

/-- (2) 交わる点 a*/T₂ は温度比だけで決まる：q_{T₁}(T₂x) = q_{T₂}(T₂x) ⇔ q_{T₁/T₂}(x) = q_1(x)。 -/
theorem crossing_ratio_only {C T1 T2 x : ℝ} (hT1 : 0 < T1) (hT2 : 0 < T2) :
    q C T1 (T2 * x) = q C T2 (T2 * x) ↔ q C (T1 / T2) x = q C 1 x := by
  rw [← q_scale hT2 hT1, show q C 1 x = T2 * q C T2 (T2 * x) by
    rw [q_scale hT2 hT2, div_self (ne_of_gt hT2)]]
  constructor
  · intro h; rw [h]
  · intro h; exact mul_left_cancel₀ (ne_of_gt hT2) h

/-- 波長あたりの分布 p_T(λ) = q_T(c₂/λ)·c₂/λ²。 -/
noncomputable def p (C c2 T l : ℝ) : ℝ := q C T (c2 / l) * (c2 / l ^ 2)

/-- (3) 波長でも交わる点は同じ。 -/
theorem wavelength_cross_iff {C c2 T1 T2 l : ℝ} (hc2 : 0 < c2) (hl : 0 < l) :
    p C c2 T1 l = p C c2 T2 l ↔ q C T1 (c2 / l) = q C T2 (c2 / l) := by
  unfold p
  have : 0 < c2 / l ^ 2 := by positivity
  constructor
  · intro h; exact mul_right_cancel₀ (ne_of_gt this) h
  · intro h; rw [h]

/-- (3) 重なりは波長でも同じ：∫min(p₁, p₂) dλ = ∫min(q₁, q₂) da（どちらも (0, ∞) の上）。 -/
theorem overlap_wavelength {C c2 T1 T2 : ℝ} (hc2 : 0 < c2) :
    ∫ l in Ioi 0, min (p C c2 T1 l) (p C c2 T2 l) =
      ∫ a in Ioi 0, min (q C T1 a) (q C T2 a) := by
  have himg : (fun l => c2 / l) '' Ioi 0 = Ioi 0 := by
    ext a
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact div_pos hc2 hl
    · intro ha; exact ⟨c2 / a, div_pos hc2 ha, by field_simp⟩
  have hd : ∀ l ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun l => c2 / l) (-(c2 / l ^ 2)) (Ioi 0) l := by
    intro l hl
    have := (hasDerivAt_const l c2).div (hasDerivAt_id' l) (ne_of_gt (mem_Ioi.mp hl))
    refine (this.congr_deriv ?_).hasDerivWithinAt
    ring
  have hinj : InjOn (fun l => c2 / l) (Ioi 0) := by
    intro x hx y hy hxy
    simp only at hxy
    have hx0 : 0 < x := hx
    have hy0 : 0 < y := hy
    field_simp at hxy
    nlinarith
  conv_rhs => rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro l hl
  have hl0 : 0 < l := hl
  simp only [smul_eq_mul]
  have hJ : 0 < c2 / l ^ 2 := by positivity
  rw [abs_neg, abs_of_pos hJ]
  unfold p
  rw [← min_mul_of_nonneg _ _ hJ.le, mul_comm]

/-- (3) 重なりは温度比だけで決まる：∫min(q_{T₁}, q_{T₂}) = ∫min(q_{T₁/T₂}, q_1)。 -/
theorem overlap_ratio_only {C T1 T2 : ℝ} (hT1 : 0 < T1) (hT2 : 0 < T2) :
    ∫ a in Ioi 0, min (q C T1 a) (q C T2 a) =
      ∫ x in Ioi 0, min (q C (T1 / T2) x) (q C 1 x) := by
  have himg : (fun x => T2 * x) '' Ioi 0 = Ioi 0 := by
    ext a
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact mul_pos hT2 hx
    · intro ha; exact ⟨a / T2, div_pos ha hT2, by field_simp⟩
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x => T2 * x) T2 (Ioi 0) x := by
    intro x _
    have := (hasDerivAt_id' x).const_mul T2
    simpa using this.hasDerivWithinAt
  have hinj : InjOn (fun x => T2 * x) (Ioi 0) := by
    intro x _ y _ hxy
    exact mul_left_cancel₀ (ne_of_gt hT2) hxy
  conv_lhs => rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  simp only [smul_eq_mul]
  rw [abs_of_pos hT2, mul_min_of_nonneg _ _ hT2.le, q_scale hT2 hT1, q_scale hT2 hT2,
    div_self (ne_of_gt hT2)]

end Paper788

end Yamagishi
