/-
論文581『森が炭素を吸う速さの頂点と、ためる量の頂点は、別の林齢にある』の格上げ（一般の形）。

原稿（581_yamagishi_fastest_uptake_is_not_largest_stock/…_jp.tex）は、
チャップマン＝リチャーズ曲線 V(t) = V_max(1 − e^(−kt))^c を V_max = 500、k = 0.04、c = 3 の一組で
数え、連年成長の頂点 ln 3/k = 27.465307 年、平均成長の頂点 47.595342 年（V′t = V を数値で解く）
を出している。頂点の順と間隔は、この一組の数だけ。

ここで証明した言明（c > 1, k > 0, V_max > 0）：
  (1) `rate_peak`：連年成長 V′(t) は t₁ = ln c/k で最大（すべての t > 0 で V′(t) ≤ V′(t₁)）。
  (2) `mean_stationary_iff`：t > 0 で V′(t)·t = V(t)（連年成長 = 平均成長）⇔ e^(kt) = 1 + c·kt。
  (3) `root_exists_unique`：e^x = 1 + cx の正の根 x_c はちょうど一つ。
      `root_bounds`：その根は ln c < x_c < 2 ln c（不等式 ln c > 1 − 1/c と c − 1/c > 2 ln c から）。
  (4) `mean_peak`：平均成長 V(t)/t は t₂ = x_c/k でただ一つの最大をとる（t ≠ t₂ なら V(t)/t < V(t₂)/t₂）。
  (5) `peaks_order`：t₁ < t₂ < 2t₁。比 t₂/t₁ = x_c/ln c は k によらない（`ratio_indep_k`）。
足した仮定：c > 1（c ≤ 1 では連年成長の頂点が t > 0 に無い）。
形式化していないもの：t₂ のランベルトの W 関数による形、比 x_c/ln c が c について減ること
（確かめの係も数値で見ただけ）、伐って植え替える一回りの平均の蓄積、二酸化炭素への換算、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper581

open Real Set

/-! ### 変数 x = kt での芯：h(x) = e^x − 1 − cx -/

/-- 平均成長の頂点の条件 e^x = 1 + cx を、h(x) = 0 と書く。 -/
noncomputable def h (c x : ℝ) : ℝ := exp x - 1 - c * x

theorem h_log_neg {c : ℝ} (hc : 1 < c) : h c (log c) < 0 := by
  unfold h
  have hl : 0 < log c := log_pos hc
  have h1 := add_one_lt_exp (x := -log c) (by linarith)
  rw [exp_neg, exp_log (by linarith)] at h1
  rw [exp_log (by linarith)]
  have hc0 : 0 < c := by linarith
  -- 1 − ln c < 1/c ⇒ c − c ln c < 1
  have : c * (-log c + 1) < c * c⁻¹ := mul_lt_mul_of_pos_left h1 hc0
  rw [mul_inv_cancel₀ (ne_of_gt hc0)] at this
  linarith

theorem h_two_log_pos {c : ℝ} (hc : 1 < c) : 0 < h c (2 * log c) := by
  unfold h
  have hl : 0 < log c := log_pos hc
  have hs := (self_lt_sinh_iff (x := log c)).mpr hl
  rw [sinh_eq, exp_neg, exp_log (by linarith)] at hs
  have hc0 : 0 < c := by linarith
  have he : exp (2 * log c) = c ^ 2 := by
    rw [show 2 * log c = log c + log c by ring, exp_add, exp_log hc0]; ring
  rw [he]
  have : 2 * log c * c < (c - c⁻¹) * c := by
    have := mul_lt_mul_of_pos_right hs hc0; linarith
  rw [sub_mul, inv_mul_cancel₀ (ne_of_gt hc0)] at this
  nlinarith

/-- 根 r の手前（0 < x < r）では h < 0（exp の狭義の凸性）。 -/
theorem h_neg_between {c r x : ℝ} (hx : 0 < x) (hxr : x < r) (hr : h c r = 0) : h c x < 0 := by
  unfold h at *
  have hr0 : 0 < r := hx.trans hxr
  set b := x / r
  have hb : 0 < b := div_pos hx hr0
  have hb1 : b < 1 := (div_lt_one hr0).mpr hxr
  have key := strictConvexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ r) (ne_of_lt hr0)
    (show (0 : ℝ) < 1 - b by linarith) hb (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at key
  have hbr : b * r = x := by simp only [b]; field_simp
  rw [hbr] at key
  have : exp r = 1 + c * r := by linarith
  rw [this] at key
  have e : b * (1 + c * r) = b + c * x := by rw [← hbr]; ring
  linarith

/-- 根 r の先（0 < r < x）では h > 0。 -/
theorem h_pos_beyond {c r x : ℝ} (hr0 : 0 < r) (hrx : r < x) (hr : h c r = 0) : 0 < h c x := by
  unfold h at *
  have hx0 : 0 < x := hr0.trans hrx
  set b := r / x
  have hb : 0 < b := div_pos hr0 hx0
  have hb1 : b < 1 := (div_lt_one hx0).mpr hrx
  have key := strictConvexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ x) (ne_of_lt hx0)
    (show (0 : ℝ) < 1 - b by linarith) hb (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at key
  have hbx : b * x = r := by simp only [b]; field_simp
  rw [hbx] at key
  have : exp r = 1 + c * r := by linarith
  rw [this] at key
  -- 1 + c r < 1 − b + b e^x、c r = c b x
  have : b * (exp x - 1 - c * x) > 0 := by rw [← hbx] at key; nlinarith
  exact pos_of_mul_pos_right this hb.le

/-- (3) 正の根の範囲：ln c < x_c < 2 ln c。 -/
theorem root_bounds {c r : ℝ} (hc : 1 < c) (hr0 : 0 < r) (hr : h c r = 0) :
    log c < r ∧ r < 2 * log c := by
  have hl : 0 < log c := log_pos hc
  constructor
  · by_contra hle
    push Not at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · have := h_pos_beyond hr0 hlt hr
      linarith [h_log_neg hc]
    · rw [heq] at hr; linarith [h_log_neg hc]
  · by_contra hle
    push Not at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · have := h_neg_between (by linarith) hlt hr
      linarith [h_two_log_pos hc]
    · rw [← heq] at hr; linarith [h_two_log_pos hc]

/-- (3) 正の根はちょうど一つ。 -/
theorem root_exists_unique {c : ℝ} (hc : 1 < c) : ∃! r, 0 < r ∧ h c r = 0 := by
  have hl : 0 < log c := log_pos hc
  have hcont : ContinuousOn (h c) (Icc (log c) (2 * log c)) := by
    unfold h; fun_prop
  obtain ⟨r, hrI, hr⟩ := intermediate_value_Ioo (by linarith) hcont
    (show (0 : ℝ) ∈ Ioo (h c (log c)) (h c (2 * log c)) from ⟨h_log_neg hc, h_two_log_pos hc⟩)
  refine ⟨r, ⟨hl.trans hrI.1, hr⟩, ?_⟩
  rintro s ⟨hs0, hs⟩
  rcases lt_trichotomy s r with hlt | heq | hgt
  · exact absurd hs (ne_of_lt (h_neg_between hs0 hlt hr))
  · exact heq
  · exact absurd hs (ne_of_gt (h_pos_beyond (hl.trans hrI.1) hgt hr))

/-! ### 成長曲線 -/

/-- 蓄積 V(t) = V_max (1 − e^(−kt))^c。 -/
noncomputable def V (Vm k c t : ℝ) : ℝ := Vm * (1 - exp (-(k * t))) ^ c

/-- 連年成長 V′(t) = V_max · c (1 − e^(−kt))^(c−1) · k e^(−kt)。 -/
noncomputable def dV (Vm k c t : ℝ) : ℝ :=
    Vm * c * (1 - exp (-(k * t))) ^ (c - 1) * (k * exp (-(k * t)))

theorem u_pos {k t : ℝ} (hk : 0 < k) (ht : 0 < t) : 0 < 1 - exp (-(k * t)) := by
  have : exp (-(k * t)) < 1 := by
    rw [← exp_zero]; exact exp_lt_exp.mpr (by nlinarith)
  linarith

theorem hasDerivAt_V (Vm c : ℝ) {k t : ℝ} (hk : 0 < k) (ht : 0 < t) :
    HasDerivAt (V Vm k c) (dV Vm k c t) t := by
  have h1 : HasDerivAt (fun s => 1 - exp (-(k * s))) (0 - exp (-(k * t)) * (-(k * 1))) t :=
    (hasDerivAt_const t 1).sub (((hasDerivAt_id' t).const_mul k).neg.exp)
  have h2 := (h1.rpow_const (p := c) (Or.inl (ne_of_gt (u_pos hk ht)))).const_mul Vm
  unfold V dV
  refine h2.congr_deriv ?_
  ring

/-- 区間 (0, 1) の u で u^(c−1)(1 − u) ≤ (1 − 1/c)^(c−1)·(1/c)（重み付きの相加相乗平均）。 -/
theorem amgm_peak {c u : ℝ} (hc : 1 < c) (hu0 : 0 < u) (hu1 : u < 1) :
    u ^ (c - 1) * (1 - u) ≤ (1 - 1 / c) ^ (c - 1) * (1 / c) := by
  have hc0 : 0 < c := by linarith
  have hw1 : 0 < 1 - 1 / c := by rw [sub_pos, div_lt_one hc0]; exact hc
  have hw2 : 0 < 1 / c := by positivity
  set a := u / (1 - 1 / c)
  set b := c * (1 - u)
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by have : 0 < 1 - u := by linarith
                        positivity
  have hg := geom_mean_le_arith_mean2_weighted hw1.le hw2.le ha hb (by ring)
  have hsum : (1 - 1 / c) * a + 1 / c * b = 1 := by
    simp only [a, b]; field_simp; ring
  rw [hsum] at hg
  have hpow := rpow_le_rpow (by positivity) hg hc0.le
  rw [one_rpow, mul_rpow (by positivity) (by positivity), ← rpow_mul ha, ← rpow_mul hb] at hpow
  have e1 : (1 - 1 / c) * c = c - 1 := by field_simp
  have e2 : 1 / c * c = 1 := by field_simp
  rw [e1, e2, rpow_one] at hpow
  simp only [a, b] at hpow
  rw [div_rpow hu0.le hw1.le] at hpow
  have hp : 0 < (1 - 1 / c) ^ (c - 1) := rpow_pos_of_pos hw1 _
  rw [div_mul_eq_mul_div, div_le_one hp] at hpow
  have : u ^ (c - 1) * (1 - u) = (u ^ (c - 1) * (c * (1 - u))) * (1 / c) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_right hpow hw2.le

/-- (1) 連年成長の頂点は t₁ = ln c/k。 -/
theorem rate_peak {Vm k c : ℝ} (hVm : 0 < Vm) (hk : 0 < k) (hc : 1 < c) {t : ℝ} (ht : 0 < t) :
    dV Vm k c t ≤ dV Vm k c (log c / k) := by
  have hc0 : 0 < c := by linarith
  have e1 : exp (-(k * (log c / k))) = 1 / c := by
    rw [show k * (log c / k) = log c by field_simp, exp_neg, exp_log hc0, one_div]
  unfold dV
  rw [e1]
  have hu := u_pos hk ht
  have hu1 : 1 - exp (-(k * t)) < 1 := by linarith [exp_pos (-(k * t))]
  have key := amgm_peak hc hu hu1
  set u := 1 - exp (-(k * t)) with hu_def
  have hE : exp (-(k * t)) = 1 - u := by rw [hu_def]; ring
  rw [hE]
  have hK : 0 < Vm * c * k := by positivity
  calc Vm * c * u ^ (c - 1) * (k * (1 - u)) = (Vm * c * k) * (u ^ (c - 1) * (1 - u)) := by ring
    _ ≤ (Vm * c * k) * ((1 - 1 / c) ^ (c - 1) * (1 / c)) := mul_le_mul_of_nonneg_left key hK.le
    _ = _ := by ring

/-- (2) 連年成長と平均成長が等しい ⇔ h(kt) = 0（e^(kt) = 1 + c·kt）。
さらに V′t − V の符号は −h(kt) の符号。 -/
theorem mean_gap {Vm k c t : ℝ} (hk : 0 < k) (ht : 0 < t) :
    dV Vm k c t * t - V Vm k c t =
      -(Vm * (1 - exp (-(k * t))) ^ (c - 1) * exp (-(k * t)) * h c (k * t)) := by
  have hu := u_pos hk ht
  unfold dV V h
  have hpow : (1 - exp (-(k * t))) ^ c = (1 - exp (-(k * t))) ^ (c - 1) * (1 - exp (-(k * t))) := by
    rw [rpow_sub_one (ne_of_gt hu)]; field_simp
  rw [hpow]
  have he : exp (-(k * t)) * exp (k * t) = 1 := by rw [← exp_add]; simp
  have : (1 - exp (-(k * t))) = exp (-(k * t)) * (exp (k * t) - 1) := by
    rw [mul_sub, he]; ring
  conv_lhs => rw [show (1 - exp (-(k * t))) ^ (c - 1) * (1 - exp (-(k * t))) =
    (1 - exp (-(k * t))) ^ (c - 1) * (exp (-(k * t)) * (exp (k * t) - 1)) by rw [← this]]
  ring

theorem mean_stationary_iff {Vm k c t : ℝ} (hVm : 0 < Vm) (hk : 0 < k) (ht : 0 < t) :
    dV Vm k c t * t = V Vm k c t ↔ h c (k * t) = 0 := by
  rw [← sub_eq_zero, mean_gap hk ht, neg_eq_zero]
  have : 0 < Vm * (1 - exp (-(k * t))) ^ (c - 1) * exp (-(k * t)) :=
    mul_pos (mul_pos hVm (rpow_pos_of_pos (u_pos hk ht) _)) (exp_pos _)
  constructor
  · intro h0; exact (mul_eq_zero.mp h0).resolve_left (ne_of_gt this)
  · intro h0; rw [h0, mul_zero]

/-- 平均成長 V(t)/t の微分。 -/
theorem hasDerivAt_mean {Vm k c t : ℝ} (hk : 0 < k) (ht : 0 < t) :
    HasDerivAt (fun s => V Vm k c s / s) ((dV Vm k c t * t - V Vm k c t) / t ^ 2) t := by
  have := (hasDerivAt_V Vm c hk ht).div (hasDerivAt_id' t) (ne_of_gt ht)
  refine this.congr_deriv ?_
  ring

/-- (4) 平均成長はただ一つの頂点 t₂ = x_c/k をもつ。 -/
theorem mean_peak {Vm k c r : ℝ} (hVm : 0 < Vm) (hk : 0 < k) (hr0 : 0 < r) (hr : h c r = 0)
    {t : ℝ} (ht : 0 < t) (hne : t ≠ r / k) :
    V Vm k c t / t < V Vm k c (r / k) / (r / k) := by
  set t₂ := r / k
  have ht₂ : 0 < t₂ := div_pos hr0 hk
  have hkt₂ : k * t₂ = r := by simp only [t₂]; field_simp
  have hA : ∀ s, 0 < s → HasDerivAt (fun s => V Vm k c s / s)
      ((dV Vm k c s * s - V Vm k c s) / s ^ 2) s :=
    fun s hs => hasDerivAt_mean hk hs
  have hpos : ∀ s, 0 < s → 0 < Vm * (1 - exp (-(k * s))) ^ (c - 1) * exp (-(k * s)) :=
    fun s hs => mul_pos (mul_pos hVm (rpow_pos_of_pos (u_pos hk hs) _)) (exp_pos _)
  have hcont : ∀ s, 0 < s → ContinuousAt (fun s => V Vm k c s / s) s :=
    fun s hs => (hA s hs).continuousAt
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- (0, t₂] で狭義に増える
    have hmono : StrictMonoOn (fun s => V Vm k c s / s) (Ioc 0 t₂) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioc 0 t₂)
      · exact fun s hs => (hcont s hs.1).continuousWithinAt
      · intro s hs
        rw [interior_Ioc] at hs
        rw [(hA s hs.1).deriv, mean_gap hk hs.1]
        have hneg : h c (k * s) < 0 := h_neg_between (by nlinarith [hs.1]) (by
          rw [← hkt₂]; exact mul_lt_mul_of_pos_left hs.2 hk) hr
        have := hpos s hs.1
        apply div_pos _ (by nlinarith [hs.1])
        nlinarith
    exact hmono ⟨ht, hlt.le⟩ ⟨ht₂, le_rfl⟩ hlt
  · -- [t₂, ∞) で狭義に減る
    have hanti : StrictAntiOn (fun s => V Vm k c s / s) (Ici t₂) := by
      apply strictAntiOn_of_deriv_neg (convex_Ici t₂)
      · exact fun s hs => (hcont s (ht₂.trans_le hs)).continuousWithinAt
      · intro s hs
        rw [interior_Ici] at hs
        have hs0 : 0 < s := ht₂.trans hs
        rw [(hA s hs0).deriv, mean_gap hk hs0]
        have hp : 0 < h c (k * s) := h_pos_beyond hr0 (by
          rw [← hkt₂]; exact mul_lt_mul_of_pos_left hs hk) hr
        have := hpos s hs0
        apply div_neg_of_neg_of_pos _ (by positivity)
        nlinarith
    exact hanti (le_refl t₂) (le_of_lt hgt) hgt

/-- (5) 頂点の順：t₁ < t₂ < 2t₁（t₁ = ln c/k、t₂ = x_c/k）。 -/
theorem peaks_order {k c r : ℝ} (hk : 0 < k) (hc : 1 < c) (hr0 : 0 < r) (hr : h c r = 0) :
    log c / k < r / k ∧ r / k < 2 * (log c / k) := by
  obtain ⟨h1, h2⟩ := root_bounds hc hr0 hr
  refine ⟨div_lt_div_of_pos_right h1 hk, ?_⟩
  rw [← mul_div_assoc]
  exact div_lt_div_of_pos_right h2 hk

/-- 比 t₂/t₁ = x_c/ln c は k によらない。 -/
theorem ratio_indep_k {k c r : ℝ} (hk : 0 < k) (hc : 1 < c) :
    (r / k) / (log c / k) = r / log c := by
  have : 0 < log c := log_pos hc
  field_simp

end Paper581

end Yamagishi
