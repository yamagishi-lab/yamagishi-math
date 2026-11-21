/-
論文511『閾値と最終規模は、同じ R₀ から出るのに、比が一定にならない』の格上げ（一般の形）。

原稿（511_yamagishi_threshold_and_final_size/…_jp.tex）は、閉じた一様な SIR 模型で
閾値 p_c = 1 − 1/R₀ と最終規模 z（z = 1 − e^(−R₀z) の正の解）を、R₀ = 0.9, 1, 1.5, 2, 3, 5 の
数表で並べ、比 z/p_c が 1.7484 から 1.2413 へ動くことを示す。上下の限界と単調性は述べていない。

ここで証明した言明：
  (1) `root_iff`：0 < z < 1 で z = 1 − e^(−R₀z) ⇔ R₀ = −ln(1 − z)/z。
      `root_exists_unique`：R₀ > 1 なら (0, 1) の解はちょうど一つ。
      `root_needs_R0_gt_one`：(0, 1) に解があれば R₀ > 1。
      `root_strictMono`：R₀ が大きいほど z は大きい。
  (2) `threshold_lt_final`・`final_lt_two_threshold`：すべての R₀ > 1 で p_c < z < 2p_c。
  (3) `ratio_bounds`：比 z/p_c について 1 + √(1 − z) < z/p_c < 2。
      `ratio_strictAnti_R0`：比 z/p_c は R₀ について狭義に減る。
      `ratio_tendsto_two`：z → 0+（R₀ → 1+ の側）で比は 2 に近づく。
足した仮定：模型の式 z = 1 − e^(−R₀z) と p_c = 1 − 1/R₀ を定義として置いた（SIR の微分方程式から
最終規模の式を出す所は形式化していない）。
形式化していないもの：R₀ → ∞ で比 → 1 の極限（下の限界 1 + √(1 − z) > 1 と、比 < z/(1 − z/L) から
出る見込みだが書いていない）。R₀ → 1+ の極限は z → 0+ の形で示した（z が R₀ について連続に 0 へ
行くことは書いていない）。数表の値、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper511

open Real Set Filter Topology

/-- L(z) = −ln(1 − z)。 -/
noncomputable def L (z : ℝ) : ℝ := -log (1 - z)

/-- 最終規模 z に対応する R₀ = L(z)/z。 -/
noncomputable def R0of (z : ℝ) : ℝ := L z / z

/-- 比 z/p_c = z/(1 − 1/R₀)。 -/
noncomputable def ratio (z R₀ : ℝ) : ℝ := z / (1 - 1 / R₀)

theorem hasDerivAt_L {z : ℝ} (hz : z < 1) : HasDerivAt L (1 / (1 - z)) z := by
  have h := ((hasDerivAt_id' z).const_sub 1).log (by linarith)
  have := h.neg
  unfold L
  refine this.congr_deriv ?_
  field_simp

/-- z < L(z) < z/(1 − z)（0 < z < 1）。 -/
theorem L_bounds {z : ℝ} (h0 : 0 < z) (h1 : z < 1) : z < L z ∧ L z < z / (1 - z) := by
  unfold L
  constructor
  · have := log_lt_sub_one_of_pos (x := 1 - z) (by linarith) (by linarith)
    linarith
  · have hw : 0 < 1 - z := by linarith
    have := log_lt_sub_one_of_pos (x := 1 / (1 - z)) (by positivity) (by
      intro h; rw [div_eq_one_iff_eq (ne_of_gt hw)] at h; linarith)
    rw [one_div, log_inv] at this
    have e : (1 - z)⁻¹ - 1 = z / (1 - z) := by field_simp; ring
    linarith

/-- 2z/(2 − z) < L(z)（0 < z < 1）。 -/
theorem L_lower2 {z : ℝ} (h0 : 0 < z) (h1 : z < 1) : 2 * z / (2 - z) < L z := by
  let φ : ℝ → ℝ := fun z => L z - 2 * z / (2 - z)
  have hφd : ∀ x, x < 1 → HasDerivAt φ (1 / (1 - x) - 4 / (2 - x) ^ 2) x := by
    intro x hx
    have h2 : HasDerivAt (fun x => 2 * x / (2 - x))
        ((2 * 1 * (2 - x) - 2 * x * (0 - 1)) / (2 - x) ^ 2) x :=
      ((hasDerivAt_id' x).const_mul 2).div ((hasDerivAt_const x 2).sub (hasDerivAt_id' x))
          (by linarith)
    refine ((hasDerivAt_L hx).sub h2).congr_deriv ?_
    have : (2 - x) ≠ 0 := by linarith
    field_simp; ring
  have hmono : StrictMonoOn φ (Ico 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico 0 1)
    · exact fun x hx => (hφd x hx.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hφd x hx.2).deriv]
      have ha : 0 < 1 - x := by linarith [hx.2]
      have hb : 0 < 2 - x := by linarith [hx.2]
      have : 1 / (1 - x) - 4 / (2 - x) ^ 2 = x ^ 2 / ((1 - x) * (2 - x) ^ 2) := by
        field_simp; ring
      rw [this]; have := hx.1; positivity
  have := hmono ⟨le_refl 0, by norm_num⟩ ⟨h0.le, h1⟩ h0
  simp only [φ, L, sub_zero, log_one, neg_zero, mul_zero, zero_div] at this
  unfold L; linarith

/-- L(z) < z/√(1 − z)（0 < z < 1）。sinh y > y から。 -/
theorem L_upper_sqrt {z : ℝ} (h0 : 0 < z) (h1 : z < 1) : L z < z / √(1 - z) := by
  have hw : 0 < 1 - z := by linarith
  set s := √(1 - z) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hw
  have hs2 : s ^ 2 = 1 - z := Real.sq_sqrt hw.le
  have hs1 : s < 1 := by nlinarith
  set y := 1 / s
  have hy : 1 < y := by rw [one_lt_div hs0]; exact hs1
  have hly : 0 < log y := log_pos hy
  have hsh := (self_lt_sinh_iff (x := log y)).mpr hly
  rw [sinh_eq, exp_neg, exp_log (by linarith)] at hsh
  have hL : L z = 2 * log y := by
    unfold L
    rw [← hs2, show s ^ 2 = (1 / y) ^ 2 by simp [y]]
    rw [log_pow, one_div, log_inv]; push_cast; ring
  have hz : z / s = y - y⁻¹ := by
    have : z = 1 - s ^ 2 := by linarith
    rw [this]; simp only [y]; field_simp
  rw [hL, hz]; linarith

/-- (1) 解の式：0 < z < 1 で z = 1 − e^(−R₀z) ⇔ R₀ = L(z)/z。 -/
theorem root_iff {z R₀ : ℝ} (h0 : 0 < z) (h1 : z < 1) :
    z = 1 - exp (-(R₀ * z)) ↔ R₀ = R0of z := by
  unfold R0of L
  constructor
  · intro h
    have he : exp (-(R₀ * z)) = 1 - z := by linarith
    have := congrArg log he
    rw [log_exp] at this
    field_simp; linarith
  · intro h
    rw [h]
    have : -(-log (1 - z) / z * z) = log (1 - z) := by field_simp
    rw [this, exp_log (by linarith)]; ring

theorem R0of_gt_one {z : ℝ} (h0 : 0 < z) (h1 : z < 1) : 1 < R0of z := by
  unfold R0of; rw [one_lt_div h0]; exact (L_bounds h0 h1).1

theorem R0of_strictMono : StrictMonoOn R0of (Ioo 0 1) := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt R0of ((1 / (1 - x) * x - L x * 1) / x ^ 2) x :=
    fun x hx => (hasDerivAt_L hx.2).div (hasDerivAt_id' x) (ne_of_gt hx.1)
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hd x hx).deriv]
    have hb := (L_bounds hx.1 hx.2).2
    apply div_pos _ (by have := hx.1; positivity)
    have : 1 / (1 - x) * x = x / (1 - x) := by ring
    linarith

/-- (1) (0, 1) に解があれば R₀ > 1。 -/
theorem root_needs_R0_gt_one {z R₀ : ℝ} (h0 : 0 < z) (h1 : z < 1) (h : z = 1 - exp (-(R₀ * z))) :
    1 < R₀ := by
  rw [(root_iff h0 h1).mp h]; exact R0of_gt_one h0 h1

/-- (1) R₀ > 1 なら (0, 1) の解はちょうど一つ。 -/
theorem root_exists_unique {R₀ : ℝ} (hR : 1 < R₀) :
    ∃! z, (0 < z ∧ z < 1) ∧ z = 1 - exp (-(R₀ * z)) := by
  have hR0 : 0 < R₀ := by linarith
  let f : ℝ → ℝ := fun z => 1 - exp (-(R₀ * z)) - z
  set z₀ := (R₀ - 1) / (2 * R₀)
  have hz₀ : 0 < z₀ := by positivity
  have hz₀1 : z₀ < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hf0 : 0 < f z₀ := by
    simp only [f]
    have hx : R₀ * z₀ = (R₀ - 1) / 2 := by simp only [z₀]; field_simp
    rw [hx, exp_neg]
    have he := add_one_le_exp ((R₀ - 1) / 2)
    have hep : 0 < exp ((R₀ - 1) / 2) := exp_pos _
    -- 1 − 1/e^x ≥ x/(1 + x) > z₀
    have : (exp ((R₀ - 1) / 2))⁻¹ ≤ 1 / ((R₀ - 1) / 2 + 1) := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by linarith) he
    have : 1 / ((R₀ - 1) / 2 + 1) = 2 / (R₀ + 1) := by field_simp; ring
    have hlt : 2 / (R₀ + 1) < 1 - z₀ := by
      simp only [z₀]
      rw [div_lt_iff₀ (by linarith)]
      field_simp
      nlinarith
    linarith
  have hf1 : f 1 < 0 := by simp only [f]; linarith [exp_pos (-(R₀ * 1))]
  have hcont : ContinuousOn f (Icc z₀ 1) := by simp only [f]; fun_prop
  obtain ⟨z, hzI, hz⟩ := intermediate_value_Ioo' hz₀1.le hcont ⟨hf1, hf0⟩
  have hz0 : 0 < z := hz₀.trans hzI.1
  have hzroot : z = 1 - exp (-(R₀ * z)) := by simp only [f] at hz; linarith
  refine ⟨z, ⟨⟨hz0, hzI.2⟩, hzroot⟩, ?_⟩
  rintro w ⟨⟨hw0, hw1⟩, hw⟩
  have e1 := (root_iff hw0 hw1).mp hw
  have e2 := (root_iff hz0 hzI.2).mp hzroot
  exact R0of_strictMono.injOn ⟨hw0, hw1⟩ ⟨hz0, hzI.2⟩ (e1.symm.trans e2)

/-- (1) R₀ が大きいほど z は大きい。 -/
theorem root_strictMono {z z' R₀ R₀' : ℝ} (hz : 0 < z ∧ z < 1) (hz' : 0 < z' ∧ z' < 1)
    (h : z = 1 - exp (-(R₀ * z))) (h' : z' = 1 - exp (-(R₀' * z'))) (hlt : R₀ < R₀') : z < z' := by
  rw [(root_iff hz.1 hz.2).mp h, (root_iff hz'.1 hz'.2).mp h'] at hlt
  by_contra hle; push Not at hle
  rcases eq_or_lt_of_le hle with heq | hlt'
  · rw [heq] at hlt; exact lt_irrefl _ hlt
  · exact lt_asymm hlt (R0of_strictMono hz' hz hlt')

/-- 比を z だけで書く：z/p_c = z·L/(L − z)。 -/
theorem ratio_eq {z : ℝ} (h0 : 0 < z) (h1 : z < 1) : ratio z (R0of z) = z * L z / (L z - z) := by
  have hL := (L_bounds h0 h1).1
  unfold ratio R0of
  have : L z - z ≠ 0 := by linarith
  have : L z ≠ 0 := by linarith
  field_simp

/-- (2) 閾値より最終規模が大きい：p_c < z。 -/
theorem threshold_lt_final {z R₀ : ℝ} (h0 : 0 < z) (h1 : z < 1) (h : z = 1 - exp (-(R₀ * z))) :
    1 - 1 / R₀ < z := by
  rw [(root_iff h0 h1).mp h]
  unfold R0of
  obtain ⟨hL1, hL2⟩ := L_bounds h0 h1
  have hLp : 0 < L z := by linarith
  rw [one_div_div, sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', lt_div_iff₀ hLp]
  rw [lt_div_iff₀ (by linarith)] at hL2
  linarith

/-- (2) 最終規模は閾値の 2 倍より小さい：z < 2p_c。 -/
theorem final_lt_two_threshold {z R₀ : ℝ} (h0 : 0 < z) (h1 : z < 1) (h : z = 1 - exp (-(R₀ * z))) :
    z < 2 * (1 - 1 / R₀) := by
  rw [(root_iff h0 h1).mp h]
  unfold R0of
  have hL := L_lower2 h0 h1
  have hLp : 0 < L z := by linarith [(L_bounds h0 h1).1]
  rw [one_div_div]
  rw [div_lt_iff₀ (by linarith)] at hL
  have : z / L z < (2 - z) / 2 := by
    rw [div_lt_div_iff₀ hLp (by norm_num)]; linarith
  linarith

/-- (3) 比の上下：1 + √(1 − z) < z/p_c < 2。 -/
theorem ratio_bounds {z : ℝ} (h0 : 0 < z) (h1 : z < 1) :
    1 + √(1 - z) < ratio z (R0of z) ∧ ratio z (R0of z) < 2 := by
  have hroot : z = 1 - exp (-(R0of z * z)) := (root_iff h0 h1).mpr rfl
  have hpc := threshold_lt_final h0 h1 hroot
  have hpc2 := final_lt_two_threshold h0 h1 hroot
  have hp : 0 < 1 - 1 / R0of z := by
    have := R0of_gt_one h0 h1
    rw [sub_pos, div_lt_one (by linarith)]; exact this
  constructor
  · rw [ratio_eq h0 h1]
    have hu := L_upper_sqrt h0 h1
    have hLz := (L_bounds h0 h1).1
    have hw : 0 < 1 - z := by linarith
    set s := √(1 - z)
    have hs0 : 0 < s := Real.sqrt_pos.mpr hw
    have hs2 : s ^ 2 = 1 - z := Real.sq_sqrt hw.le
    have hs1 : s < 1 := by nlinarith
    rw [lt_div_iff₀ (by linarith)]
    rw [lt_div_iff₀ hs0] at hu
    -- (1 + s)(L − z) < zL ⇔ L(1 + s − z) < z(1 + s) ⇔ L·s(1 + s)·… を s² = 1 − z で整理
    have : 1 + s - z = s * (1 + s) := by nlinarith
    nlinarith [mul_lt_mul_of_pos_right hu (by linarith : (0 : ℝ) < 1 + s)]
  · unfold ratio
    rw [div_lt_iff₀ hp]; linarith

/-- 比 z·L/(L − z) は z について狭義に減る。 -/
theorem ratio_strictAnti_z : StrictAntiOn (fun z => z * L z / (L z - z)) (Ioo 0 1) := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun z => z * L z / (L z - z))
      ((L x ^ 2 - x ^ 2 * (1 / (1 - x))) / (L x - x) ^ 2) x := by
    intro x hx
    have hL := hasDerivAt_L hx.2
    have hne : L x - x ≠ 0 := by linarith [(L_bounds hx.1 hx.2).1]
    have := ((hasDerivAt_id' x).mul hL).div (hL.sub (hasDerivAt_id' x)) hne
    refine this.congr_deriv ?_
    have h1x : 1 - x ≠ 0 := by linarith [hx.2]
    simp only [Pi.mul_apply, Pi.sub_apply]
    field_simp
    ring
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hd x hx).deriv]
    have hu := L_upper_sqrt hx.1 hx.2
    have hLz := (L_bounds hx.1 hx.2).1
    have hw : 0 < 1 - x := by linarith [hx.2]
    have hs0 : 0 < √(1 - x) := Real.sqrt_pos.mpr hw
    have hs2 : √(1 - x) ^ 2 = 1 - x := Real.sq_sqrt hw.le
    apply div_neg_of_neg_of_pos _ (by have : L x - x ≠ 0 := by linarith
                                      positivity)
    -- L² < x²/(1 − x)
    have hLp : 0 < L x := by linarith [hx.1]
    have h2 : L x ^ 2 < (x / √(1 - x)) ^ 2 := by
      apply pow_lt_pow_left₀ hu hLp.le (by norm_num)
    rw [div_pow, hs2] at h2
    have : x ^ 2 * (1 / (1 - x)) = x ^ 2 / (1 - x) := by ring
    linarith

/-- (3) 比 z/p_c は R₀ について狭義に減る。 -/
theorem ratio_strictAnti_R0 {z z' R₀ R₀' : ℝ} (hz : 0 < z ∧ z < 1) (hz' : 0 < z' ∧ z' < 1)
    (h : z = 1 - exp (-(R₀ * z))) (h' : z' = 1 - exp (-(R₀' * z'))) (hlt : R₀ < R₀') :
    ratio z' R₀' < ratio z R₀ := by
  have hzz := root_strictMono hz hz' h h' hlt
  rw [(root_iff hz.1 hz.2).mp h, (root_iff hz'.1 hz'.2).mp h',
      ratio_eq hz.1 hz.2, ratio_eq hz'.1 hz'.2]
  exact ratio_strictAnti_z hz hz' hzz

/-- (3) z → 0+ で比 → 2。 -/
theorem ratio_tendsto_two :
    Tendsto (fun z => ratio z (R0of z)) (𝓝[>] 0) (𝓝 2) := by
  have hlow : Tendsto (fun z : ℝ => 1 + √(1 - z)) (𝓝[>] 0) (𝓝 2) := by
    have : Tendsto (fun z : ℝ => 1 + √(1 - z)) (𝓝 0) (𝓝 (1 + √(1 - 0))) := by
      apply Continuous.tendsto; fun_prop
    simp only [sub_zero, sqrt_one] at this
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ z in 𝓝[>] (0 : ℝ), 0 < z ∧ z < 1 := by
    have : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with z hz using hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [hev] with z hz using (ratio_bounds hz.1 hz.2).1.le
  · filter_upwards [hev] with z hz using (ratio_bounds hz.1 hz.2).2.le

end Paper511

end Yamagishi
