/-
論文385『撚りは繊維を荷重方向から傾けるだけなのに、撚らない糸の強度はゼロである』の格上げ（一般の形）。

原稿（385_yamagishi_twisting_only_tilts_the_fibres_yet_zero_twist_is_zero_strength/…_jp.tex）は、
模型 S(α) = cos²α·(1 − e^(−k tan α)) を k = 1.2 の一つの値で数え、撚角 0〜60 度の表と、
最大の位置 34.55 度・値 0.381464 を出している。最大がただ一つであることや、45 度未満であることは
述べていない（観察 5.5 で「最大の位置は k で動く」とだけ書く）。

ここで証明した言明（すべての k > 0）：
  (1) `S_eq_F`：t = tan α と置くと S = (1 − e^(−kt))/(1 + t²)。
  (2) `root_unique`：2t(e^(kt) − 1) = k(1 + t²) の正の解はちょうど一つで、0 < t* < 1。
  (3) `F_lt_max`・`S_lt_max`：強度は t*（角では α* = arctan t*）でただ一つの最大をとる。
      `astar_lt_pi_div_four`：0 < α* < 45 度（π/4）。
  (4) `tstar_strictAnti`・`astar_strictAnti`：k が大きいほど α* は狭義に小さい。
  (5) `tstar_lower`・`tstar_upper`：1 < t*²(2e^k − 1)、k t*³ < 1（すべての k > 0 での上下の限界）。
      `astar_tendsto_zero_right`：k → 0+ で α* → 45 度。`astar_tendsto_atTop`：k → ∞ で α* → 0。
  (6) `S_zero`：0 度の強度はちょうど 0。
定義に置いたもの：強度の模型 S（原稿の式そのまま）。形式化していないもの：繊維の力学・分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper385

open Real Set Filter Topology

/-- 撚角 α での強度（原稿の模型）。 -/
noncomputable def S (k α : ℝ) : ℝ := cos α ^ 2 * (1 - exp (-(k * tan α)))

/-- t = tan α で書いた強度。 -/
noncomputable def F (k t : ℝ) : ℝ := (1 - exp (-(k * t))) / (1 + t ^ 2)

/-- 停留点の式 2t(e^(kt) − 1) − k(1 + t²)。 -/
noncomputable def g (k t : ℝ) : ℝ := 2 * t * (exp (k * t) - 1) - k * (1 + t ^ 2)

/-- (1) t = tan α への書き換え。 -/
theorem S_eq_F (k α : ℝ) (h : cos α ≠ 0) : S k α = F k (tan α) := by
  unfold S F
  rw [div_eq_mul_inv, inv_one_add_tan_sq h]; ring

/-- (6) 0 度の強度は 0。 -/
theorem S_zero (k : ℝ) : S k 0 = 0 := by simp [S]

theorem numer_eq (k t : ℝ) :
    k * exp (-(k * t)) * (1 + t ^ 2) - (1 - exp (-(k * t))) * (2 * t)
      = -(exp (-(k * t)) * g k t) := by
  unfold g
  have hE : exp (k * t) ≠ 0 := (exp_pos _).ne'
  rw [exp_neg]; field_simp; ring

theorem hasDerivAt_F (k t : ℝ) :
    HasDerivAt (F k) (-(exp (-(k * t)) * g k t) / (1 + t ^ 2) ^ 2) t := by
  have h0 : HasDerivAt (fun t => -(k * t)) (-k) t := by
    have := (hasDerivAt_id t).const_mul (-k)
    convert this using 1
    · funext x; simp
    · simp
  have h1 : HasDerivAt (fun t => 1 - exp (-(k * t))) (k * exp (-(k * t))) t := by
    have := h0.exp.const_sub 1
    convert this using 1; ring
  have h2 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    have := (hasDerivAt_pow 2 t).const_add 1
    convert this using 1; ring
  have hne : (1 + t ^ 2) ≠ 0 := by positivity
  have := h1.div h2 hne
  rw [← numer_eq]
  exact this

theorem continuous_F (k : ℝ) : Continuous (F k) := by
  show Continuous fun t => (1 - exp (-(k * t))) / (1 + t ^ 2)
  exact (by fun_prop : Continuous fun t => 1 - exp (-(k * t))).div
    (by fun_prop : Continuous fun t : ℝ => 1 + t ^ 2) (fun t => by positivity)

theorem continuous_g (k : ℝ) : Continuous (g k) := by
  show Continuous fun t => 2 * t * (exp (k * t) - 1) - k * (1 + t ^ 2)
  fun_prop

theorem hasDerivAt_g (k t : ℝ) :
    HasDerivAt (g k) (2 * (exp (k * t) - 1) * (1 + k * t)) t := by
  have h1 : HasDerivAt (fun t => exp (k * t)) (k * exp (k * t)) t := by
    have := ((hasDerivAt_id t).const_mul k).exp
    convert this using 1 <;> simp [mul_comm]
  have h2 := (((hasDerivAt_id t).const_mul 2).mul (h1.sub_const 1)).sub
    (((hasDerivAt_pow 2 t).const_add 1).const_mul k)
  unfold g
  convert h2 using 1
  · funext x; simp
  · simp; ring

theorem g_strictMonoOn {k : ℝ} (hk : 0 < k) : StrictMonoOn (g k) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (continuous_g k).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  have hx : 0 < x := hx
  rw [(hasDerivAt_g k x).deriv]
  have : 1 < exp (k * x) := one_lt_exp_iff.2 (by positivity)
  have : 0 < 1 + k * x := by positivity
  have : 0 < exp (k * x) - 1 := by linarith
  positivity

theorem g_zero (k : ℝ) : g k 0 = -k := by simp [g]

theorem g_one {k : ℝ} (hk : 0 < k) : 0 < g k 1 := by
  have := add_one_lt_exp hk.ne'
  unfold g; norm_num; nlinarith

/-- (2) 根は (0, 1) にある。 -/
theorem root_exists {k : ℝ} (hk : 0 < k) : ∃ t, 0 < t ∧ t < 1 ∧ g k t = 0 := by
  have hmem : (0 : ℝ) ∈ Ioo (g k 0) (g k 1) := ⟨by rw [g_zero]; linarith, g_one hk⟩
  obtain ⟨t, ⟨ht0, ht1⟩, hgt⟩ :=
    intermediate_value_Ioo zero_le_one (continuous_g k).continuousOn hmem
  exact ⟨t, ht0, ht1, hgt⟩

/-- 最良の tan α（k ≤ 0 では 0 を置く）。 -/
noncomputable def tstar (k : ℝ) : ℝ :=
  if hk : 0 < k then Classical.choose (root_exists hk) else 0

theorem tstar_spec {k : ℝ} (hk : 0 < k) : 0 < tstar k ∧ tstar k < 1 ∧ g k (tstar k) = 0 := by
  simp only [tstar, hk, ↓reduceDIte]; exact Classical.choose_spec (root_exists hk)

/-- (2) 正の解はちょうど一つ。 -/
theorem root_unique {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : 0 < t) (hg : g k t = 0) :
    t = tstar k := by
  obtain ⟨h0, -, hg0⟩ := tstar_spec hk
  exact (g_strictMonoOn hk).injOn (mem_Ici.2 ht.le) (mem_Ici.2 h0.le) (hg.trans hg0.symm)

theorem g_neg_of_lt {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : 0 ≤ t) (h : t < tstar k) : g k t < 0 := by
  obtain ⟨h0, -, hg0⟩ := tstar_spec hk
  have := g_strictMonoOn hk (mem_Ici.2 ht) (mem_Ici.2 h0.le) h
  linarith

theorem g_pos_of_gt {k : ℝ} (hk : 0 < k) {t : ℝ} (h : tstar k < t) : 0 < g k t := by
  obtain ⟨h0, -, hg0⟩ := tstar_spec hk
  have := g_strictMonoOn hk (mem_Ici.2 h0.le) (mem_Ici.2 (h0.le.trans h.le)) h
  linarith

theorem F_strictMonoOn {k : ℝ} (hk : 0 < k) : StrictMonoOn (F k) (Icc 0 (tstar k)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_F k).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_F k x).deriv]
  have := g_neg_of_lt hk hx.1.le hx.2
  have : 0 < exp (-(k * x)) := exp_pos _
  have : 0 < (1 + x ^ 2) ^ 2 := by positivity
  apply div_pos _ this
  nlinarith

theorem F_strictAntiOn {k : ℝ} (hk : 0 < k) : StrictAntiOn (F k) (Ici (tstar k)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (continuous_F k).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  rw [(hasDerivAt_F k x).deriv]
  have := g_pos_of_gt hk hx
  have : 0 < exp (-(k * x)) := exp_pos _
  have : 0 < (1 + x ^ 2) ^ 2 := by positivity
  apply div_neg_of_neg_of_pos _ this
  nlinarith

/-- (3) t* でただ一つの最大。 -/
theorem F_lt_max {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : 0 ≤ t) (hne : t ≠ tstar k) :
    F k t < F k (tstar k) := by
  obtain ⟨h0, -, -⟩ := tstar_spec hk
  rcases lt_or_gt_of_ne hne with h | h
  · exact F_strictMonoOn hk ⟨ht, h.le⟩ ⟨h0.le, le_rfl⟩ h
  · exact F_strictAntiOn hk (mem_Ici.2 le_rfl) (mem_Ici.2 h.le) h

/-- 最良の撚角 α* = arctan t*。 -/
noncomputable def astar (k : ℝ) : ℝ := arctan (tstar k)

theorem astar_pos {k : ℝ} (hk : 0 < k) : 0 < astar k := by
  have := arctan_strictMono (tstar_spec hk).1
  rwa [arctan_zero] at this

/-- (3) α* は 45 度未満。 -/
theorem astar_lt_pi_div_four {k : ℝ} (hk : 0 < k) : astar k < π / 4 := by
  have := arctan_strictMono (tstar_spec hk).2.1
  rwa [arctan_one] at this

theorem astar_lt_pi_div_two {k : ℝ} (hk : 0 < k) : astar k < π / 2 := by
  have := astar_lt_pi_div_four hk; linarith [pi_pos]

/-- (3) 角で書いた強度は α* でただ一つの最大をとる（0 < α < 90 度）。 -/
theorem S_lt_max {k : ℝ} (hk : 0 < k) {α : ℝ} (h0 : 0 < α) (h1 : α < π / 2)
    (hne : α ≠ astar k) : S k α < S k (astar k) := by
  have hc : cos α ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h1⟩).ne'
  rw [S_eq_F k α hc, astar, S_eq_F k _ (cos_arctan_pos _).ne', tan_arctan]
  apply F_lt_max hk (tan_pos_of_pos_of_lt_pi_div_two h0 h1).le
  intro h
  apply hne
  rw [astar, ← h, arctan_tan (by linarith [pi_pos]) h1]

theorem S_le_max {k : ℝ} (hk : 0 < k) {α : ℝ} (h0 : 0 < α) (h1 : α < π / 2) :
    S k α ≤ S k (astar k) := by
  by_cases h : α = astar k
  · rw [h]
  · exact (S_lt_max hk h0 h1 h).le

/-- 根での鍵の不等式 1 + t*² < 2t*²e^(kt*)。 -/
theorem key_ineq {k : ℝ} (hk : 0 < k) :
    1 + tstar k ^ 2 < 2 * tstar k ^ 2 * exp (k * tstar k) := by
  obtain ⟨h0, -, hg⟩ := tstar_spec hk
  set t := tstar k
  set E := exp (k * t)
  have hu : 0 < k * t := by positivity
  -- 1 − u < e^(−u) から E − 1 < uE
  have h1 : 1 - k * t < exp (-(k * t)) := by
    have := add_one_lt_exp (neg_ne_zero.2 hu.ne'); linarith
  have hEpos : 0 < E := exp_pos _
  have h2 : E - 1 < k * t * E := by
    have : exp (-(k * t)) * E = 1 := by rw [← exp_add]; simp
    nlinarith
  unfold g at hg
  -- 2t(E − 1) = k(1 + t²)
  have h3 : k * (1 + t ^ 2) < k * (2 * t ^ 2 * E) := by nlinarith
  exact lt_of_mul_lt_mul_left h3 hk.le

/-- (4) k が大きいほど t* は狭義に小さい。 -/
theorem tstar_strictAnti {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (h : k₁ < k₂) : tstar k₂ < tstar k₁ := by
  have hk₂ : 0 < k₂ := hk₁.trans h
  obtain ⟨h0, -, hg1⟩ := tstar_spec hk₁
  set t := tstar k₁ with ht
  have hkey := key_ineq hk₁
  rw [← ht] at hkey
  -- g k₂ t > 0
  have hpos : 0 < g k₂ t := by
    have hexp : exp (k₁ * t) * (1 + (k₂ - k₁) * t) ≤ exp (k₂ * t) := by
      have := add_one_le_exp ((k₂ - k₁) * t)
      have h' : exp (k₂ * t) = exp (k₁ * t) * exp ((k₂ - k₁) * t) := by
        rw [← exp_add]; ring_nf
      rw [h']
      exact mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
    unfold g at hg1 ⊢
    have hd : 0 < k₂ - k₁ := by linarith
    nlinarith [mul_pos hd (by linarith : (0:ℝ) < 2 * t ^ 2 * exp (k₁ * t) - (1 + t ^ 2))]
  by_contra hc
  push Not at hc
  have hs := tstar_spec hk₂
  have : g k₂ t ≤ g k₂ (tstar k₂) :=
    (g_strictMonoOn hk₂).monotoneOn (mem_Ici.2 h0.le) (mem_Ici.2 hs.1.le) hc
  linarith [hs.2.2]

theorem astar_strictAnti {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (h : k₁ < k₂) : astar k₂ < astar k₁ :=
  arctan_strictMono (tstar_strictAnti hk₁ h)

/-- (5) 下の限界 1 < t*²(2e^k − 1)。 -/
theorem tstar_lower {k : ℝ} (hk : 0 < k) : 1 < tstar k ^ 2 * (2 * exp k - 1) := by
  obtain ⟨h0, h1, -⟩ := tstar_spec hk
  have hkey := key_ineq hk
  have : exp (k * tstar k) < exp k := exp_lt_exp.2 (by nlinarith)
  nlinarith [sq_nonneg (tstar k), mul_pos h0 h0]

/-- (5) 上の限界 k t*³ < 1。 -/
theorem tstar_upper {k : ℝ} (hk : 0 < k) : k * tstar k ^ 3 < 1 := by
  obtain ⟨h0, h1, hg⟩ := tstar_spec hk
  set t := tstar k
  have hq := quadratic_le_exp_of_nonneg (by positivity : 0 ≤ k * t)
  unfold g at hg
  -- k(1 + t²) = 2t(E − 1) ≥ 2t(kt + k²t²/2)
  have : k * (2 * t ^ 2 + k * t ^ 3) ≤ k * (1 + t ^ 2) := by nlinarith
  have := le_of_mul_le_mul_left this hk
  nlinarith [pow_pos h0 2]

/-- (5) k → 0+ で t* → 1。 -/
theorem tstar_tendsto_zero_right : Tendsto tstar (𝓝[>] 0) (𝓝 1) := by
  have hc : Continuous (fun k : ℝ => 2 * exp k - 1) := by fun_prop
  have h := (hc.tendsto 0).inv₀ (by norm_num : (2 * exp 0 - 1 : ℝ) ≠ 0)
  have hl : Tendsto (fun k : ℝ => 1 / (2 * exp k - 1)) (𝓝[>] 0) (𝓝 1) := by
    simp only [one_div]
    convert h.mono_left nhdsWithin_le_nhds using 2
    norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with k hk
    obtain ⟨h0, h1, -⟩ := tstar_spec hk
    have hlow := tstar_lower hk
    have he : 1 < 2 * exp k - 1 := by have := one_lt_exp_iff.2 hk; linarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · filter_upwards [self_mem_nhdsWithin] with k hk
    exact (tstar_spec hk).2.1.le

/-- (5) k → 0+ で α* → 45 度。 -/
theorem astar_tendsto_zero_right : Tendsto astar (𝓝[>] 0) (𝓝 (π / 4)) := by
  rw [← arctan_one]
  exact (continuous_arctan.tendsto 1).comp tstar_tendsto_zero_right

/-- (5) k → ∞ で t* → 0。 -/
theorem tstar_tendsto_atTop : Tendsto tstar atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact ha.trans (tstar_spec hk).1
  · intro b hb
    filter_upwards [eventually_gt_atTop (1 / b ^ 3)] with k hk
    have hb3 : 0 < b ^ 3 := by positivity
    have hkpos : 0 < k := lt_trans (by positivity) hk
    have hup := tstar_upper hkpos
    have h0 := (tstar_spec hkpos).1
    have : tstar k ^ 3 < b ^ 3 := by
      rw [div_lt_iff₀ hb3] at hk
      nlinarith [pow_pos h0 3]
    exact lt_of_pow_lt_pow_left₀ 3 hb.le this

/-- (5) k → ∞ で α* → 0。 -/
theorem astar_tendsto_atTop : Tendsto astar atTop (𝓝 0) := by
  have := (continuous_arctan.tendsto 0).comp tstar_tendsto_atTop
  rwa [arctan_zero] at this

end Paper385

end Yamagishi
