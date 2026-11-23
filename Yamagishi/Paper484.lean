/-
論文484『期待値を最大にする賭け方は、確率 1 で破産する』の格上げ（一般の形）。

日本語：等倍配当で勝率 p が 1/2 と 1 のあいだにあるとき、成長率 g(f) = p ln(1 + f) + q ln(1 − f) が
0 に戻る正の点 f₀ はただ一つで、いつもケリーの賭け率 f* = 2p − 1 と min(2f*, 1) のあいだにある。
「2 倍ケリーで成長率 0」には届かず、必ず手前で 0 を割る。配当 2 倍では成り立たない。
English: At even odds with 1/2 < p < 1, the growth rate returns to zero at a unique f₀ with
f* < f₀ < min(2f*, 1), where f* = 2p − 1 is the Kelly fraction; with odds 2 to 1 this fails.

原稿（484_yamagishi_maximising_expectation_goes_bust/…_jp.tex）は、p = 0.6、b = 1 の一点で
f* = 0.2、成長率が 0 に戻る点 0.389391（f* の 1.946953 倍）、二次近似なら 0.4 ちょうど、
全額賭け 50 回の破産確率 1 − p⁵⁰ を数値で示す。

ここで証明した言明（b = 1、1/2 < p < 1、q = 1 − p）：
  (1) `hasDerivAt_g`：g′(f) = (f* − f)/(1 − f²)。`g_strictMonoOn`・`g_strictAntiOn`：g は [0, f*] で
      狭義に増え、[f*, 1) で狭義に減る。`g_pos`：0 < f ≤ f* で g > 0。
  (2) `psi_neg`：0 < x < 1 で ψ(x) = (1 + x/2) ln(1 + x) + (1 − x/2) ln(1 − x) < 0。
      `g_two_fstar`：g(2f*) = ψ(2f*)/2、したがって 2f* < 1 なら g(2f*) < 0。
  (3) `root_exists_unique`：g(f₀) = 0 となる f₀ ∈ (0, 1) はちょうど一つ。
      `root_bounds`：その f₀ は f* < f₀ < min(2f*, 1)。
  (4) `quadratic_root`：二次近似 f*·f − f²/2 の正の根はちょうど 2f*（原稿の観察 3.6）。
      `ruin_tendsto`：全額賭けを n 回続けたときの破産確率 1 − pⁿ は n → ∞ で 1 に近づく。
  (5) `counterexample_b2`：配当 b = 2、p = 0.4 では f* = p − q/b = 0.1 で、g_b(2f*) > 0
      （1.4²·0.8³ = 1.00352 > 1 から）。等倍でない賭けでは「2f* より手前で 0 を割る」は成り立たない。
足した仮定：b = 1（等倍）。b < 1 は扱っていない。
形式化していないもの：比 f₀/f* が p について単調に減ること、b < 1 の場合、横断と時間の平均の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper484

open Real Set Filter Topology

/-- 成長率 g(f) = p ln(1 + f) + (1 − p) ln(1 − f)（等倍配当）。 -/
noncomputable def g (p f : ℝ) : ℝ := p * log (1 + f) + (1 - p) * log (1 - f)

theorem g_zero (p : ℝ) : g p 0 = 0 := by simp [g]

/-- (1) g′(f) = (2p − 1 − f)/(1 − f²)。 -/
theorem hasDerivAt_g (p : ℝ) {f : ℝ} (h1 : -1 < f) (h2 : f < 1) :
    HasDerivAt (g p) ((2 * p - 1 - f) / (1 - f ^ 2)) f := by
  have ha : HasDerivAt (fun f => log (1 + f)) (1 / (1 + f)) f :=
    ((hasDerivAt_id' f).const_add 1).log (by linarith)
  have hb : HasDerivAt (fun f => log (1 - f)) (-1 / (1 - f)) f :=
    ((hasDerivAt_id' f).const_sub 1).log (by linarith)
  have h := (ha.const_mul p).add (hb.const_mul (1 - p))
  have e : g p = fun f => p * log (1 + f) + (1 - p) * log (1 - f) := rfl
  rw [e]
  convert h using 1
  have : (1 : ℝ) + f ≠ 0 := by linarith
  have : (1 : ℝ) - f ≠ 0 := by linarith
  have : (1 : ℝ) - f ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

theorem g_strictMonoOn {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) :
    StrictMonoOn (g p) (Icc 0 (2 * p - 1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro f hf
    exact (hasDerivAt_g p (by linarith [hf.1]) (by linarith [hf.2])).continuousAt.continuousWithinAt
  · intro f hf
    rw [interior_Icc] at hf
    obtain ⟨h0, h1⟩ := hf
    rw [(hasDerivAt_g p (by linarith) (by linarith)).deriv]
    apply div_pos (by linarith)
    nlinarith

theorem g_strictAntiOn {p : ℝ} (hp : 1 / 2 < p) :
    StrictAntiOn (g p) (Ico (2 * p - 1) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico _ _)
  · intro f hf
    exact (hasDerivAt_g p (by linarith [hf.1]) hf.2).continuousAt.continuousWithinAt
  · intro f hf
    rw [interior_Ico] at hf
    obtain ⟨h0, h1⟩ := hf
    rw [(hasDerivAt_g p (by linarith) h1).deriv]
    apply div_neg_of_neg_of_pos (by linarith)
    nlinarith

/-- (1) 0 < f ≤ f* で g > 0。 -/
theorem g_pos {p f : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (h0 : 0 < f) (h1 : f ≤ 2 * p - 1) :
    0 < g p f := by
  have := g_strictMonoOn hp hp1 (left_mem_Icc.mpr (by linarith)) ⟨h0.le, h1⟩ h0
  rwa [g_zero] at this

/-! ### (2) 2f* での成長率 -/

/-- ψ(x) = (1 + x/2) ln(1 + x) + (1 − x/2) ln(1 − x)。 -/
noncomputable def psi (x : ℝ) : ℝ := (1 + x / 2) * log (1 + x) + (1 - x / 2) * log (1 - x)

theorem hasDerivAt_psi {x : ℝ} (h1 : -1 < x) (h2 : x < 1) :
    HasDerivAt psi ((log (1 + x) - log (1 - x)) / 2 - x / (1 - x ^ 2)) x := by
  have ha : HasDerivAt (fun x => log (1 + x)) (1 / (1 + x)) x :=
    ((hasDerivAt_id' x).const_add 1).log (by linarith)
  have hb : HasDerivAt (fun x => log (1 - x)) (-1 / (1 - x)) x :=
    ((hasDerivAt_id' x).const_sub 1).log (by linarith)
  have hc : HasDerivAt (fun x : ℝ => 1 + x / 2) (1 / 2) x := by
    simpa using ((hasDerivAt_id' x).div_const 2).const_add 1
  have hd : HasDerivAt (fun x : ℝ => 1 - x / 2) (-(1 / 2)) x := by
    simpa using ((hasDerivAt_id' x).div_const 2).const_sub 1
  have h := (hc.mul ha).add (hd.mul hb)
  have e : psi = fun x => (1 + x / 2) * log (1 + x) + (1 - x / 2) * log (1 - x) := rfl
  rw [e]
  convert h using 1
  have : (1 : ℝ) + x ≠ 0 := by linarith
  have : (1 : ℝ) - x ≠ 0 := by linarith
  have : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-- 0 < x < 1 で ln((1 + x)/(1 − x)) < 2x/(1 − x²)（2 ln y < y − 1/y から）。 -/
theorem log_ratio_lt {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    log (1 + x) - log (1 - x) < 2 * x / (1 - x ^ 2) := by
  set y := (1 + x) / (1 - x) with hy
  have hy0 : 0 < y := div_pos (by linarith) (by linarith)
  have hy1 : 1 < y := by rw [hy, one_lt_div (by linarith)]; linarith
  have hl : log y = log (1 + x) - log (1 - x) := log_div (by linarith) (by linarith)
  have key := (self_lt_sinh_iff (x := log y)).mpr (log_pos hy1)
  rw [sinh_eq, exp_neg, exp_log hy0] at key
  have e : (y - y⁻¹) / 2 = 2 * x / (1 - x ^ 2) := by
    rw [hy]
    have : (1 : ℝ) - x ≠ 0 := by linarith
    have : (1 : ℝ) + x ≠ 0 := by linarith
    have : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith
    field_simp
    ring
  rw [← hl, ← e]
  exact key

/-- (2) 0 < x < 1 で ψ(x) < 0。 -/
theorem psi_neg {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : psi x < 0 := by
  have hanti : StrictAntiOn psi (Ico 0 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Ico 0 1)
    · intro y hy
      exact (hasDerivAt_psi (by linarith [hy.1]) hy.2).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ico] at hy
      obtain ⟨hy0, hy1⟩ := hy
      rw [(hasDerivAt_psi (by linarith) hy1).deriv]
      have := log_ratio_lt hy0 hy1
      have e : 2 * y / (1 - y ^ 2) / 2 = y / (1 - y ^ 2) := by ring
      linarith [div_lt_div_of_pos_right this (show (0 : ℝ) < 2 by norm_num)]
  have := hanti (left_mem_Ico.mpr (by norm_num)) ⟨h0.le, h1⟩ h0
  have hz : psi 0 = 0 := by simp [psi]
  linarith

/-- (2) g(2f*) = ψ(2f*)/2。 -/
theorem g_two_fstar (p : ℝ) : g p (2 * (2 * p - 1)) = psi (2 * (2 * p - 1)) / 2 := by
  unfold g psi; ring_nf

theorem g_two_fstar_neg {p : ℝ} (hp : 1 / 2 < p) (h2 : 2 * (2 * p - 1) < 1) :
    g p (2 * (2 * p - 1)) < 0 := by
  rw [g_two_fstar]
  have := psi_neg (show 0 < 2 * (2 * p - 1) by linarith) h2
  linarith

/-! ### (3) 0 に戻る点 -/

/-- 1 の近くで g < 0 になる点。 -/
theorem exists_neg {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) :
    ∃ f₁, 0 < f₁ ∧ f₁ < 1 ∧ g p f₁ < 0 := by
  set E := exp (-(p * log 2 / (1 - p)) - 1) with hE
  have hE0 : 0 < E := exp_pos _
  have hE1 : E < 1 := by
    have : 0 ≤ p * log 2 / (1 - p) := div_nonneg (by positivity) (by linarith)
    rw [hE]
    calc exp (-(p * log 2 / (1 - p)) - 1) < exp 0 := exp_lt_exp.mpr (by linarith)
      _ = 1 := exp_zero
  refine ⟨1 - E, by linarith, by linarith, ?_⟩
  unfold g
  rw [show 1 - (1 - E) = E by ring, hE, log_exp]
  have hl : log (1 + (1 - E)) < log 2 := log_lt_log (by linarith) (by linarith)
  have hq : (1 - p) * (-(p * log 2 / (1 - p)) - 1) = -(p * log 2) - (1 - p) := by
    field_simp
  rw [hq]
  nlinarith

/-- (3) 0 に戻る正の点はちょうど一つ。 -/
theorem root_exists_unique {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) :
    ∃! f₀, 0 < f₀ ∧ f₀ < 1 ∧ g p f₀ = 0 := by
  obtain ⟨f₁, h10, h11, hg1⟩ := exists_neg hp hp1
  have hs : 2 * p - 1 < f₁ := by
    by_contra h
    push Not at h
    linarith [g_pos hp hp1 h10 h]
  have hgs := g_pos hp hp1 (by linarith) le_rfl
  have hcont : ContinuousOn (g p) (Icc (2 * p - 1) f₁) := by
    intro f hf
    exact (hasDerivAt_g p (by linarith [hf.1]) (by linarith [hf.2])).continuousAt.continuousWithinAt
  obtain ⟨f₀, hf₀, hroot⟩ := intermediate_value_Ioo' hs.le hcont
    (show (0 : ℝ) ∈ Ioo (g p f₁) (g p (2 * p - 1)) from ⟨hg1, hgs⟩)
  refine ⟨f₀, ⟨by linarith [hf₀.1], by linarith [hf₀.2], hroot⟩, ?_⟩
  rintro f ⟨hf0, hf1, hgf⟩
  have hfs : 2 * p - 1 < f := by
    by_contra h
    push Not at h
    linarith [g_pos hp hp1 hf0 h]
  have hanti := g_strictAntiOn hp
  rcases lt_trichotomy f f₀ with h | h | h
  · have := hanti ⟨hfs.le, hf1⟩ ⟨hf₀.1.le, by linarith [hf₀.2]⟩ h; linarith
  · exact h
  · have := hanti ⟨hf₀.1.le, by linarith [hf₀.2]⟩ ⟨hfs.le, hf1⟩ h; linarith

/-- (3) 0 に戻る点は f* < f₀ < min(2f*, 1)。 -/
theorem root_bounds {p f₀ : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (h0 : 0 < f₀) (h1 : f₀ < 1)
    (hg : g p f₀ = 0) : 2 * p - 1 < f₀ ∧ f₀ < min (2 * (2 * p - 1)) 1 := by
  have hs : 2 * p - 1 < f₀ := by
    by_contra h
    push Not at h
    linarith [g_pos hp hp1 h0 h]
  refine ⟨hs, lt_min ?_ h1⟩
  by_cases h2 : 2 * (2 * p - 1) < 1
  · by_contra hle
    push Not at hle
    have hneg := g_two_fstar_neg hp h2
    rcases lt_or_eq_of_le hle with hlt | heq
    · have := g_strictAntiOn hp ⟨by linarith, h2⟩ ⟨hs.le, h1⟩ hlt
      linarith
    · rw [heq] at hneg; linarith
  · push Not at h2; linarith

/-! ### (4) 二次近似と破産確率 -/

/-- (4) 二次近似 f*·f − f²/2 は f = 2f* で 0。 -/
theorem quadratic_root (s : ℝ) : s * (2 * s) - (2 * s) ^ 2 / 2 = 0 := by ring

/-- (4) 全額賭けを n 回続けたときの破産確率 1 − pⁿ → 1。 -/
theorem ruin_tendsto {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Tendsto (fun n : ℕ => 1 - p ^ n) atTop (𝓝 1) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hp0 hp1).const_sub 1
  simpa using this

/-! ### (5) 等倍でない賭けの反例 -/

/-- 配当 b の成長率 g_b(f) = p ln(1 + bf) + (1 − p) ln(1 − f)。 -/
noncomputable def gb (b p f : ℝ) : ℝ := p * log (1 + b * f) + (1 - p) * log (1 - f)

/-- (5) b = 2、p = 0.4：f* = p − q/b = 0.1 で、g_b(2f*) = g_b(0.2) > 0。 -/
theorem counterexample_b2 : (2 : ℝ) / 5 - (1 - 2 / 5) / 2 = 1 / 10 ∧
    0 < gb 2 (2 / 5) (2 * (1 / 10)) := by
  refine ⟨by norm_num, ?_⟩
  unfold gb
  have h1 : log (7 / 5 : ℝ) * 2 + log (4 / 5) * 3 = log ((7 / 5) ^ 2 * (4 / 5) ^ 3) := by
    rw [log_mul (by norm_num) (by norm_num), log_pow, log_pow]
    push_cast
    ring
  have h2 : 0 < log ((7 / 5 : ℝ) ^ 2 * (4 / 5) ^ 3) := log_pos (by norm_num)
  have e1 : (1 : ℝ) + 2 * (2 * (1 / 10)) = 7 / 5 := by norm_num
  have e2 : (1 : ℝ) - 2 * (1 / 10) = 4 / 5 := by norm_num
  rw [e1, e2]
  linarith

end Paper484

end Yamagishi
