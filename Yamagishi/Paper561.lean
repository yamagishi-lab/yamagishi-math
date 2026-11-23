/-
論文561『重ねを倍にしても、耐力は 1 パーセントも増えない』の格上げ（一般の形）。

日本語：フォルケルセンの解で、重ね継手の耐力は重ね長さについて増え、凹で、上限 2τ_a b/ω には
届かない。重ねを倍にしたときの耐力の比は 2/(1 + tanh²(ωL/2)) で、1 と 2 のあいだにあり、
長さとともに狭義に減る。
English: Under Volkersen's solution the joint strength increases and is strictly concave in the
overlap, never reaching 2τ_a b/ω; doubling the overlap multiplies it by 2/(1 + tanh²(ωL/2)),
which lies in (1, 2) and decreases strictly with the overlap.

原稿（561_yamagishi_doubling_the_overlap_adds_nothing/…_jp.tex）は、τ_max/τ̄ = u coth u
（u = ωL/2）を置き、アルミ板・接着層の一組で、重ね 5〜80 mm の尖りと耐力、倍の比四つ
（1.491669 から 1.000046）、上限 2/ω = 7.483315 mm 相当を数値で出す。

ここで証明した言明（τ_a b > 0、ω > 0。尖りの式 u coth u はフォルケルセンの解として定義に置いた）：
  (1) `load_eq`：最大せん断が τ_a で壊れるとき、耐力 τ_a b L/(u coth u) は P(L) = τ_a b (2/ω) tanh(ωL/2)。
      `peak_gt_one`：尖り u coth u は u > 0 で 1 より大きい（せん断は一様でない）。
  (2) `load_strictMono`：P は L について狭義に増える。`load_strictConcaveOn`：L ≥ 0 で狭義に凹。
      `load_lt_ceiling`：P < 2τ_a b/ω。`load_tendsto`：L → ∞ で P → 2τ_a b/ω。
      `load_fraction`：上限への到達割合は tanh(ωL/2)。
  (3) `double_ratio`：P(2L)/P(L) = 2/(1 + tanh²(ωL/2))（tanh の二倍角の式）。
      `double_ratio_bounds`：1 < P(2L)/P(L) < 2。`double_ratio_strictAntiOn`：L について狭義に減る。
      `double_ratio_lt_iff`：比が 1.01 より小さい ⇔ tanh²(ωL/2) > 99/101。
足した仮定：フォルケルセンの模型（せん断のみ・弾性の接着層・同じ二枚の板）と、最大せん断で壊れる
という基準（原稿と同じ）。
形式化していないもの：u coth u をせん断遅れの微分方程式から出す所、はく離と曲げ、接着剤の降伏、
接着層の厚みの表、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper561

open Real Set Filter Topology

/-! ### tanh の性質 -/

theorem tanh_strictMono' : StrictMono tanh := by
  intro x y h
  by_contra hle
  push Not at hle
  have := artanh_le_artanh (neg_one_lt_tanh y) (tanh_lt_one x) hle
  rw [artanh_tanh, artanh_tanh] at this
  linarith

theorem tanh_pos' {u : ℝ} (hu : 0 < u) : 0 < tanh u := by
  have := tanh_strictMono' hu; rwa [tanh_zero] at this

/-- u > 0 で tanh u < u（artanh y ≥ y + y³/3 から）。 -/
theorem tanh_lt_self {u : ℝ} (hu : 0 < u) : tanh u < u := by
  have h0 := tanh_pos' hu
  have h1 := tanh_lt_one u
  have := sum_range_le_artanh h0.le h1 2
  rw [artanh_tanh] at this
  simp [Finset.sum_range_succ] at this
  nlinarith [pow_pos h0 3]

/-- tanh の二倍角の式。 -/
theorem tanh_two_mul' (u : ℝ) : tanh (2 * u) = 2 * tanh u / (1 + tanh u ^ 2) := by
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, sinh_two_mul, cosh_two_mul]
  have hc : 0 < cosh u := cosh_pos u
  field_simp

theorem hasDerivAt_tanh' (x : ℝ) : HasDerivAt tanh (1 / cosh x ^ 2) x := by
  have h := (hasDerivAt_sinh x).div (hasDerivAt_cosh x) (cosh_pos x).ne'
  have e : tanh = fun y => sinh y / cosh y := by funext y; exact tanh_eq_sinh_div_cosh y
  rw [e]
  convert h using 1
  rw [show cosh x * cosh x - sinh x * sinh x = 1 by nlinarith [cosh_sq x]]

theorem tendsto_tanh_atTop : Tendsto tanh atTop (𝓝 1) := by
  have e : ∀ x, tanh x = (1 - exp (-(2 * x))) / (1 + exp (-(2 * x))) := by
    intro x
    rw [tanh_eq]
    have h1 : exp x - exp (-x) = exp x * (1 - exp (-(2 * x))) := by
      rw [mul_sub, ← exp_add]; ring_nf
    have h2 : exp x + exp (-x) = exp x * (1 + exp (-(2 * x))) := by
      rw [mul_add, ← exp_add]; ring_nf
    rw [h1, h2, mul_div_mul_left _ _ (exp_pos x).ne']
  have h : Tendsto (fun x : ℝ => exp (-(2 * x))) atTop (𝓝 0) := by
    apply tendsto_exp_atBot.comp
    exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by norm_num))
  have := (h.const_sub 1).div (h.const_add 1) (by norm_num)
  simp only [sub_zero, add_zero, div_one] at this
  exact this.congr (fun x => (e x).symm)

/-! ### (1) 模型 -/

/-- 尖り τ_max/τ̄ = u coth u（フォルケルセンの解。模型の式として置く）。 -/
noncomputable def peak (u : ℝ) : ℝ := u * (cosh u / sinh u)

/-- 耐力 P(L) = τ_a b (2/ω) tanh(ωL/2)。 -/
noncomputable def load (τa b ω L : ℝ) : ℝ := τa * b * (2 / ω) * tanh (ω * L / 2)

/-- (1) 最大せん断が τ_a に達して壊れるとき、平均 τ̄ = τ_a/(u coth u)、耐力 τ̄ b L は P(L)。 -/
theorem load_eq {τa b ω L : ℝ} (hω : 0 < ω) (hL : 0 < L) :
    τa * b * L / peak (ω * L / 2) = load τa b ω L := by
  unfold peak load
  have hu : 0 < ω * L / 2 := by positivity
  have hs : 0 < sinh (ω * L / 2) := sinh_pos_iff.mpr hu
  have hc : 0 < cosh (ω * L / 2) := cosh_pos _
  rw [tanh_eq_sinh_div_cosh]
  field_simp

/-- (1) u > 0 で尖りは 1 より大きい。 -/
theorem peak_gt_one {u : ℝ} (hu : 0 < u) : 1 < peak u := by
  unfold peak
  have hs : 0 < sinh u := sinh_pos_iff.mpr hu
  have hc : 0 < cosh u := cosh_pos u
  have ht := tanh_lt_self hu
  rw [tanh_eq_sinh_div_cosh, div_lt_iff₀ hc] at ht
  rw [mul_div_assoc', lt_div_iff₀ hs]
  linarith

/-! ### (2) 耐力の形 -/

theorem load_strictMono {τa b ω : ℝ} (hK : 0 < τa * b) (hω : 0 < ω) :
    StrictMono (load τa b ω) := by
  intro L₁ L₂ h
  unfold load
  have : tanh (ω * L₁ / 2) < tanh (ω * L₂ / 2) := tanh_strictMono' (by nlinarith)
  have hK' : 0 < τa * b * (2 / ω) := by positivity
  nlinarith

theorem load_lt_ceiling {τa b ω : ℝ} (hK : 0 < τa * b) (hω : 0 < ω) (L : ℝ) :
    load τa b ω L < τa * b * (2 / ω) := by
  unfold load
  have hK' : 0 < τa * b * (2 / ω) := by positivity
  have := tanh_lt_one (ω * L / 2)
  nlinarith

theorem load_fraction {τa b ω : ℝ} (hK : 0 < τa * b) (hω : 0 < ω) (L : ℝ) :
    load τa b ω L / (τa * b * (2 / ω)) = tanh (ω * L / 2) := by
  unfold load
  have hK' : 0 < τa * b * (2 / ω) := by positivity
  rw [mul_comm, mul_div_assoc, div_self hK'.ne', mul_one]

theorem load_tendsto {τa b ω : ℝ} (hω : 0 < ω) :
    Tendsto (load τa b ω) atTop (𝓝 (τa * b * (2 / ω))) := by
  have h : Tendsto (fun L : ℝ => ω * L / 2) atTop atTop := by
    have := tendsto_id.const_mul_atTop hω
    exact this.atTop_div_const (by norm_num)
  have := (tendsto_tanh_atTop.comp h).const_mul (τa * b * (2 / ω))
  rw [mul_one] at this
  exact this

/-- (2) L ≥ 0 で狭義に凹。 -/
theorem load_strictConcaveOn {τa b ω : ℝ} (hK : 0 < τa * b) (hω : 0 < ω) :
    StrictConcaveOn ℝ (Ici 0) (load τa b ω) := by
  have hd : ∀ L, HasDerivAt (load τa b ω)
      (τa * b * (2 / ω) * (1 / cosh (ω * L / 2) ^ 2 * (ω / 2))) L := by
    intro L
    have h1 : HasDerivAt (fun L : ℝ => ω * L / 2) (ω / 2) L := by
      have := ((hasDerivAt_id' L).const_mul ω).div_const 2
      simpa using this
    exact ((hasDerivAt_tanh' (ω * L / 2)).comp L h1).const_mul (τa * b * (2 / ω))
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0)
  · exact (fun L _ => (hd L).continuousAt.continuousWithinAt)
  · intro L₁ h₁ L₂ h₂ h12
    rw [interior_Ici, mem_Ioi] at h₁ h₂
    rw [(hd L₁).deriv, (hd L₂).deriv]
    have hK' : 0 < τa * b * (2 / ω) := by positivity
    have hc : cosh (ω * L₁ / 2) < cosh (ω * L₂ / 2) :=
      cosh_strictMonoOn (mem_Ici.mpr (by positivity)) (mem_Ici.mpr (by positivity))
        (by nlinarith)
    have hc1 : 0 < cosh (ω * L₁ / 2) := cosh_pos _
    have hsq : cosh (ω * L₁ / 2) ^ 2 < cosh (ω * L₂ / 2) ^ 2 := by nlinarith
    have : 1 / cosh (ω * L₂ / 2) ^ 2 < 1 / cosh (ω * L₁ / 2) ^ 2 :=
      one_div_lt_one_div_of_lt (by positivity) hsq
    have hw : 0 < ω / 2 := by positivity
    have := mul_lt_mul_of_pos_right this hw
    exact mul_lt_mul_of_pos_left this hK'

/-! ### (3) 倍にしたときの比 -/

/-- (3) P(2L)/P(L) = 2/(1 + tanh²(ωL/2))。 -/
theorem double_ratio {τa b ω L : ℝ} (hK : 0 < τa * b) (hω : 0 < ω) (hL : 0 < L) :
    load τa b ω (2 * L) / load τa b ω L = 2 / (1 + tanh (ω * L / 2) ^ 2) := by
  unfold load
  have ht := tanh_pos' (show 0 < ω * L / 2 by positivity)
  have hK' : 0 < τa * b * (2 / ω) := by positivity
  rw [show ω * (2 * L) / 2 = 2 * (ω * L / 2) by ring, tanh_two_mul', mul_div_mul_left _ _ hK'.ne']
  field_simp

theorem double_ratio_bounds {τa b ω L : ℝ} (hK : 0 < τa * b) (hω : 0 < ω) (hL : 0 < L) :
    1 < load τa b ω (2 * L) / load τa b ω L ∧ load τa b ω (2 * L) / load τa b ω L < 2 := by
  rw [double_ratio hK hω hL]
  have ht := tanh_pos' (show 0 < ω * L / 2 by positivity)
  have ht1 := tanh_lt_one (ω * L / 2)
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- (3) 比は L について狭義に減る。 -/
theorem double_ratio_strictAntiOn {τa b ω : ℝ} (hK : 0 < τa * b) (hω : 0 < ω) :
    StrictAntiOn (fun L => load τa b ω (2 * L) / load τa b ω L) (Ioi 0) := by
  intro L₁ h₁ L₂ h₂ h12
  rw [mem_Ioi] at h₁ h₂
  simp only [double_ratio hK hω h₁, double_ratio hK hω h₂]
  have ht1 := tanh_pos' (show 0 < ω * L₁ / 2 by positivity)
  have ht := tanh_strictMono' (show ω * L₁ / 2 < ω * L₂ / 2 by nlinarith)
  apply div_lt_div_of_pos_left (by norm_num) (by positivity)
  nlinarith

/-- (3) 比が 1.01 より小さい ⇔ tanh²(ωL/2) > 99/101。 -/
theorem double_ratio_lt_iff {τa b ω L : ℝ} (hK : 0 < τa * b) (hω : 0 < ω) (hL : 0 < L) :
    load τa b ω (2 * L) / load τa b ω L < 101 / 100 ↔ 99 / 101 < tanh (ω * L / 2) ^ 2 := by
  rw [double_ratio hK hω hL, div_lt_div_iff₀ (by positivity) (by norm_num)]
  constructor <;> intro h <;> linarith

end Paper561

end Yamagishi
