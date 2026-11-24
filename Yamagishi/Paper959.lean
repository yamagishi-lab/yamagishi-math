/-
論文959『減光を受けた星の色の温度は、熱い星ほど低く出て、上限がある』の格上げ（一般の形・論文943 の系）。

日本語の一文：どの二つの波長でも、明るさの比に温度によらない割合 k（0 < k < 1）が掛かると、比から読む
見かけの温度 T′ は本当の温度より低く、T について増え、T′/T は狭義に減り、上限 T_max を超えずにそこへ
近づき、効きによる一次の見積もり exp(ln k/S(T)) はいつも T′/T より低い。
English: For any two wavelengths and any temperature-independent factor 0 < k < 1 on the Planck
ratio R, the apparent temperature T′ defined by R(T′) = kR(T) exists and is unique, T′ < T, T′
increases with T, T′/T decreases strictly, T′ < T_max with R(T_max) = k(λ₂/λ₁)⁴ and T′ → T_max as
T → ∞, and the first-order estimate exp(ln k/S(T)) is strictly below T′/T for every T and k.

原稿（959_yamagishi_a_reddened_stars_color_temperature_reads_lower_the_hotter_and_has_a_ceiling/
…_jp.tex）は、440 nm と 550 nm、A₅₅₀ = 0.1・0.3・1.0 等（1/λ の形）と五つの温度の 15 通りを二分法で解き、
一次の見積もりとの比べと三つの上限 146755.189・51795.827・17921.911 K を数値で出している。
上限の理由は観察 4.1 で一般に書いているが、単調性と一次との大小は 15 通りの数だけ。

ここで証明した言明（0 < b < a は論文943 と同じ a = c₂/λ₁、b = c₂/λ₂、0 < k < 1）：
  (1) `apparent_exists_unique`：T > 0 ごとに R(T′) = kR(T) をみたす T′ > 0 がただ一つ在る。
      `apparent_lt`：T′ < T。`apparent_strictMono`：T₁ < T₂ なら T₁′ < T₂′。
  (2) `ratio_strictAnti`：T₁ < T₂ なら T₂′/T₂ < T₁′/T₁（ln R を ln T の関数として見たとき、
      その傾き S が減ること、つまり論文943 の `S_strictAntiOn` から）。
  (3) `ceiling_exists_unique`：R(T_max) = k(a/b)⁴ をみたす T_max > 0 がただ一つ在る。
      `apparent_lt_ceiling`：T′ < T_max。`apparent_tendsto`：T → ∞ で T′ → T_max。
  (4) `first_order_lt`：exp(ln k/S(T)) < T′/T（一次の見積もりはいつも低く出る）。平均値の定理で
      ln R(T) − ln R(T′) = S(ξ)·ln(T/T′)、ξ < T なので S(ξ) > S(T)。
  (5) `factor_lt_one`：色の超過 E > 0 なら k = 10^(−0.4E) は 0 と 1 のあいだ（A_λ₁ > A_λ₂ なら減光の形によらない）。
足した仮定：黒体の比 R と効き S は論文943 の定義をそのまま使った。減光は比に温度によらない割合 k を
掛けるとした（原稿の置き方）。
注意：k > 1（長い波長の側がより強く減る）では kR(T) が (a/b)⁴ を超える温度で T′ が無くなる。ここでは
0 < k < 1 だけを扱った。
形式化していないもの：原稿の 15 通りの数値と三つの上限の数値、減光の形 1/λ の値、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib
import Yamagishi.Paper943

namespace Yamagishi

namespace Paper959

open Real Set Filter Topology Paper943

variable {a b k : ℝ}

/-- ln R を ln T の関数として見たもの f(u) = ln R(e^u)。 -/
noncomputable def f (a b u : ℝ) : ℝ := log (R a b (exp u))

theorem R_continuousOn (ha : 0 < a) : ContinuousOn (R a b) (Ioi 0) := by
  have hn : ∀ c : ℝ, ContinuousOn (fun T : ℝ => exp (c / T) - 1) (Ioi 0) := fun c =>
    ((continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt hx)).rexp).sub
      continuousOn_const
  show ContinuousOn (fun T => (a / b) ^ 5 * ((exp (b / T) - 1) / (exp (a / T) - 1))) (Ioi 0)
  exact continuousOn_const.mul ((hn b).div (hn a)
    (fun x hx => ne_of_gt (expm1_pos (div_pos ha hx))))

/-- R(T) が値 y（0 < y < (a/b)⁴）をとる T > 0 はただ一つ。 -/
theorem R_hits (ha : 0 < a) (hb : 0 < b) (hab : b < a) {y : ℝ} (hy : 0 < y)
    (hy' : y < (a / b) ^ 4) : ∃! T, 0 < T ∧ R a b T = y := by
  -- 下の端：R → 0
  obtain ⟨T₀, hT₀, hR₀⟩ : ∃ T₀, 0 < T₀ ∧ R a b T₀ < y := by
    have := (R_tendsto_zero ha hb hab).eventually (gt_mem_nhds hy)
    obtain ⟨T₀, hT₀⟩ := (this.and self_mem_nhdsWithin).exists
    exact ⟨T₀, hT₀.2, hT₀.1⟩
  -- 上の端：R → (a/b)⁴
  obtain ⟨T₁, hT₁, hR₁⟩ : ∃ T₁, T₀ < T₁ ∧ y < R a b T₁ := by
    have := ((R_tendsto_atTop ha hb).eventually (lt_mem_nhds hy')).and (eventually_gt_atTop T₀)
    obtain ⟨T₁, h1, h2⟩ := this.exists
    exact ⟨T₁, h2, h1⟩
  have hcont : ContinuousOn (R a b) (Icc T₀ T₁) :=
    (R_continuousOn ha).mono (fun t ht => lt_of_lt_of_le hT₀ ht.1)
  obtain ⟨T, hTI, hRT⟩ := intermediate_value_Ioo hT₁.le hcont ⟨hR₀, hR₁⟩
  refine ⟨T, ⟨hT₀.trans hTI.1, hRT⟩, ?_⟩
  rintro T' ⟨hT', hRT'⟩
  exact (R_strictMonoOn ha hb hab).injOn hT' (hT₀.trans hTI.1) (hRT'.trans hRT.symm)

/-- (1) 見かけの温度はただ一つ在る。 -/
theorem apparent_exists_unique (ha : 0 < a) (hb : 0 < b) (hab : b < a) (hk : 0 < k)
    (hk1 : k < 1) {T : ℝ} (hT : 0 < T) : ∃! T', 0 < T' ∧ R a b T' = k * R a b T := by
  have hR := R_pos ha hb hT
  apply R_hits ha hb hab (by positivity)
  calc k * R a b T < 1 * R a b T := mul_lt_mul_of_pos_right hk1 hR
    _ = R a b T := one_mul _
    _ < (a / b) ^ 4 := R_lt_limit ha hb hab hT

/-- (1) T′ < T。 -/
theorem apparent_lt (ha : 0 < a) (hb : 0 < b) (hab : b < a) (hk1 : k < 1) {T T' : ℝ}
    (hT : 0 < T) (hT' : 0 < T') (h : R a b T' = k * R a b T) : T' < T := by
  have hR := R_pos ha hb hT
  have : R a b T' < R a b T := by rw [h]; nlinarith
  exact (R_strictMonoOn ha hb hab).lt_iff_lt hT' hT |>.mp this

/-- (1) 見かけの温度は本当の温度について狭義に増える。 -/
theorem apparent_strictMono (ha : 0 < a) (hb : 0 < b) (hab : b < a) (hk : 0 < k)
    {T₁ T₂ T₁' T₂' : ℝ} (h₁ : 0 < T₁) (h₂ : 0 < T₂) (h₁' : 0 < T₁') (h₂' : 0 < T₂')
    (e₁ : R a b T₁' = k * R a b T₁) (e₂ : R a b T₂' = k * R a b T₂) (hT : T₁ < T₂) :
    T₁' < T₂' := by
  have hmono := R_strictMonoOn ha hb hab
  have : R a b T₁' < R a b T₂' := by
    rw [e₁, e₂]; exact mul_lt_mul_of_pos_left (hmono h₁ h₂ hT) hk
  exact hmono.lt_iff_lt h₁' h₂' |>.mp this

/-- f′(u) = S(e^u)。 -/
theorem hasDerivAt_f (ha : 0 < a) (hb : 0 < b) (u : ℝ) : HasDerivAt (f a b) (S a b (exp u)) u :=
  hasDerivAt_logR ha hb u

/-- 固定した幅 h > 0 について u ↦ f(u) − f(u − h) は狭義に減る（f′ = S∘exp が減るため）。 -/
theorem increment_strictAnti (ha : 0 < a) (hb : 0 < b) (hab : b < a) {h : ℝ} (hh : 0 < h) :
    StrictAnti (fun u => f a b u - f a b (u - h)) := by
  apply strictAnti_of_deriv_neg
  intro u
  have h1 := hasDerivAt_f ha hb u
  have h2 := (hasDerivAt_f ha hb (u - h)).comp u ((hasDerivAt_id' u).sub_const h)
  have h3 : HasDerivAt (fun u => f a b u - f a b (u - h))
      (S a b (exp u) - S a b (exp (u - h)) * 1) u := h1.sub h2
  rw [h3.deriv, mul_one]
  have : S a b (exp u) < S a b (exp (u - h)) :=
    S_strictAntiOn ha hb hab (exp_pos _) (exp_pos _) (exp_lt_exp.mpr (by linarith))
  linarith

theorem f_strictMono (ha : 0 < a) (hb : 0 < b) (hab : b < a) : StrictMono (f a b) := by
  apply strictMono_of_deriv_pos
  intro u
  rw [(hasDerivAt_f ha hb u).deriv]
  exact S_pos ha hb hab (exp_pos u)

/-- R(T′) = kR(T) を ln で書くと f(ln T) − f(ln T′) = −ln k。 -/
theorem log_relation (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) {T T' : ℝ} (hT : 0 < T)
    (hT' : 0 < T') (h : R a b T' = k * R a b T) : f a b (log T) - f a b (log T') = -log k := by
  unfold f
  rw [exp_log hT, exp_log hT', h, log_mul (ne_of_gt hk) (ne_of_gt (R_pos ha hb hT))]
  ring

/-- (2) T′/T は T について狭義に減る。 -/
theorem ratio_strictAnti (ha : 0 < a) (hb : 0 < b) (hab : b < a) (hk : 0 < k) (hk1 : k < 1)
    {T₁ T₂ T₁' T₂' : ℝ} (h₁ : 0 < T₁) (h₂ : 0 < T₂) (h₁' : 0 < T₁') (h₂' : 0 < T₂')
    (e₁ : R a b T₁' = k * R a b T₁) (e₂ : R a b T₂' = k * R a b T₂) (hT : T₁ < T₂) :
    T₂' / T₂ < T₁' / T₁ := by
  set u₁ := log T₁
  set u₂ := log T₂
  set Δ₁ := log T₁ - log T₁'
  set Δ₂ := log T₂ - log T₂'
  have hl₁ := log_relation ha hb hk h₁ h₁' e₁
  have hl₂ := log_relation ha hb hk h₂ h₂' e₂
  have hΔ₁ : 0 < Δ₁ := by
    have := apparent_lt ha hb hab hk1 h₁ h₁' e₁
    simp only [Δ₁]; linarith [log_lt_log h₁' this]
  have hu : u₁ < u₂ := log_lt_log h₁ hT
  -- Δ₁ < Δ₂ を示す
  have key : Δ₁ < Δ₂ := by
    by_contra hc
    push Not at hc
    have s1 : f a b u₂ - f a b (u₂ - Δ₂) ≤ f a b u₂ - f a b (u₂ - Δ₁) := by
      have := (f_strictMono ha hb hab).monotone (show u₂ - Δ₁ ≤ u₂ - Δ₂ by linarith)
      linarith
    have s2 := increment_strictAnti ha hb hab hΔ₁ hu
    simp only at s2
    have e1 : u₁ - Δ₁ = log T₁' := by simp only [u₁, Δ₁]; ring
    have e2 : u₂ - Δ₂ = log T₂' := by simp only [u₂, Δ₂]; ring
    rw [e1] at s2
    rw [e2] at s1
    linarith
  have r₁ : T₁' / T₁ = exp (-Δ₁) := by
    simp only [Δ₁]; rw [neg_sub, exp_sub, exp_log h₁', exp_log h₁]
  have r₂ : T₂' / T₂ = exp (-Δ₂) := by
    simp only [Δ₂]; rw [neg_sub, exp_sub, exp_log h₂', exp_log h₂]
  rw [r₁, r₂]
  exact exp_lt_exp.mpr (by linarith)

/-- (3) 上限 T_max：R(T_max) = k(a/b)⁴ をみたす T_max > 0 はただ一つ。 -/
theorem ceiling_exists_unique (ha : 0 < a) (hb : 0 < b) (hab : b < a) (hk : 0 < k)
    (hk1 : k < 1) : ∃! Tm, 0 < Tm ∧ R a b Tm = k * (a / b) ^ 4 := by
  apply R_hits ha hb hab (by positivity)
  have : 0 < (a / b) ^ 4 := by positivity
  nlinarith

/-- (3) T′ < T_max。 -/
theorem apparent_lt_ceiling (ha : 0 < a) (hb : 0 < b) (hab : b < a) (hk : 0 < k)
    {T T' Tm : ℝ} (hT : 0 < T) (hT' : 0 < T') (hTm : 0 < Tm) (h : R a b T' = k * R a b T)
    (hm : R a b Tm = k * (a / b) ^ 4) : T' < Tm := by
  have : R a b T' < R a b Tm := by
    rw [h, hm]; exact mul_lt_mul_of_pos_left (R_lt_limit ha hb hab hT) hk
  exact (R_strictMonoOn ha hb hab).lt_iff_lt hT' hTm |>.mp this

/-- 見かけの温度を関数として取り出す（T ≤ 0 では 0）。 -/
noncomputable def Tapp (a b k T : ℝ) : ℝ :=
  if h : 0 < a ∧ 0 < b ∧ b < a ∧ 0 < k ∧ k < 1 ∧ 0 < T then
    (apparent_exists_unique h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2).exists.choose
  else 0

theorem Tapp_spec (ha : 0 < a) (hb : 0 < b) (hab : b < a) (hk : 0 < k) (hk1 : k < 1) {T : ℝ}
    (hT : 0 < T) : 0 < Tapp a b k T ∧ R a b (Tapp a b k T) = k * R a b T := by
  have h : 0 < a ∧ 0 < b ∧ b < a ∧ 0 < k ∧ k < 1 ∧ 0 < T := ⟨ha, hb, hab, hk, hk1, hT⟩
  unfold Tapp
  simp only [h, and_self, ↓reduceDIte]
  exact (apparent_exists_unique ha hb hab hk hk1 hT).exists.choose_spec

/-- (3) T → ∞ で T′ → T_max。 -/
theorem apparent_tendsto (ha : 0 < a) (hb : 0 < b) (hab : b < a) (hk : 0 < k) (hk1 : k < 1)
    {Tm : ℝ} (hTm : 0 < Tm) (hm : R a b Tm = k * (a / b) ^ 4) :
    Tendsto (Tapp a b k) atTop (𝓝 Tm) := by
  rw [tendsto_order]
  constructor
  · intro l hl
    rcases le_or_gt l 0 with hl0 | hl0
    · filter_upwards [eventually_gt_atTop 0] with T hT
      exact lt_of_le_of_lt hl0 (Tapp_spec ha hb hab hk hk1 hT).1
    · have hRl : R a b l < k * (a / b) ^ 4 := by
        rw [← hm]; exact R_strictMonoOn ha hb hab hl0 hTm hl
      have hlim : Tendsto (fun T => k * R a b T) atTop (𝓝 (k * (a / b) ^ 4)) :=
        (R_tendsto_atTop ha hb).const_mul k
      filter_upwards [hlim.eventually (lt_mem_nhds hRl), eventually_gt_atTop 0] with T h1 hT
      obtain ⟨hpos, hspec⟩ := Tapp_spec ha hb hab hk hk1 hT
      rw [← hspec] at h1
      exact (R_strictMonoOn ha hb hab).lt_iff_lt hl0 hpos |>.mp h1
  · intro u hu
    filter_upwards [eventually_gt_atTop 0] with T hT
    obtain ⟨hpos, hspec⟩ := Tapp_spec ha hb hab hk hk1 hT
    exact lt_trans (apparent_lt_ceiling ha hb hab hk hT hpos hTm hspec hm) hu

/-- (4) 一次の見積もり exp(ln k/S(T)) は T′/T より真に小さい。 -/
theorem first_order_lt (ha : 0 < a) (hb : 0 < b) (hab : b < a) (hk : 0 < k) (hk1 : k < 1)
    {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (h : R a b T' = k * R a b T) :
    exp (log k / S a b T) < T' / T := by
  have hlt := apparent_lt ha hb hab hk1 hT hT' h
  have hlog : log T' < log T := log_lt_log hT' hlt
  have hrel := log_relation ha hb hk hT hT' h
  -- 平均値の定理
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope (f a b) (fun u => S a b (exp u)) hlog
    (continuous_iff_continuousAt.mpr (fun u => (hasDerivAt_f ha hb u).continuousAt)).continuousOn
    (fun u _ => hasDerivAt_f ha hb u)
  have hS : S a b T < S a b (exp ξ) := by
    have : exp ξ < T := by rw [← exp_log hT]; exact exp_lt_exp.mpr hξ.2
    exact S_strictAntiOn ha hb hab (exp_pos ξ) hT this
  have hST := S_pos ha hb hab hT
  set Δ := log T - log T'
  have hΔ : 0 < Δ := by simp only [Δ]; linarith
  have hK : -log k = S a b (exp ξ) * Δ := by
    rw [← hrel, hξd]; simp only [Δ]; field_simp
  have hratio : T' / T = exp (-Δ) := by
    simp only [Δ]; rw [neg_sub, exp_sub, exp_log hT', exp_log hT]
  rw [hratio]
  apply exp_lt_exp.mpr
  rw [div_lt_iff₀ hST]
  nlinarith

/-- (5) 色の超過 E > 0 なら比に掛かる割合 k = 10^(−0.4E) は 0 と 1 のあいだ。 -/
theorem factor_lt_one {E : ℝ} (hE : 0 < E) :
    0 < (10 : ℝ) ^ (-(0.4 * E)) ∧ (10 : ℝ) ^ (-(0.4 * E)) < 1 := by
  constructor
  · positivity
  · apply rpow_lt_one_of_one_lt_of_neg (by norm_num)
    nlinarith

end Paper959

end Yamagishi
