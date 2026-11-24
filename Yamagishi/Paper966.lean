/-
論文966『細胞は同じ倍率の濃さの違いでも、縮むほうが膨らむより速く落ち着く』の格上げ（一般の形）。

日本語の一文：膜の面積を一定とした水の出入りの模型で、外を 1/q 倍にして膨らむ時間と q 倍にして縮む
時間の比は、浸透で動かない体積の割合 b によらず閉じた式で書け、変化の割合 p とともに q² から q⁴ へ
狭義に増える。
English: In the constant-area osmotic model dx/dt = (1 − b)/(x − b) − r, x(0) = 1, the time to cover
a fraction p of the way to equilibrium is (1 − b)(L + p(r − 1))/r² with L = −ln(1 − p); the swelling
(r = 1/q) to shrinking (r = q) time ratio is q³(qL − (q − 1)p)/(L + (q − 1)p) for every b, it
increases strictly in p, and q² < ratio < q⁴ with limits q² (p → 0) and q⁴ (p → 1).

原稿（966_yamagishi_a_cell_settles_faster_when_it_shrinks_than_when_it_swells/…_jp.tex）は、
b = 0.4、q = 2・1.5・1.25 で、変化の半分・90%・99% に届く時間の比を数値の積分で出し
（倍率 2 で 5.941899・9.255412・11.753247）、そばの速さ r²/(1 − b) とその比 q⁴ を一般の式で書く。
時間の比の閉じた式と、b によらないこと、上下の限界は示していない。

ここで証明した言明（b < 1、r > 0、r ≠ 1。原稿の 0 ≤ b < 1 より広い）：
  (1) `hasDerivAt_tm`：時間の式 t(x) = (1 − x)/r + ((1 − b)/r²)·ln((1 − x∞)/(x − x∞))
      （x∞ = b + (1 − b)/r）は dt/dx = 1/F(x)、F(x) = (1 − b)/(x − b) − r をみたす。
      `time_along_solution`：x(0) = 1 から dx/dt = F(x) に従う解が [0, T] で x∞ に触れず
      b より大きいなら、t(x(T)) = T（解が x に届く時刻は t(x) だけ）。
  (2) `time_to_fraction`：変化の割合 p（0 ≤ p < 1）に届く時刻は (1 − b)(L + p(r − 1))/r²、L = −ln(1 − p)。
  (3) `ratio_eq`：膨らむ（r = 1/q）時間 ÷ 縮む（r = q）時間 = q³(qL − (q − 1)p)/(L + (q − 1)p)。b は入らない。
  (4) `ratio_bounds`：q > 1、0 < p < 1 で q² < 比 < q⁴（左は p < −ln(1 − p) から）。
      `ratio_strictMono`：比は p について狭義に増える。
      `ratio_tendsto_zero`・`ratio_tendsto_one`：p → 0 で q²、p → 1 で q⁴ に近づく。
  (5) `near_rate`：落ち着く体積のそばの速さ −F′(x∞) = r²/(1 − b)。`near_rate_ratio`：縮む ÷ 膨らむ = q⁴。
  (6) `paper_half`：q = 2、p = 1/2 の閉じた値は 5.9425 と 5.9426 のあいだ（原稿の数値の積分は 5.941899 で、
      四桁目で違う。下読みの AI の指摘を機械で確かめた）。
足した仮定：水の出入りの式 dx/dt = (1 − b)/(x − b) − r（膜の面積一定、時間は原稿の単位）を定義として置いた。
形式化していないもの：面積を x^(2/3) とした場合（そのときは比が b による）、数表の数値の積分、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper966

open Real Set Filter Topology

/-- 水の出入りの右辺 F(x) = (1 − b)/(x − b) − r。 -/
noncomputable def F (b r x : ℝ) : ℝ := (1 - b) / (x - b) - r

/-- 落ち着く体積 x∞ = b + (1 − b)/r。 -/
noncomputable def xinf (b r : ℝ) : ℝ := b + (1 - b) / r

/-- x(0) = 1 から体積 x に届く時刻の式。 -/
noncomputable def tm (b r x : ℝ) : ℝ :=
  (1 - x) / r + (1 - b) / r ^ 2 * log ((1 - xinf b r) / (x - xinf b r))

theorem one_sub_xinf {b r : ℝ} (hr : r ≠ 0) : 1 - xinf b r = (1 - b) * (r - 1) / r := by
  unfold xinf; field_simp; ring

theorem one_sub_xinf_ne {b r : ℝ} (hb : b < 1) (hr : 0 < r) (hr1 : r ≠ 1) : 1 - xinf b r ≠ 0 := by
  rw [one_sub_xinf (ne_of_gt hr)]
  have : r - 1 ≠ 0 := sub_ne_zero.mpr hr1
  have : 1 - b ≠ 0 := by linarith
  have : r ≠ 0 := ne_of_gt hr
  positivity

/-- F の別の形：F(x) = −r(x − x∞)/(x − b)。 -/
theorem F_eq {b r x : ℝ} (hr : r ≠ 0) (hxb : x ≠ b) :
    F b r x = -(r * (x - xinf b r)) / (x - b) := by
  unfold F xinf
  have : x - b ≠ 0 := sub_ne_zero.mpr hxb
  field_simp
  ring

theorem F_ne {b r x : ℝ} (hr : 0 < r) (hx : x ≠ xinf b r) (hxb : x ≠ b) : F b r x ≠ 0 := by
  rw [F_eq (ne_of_gt hr) hxb]
  have : x - xinf b r ≠ 0 := sub_ne_zero.mpr hx
  have : x - b ≠ 0 := sub_ne_zero.mpr hxb
  have : r ≠ 0 := ne_of_gt hr
  have : -(r * (x - xinf b r)) ≠ 0 := by
    apply neg_ne_zero.mpr; positivity
  positivity

/-- (1) 時間の式の微分は 1/F。 -/
theorem hasDerivAt_tm {b r x : ℝ} (hb : b < 1) (hr : 0 < r) (hr1 : r ≠ 1) (hx : x ≠ xinf b r)
    (hxb : x ≠ b) : HasDerivAt (tm b r) (1 / F b r x) x := by
  have hc := one_sub_xinf_ne hb hr hr1
  have hxi : x - xinf b r ≠ 0 := sub_ne_zero.mpr hx
  have hq : HasDerivAt (fun y => (1 - xinf b r) / (y - xinf b r))
      ((0 * (x - xinf b r) - (1 - xinf b r) * 1) / (x - xinf b r) ^ 2) x :=
    (hasDerivAt_const x (1 - xinf b r)).div ((hasDerivAt_id x).sub_const (xinf b r)) hxi
  have hlog := hq.log (div_ne_zero hc hxi)
  have hlin : HasDerivAt (fun y => (1 - y) / r) ((0 - 1) / r) x :=
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).div_const r
  have := hlin.add (hlog.const_mul ((1 - b) / r ^ 2))
  unfold tm
  convert this using 1
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hxb' : x - b ≠ 0 := sub_ne_zero.mpr hxb
  rw [F_eq hr0 hxb]
  have hxi' : x - xinf b r = x - b - (1 - b) / r := by unfold xinf; ring
  field_simp
  rw [hxi']
  field_simp
  ring

theorem tm_one (b r : ℝ) : tm b r 1 = 0 := by
  unfold tm
  by_cases h : 1 - xinf b r = 0
  · simp [h]
  · simp [div_self h]

/-- (1) 解に沿うと、時間の式はちょうど経った時間を返す。 -/
theorem time_along_solution {b r T : ℝ} (hb : b < 1) (hr : 0 < r) (hr1 : r ≠ 1) (hT : 0 ≤ T)
    (x : ℝ → ℝ) (hx0 : x 0 = 1) (hode : ∀ s ∈ Icc 0 T, HasDerivAt x (F b r (x s)) s)
    (havoid : ∀ s ∈ Icc 0 T, x s ≠ xinf b r ∧ b < x s) :
    tm b r (x T) = T := by
  have hd : ∀ s ∈ Icc 0 T, HasDerivAt (fun u => tm b r (x u) - u) 0 s := by
    intro s hs
    obtain ⟨h1, h2⟩ := havoid s hs
    have hF := F_ne hr h1 (ne_of_gt h2)
    have := ((hasDerivAt_tm hb hr hr1 h1 (ne_of_gt h2)).comp s (hode s hs)).sub (hasDerivAt_id s)
    have h' : HasDerivAt (fun u => tm b r (x u) - u)
        (1 / F b r (x s) * F b r (x s) - 1) s := this
    rwa [one_div_mul_cancel hF, sub_self] at h'
  have hcont : ContinuousOn (fun u => tm b r (x u) - u) (Icc 0 T) :=
    fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
  have := hconst T ⟨hT, le_rfl⟩
  simp only [hx0, tm_one, sub_zero] at this
  linarith

/-- (2) 変化の割合 p に届く体積 x_p = 1 + p(x∞ − 1) と、その時刻。 -/
theorem time_to_fraction {b r p : ℝ} (hb : b < 1) (hr : 0 < r) (hr1 : r ≠ 1) (_hp0 : 0 ≤ p)
    (hp1 : p < 1) :
    tm b r (1 + p * (xinf b r - 1)) = (1 - b) * (-log (1 - p) + p * (r - 1)) / r ^ 2 := by
  have hc := one_sub_xinf_ne hb hr hr1
  have hr0 : r ≠ 0 := ne_of_gt hr
  have h1p : 1 - p ≠ 0 := by linarith
  have hratio : (1 - xinf b r) / (1 + p * (xinf b r - 1) - xinf b r) = (1 - p)⁻¹ := by
    rw [show 1 + p * (xinf b r - 1) - xinf b r = (1 - xinf b r) * (1 - p) by ring]
    field_simp
  unfold tm
  rw [hratio, log_inv]
  have h1 : 1 - (1 + p * (xinf b r - 1)) = p * (1 - xinf b r) := by ring
  rw [h1, one_sub_xinf hr0]
  field_simp
  ring

/-- 膨らむ時間（r = 1/q）と縮む時間（r = q）。 -/
noncomputable def tSwell (b q p : ℝ) : ℝ := (1 - b) * (-log (1 - p) + p * (1 / q - 1)) / (1 / q) ^ 2
noncomputable def tShrink (b q p : ℝ) : ℝ := (1 - b) * (-log (1 - p) + p * (q - 1)) / q ^ 2

/-- 時間の比の閉じた式（b を含まない）。 -/
noncomputable def ratio (q p : ℝ) : ℝ :=
  q ^ 3 * (q * (-log (1 - p)) - (q - 1) * p) / (-log (1 - p) + (q - 1) * p)

/-- p < −ln(1 − p)（0 < p < 1）。 -/
theorem p_lt_L {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : p < -log (1 - p) := by
  have := log_lt_sub_one_of_pos (show 0 < 1 - p by linarith) (by linarith)
  linarith

/-- (3) 比は b によらず閉じた式になる。 -/
theorem ratio_eq {b q p : ℝ} (hb : b < 1) (hq : 1 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    tSwell b q p / tShrink b q p = ratio q p := by
  have hL := p_lt_L hp0 hp1
  have hq0 : q ≠ 0 := by linarith
  have hb' : 1 - b ≠ 0 := by linarith
  have hden : -log (1 - p) + p * (q - 1) ≠ 0 := by nlinarith
  have hden' : -log (1 - p) + (q - 1) * p ≠ 0 := by nlinarith
  unfold tSwell tShrink ratio
  field_simp
  ring

/-- (4) 上下の限界 q² < 比 < q⁴。 -/
theorem ratio_bounds {q p : ℝ} (hq : 1 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    q ^ 2 < ratio q p ∧ ratio q p < q ^ 4 := by
  have hL := p_lt_L hp0 hp1
  set L := -log (1 - p)
  have hD : 0 < L + (q - 1) * p := by nlinarith
  unfold ratio
  constructor
  · rw [lt_div_iff₀ hD]
    have : 0 < q * (q ^ 2 - 1) * (L - p) := by
      have : 0 < q ^ 2 - 1 := by nlinarith
      have : 0 < L - p := by linarith
      positivity
    nlinarith
  · rw [div_lt_iff₀ hD]
    have : 0 < q ^ 3 * (q * (q - 1) * p) := by
      have : 0 < q - 1 := by linarith
      positivity
    nlinarith

/-- L/p（L = −ln(1 − p)）は (0, 1) で狭義に増える。 -/
theorem Lp_strictMono : StrictMonoOn (fun p => -log (1 - p) / p) (Ioo 0 1) := by
  have hd : ∀ p ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun p => -log (1 - p) / p)
      ((p / (1 - p) + log (1 - p)) / p ^ 2) p := by
    intro p hp
    have h1p : (1 : ℝ) - p ≠ 0 := by linarith [hp.2]
    have hl : HasDerivAt (fun p => -log (1 - p)) (1 / (1 - p)) p := by
      have := (((hasDerivAt_id' p).const_sub (1 : ℝ)).log h1p).neg
      convert this using 1
      field_simp
    have := hl.div (hasDerivAt_id' p) (ne_of_gt hp.1)
    convert this using 1
    field_simp
    ring
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · exact fun p hp => (hd p hp).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Ioo] at hp
    rw [(hd p hp).deriv]
    have h1p : 0 < 1 - p := by linarith [hp.2]
    have key := log_lt_sub_one_of_pos (show 0 < (1 - p)⁻¹ by positivity)
      (by
        intro h
        have : 1 - p = 1 := by rw [← inv_inv (1 - p), h, inv_one]
        linarith [hp.1])
    rw [log_inv] at key
    have : p / (1 - p) = (1 - p)⁻¹ - 1 := by field_simp; ring
    apply div_pos _ (by have := hp.1; positivity)
    linarith

/-- 比を y = L/p で書く：比 = q³(qy − (q − 1))/(y + (q − 1))。 -/
theorem ratio_via_y {q p : ℝ} (hp0 : 0 < p) :
    ratio q p = q ^ 3 * (q * (-log (1 - p) / p) - (q - 1)) / (-log (1 - p) / p + (q - 1)) := by
  unfold ratio
  have : p ≠ 0 := ne_of_gt hp0
  rw [show q * (-log (1 - p) / p) - (q - 1) = (q * (-log (1 - p)) - (q - 1) * p) / p by
      field_simp,
    show -log (1 - p) / p + (q - 1) = (-log (1 - p) + (q - 1) * p) / p by field_simp]
  rw [mul_div_assoc', div_div_div_cancel_right₀ this]

/-- y ↦ (qy − (q − 1))/(y + (q − 1)) は y > 0 で狭義に増える。 -/
theorem frac_strictMono {q : ℝ} (hq : 1 < q) :
    StrictMonoOn (fun y => (q * y - (q - 1)) / (y + (q - 1))) (Ioi 0) := by
  intro y₁ h₁ y₂ h₂ hy
  simp only [mem_Ioi] at h₁ h₂
  simp only
  have hd1 : 0 < y₁ + (q - 1) := by linarith
  have hd2 : 0 < y₂ + (q - 1) := by linarith
  rw [div_lt_div_iff₀ hd1 hd2]
  have e : (q * y₂ - (q - 1)) * (y₁ + (q - 1)) - (q * y₁ - (q - 1)) * (y₂ + (q - 1)) =
      (q - 1) * (q + 1) * (y₂ - y₁) := by ring
  have : 0 < (q - 1) * (q + 1) * (y₂ - y₁) := by
    have : 0 < q - 1 := by linarith
    have : 0 < y₂ - y₁ := by linarith
    have : 0 < q + 1 := by linarith
    positivity
  linarith

/-- (4) 比は p について狭義に増える。 -/
theorem ratio_strictMono {q : ℝ} (hq : 1 < q) : StrictMonoOn (ratio q) (Ioo 0 1) := by
  intro p₁ h₁ p₂ h₂ hp
  rw [ratio_via_y h₁.1, ratio_via_y h₂.1, mul_div_assoc, mul_div_assoc]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  have hy1 : 0 < -log (1 - p₁) / p₁ := div_pos (by linarith [p_lt_L h₁.1 h₁.2, h₁.1]) h₁.1
  have hy2 : 0 < -log (1 - p₂) / p₂ := div_pos (by linarith [p_lt_L h₂.1 h₂.2, h₂.1]) h₂.1
  exact frac_strictMono hq hy1 hy2 (Lp_strictMono h₁ h₂ hp)

/-- L/p → 1（p → 0⁺）。 -/
theorem Lp_tendsto_zero : Tendsto (fun p => -log (1 - p) / p) (𝓝[>] 0) (𝓝 1) := by
  have hl : HasDerivAt (fun p => -log (1 - p)) 1 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).const_sub (1 : ℝ)).log (by norm_num)).neg
    convert this using 1
    norm_num
  have := hl.tendsto_slope_zero_right
  simp only [zero_add, sub_zero, log_one, neg_zero, smul_eq_mul] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p hp
  rw [div_eq_inv_mul]

/-- L/p → ∞（p → 1⁻）。 -/
theorem Lp_tendsto_one : Tendsto (fun p => -log (1 - p) / p) (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun p : ℝ => 1 - p) (𝓝[<] 1) (𝓝[>] 0) := by
    have hcont : Continuous (fun p : ℝ => 1 - p) := by fun_prop
    have hc : Tendsto (fun p : ℝ => 1 - p) (𝓝[<] 1) (𝓝 0) := by
      have := (hcont.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
      simpa using this
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hc
      (by filter_upwards [self_mem_nhdsWithin] with p hp; simpa using hp)
  have hL : Tendsto (fun p => -log (1 - p)) (𝓝[<] 1) atTop :=
    tendsto_neg_atBot_atTop.comp (tendsto_log_nhdsGT_zero.comp h1)
  have hp : Tendsto (fun p : ℝ => p) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hinv : Tendsto (fun p : ℝ => p⁻¹) (𝓝[<] 1) (𝓝 1) := by
    have := hp.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa using this
  have := hL.atTop_mul_pos (C := 1) (by norm_num) hinv
  simpa [div_eq_mul_inv] using this

/-- (4) p → 0⁺ で比は q² に近づく。 -/
theorem ratio_tendsto_zero {q : ℝ} (hq : 1 < q) :
    Tendsto (ratio q) (𝓝[>] 0) (𝓝 (q ^ 2)) := by
  have hy := Lp_tendsto_zero
  have hcont : Tendsto (fun y => q ^ 3 * (q * y - (q - 1)) / (y + (q - 1))) (𝓝 1)
      (𝓝 (q ^ 3 * (q * 1 - (q - 1)) / (1 + (q - 1)))) := by
    have hf : Continuous (fun y : ℝ => q ^ 3 * (q * y - (q - 1))) := by fun_prop
    have hg : Continuous (fun y : ℝ => y + (q - 1)) := by fun_prop
    exact (hf.continuousAt.div hg.continuousAt (ne_of_gt (by linarith))).tendsto
  have := hcont.comp hy
  rw [show q ^ 3 * (q * 1 - (q - 1)) / (1 + (q - 1)) = q ^ 2 by field_simp; ring] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (ratio_via_y hp).symm

/-- (4) p → 1⁻ で比は q⁴ に近づく。 -/
theorem ratio_tendsto_one {q : ℝ} (hq : 1 < q) :
    Tendsto (ratio q) (𝓝[<] 1) (𝓝 (q ^ 4)) := by
  have hy := Lp_tendsto_one
  -- (qy − (q − 1))/(y + (q − 1)) = q − (q² − 1)/(y + (q − 1)) → q
  have hinv : Tendsto (fun y => (q ^ 2 - 1) / (y + (q - 1))) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_right _ _ tendsto_id)
  have hfrac : Tendsto (fun y => q ^ 3 * (q - (q ^ 2 - 1) / (y + (q - 1)))) atTop
      (𝓝 (q ^ 3 * (q - 0))) := (tendsto_const_nhds.sub hinv).const_mul _
  rw [show q ^ 3 * (q - 0) = q ^ 4 by ring] at hfrac
  have := hfrac.comp hy
  refine this.congr' ?_
  have hev : ∀ᶠ p in 𝓝[<] (1 : ℝ), 0 < p := by
    have : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
    filter_upwards [this] with p hp using hp.1
  have hev2 : ∀ᶠ p in 𝓝[<] (1 : ℝ), 0 < -log (1 - p) / p + (q - 1) := by
    filter_upwards [hy.eventually_gt_atTop 0] with p hp
    linarith
  filter_upwards [hev, hev2] with p hp hp2
  simp only [Function.comp]
  rw [ratio_via_y hp, mul_div_assoc]
  congr 1
  generalize -log (1 - p) / p = y at hp2 ⊢
  field_simp
  ring

/-- (5) 落ち着く体積のそばの速さ：F′(x∞) = −r²/(1 − b)。 -/
theorem near_rate {b r : ℝ} (hb : b < 1) (hr : 0 < r) :
    HasDerivAt (F b r) (-(r ^ 2 / (1 - b))) (xinf b r) := by
  have hne : xinf b r - b ≠ 0 := by
    unfold xinf
    have : (1 - b) / r ≠ 0 := by
      have : 1 - b ≠ 0 := by linarith
      positivity
    simpa using this
  have := ((hasDerivAt_const (xinf b r) (1 - b)).div ((hasDerivAt_id _).sub_const b)
    hne).sub_const r
  have h' : HasDerivAt (fun x => (1 - b) / (x - b) - r)
      ((0 * (xinf b r - b) - (1 - b) * 1) / (xinf b r - b) ^ 2) (xinf b r) := this
  unfold F
  convert h' using 1
  have hxb : xinf b r - b = (1 - b) / r := by unfold xinf; ring
  rw [hxb]
  have : 1 - b ≠ 0 := by linarith
  have : r ≠ 0 := ne_of_gt hr
  field_simp
  ring

/-- (5) そばの速さの比（縮む r = q ÷ 膨らむ r = 1/q）は q⁴。 -/
theorem near_rate_ratio {b q : ℝ} (hb : b < 1) (hq : 0 < q) :
    (q ^ 2 / (1 - b)) / ((1 / q) ^ 2 / (1 - b)) = q ^ 4 := by
  have : 1 - b ≠ 0 := by linarith
  have : q ≠ 0 := ne_of_gt hq
  field_simp

/-- (6) q = 2、p = 1/2 の閉じた値は 5.9425 と 5.9426 のあいだ（原稿の 5.941899 は四桁目で違う）。 -/
theorem paper_half : 5.9425 < ratio 2 (1 / 2) ∧ ratio 2 (1 / 2) < 5.9426 := by
  have h1 : -log (1 - 1 / 2 : ℝ) = log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, log_inv, neg_neg]
  unfold ratio
  rw [h1]
  have lo := log_two_gt_d9
  have hi := log_two_lt_d9
  have hD : (0 : ℝ) < log 2 + (2 - 1) * (1 / 2) := by linarith
  constructor
  · rw [lt_div_iff₀ hD]; nlinarith
  · rw [div_lt_iff₀ hD]; nlinarith

end Paper966

end Yamagishi
