/-
論文799『濃度で読む位置の細かさは、誤差を濃度の割合で置けばどこでも同じ、分子の数なら遠いほど粗い』の
格上げ（一般の形）。

原稿（799_yamagishi_reading_position_from_concentration_fraction_or_count/…_jp.tex）は、
指数の勾配 k̄(x) = N₀ e^(−x/λ)（λ = 0.2, N₀ = 10000）一つだけで、
  ・割合の誤差 σ_k = ε k̄ では位置の誤差 σ_x ≈ λε が場所によらない、
  ・数の揺らぎ σ_k = √k̄ では σ_x ≈ λ/√(N₀ e^(−x/λ)) が遠いほど指数で粗い、
を一次の式・数値積分・乱数で示し、x* = λ ln(N₀w²/λ²)、N₁ = (λ²/w²)e^(L/λ)、
N₂ = (λ²/(2w²))e^(L/(2λ))、N₁/N₂ = 2e^(L/(2λ)) を閉じた式で出している。

ここで証明した言明（一次の誤差の式 σ_x = σ_k/|c'(x)| を出発点に置く）：
  (1) `uniform_fraction_iff_exponential`：開区間 (a, b) で正で、微分できて、狭義に減る濃度 c について、
      割合の誤差の位置誤差 ε c/|c'| がどこでも同じ ⇔ c = N₀ e^(−x/λ)（N₀, λ > 0）。そのとき値は λε。
  (2) `uniform_count_iff_square`：同じ条件で、数の揺らぎの位置誤差 √c/|c'| がどこでも同じ
      ⇔ c = (α − βx)²（β > 0、区間の上で α − βx > 0）。
  (3) `count_error_exponential`・`count_error_ratio`：指数の勾配では √c/|c'| = (λ/√N₀) e^(x/(2λ))、
      二点の比は e^((x₂ − x₁)/(2λ))（原稿の e² はこの x₂ − x₁ = 0.8, λ = 0.2 の場合）。
  (4) `one_side_reach`・`one_side_needed`：片側から送ると σ_x ≤ w ⇔ x ≤ λ ln(N₀w²/λ²)、
      位置 L まで読めるのは N₀ ≥ (λ²/w²)e^(L/λ) のときだけ。
  (5) `two_side_worst_middle`・`two_side_needed`：両側から同じ勾配を送り分散の逆数で重みを付けると、
      精度（分散の逆数）が最も低いのは真ん中で、組織の全部で σ_x ≤ w ⇔ N₀ ≥ (λ²/(2w²))e^(L/(2λ))。
足した仮定：濃度 c は区間の上で正・微分できる・狭義に減る（c' < 0）。誤差の伝わり方は一次の式
σ_x = σ_k/|c'| を定義として置いた（推定値の分布そのものや数値積分の側は扱っていない）。
両側の組み合わせは原稿どおり、二本が独立で分散の逆数の重み 1/σ² = 1/σ₁² + 1/σ₂² と置いた。

形式化していないもの：一次の式の外の「推定値の分布全体が場所によらないのは指数の形だけ」
（関数方程式 c(x + h(t)) = t c(x) の側）、数値積分・乱数の値、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper799

open Real Set

/-- 割合の誤差 ε で置いたときの、一次の位置誤差 ε c/|c'|。 -/
noncomputable def fracErr (ε c c' : ℝ) : ℝ := ε * c / |c'|

/-- 数の揺らぎ（分散 = 平均）で置いたときの、一次の位置誤差 √c/|c'|。 -/
noncomputable def countErr (c c' : ℝ) : ℝ := √c / |c'|

/-- (1) 割合の誤差の位置誤差がどこでも同じになるのは、指数の形のときだけ。 -/
theorem uniform_fraction_iff_exponential {a b ε : ℝ} (hab : a < b) (hε : 0 < ε)
    {c c' : ℝ → ℝ} (hd : ∀ x ∈ Ioo a b, HasDerivAt c (c' x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < c x) (hdec : ∀ x ∈ Ioo a b, c' x < 0) :
    (∃ σ, ∀ x ∈ Ioo a b, fracErr ε (c x) (c' x) = σ) ↔
      ∃ N₀ > 0, ∃ l > 0, ∀ x ∈ Ioo a b, c x = N₀ * exp (-x / l) := by
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨x₀, hx₀⟩ : (Ioo a b).Nonempty := nonempty_Ioo.mpr hab
    have hσpos : 0 < σ := by
      rw [← hσ x₀ hx₀, fracErr]
      have := hpos x₀ hx₀; have := hdec x₀ hx₀
      apply div_pos (by positivity); exact abs_pos.mpr (ne_of_lt (hdec x₀ hx₀))
    set l := σ / ε with hl
    have hlpos : 0 < l := div_pos hσpos hε
    -- c' = −c/l
    have hc' : ∀ x ∈ Ioo a b, c' x = -c x / l := by
      intro x hx
      have h1 := hσ x hx
      rw [fracErr, abs_of_neg (hdec x hx)] at h1
      have hne : -c' x ≠ 0 := by have := hdec x hx; linarith
      rw [div_eq_iff hne] at h1
      rw [hl]; field_simp; linarith
    -- g = c · e^(x/l) は定数
    let g : ℝ → ℝ := fun x => c x * exp (x / l)
    have hg : ∀ x ∈ Ioo a b, HasDerivAt g 0 x := by
      intro x hx
      have h1 : HasDerivAt (fun x => exp (x / l)) (exp (x / l) * (1 / l)) x := by
        have := ((hasDerivAt_id x).div_const l).exp
        simpa using this
      have h2 := (hd x hx).mul h1
      convert h2 using 1
      rw [hc' x hx]; field_simp; ring
    have hgd : DifferentiableOn ℝ g (Ioo a b) :=
        fun x hx => (hg x hx).differentiableAt.differentiableWithinAt
    have hg0 : (Ioo a b).EqOn (deriv g) 0 := fun x hx => (hg x hx).deriv
    obtain ⟨N₀, hN₀⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo hgd hg0
    have hN₀pos : 0 < N₀ := by
      rw [← hN₀ x₀ hx₀]; exact mul_pos (hpos x₀ hx₀) (exp_pos _)
    refine ⟨N₀, hN₀pos, l, hlpos, fun x hx => ?_⟩
    have := hN₀ x hx
    simp only [g] at this
    rw [← this, mul_assoc, ← exp_add]
    have : x / l + -x / l = 0 := by ring
    rw [this, exp_zero, mul_one]
  · rintro ⟨N₀, hN₀, l, hl, hc⟩
    refine ⟨l * ε, fun x hx => ?_⟩
    have hdx : HasDerivAt c (N₀ * (exp (-x / l) * (-1 / l))) x := by
      have h1 : HasDerivAt (fun x => N₀ * exp (-x / l)) (N₀ * (exp (-x / l) * (-1 / l))) x := by
        have := (((hasDerivAt_id x).neg).div_const l).exp.const_mul N₀
        simpa using this
      apply h1.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using hc y hy
    have := (hd x hx).unique hdx
    rw [fracErr, this, hc x hx]
    have he := exp_pos (-x / l)
    rw [abs_of_neg (by
      have : N₀ * exp (-x / l) > 0 := by positivity
      have : N₀ * (exp (-x / l) * (-1 / l)) = -(N₀ * exp (-x / l) / l) := by ring
      rw [this]; have : N₀ * exp (-x / l) / l > 0 := by positivity
      linarith)]
    field_simp

/-- (2) 数の揺らぎの位置誤差がどこでも同じになるのは、二乗の形 (α − βx)² のときだけ。 -/
theorem uniform_count_iff_square {a b : ℝ} (hab : a < b)
    {c c' : ℝ → ℝ} (hd : ∀ x ∈ Ioo a b, HasDerivAt c (c' x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < c x) (hdec : ∀ x ∈ Ioo a b, c' x < 0) :
    (∃ κ, ∀ x ∈ Ioo a b, countErr (c x) (c' x) = κ) ↔
      ∃ α, ∃ β > 0, ∀ x ∈ Ioo a b, 0 < α - β * x ∧ c x = (α - β * x) ^ 2 := by
  constructor
  · rintro ⟨κ, hκ⟩
    obtain ⟨x₀, hx₀⟩ : (Ioo a b).Nonempty := nonempty_Ioo.mpr hab
    have hκpos : 0 < κ := by
      rw [← hκ x₀ hx₀, countErr]
      apply div_pos (Real.sqrt_pos.mpr (hpos x₀ hx₀))
      exact abs_pos.mpr (ne_of_lt (hdec x₀ hx₀))
    have hc' : ∀ x ∈ Ioo a b, c' x = -√(c x) / κ := by
      intro x hx
      have h1 := hκ x hx
      rw [countErr, abs_of_neg (hdec x hx)] at h1
      have hne : -c' x ≠ 0 := by have := hdec x hx; linarith
      rw [div_eq_iff hne] at h1
      field_simp; linarith
    -- h = √c + x/(2κ) は定数
    let h : ℝ → ℝ := fun x => √(c x) + x / (2 * κ)
    have hh : ∀ x ∈ Ioo a b, HasDerivAt h 0 x := by
      intro x hx
      have hs := (hd x hx).sqrt (ne_of_gt (hpos x hx))
      have h2 := hs.add ((hasDerivAt_id' x).div_const (2 * κ))
      refine h2.congr_deriv ?_
      rw [hc' x hx]
      have : 0 < √(c x) := Real.sqrt_pos.mpr (hpos x hx)
      field_simp; ring
    have hhd : DifferentiableOn ℝ h (Ioo a b) :=
        fun x hx => (hh x hx).differentiableAt.differentiableWithinAt
    have hh0 : (Ioo a b).EqOn (deriv h) 0 := fun x hx => (hh x hx).deriv
    obtain ⟨α, hα⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo hhd hh0
    refine ⟨α, 1 / (2 * κ), by positivity, fun x hx => ?_⟩
    have e := hα x hx
    simp only [h] at e
    have hsq : √(c x) = α - 1 / (2 * κ) * x := by rw [← e]; ring
    refine ⟨by rw [← hsq]; exact Real.sqrt_pos.mpr (hpos x hx), ?_⟩
    rw [← hsq, Real.sq_sqrt (le_of_lt (hpos x hx))]
  · rintro ⟨α, β, hβ, hc⟩
    refine ⟨1 / (2 * β), fun x hx => ?_⟩
    obtain ⟨hp, hcx⟩ := hc x hx
    have hdx : HasDerivAt c (2 * (α - β * x) * (-β)) x := by
      have h0 : HasDerivAt (fun y => α - β * y) (0 - β * 1) x :=
        (hasDerivAt_const x α).sub ((hasDerivAt_id' x).const_mul β)
      have h1 : HasDerivAt (fun y => (α - β * y) ^ 2) (2 * (α - β * x) * (-β)) x :=
        (h0.pow 2).congr_deriv (by norm_num)
      apply h1.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using (hc y hy).2
    rw [countErr, (hd x hx).unique hdx, hcx, Real.sqrt_sq (le_of_lt hp)]
    rw [abs_of_neg (by nlinarith)]
    field_simp

/-- (3) 指数の勾配では、数の揺らぎの位置誤差は (λ/√N₀) e^(x/(2λ))。 -/
theorem count_error_exponential {N₀ l : ℝ} (hN : 0 < N₀) (hl : 0 < l) (x : ℝ) :
    countErr (N₀ * exp (-x / l)) (N₀ * exp (-x / l) * (-1 / l)) =
      l / √N₀ * exp (x / (2 * l)) := by
  rw [countErr]
  set s := √N₀ with hs_def
  set E := exp (-x / (2 * l)) with hE_def
  have hs : 0 < s := Real.sqrt_pos.mpr hN
  have hE : 0 < E := exp_pos _
  have hN' : N₀ = s ^ 2 := (Real.sq_sqrt (le_of_lt hN)).symm
  have he : exp (-x / l) = E ^ 2 := by
    rw [hE_def, ← exp_natCast_mul]; congr 1; push_cast; field_simp
  have he' : exp (x / (2 * l)) = E⁻¹ := by
    rw [hE_def, ← exp_neg]; congr 1; ring
  rw [he, he', hN', Real.sqrt_mul (by positivity), Real.sqrt_sq hs.le, Real.sqrt_sq hE.le]
  rw [abs_of_neg (by
    have : s ^ 2 * E ^ 2 * (-1 / l) = -(s ^ 2 * E ^ 2 / l) := by ring
    rw [this]; have : 0 < s ^ 2 * E ^ 2 / l := by positivity
    linarith)]
  field_simp

/-- 二点の位置誤差の比は e^((x₂ − x₁)/(2λ))。 -/
theorem count_error_ratio {N₀ l : ℝ} (hN : 0 < N₀) (hl : 0 < l) (x₁ x₂ : ℝ) :
    countErr (N₀ * exp (-x₂ / l)) (N₀ * exp (-x₂ / l) * (-1 / l)) /
      countErr (N₀ * exp (-x₁ / l)) (N₀ * exp (-x₁ / l) * (-1 / l)) =
      exp ((x₂ - x₁) / (2 * l)) := by
  rw [count_error_exponential hN hl, count_error_exponential hN hl]
  have hs : 0 < √N₀ := Real.sqrt_pos.mpr hN
  rw [show (x₂ - x₁) / (2 * l) = x₂ / (2 * l) - x₁ / (2 * l) by ring, exp_sub]
  field_simp

/-- 原稿の数：位置 0.1 と 0.9、λ = 0.2 で比は e²。 -/
example : exp (((0.9 : ℝ) - 0.1) / (2 * 0.2)) = exp 2 := by norm_num

/-- 指数の勾配での数の揺らぎの位置誤差（閉じた形）。 -/
noncomputable def sigmaOne (N₀ l x : ℝ) : ℝ := l / √N₀ * exp (x / (2 * l))

/-- (4) 片側から：σ_x ≤ w ⇔ x ≤ λ ln(N₀w²/λ²)。 -/
theorem one_side_reach {N₀ l w : ℝ} (hN : 0 < N₀) (hl : 0 < l) (hw : 0 < w) (x : ℝ) :
    sigmaOne N₀ l x ≤ w ↔ x ≤ l * log (N₀ * w ^ 2 / l ^ 2) := by
  unfold sigmaOne
  have hs : 0 < √N₀ := Real.sqrt_pos.mpr hN
  have hsq : √N₀ ^ 2 = N₀ := Real.sq_sqrt (le_of_lt hN)
  rw [div_mul_eq_mul_div, div_le_iff₀ hs]
  -- 両辺正なので、二乗して対数をとる
  have hA : 0 < l * exp (x / (2 * l)) := by positivity
  have hB : 0 < w * √N₀ := by positivity
  rw [← pow_le_pow_iff_left₀ hA.le hB.le (two_ne_zero), mul_pow, mul_pow, hsq, ← exp_natCast_mul]
  have : ((2 : ℕ) : ℝ) * (x / (2 * l)) = x / l := by push_cast; field_simp
  rw [this, ← le_div_iff₀' (by positivity), ← log_le_log_iff (exp_pos _) (by positivity), log_exp,
    div_le_iff₀ hl]
  rw [mul_comm (w ^ 2) N₀, mul_comm l]

/-- 位置 L まで細胞一つ以内に読めるのは、N₀ ≥ (λ²/w²) e^(L/λ) のときだけ。 -/
theorem one_side_needed {N₀ l w L : ℝ} (hN : 0 < N₀) (hl : 0 < l) (hw : 0 < w) :
    sigmaOne N₀ l L ≤ w ↔ l ^ 2 / w ^ 2 * exp (L / l) ≤ N₀ := by
  rw [one_side_reach hN hl hw, ← div_le_iff₀' hl, ← exp_le_exp, exp_log (by positivity)]
  rw [le_div_iff₀ (by positivity), div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith [exp_pos (L / l)]

/-- 両側から送ったときの精度（分散の逆数）1/σ₁² + 1/σ₂² = (N₀/λ²)(e^(−x/λ) + e^(−(L−x)/λ))。 -/
noncomputable def precisionTwo (N₀ l L x : ℝ) : ℝ :=
    N₀ / l ^ 2 * (exp (-x / l) + exp (-(L - x) / l))

theorem precision_one_side {N₀ l : ℝ} (hN : 0 < N₀) (hl : 0 < l) (x : ℝ) :
    1 / sigmaOne N₀ l x ^ 2 = N₀ / l ^ 2 * exp (-x / l) := by
  unfold sigmaOne
  set s := √N₀ with hs_def
  set E := exp (x / (2 * l)) with hE_def
  have hs : 0 < s := Real.sqrt_pos.mpr hN
  have hE : 0 < E := exp_pos _
  have hN' : N₀ = s ^ 2 := (Real.sq_sqrt (le_of_lt hN)).symm
  have he : exp (-x / l) = (E ^ 2)⁻¹ := by
    rw [hE_def, ← exp_natCast_mul, ← exp_neg]; congr 1; push_cast; field_simp
  rw [he, hN']
  field_simp

/-- (5) 両側から：精度が最も低いのは真ん中 x = L/2。 -/
theorem two_side_worst_middle {N₀ l L : ℝ} (hN : 0 < N₀) (hl : 0 < l) (x : ℝ) :
    precisionTwo N₀ l L (L / 2) ≤ precisionTwo N₀ l L x := by
  unfold precisionTwo
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  -- e^u + e^v ≥ 2 e^((u+v)/2)
  set u := -x / l; set v := -(L - x) / l
  have hm : -(L / 2) / l = (u + v) / 2 := by simp only [u, v]; ring
  have hm2 : -(L - L / 2) / l = (u + v) / 2 := by simp only [u, v]; ring
  rw [hm, hm2]
  have h1 : exp u = exp ((u + v) / 2) * exp ((u - v) / 2) := by rw [← exp_add]; ring_nf
  have h2 : exp v = exp ((u + v) / 2) * exp (-((u - v) / 2)) := by rw [← exp_add]; ring_nf
  rw [h1, h2, exp_neg]
  have hp := exp_pos ((u + v) / 2)
  have hq := exp_pos ((u - v) / 2)
  set q := exp ((u - v) / 2)
  have : q + q⁻¹ ≥ 2 := by
    rw [ge_iff_le, ← sub_nonneg]
    have : q + q⁻¹ - 2 = (q - 1) ^ 2 / q := by field_simp; ring
    rw [this]; positivity
  nlinarith

theorem precision_two_middle {N₀ l L : ℝ} :
    precisionTwo N₀ l L (L / 2) = 2 * N₀ / l ^ 2 * exp (-L / (2 * l)) := by
  unfold precisionTwo
  have : -(L - L / 2) / l = -L / (2 * l) := by ring
  have h2 : -(L / 2) / l = -L / (2 * l) := by ring
  rw [this, h2]; ring

/-- 両側から：組織 [0, L] の全部で σ_x ≤ w（精度 ≥ 1/w²）⇔ N₀ ≥ (λ²/(2w²)) e^(L/(2λ))。 -/
theorem two_side_needed {N₀ l w L : ℝ} (hN : 0 < N₀) (hl : 0 < l) (hw : 0 < w) :
    (∀ x, 1 / w ^ 2 ≤ precisionTwo N₀ l L x) ↔ l ^ 2 / (2 * w ^ 2) * exp (L / (2 * l)) ≤ N₀ := by
  have key : (∀ x, 1 / w ^ 2 ≤ precisionTwo N₀ l L x) ↔ 1 / w ^ 2 ≤ precisionTwo N₀ l L (L / 2) :=
    ⟨fun h => h _, fun h x => h.trans (two_side_worst_middle hN hl x)⟩
  rw [key, precision_two_middle]
  have he : exp (-L / (2 * l)) * exp (L / (2 * l)) = 1 := by rw [← exp_add]; ring_nf; simp
  have hE := exp_pos (L / (2 * l))
  have hE' := exp_pos (-L / (2 * l))
  have hw2 : 0 < w ^ 2 := by positivity
  have hl2 : 0 < l ^ 2 := by positivity
  rw [div_le_iff₀ hw2, show 2 * N₀ / l ^ 2 * exp (-L / (2 * l)) * w ^ 2 =
      (2 * N₀ * exp (-L / (2 * l)) * w ^ 2) / l ^ 2 by ring, le_div_iff₀ hl2, one_mul,
    show l ^ 2 / (2 * w ^ 2) * exp (L / (2 * l)) =
        (l ^ 2 * exp (L / (2 * l))) / (2 * w ^ 2) by ring,
    div_le_iff₀ (by positivity)]
  constructor
  · intro h; nlinarith [mul_le_mul_of_nonneg_right h hE.le]
  · intro h; nlinarith [mul_le_mul_of_nonneg_right h hE'.le]

/-- 片側と両側（源ごと）の必要な数の比は 2 e^(L/(2λ))。 -/
theorem needed_ratio {l w L : ℝ} (hl : 0 < l) (hw : 0 < w) :
    (l ^ 2 / w ^ 2 * exp (L / l)) / (l ^ 2 / (2 * w ^ 2) * exp (L / (2 * l))) =
      2 * exp (L / (2 * l)) := by
  have : exp (L / l) = exp (L / (2 * l)) * exp (L / (2 * l)) := by
      rw [← exp_add]; congr 1; field_simp; ring
  rw [this]
  have := exp_pos (L / (2 * l))
  field_simp

end Paper799

end Yamagishi
