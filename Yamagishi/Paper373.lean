/-
論文373『捕食者と被食者の振幅を決めているのは、方程式ではなく初期値である』の格上げ（一般の形・芯）。

原稿（373_yamagishi_the_amplitude_is_set_by_the_initial_condition_not_the_equation/…_jp.tex）は、
ロトカ＝ヴォルテラ系 x′ = ax − bxy、y′ = −cy + dxy と保存量 V = dx − c ln x + by − a ln y を置き、
一組の係数（a = 1、b = 0.1、c = 1、d = 0.075）と四つの初期値で、被食者の最小・最大・振幅比と V を
オイラー法で数えている（V のずれ 1.457×10⁻⁴）。振幅比が V の関数であることは数で見ているだけ。

ここで証明した言明（すべての a, b, c, d > 0）：
  (1) `V_const`：正の解の上で V は時間によらず一定。
  (2) `extreme_on_line`・`extreme_level`：x′(t) = 0 となる時刻（被食者の極値）では y(t) = a/b で、
      f(x(t)) = V − g(a/b)（f(x) = dx − c ln x、g(y) = by − a ln y）。極値は保存量の値 V で決まる。
  (3) `f_strictAntiOn`・`f_strictMonoOn`：f は (0, c/d] で狭義に減り、[c/d, ∞) で狭義に増える。
      `pair_sides`：f(x₁) = f(x₂)、x₁ < x₂ なら x₁ < c/d < x₂。
  (4) `ratio_strictMono`：同じ高さ h の二つの解の比 x₂/x₁ は、h について狭義に増える。
  (5) `ratio_attained`：1 より大きいどの ρ にも、比が ρ になる高さがある
      （x₁ = c ln ρ/(d(ρ − 1))、x₂ = ρx₁）。したがって比は 1 から ∞ までのすべての値をとる。
形式化していないもの：解が閉じた周期軌道を回ること（周期性）、極値がちょうど二つの値を交互にとること、
解の存在、オイラー法の誤差、機能的応答を足した模型（観察 4.2）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper373

open Real Set

variable {a b c d : ℝ}

/-- 保存量。 -/
noncomputable def V (a b c d x y : ℝ) : ℝ := d * x - c * log x + b * y - a * log y

/-- x の部分 f(x) = dx − c ln x。 -/
noncomputable def f (c d x : ℝ) : ℝ := d * x - c * log x

/-- y の部分 g(y) = by − a ln y。 -/
noncomputable def g (a b y : ℝ) : ℝ := b * y - a * log y

theorem V_eq (x y : ℝ) : V a b c d x y = f c d x + g a b y := by
  unfold V f g; ring

/-- (1) 保存量は一定。 -/
theorem V_const {x y : ℝ → ℝ} (hx : ∀ t, 0 < x t) (hy : ∀ t, 0 < y t)
    (hx' : ∀ t, HasDerivAt x (a * x t - b * x t * y t) t)
    (hy' : ∀ t, HasDerivAt y (-c * y t + d * x t * y t) t) (t₁ t₂ : ℝ) :
    V a b c d (x t₁) (y t₁) = V a b c d (x t₂) (y t₂) := by
  have hd : ∀ t, HasDerivAt (fun t => V a b c d (x t) (y t)) 0 t := by
    intro t
    have h1 := (hx' t).const_mul d
    have h2 := ((hx' t).log (hx t).ne').const_mul c
    have h3 := (hy' t).const_mul b
    have h4 := ((hy' t).log (hy t).ne').const_mul a
    have h := ((h1.sub h2).add h3).sub h4
    unfold V
    convert h using 1
    have := (hx t).ne'; have := (hy t).ne'
    field_simp
    ring
  have hdiff : Differentiable ℝ (fun t => V a b c d (x t) (y t)) :=
    fun t => (hd t).differentiableAt
  exact is_const_of_deriv_eq_zero hdiff (fun t => (hd t).deriv) t₁ t₂

/-- (2) 被食者の極値（x′ = 0）は直線 y = a/b の上。 -/
theorem extreme_on_line (hb : 0 < b) {x y : ℝ} (hx : 0 < x) (h : a * x - b * x * y = 0) :
    y = a / b := by
  have : x * (a - b * y) = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_left hx.ne'
  field_simp; linarith

/-- (2) そのときの x は f(x) = V − g(a/b) を満たす。 -/
theorem extreme_level (hb : 0 < b) {x y : ℝ} (hx : 0 < x) (h : a * x - b * x * y = 0) :
    f c d x = V a b c d x y - g a b (a / b) := by
  rw [V_eq, extreme_on_line hb hx h]; ring

/-- (3) f は (0, c/d] で狭義に減る。 -/
theorem f_strictAntiOn (hc : 0 < c) (hd : 0 < d) : StrictAntiOn (f c d) (Ioc 0 (c / d)) := by
  intro u hu v hv huv
  have hu0 := hu.1; have hv0 := hv.1
  -- ln(v/u) > 1 − u/v
  have hlog : 1 - u / v < log (v / u) := by
    have h1 : u / v ≠ 1 := by rw [Ne, div_eq_one_iff_eq hv0.ne']; exact huv.ne
    have := log_lt_sub_one_of_pos (div_pos hu0 hv0) h1
    rw [show v / u = (u / v)⁻¹ by field_simp, log_inv]
    linarith
  have hcv : d * v ≤ c := by
    have := hv.2; rw [le_div_iff₀ hd] at this; linarith
  unfold f
  rw [log_div hv0.ne' hu0.ne'] at hlog
  have : c * (1 - u / v) * v = c * (v - u) := by field_simp
  nlinarith [mul_pos hc hv0]

/-- (3) f は [c/d, ∞) で狭義に増える。 -/
theorem f_strictMonoOn (hc : 0 < c) (hd : 0 < d) : StrictMonoOn (f c d) (Ici (c / d)) := by
  intro u hu v hv huv
  have hu0 : 0 < u := lt_of_lt_of_le (div_pos hc hd) hu
  have hv0 : 0 < v := hu0.trans huv
  have hlog : log (v / u) < v / u - 1 := by
    have h1 : v / u ≠ 1 := by rw [Ne, div_eq_one_iff_eq hu0.ne']; exact huv.ne'
    exact log_lt_sub_one_of_pos (div_pos hv0 hu0) h1
  have hcu : c ≤ d * u := by
    have := mem_Ici.1 hu; rw [div_le_iff₀ hd] at this; linarith
  unfold f
  rw [log_div hv0.ne' hu0.ne'] at hlog
  have : c * (v / u - 1) * u = c * (v - u) := by field_simp
  nlinarith [mul_pos hc hu0]

/-- (3) 同じ高さの二つの解は c/d の両側にある。 -/
theorem pair_sides (hc : 0 < c) (hd : 0 < d) {x₁ x₂ : ℝ} (h1 : 0 < x₁) (h12 : x₁ < x₂)
    (hf : f c d x₁ = f c d x₂) : x₁ < c / d ∧ c / d < x₂ := by
  have hm := div_pos hc hd
  constructor
  · by_contra h
    push Not at h
    have := f_strictMonoOn hc hd (mem_Ici.2 h) (mem_Ici.2 (h.trans h12.le)) h12
    linarith
  · by_contra h
    push Not at h
    have := f_strictAntiOn hc hd ⟨h1, h12.le.trans h⟩ ⟨h1.trans h12, h⟩ h12
    linarith

/-- (4) 振幅の比 x₂/x₁ は高さについて狭義に増える。 -/
theorem ratio_strictMono (hc : 0 < c) (hd : 0 < d) {x₁ x₂ y₁ y₂ : ℝ}
    (hx1 : 0 < x₁) (hx : x₁ < x₂) (hfx : f c d x₁ = f c d x₂)
    (hy1 : 0 < y₁) (hy : y₁ < y₂) (hfy : f c d y₁ = f c d y₂)
    (hlt : f c d x₁ < f c d y₁) : x₂ / x₁ < y₂ / y₁ := by
  obtain ⟨hx1m, hx2m⟩ := pair_sides hc hd hx1 hx hfx
  obtain ⟨hy1m, hy2m⟩ := pair_sides hc hd hy1 hy hfy
  -- 左側：y₁ < x₁
  have h1 : y₁ < x₁ := by
    by_contra h
    push Not at h
    have := (f_strictAntiOn hc hd).antitoneOn ⟨hx1, hx1m.le⟩ ⟨hy1, hy1m.le⟩ h
    linarith
  -- 右側：x₂ < y₂
  have h2 : x₂ < y₂ := by
    by_contra h
    push Not at h
    have := (f_strictMonoOn hc hd).monotoneOn (mem_Ici.2 hy2m.le) (mem_Ici.2 hx2m.le) h
    linarith
  rw [div_lt_div_iff₀ hx1 hy1]
  nlinarith

/-- (5) 1 より大きいどの比も、ある高さで実現する。 -/
theorem ratio_attained (hc : 0 < c) (hd : 0 < d) {ρ : ℝ} (hρ : 1 < ρ) :
    let x₁ := c * log ρ / (d * (ρ - 1))
    0 < x₁ ∧ x₁ < ρ * x₁ ∧ f c d x₁ = f c d (ρ * x₁) ∧ (ρ * x₁) / x₁ = ρ := by
  intro x₁
  have hl : 0 < log ρ := log_pos hρ
  have hx : 0 < x₁ := div_pos (mul_pos hc hl) (mul_pos hd (by linarith))
  refine ⟨hx, by nlinarith, ?_, by field_simp⟩
  unfold f
  rw [log_mul (by linarith) hx.ne']
  have : d * (ρ * x₁) - d * x₁ = c * log ρ := by
    simp only [x₁]; field_simp
  linarith

end Paper373

end Yamagishi
