/-
論文59『単位球の体積は 5 次元で最大になる』（第 2 版）の格上げ（一般の形・上限の所は芯だけ）。

原稿（59_yamagishi_unit_ball_volume_peak_5d/…_jp.tex）は、半径 λ の n 次元ボールの体積
V_n λ^n = π^(n/2) λ^n / Γ(n/2 + 1) の峰が ψ(n/2 + 1) = ln(πλ²) で決まると書き、λ = 1/2・1・2・3・10 の
五点で峰の位置（0.48・5.26・24.1・55.5・627）を数値で確かめている。峰がただ一つであることや、
峰の位置の限界は示していない。

ここで証明した言明（λ > 0、X = πλ²、実数 n > −2、f(n) = log(V_n λ^n)）：
  (1) `log_V`：log(V_n λ^n) = (n/2)ln π + n ln λ − ln Γ(n/2 + 1)。
  (2) `strictConvexOn_log_Gamma`：ln Γ は (0, ∞) で狭義に凸（関数等式と log の狭義の凹性から導いた。
      論文45 のファイルと同じ証明）。`f_strictConcave`：f は (−2, ∞) で狭義に凹。
  (3) `f_add_two`：f(n + 2) − f(n) = ln X − ln(n/2 + 1)（Γ の関数等式）。
  (4) `peak_exists`：峰 n* がただ一つあり、2X − 2 < n* < 2X（すべての n ≠ n* で f(n) < f(n*)）。
  (5) `peak_eq`：峰では ψ(n*/2 + 1) = ln(πλ²)（ψ は ln Γ の導関数、原稿の式）。
  (6) `peak_strictMono`：λ₁ < λ₂ なら n*(λ₁) < n*(λ₂)。
  (7) `peak_upper_of_digamma`（芯だけ）：すべての x > 0 で ψ(x + 1/2) > ln x という不等式を仮定に置くと、
      n* < 2πλ² − 1。
仮定に置いたもの：(7) の ψ(x + 1/2) > ln x。これは ψ(x + 1/2) − ln x = ∫₀^∞ e^(−xt)(1/t − 1/(2 sinh(t/2))) dt
で被積分関数が正であることから出る既知の不等式だが、Mathlib に実数のディガンマ関数の積分表示が無いので、
名指しで仮定に置いた。
形式化していないもの：漸近形 n* = 2πλ² − 1 − 1/(12πλ²) + O(λ⁻⁶)、下側の明示の限界、整数次元に限った峰
（λ = 1 で n = 5、λ < 0.4228 で n = 0）、五点の数値。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）

For every radius λ > 0 the volume π^(n/2)λ^n/Γ(n/2 + 1), as a function of real n > −2, is strictly
log-concave and has exactly one peak n*, with 2πλ² − 2 < n* < 2πλ², ψ(n*/2 + 1) = ln(πλ²), and n*
strictly increasing in λ; assuming ψ(x + 1/2) > ln x, the peak lies below 2πλ² − 1 (core only).
-/
import Mathlib

namespace Yamagishi

namespace Paper59

open Real Set Filter Topology

/-- 半径 λ の n 次元ボールの体積。 -/
noncomputable def V (lam n : ℝ) : ℝ := π ^ (n / 2) * lam ^ n / Gamma (n / 2 + 1)

/-- その対数。 -/
noncomputable def f (lam n : ℝ) : ℝ := n / 2 * log π + n * log lam - log (Gamma (n / 2 + 1))

/-- ディガンマ関数（ln Γ の導関数）。 -/
noncomputable def psi (y : ℝ) : ℝ := deriv (log ∘ Gamma) y

/-- (1) log(V_n λ^n) = f(n)。 -/
theorem log_V {lam n : ℝ} (hl : 0 < lam) (hn : -2 < n) : log (V lam n) = f lam n := by
  unfold V f
  have hG := Gamma_pos_of_pos (show 0 < n / 2 + 1 by linarith)
  have h1 : 0 < π ^ (n / 2) := rpow_pos_of_pos pi_pos _
  have h2 : 0 < lam ^ n := rpow_pos_of_pos hl _
  rw [log_div (mul_pos h1 h2).ne' hG.ne', log_mul h1.ne' h2.ne', log_rpow pi_pos, log_rpow hl]

/-- log Γ(x + 1) = log Γ(x) + log x（x > 0）。 -/
theorem log_Gamma_succ {x : ℝ} (hx : 0 < x) :
    log (Gamma (x + 1)) = log (Gamma x) + log x := by
  rw [Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_comm]

/-- (2) log Γ は (0, ∞) で狭義に凸。 -/
theorem strictConvexOn_log_Gamma : StrictConvexOn ℝ (Ioi 0) (log ∘ Gamma) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  simp only [Function.comp, smul_eq_mul]
  set z := a * x + b * y with hz
  have hz0 : 0 < z := by positivity
  have hc := convexOn_log_Gamma.2 (show x + 1 ∈ Ioi (0 : ℝ) from by simp; linarith)
    (show y + 1 ∈ Ioi (0 : ℝ) from by simp; linarith) ha.le hb.le hab
  simp only [Function.comp, smul_eq_mul] at hc
  have hz1 : a * (x + 1) + b * (y + 1) = z + 1 := by rw [hz]; linear_combination hab
  rw [hz1] at hc
  have hlog := strictConcaveOn_log_Ioi.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at hlog
  rw [← hz] at hlog
  rw [log_Gamma_succ hz0, log_Gamma_succ hx', log_Gamma_succ hy'] at hc
  nlinarith

/-- (2) f は (−2, ∞) で狭義に凹。 -/
theorem f_strictConcave (lam : ℝ) : StrictConcaveOn ℝ (Ioi (-2)) (f lam) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx' : -2 < x := hx
  have hy' : -2 < y := hy
  simp only [smul_eq_mul]
  have h := strictConvexOn_log_Gamma.2 (show x / 2 + 1 ∈ Ioi (0 : ℝ) from by simp; linarith)
    (show y / 2 + 1 ∈ Ioi (0 : ℝ) from by simp; linarith) (by intro h; apply hxy; linarith)
    ha hb hab
  simp only [Function.comp, smul_eq_mul] at h
  have e : a * (x / 2 + 1) + b * (y / 2 + 1) = (a * x + b * y) / 2 + 1 := by
    linear_combination hab
  rw [e] at h
  unfold f
  have e2 : (a * x + b * y) / 2 * log π + (a * x + b * y) * log lam =
      a * (x / 2 * log π + x * log lam) + b * (y / 2 * log π + y * log lam) := by ring
  linarith

/-- (3) f(n + 2) − f(n) = ln(πλ²) − ln(n/2 + 1)。 -/
theorem f_add_two {lam n : ℝ} (hl : 0 < lam) (hn : -2 < n) :
    f lam (n + 2) - f lam n = log (π * lam ^ 2) - log (n / 2 + 1) := by
  unfold f
  have hy : 0 < n / 2 + 1 := by linarith
  rw [show (n + 2) / 2 + 1 = (n / 2 + 1) + 1 by ring, log_Gamma_succ hy,
    log_mul pi_pos.ne' (by positivity), log_pow]
  push_cast
  ring

/-- f の導関数：f′(n) = (1/2)ln π + ln λ − ψ(n/2 + 1)/2。 -/
theorem hasDerivAt_f {lam n : ℝ} (hn : -2 < n) :
    HasDerivAt (f lam) (1 / 2 * log π + log lam - psi (n / 2 + 1) * (1 / 2)) n := by
  have hy : 0 < n / 2 + 1 := by linarith
  have hGd : DifferentiableAt ℝ Gamma (n / 2 + 1) := by
    apply differentiableAt_Gamma
    intro m h
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hLd : DifferentiableAt ℝ (log ∘ Gamma) (n / 2 + 1) :=
    (differentiableAt_log (Gamma_pos_of_pos hy).ne').comp _ hGd
  have hg : HasDerivAt (fun n : ℝ => n / 2 + 1) (1 / 2) n := by
    simpa using ((hasDerivAt_id n).div_const 2).add_const 1
  have hcomp := hLd.hasDerivAt.comp n hg
  have hlin : HasDerivAt (fun n : ℝ => n / 2 * log π + n * log lam)
      (1 / 2 * log π + log lam) n := by
    have h1 := ((hasDerivAt_id' n).div_const 2).mul_const (log π)
    have h2 := (hasDerivAt_id' n).mul_const (log lam)
    have h3 := h1.add h2
    simp only [one_mul] at h3
    exact h3
  have := hlin.sub hcomp
  unfold f psi
  exact this

/-- 狭義に凹な関数の三点の形：u < v < w なら min(f u, f w) < f v。 -/
theorem min_lt_of_strictConcave {g : ℝ → ℝ} {s : Set ℝ} (hg : StrictConcaveOn ℝ s g)
    {u v w : ℝ} (hu : u ∈ s) (hw : w ∈ s) (huv : u < v) (hvw : v < w) :
    min (g u) (g w) < g v := by
  have hwu : 0 < w - u := by linarith
  set a := (w - v) / (w - u)
  set b := (v - u) / (w - u)
  have ha : 0 < a := div_pos (by linarith) hwu
  have hb : 0 < b := div_pos (by linarith) hwu
  have hab : a + b = 1 := by simp only [a, b]; field_simp; ring
  have hv : a * u + b * w = v := by simp only [a, b]; field_simp; ring
  have h := hg.2 hu hw (ne_of_lt (huv.trans hvw)) ha hb hab
  simp only [smul_eq_mul] at h
  rw [hv] at h
  have h1 := mul_le_mul_of_nonneg_left (min_le_left (g u) (g w)) ha.le
  have h2 := mul_le_mul_of_nonneg_left (min_le_right (g u) (g w)) hb.le
  have h3 : a * min (g u) (g w) + b * min (g u) (g w) = min (g u) (g w) := by
    rw [← add_mul, hab, one_mul]
  linarith

/-- (4) 峰はただ一つあり、2X − 2 < n* < 2X（X = πλ²）。 -/
theorem peak_exists {lam : ℝ} (hl : 0 < lam) :
    ∃ c, 2 * (π * lam ^ 2) - 2 < c ∧ c < 2 * (π * lam ^ 2) ∧
      ∀ n, -2 < n → n ≠ c → f lam n < f lam c := by
  set X := π * lam ^ 2 with hXdef
  have hX : 0 < X := by positivity
  set p := 2 * X - 2 with hpdef
  have hp : -2 < p := by linarith
  have hrec : f lam (p + 2) = f lam p := by
    have := f_add_two hl hp
    rw [show p / 2 + 1 = X by rw [hpdef]; ring] at this
    linarith
  have hconc := f_strictConcave lam
  have mem : ∀ x, -2 < x → x ∈ Ioi (-2 : ℝ) := fun x hx => hx
  have hcont : ContinuousOn (f lam) (Icc p (p + 2)) := fun x hx =>
    (hasDerivAt_f (n := x) (lam := lam) (by linarith [hx.1])).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by linarith)) hcont
  have hmid : f lam p < f lam (p + 1) := by
    have := min_lt_of_strictConcave hconc (mem p hp) (mem (p + 2) (by linarith))
      (show p < p + 1 by linarith) (show p + 1 < p + 2 by linarith)
    rw [hrec, min_self] at this
    exact this
  have hc1 : f lam (p + 1) ≤ f lam c :=
    hmax (show p + 1 ∈ Icc p (p + 2) by constructor <;> linarith)
  have hcp : c ≠ p := by intro h; rw [h] at hc1; linarith
  have hcp2 : c ≠ p + 2 := by intro h; rw [h, hrec] at hc1; linarith
  have hc' : p < c ∧ c < p + 2 := ⟨lt_of_le_of_ne hc.1 (Ne.symm hcp), lt_of_le_of_ne hc.2 hcp2⟩
  refine ⟨c, hc'.1, by linarith [hc'.2], ?_⟩
  intro n hn hnc
  have hfp : f lam p < f lam c := by linarith
  have hfp2 : f lam (p + 2) < f lam c := by linarith
  rcases lt_or_ge n p with h1 | h1
  · have := min_lt_of_strictConcave hconc (mem n hn) (mem c (by linarith)) h1 hc'.1
    rcases le_total (f lam n) (f lam c) with h2 | h2
    · rw [min_eq_left h2] at this; linarith
    · rw [min_eq_right h2] at this; linarith
  rcases lt_or_ge (p + 2) n with h3 | h3
  · have := min_lt_of_strictConcave hconc (mem c (by linarith)) (mem n hn) hc'.2 h3
    rcases le_total (f lam c) (f lam n) with h2 | h2
    · rw [min_eq_left h2] at this; linarith
    · rw [min_eq_right h2] at this; linarith
  · have hle : f lam n ≤ f lam c := hmax ⟨h1, h3⟩
    rcases lt_or_eq_of_le hle with h4 | h4
    · exact h4
    · exfalso
      rcases lt_or_gt_of_ne hnc with h5 | h5
      · have := min_lt_of_strictConcave hconc (mem n hn) (mem c (by linarith))
          (show n < (n + c) / 2 by linarith) (show (n + c) / 2 < c by linarith)
        rw [h4, min_self] at this
        have : f lam ((n + c) / 2) ≤ f lam c :=
          hmax (show (n + c) / 2 ∈ Icc p (p + 2) by constructor <;> linarith)
        linarith
      · have := min_lt_of_strictConcave hconc (mem c (by linarith)) (mem n hn)
          (show c < (n + c) / 2 by linarith) (show (n + c) / 2 < n by linarith)
        rw [h4, min_self] at this
        have : f lam ((n + c) / 2) ≤ f lam c :=
          hmax (show (n + c) / 2 ∈ Icc p (p + 2) by constructor <;> linarith)
        linarith

/-- (5) 峰では ψ(n*/2 + 1) = ln(πλ²)。 -/
theorem peak_eq {lam c : ℝ} (hl : 0 < lam) (hc : -2 < c)
    (hmax : ∀ n, -2 < n → f lam n ≤ f lam c) : psi (c / 2 + 1) = log (π * lam ^ 2) := by
  have hloc : IsLocalMax (f lam) c :=
    Filter.eventually_of_mem (Ioi_mem_nhds hc) (fun n hn => hmax n hn)
  have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_f hc)
  rw [log_mul pi_pos.ne' (by positivity), log_pow]
  push_cast
  linarith

/-- (6) λ₁ < λ₂ なら峰は右へ動く。 -/
theorem peak_strictMono {l1 l2 c1 c2 : ℝ} (h1 : 0 < l1) (h12 : l1 < l2)
    (hc1 : -2 < c1) (hc2 : -2 < c2)
    (hm1 : ∀ n, -2 < n → f l1 n ≤ f l1 c1) (hm2 : ∀ n, -2 < n → f l2 n ≤ f l2 c2) : c1 < c2 := by
  have h2 : 0 < l2 := h1.trans h12
  have hd : 0 < log l2 - log l1 := sub_pos.mpr (log_lt_log h1 h12)
  have shift : ∀ n, f l2 n = f l1 n + n * (log l2 - log l1) := by intro n; unfold f; ring
  have a := hm1 c2 hc2
  have b := hm2 c1 hc1
  rw [shift, shift] at b
  have hle : c1 ≤ c2 := by
    by_contra h
    have h' : c2 < c1 := lt_of_not_ge h
    nlinarith
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    have e1 := peak_eq h1 hc1 hm1
    have e2 := peak_eq h2 hc2 hm2
    rw [h] at e1
    rw [e1] at e2
    have := log_injOn_pos (show π * l1 ^ 2 ∈ Ioi 0 by simp; positivity)
      (show π * l2 ^ 2 ∈ Ioi 0 by simp; positivity) e2
    have : l1 ^ 2 = l2 ^ 2 := by
      have hp := pi_pos
      field_simp at this; nlinarith
    nlinarith

/-- ψ は (0, ∞) で狭義に増える（ln Γ の狭義の凸性から）。 -/
theorem psi_strictMonoOn : StrictMonoOn psi (Ioi 0) := by
  apply strictConvexOn_log_Gamma.strictMonoOn_deriv
  intro y hy
  have hy' : 0 < y := hy
  apply (differentiableAt_log (Gamma_pos_of_pos hy').ne').comp
  apply differentiableAt_Gamma
  intro m h
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- (7) 芯だけ：すべての x > 0 で ψ(x + 1/2) > ln x を仮定に置くと、峰は 2πλ² − 1 より下。 -/
theorem peak_upper_of_digamma (hψ : ∀ x : ℝ, 0 < x → log x < psi (x + 1 / 2))
    {lam c : ℝ} (hl : 0 < lam) (hc : -2 < c)
    (hmax : ∀ n, -2 < n → f lam n ≤ f lam c) : c < 2 * (π * lam ^ 2) - 1 := by
  have he := peak_eq hl hc hmax
  have hX : 0 < π * lam ^ 2 := by positivity
  have h1 := hψ _ hX
  by_contra h
  have h' : π * lam ^ 2 + 1 / 2 ≤ c / 2 + 1 := by linarith [le_of_not_gt h]
  have hm := psi_strictMonoOn.monotoneOn (show π * lam ^ 2 + 1 / 2 ∈ Ioi (0 : ℝ) by
    simp; linarith) (show c / 2 + 1 ∈ Ioi (0 : ℝ) by simp; linarith) h'
  linarith

end Paper59

end Yamagishi
