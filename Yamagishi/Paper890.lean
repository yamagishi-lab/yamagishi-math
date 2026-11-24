/-
論文890『揺らぐ風では、風速計は平均の風速より多く回る』の格上げ（一般の形）。

日本語の一文：追いつく時間が距離定数を風速で割った値である風速計の模型では、風が正で周期的なら、
どんな揺らぎの形でも、一周期の指示の平均は風速の平均以上で、等しいのは風が一定のときだけである。
追いつく時間が一定なら、二つの平均はちょうど等しい。
English: For the cup-anemometer model dV/dt = U(U − V)/L with a positive wind U and a positive
P-periodic reading V (V(P) = V(0)), ∫₀^P V ≥ ∫₀^P U for every L > 0 and every shape of the gusts,
with equality exactly when U is constant on [0, P]; with a fixed response time,
dV/dt = (U − V)/τ, the two integrals are equal.

原稿（890_yamagishi_gusty_wind_makes_anemometer_read_high/…_jp.tex）は、L = 3 m、U₀ = 5 m/s、正弦の
揺らぎ一つ（大きさ 0.1〜0.3、速さ 0.05〜5 回/秒）を数値で積分し、過大 0.003909〜0.044949 と、
追いつく時間を 0.6 秒に固定した対照の −0.000001 を出している。過大が負にならないことの一般の
理由は書いていない。

ここで証明した言明（L > 0、P > 0、[0, P] で U は連続で正、V は微分できて正、V(P) = V(0)）：
  (1) `log_identity`：∫₀^P U(U − V)/V dt = 0（d(ln V)/dt の一周期の積分が 0）。
  (2) `excess_eq`：∫₀^P V − ∫₀^P U = ∫₀^P (U − V)²/V dt。
      `mean_ge`：よって ∫₀^P U ≤ ∫₀^P V（指示の平均 ≥ 風速の平均）。揺らぎの形・大きさ・速さ・L によらない。
  (3) `mean_eq_iff_eq`：等号 ⇔ [0, P] のすべての t で U(t) = V(t)。
      `const_of_eq`：そのとき U は [0, P] で一定。
      `eq_of_const`：逆に U が一定 c なら、周期の解は V ≡ c しかない。
      `mean_eq_iff_const`：まとめて、等号 ⇔ 風が [0, P] で一定。
  (4) `fixed_tau`：追いつく時間が一定の対照 dV/dt = (U − V)/τ では、∫₀^P V = ∫₀^P U。
足した仮定：風速計の模型 dV/dt = U(U − V)/L（追いつく時間 L/U）を定義として置いた。周期の解 V が在って
正であることは仮定に置いた（線形の一階の式なので在ることは標準の事実だが、ここでは形式化していない）。
原稿の正弦の風はこの仮定をみたす。
形式化していないもの：周期の解が在ってただ一つで引き寄せること、長い時間の平均と一周期の平均の一致、
上の限界の予想（指示の平均 ≤ U² の平均 ÷ U の平均。下読みの AI は数値で破れを見つけていないが、証明は無い）、
数表の数値の積分、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper890

open Real Set intervalIntegral MeasureTheory

/-- 導関数が [0, P] で 0 なら、[0, P] で一定。 -/
theorem const_on {g : ℝ → ℝ} {P : ℝ} (hd : ∀ t ∈ Icc 0 P, HasDerivAt g 0 t) :
    ∀ t ∈ Icc 0 P, g t = g 0 := by
  have hcont : ContinuousOn g (Icc 0 P) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  exact constant_of_has_deriv_right_zero hcont
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)

section Model

variable {L P : ℝ} {U V : ℝ → ℝ}

theorem V_cont (hV : ∀ t ∈ Icc 0 P, HasDerivAt V (U t * (U t - V t) / L) t) :
    ContinuousOn V (Icc 0 P) := fun t ht => (hV t ht).continuousAt.continuousWithinAt

/-- (1) d(ln V)/dt の一周期の積分は 0：∫ U(U − V)/V = 0。 -/
theorem log_identity (hL : 0 < L) (hP : 0 < P) (hU : ContinuousOn U (Icc 0 P))
    (hV : ∀ t ∈ Icc 0 P, HasDerivAt V (U t * (U t - V t) / L) t)
    (hVpos : ∀ t ∈ Icc 0 P, 0 < V t) (hper : V P = V 0) :
    ∫ t in (0 : ℝ)..P, U t * (U t - V t) / V t = 0 := by
  have hVc := V_cont hV
  have hI : Icc 0 P = uIcc 0 P := (uIcc_of_le hP.le).symm
  have hcont : ContinuousOn (fun t => U t * (U t - V t) / L / V t) (Icc 0 P) := by
    apply ContinuousOn.div _ hVc (fun t ht => ne_of_gt (hVpos t ht))
    exact ((hU.mul (hU.sub hVc)).div_const L)
  have hftc := integral_eq_sub_of_hasDerivAt (f := fun t => log (V t))
    (f' := fun t => U t * (U t - V t) / L / V t)
    (fun t ht => by rw [← hI] at ht; exact (hV t ht).log (ne_of_gt (hVpos t ht)))
    (by rw [hI] at hcont; exact hcont.intervalIntegrable)
  rw [hper, sub_self] at hftc
  have : (fun t => U t * (U t - V t) / L / V t) = fun t => L⁻¹ * (U t * (U t - V t) / V t) := by
    funext t; field_simp
  rw [this, intervalIntegral.integral_const_mul] at hftc
  rcases mul_eq_zero.mp hftc with h | h
  · exact absurd h (inv_ne_zero (ne_of_gt hL))
  · exact h

/-- 各点の恒等式 U(U − V)/V = (U − V) + (U − V)²/V。 -/
theorem pointwise {u v : ℝ} (hv : v ≠ 0) : u * (u - v) / v = (u - v) + (u - v) ^ 2 / v := by
  field_simp; ring

/-- (2) 過大の積分の形：∫V − ∫U = ∫(U − V)²/V。 -/
theorem excess_eq (hL : 0 < L) (hP : 0 < P) (hU : ContinuousOn U (Icc 0 P))
    (hV : ∀ t ∈ Icc 0 P, HasDerivAt V (U t * (U t - V t) / L) t)
    (hVpos : ∀ t ∈ Icc 0 P, 0 < V t) (hper : V P = V 0) :
    (∫ t in (0 : ℝ)..P, V t) - (∫ t in (0 : ℝ)..P, U t) =
      ∫ t in (0 : ℝ)..P, (U t - V t) ^ 2 / V t := by
  have hVc := V_cont hV
  have hI : Icc 0 P = uIcc 0 P := (uIcc_of_le hP.le).symm
  have hid := log_identity hL hP hU hV hVpos hper
  have hU' : IntervalIntegrable U volume 0 P := by rw [hI] at hU; exact hU.intervalIntegrable
  have hV' : IntervalIntegrable V volume 0 P := by rw [hI] at hVc; exact hVc.intervalIntegrable
  have hw : IntervalIntegrable (fun t => (U t - V t) ^ 2 / V t) volume 0 P := by
    have : ContinuousOn (fun t => (U t - V t) ^ 2 / V t) (Icc 0 P) :=
      ((hU.sub hVc).pow 2).div hVc (fun t ht => ne_of_gt (hVpos t ht))
    rw [hI] at this; exact this.intervalIntegrable
  have hcongr : ∫ t in (0 : ℝ)..P, U t * (U t - V t) / V t =
      ∫ t in (0 : ℝ)..P, ((U t - V t) + (U t - V t) ^ 2 / V t) := by
    apply integral_congr
    intro t ht
    rw [← hI] at ht
    exact pointwise (ne_of_gt (hVpos t ht))
  rw [hcongr, integral_add (hU'.sub hV') hw, integral_sub hU' hV'] at hid
  linarith

/-- (2) 指示の平均 ≥ 風速の平均。 -/
theorem mean_ge (hL : 0 < L) (hP : 0 < P) (hU : ContinuousOn U (Icc 0 P))
    (hV : ∀ t ∈ Icc 0 P, HasDerivAt V (U t * (U t - V t) / L) t)
    (hVpos : ∀ t ∈ Icc 0 P, 0 < V t) (hper : V P = V 0) :
    (∫ t in (0 : ℝ)..P, U t) ≤ ∫ t in (0 : ℝ)..P, V t := by
  have h := excess_eq hL hP hU hV hVpos hper
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..P, (U t - V t) ^ 2 / V t := by
    apply integral_nonneg hP.le
    intro t ht
    have := hVpos t ht
    positivity
  linarith

/-- (3) 等号 ⇔ [0, P] で U = V。 -/
theorem mean_eq_iff_eq (hL : 0 < L) (hP : 0 < P) (hU : ContinuousOn U (Icc 0 P))
    (hV : ∀ t ∈ Icc 0 P, HasDerivAt V (U t * (U t - V t) / L) t)
    (hVpos : ∀ t ∈ Icc 0 P, 0 < V t) (hper : V P = V 0) :
    (∫ t in (0 : ℝ)..P, V t) = (∫ t in (0 : ℝ)..P, U t) ↔ ∀ t ∈ Icc 0 P, U t = V t := by
  have h := excess_eq hL hP hU hV hVpos hper
  have hVc := V_cont hV
  have hwc : ContinuousOn (fun t => (U t - V t) ^ 2 / V t) (Icc 0 P) :=
    ((hU.sub hVc).pow 2).div hVc (fun t ht => ne_of_gt (hVpos t ht))
  constructor
  · intro heq
    by_contra hne
    push Not at hne
    obtain ⟨t₀, ht₀, hne₀⟩ := hne
    have hpos : 0 < (U t₀ - V t₀) ^ 2 / V t₀ := by
      have := hVpos t₀ ht₀
      have : U t₀ - V t₀ ≠ 0 := sub_ne_zero.mpr hne₀
      positivity
    have hlt := integral_lt_integral_of_continuousOn_of_le_of_exists_lt (f := fun _ => (0 : ℝ))
      hP continuousOn_const hwc
      (fun t ht => by
        have := hVpos t (Ioc_subset_Icc_self ht)
        positivity)
      ⟨t₀, ht₀, hpos⟩
    simp only [intervalIntegral.integral_zero] at hlt
    linarith
  · intro heq
    have : ∫ t in (0 : ℝ)..P, (U t - V t) ^ 2 / V t = ∫ t in (0 : ℝ)..P, (0 : ℝ) :=
      integral_congr (fun t ht => by rw [uIcc_of_le hP.le] at ht; simp [heq t ht])
    rw [intervalIntegral.integral_zero] at this
    linarith

/-- (3) U = V なら U は [0, P] で一定。 -/
theorem const_of_eq (hV : ∀ t ∈ Icc 0 P, HasDerivAt V (U t * (U t - V t) / L) t)
    (heq : ∀ t ∈ Icc 0 P, U t = V t) : ∀ t ∈ Icc 0 P, U t = U 0 := by
  have hd : ∀ t ∈ Icc 0 P, HasDerivAt V 0 t := by
    intro t ht
    have := hV t ht
    rwa [heq t ht, sub_self, mul_zero, zero_div] at this
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc 0 P := ⟨le_rfl, le_trans ht.1 ht.2⟩
  rw [heq t ht, heq 0 h0]
  exact const_on hd t ht

/-- (3) U が一定 c なら、周期の解は V ≡ c しかない。 -/
theorem eq_of_const {c : ℝ} (hL : 0 < L) (hP : 0 < P) (hc : 0 < c)
    (hV : ∀ t ∈ Icc 0 P, HasDerivAt V (U t * (U t - V t) / L) t) (hper : V P = V 0)
    (hconst : ∀ t ∈ Icc 0 P, U t = c) : ∀ t ∈ Icc 0 P, V t = c := by
  -- (V − c)·e^(ct/L) は一定
  have hd : ∀ t ∈ Icc 0 P, HasDerivAt (fun s => (V s - c) * exp (c * s / L)) 0 t := by
    intro t ht
    have h1 := (hV t ht).sub_const c
    have h2 : HasDerivAt (fun s => exp (c * s / L)) (exp (c * t / L) * (c / L)) t := by
      have := (((hasDerivAt_id' t).const_mul c).div_const L).exp
      convert this using 1
      ring
    have := h1.mul h2
    convert this using 1
    rw [hconst t ht]
    field_simp
    ring
  have hk := const_on hd
  have hP' : P ∈ Icc 0 P := ⟨hP.le, le_rfl⟩
  have hPv := hk P hP'
  simp only [mul_zero, zero_div, exp_zero, mul_one] at hPv
  rw [hper] at hPv
  have hexp : 1 < exp (c * P / L) := by
    rw [← exp_zero]; exact exp_lt_exp.mpr (by positivity)
  have hV0 : V 0 = c := by
    have : (V 0 - c) * (exp (c * P / L) - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  intro t ht
  have := hk t ht
  simp only [mul_zero, zero_div, exp_zero, mul_one, hV0, sub_self] at this
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h (ne_of_gt (exp_pos _))

/-- (3) まとめ：等号 ⇔ 風が [0, P] で一定。 -/
theorem mean_eq_iff_const (hL : 0 < L) (hP : 0 < P) (hU : ContinuousOn U (Icc 0 P))
    (hUpos : ∀ t ∈ Icc 0 P, 0 < U t)
    (hV : ∀ t ∈ Icc 0 P, HasDerivAt V (U t * (U t - V t) / L) t)
    (hVpos : ∀ t ∈ Icc 0 P, 0 < V t) (hper : V P = V 0) :
    (∫ t in (0 : ℝ)..P, V t) = (∫ t in (0 : ℝ)..P, U t) ↔ ∀ t ∈ Icc 0 P, U t = U 0 := by
  rw [mean_eq_iff_eq hL hP hU hV hVpos hper]
  constructor
  · exact const_of_eq hV
  · intro hconst t ht
    have h0 : (0 : ℝ) ∈ Icc 0 P := ⟨le_rfl, hP.le⟩
    rw [hconst t ht, eq_of_const hL hP (hUpos 0 h0) hV hper hconst t ht]

end Model

/-- (4) 追いつく時間が一定の対照では、二つの平均はちょうど等しい。 -/
theorem fixed_tau {τ P : ℝ} {U V : ℝ → ℝ} (hτ : 0 < τ) (hP : 0 < P)
    (hU : ContinuousOn U (Icc 0 P)) (hV : ∀ t ∈ Icc 0 P, HasDerivAt V ((U t - V t) / τ) t)
    (hper : V P = V 0) :
    (∫ t in (0 : ℝ)..P, V t) = ∫ t in (0 : ℝ)..P, U t := by
  have hVc : ContinuousOn V (Icc 0 P) := fun t ht => (hV t ht).continuousAt.continuousWithinAt
  have hI : Icc 0 P = uIcc 0 P := (uIcc_of_le hP.le).symm
  have hU' : IntervalIntegrable U volume 0 P := by rw [hI] at hU; exact hU.intervalIntegrable
  have hV' : IntervalIntegrable V volume 0 P := by rw [hI] at hVc; exact hVc.intervalIntegrable
  have hftc := integral_eq_sub_of_hasDerivAt (f := V) (f' := fun t => (U t - V t) / τ)
    (fun t ht => by rw [← hI] at ht; exact hV t ht) ((hU'.sub hV').div_const τ)
  rw [hper, sub_self, intervalIntegral.integral_div, integral_sub hU' hV'] at hftc
  have := (div_eq_zero_iff.mp hftc).resolve_right (ne_of_gt hτ)
  linarith

end Paper890

end Yamagishi
