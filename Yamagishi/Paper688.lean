/-
論文688『地球の内部は、届いた波ではなく、届かなかった波から分かった』の格上げ（芯だけ）。

日本語の一文：球対称の媒質で、核をかすめる射線の震央距離を射線の積分の式で書いたものを入力に置くと、
核の外の速さがどこでも核の縁の速さを越えないなら、その距離は直線の 2 arccos(r_c/R) 以下で、等号は
速さがほとんど至る所で核の縁の速さに等しいときに限り、直線と置いて逆算した核の半径 R cos(Δ/2) は
真の半径以上になる。
English: Core only: taking the ray-integral formula for the epicentral distance of the ray grazing
the core as input, if the speed outside the core never exceeds its value at the core boundary, the
distance is at most the straight-line value 2 arccos(r_c/R), with equality iff the speed equals the
boundary value almost everywhere, so the radius R cos(Δ/2) inferred with straight rays is at least
the true core radius; for v ∝ √r the distance is 2 arccos(2r_c/R − 1), beyond the straight-line
value.

原稿（688_yamagishi_the_interior_was_read_from_the_waves_that_did_not_arrive/…_jp.tex）は、半径の比
0.546225 で直線の接する距離 113.783157 度、観測の影の始まり 103 度から直線で逆算した核の半径
3966.0408 km（真の値と 0.139667 の食い違い）を出し、観察 2.4 で「直線近似は核を実際より大きく見積もる
（深いほど速いので）」と言葉で述べている。一般の証明は無い。

ここで証明した言明（0 < r_c < R、v は (r_c, R] で正で測れる関数、v_c = v(r_c) > 0）：
  (1) `integrand_le`：r_c < r で v(r) ≤ v_c なら、射線の被積分関数 p/(r√(η² − p²))
      （η = r/v(r)、p = r_c/v_c）は直線の被積分関数 r_c/(r√(r² − r_c²)) 以下。
      `integrand_lt`：v(r) < v_c なら真に小さい。`integrand_const`：v(r) = v_c なら等しい。
  (2) `integral_straight`：∫_{r_c}^{R} r_c/(r√(r² − r_c²)) dr = arccos(r_c/R)（端で発散する広義の積分）。
  (3) `grazing_le`：(r_c, R] で v ≤ v_c なら Δ ≤ 2 arccos(r_c/R)。
      `grazing_eq_iff`：等号 ⇔ (r_c, R] のほとんど至る所で v = v_c。
  (4) `radius_ge`：直線と置いて逆算した半径 R cos(Δ/2) は r_c 以上。
      `radius_gt`：v = v_c がほとんど至る所では成り立たないなら、真に大きい（核を大きく見積もる）。
  (5) `sqrt_profile`：条件は外せない。v(r) = √r（外ほど速い）では Δ = 2 arccos(2r_c/R − 1) で、
      これは直線の 2 arccos(r_c/R) より真に大きい（半径の比 0.546225 で約 169 度）。
足した仮定（ここが「芯だけ」の理由）：かすめる射線の震央距離を、射線の母数 p = r sin i/v(r) が保たれる
こと（ベンドルフの関係）から出る積分の式 Δ = 2∫_{r_c}^{R} p dr/(r√(η² − p²)) として定義に置いた。
射線の式の導き方（スネルの法則から）、観測の影の始まりがかすめる射線と一致すること（Δ(p) が単調で
三重化が無いこと、回折を入れないこと）は形式化していない。震源は表面に置く。
形式化していないもの：原稿の数（113.783157 度・3966.0408 km・影の面積の割合・体積比）、分離子の読み。
論文824 は同じ言明を「連続な速さの分布で、等号は速さが一定のときだけ」と言い換えたもので、
`Yamagishi/Paper824.lean` がこのファイルを読み込んで導く。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper688

open Real Set MeasureTheory intervalIntegral

/-- かすめる射線（母数 p = r_c/v(r_c)）の被積分関数 p/(r√(η(r)² − p²))、η(r) = r/v(r)。 -/
noncomputable def integrand (v : ℝ → ℝ) (rc r : ℝ) : ℝ :=
  (rc / v rc) / (r * √((r / v r) ^ 2 - (rc / v rc) ^ 2))

/-- かすめる射線の震央距離 Δ = 2∫_{r_c}^{R} p dr/(r√(η² − p²))（射線の積分の式を定義として置く）。 -/
noncomputable def Delta (v : ℝ → ℝ) (rc R : ℝ) : ℝ := 2 * ∫ r in rc..R, integrand v rc r

/-- 直線（速さ一定）の被積分関数 r_c/(r√(r² − r_c²))。 -/
noncomputable def straight (rc r : ℝ) : ℝ := rc / (r * √(r ^ 2 - rc ^ 2))

theorem integrand_nonneg {v : ℝ → ℝ} {rc r : ℝ} (hrc : 0 < rc) (hvc : 0 < v rc) (hr : 0 ≤ r) :
    0 ≤ integrand v rc r := by
  unfold integrand
  apply div_nonneg (div_pos hrc hvc).le
  exact mul_nonneg hr (sqrt_nonneg _)

theorem straight_nonneg {rc r : ℝ} (hrc : 0 < rc) (hr : 0 ≤ r) : 0 ≤ straight rc r := by
  unfold straight
  exact div_nonneg hrc.le (mul_nonneg hr (sqrt_nonneg _))

/-- 速さが v_c のとき、根号の中は (r² − r_c²)/v_c²。 -/
theorem inner_ge {v : ℝ → ℝ} {rc r : ℝ} (hr : 0 < r) (hv : 0 < v r) (hvc : 0 < v rc)
    (hle : v r ≤ v rc) :
    (r ^ 2 - rc ^ 2) / v rc ^ 2 ≤ (r / v r) ^ 2 - (rc / v rc) ^ 2 := by
  have h1 : r / v rc ≤ r / v r := div_le_div_of_nonneg_left hr.le hv hle
  have h2 : (r / v rc) ^ 2 ≤ (r / v r) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have : (r ^ 2 - rc ^ 2) / v rc ^ 2 = (r / v rc) ^ 2 - (rc / v rc) ^ 2 := by
    field_simp
  linarith

theorem inner_gt {v : ℝ → ℝ} {rc r : ℝ} (hr : 0 < r) (hv : 0 < v r) (hvc : 0 < v rc)
    (hlt : v r < v rc) :
    (r ^ 2 - rc ^ 2) / v rc ^ 2 < (r / v r) ^ 2 - (rc / v rc) ^ 2 := by
  have h1 : r / v rc < r / v r := div_lt_div_of_pos_left hr hv hlt
  have h2 : (r / v rc) ^ 2 < (r / v r) ^ 2 := pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
  have : (r ^ 2 - rc ^ 2) / v rc ^ 2 = (r / v rc) ^ 2 - (rc / v rc) ^ 2 := by
    field_simp
  linarith

theorem sqrt_div_sq {x c : ℝ} (hc : 0 < c) : √(x / c ^ 2) = √x / c := by
  rw [sqrt_div' x (sq_nonneg c), sqrt_sq hc.le]

/-- 直線の被積分関数を p と v_c で書き直す。 -/
theorem straight_eq {rc r c : ℝ} (hrc : 0 ≤ rc) (hc : 0 < c) (hr : 0 < r) (hrr : rc < r) :
    straight rc r = (rc / c) / (r * √((r ^ 2 - rc ^ 2) / c ^ 2)) := by
  unfold straight
  rw [sqrt_div_sq hc]
  have : 0 < √(r ^ 2 - rc ^ 2) := sqrt_pos.mpr (by nlinarith)
  field_simp

/-- (1) 被積分関数は直線のもの以下。 -/
theorem integrand_le {v : ℝ → ℝ} {rc r : ℝ} (hrc : 0 < rc) (hrr : rc < r) (hv : 0 < v r)
    (hvc : 0 < v rc) (hle : v r ≤ v rc) : integrand v rc r ≤ straight rc r := by
  have hr : 0 < r := hrc.trans hrr
  rw [straight_eq hrc.le hvc hr hrr]
  unfold integrand
  have hin := inner_ge hr hv hvc hle
  have hpos : 0 < (r ^ 2 - rc ^ 2) / v rc ^ 2 := div_pos (by nlinarith) (by positivity)
  have hs : √((r ^ 2 - rc ^ 2) / v rc ^ 2) ≤ √((r / v r) ^ 2 - (rc / v rc) ^ 2) := sqrt_le_sqrt hin
  have hs0 : 0 < √((r ^ 2 - rc ^ 2) / v rc ^ 2) := sqrt_pos.mpr hpos
  apply div_le_div_of_nonneg_left (div_pos hrc hvc).le (mul_pos hr hs0)
  exact mul_le_mul_of_nonneg_left hs hr.le

theorem integrand_lt {v : ℝ → ℝ} {rc r : ℝ} (hrc : 0 < rc) (hrr : rc < r) (hv : 0 < v r)
    (hvc : 0 < v rc) (hlt : v r < v rc) : integrand v rc r < straight rc r := by
  have hr : 0 < r := hrc.trans hrr
  rw [straight_eq hrc.le hvc hr hrr]
  unfold integrand
  have hin := inner_gt hr hv hvc hlt
  have hpos : 0 < (r ^ 2 - rc ^ 2) / v rc ^ 2 := div_pos (by nlinarith) (by positivity)
  have hs : √((r ^ 2 - rc ^ 2) / v rc ^ 2) < √((r / v r) ^ 2 - (rc / v rc) ^ 2) :=
    sqrt_lt_sqrt hpos.le hin
  have hs0 : 0 < √((r ^ 2 - rc ^ 2) / v rc ^ 2) := sqrt_pos.mpr hpos
  apply div_lt_div_of_pos_left (div_pos hrc hvc) (mul_pos hr hs0)
  exact mul_lt_mul_of_pos_left hs hr

theorem integrand_const {v : ℝ → ℝ} {rc r : ℝ} (hrc : 0 < rc) (hrr : rc < r)
    (hvc : 0 < v rc) (heq : v r = v rc) : integrand v rc r = straight rc r := by
  have hr : 0 < r := hrc.trans hrr
  rw [straight_eq hrc.le hvc hr hrr]
  unfold integrand
  rw [heq]
  congr 3
  field_simp

/-- arccos(r_c/r) の微分は直線の被積分関数。 -/
theorem hasDerivAt_arccos_div {rc r : ℝ} (hrc : 0 < rc) (hrr : rc < r) :
    HasDerivAt (fun x => arccos (rc / x)) (straight rc r) r := by
  have hr : 0 < r := hrc.trans hrr
  have hx1 : rc / r < 1 := (div_lt_one hr).mpr hrr
  have hx0 : 0 < rc / r := div_pos hrc hr
  have h1 : HasDerivAt (fun x => rc / x) ((0 * r - rc * 1) / r ^ 2) r :=
    (hasDerivAt_const r rc).div (hasDerivAt_id' r) (ne_of_gt hr)
  have h2 := (hasDerivAt_arccos (by linarith) (ne_of_lt hx1)).comp r h1
  refine HasDerivAt.congr_deriv h2 ?_
  unfold straight
  have hsq : r ^ 2 - rc ^ 2 = r ^ 2 * (1 - (rc / r) ^ 2) := by field_simp
  rw [hsq, sqrt_mul (sq_nonneg r), sqrt_sq hr.le]
  have : 0 < √(1 - (rc / r) ^ 2) := sqrt_pos.mpr (by nlinarith)
  field_simp
  ring

theorem continuousOn_arccos_div {rc R : ℝ} (hrc : 0 < rc) :
    ContinuousOn (fun x => arccos (rc / x)) (Icc rc R) := by
  apply continuous_arccos.comp_continuousOn
  apply continuousOn_const.div continuousOn_id
  intro x hx; exact ne_of_gt (hrc.trans_le hx.1)

theorem intervalIntegrable_straight {rc R : ℝ} (hrc : 0 < rc) (hR : rc ≤ R) :
    IntervalIntegrable (straight rc) volume rc R := by
  apply intervalIntegrable_deriv_of_nonneg (g := fun x => arccos (rc / x))
  · rw [uIcc_of_le hR]; exact continuousOn_arccos_div hrc
  · intro x hx
    rw [min_eq_left hR, max_eq_right hR] at hx
    exact hasDerivAt_arccos_div hrc hx.1
  · intro x hx
    rw [min_eq_left hR, max_eq_right hR] at hx
    exact straight_nonneg hrc (hrc.trans hx.1).le

/-- (2) 直線の積分は arccos(r_c/R)。 -/
theorem integral_straight {rc R : ℝ} (hrc : 0 < rc) (hR : rc ≤ R) :
    ∫ r in rc..R, straight rc r = arccos (rc / R) := by
  rw [integral_eq_sub_of_hasDerivAt_of_le hR (continuousOn_arccos_div hrc)
    (fun x hx => hasDerivAt_arccos_div hrc hx.1) (intervalIntegrable_straight hrc hR)]
  rw [div_self (ne_of_gt hrc), arccos_one, sub_zero]

/-- 被積分関数は (r_c, R] で測れる。 -/
theorem aestronglyMeasurable_integrand {v : ℝ → ℝ} {rc R : ℝ}
    (hm : AEMeasurable v (volume.restrict (Ioc rc R))) :
    AEStronglyMeasurable (integrand v rc) (volume.restrict (Ioc rc R)) := by
  unfold integrand
  apply AEMeasurable.aestronglyMeasurable
  apply aemeasurable_const.div
  apply aemeasurable_id.mul
  apply continuous_sqrt.measurable.comp_aemeasurable
  exact ((aemeasurable_id.div hm).pow_const 2).sub_const _

theorem intervalIntegrable_integrand {v : ℝ → ℝ} {rc R : ℝ} (hrc : 0 < rc) (hR : rc ≤ R)
    (hm : AEMeasurable v (volume.restrict (Ioc rc R)))
    (hpos : ∀ r ∈ Ioc rc R, 0 < v r) (hvc : 0 < v rc) (hle : ∀ r ∈ Ioc rc R, v r ≤ v rc) :
    IntervalIntegrable (integrand v rc) volume rc R := by
  apply (intervalIntegrable_straight hrc hR).mono_fun
  · rw [uIoc_of_le hR]; exact aestronglyMeasurable_integrand hm
  · rw [uIoc_of_le hR]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := (hrc.trans hr.1).le
    rw [Real.norm_of_nonneg (integrand_nonneg hrc hvc hr0),
      Real.norm_of_nonneg (straight_nonneg hrc hr0)]
    exact integrand_le hrc hr.1 (hpos r hr) hvc (hle r hr)

/-- (3) Δ ≤ 2 arccos(r_c/R)。 -/
theorem grazing_le {v : ℝ → ℝ} {rc R : ℝ} (hrc : 0 < rc) (hR : rc < R)
    (hm : AEMeasurable v (volume.restrict (Ioc rc R)))
    (hpos : ∀ r ∈ Ioc rc R, 0 < v r) (hvc : 0 < v rc) (hle : ∀ r ∈ Ioc rc R, v r ≤ v rc) :
    Delta v rc R ≤ 2 * arccos (rc / R) := by
  unfold Delta
  rw [← integral_straight hrc hR.le]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply integral_mono_ae_restrict hR.le
    (intervalIntegrable_integrand hrc hR.le hm hpos hvc hle) (intervalIntegrable_straight hrc hR.le)
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  have hnull : ∀ᵐ r ∂volume, r ≠ rc := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hnull] with r hne hr
  exact integrand_le hrc (lt_of_le_of_ne hr.1 (Ne.symm hne)) (hpos r ⟨lt_of_le_of_ne hr.1
    (Ne.symm hne), hr.2⟩) hvc (hle r ⟨lt_of_le_of_ne hr.1 (Ne.symm hne), hr.2⟩)

theorem Delta_nonneg {v : ℝ → ℝ} {rc R : ℝ} (hrc : 0 < rc) (hR : rc ≤ R) (hvc : 0 < v rc) :
    0 ≤ Delta v rc R := by
  unfold Delta
  apply mul_nonneg (by norm_num)
  apply integral_nonneg hR
  intro r hr
  exact integrand_nonneg hrc hvc (hrc.le.trans hr.1)

/-- (3) 等号 ⇔ (r_c, R] のほとんど至る所で v = v_c。 -/
theorem grazing_eq_iff {v : ℝ → ℝ} {rc R : ℝ} (hrc : 0 < rc) (hR : rc < R)
    (hm : AEMeasurable v (volume.restrict (Ioc rc R)))
    (hpos : ∀ r ∈ Ioc rc R, 0 < v r) (hvc : 0 < v rc) (hle : ∀ r ∈ Ioc rc R, v r ≤ v rc) :
    Delta v rc R = 2 * arccos (rc / R) ↔ ∀ᵐ r ∂(volume.restrict (Ioc rc R)), v r = v rc := by
  unfold Delta
  rw [← integral_straight hrc hR.le]
  have hfi := intervalIntegrable_integrand hrc hR.le hm hpos hvc hle
  have hgi := intervalIntegrable_straight hrc hR.le
  rw [intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_of_le hR.le]
  have hfle : integrand v rc ≤ᵐ[volume.restrict (Ioc rc R)] straight rc := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact integrand_le hrc hr.1 (hpos r hr) hvc (hle r hr)
  have key := integral_eq_iff_of_ae_le ((intervalIntegrable_iff_integrableOn_Ioc_of_le
    hR.le).mp hfi) ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mp hgi) hfle
  constructor
  · intro h
    have h2 : ∫ r in Ioc rc R, integrand v rc r = ∫ r in Ioc rc R, straight rc r := by linarith
    have hae := key.mp h2
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with r he hr
    by_contra hne
    have := integrand_lt hrc hr.1 (hpos r hr) hvc (lt_of_le_of_ne (hle r hr) hne)
    rw [he] at this
    exact lt_irrefl _ this
  · intro h
    have hae : integrand v rc =ᵐ[volume.restrict (Ioc rc R)] straight rc := by
      filter_upwards [h, ae_restrict_mem measurableSet_Ioc] with r he hr
      exact integrand_const hrc hr.1 hvc he
    rw [key.mpr hae]

/-- (4) 直線で逆算した半径 R cos(Δ/2) は r_c 以上。 -/
theorem radius_ge {v : ℝ → ℝ} {rc R : ℝ} (hrc : 0 < rc) (hR : rc < R)
    (hm : AEMeasurable v (volume.restrict (Ioc rc R)))
    (hpos : ∀ r ∈ Ioc rc R, 0 < v r) (hvc : 0 < v rc) (hle : ∀ r ∈ Ioc rc R, v r ≤ v rc) :
    rc ≤ R * cos (Delta v rc R / 2) := by
  have hR0 : 0 < R := hrc.trans hR
  have h1 := grazing_le hrc hR hm hpos hvc hle
  have h0 := Delta_nonneg hrc hR.le hvc (v := v)
  have hx : rc / R ∈ Icc (-1 : ℝ) 1 :=
    ⟨by have := div_pos hrc hR0; linarith, (div_le_one hR0).mpr hR.le⟩
  have hc : cos (arccos (rc / R)) ≤ cos (Delta v rc R / 2) := by
    apply cos_le_cos_of_nonneg_of_le_pi (by linarith) (arccos_le_pi _) (by linarith)
  rw [cos_arccos hx.1 hx.2] at hc
  rw [div_le_iff₀ hR0] at hc
  linarith

/-- (4) ほとんど至る所で一定でないなら、核を真に大きく見積もる。 -/
theorem radius_gt {v : ℝ → ℝ} {rc R : ℝ} (hrc : 0 < rc) (hR : rc < R)
    (hm : AEMeasurable v (volume.restrict (Ioc rc R)))
    (hpos : ∀ r ∈ Ioc rc R, 0 < v r) (hvc : 0 < v rc) (hle : ∀ r ∈ Ioc rc R, v r ≤ v rc)
    (hnot : ¬ ∀ᵐ r ∂(volume.restrict (Ioc rc R)), v r = v rc) :
    Delta v rc R < 2 * arccos (rc / R) ∧ rc < R * cos (Delta v rc R / 2) := by
  have hR0 : 0 < R := hrc.trans hR
  have h1 : Delta v rc R < 2 * arccos (rc / R) := lt_of_le_of_ne
    (grazing_le hrc hR hm hpos hvc hle)
    (fun h => hnot ((grazing_eq_iff hrc hR hm hpos hvc hle).mp h))
  have h0 := Delta_nonneg hrc hR.le hvc (v := v)
  have hx : rc / R ∈ Icc (-1 : ℝ) 1 :=
    ⟨by have := div_pos hrc hR0; linarith, (div_le_one hR0).mpr hR.le⟩
  have hc : cos (arccos (rc / R)) < cos (Delta v rc R / 2) := by
    apply cos_lt_cos_of_nonneg_of_le_pi (by linarith) (arccos_le_pi _) (by linarith)
  rw [cos_arccos hx.1 hx.2, div_lt_iff₀ hR0] at hc
  exact ⟨h1, by linarith⟩

/-! ### 条件を外した例：v(r) = √r -/

/-- arccos(2r_c/r − 1) の微分は √r_c/(r√(r − r_c))。 -/
theorem hasDerivAt_sqrt_profile {rc r : ℝ} (hrc : 0 < rc) (hrr : rc < r) :
    HasDerivAt (fun x => arccos (2 * rc / x - 1)) (√rc / (r * √(r - rc))) r := by
  have hr : 0 < r := hrc.trans hrr
  have hx1 : 2 * rc / r - 1 < 1 := by
    have : 2 * rc / r < 2 := by rw [div_lt_iff₀ hr]; linarith
    linarith
  have hx0 : -1 < 2 * rc / r - 1 := by have := div_pos (by linarith : 0 < 2 * rc) hr; linarith
  have h1 : HasDerivAt (fun x => 2 * rc / x - 1) ((0 * r - 2 * rc * 1) / r ^ 2) r :=
    ((hasDerivAt_const r (2 * rc)).div (hasDerivAt_id' r) (ne_of_gt hr)).sub_const 1
  have h2 := (hasDerivAt_arccos (ne_of_gt hx0) (ne_of_lt hx1)).comp r h1
  refine HasDerivAt.congr_deriv h2 ?_
  have hsq : 1 - (2 * rc / r - 1) ^ 2 = (2 / r) ^ 2 * (rc * (r - rc)) := by field_simp; ring
  rw [hsq, sqrt_mul (sq_nonneg _), sqrt_sq (by positivity), sqrt_mul hrc.le]
  have hs1 : 0 < √rc := sqrt_pos.mpr hrc
  have hs2 : 0 < √(r - rc) := sqrt_pos.mpr (by linarith)
  have : √rc * √rc = rc := mul_self_sqrt hrc.le
  field_simp
  nlinarith [this]

/-- (5) v(r) = √r の被積分関数は √r_c/(r√(r − r_c))。 -/
theorem integrand_sqrt {rc r : ℝ} (hrc : 0 < rc) (hrr : rc < r) :
    integrand (fun x => √x) rc r = √rc / (r * √(r - rc)) := by
  have hr : 0 < r := hrc.trans hrr
  unfold integrand
  have e1 : r / √r = √r := by
    have := sqrt_pos.mpr hr
    field_simp
    rw [sq_sqrt hr.le]
  have e2 : rc / √rc = √rc := by
    have := sqrt_pos.mpr hrc
    field_simp
    rw [sq_sqrt hrc.le]
  rw [e1, e2, sq_sqrt hr.le, sq_sqrt hrc.le]

/-- (5) v(r) = √r では Δ = 2 arccos(2r_c/R − 1) > 2 arccos(r_c/R)。 -/
theorem sqrt_profile {rc R : ℝ} (hrc : 0 < rc) (hR : rc < R) :
    Delta (fun x => √x) rc R = 2 * arccos (2 * rc / R - 1) ∧
      2 * arccos (rc / R) < Delta (fun x => √x) rc R := by
  have hR0 : 0 < R := hrc.trans hR
  have hcont : ContinuousOn (fun x => arccos (2 * rc / x - 1)) (Icc rc R) := by
    apply continuous_arccos.comp_continuousOn
    apply ContinuousOn.sub _ continuousOn_const
    apply continuousOn_const.div continuousOn_id
    intro x hx; exact ne_of_gt (hrc.trans_le hx.1)
  have hderiv : ∀ x ∈ Ioo rc R, HasDerivAt (fun x => arccos (2 * rc / x - 1))
      (integrand (fun x => √x) rc x) x := by
    intro x hx
    rw [integrand_sqrt hrc hx.1]
    exact hasDerivAt_sqrt_profile hrc hx.1
  have hint : IntervalIntegrable (integrand (fun x => √x) rc) volume rc R := by
    apply intervalIntegrable_deriv_of_nonneg (g := fun x => arccos (2 * rc / x - 1))
    · rw [uIcc_of_le hR.le]; exact hcont
    · intro x hx
      rw [min_eq_left hR.le, max_eq_right hR.le] at hx
      exact hderiv x hx
    · intro x hx
      rw [min_eq_left hR.le, max_eq_right hR.le] at hx
      rw [integrand_sqrt hrc hx.1]
      exact div_nonneg (sqrt_nonneg _) (mul_nonneg (hrc.trans hx.1).le (sqrt_nonneg _))
  have hval : Delta (fun x => √x) rc R = 2 * arccos (2 * rc / R - 1) := by
    unfold Delta
    rw [integral_eq_sub_of_hasDerivAt_of_le hR.le hcont hderiv hint]
    rw [show 2 * rc / rc - 1 = 1 by field_simp; ring, arccos_one, sub_zero]
  refine ⟨hval, ?_⟩
  rw [hval]
  have hlt : 2 * rc / R - 1 < rc / R := by
    have : rc / R < 1 := (div_lt_one hR0).mpr hR
    have e : 2 * rc / R - 1 = rc / R + (rc / R - 1) := by ring
    linarith
  have hx0 : -1 ≤ 2 * rc / R - 1 := by have := div_pos (by linarith : 0 < 2 * rc) hR0; linarith
  have := arccos_lt_arccos hx0 hlt ((div_le_one hR0).mpr hR.le)
  linarith

end Paper688

end Yamagishi
