/-
論文557『歯を強くする角度は、伝動をなめらかにする角度と逆を向いている』の格上げ（一般の形）。

原稿（557_yamagishi_strength_points_against_smoothness/…_jp.tex）は、標準歯形の平歯車のかみ合い率
ε = (√(r_a1² − r_b1²) + √(r_a2² − r_b2²) − a sin α)/(πm cos α) を、歯数 20 と 40 で圧力角 14.5〜30 度の
6 点、20 度で 5 組の歯数について数え、かみ合い率が 1 になる歯たけ 0.572468 モジュールを二分法で出す。
単調性は表から読むだけ。

ここで証明した言明（モジュールを単位にして、ピッチ円の半径 r = z/2、歯先円の半径 R = z/2 + h_a、
各歯車の寄与 g(α) = (√(R² − r² cos²α) − r sin α)/(π cos α)、ε = g_{z₁} + g_{z₂}）：
  (0) `eps_eq_paper`：原稿の式 ε はモジュール m によらず g_{z₁} + g_{z₂} に等しい。
  (1) `hasDerivAt_g`：g′(α) = (A − r sin α)(A sin α − r cos²α)/(πA cos²α)、A = √(R² − r² cos²α)。
  (2) `g_strictAntiOn`・`g_strictMonoOn`：各歯車の寄与は α* = arctan(r/R) = arctan(z/(z + 2h_a)) の手前
      [0, α*] で狭義に減り、先 [α*, π/2) で狭義に増える（谷はただ一つ）。
  (3) `g_strictMono_r`：どの α ∈ [0, π/2) でも、g は歯数について狭義に増える
      （芯は (h + r sin²α)² − sin²α·A² = h²cos²α > 0）。
  (4) `eps_strictAntiOn`：ε は α ∈ [0, arctan(z_min/(z_min + 2h_a))] で圧力角について狭義に減る。
      `eps_strictMono_z₁`：ε はどの α でも各歯数について狭義に増える。
  (5) `valley_six`：並歯（h_a = 1）・歯数 6 なら tan α* = 3/4（36.87 度）。
足した仮定：h_a > 0、z > 0、0 ≤ α < π/2。式が実際のかみ合い率に等しいのは干渉が無いときだけである
（原稿の 14.5 度の 20/40、20 度の 10/20 と 12/24 は干渉の範囲にあり、そこでの値は式の値）。
式の上では α → 90 度で ε → ∞ になり、単調減少は全域では偽（谷の先で増える）。
形式化していないもの：干渉と歯先のとがりの範囲、表の数値、歯たけ 0.572468、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）

For a standard spur gear the contribution of one gear to the contact ratio has a single minimum
at tan α = z/(z + 2h_a), falling before it and rising after it, and it rises strictly with the
number of teeth; so the contact ratio falls with the pressure angle up to
arctan(z_min/(z_min + 2h_a)).
-/
import Mathlib

namespace Yamagishi

namespace Paper557

open Real Set

/-- 一つの歯車の寄与（r はピッチ円、R は歯先円の半径、モジュールが単位）。 -/
noncomputable def g (r R α : ℝ) : ℝ := (√(R ^ 2 - r ^ 2 * cos α ^ 2) - r * sin α) / (π * cos α)

/-- かみ合い率。 -/
noncomputable def eps (z₁ z₂ h α : ℝ) : ℝ := g (z₁ / 2) (z₁ / 2 + h) α + g (z₂ / 2) (z₂ / 2 + h) α

/-- (0) 原稿の式（モジュール m、中心距離 a = m(z₁ + z₂)/2）は eps に等しい。 -/
theorem eps_eq_paper {m z₁ z₂ h α : ℝ} (hm : 0 < m) (hc : 0 < cos α) :
    (√((m * (z₁ / 2 + h)) ^ 2 - (m * (z₁ / 2) * cos α) ^ 2) +
      √((m * (z₂ / 2 + h)) ^ 2 - (m * (z₂ / 2) * cos α) ^ 2) - m * (z₁ + z₂) / 2 * sin α) /
        (π * m * cos α) = eps z₁ z₂ h α := by
  have e : ∀ r R : ℝ, √((m * R) ^ 2 - (m * r * cos α) ^ 2) = m * √(R ^ 2 - r ^ 2 * cos α ^ 2) := by
    intro r R
    rw [show (m * R) ^ 2 - (m * r * cos α) ^ 2 = m ^ 2 * (R ^ 2 - r ^ 2 * cos α ^ 2) by ring,
      sqrt_mul (sq_nonneg m), sqrt_sq hm.le]
  rw [e, e]
  unfold eps g
  have hp := pi_pos
  field_simp
  ring

/-- A² > (r sin α)²、したがって A > r sin α（0 ≤ r < R）。 -/
theorem A_gt {r R α : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    0 < R ^ 2 - r ^ 2 * cos α ^ 2 ∧ r * sin α < √(R ^ 2 - r ^ 2 * cos α ^ 2) := by
  have hs := sin_sq_add_cos_sq α
  have hq : (r * sin α) ^ 2 < R ^ 2 - r ^ 2 * cos α ^ 2 := by nlinarith
  have hq0 : 0 < R ^ 2 - r ^ 2 * cos α ^ 2 := by nlinarith [sq_nonneg (r * sin α)]
  exact ⟨hq0, lt_sqrt_of_sq_lt hq⟩

/-- (1) g の α についての導関数。 -/
theorem hasDerivAt_g {r R α : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hc : 0 < cos α) :
    HasDerivAt (g r R)
      ((√(R ^ 2 - r ^ 2 * cos α ^ 2) - r * sin α) *
          (√(R ^ 2 - r ^ 2 * cos α ^ 2) * sin α - r * cos α ^ 2) /
        (π * √(R ^ 2 - r ^ 2 * cos α ^ 2) * cos α ^ 2)) α := by
  obtain ⟨hq0, -⟩ := A_gt (α := α) hr hrR
  have hA : 0 < √(R ^ 2 - r ^ 2 * cos α ^ 2) := sqrt_pos.mpr hq0
  have hq : HasDerivAt (fun x => R ^ 2 - r ^ 2 * cos x ^ 2)
      (-(r ^ 2 * (2 * cos α * (-sin α)))) α := by
    have := ((hasDerivAt_cos α).pow 2).const_mul (r ^ 2)
    have h2 := this.const_sub (R ^ 2)
    convert h2 using 1
    simp
  have hsq := hq.sqrt hq0.ne'
  have hN := hsq.sub ((hasDerivAt_sin α).const_mul r)
  have hD := (hasDerivAt_cos α).const_mul π
  have h := hN.div hD (by positivity)
  unfold g
  convert h using 1
  simp only [Pi.sub_apply]
  have hp := pi_pos
  field_simp
  ring

/-- 谷の位置の判定：0 < α < π/2 で R sin α < r cos α ⇔ α < arctan(r/R)。 -/
theorem below_valley_iff {r R α : ℝ} (hR : 0 < R) (h0 : 0 < α) (h1 : α < π / 2) :
    R * sin α < r * cos α ↔ α < arctan (r / R) := by
  have hc : 0 < cos α := cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have ht : tan α = sin α / cos α := tan_eq_sin_div_cos α
  have e : R * sin α < r * cos α ↔ tan α < r / R := by
    rw [ht, div_lt_div_iff₀ hc hR]; constructor <;> intro h <;> linarith
  rw [e]
  have hα : arctan (tan α) = α := arctan_tan (by linarith) h1
  constructor
  · intro h; have := arctan_strictMono h; rwa [hα] at this
  · intro h
    rw [← hα] at h
    exact arctan_strictMono.lt_iff_lt.mp h

/-- A sin α − r cos²α の符号は R sin α − r cos α の符号と同じ（0 < α < π/2）。 -/
theorem factor_sign {r R α : ℝ} (hr : 0 ≤ r) (hrR : r < R) (h0 : 0 < α) (h1 : α < π / 2) :
    (√(R ^ 2 - r ^ 2 * cos α ^ 2) * sin α - r * cos α ^ 2 < 0 ↔ R * sin α < r * cos α) ∧
    (0 < √(R ^ 2 - r ^ 2 * cos α ^ 2) * sin α - r * cos α ^ 2 ↔ r * cos α < R * sin α) := by
  obtain ⟨hq0, -⟩ := A_gt (α := α) hr hrR
  have hc : 0 < cos α := cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have hs : 0 < sin α := sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hA2 : √(R ^ 2 - r ^ 2 * cos α ^ 2) ^ 2 = R ^ 2 - r ^ 2 * cos α ^ 2 := sq_sqrt hq0.le
  have hA0 := sqrt_nonneg (R ^ 2 - r ^ 2 * cos α ^ 2)
  set A := √(R ^ 2 - r ^ 2 * cos α ^ 2)
  have hsc := sin_sq_add_cos_sq α
  -- (A s)² − (r c²)² = c²·((R s)² − (r c)²)
  have key : (A * sin α) ^ 2 - (r * cos α ^ 2) ^ 2 =
      ((R * sin α) ^ 2 - (r * cos α) ^ 2) := by
    rw [mul_pow, hA2]; nlinarith [hsc]
  have p1 : 0 ≤ A * sin α := by positivity
  have p2 : 0 ≤ r * cos α ^ 2 := by positivity
  have p3 : 0 ≤ R * sin α := mul_nonneg (by linarith) hs.le
  have p4 : 0 ≤ r * cos α := by positivity
  constructor
  · rw [sub_neg]
    constructor
    · intro h
      have : (A * sin α) ^ 2 < (r * cos α ^ 2) ^ 2 := by nlinarith
      nlinarith
    · intro h
      have : (R * sin α) ^ 2 < (r * cos α) ^ 2 := by nlinarith
      nlinarith
  · rw [sub_pos]
    constructor
    · intro h
      have : (r * cos α ^ 2) ^ 2 < (A * sin α) ^ 2 := by nlinarith
      nlinarith
    · intro h
      have : (r * cos α) ^ 2 < (R * sin α) ^ 2 := by nlinarith
      nlinarith

/-- 谷の角 α* = arctan(r/R) は (0, π/2) の中（0 < r）。 -/
theorem valley_mem {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    0 < arctan (r / R) ∧ arctan (r / R) < π / 2 :=
  ⟨arctan_pos.mpr (div_pos hr hR), arctan_lt_pi_div_two _⟩

/-- (2) g は [0, α*] で狭義に減る。 -/
theorem g_strictAntiOn {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    StrictAntiOn (g r R) (Icc 0 (arctan (r / R))) := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨hv0, hv1⟩ := valley_mem hr hR
  have hd : ∀ α ∈ Icc 0 (arctan (r / R)), HasDerivAt (g r R) _ α := fun α hα =>
    hasDerivAt_g hr.le hrR (cos_pos_of_mem_Ioo ⟨by linarith [hα.1, pi_pos], by linarith [hα.2]⟩)
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    (fun α hα => (hd α hα).continuousAt.continuousWithinAt)
    (fun α hα => (hd α (interior_subset hα)).hasDerivWithinAt)
  intro α hα
  rw [interior_Icc] at hα
  have h1 : α < π / 2 := by linarith [hα.2]
  have hc : 0 < cos α := cos_pos_of_mem_Ioo ⟨by linarith [hα.1, pi_pos], h1⟩
  obtain ⟨hq0, hAr⟩ := A_gt (α := α) hr.le hrR
  have hA : 0 < √(R ^ 2 - r ^ 2 * cos α ^ 2) := sqrt_pos.mpr hq0
  have hneg := ((factor_sign hr.le hrR hα.1 h1).1).mpr
    ((below_valley_iff hR hα.1 h1).mpr hα.2)
  apply div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) hneg) (by positivity)

/-- (2) g は [α*, π/2) で狭義に増える。 -/
theorem g_strictMonoOn {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    StrictMonoOn (g r R) (Ico (arctan (r / R)) (π / 2)) := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨hv0, hv1⟩ := valley_mem hr hR
  have hd : ∀ α ∈ Ico (arctan (r / R)) (π / 2), HasDerivAt (g r R) _ α := fun α hα =>
    hasDerivAt_g hr.le hrR (cos_pos_of_mem_Ioo ⟨by linarith [hα.1, pi_pos], hα.2⟩)
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ico _ _)
    (fun α hα => (hd α hα).continuousAt.continuousWithinAt)
    (fun α hα => (hd α (interior_subset hα)).hasDerivWithinAt)
  intro α hα
  rw [interior_Ico] at hα
  have h0 : 0 < α := by linarith [hα.1]
  have hc : 0 < cos α := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hα.2⟩
  obtain ⟨hq0, hAr⟩ := A_gt (α := α) hr.le hrR
  have hA : 0 < √(R ^ 2 - r ^ 2 * cos α ^ 2) := sqrt_pos.mpr hq0
  have hnot : ¬ (R * sin α < r * cos α) := by
    rw [below_valley_iff hR h0 hα.2]; exact not_lt.mpr hα.1.le
  have hne : R * sin α ≠ r * cos α := by
    intro he
    have ht : tan α = r / R := by
      rw [tan_eq_sin_div_cos, div_eq_div_iff hc.ne' hR.ne']; linarith
    have := arctan_tan (show -(π / 2) < α by linarith [pi_pos]) hα.2
    rw [ht] at this
    linarith [hα.1]
  have hgt : r * cos α < R * sin α := lt_of_le_of_ne (not_lt.mp hnot) (Ne.symm hne)
  have hpos := ((factor_sign hr.le hrR h0 hα.2).2).mpr hgt
  apply div_pos (mul_pos (by linarith) hpos) (by positivity)

/-- (3) どの α ∈ [0, π/2) でも、g は r について狭義に増える（R = r + h、h > 0）。 -/
theorem g_strictMono_r {h α : ℝ} (hh : 0 < h) (hα0 : 0 ≤ α) (hα1 : α < π / 2) :
    StrictMonoOn (fun r => g r (r + h) α) (Ici 0) := by
  have hc : 0 < cos α := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hα1⟩
  have hs : 0 ≤ sin α := sin_nonneg_of_nonneg_of_le_pi hα0 (by linarith)
  have hsc := sin_sq_add_cos_sq α
  have hd : ∀ r ∈ Ici (0 : ℝ), HasDerivAt (fun r => g r (r + h) α)
      (((r + h - r * cos α ^ 2) / √((r + h) ^ 2 - r ^ 2 * cos α ^ 2) - sin α) / (π * cos α)) r := by
    intro r hr
    have hr' : (0 : ℝ) ≤ r := hr
    obtain ⟨hq0, -⟩ := A_gt (α := α) hr' (show r < r + h by linarith)
    have hq : HasDerivAt (fun x => (x + h) ^ 2 - x ^ 2 * cos α ^ 2)
        (2 * (r + h) - 2 * r * cos α ^ 2) r := by
      have h1 := ((hasDerivAt_id' r).add_const h).pow 2
      have h2 := ((hasDerivAt_id' r).pow 2).mul_const (cos α ^ 2)
      convert h1.sub h2 using 1
      simp
    have hsq := hq.sqrt hq0.ne'
    have hN := hsq.sub ((hasDerivAt_id' r).mul_const (sin α))
    have hfin := hN.div_const (π * cos α)
    unfold g
    convert hfin using 1
    have hA : 0 < √((r + h) ^ 2 - r ^ 2 * cos α ^ 2) := sqrt_pos.mpr hq0
    field_simp
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hd r (interior_subset hr)).hasDerivWithinAt)
  intro r hr
  rw [interior_Ici] at hr
  have hr' : (0 : ℝ) < r := hr
  obtain ⟨hq0, -⟩ := A_gt (α := α) hr'.le (show r < r + h by linarith)
  have hA2 : √((r + h) ^ 2 - r ^ 2 * cos α ^ 2) ^ 2 = (r + h) ^ 2 - r ^ 2 * cos α ^ 2 :=
    sq_sqrt hq0.le
  have hA : 0 < √((r + h) ^ 2 - r ^ 2 * cos α ^ 2) := sqrt_pos.mpr hq0
  set A := √((r + h) ^ 2 - r ^ 2 * cos α ^ 2)
  -- 芯：(h + r sin²α)² − sin²α·A² = h² cos²α > 0
  have key : (h + r * sin α ^ 2) ^ 2 - (sin α * A) ^ 2 = h ^ 2 * cos α ^ 2 := by
    rw [mul_pow, hA2]; linear_combination (r ^ 2 * sin α ^ 2 - h ^ 2) * hsc
  have hpos1 : 0 < h + r * sin α ^ 2 := by positivity
  have hpos2 : 0 ≤ sin α * A := by positivity
  have hlt : sin α * A < h + r * sin α ^ 2 := by
    have : (sin α * A) ^ 2 < (h + r * sin α ^ 2) ^ 2 := by
      have : 0 < h ^ 2 * cos α ^ 2 := by positivity
      linarith
    nlinarith
  apply div_pos _ (by positivity)
  rw [sub_pos, lt_div_iff₀ hA]
  have e : r + h - r * cos α ^ 2 = h + r * sin α ^ 2 := by linear_combination (-r) * hsc
  rw [e]
  linarith

/-- (4) ε は α ∈ [0, arctan(z_min/(z_min + 2h))] で狭義に減る（z₁ ≤ z₂ のとき z_min = z₁）。 -/
theorem eps_strictAntiOn {z₁ z₂ h : ℝ} (hz₁ : 0 < z₁) (h12 : z₁ ≤ z₂) (hh : 0 < h) :
    StrictAntiOn (eps z₁ z₂ h) (Icc 0 (arctan (z₁ / (z₁ + 2 * h)))) := by
  have e : ∀ z : ℝ, 0 < z → (z / 2) / (z / 2 + h) = z / (z + 2 * h) := by
    intro z hz; field_simp
  have hz₂ : 0 < z₂ := lt_of_lt_of_le hz₁ h12
  have a1 := g_strictAntiOn (r := z₁ / 2) (R := z₁ / 2 + h) (by positivity) (by linarith)
  have a2 := g_strictAntiOn (r := z₂ / 2) (R := z₂ / 2 + h) (by positivity) (by linarith)
  rw [e z₁ hz₁] at a1
  rw [e z₂ hz₂] at a2
  -- 谷の角は歯数について増える
  have hv : arctan (z₁ / (z₁ + 2 * h)) ≤ arctan (z₂ / (z₂ + 2 * h)) := by
    apply arctan_strictMono.monotone
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  intro x hx y hy hxy
  have hx2 : x ∈ Icc 0 (arctan (z₂ / (z₂ + 2 * h))) := ⟨hx.1, hx.2.trans hv⟩
  have hy2 : y ∈ Icc 0 (arctan (z₂ / (z₂ + 2 * h))) := ⟨hy.1, hy.2.trans hv⟩
  unfold eps
  have := a1 hx hy hxy
  have := a2 hx2 hy2 hxy
  linarith

/-- (4) ε はどの α ∈ [0, π/2) でも歯数 z₁ について狭義に増える。 -/
theorem eps_strictMono_z₁ {z₂ h α : ℝ} (hh : 0 < h) (hα0 : 0 ≤ α) (hα1 : α < π / 2) :
    StrictMonoOn (fun z => eps z z₂ h α) (Ici 0) := by
  intro x hx y hy hxy
  have hm := g_strictMono_r hh hα0 hα1
  have : g (x / 2) (x / 2 + h) α < g (y / 2) (y / 2 + h) α :=
    hm (show x / 2 ∈ Ici (0 : ℝ) by simp only [mem_Ici] at hx ⊢; linarith)
      (show y / 2 ∈ Ici (0 : ℝ) by simp only [mem_Ici] at hy ⊢; linarith)
      (by linarith)
  unfold eps
  linarith

/-- (5) 並歯（h = 1）・歯数 6 なら谷は tan α* = 3/4（36.87 度）。 -/
theorem valley_six : (6 : ℝ) / (6 + 2 * 1) = 3 / 4 := by norm_num

end Paper557

end Yamagishi
