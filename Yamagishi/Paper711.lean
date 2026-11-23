/-
論文711『「潤滑を良くするほど滑らかになる」は、谷の手前でだけ正しい』の格上げ（一般の形）。

日本語：摩擦係数の模型 μ(x) = μ_b/(1 + (x/x₀)²) + cx で r = cx₀/μ_b と置くと、膜厚の途中に谷
（極小）があるのは r < 3√3/8 のときだけで、あればただ一つ。谷が乾いた端 μ_b より低いのは
r < 1/2 のときだけ。流体の係数 c を大きくすると、谷は左へ動き、浅くなる。
English: For μ(x) = μ_b/(1 + (x/x₀)²) + cx with r = cx₀/μ_b, an interior minimum exists exactly
when r < 3√3/8 and is then unique; it beats the dry end μ_b exactly when r < 1/2; a larger c moves
it left and makes it shallower.

原稿（711_yamagishi_better_lubrication_holds_only_before_the_minimum/…_jp.tex）は、
μ_b = 0.10、x₀ = 1、c = 0.001 の一組で、x = 0〜30 の 8 点の表（谷 x = 5.73・0.008686）と、
二つの項を別々に見た表を出す。谷の位置と深さが c で動くことは言葉で述べるだけ。観察 3.3 は
「減る項と増える項を足せば、どこかで入れ替わる」と書く。

ここで証明した言明（μ_b, x₀ > 0、c ≥ 0。無次元の形 F(r, s) = 1/(1 + s²) + rs、s = x/x₀、
r = cx₀/μ_b で書き、`mu_eq`：μ(x) = μ_b·F(r, x/x₀) と、`isLocalMin_mu_iff`：μ の極小と F の極小が
対応することも示した）：
  (1) `hasDerivAt_F`：∂F/∂s = r − h(s)、h(s) = 2s/(1 + s²)²。`h_lt_kappa`：s ≥ 0、s ≠ 1/√3 で
      h(s) < 3√3/8 = h(1/√3)。
  (2) `exists_below_iff`・`exists_mu_below_iff`：乾いた端より低い点がある（∃ x > 0, μ(x) < μ_b）
      ⇔ r < 1/2。`endpoint_min_of_ge`：r ≥ 1/2 なら x = 0 が最小。
      `global_min_interior`：0 < r < 1/2 なら全体の最小は内点にある。
  (3) `exists_localMin_iff`・`exists_localMin_mu_iff`：内点の極小がある ⇔ r < 3√3/8。
      `localMin_unique`：あれば、ただ一つ。
  (4) `localMin_monotone`：0 < r < r′ < 3√3/8 で、谷の位置は s′ < s（左へ動く）、谷の深さは
      F(r, s) < F(r′, s′)（浅くなる）。r = cx₀/μ_b なので c について同じ向き。
  (5) `no_valley_example`：r ≥ 3√3/8 では F は単調で谷が無い（「減る項と増える項の和には谷がある」は
      一般には偽）。`dry_end_wins_example`：r = 0.51 では内点に極小があるが、全体の最小は x = 0。
足した仮定：境界の項をローレンツ型 1/(1 + s²) に置いた原稿の模型そのもの（境目の値 1/2 と 3√3/8 は
この形に依る）。
形式化していないもの：谷の位置の近似 (2μ_b x₀²/c)^(1/3)、原稿の表の数値、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper711

open Real Set Filter Topology

/-! ### 模型と無次元の形 -/

/-- 無次元の摩擦係数 F(r, s) = 1/(1 + s²) + rs。 -/
noncomputable def F (r s : ℝ) : ℝ := 1 / (1 + s ^ 2) + r * s

/-- 原稿の模型 μ(x) = μ_b/(1 + (x/x₀)²) + cx。 -/
noncomputable def mu (μb x0 c x : ℝ) : ℝ := μb / (1 + (x / x0) ^ 2) + c * x

theorem mu_eq {μb x0 c : ℝ} (hb : 0 < μb) (h0 : 0 < x0) (x : ℝ) :
    mu μb x0 c x = μb * F (c * x0 / μb) (x / x0) := by
  unfold mu F
  field_simp

/-- h(s) = 2s/(1 + s²)²。 -/
noncomputable def h (s : ℝ) : ℝ := 2 * s / (1 + s ^ 2) ^ 2

/-- (1) ∂F/∂s = r − h(s)。 -/
theorem hasDerivAt_F (r s : ℝ) : HasDerivAt (F r) (r - h s) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).const_add 1
  have h2 := h1.inv (by positivity)
  have h3 := (hasDerivAt_id' s).const_mul r
  have e : F r = fun s => (1 + s ^ 2)⁻¹ + r * s := by funext s; simp [F]
  rw [e]
  convert h2.add h3 using 1
  unfold h
  ring

theorem hasDerivAt_h (s : ℝ) : HasDerivAt h (2 * (1 - 3 * s ^ 2) / (1 + s ^ 2) ^ 3) s := by
  have hc : HasDerivAt (fun s : ℝ => 2 * s) 2 s := by
    simpa using (hasDerivAt_id' s).const_mul 2
  have hd : HasDerivAt (fun s : ℝ => (1 + s ^ 2) ^ 2) (2 * (1 + s ^ 2) * (2 * s)) s := by
    have := ((hasDerivAt_pow 2 s).const_add 1).pow 2
    convert this using 1
    simp
  have := hc.div hd (by positivity)
  have e : h = fun s => 2 * s / (1 + s ^ 2) ^ 2 := rfl
  rw [e]
  convert this using 1
  have : (1 + s ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-! ### h の山：頂点 1/√3、高さ 3√3/8 -/

/-- 山の頂点 a₀ = 1/√3 = √3/3。 -/
noncomputable def a0 : ℝ := √3 / 3

/-- 山の高さ κ = 3√3/8。 -/
noncomputable def κ : ℝ := 3 * √3 / 8

theorem sq_sqrt3 : (√3 : ℝ) ^ 2 = 3 := sq_sqrt (by norm_num)

theorem a0_pos : 0 < a0 := by unfold a0; positivity

theorem a0_sq : a0 ^ 2 = 1 / 3 := by unfold a0; rw [div_pow, sq_sqrt3]; norm_num

theorem kappa_pos : 0 < κ := by unfold κ; positivity

theorem h_a0 : h a0 = κ := by
  unfold h
  rw [a0_sq]
  unfold a0 κ
  ring

/-- (1) s ≥ 0、s ≠ a₀ で h(s) < κ。 -/
theorem h_lt_kappa {s : ℝ} (hs : 0 ≤ s) (hne : s ≠ a0) : h s < κ := by
  unfold h κ
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  set u := √3 with hu
  have hu0 : 0 < u := by positivity
  have key : u * (3 * u * (1 + s ^ 2) ^ 2 - 16 * s) =
      (u * s - 1) ^ 2 * ((u * s) ^ 2 + 2 * (u * s) + 9) := by
    linear_combination (3 - s ^ 4 * u ^ 2) * sq_sqrt3
  have hus : u * s - 1 ≠ 0 := by
    intro h0
    apply hne
    unfold a0
    have : u * s = 1 := by linarith
    have h3 : u * u = 3 := by rw [← sq]; exact sq_sqrt3
    field_simp
    nlinarith
  have hpos : 0 < (u * s - 1) ^ 2 * ((u * s) ^ 2 + 2 * (u * s) + 9) := by
    apply mul_pos (by positivity)
    nlinarith [mul_nonneg hu0.le hs]
  rw [← key] at hpos
  have : 0 < 3 * u * (1 + s ^ 2) ^ 2 - 16 * s := pos_of_mul_pos_right hpos hu0.le
  nlinarith

theorem h_le_kappa {s : ℝ} (hs : 0 ≤ s) : h s ≤ κ := by
  by_cases hne : s = a0
  · rw [hne, h_a0]
  · exact (h_lt_kappa hs hne).le

theorem h_strictMonoOn : StrictMonoOn h (Icc 0 a0) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 a0)
  · exact fun s _ => (hasDerivAt_h s).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    rw [(hasDerivAt_h s).deriv]
    have : s ^ 2 < a0 ^ 2 := by nlinarith [hs.1, hs.2]
    rw [a0_sq] at this
    apply div_pos (by linarith) (by positivity)

theorem h_strictAntiOn : StrictAntiOn h (Ici a0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici a0)
  · exact fun s _ => (hasDerivAt_h s).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ici, mem_Ioi] at hs
    rw [(hasDerivAt_h s).deriv]
    have : a0 ^ 2 < s ^ 2 := by nlinarith [a0_pos]
    rw [a0_sq] at this
    apply div_neg_of_neg_of_pos (by linarith) (by positivity)

theorem h_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ h s := by unfold h; positivity

/-- h は大きい s で小さい：S = a₀ + 1/r で h(S) < r。 -/
theorem h_small {r : ℝ} (hr : 0 < r) : h (a0 + 1 / r) < r := by
  set S := a0 + 1 / r
  have hS : 1 / r ≤ S := by have := a0_pos; simp only [S]; linarith
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS
  have h1 : h S ≤ 1 / (1 + S ^ 2) := by
    unfold h
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (S - 1), sq_nonneg S]
  have h2 : 1 / (1 + S ^ 2) < r := by
    rw [div_lt_iff₀ (by positivity)]
    have : (1 / r) ^ 2 ≤ S ^ 2 := by
      have : 0 ≤ 1 / r := by positivity
      nlinarith
    have e : r * (1 / r) = 1 := by field_simp
    nlinarith [sq_nonneg (1 / r - 1 / 2)]
  linarith

/-! ### 極小でないことの道具 -/

theorem not_isLocalMin_of_strictAntiOn {f : ℝ → ℝ} {s b : ℝ} (hsb : s < b)
    (hf : StrictAntiOn f (Icc s b)) : ¬ IsLocalMin f s := by
  intro hmin
  have h1 : ∀ᶠ y in 𝓝[>] s, f s ≤ f y := hmin.filter_mono nhdsWithin_le_nhds
  have h2 : ∀ᶠ y in 𝓝[>] s, y ∈ Ioo s b := Ioo_mem_nhdsGT hsb
  obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
  have := hf ⟨le_rfl, hsb.le⟩ ⟨hy2.1.le, hy2.2.le⟩ hy2.1
  linarith

theorem not_isLocalMin_of_strictMonoOn {f : ℝ → ℝ} {a s : ℝ} (has : a < s)
    (hf : StrictMonoOn f (Icc a s)) : ¬ IsLocalMin f s := by
  intro hmin
  have h1 : ∀ᶠ y in 𝓝[<] s, f s ≤ f y := hmin.filter_mono nhdsWithin_le_nhds
  have h2 : ∀ᶠ y in 𝓝[<] s, y ∈ Ioo a s := Ioo_mem_nhdsLT has
  obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
  have := hf ⟨hy2.1.le, hy2.2.le⟩ ⟨has.le, le_rfl⟩ hy2.2
  linarith

/-! ### (2) 乾いた端との比べ -/

/-- (2) 乾いた端 F(r, 0) = 1 より低い点がある ⇔ r < 1/2。 -/
theorem exists_below_iff (r : ℝ) : (∃ s, 0 < s ∧ F r s < 1) ↔ r < 1 / 2 := by
  constructor
  · rintro ⟨s, hs, hF⟩
    unfold F at hF
    have h1 : 1 / (1 + s ^ 2) = 1 - s ^ 2 / (1 + s ^ 2) := by field_simp; ring
    rw [h1] at hF
    have h2 : r * s < s ^ 2 / (1 + s ^ 2) := by linarith
    rw [lt_div_iff₀ (by positivity)] at h2
    by_contra hge
    push Not at hge
    have hp : 0 < 1 + s ^ 2 := by positivity
    nlinarith [mul_nonneg hs.le (sq_nonneg (s - 1)),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hge) hs.le) hp.le]
  · intro hr
    exact ⟨1, one_pos, by unfold F; norm_num; linarith⟩

/-- (2) r ≥ 1/2 なら x = 0 が最小（谷があっても乾いた端に負ける）。 -/
theorem endpoint_min_of_ge {r : ℝ} (hr : 1 / 2 ≤ r) {s : ℝ} (hs : 0 ≤ s) : F r 0 ≤ F r s := by
  have hF0 : F r 0 = 1 := by simp [F]
  rw [hF0]
  unfold F
  have hp : 0 < 1 + s ^ 2 := by positivity
  rw [← sub_nonneg]
  have e : 1 / (1 + s ^ 2) + r * s - 1 = s * (r * (1 + s ^ 2) - s) / (1 + s ^ 2) := by
    field_simp; ring
  rw [e]
  apply div_nonneg _ hp.le
  apply mul_nonneg hs
  nlinarith [sq_nonneg (s - 1), mul_nonneg (sub_nonneg.mpr hr) hp.le]

/-- (2) 0 < r < 1/2 なら全体の最小は内点にあり、乾いた端より低い。 -/
theorem global_min_interior {r : ℝ} (hr0 : 0 < r) (hr : r < 1 / 2) :
    ∃ s, 0 < s ∧ F r s < F r 0 ∧ ∀ t, 0 ≤ t → F r s ≤ F r t := by
  have hcont : Continuous (F r) := by
    have hd : Continuous (fun s : ℝ => 1 + s ^ 2) := continuous_const.add (continuous_pow 2)
    have : Continuous (fun s : ℝ => 1 / (1 + s ^ 2)) :=
      continuous_const.div hd (fun x => (by positivity : (0 : ℝ) < 1 + x ^ 2).ne')
    exact this.add (by fun_prop)
  obtain ⟨s, hs, hmin⟩ := (isCompact_Icc (a := 0) (b := 1 / r)).exists_isMinOn
    (nonempty_Icc.mpr (by positivity)) hcont.continuousOn
  have hF0 : F r 0 = 1 := by simp [F]
  have hlow : F r s < 1 := by
    have h1 : F r s ≤ F r 1 := hmin ⟨by norm_num, by rw [le_div_iff₀ hr0]; linarith⟩
    have h2 : F r 1 < 1 := by unfold F; norm_num; linarith
    linarith
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hF0] at hlow; linarith
    · exact h
  refine ⟨s, hs0, by rw [hF0]; exact hlow, ?_⟩
  intro t ht
  by_cases htr : t ≤ 1 / r
  · exact hmin ⟨ht, htr⟩
  · push Not at htr
    have h1 : 1 ≤ r * t := by rw [div_lt_iff₀ hr0] at htr; linarith
    have h2 : 0 < 1 / (1 + t ^ 2) := by positivity
    have h3 : F r t ≥ 1 := by unfold F; linarith
    linarith

/-! ### (3) 内点の極小 -/

/-- 極小の点では h(s) = r で、a₀ より右にある。 -/
theorem localMin_props {r s : ℝ} (hr : r < κ) (hs : 0 ≤ s) (hmin : IsLocalMin (F r) s) :
    h s = r ∧ a0 < s := by
  have hd := (hasDerivAt_F r s)
  have h0 : r - h s = 0 := hmin.hasDerivAt_eq_zero hd
  have hhs : h s = r := by linarith
  refine ⟨hhs, ?_⟩
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq, h_a0] at hhs; linarith
  · apply not_isLocalMin_of_strictAntiOn hlt _ hmin
    apply strictAntiOn_of_deriv_neg (convex_Icc s a0)
    · exact fun t _ => (hasDerivAt_F r t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_F r t).deriv]
      have := h_strictMonoOn ⟨hs, hlt.le⟩ ⟨by linarith [ht.1], ht.2.le⟩ ht.1
      linarith

/-- (3) 内点の極小がある ⇔ r < κ = 3√3/8（r > 0）。 -/
theorem exists_localMin_iff {r : ℝ} (hr0 : 0 < r) :
    (∃ s, 0 < s ∧ IsLocalMin (F r) s) ↔ r < κ := by
  constructor
  · rintro ⟨s, hs, hmin⟩
    by_contra hge
    push Not at hge
    have hd := hasDerivAt_F r s
    have h0 : r - h s = 0 := hmin.hasDerivAt_eq_zero hd
    have hsa : s = a0 := by
      by_contra hne
      have := h_lt_kappa hs.le hne
      linarith
    subst hsa
    apply not_isLocalMin_of_strictMonoOn a0_pos _ hmin
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 a0)
    · exact fun t _ => (hasDerivAt_F r t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_F r t).deriv]
      have := h_lt_kappa ht.1.le (ne_of_lt ht.2)
      linarith
  · intro hr
    set S := a0 + 1 / r
    have h1r : 0 < 1 / r := by positivity
    have hSa : a0 < S := by simp only [S]; linarith
    have hhS := h_small hr0
    have hcont : ContinuousOn h (Icc a0 S) :=
      fun t _ => (hasDerivAt_h t).continuousAt.continuousWithinAt
    obtain ⟨s, hsI, hhs⟩ := intermediate_value_Ioo' hSa.le hcont
      (show r ∈ Ioo (h S) (h a0) from ⟨hhS, by rw [h_a0]; exact hr⟩)
    have hs0 : 0 < s := a0_pos.trans hsI.1
    refine ⟨s, hs0, ?_⟩
    have hanti : StrictAntiOn (F r) (Icc a0 s) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc a0 s)
      · exact fun t _ => (hasDerivAt_F r t).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hasDerivAt_F r t).deriv]
        have := h_strictAntiOn (mem_Ici.mpr ht.1.le) (mem_Ici.mpr hsI.1.le) ht.2
        linarith
    have hmono : StrictMonoOn (F r) (Ici s) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici s)
      · exact fun t _ => (hasDerivAt_F r t).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Ici, mem_Ioi] at ht
        rw [(hasDerivAt_F r t).deriv]
        have := h_strictAntiOn (mem_Ici.mpr hsI.1.le) (mem_Ici.mpr (by linarith [hsI.1])) ht
        linarith
    filter_upwards [Ioi_mem_nhds hsI.1] with t ht
    rcases le_total t s with hts | hts
    · rcases eq_or_lt_of_le hts with heq | hlt
      · rw [heq]
      · exact (hanti ⟨ht.le, hts⟩ ⟨hsI.1.le, le_rfl⟩ hlt).le
    · rcases eq_or_lt_of_le hts with heq | hlt
      · rw [heq]
      · exact (hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hts) hlt).le

/-- (3) 内点の極小は、あればただ一つ。 -/
theorem localMin_unique {r s t : ℝ} (hr : r < κ) (hs : 0 < s) (ht : 0 < t)
    (hms : IsLocalMin (F r) s) (hmt : IsLocalMin (F r) t) : s = t := by
  obtain ⟨h1, h2⟩ := localMin_props hr hs.le hms
  obtain ⟨h3, h4⟩ := localMin_props hr ht.le hmt
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := h_strictAntiOn (mem_Ici.mpr h2.le) (mem_Ici.mpr h4.le) hlt; linarith
  · have := h_strictAntiOn (mem_Ici.mpr h4.le) (mem_Ici.mpr h2.le) hlt; linarith

/-! ### (4) 流体の係数で谷が動く -/

/-- (4) r < r′ < κ で、谷は左へ動き（s′ < s）、浅くなる（F(r, s) < F(r′, s′)）。 -/
theorem localMin_monotone {r r' s s' : ℝ} (hr : r < r') (hr' : r' < κ) (hs : 0 < s)
    (hs' : 0 < s') (hm : IsLocalMin (F r) s) (hm' : IsLocalMin (F r') s') :
    s' < s ∧ F r s < F r' s' := by
  obtain ⟨h1, h2⟩ := localMin_props (hr.trans hr') hs.le hm
  obtain ⟨h3, h4⟩ := localMin_props hr' hs'.le hm'
  have hlt : s' < s := by
    by_contra hle
    push Not at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq] at h1; linarith
    · have := h_strictAntiOn (mem_Ici.mpr h2.le) (mem_Ici.mpr h4.le) hlt; linarith
  refine ⟨hlt, ?_⟩
  have hanti : StrictAntiOn (F r) (Icc a0 s) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a0 s)
    · exact fun t _ => (hasDerivAt_F r t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_F r t).deriv]
      have := h_strictAntiOn (mem_Ici.mpr ht.1.le) (mem_Ici.mpr h2.le) ht.2
      linarith
  have e1 : F r s < F r s' := hanti ⟨h4.le, hlt.le⟩ ⟨h2.le, le_rfl⟩ hlt
  have e2 : F r s' < F r' s' := by unfold F; nlinarith
  linarith

/-! ### 元の模型 μ へ戻す -/

/-- μ の極小と F の極小の対応（x = x₀ s）。 -/
theorem isLocalMin_mu_iff {μb x0 c x : ℝ} (hb : 0 < μb) (h0 : 0 < x0) :
    IsLocalMin (mu μb x0 c) x ↔ IsLocalMin (F (c * x0 / μb)) (x / x0) := by
  have e : mu μb x0 c = fun y => μb * F (c * x0 / μb) (y / x0) := by
    funext y; exact mu_eq hb h0 y
  rw [e]
  constructor
  · intro hmin
    have hx : x0 * (x / x0) = x := by field_simp
    rw [← hx] at hmin
    have hc : ContinuousAt (fun s : ℝ => x0 * s) (x / x0) := by fun_prop
    have h2 := IsLocalMin.comp_continuous (g := fun s : ℝ => x0 * s) (b := x / x0) hmin hc
    filter_upwards [h2] with s hs
    simp only [Function.comp_apply] at hs
    have e1 : x0 * (x / x0) / x0 = x / x0 := by field_simp
    have e2 : x0 * s / x0 = s := by field_simp
    rw [e1, e2] at hs
    exact le_of_mul_le_mul_left hs hb
  · intro hmin
    have hc : ContinuousAt (fun y : ℝ => y / x0) x := by fun_prop
    have h2 := IsLocalMin.comp_continuous (g := fun y : ℝ => y / x0) (b := x) hmin hc
    filter_upwards [h2] with y hy
    exact mul_le_mul_of_nonneg_left hy hb.le

/-- (2) 元の模型で：∃ x > 0、μ(x) < μ_b ⇔ c x₀/μ_b < 1/2。 -/
theorem exists_mu_below_iff {μb x0 c : ℝ} (hb : 0 < μb) (h0 : 0 < x0) :
    (∃ x, 0 < x ∧ mu μb x0 c x < μb) ↔ c * x0 / μb < 1 / 2 := by
  rw [← exists_below_iff]
  constructor
  · rintro ⟨x, hx, hm⟩
    refine ⟨x / x0, by positivity, ?_⟩
    rw [mu_eq hb h0] at hm
    nlinarith
  · rintro ⟨s, hs, hF⟩
    refine ⟨x0 * s, by positivity, ?_⟩
    rw [mu_eq hb h0, show x0 * s / x0 = s by field_simp]
    nlinarith

/-- (3) 元の模型で：内点の極小がある ⇔ c x₀/μ_b < 3√3/8（c > 0）。 -/
theorem exists_localMin_mu_iff {μb x0 c : ℝ} (hb : 0 < μb) (h0 : 0 < x0) (hc : 0 < c) :
    (∃ x, 0 < x ∧ IsLocalMin (mu μb x0 c) x) ↔ c * x0 / μb < 3 * √3 / 8 := by
  rw [show (3 * √3 / 8 : ℝ) = κ from rfl, ← exists_localMin_iff (by positivity)]
  constructor
  · rintro ⟨x, hx, hm⟩
    exact ⟨x / x0, by positivity, (isLocalMin_mu_iff hb h0).mp hm⟩
  · rintro ⟨s, hs, hm⟩
    refine ⟨x0 * s, by positivity, (isLocalMin_mu_iff hb h0).mpr ?_⟩
    rw [show x0 * s / x0 = s by field_simp]
    exact hm

/-! ### (5) 境目の外の例 -/

/-- (5) r ≥ κ では、正の s に極小は無い（和は単調で谷を作らない）。 -/
theorem no_valley_example {r : ℝ} (hr : κ ≤ r) {s : ℝ} (hs : 0 < s) : ¬ IsLocalMin (F r) s := by
  intro hm
  have := (exists_localMin_iff (kappa_pos.trans_le hr)).mp ⟨s, hs, hm⟩
  linarith

/-- (5) r = 0.51：内点に極小があるが、全体の最小は x = 0（乾いた端）。 -/
theorem dry_end_wins_example :
    (∃ s, 0 < s ∧ IsLocalMin (F (51 / 100)) s) ∧ ∀ t, 0 ≤ t → F (51 / 100) 0 ≤ F (51 / 100) t := by
  refine ⟨(exists_localMin_iff (by norm_num)).mpr ?_, fun t ht => endpoint_min_of_ge
    (by norm_num) ht⟩
  unfold κ
  have : (17 : ℝ) / 10 < √3 := by
    rw [lt_sqrt (by norm_num)]; norm_num
  linarith

end Paper711

end Yamagishi
