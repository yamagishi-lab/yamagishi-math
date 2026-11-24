/-
論文999『速く投げ込んだ粒子を割っても、取り出せるエネルギーは増えず、投げ込むほど減る』の格上げ
（一般の形）。

日本語の一文：カー時空の赤道面の折り返しの点で、遠くでのエネルギー E₀ の粒子が二つの光子に割れると、
二つの光子のエネルギーの積は回転によらず (1 − 2/r)/4 に決まり、外へ出る光子が取り出す量は
(√(E₀² − 1 + 2/r) − E₀)/2 で、E₀ についても r についても減る。
English: At an equatorial turning point of the Kerr metric (G = c = M = 1, any spin a with Δ > 0),
if a unit-mass particle of energy E₀ splits into two photons that also turn there, conservation and
the null conditions force E₁E₂ = (1 − 2/r)/4 for every a, so the larger photon energy exceeds E₀ by
(√(E₀² − 1 + 2/r) − E₀)/2; this gain decreases in E₀ (for r < 2) and in r, and
E₀·gain → (2/r − 1)/4.

原稿（999_yamagishi_splitting_a_particle_thrown_in_faster_extracts_no_more_energy/…_jp.tex）は、
a = 1 で r = 1.0001・1.2・1.5・1.8、E₀ = 1・1.1・1.5・2・5・10 の 24 点を保存則の数値解で出し、
取り出した量がこの形と 9.030×10⁻⁸ 以内で一致すると確かめている。式は「導いていない」と書く。

ここで証明した言明（0 < r、Δ = r² − 2r + a² > 0）：
  (1) `turning_condition`：原稿の折り返しの条件 [E(r² + a²) − aL]² = Δ[μ²r² + (L − aE)²] は、
      赤道面の計量で作った二次形式 Q(E, L) = g_φφE² + 2g_tφEL + g_ttL² が μ²Δ に等しいことと同じ
      （差は r² 倍）。`det_eq`：g_tt g_φφ − g_tφ² = −Δ。
  (2) `photon_product`：0 < r < 2 で、Q(E₀, L₀) = Δ（質量 1 の粒子）、Q(E₁, L₁) = Q(E₂, L₂) = 0
      （光子）、E₁ + E₂ = E₀、L₁ + L₂ = L₀ なら、E₁E₂ = (1 − 2/r)/4。式に a は入らない。
  (3) `photon_energies`：よって (2E₁ − E₀)² = E₀² − 1 + 2/r、二つの光子のエネルギーは
      (E₀ ± √(E₀² − 1 + 2/r))/2 の二つに決まる。`gain_eq`：大きいほうから E₀ を引くと
      gain(E₀, r) = (√(E₀² − 1 + 2/r) − E₀)/2。
      `split_exists`：どの (E₀, L₀) にも、この形の分け方（二つの光の向きへの分解）が在る。
  (4) `falling_negative_iff`：E₀ > 0 なら、落ちる光子のエネルギーが負 ⇔ r < 2。
  (5) `gain_strictAnti_E`：0 < r < 2 なら gain は E₀ > 0 について狭義に減る。
      `gain_strictAnti_r`：E₀ を固めると、gain は r について狭義に減る（深いほど多く取り出す）。
      `gain_tendsto`：E₀ → ∞ で E₀·gain(E₀, r) → (2/r − 1)/4。
      `gain_one`：E₀ = 1 では論文939 の ½(√(2/r) − 1) に戻る。
足した仮定：カー時空の赤道面の計量の成分 g_tt = −(1 − 2/r)、g_tφ = −2a/r、g_φφ = r² + a² + 2a²/r を
定義として置き、折り返しの点では運動量が t と φ の面にあること（動径と θ の成分が 0）を、保存量
E = −p_t、L = p_φ と質量の殻 g^{μν}p_μp_ν = −μ² の形で置いた。
形式化していないもの：投げ込んだ粒子が分裂の点まで届くか（論文939 のファイルで一部）、二つの光子が
未来を向くかの区別、外へ出る光子が無限遠へ逃げるか、原稿の数値の解き方、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib
import Yamagishi.Paper939

namespace Yamagishi

namespace Paper999

open Real Filter Topology

/-- g_tt = −(1 − 2/r)。 -/
noncomputable def gtt (r : ℝ) : ℝ := -(1 - 2 / r)
/-- g_tφ = −2a/r。 -/
noncomputable def gtp (a r : ℝ) : ℝ := -(2 * a / r)
/-- g_φφ = r² + a² + 2a²/r。 -/
noncomputable def gpp (a r : ℝ) : ℝ := r ^ 2 + a ^ 2 + 2 * a ^ 2 / r
/-- Δ = r² − 2r + a²。 -/
def Δ (a r : ℝ) : ℝ := r ^ 2 - 2 * r + a ^ 2

/-- 保存量 (E, L) の二次形式 Q(E, L) = g_φφE² + 2g_tφEL + g_ttL²（g^{μν}p_μp_ν = −Q/Δ）。 -/
noncomputable def Q (a r E L : ℝ) : ℝ := gpp a r * E ^ 2 + 2 * gtp a r * E * L + gtt r * L ^ 2

/-- 取り出す量 (√(E₀² − 1 + 2/r) − E₀)/2。 -/
noncomputable def gain (E₀ r : ℝ) : ℝ := (√(E₀ ^ 2 - 1 + 2 / r) - E₀) / 2

/-- 行列式：g_tt g_φφ − g_tφ² = −Δ。 -/
theorem det_eq {a r : ℝ} (hr : r ≠ 0) : gtt r * gpp a r - gtp a r ^ 2 = -Δ a r := by
  unfold gtt gpp gtp Δ
  field_simp
  ring

/-- (1) 原稿の折り返しの条件との対応：差は r² 倍。 -/
theorem turning_condition {a r E L μ : ℝ} (hr : r ≠ 0) :
    r ^ 2 * (Q a r E L - μ ^ 2 * Δ a r) =
      (E * (r ^ 2 + a ^ 2) - a * L) ^ 2 - Δ a r * (μ ^ 2 * r ^ 2 + (L - a * E) ^ 2) := by
  unfold Q gpp gtp gtt Δ
  field_simp
  ring

/-- g_tt·Q(E, L) = (g_tt L + g_tφ E)² − ΔE²。 -/
theorem gtt_mul_Q {a r E L : ℝ} (hr : r ≠ 0) :
    gtt r * Q a r E L = (gtt r * L + gtp a r * E) ^ 2 - Δ a r * E ^ 2 := by
  have := det_eq (a := a) hr
  unfold Q
  linear_combination E ^ 2 * this

/-- (2) 二つの光子のエネルギーの積は (1 − 2/r)/4（回転 a によらない）。 -/
theorem photon_product {a r E₀ L₀ E₁ L₁ E₂ L₂ : ℝ} (hr : 0 < r) (hr2 : r < 2)
    (hΔ : 0 < Δ a r) (h0 : Q a r E₀ L₀ = Δ a r) (h1 : Q a r E₁ L₁ = 0) (h2 : Q a r E₂ L₂ = 0)
    (hE : E₁ + E₂ = E₀) (hL : L₁ + L₂ = L₀) :
    E₁ * E₂ = (1 - 2 / r) / 4 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hg : gtt r ≠ 0 := by
    unfold gtt
    have : 1 < 2 / r := by rw [lt_div_iff₀ hr]; linarith
    linarith
  set s₁ := gtt r * L₁ + gtp a r * E₁
  set s₂ := gtt r * L₂ + gtp a r * E₂
  have e1 : s₁ ^ 2 = Δ a r * E₁ ^ 2 := by
    have := gtt_mul_Q (a := a) (E := E₁) (L := L₁) hr0
    rw [h1, mul_zero] at this; linarith
  have e2 : s₂ ^ 2 = Δ a r * E₂ ^ 2 := by
    have := gtt_mul_Q (a := a) (E := E₂) (L := L₂) hr0
    rw [h2, mul_zero] at this; linarith
  have e0 : gtt r * Δ a r = (s₁ + s₂) ^ 2 - Δ a r * (E₁ + E₂) ^ 2 := by
    have := gtt_mul_Q (a := a) (E := E₀) (L := L₀) hr0
    rw [h0, ← hE, ← hL] at this
    rw [this]; simp only [s₁, s₂]; ring
  -- s₁s₂ = ΔE₁E₂ + g_ttΔ/2、二乗すると (ΔE₁E₂)²
  have hs : s₁ * s₂ = Δ a r * (E₁ * E₂) + gtt r * Δ a r / 2 := by nlinarith
  have hsq : (s₁ * s₂) ^ 2 = (Δ a r * (E₁ * E₂)) ^ 2 := by
    rw [mul_pow, e1, e2]; ring
  rw [hs] at hsq
  have hk : gtt r * Δ a r * (Δ a r * (E₁ * E₂) + gtt r * Δ a r / 4) = 0 := by
    linear_combination hsq
  have hne : gtt r * Δ a r ≠ 0 := mul_ne_zero hg (ne_of_gt hΔ)
  have := (mul_eq_zero.mp hk).resolve_left hne
  have h3 : Δ a r * (E₁ * E₂ + gtt r / 4) = 0 := by linear_combination this
  have h4 := (mul_eq_zero.mp h3).resolve_left (ne_of_gt hΔ)
  unfold gtt at h4
  linarith

/-- (3) 光子のエネルギーは (E₀ ± √(E₀² − 1 + 2/r))/2 の二つ。 -/
theorem photon_energies {a r E₀ L₀ E₁ L₁ E₂ L₂ : ℝ} (hr : 0 < r) (hr2 : r < 2)
    (hΔ : 0 < Δ a r) (h0 : Q a r E₀ L₀ = Δ a r) (h1 : Q a r E₁ L₁ = 0) (h2 : Q a r E₂ L₂ = 0)
    (hE : E₁ + E₂ = E₀) (hL : L₁ + L₂ = L₀) :
    (2 * E₁ - E₀) ^ 2 = E₀ ^ 2 - 1 + 2 / r ∧
      ((E₁ = (E₀ + √(E₀ ^ 2 - 1 + 2 / r)) / 2 ∧ E₂ = (E₀ - √(E₀ ^ 2 - 1 + 2 / r)) / 2) ∨
       (E₁ = (E₀ - √(E₀ ^ 2 - 1 + 2 / r)) / 2 ∧ E₂ = (E₀ + √(E₀ ^ 2 - 1 + 2 / r)) / 2)) := by
  have hp := photon_product hr hr2 hΔ h0 h1 h2 hE hL
  have hsq : (2 * E₁ - E₀) ^ 2 = E₀ ^ 2 - 1 + 2 / r := by
    rw [← hE]; linear_combination (-4) * hp
  refine ⟨hsq, ?_⟩
  have hnn : 0 ≤ E₀ ^ 2 - 1 + 2 / r := by rw [← hsq]; positivity
  have habs : |2 * E₁ - E₀| = √(E₀ ^ 2 - 1 + 2 / r) := by
    rw [← hsq, sqrt_sq_eq_abs]
  rcases abs_cases (2 * E₁ - E₀) with ⟨h, _⟩ | ⟨h, _⟩
  · left; constructor <;> linarith
  · right; constructor <;> linarith

/-- (3) 大きいほうの光子が取り出す量は gain(E₀, r)。 -/
theorem gain_eq {a r E₀ L₀ E₁ L₁ E₂ L₂ : ℝ} (hr : 0 < r) (hr2 : r < 2)
    (hΔ : 0 < Δ a r) (h0 : Q a r E₀ L₀ = Δ a r) (h1 : Q a r E₁ L₁ = 0) (h2 : Q a r E₂ L₂ = 0)
    (hE : E₁ + E₂ = E₀) (hL : L₁ + L₂ = L₀) :
    max E₁ E₂ - E₀ = gain E₀ r ∧ min E₁ E₂ = (E₀ - √(E₀ ^ 2 - 1 + 2 / r)) / 2 := by
  have hs := sqrt_nonneg (E₀ ^ 2 - 1 + 2 / r)
  rcases (photon_energies hr hr2 hΔ h0 h1 h2 hE hL).2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2, max_eq_left (by linarith), min_eq_right (by linarith)]
    unfold gain; constructor <;> ring
  · rw [e1, e2, max_eq_right (by linarith), min_eq_left (by linarith)]
    unfold gain; constructor <;> ring

/-- (3) 分け方は在る：どの (E₀, L₀) も、二つの光の向きの和に書ける。 -/
theorem split_exists {a r : ℝ} (hr : 0 < r) (hr2 : r < 2) (hΔ : 0 < Δ a r) (E₀ L₀ : ℝ) :
    ∃ E₁ L₁ E₂ L₂, Q a r E₁ L₁ = 0 ∧ Q a r E₂ L₂ = 0 ∧ E₁ + E₂ = E₀ ∧ L₁ + L₂ = L₀ := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hg : 0 < gtt r := by
    unfold gtt
    have : 1 < 2 / r := by rw [lt_div_iff₀ hr]; linarith
    linarith
  set w := √(Δ a r)
  have hw : w ^ 2 = Δ a r := sq_sqrt hΔ.le
  have hw0 : 0 < w := sqrt_pos.mpr hΔ
  -- 光の向き (1, b₊)、(1, b₋)、b± = (−g_tφ ± √Δ)/g_tt
  set bp := (-gtp a r + w) / gtt r
  set bm := (-gtp a r - w) / gtt r
  have hnull : ∀ b E, gtt r * b ^ 2 + 2 * gtp a r * b + gpp a r = 0 → Q a r E (E * b) = 0 := by
    intro b E hb
    unfold Q
    linear_combination E ^ 2 * hb
  have hroot : ∀ b, (b = bp ∨ b = bm) → gtt r * b ^ 2 + 2 * gtp a r * b + gpp a r = 0 := by
    have hd := det_eq (a := a) hr0
    have hg0 : gtt r ≠ 0 := ne_of_gt hg
    have key : ∀ σ : ℝ, σ ^ 2 = 1 →
        gtt r * ((-gtp a r + σ * w) / gtt r) ^ 2 + 2 * gtp a r * ((-gtp a r + σ * w) / gtt r)
          + gpp a r = 0 := by
      intro σ hσ
      have : gtt r * ((-gtp a r + σ * w) / gtt r) ^ 2 + 2 * gtp a r * ((-gtp a r + σ * w) / gtt r)
          + gpp a r = (σ ^ 2 * w ^ 2 - gtp a r ^ 2 + gtt r * gpp a r) / gtt r := by
        field_simp; ring
      rw [this, hσ, hw, one_mul, show Δ a r - gtp a r ^ 2 + gtt r * gpp a r = 0 by linarith,
        zero_div]
    rintro b (rfl | rfl)
    · have := key 1 (by norm_num); simpa [bp] using this
    · have := key (-1) (by norm_num)
      simp only [bm]
      rw [show -gtp a r - w = -gtp a r + -1 * w by ring]
      exact this
  have hdiff : bp - bm ≠ 0 := by
    simp only [bp, bm]
    rw [div_sub_div_same]
    have : -gtp a r + w - (-gtp a r - w) = 2 * w := by ring
    rw [this]; positivity
  set E₁ := (L₀ - bm * E₀) / (bp - bm)
  refine ⟨E₁, E₁ * bp, E₀ - E₁, (E₀ - E₁) * bm, hnull _ _ (hroot _ (Or.inl rfl)),
    hnull _ _ (hroot _ (Or.inr rfl)), by ring, ?_⟩
  simp only [E₁]
  field_simp
  ring

/-- (4) E₀ > 0 なら、落ちる光子のエネルギーが負 ⇔ r < 2。 -/
theorem falling_negative_iff {E₀ r : ℝ} (hE : 0 < E₀) (hr : 0 < r) :
    (E₀ - √(E₀ ^ 2 - 1 + 2 / r)) / 2 < 0 ↔ r < 2 := by
  constructor
  · intro h
    have h1 : E₀ < √(E₀ ^ 2 - 1 + 2 / r) := by linarith
    have h2 : E₀ ^ 2 < E₀ ^ 2 - 1 + 2 / r := by
      have := (lt_sqrt hE.le).mp h1
      linarith
    have : 1 < 2 / r := by linarith
    rwa [lt_div_iff₀ hr, one_mul] at this
  · intro h
    have : 1 < 2 / r := by rw [lt_div_iff₀ hr]; linarith
    have h1 : E₀ < √(E₀ ^ 2 - 1 + 2 / r) := (lt_sqrt hE.le).mpr (by nlinarith)
    linarith

/-- gain の別の形：c = 2/r − 1 として gain = c/(2(√(E₀² + c) + E₀))。 -/
theorem gain_alt {E₀ r : ℝ} (hE : 0 < E₀) (hc : 0 ≤ E₀ ^ 2 - 1 + 2 / r) :
    gain E₀ r = (2 / r - 1) / (2 * (√(E₀ ^ 2 - 1 + 2 / r) + E₀)) := by
  have hs := sqrt_nonneg (E₀ ^ 2 - 1 + 2 / r)
  have hpos : 0 < √(E₀ ^ 2 - 1 + 2 / r) + E₀ := by linarith
  have hsq := sq_sqrt hc
  unfold gain
  field_simp
  nlinarith

/-- (5) 0 < r < 2 なら、gain は E₀ について狭義に減る。 -/
theorem gain_strictAnti_E {r : ℝ} (hr : 0 < r) (hr2 : r < 2) :
    StrictAntiOn (fun E₀ => gain E₀ r) (Set.Ioi 0) := by
  have hc : 0 < 2 / r - 1 := by
    have : 1 < 2 / r := by rw [lt_div_iff₀ hr]; linarith
    linarith
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  simp only
  have hcx : 0 ≤ x ^ 2 - 1 + 2 / r := by nlinarith
  have hcy : 0 ≤ y ^ 2 - 1 + 2 / r := by nlinarith
  rw [gain_alt hx hcx, gain_alt hy hcy]
  apply div_lt_div_of_pos_left hc
  · have := sqrt_nonneg (x ^ 2 - 1 + 2 / r); positivity
  · have : √(x ^ 2 - 1 + 2 / r) ≤ √(y ^ 2 - 1 + 2 / r) :=
      sqrt_le_sqrt (by nlinarith)
    linarith

/-- (5) E₀ を固めると、gain は r について狭義に減る。 -/
theorem gain_strictAnti_r {E₀ : ℝ} :
    StrictAntiOn (fun r => gain E₀ r) {r | 0 < r ∧ 0 ≤ E₀ ^ 2 - 1 + 2 / r} := by
  rintro x ⟨hx, hx'⟩ y ⟨hy, hy'⟩ hxy
  simp only
  unfold gain
  have : 2 / y < 2 / x := div_lt_div_of_pos_left (by norm_num) hx hxy
  have := sqrt_lt_sqrt hy' (show E₀ ^ 2 - 1 + 2 / y < E₀ ^ 2 - 1 + 2 / x by linarith)
  linarith

/-- (5) E₀ → ∞ で E₀·gain(E₀, r) → (2/r − 1)/4。 -/
theorem gain_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun E₀ => E₀ * gain E₀ r) atTop (𝓝 ((2 / r - 1) / 4)) := by
  set c := 2 / r - 1
  -- 十分大きい E₀ では E₀·gain = c/(2(√(1 + c/E₀²) + 1))
  have heq : ∀ᶠ E₀ in atTop, c / (2 * (√(1 + c / E₀ ^ 2) + 1)) = E₀ * gain E₀ r := by
    filter_upwards [eventually_gt_atTop (1 + |c|)] with E₀ hE
    have hE0 : 0 < E₀ := by linarith [abs_nonneg c]
    have hc : 0 ≤ E₀ ^ 2 - 1 + 2 / r := by
      have : -c ≤ |c| := neg_le_abs c
      nlinarith
    rw [gain_alt hE0 hc]
    have h1 : √(E₀ ^ 2 - 1 + 2 / r) = E₀ * √(1 + c / E₀ ^ 2) := by
      rw [show E₀ ^ 2 - 1 + 2 / r = E₀ ^ 2 * (1 + c / E₀ ^ 2) by simp only [c]; field_simp; ring,
        sqrt_mul (sq_nonneg _), sqrt_sq hE0.le]
    rw [h1]
    have : 0 ≤ √(1 + c / E₀ ^ 2) := sqrt_nonneg _
    field_simp
    simp only [c]
    field_simp
  refine Tendsto.congr' heq ?_
  have h0 : Tendsto (fun E₀ : ℝ => c / E₀ ^ 2) atTop (𝓝 0) := by
    exact Tendsto.div_atTop tendsto_const_nhds (tendsto_pow_atTop two_ne_zero)
  have h1 : Tendsto (fun E₀ : ℝ => √(1 + c / E₀ ^ 2)) atTop (𝓝 1) := by
    have := (h0.const_add 1).sqrt
    simpa using this
  have h2 := ((h1.add_const 1).const_mul 2)
  have h3 := h2.inv₀ (by norm_num)
  have h4 := h3.const_mul c
  convert h4 using 1
  · funext E₀; simp only [div_eq_mul_inv]
  · norm_num; ring

/-- (5) E₀ = 1 では論文939 の式 ½(√(2/r) − 1) に戻る。 -/
theorem gain_one (r : ℝ) : gain 1 r = Paper939.gain r := by
  unfold gain Paper939.gain
  norm_num

end Paper999

end Yamagishi
