/-
論文943『二つの色の明るさの比は熱い星ほど一定の値に近づき、温度を読む力が落ちる』の格上げ（一般の形）。

日本語の一文：どの二つの波長でも、黒体の明るさの比は温度とともに狭義に増えて波長の比の四乗に近づき、
その効き S は狭義に減って 0 に向かい、効きと温度の積は低温の値 c₂(1/λ₁ − 1/λ₂) からちょうどその半分へ
狭義に減りながら移る。
English: For any two wavelengths λ₁ < λ₂ (a = c₂/λ₁ > b = c₂/λ₂ > 0), the Planck ratio
R(T) = (a/b)⁵(e^(b/T) − 1)/(e^(a/T) − 1) increases strictly to (a/b)⁴ = (λ₂/λ₁)⁴, its sensitivity
S = d ln R/d ln T = g(a/T) − g(b/T), g(x) = x eˣ/(eˣ − 1), decreases strictly to 0, and T·S
decreases strictly from a − b (T → 0) to exactly (a − b)/2 (T → ∞), for every pair of wavelengths.

原稿（943_yamagishi_the_color_ratio_levels_off_for_hotter_stars_and_its_power_to_read_temperature_
fades/…_jp.tex）は、440 nm と 550 nm の一組で七つの温度の比と効き、T·S の二つの極限 6539.895 K と
3269.947 K を数値で出し、365 nm の組と比べている。極限の値は観察 3.2 で一般に説明しているが、
単調性と「ちょうど半分」が波長によらないことは示していない。

ここで証明した言明（0 < b < a、T > 0）：
  (1) `hasDerivAt_g`・`hasDerivAt_g1`：g の一階・二階の微分の閉じた形。`g1_pos`・`g2_pos`：x > 0 で
      どちらも正。`g_strictMonoOn`・`g_strictConvexOn`：g は (0, ∞) で狭義に増え、狭義に凸。
  (2) `hasDerivAt_logR`：u = ln T とおくと d ln R(e^u)/du = S(e^u)（S は効き）。
      `S_pos`：S > 0。`R_strictMonoOn`：R は T について狭義に増える。
      `R_tendsto_atTop`：T → ∞ で R → (a/b)⁴。`R_lt_limit`：R < (a/b)⁴。
      `R_tendsto_zero`：T → 0⁺ で R → 0。
  (3) `TS_eq`：T·S = (a − b) + a/(e^(a/T) − 1) − b/(e^(b/T) − 1) = (a − b)×（g の割線の傾き）。
      `TS_strictAntiOn`：T·S は T について狭義に減る（g の狭義の凸性）。
      `TS_tendsto_zero`：T → 0⁺ で T·S → a − b。`TS_tendsto_atTop`：T → ∞ で T·S → (a − b)/2。
      `TS_bounds`：どの T でも (a − b)/2 < T·S < a − b。半分という値は波長の組によらない。
  (4) `S_strictAntiOn`：S は T について狭義に減る。`S_tendsto_atTop`：T → ∞ で S → 0。
  (5) `Rnu_eq`：振動数あたりの比は R/(a/b)²（極限は (a/b)²）。`hasDerivAt_logRnu`：効きは同じ S。
  (6) `paper_limits`：原稿の c₂ と 440 nm・550 nm で a − b は 6539.894 と 6539.896 のあいだ、
      半分は 3269.947 と 3269.948 のあいだ（原稿の 6539.895 K と 3269.947 K）。
足した仮定：プランクの式の形 B_λ ∝ λ^(−5)/(e^(c₂/(λT)) − 1)（定数は比で消える）を定義として置いた。
形式化していないもの：七つの温度の数表、二つの明るさが等しくなる温度、フィルターの幅、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper943

open Real Set Filter Topology

/-! ### g(x) = x eˣ/(eˣ − 1) -/

/-- g(x) = x eˣ/(eˣ − 1)。 -/
noncomputable def g (x : ℝ) : ℝ := x * exp x / (exp x - 1)
/-- g′(x) = eˣ(eˣ − 1 − x)/(eˣ − 1)²。 -/
noncomputable def g1 (x : ℝ) : ℝ := exp x * (exp x - 1 - x) / (exp x - 1) ^ 2
/-- g″(x) = eˣ(x(eˣ + 1) − 2(eˣ − 1))/(eˣ − 1)³。 -/
noncomputable def g2 (x : ℝ) : ℝ := exp x * (x * (exp x + 1) - 2 * (exp x - 1)) / (exp x - 1) ^ 3

theorem expm1_pos {x : ℝ} (hx : 0 < x) : 0 < exp x - 1 := by
  linarith [add_one_lt_exp (ne_of_gt hx)]

theorem expm1_ne {x : ℝ} (hx : x ≠ 0) : exp x - 1 ≠ 0 := by
  intro h
  exact hx (exp_eq_one_iff x |>.mp (by linarith))

theorem hasDerivAt_g {x : ℝ} (hx : x ≠ 0) : HasDerivAt g (g1 x) x := by
  have hd := expm1_ne hx
  have h1 : HasDerivAt (fun y => y * exp y) (1 * exp x + x * exp x) x :=
    (hasDerivAt_id' x).mul (hasDerivAt_exp x)
  have h2 : HasDerivAt (fun y => exp y - 1) (exp x) x := (hasDerivAt_exp x).sub_const 1
  have := h1.div h2 hd
  unfold g g1
  convert this using 1
  field_simp
  ring

theorem hasDerivAt_g1 {x : ℝ} (hx : x ≠ 0) : HasDerivAt g1 (g2 x) x := by
  have hd := expm1_ne hx
  have h1 : HasDerivAt (fun y => exp y * (exp y - 1 - y)) (exp x * (exp x - 1 - x) +
      exp x * (exp x - 1)) x :=
    (hasDerivAt_exp x).mul (((hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id' x))
  have h2 : HasDerivAt (fun y => (exp y - 1) * (exp y - 1))
      (exp x * (exp x - 1) + (exp x - 1) * exp x) x :=
    ((hasDerivAt_exp x).sub_const 1).mul ((hasDerivAt_exp x).sub_const 1)
  have := h1.div h2 (mul_ne_zero hd hd)
  have e : g1 = fun y => exp y * (exp y - 1 - y) / ((exp y - 1) * (exp y - 1)) := by
    funext y; unfold g1; ring
  rw [e]
  convert this using 1
  unfold g2
  field_simp
  ring

/-- φ(x) = x(eˣ + 1) − 2(eˣ − 1) > 0（x > 0）。 -/
theorem phi_pos {x : ℝ} (hx : 0 < x) : 0 < x * (exp x + 1) - 2 * (exp x - 1) := by
  let φ := fun y : ℝ => y * (exp y + 1) - 2 * (exp y - 1)
  have hd : ∀ y, HasDerivAt φ (1 - exp y + y * exp y) y := by
    intro y
    have := (((hasDerivAt_id' y).mul ((hasDerivAt_exp y).add_const 1))).sub
      (((hasDerivAt_exp y).sub_const 1).const_mul 2)
    convert this using 1; ring
  have hmono : StrictMonoOn φ (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun y _ => (hd y).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hd y).deriv]
      have h1 := add_one_lt_exp (show -y ≠ 0 by linarith [mem_Ioi.mp hy])
      rw [exp_neg] at h1
      have hey := exp_pos y
      have : 1 - exp y + y * exp y = exp y * ((exp y)⁻¹ - 1 + y) := by field_simp
      rw [this]
      apply mul_pos hey
      linarith
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx
  simpa [φ] using this

theorem g1_pos {x : ℝ} (hx : 0 < x) : 0 < g1 x := by
  unfold g1
  have := expm1_pos hx
  have : 0 < exp x - 1 - x := by linarith [add_one_lt_exp (ne_of_gt hx)]
  have := exp_pos x
  positivity

theorem g2_pos {x : ℝ} (hx : 0 < x) : 0 < g2 x := by
  unfold g2
  have := expm1_pos hx
  have := phi_pos hx
  have := exp_pos x
  positivity

theorem g_strictMonoOn : StrictMonoOn g (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun x hx => (hasDerivAt_g (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hasDerivAt_g (ne_of_gt hx)).deriv]
    exact g1_pos hx

theorem g1_strictMonoOn : StrictMonoOn g1 (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun x hx => (hasDerivAt_g1 (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hasDerivAt_g1 (ne_of_gt hx)).deriv]
    exact g2_pos hx

theorem g_strictConvexOn : StrictConvexOn ℝ (Ioi 0) g := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0)
  · exact fun x hx => (hasDerivAt_g (ne_of_gt hx)).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    exact g1_strictMonoOn.congr (fun x hx => ((hasDerivAt_g (ne_of_gt hx)).deriv).symm)

/-- 割線の傾きは両端を右へ動かすと狭義に増える。 -/
theorem slope_lt {p₁ q₁ p₂ q₂ : ℝ} (hp₁ : 0 < p₁) (hpq₁ : p₁ < q₁) (hpq₂ : p₂ < q₂)
    (hp : p₁ < p₂) (hq : q₁ < q₂) :
    (g q₁ - g p₁) / (q₁ - p₁) < (g q₂ - g p₂) / (q₂ - p₂) := by
  have hc := g_strictConvexOn
  have m1 : p₁ ∈ Ioi (0 : ℝ) := hp₁
  have m2 : q₁ ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by linarith)
  have m3 : q₂ ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by linarith)
  have m4 : p₂ ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by linarith)
  have s1 := hc.secant_strict_mono m1 m2 m3 (ne_of_gt hpq₁) (by linarith) hq
  have s2 := hc.secant_strict_mono m3 m1 m4 (by linarith) (ne_of_lt hpq₂) hp
  have e1 : (g p₁ - g q₂) / (p₁ - q₂) = (g q₂ - g p₁) / (q₂ - p₁) := by
    rw [← neg_div_neg_eq]; ring_nf
  have e2 : (g p₂ - g q₂) / (p₂ - q₂) = (g q₂ - g p₂) / (q₂ - p₂) := by
    rw [← neg_div_neg_eq]; ring_nf
  rw [e1, e2] at s2
  linarith

/-! ### 比 R と効き S -/

/-- 波長あたりの明るさの比 R(T) = (a/b)⁵(e^(b/T) − 1)/(e^(a/T) − 1)（a = c₂/λ₁、b = c₂/λ₂）。 -/
noncomputable def R (a b T : ℝ) : ℝ := (a / b) ^ 5 * ((exp (b / T) - 1) / (exp (a / T) - 1))

/-- 振動数あたりの明るさの比。 -/
noncomputable def Rnu (a b T : ℝ) : ℝ := (a / b) ^ 3 * ((exp (b / T) - 1) / (exp (a / T) - 1))

/-- 効き S(T) = g(a/T) − g(b/T)。 -/
noncomputable def S (a b T : ℝ) : ℝ := g (a / T) - g (b / T)

section Pair

variable {a b : ℝ}

theorem R_pos (ha : 0 < a) (hb : 0 < b) {T : ℝ} (hT : 0 < T) : 0 < R a b T := by
  unfold R
  have := expm1_pos (show 0 < b / T by positivity)
  have := expm1_pos (show 0 < a / T by positivity)
  positivity

/-- 補題：c > 0 のとき d/du ln(e^(c e^(−u)) − 1) = −g(c e^(−u))。 -/
theorem hasDerivAt_logpart {c : ℝ} (hc : 0 < c) (u : ℝ) :
    HasDerivAt (fun v => log (exp (c / exp v) - 1)) (-g (c / exp u)) u := by
  have hx : 0 < c / exp u := by positivity
  have h1 : HasDerivAt (fun v => c / exp v) (-(c / exp u)) u := by
    have := (hasDerivAt_exp u).inv (ne_of_gt (exp_pos u))
    have := this.const_mul c
    convert this using 1
    · funext v; simp [div_eq_mul_inv]
    · field_simp
  have h2 := ((h1.exp).sub_const 1).log (ne_of_gt (expm1_pos hx))
  convert h2 using 1
  unfold g
  field_simp

/-- (2) d ln R(e^u)/du = S(e^u)。 -/
theorem hasDerivAt_logR (ha : 0 < a) (hb : 0 < b) (u : ℝ) :
    HasDerivAt (fun v => log (R a b (exp v))) (S a b (exp u)) u := by
  have e : (fun v => log (R a b (exp v))) =
      fun v => 5 * log (a / b) + (log (exp (b / exp v) - 1) - log (exp (a / exp v) - 1)) := by
    funext v
    unfold R
    have h1 := expm1_pos (show 0 < b / exp v by positivity)
    have h2 := expm1_pos (show 0 < a / exp v by positivity)
    rw [log_mul (by positivity) (by positivity), log_pow, log_div (ne_of_gt h1) (ne_of_gt h2)]
    push_cast; ring
  rw [e]
  have := ((hasDerivAt_logpart hb u).sub (hasDerivAt_logpart ha u)).const_add (5 * log (a / b))
  convert this using 1
  unfold S; ring

theorem S_pos (ha : 0 < a) (hb : 0 < b) (hab : b < a) {T : ℝ} (hT : 0 < T) : 0 < S a b T := by
  unfold S
  have := g_strictMonoOn (mem_Ioi.mpr (by positivity) : b / T ∈ Ioi (0 : ℝ))
    (mem_Ioi.mpr (by positivity) : a / T ∈ Ioi (0 : ℝ))
    (div_lt_div_of_pos_right hab hT)
  linarith

/-- (2) R は T について狭義に増える。 -/
theorem R_strictMonoOn (ha : 0 < a) (hb : 0 < b) (hab : b < a) : StrictMonoOn (R a b) (Ioi 0) := by
  have hf : StrictMono (fun v => log (R a b (exp v))) := by
    apply strictMono_of_deriv_pos
    intro u
    rw [(hasDerivAt_logR ha hb u).deriv]
    exact S_pos ha hb hab (exp_pos u)
  intro T₁ h₁ T₂ h₂ hT
  have h := hf (log_lt_log h₁ hT)
  simp only [exp_log h₁, exp_log (show (0 : ℝ) < T₂ from h₂)] at h
  exact (log_lt_log_iff (R_pos ha hb h₁) (R_pos ha hb h₂)).mp h

theorem expm1_le_mul (x : ℝ) : exp x - 1 ≤ x * exp x := by
  have := add_one_le_exp (-x)
  rw [exp_neg] at this
  have he := exp_pos x
  have : 1 - x ≤ (exp x)⁻¹ := by linarith
  have := mul_le_mul_of_nonneg_left this he.le
  rw [mul_inv_cancel₀ (ne_of_gt he)] at this
  nlinarith

/-- (2) T → ∞ で R → (a/b)⁴。 -/
theorem R_tendsto_atTop (ha : 0 < a) (hb : 0 < b) :
    Tendsto (R a b) atTop (𝓝 ((a / b) ^ 4)) := by
  have hc : ∀ c : ℝ, Tendsto (fun T : ℝ => exp (c / T)) atTop (𝓝 1) := by
    intro c
    have h0 : Tendsto (fun T : ℝ => c / T) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds tendsto_id
    have := (continuous_exp.tendsto 0).comp h0
    rw [exp_zero] at this
    exact this
  have hlo : Tendsto (fun T => (a / b) ^ 4 * exp (-a / T)) atTop (𝓝 ((a / b) ^ 4)) := by
    simpa using (hc (-a)).const_mul ((a / b) ^ 4)
  have hhi : Tendsto (fun T => (a / b) ^ 4 * exp (b / T)) atTop (𝓝 ((a / b) ^ 4)) := by
    simpa using (hc b).const_mul ((a / b) ^ 4)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_gt_atTop 0] with T hT
    have hx1 : 0 < a / T := by positivity
    have hx2 : 0 < b / T := by positivity
    have e1 := expm1_pos hx1
    have l1 : b / T ≤ exp (b / T) - 1 := by linarith [add_one_le_exp (b / T)]
    have u1 := expm1_le_mul (a / T)
    unfold R
    rw [show (a / b) ^ 5 * ((exp (b / T) - 1) / (exp (a / T) - 1)) =
      (a / b) ^ 4 * (a / b * (exp (b / T) - 1) / (exp (a / T) - 1)) by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [le_div_iff₀ e1, show -a / T = -(a / T) by ring]
    calc exp (-(a / T)) * (exp (a / T) - 1) ≤ exp (-(a / T)) * (a / T * exp (a / T)) :=
          mul_le_mul_of_nonneg_left u1 (exp_pos _).le
      _ = a / b * (b / T) := by rw [exp_neg]; field_simp
      _ ≤ a / b * (exp (b / T) - 1) := mul_le_mul_of_nonneg_left l1 (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with T hT
    have hx1 : 0 < a / T := by positivity
    have hx2 : 0 < b / T := by positivity
    have e1 := expm1_pos hx1
    have l1 : a / T ≤ exp (a / T) - 1 := by linarith [add_one_le_exp (a / T)]
    have u2 := expm1_le_mul (b / T)
    unfold R
    rw [show (a / b) ^ 5 * ((exp (b / T) - 1) / (exp (a / T) - 1)) =
      (a / b) ^ 4 * (a / b * (exp (b / T) - 1) / (exp (a / T) - 1)) by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ e1]
    calc a / b * (exp (b / T) - 1) ≤ a / b * (b / T * exp (b / T)) :=
          mul_le_mul_of_nonneg_left u2 (by positivity)
      _ = a / T * exp (b / T) := by field_simp
      _ ≤ (exp (a / T) - 1) * exp (b / T) := mul_le_mul_of_nonneg_right l1 (exp_pos _).le
      _ = exp (b / T) * (exp (a / T) - 1) := by ring

/-- (2) T → 0⁺ で R → 0。 -/
theorem R_tendsto_zero (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    Tendsto (R a b) (𝓝[>] 0) (𝓝 0) := by
  have hinv : Tendsto (fun T : ℝ => (b - a) * T⁻¹) (𝓝[>] 0) atBot :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg (by linarith)
  have hup : Tendsto (fun T : ℝ => (a / b) ^ 5 * exp ((b - a) * T⁻¹)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_exp_atBot.comp hinv).const_mul ((a / b) ^ 5)
  apply squeeze_zero' _ _ hup
  · filter_upwards [self_mem_nhdsWithin] with T hT
    exact (R_pos ha hb hT).le
  · filter_upwards [self_mem_nhdsWithin] with T hT
    have hT : 0 < T := hT
    have hx1 : 0 < a / T := by positivity
    have e1 := expm1_pos hx1
    unfold R
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ e1, show (b - a) * T⁻¹ = b / T - a / T by field_simp, exp_sub]
    have : exp (b / T) ≤ exp (a / T) := exp_le_exp.mpr (div_le_div_of_nonneg_right hab.le hT.le)
    have hea := exp_pos (a / T)
    field_simp
    nlinarith

/-- (2) R < (a/b)⁴。 -/
theorem R_lt_limit (ha : 0 < a) (hb : 0 < b) (hab : b < a) {T : ℝ} (hT : 0 < T) :
    R a b T < (a / b) ^ 4 := by
  have hmono := R_strictMonoOn ha hb hab
  have h2 : R a b (2 * T) ≤ (a / b) ^ 4 := by
    apply ge_of_tendsto (R_tendsto_atTop ha hb)
    filter_upwards [eventually_ge_atTop (2 * T)] with t ht
    exact hmono.monotoneOn (mem_Ioi.mpr (by positivity) : 2 * T ∈ Ioi (0 : ℝ))
      (show t ∈ Ioi 0 from lt_of_lt_of_le (by positivity) ht) ht
  exact lt_of_lt_of_le
    (hmono hT (mem_Ioi.mpr (by positivity) : 2 * T ∈ Ioi (0 : ℝ)) (by linarith)) h2

/-! ### 効きと温度の積 T·S -/

/-- (3) T·S の閉じた形。 -/
theorem TS_eq (ha : 0 < a) (hb : 0 < b) {T : ℝ} (hT : 0 < T) :
    T * S a b T = (a - b) + a / (exp (a / T) - 1) - b / (exp (b / T) - 1) := by
  have h1 := expm1_pos (show 0 < a / T by positivity)
  have h2 := expm1_pos (show 0 < b / T by positivity)
  unfold S g
  field_simp
  ring

/-- (3) T·S = (a − b)×（g の b/T から a/T への割線の傾き）。 -/
theorem TS_slope (hab : b < a) {T : ℝ} (hT : 0 < T) :
    T * S a b T = (a - b) * ((g (a / T) - g (b / T)) / (a / T - b / T)) := by
  have : a / T - b / T = (a - b) / T := by ring
  rw [this]
  have : a - b ≠ 0 := by linarith
  unfold S
  field_simp

/-- (3) T·S は T について狭義に減る。 -/
theorem TS_strictAntiOn (hb : 0 < b) (hab : b < a) :
    StrictAntiOn (fun T => T * S a b T) (Ioi 0) := by
  intro T₁ h₁ T₂ h₂ hT
  have h₁ : (0 : ℝ) < T₁ := h₁
  have h₂ : (0 : ℝ) < T₂ := h₂
  simp only
  rw [TS_slope hab h₁, TS_slope hab h₂]
  apply mul_lt_mul_of_pos_left _ (by linarith)
  apply slope_lt (by positivity) (div_lt_div_of_pos_right hab h₂) (div_lt_div_of_pos_right hab h₁)
  · exact div_lt_div_of_pos_left hb h₁ hT
  · exact div_lt_div_of_pos_left (by linarith) h₁ hT

/-- c/(e^(c/T) − 1) ≤ T（e^x − 1 ≥ x）。 -/
theorem frac_le {c T : ℝ} (hc : 0 < c) (hT : 0 < T) : c / (exp (c / T) - 1) ≤ T := by
  have hx : 0 < c / T := by positivity
  have e := expm1_pos hx
  rw [div_le_iff₀ e]
  have : c / T ≤ exp (c / T) - 1 := by linarith [add_one_le_exp (c / T)]
  calc c = T * (c / T) := by field_simp
    _ ≤ T * (exp (c / T) - 1) := mul_le_mul_of_nonneg_left this hT.le

/-- (3) T → 0⁺ で T·S → a − b。 -/
theorem TS_tendsto_zero (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun T => T * S a b T) (𝓝[>] 0) (𝓝 (a - b)) := by
  have hid : Tendsto (fun T : ℝ => T) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hf : ∀ c : ℝ, 0 < c → Tendsto (fun T => c / (exp (c / T) - 1)) (𝓝[>] 0) (𝓝 0) := by
    intro c hc
    apply squeeze_zero' _ _ hid
    · filter_upwards [self_mem_nhdsWithin] with T hT
      have hT : (0 : ℝ) < T := hT
      have := expm1_pos (show 0 < c / T by positivity)
      positivity
    · filter_upwards [self_mem_nhdsWithin] with T hT
      exact frac_le hc hT
  have := ((hf a ha).const_add (a - b)).sub (hf b hb)
  simp only [add_zero, sub_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with T hT
  exact (TS_eq ha hb hT).symm

/-- B(x) = x/(eˣ − 1) の下の限界 1 − x/2 < B(x)（x > 0）。 -/
theorem B_lower {x : ℝ} (hx : 0 < x) : 1 - x / 2 < x / (exp x - 1) := by
  let ρ := fun y : ℝ => (y - 2) * exp y + y + 2
  have hd : ∀ y, HasDerivAt ρ ((y - 1) * exp y + 1) y := by
    intro y
    have := ((((hasDerivAt_id' y).sub_const 2).mul (hasDerivAt_exp y)).add (hasDerivAt_id' y))
      |>.add_const 2
    convert this using 1; ring
  have hmono : StrictMonoOn ρ (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun y _ => (hd y).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hd y).deriv]
      have h1 := add_one_lt_exp (show -y ≠ 0 by linarith [mem_Ioi.mp hy])
      rw [exp_neg] at h1
      have hey := exp_pos y
      have : (y - 1) * exp y + 1 = exp y * (y - 1 + (exp y)⁻¹) := by field_simp
      rw [this]
      apply mul_pos hey
      linarith
  have hρ := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx
  simp only [ρ, zero_sub, exp_zero, mul_one] at hρ
  have e := expm1_pos hx
  rw [lt_div_iff₀ e]
  nlinarith

/-- B(x) の上の限界 B(x) < 1 − x/2 + x²（x > 0）。 -/
theorem B_upper {x : ℝ} (hx : 0 < x) : x / (exp x - 1) < 1 - x / 2 + x ^ 2 := by
  have e := expm1_pos hx
  rw [div_lt_iff₀ e]
  have hq := quadratic_le_exp_of_nonneg hx.le
  have hP : 0 < 1 - x / 2 + x ^ 2 := by nlinarith [sq_nonneg (x - 1 / 4)]
  have : (1 - x / 2 + x ^ 2) * (x + x ^ 2 / 2) ≤ (1 - x / 2 + x ^ 2) * (exp x - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hP.le
  nlinarith [pow_pos hx 3, pow_pos hx 4]

/-- c/(e^(c/T) − 1) の上下の限界：T − c/2 < · < T − c/2 + c²/T。 -/
theorem frac_bounds {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    T - c / 2 < c / (exp (c / T) - 1) ∧ c / (exp (c / T) - 1) < T - c / 2 + c ^ 2 / T := by
  have hx : 0 < c / T := by positivity
  have e : c / (exp (c / T) - 1) = T * ((c / T) / (exp (c / T) - 1)) := by field_simp
  rw [e]
  constructor
  · have := mul_lt_mul_of_pos_left (B_lower hx) hT
    have h : T * (1 - c / T / 2) = T - c / 2 := by field_simp
    linarith
  · have := mul_lt_mul_of_pos_left (B_upper hx) hT
    have h : T * (1 - c / T / 2 + (c / T) ^ 2) = T - c / 2 + c ^ 2 / T := by field_simp
    linarith

/-- (3) T → ∞ で T·S → (a − b)/2（ちょうど半分）。 -/
theorem TS_tendsto_atTop (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun T => T * S a b T) atTop (𝓝 ((a - b) / 2)) := by
  have hz : ∀ c : ℝ, Tendsto (fun T : ℝ => c / T) atTop (𝓝 0) :=
    fun c => Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have hlo : Tendsto (fun T => (a - b) / 2 - b ^ 2 / T) atTop (𝓝 ((a - b) / 2)) := by
    simpa using (hz (b ^ 2)).const_sub ((a - b) / 2)
  have hhi : Tendsto (fun T => (a - b) / 2 + a ^ 2 / T) atTop (𝓝 ((a - b) / 2)) := by
    simpa using (hz (a ^ 2)).const_add ((a - b) / 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_gt_atTop 0] with T hT
    rw [TS_eq ha hb hT]
    have := (frac_bounds ha hT).1
    have := (frac_bounds hb hT).2
    linarith
  · filter_upwards [eventually_gt_atTop 0] with T hT
    rw [TS_eq ha hb hT]
    have := (frac_bounds ha hT).2
    have := (frac_bounds hb hT).1
    linarith

/-- (3) どの T でも (a − b)/2 < T·S < a − b。 -/
theorem TS_bounds (ha : 0 < a) (hb : 0 < b) (hab : b < a) {T : ℝ} (hT : 0 < T) :
    (a - b) / 2 < T * S a b T ∧ T * S a b T < a - b := by
  have hanti := TS_strictAntiOn hb hab
  constructor
  · have h2 : (a - b) / 2 ≤ (2 * T) * S a b (2 * T) := by
      apply le_of_tendsto (TS_tendsto_atTop ha hb)
      filter_upwards [eventually_ge_atTop (2 * T)] with t ht
      exact hanti.antitoneOn (mem_Ioi.mpr (by positivity) : 2 * T ∈ Ioi (0 : ℝ))
        (show t ∈ Ioi 0 from lt_of_lt_of_le (by positivity) ht) ht
    exact lt_of_le_of_lt h2
      (hanti hT (mem_Ioi.mpr (by positivity) : 2 * T ∈ Ioi (0 : ℝ)) (by linarith))
  · have h2 : (T / 2) * S a b (T / 2) ≤ a - b := by
      apply ge_of_tendsto (TS_tendsto_zero ha hb)
      have : Ioo (0 : ℝ) (T / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
      filter_upwards [this] with t ht
      exact hanti.antitoneOn ht.1 (mem_Ioi.mpr (by positivity) : T / 2 ∈ Ioi (0 : ℝ)) ht.2.le
    exact lt_of_lt_of_le
      (hanti (mem_Ioi.mpr (by positivity) : T / 2 ∈ Ioi (0 : ℝ)) hT (by linarith)) h2

/-- (4) S は T について狭義に減る。 -/
theorem S_strictAntiOn (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    StrictAntiOn (S a b) (Ioi 0) := by
  intro T₁ h₁ T₂ h₂ hT
  have h₁ : (0 : ℝ) < T₁ := h₁
  have h₂ : (0 : ℝ) < T₂ := h₂
  have hts := TS_strictAntiOn hb hab (show T₁ ∈ Ioi 0 from h₁) (show T₂ ∈ Ioi 0 from h₂) hT
  simp only at hts
  have hS1 := S_pos ha hb hab h₁
  have hS2 := S_pos ha hb hab h₂
  by_contra hc
  push Not at hc
  have : T₁ * S a b T₁ < T₂ * S a b T₂ := by
    calc T₁ * S a b T₁ < T₂ * S a b T₁ := mul_lt_mul_of_pos_right hT hS1
      _ ≤ T₂ * S a b T₂ := mul_le_mul_of_nonneg_left hc h₂.le
  linarith

/-- (4) T → ∞ で S → 0。 -/
theorem S_tendsto_atTop (ha : 0 < a) (hb : 0 < b) (hab : b < a) :
    Tendsto (S a b) atTop (𝓝 0) := by
  have hup : Tendsto (fun T : ℝ => (a - b) / T) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_id
  apply squeeze_zero' _ _ hup
  · filter_upwards [eventually_gt_atTop 0] with T hT
    exact (S_pos ha hb hab hT).le
  · filter_upwards [eventually_gt_atTop 0] with T hT
    rw [le_div_iff₀ hT, mul_comm]
    exact (TS_bounds ha hb hab hT).2.le

/-- (5) 振動数あたりの比は R/(a/b)²。 -/
theorem Rnu_eq (ha : 0 < a) (hb : 0 < b) (T : ℝ) : Rnu a b T = R a b T / (a / b) ^ 2 := by
  unfold Rnu R
  field_simp

/-- (5) 振動数あたりでも効きは同じ S。 -/
theorem hasDerivAt_logRnu (ha : 0 < a) (hb : 0 < b) (u : ℝ) :
    HasDerivAt (fun v => log (Rnu a b (exp v))) (S a b (exp u)) u := by
  have e : (fun v => log (Rnu a b (exp v))) = fun v => log (R a b (exp v)) - 2 * log (a / b) := by
    funext v
    rw [Rnu_eq ha hb, log_div (ne_of_gt (R_pos ha hb (exp_pos v))) (by positivity), log_pow]
    push_cast; ring
  rw [e]
  have := (hasDerivAt_logR ha hb u).sub_const (2 * log (a / b))
  exact this

end Pair

/-- (6) 原稿の c₂ = 1.43877688×10⁻² m K と 440 nm・550 nm での二つの極限。 -/
theorem paper_limits :
    let a : ℝ := 1.43877688e-2 / 440e-9
    let b : ℝ := 1.43877688e-2 / 550e-9
    (6539.894 < a - b ∧ a - b < 6539.896) ∧ (3269.947 < (a - b) / 2 ∧ (a - b) / 2 < 3269.948) := by
  intro a b
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> norm_num [a, b]

end Paper943

end Yamagishi
