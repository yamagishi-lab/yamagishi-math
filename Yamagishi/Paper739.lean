/-
論文739『スプリンクラーの遅れは部品の定数ではない。火が育つほど気流が速くなり、遅れそのものが縮む』の
格上げ（一般の形）。

日本語の一文：感知部の式 dT_L/dt = (√u/RTI)(T_g − T_L) で、天井流が ΔT_g = a t^(4/3)、√u = b t^(1/3)
（t² の火にアルパートの相関を当てた形）のとき、感知部の温度は閉じた形 ΔT_g[1 − (1 − e^(−w))/w]
（w = (3b/(4RTI)) t^(4/3)）になり、RTI₁ < RTI₂ ならどの a・b・作動温度でも作動時刻の比は 1 より大きく
(RTI₂/RTI₁)^(3/8) より小さい。
English: For the link equation dT_L/dt = (√u/RTI)(T_g − T_L) with a ceiling jet ΔT_g = a t^(4/3),
√u = b t^(1/3) (Alpert's correlations for a t² fire), the link temperature is
ΔT_g[1 − (1 − e^(−w))/w], w = (3b/(4RTI)) t^(4/3), and for RTI₁ < RTI₂ the activation times satisfy
1 < t₂/t₁ < (RTI₂/RTI₁)^(3/8) for every a, b and activation temperature.

原稿（739_yamagishi_the_lag_of_a_sprinkler_shrinks_as_the_fire_grows/…_jp.tex）は、天井 3 m・水平距離
2 m・α = 0.0469 kW/s²・作動 68 ℃の一組で、RTI 35・50・100・250 の作動時刻（104.78〜182.59 秒、
比 1.742604）を数値積分で出し、RTI の比 7.142857 が作動時刻の比に写らないことを示している。
閉じた形と比の限界は書いていない。

ここで証明した言明（a, b, RTI > 0、温度は周囲からの上がり）：
  (1) `hasDerivAt_TL`・`TL_zero`：閉じた形 T_L(t) = (4a·RTI/(3b))·g(w)、g(w) = w − 1 + e^(−w) は、t > 0 で
      感知部の式を満たし、T_L(0) = 0。`TL_closed_form`：T_L = ΔT_g[1 − (1 − e^(−w))/w]。
      `solution_unique`：[0, ∞) で連続で y(0) = 0 の解はこの閉じた形だけ。
  (2) `activation_exists_unique`：作動温度の上がり Δ > 0 に届く時刻 t_a > 0 はちょうど一つ。
      `activation_after_gas`：作動の時には天井流のほうが熱い（a t_a^(4/3) > Δ、遅れの無い極限より遅い）。
  (3) `activation_ratio`：RTI₁ < RTI₂ なら 1 < t₂/t₁ < (RTI₂/RTI₁)^(3/8)（a、b、Δ によらない）。
      芯は w > 0 での二つの不等式：w/g(w) は狭義に減る（`psi_strictAnti`）、w²/g(w) は狭義に増える
      （`phi_strictMono`）。
  (4) `time_constant_ratio`：作動の時の時定数 τ = RTI/(b t_a^(1/3)) の比は
      (RTI₂/RTI₁)^(7/8) < τ₂/τ₁ < RTI₂/RTI₁（遅れそのものが RTI の比より縮む）。
      `fire_ratio`：作動の時の火 Q ∝ t_a² の比は 1 < Q₂/Q₁ < (RTI₂/RTI₁)^(3/4)。
  (5) `lag_tendsto`：温度の遅れ ΔT_g − T_L は 4a·RTI/(3b)（= (4/3)(a/b)RTI）に近づく。
足した仮定：アルパートの相関の冪（ΔT_g ∝ Q^(2/3)、u ∝ Q^(1/3)）と Q ∝ t² を、ΔT_g = a t^(4/3)、
√u = b t^(1/3) の形で定義に置いた（高さと水平距離を固定した形）。天井流の到達の遅れと配管への熱の
逃げ（C 係数）は入れない。
形式化していないもの：原稿の数値積分の表、弾性 d ln t_a/d ln RTI が RTI → 0 で 0、RTI → ∞ で 3/8 に
近づくこと（比の形の限界は (3) で証明した）、t^p の火（p ≠ 2）、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper739

open Real Set Filter Topology

/-! ### 芯：g(w) = w − 1 + e^(−w) -/

/-- g(w) = w − 1 + e^(−w)。 -/
noncomputable def g (w : ℝ) : ℝ := w - 1 + exp (-w)

theorem hasDerivAt_g (w : ℝ) : HasDerivAt g (1 - exp (-w)) w := by
  have := ((hasDerivAt_id' w).sub_const 1).add ((hasDerivAt_neg w).exp)
  unfold g
  convert this using 1
  ring

theorem g_zero : g 0 = 0 := by simp [g]

theorem g_pos {w : ℝ} (hw : 0 < w) : 0 < g w := by
  unfold g
  have := add_one_lt_exp (x := -w) (by linarith)
  linarith

theorem g_lt {w : ℝ} (hw : 0 < w) : g w < w := by
  unfold g
  have : exp (-w) < 1 := by rw [← exp_zero]; exact exp_lt_exp.mpr (by linarith)
  linarith

theorem one_sub_exp_pos {w : ℝ} (hw : 0 < w) : 0 < 1 - exp (-w) := by
  have : exp (-w) < 1 := by rw [← exp_zero]; exact exp_lt_exp.mpr (by linarith)
  linarith

theorem g_strictMonoOn : StrictMonoOn g (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact fun w _ => (hasDerivAt_g w).continuousAt.continuousWithinAt
  · intro w hw
    rw [interior_Ici] at hw
    rw [(hasDerivAt_g w).deriv]
    exact one_sub_exp_pos hw

/-- (1 + w)e^(−w) < 1（w > 0）。 -/
theorem one_add_mul_exp_lt {w : ℝ} (hw : 0 < w) : (1 + w) * exp (-w) < 1 := by
  have h := add_one_lt_exp (x := w) (ne_of_gt hw)
  have he : exp w * exp (-w) = 1 := by rw [← exp_add]; simp
  have := exp_pos (-w)
  nlinarith

/-- ψ(w) = w/g(w) は (0, ∞) で狭義に減る。 -/
theorem psi_strictAnti : StrictAntiOn (fun w => w / g w) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro w hw
    exact ((continuousAt_id.div (hasDerivAt_g w).continuousAt
      (ne_of_gt (g_pos hw)))).continuousWithinAt
  · intro w hw
    rw [interior_Ioi] at hw
    have hg := g_pos hw
    have hd : HasDerivAt (fun x => x / g x) ((1 * g w - w * (1 - exp (-w))) / g w ^ 2) w :=
      (hasDerivAt_id' w).div (hasDerivAt_g w) (ne_of_gt hg)
    rw [hd.deriv]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have := one_add_mul_exp_lt hw
    unfold g
    nlinarith

/-- f(w) = w − 2 + (2 + w)e^(−w) は w > 0 で正。 -/
theorem f_pos {w : ℝ} (hw : 0 < w) : 0 < w - 2 + (2 + w) * exp (-w) := by
  have hd : ∀ x, HasDerivAt (fun x => x - 2 + (2 + x) * exp (-x))
      (1 - (1 + x) * exp (-x)) x := by
    intro x
    have := ((hasDerivAt_id' x).sub_const 2).add
      (((hasDerivAt_id' x).const_add 2).mul ((hasDerivAt_neg x).exp))
    convert this using 1
    ring
  have hmono : StrictMonoOn (fun x => x - 2 + (2 + x) * exp (-x)) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      have := one_add_mul_exp_lt hx
      linarith
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hw.le) hw
  simp at this
  linarith

/-- φ(w) = w²/g(w) は (0, ∞) で狭義に増える。 -/
theorem phi_strictMono : StrictMonoOn (fun w => w ^ 2 / g w) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro w hw
    exact (((continuous_pow 2).continuousAt).div (hasDerivAt_g w).continuousAt
      (ne_of_gt (g_pos hw))).continuousWithinAt
  · intro w hw
    rw [interior_Ioi] at hw
    have hg := g_pos hw
    have hd : HasDerivAt (fun x => x ^ 2 / g x)
        ((↑2 * w ^ (2 - 1) * g w - w ^ 2 * (1 - exp (-w))) / g w ^ 2) w :=
      (hasDerivAt_pow 2 w).div (hasDerivAt_g w) (ne_of_gt hg)
    rw [hd.deriv]
    apply div_pos _ (by positivity)
    have := f_pos hw
    unfold g
    have e : (↑2 : ℝ) * w ^ (2 - 1) * (w - 1 + exp (-w)) - w ^ 2 * (1 - exp (-w)) =
        w * (w - 2 + (2 + w) * exp (-w)) := by norm_num; ring
    rw [e]
    exact mul_pos hw this

/-! ### 模型 -/

/-- w(t) = (3b/(4RTI)) t^(4/3)。 -/
noncomputable def w (b c t : ℝ) : ℝ := 3 * b / (4 * c) * t ^ (4 / 3 : ℝ)

/-- 感知部の温度の上がり T_L(t) = (4a·RTI/(3b))·g(w(t))。 -/
noncomputable def TL (a b c t : ℝ) : ℝ := 4 * a * c / (3 * b) * g (w b c t)

/-- 天井流の温度の上がり ΔT_g = a t^(4/3)。 -/
noncomputable def Tg (a t : ℝ) : ℝ := a * t ^ (4 / 3 : ℝ)

/-- 感知部の式の右辺 (√u/RTI)(T_g − T_L)、√u = b t^(1/3)。 -/
noncomputable def rhs (a b c t T : ℝ) : ℝ := b * t ^ (1 / 3 : ℝ) / c * (Tg a t - T)

theorem Tg_eq {a b c t : ℝ} (hb : 0 < b) (hc : 0 < c) :
    Tg a t = 4 * a * c / (3 * b) * w b c t := by
  unfold Tg w
  field_simp

theorem TL_zero (a b c : ℝ) : TL a b c 0 = 0 := by
  simp [TL, w, g_zero, zero_rpow (show (4 / 3 : ℝ) ≠ 0 by norm_num)]

theorem hasDerivAt_w {b c t : ℝ} (ht : 0 < t) :
    HasDerivAt (w b c) (3 * b / (4 * c) * ((4 / 3 : ℝ) * t ^ ((4 / 3 : ℝ) - 1))) t :=
  (hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).const_mul _

/-- (1) 閉じた形は感知部の式を満たす。 -/
theorem hasDerivAt_TL {a b c t : ℝ} (hb : 0 < b) (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (TL a b c) (rhs a b c t (TL a b c t)) t := by
  have h := ((hasDerivAt_g (w b c t)).comp t (hasDerivAt_w (b := b) (c := c) ht)).const_mul
    (4 * a * c / (3 * b))
  unfold TL
  refine h.congr_deriv ?_
  unfold rhs
  rw [Tg_eq hb hc]
  unfold g
  have e : (4 / 3 : ℝ) - 1 = 1 / 3 := by norm_num
  rw [e]
  field_simp
  ring

/-- (1) 閉じた形：T_L = ΔT_g[1 − (1 − e^(−w))/w]（t > 0）。 -/
theorem TL_closed_form {a b c t : ℝ} (hb : 0 < b) (hc : 0 < c) (ht : 0 < t) :
    TL a b c t = Tg a t * (1 - (1 - exp (-w b c t)) / w b c t) := by
  have hw : 0 < w b c t := by unfold w; positivity
  rw [Tg_eq hb hc]
  unfold TL g
  field_simp
  ring

theorem w_pos {b c t : ℝ} (hb : 0 < b) (hc : 0 < c) (ht : 0 < t) : 0 < w b c t := by
  unfold w; positivity

/-- (2) 作動の時には天井流のほうが熱い。 -/
theorem activation_after_gas {a b c t Δ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ht : 0 < t) (h : TL a b c t = Δ) : Δ < Tg a t := by
  rw [← h, Tg_eq hb hc]
  unfold TL
  have := g_lt (w_pos hb hc ht)
  have : 0 < 4 * a * c / (3 * b) := by positivity
  nlinarith

theorem w_strictMonoOn {b c : ℝ} (hb : 0 < b) (hc : 0 < c) : StrictMonoOn (w b c) (Ici 0) := by
  intro x hx y hy hxy
  unfold w
  have : x ^ (4 / 3 : ℝ) < y ^ (4 / 3 : ℝ) := rpow_lt_rpow hx hxy (by norm_num)
  have : 0 < 3 * b / (4 * c) := by positivity
  nlinarith

theorem TL_strictMonoOn {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    StrictMonoOn (TL a b c) (Ici 0) := by
  intro x hx y hy hxy
  unfold TL
  have hw0 : ∀ s, s ∈ Ici (0 : ℝ) → 0 ≤ w b c s := fun s hs => by
    unfold w; have := rpow_nonneg (mem_Ici.mp hs) (4 / 3 : ℝ); positivity
  have := g_strictMonoOn (mem_Ici.mpr (hw0 x hx)) (mem_Ici.mpr (hw0 y hy))
    (w_strictMonoOn hb hc hx hy hxy)
  have : 0 < 4 * a * c / (3 * b) := by positivity
  nlinarith

theorem continuous_g : Continuous g :=
  (continuous_id.sub continuous_const).add continuous_neg.rexp

theorem continuous_TL (a b c : ℝ) : Continuous (TL a b c) := by
  have h1 : Continuous (fun t : ℝ => t ^ (4 / 3 : ℝ)) :=
    continuous_id.rpow_const (fun _ => Or.inr (by norm_num))
  have h2 : Continuous (w b c) := continuous_const.mul h1
  exact continuous_const.mul (continuous_g.comp h2)

/-- (2) 作動の時刻はちょうど一つ。 -/
theorem activation_exists_unique {a b c Δ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hΔ : 0 < Δ) : ∃! t, 0 < t ∧ TL a b c t = Δ := by
  set M := (Δ + 4 * a * c / (3 * b)) / a with hM
  have hM0 : 0 < M := by positivity
  set T := M ^ (3 / 4 : ℝ) with hT
  have hT0 : 0 < T := rpow_pos_of_pos hM0 _
  have hTpow : T ^ (4 / 3 : ℝ) = M := by
    rw [hT, ← rpow_mul hM0.le]; norm_num
  have hTge : Δ ≤ TL a b c T := by
    unfold TL g
    have hw : w b c T = 3 * b / (4 * c) * M := by unfold w; rw [hTpow]
    rw [hw]
    have he := exp_pos (-(3 * b / (4 * c) * M))
    have hk : 4 * a * c / (3 * b) * (3 * b / (4 * c) * M) = Δ + 4 * a * c / (3 * b) := by
      rw [hM]; field_simp
    have : 0 < 4 * a * c / (3 * b) := by positivity
    nlinarith
  obtain ⟨t, htI, htv⟩ := intermediate_value_Icc hT0.le (continuous_TL a b c).continuousOn
    (show Δ ∈ Icc (TL a b c 0) (TL a b c T) by rw [TL_zero]; exact ⟨hΔ.le, hTge⟩)
  have ht0 : 0 < t := by
    rcases eq_or_lt_of_le htI.1 with h | h
    · rw [← h, TL_zero] at htv; linarith
    · exact h
  refine ⟨t, ⟨ht0, htv⟩, ?_⟩
  rintro s ⟨hs0, hs⟩
  exact (TL_strictMonoOn ha hb hc).injOn (mem_Ici.mpr hs0.le) (mem_Ici.mpr ht0.le)
    (hs.trans htv.symm)

/-- (1) 解の一意性：[0, ∞) で連続、y(0) = 0、t > 0 で感知部の式を満たす y は閉じた形に等しい。 -/
theorem solution_unique {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) {y : ℝ → ℝ}
    (hy : ContinuousOn y (Ici 0)) (hy0 : y 0 = 0)
    (hyd : ∀ t, 0 < t → HasDerivAt y (rhs a b c t (y t)) t) :
    ∀ t, 0 ≤ t → y t = TL a b c t := by
  have hwc : Continuous (w b c) :=
    continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num)))
  set F := fun t => (y t - TL a b c t) * exp (w b c t) with hF
  have hFd : ∀ t, 0 < t → HasDerivAt F 0 t := by
    intro t ht
    have h1 := ((hyd t ht).sub (hasDerivAt_TL (a := a) hb hc ht)).mul
      ((hasDerivAt_w (b := b) (c := c) ht).exp)
    refine h1.congr_deriv ?_
    unfold rhs
    have e : (4 / 3 : ℝ) - 1 = 1 / 3 := by norm_num
    rw [e]
    simp only [Pi.sub_apply]
    field_simp
    ring
  have hFc : ContinuousOn F (Ici 0) :=
    (hy.sub (continuous_TL a b c).continuousOn).mul (hwc.rexp.continuousOn)
  intro t ht
  rcases eq_or_lt_of_le ht with h0 | hpos
  · rw [← h0, hy0, TL_zero]
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope F (fun _ => 0) hpos
      (hFc.mono Icc_subset_Ici_self) (fun x hx => hFd x hx.1)
    have hF0 : F 0 = 0 := by simp [hF, hy0, TL_zero]
    rw [hF0, sub_zero, eq_div_iff (by linarith), zero_mul] at hslope
    have : (y t - TL a b c t) * exp (w b c t) = 0 := hslope.symm
    have := (mul_eq_zero.mp this).resolve_right (exp_pos _).ne'
    linarith

/-! ### 作動時刻の比 -/

/-- 作動の条件は g(w) = K/RTI（K = 3bΔ/(4a)）。 -/
theorem activation_g {a b c t Δ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : TL a b c t = Δ) : g (w b c t) = 3 * b * Δ / (4 * a) / c := by
  rw [← h]
  unfold TL
  field_simp

/-- t^(4/3) = (4/(3b))·RTI·w。 -/
theorem pow_eq {b c t : ℝ} (hb : 0 < b) (hc : 0 < c) :
    t ^ (4 / 3 : ℝ) = 4 * c / (3 * b) * w b c t := by
  unfold w; field_simp

/-- x, y > 0 で x < y^(3/8) ⇔ x^(4/3) < √y。 -/
theorem lt_rpow_38_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x < y ^ (3 / 8 : ℝ) ↔ x ^ (4 / 3 : ℝ) < √y := by
  rw [← rpow_lt_rpow_iff hx.le (rpow_nonneg hy.le _) (show (0 : ℝ) < 4 / 3 by norm_num),
    ← rpow_mul hy.le, sqrt_eq_rpow]
  norm_num

/-- 作動の時の t^(4/3) を ψ(w) で書く：g(w) = K/RTI なら t^(4/3) = (4K/(3b))·w/g(w)。 -/
theorem pow_psi {b c t K : ℝ} (hb : 0 < b) (hc : 0 < c) (ht : 0 < t)
    (hg : g (w b c t) = K / c) :
    t ^ (4 / 3 : ℝ) = 4 * K / (3 * b) * (w b c t / g (w b c t)) := by
  have hgp := g_pos (w_pos hb hc ht)
  have hK : g (w b c t) * c = K := by rw [hg]; field_simp
  rw [pow_eq hb hc, ← hK]
  field_simp

/-- (3) RTI₁ < RTI₂ なら 1 < t₂/t₁ < (RTI₂/RTI₁)^(3/8)。 -/
theorem activation_ratio {a b Δ c1 c2 t1 t2 : ℝ} (ha : 0 < a) (hb : 0 < b) (hΔ : 0 < Δ)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (h1 : TL a b c1 t1 = Δ) (h2 : TL a b c2 t2 = Δ) :
    1 < t2 / t1 ∧ t2 / t1 < (c2 / c1) ^ (3 / 8 : ℝ) := by
  have hc2 : 0 < c2 := hc1.trans hc12
  have hK0 : 0 < 3 * b * Δ / (4 * a) := by positivity
  have hg1 := activation_g ha hb hc1 h1
  have hg2 := activation_g ha hb hc2 h2
  have hp1 := pow_psi hb hc1 ht1 hg1
  have hp2 := pow_psi hb hc2 ht2 hg2
  have hw1 : 0 < w b c1 t1 := w_pos hb hc1 ht1
  have hw2 : 0 < w b c2 t2 := w_pos hb hc2 ht2
  have hcg1 : g (w b c1 t1) * c1 = 3 * b * Δ / (4 * a) := by rw [hg1]; field_simp
  have hcg2 : g (w b c2 t2) * c2 = 3 * b * Δ / (4 * a) := by rw [hg2]; field_simp
  generalize w b c1 t1 = w1 at *
  generalize w b c2 t2 = w2 at *
  generalize 3 * b * Δ / (4 * a) = K at *
  have hgp1 := g_pos hw1
  have hgp2 := g_pos hw2
  -- w₂ < w₁
  have hw21 : w2 < w1 := by
    by_contra hc; push Not at hc
    have := g_strictMonoOn.monotoneOn (mem_Ici.mpr hw1.le) (mem_Ici.mpr hw2.le) hc
    rw [hg1, hg2] at this
    have : K / c2 < K / c1 := div_lt_div_of_pos_left hK0 hc1 hc12
    linarith
  have hpsi := psi_strictAnti (mem_Ioi.mpr hw2) (mem_Ioi.mpr hw1) hw21
  have hphi := phi_strictMono (mem_Ioi.mpr hw2) (mem_Ioi.mpr hw1) hw21
  simp only at hpsi hphi
  have hq : 0 < t2 / t1 := div_pos ht2 ht1
  have hratio : (t2 / t1) ^ (4 / 3 : ℝ) = (w2 / g w2) / (w1 / g w1) := by
    rw [div_rpow ht2.le ht1.le, hp1, hp2]
    have : 0 < w1 / g w1 := div_pos hw1 hgp1
    have : 0 < 4 * K / (3 * b) := by positivity
    field_simp
  constructor
  · rw [← rpow_lt_rpow_iff zero_le_one hq.le (show (0 : ℝ) < 4 / 3 by norm_num), one_rpow,
      hratio, one_lt_div (div_pos hw1 hgp1)]
    exact hpsi
  · rw [lt_rpow_38_iff hq (div_pos hc2 hc1), hratio]
    have hcc : c2 / c1 = g w1 / g w2 := by
      field_simp
      nlinarith [hcg1, hcg2]
    rw [hcc, lt_sqrt (div_pos (div_pos hw2 hgp2) (div_pos hw1 hgp1)).le]
    rw [div_lt_div_iff₀ hgp2 hgp1] at hphi
    rw [div_pow, div_pow, div_pow, div_div_div_eq, div_lt_div_iff₀ (by positivity) hgp2]
    nlinarith [mul_pos (pow_pos hw1 2) hgp1, mul_pos hgp1 hgp2, mul_pos (pow_pos hgp1 2) hgp2]

/-- (4) 作動の時の時定数の比：(RTI₂/RTI₁)^(7/8) < τ₂/τ₁ < RTI₂/RTI₁。
τ_i = RTI_i/(b t_i^(1/3)) なので τ₂/τ₁ = (RTI₂/RTI₁)·(t₂/t₁)^(−1/3)。 -/
theorem time_constant_ratio {a b Δ c1 c2 t1 t2 : ℝ} (ha : 0 < a) (hb : 0 < b) (hΔ : 0 < Δ)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (h1 : TL a b c1 t1 = Δ) (h2 : TL a b c2 t2 = Δ) :
    (c2 / c1) ^ (7 / 8 : ℝ) < (c2 / c1) * (t2 / t1) ^ (-(1 / 3) : ℝ) ∧
      (c2 / c1) * (t2 / t1) ^ (-(1 / 3) : ℝ) < c2 / c1 := by
  obtain ⟨hlo, hhi⟩ := activation_ratio ha hb hΔ hc1 hc12 ht1 ht2 h1 h2
  have hr : 1 < c2 / c1 := by rw [one_lt_div hc1]; exact hc12
  have hr0 : 0 < c2 / c1 := by linarith
  have hq : 0 < t2 / t1 := by linarith
  constructor
  · -- (t₂/t₁)^(−1/3) > ((c₂/c₁)^(3/8))^(−1/3) = (c₂/c₁)^(−1/8)
    have h3 : ((c2 / c1) ^ (3 / 8 : ℝ)) ^ (-(1 / 3) : ℝ) < (t2 / t1) ^ (-(1 / 3) : ℝ) :=
      rpow_lt_rpow_of_neg hq hhi (by norm_num)
    rw [← rpow_mul hr0.le] at h3
    have e : (c2 / c1) ^ (7 / 8 : ℝ) = (c2 / c1) * (c2 / c1) ^ ((3 / 8 : ℝ) * (-(1 / 3))) := by
      rw [show (7 / 8 : ℝ) = 1 + (3 / 8) * (-(1 / 3)) by norm_num, rpow_add hr0, rpow_one]
    rw [e]
    exact mul_lt_mul_of_pos_left h3 hr0
  · have h3 : (t2 / t1) ^ (-(1 / 3) : ℝ) < 1 :=
      rpow_lt_one_of_one_lt_of_neg hlo (by norm_num)
    calc (c2 / c1) * (t2 / t1) ^ (-(1 / 3) : ℝ) < (c2 / c1) * 1 :=
          mul_lt_mul_of_pos_left h3 hr0
      _ = c2 / c1 := mul_one _

/-- (4) 作動の時の火（Q ∝ t²）の比：1 < (t₂/t₁)² < (RTI₂/RTI₁)^(3/4)。 -/
theorem fire_ratio {a b Δ c1 c2 t1 t2 : ℝ} (ha : 0 < a) (hb : 0 < b) (hΔ : 0 < Δ)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (h1 : TL a b c1 t1 = Δ) (h2 : TL a b c2 t2 = Δ) :
    1 < (t2 / t1) ^ 2 ∧ (t2 / t1) ^ 2 < (c2 / c1) ^ (3 / 4 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := activation_ratio ha hb hΔ hc1 hc12 ht1 ht2 h1 h2
  have hr0 : 0 < c2 / c1 := div_pos (hc1.trans hc12) hc1
  constructor
  · nlinarith
  · have : (t2 / t1) ^ 2 < ((c2 / c1) ^ (3 / 8 : ℝ)) ^ 2 :=
      pow_lt_pow_left₀ hhi (by linarith) two_ne_zero
    have e : ((c2 / c1) ^ (3 / 8 : ℝ)) ^ 2 = (c2 / c1) ^ (3 / 4 : ℝ) := by
      rw [← rpow_natCast, ← rpow_mul hr0.le]; norm_num
    rw [e] at this
    exact this

/-- (5) 温度の遅れ ΔT_g − T_L は 4a·RTI/(3b) に近づく。 -/
theorem lag_tendsto {a b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun t => Tg a t - TL a b c t) atTop (𝓝 (4 * a * c / (3 * b))) := by
  have hw : Tendsto (w b c) atTop atTop := by
    unfold w
    exact (tendsto_rpow_atTop (by norm_num)).const_mul_atTop (by positivity)
  have he : Tendsto (fun t => exp (-w b c t)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hw)
  have hEq : ∀ t, Tg a t - TL a b c t = 4 * a * c / (3 * b) * (1 - exp (-w b c t)) := by
    intro t
    rw [Tg_eq hb hc]; unfold TL g; ring
  simp_rw [hEq]
  have := ((tendsto_const_nhds (x := (1 : ℝ))).sub he).const_mul (4 * a * c / (3 * b))
  simpa using this

end Paper739

end Yamagishi
