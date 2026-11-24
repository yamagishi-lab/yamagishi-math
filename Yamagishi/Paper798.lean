/-
論文798『体温で死後の時間を読むとき、遅い時刻の誤差を決めるのは温度計ではなく周りの気温である』の
格上げ（一般の形）。

日本語の一文：冷えの割合 Q(t) = (T − Ta)/(T0 − Ta) が気温によらない単調な式なら、どんな冷え方の式でも、
気温を δa 誤ったときと体温を δT 誤ったときの読む時刻の一次のずれの比は δa(1 − Q)/δT で、気温の側が
追い越すのは 1 − Q = δT/δa のときであり、ヘンスゲの式では温度計の誤差が最小になるのは
t = ln 5/(4|B|) のときに限る。
English: If the cooling fraction Q(t) = (T − Ta)/(T0 − Ta) is a monotone law that does not depend
on the air temperature, then for every such law the first-order time shifts from an air-temperature
error δa and a thermometer error δT are in the ratio δa(1 − Q)/δT, so the air error overtakes
exactly when 1 − Q = δT/δa; for Henssge's law the thermometer error is smallest only at
t = ln 5/(4|B|).

原稿（798_yamagishi_late_hours_are_limited_by_air_temperature_not_the_thermometer/…_jp.tex）は、
体重 70 kg・T0 = 37.2 ℃・Ta = 18 ℃ の一組で、温度計 ±0.1 ℃と気温 ±1 ℃のずれを時刻ごとに数値で出し、
追い越しの時刻 3.980859 時間、24 時間の比 8.119852、変曲点 6.525445 時間を出している。平坦部を
無視したずれ ln 1.25/B と変曲点の式は書いてあるが、追い越しの一般の条件は無い。

ここで証明した言明：
  (1) `hasDerivAt_G_T`・`hasDerivAt_G_Ta`：割合 G = (T − Ta)/(T0 − Ta) の体温と気温での微分は
      1/(T0 − Ta) と −(1 − G)/(T0 − Ta)。
      `reading_derivs`：Q の逆の関数で時刻を読むと（Q の微分 Q′ ≠ 0、逆が連続）、読む時刻の微分は
      1/((T0 − Ta)Q′) と −(1 − Q)/((T0 − Ta)Q′)。
  (2) `shift_ratio`：一次のずれの比 |∂_a|δa/(|∂_T|δT) = δa(1 − Q)/δT（冷え方の式にも体重にもよらない）。
      `overtake_iff`：気温の側が温度計の側以上 ⇔ 1 − Q ≥ δT/δa。
  (3) ヘンスゲの式 Q_H(t) = 1.25 e^(Bt) − 0.25 e^(5Bt)（B < 0）について：
      `QH_zero`・`QH_pos`・`QH_strictAntiOn`：Q_H(0) = 1、Q_H > 0、t ≥ 0 で狭義に減る。
      `deriv_QH_neg`：t > 0 で dQ_H/dt < 0（t = 0 では傾き 0 の平坦部）。
      `steepest`：t ≥ 0 で |dQ_H/dt| は t* = ln 5/(4|B|) でただ一つの最大をとる。
      `thermometer_min`：温度計の一次のずれ δT/((T0 − Ta)|Q_H′|) は t* でただ一つの最小をとる。
      `QH_scale`：Q_H(B, t) = Q_H(−1, |B|t)（体重は時間の尺度だけを変える）。
  (4) `newton_shift`・`newton_shift_tendsto`：同じ B のニュートンの冷却則で読んだ時刻のずれは
      ln(1.25 − 0.25 e^(4Bt))/B で、t → ∞ で ln 1.25/B（時定数の ln 1.25 倍）に近づく。
足した仮定：冷えの割合 Q が気温によらないこと（ヘンスゲの式は気温 23 ℃を境に係数が変わるので、
取り違えがその境をまたぐと成り立たない）。誤差は一次の式で扱う（原稿の 3.980859 時間は大きいほうの側を
正確に解いた値で、一次では Q = 0.9 の時刻、約 4.103798 時間になる）。
形式化していないもの：原稿の数表、正確に解いたときの追い越しの時刻、0.5 時間の窓、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper798

open Real Set Filter Topology

/-! ### 一般の冷え方の式 -/

/-- 読む割合 G(T, Ta) = (T − Ta)/(T0 − Ta)。 -/
noncomputable def G (T0 T Ta : ℝ) : ℝ := (T - Ta) / (T0 - Ta)

theorem hasDerivAt_G_T (T0 T Ta : ℝ) :
    HasDerivAt (fun x => G T0 x Ta) (1 / (T0 - Ta)) T := by
  unfold G
  have := ((hasDerivAt_id' T).sub_const Ta).div_const (T0 - Ta)
  simpa using this

theorem hasDerivAt_G_Ta {T0 T Ta : ℝ} (h : Ta ≠ T0) :
    HasDerivAt (fun a => G T0 T a) (-(1 - G T0 T Ta) / (T0 - Ta)) Ta := by
  have hne : T0 - Ta ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have h1 : HasDerivAt (fun a => T - a) (-1) Ta := (hasDerivAt_id' Ta).const_sub T
  have h2 : HasDerivAt (fun a => T0 - a) (-1) Ta := (hasDerivAt_id' Ta).const_sub T0
  have := h1.div h2 hne
  unfold G
  convert this using 1
  field_simp
  ring

/-- (1) 逆の関数 g で時刻を読むときの微分。Q(g(y)) = y が q の近くで成り立ち、g は q で連続、
Q は g(q) で微分 Q′ ≠ 0 をもつとする（q = G(T, Ta)）。 -/
theorem reading_derivs {Q g : ℝ → ℝ} {Q' T0 T Ta : ℝ} (hTa : Ta ≠ T0)
    (hg : ContinuousAt g (G T0 T Ta)) (hQ : HasDerivAt Q Q' (g (G T0 T Ta))) (hQ' : Q' ≠ 0)
    (hinv : ∀ᶠ y in 𝓝 (G T0 T Ta), Q (g y) = y) :
    HasDerivAt (fun x => g (G T0 x Ta)) (1 / ((T0 - Ta) * Q')) T ∧
      HasDerivAt (fun a => g (G T0 T a)) (-(1 - G T0 T Ta) / ((T0 - Ta) * Q')) Ta := by
  have hgd : HasDerivAt g Q'⁻¹ (G T0 T Ta) := HasDerivAt.of_local_left_inverse hg hQ hQ' hinv
  have hne : T0 - Ta ≠ 0 := sub_ne_zero.mpr (Ne.symm hTa)
  constructor
  · have := hgd.comp T (hasDerivAt_G_T T0 T Ta)
    rw [show Q'⁻¹ * (1 / (T0 - Ta)) = 1 / ((T0 - Ta) * Q') by
      simp only [div_eq_mul_inv, mul_inv]; ring] at this
    exact this
  · have := hgd.comp Ta (hasDerivAt_G_Ta hTa)
    rw [show Q'⁻¹ * (-(1 - G T0 T Ta) / (T0 - Ta)) = -(1 - G T0 T Ta) / ((T0 - Ta) * Q') by
      simp only [div_eq_mul_inv, mul_inv]; ring] at this
    exact this

/-- 気温の誤差 δa による一次の時刻のずれ |∂t/∂Ta|·δa。 -/
noncomputable def shiftAir (T0 Ta Q Q' δa : ℝ) : ℝ := |(-(1 - Q) / ((T0 - Ta) * Q'))| * δa

/-- 体温の誤差 δT による一次の時刻のずれ |∂t/∂T|·δT。 -/
noncomputable def shiftThermo (T0 Ta Q' δT : ℝ) : ℝ := |1 / ((T0 - Ta) * Q')| * δT

/-- (2) 一次のずれの比は δa(1 − Q)/δT。 -/
theorem shift_ratio {T0 Ta Q Q' δa δT : ℝ} (hTa : Ta ≠ T0) (hQ' : Q' ≠ 0) (hQ : Q ≤ 1)
    (hδT : 0 < δT) :
    shiftAir T0 Ta Q Q' δa / shiftThermo T0 Ta Q' δT = δa * (1 - Q) / δT := by
  have hne : T0 - Ta ≠ 0 := sub_ne_zero.mpr (Ne.symm hTa)
  have hm : (T0 - Ta) * Q' ≠ 0 := mul_ne_zero hne hQ'
  unfold shiftAir shiftThermo
  rw [neg_div, abs_neg, abs_div, abs_div, abs_one, abs_of_nonneg (by linarith : 0 ≤ 1 - Q)]
  have hA : 0 < |(T0 - Ta) * Q'| := abs_pos.mpr hm
  field_simp

/-- (2) 気温の側が温度計の側以上 ⇔ 1 − Q ≥ δT/δa。 -/
theorem overtake_iff {T0 Ta Q Q' δa δT : ℝ} (hTa : Ta ≠ T0) (hQ' : Q' ≠ 0) (hQ : Q ≤ 1)
    (hδa : 0 < δa) :
    shiftThermo T0 Ta Q' δT ≤ shiftAir T0 Ta Q Q' δa ↔ δT / δa ≤ 1 - Q := by
  have hne : T0 - Ta ≠ 0 := sub_ne_zero.mpr (Ne.symm hTa)
  have hm : (T0 - Ta) * Q' ≠ 0 := mul_ne_zero hne hQ'
  have hA : 0 < |(T0 - Ta) * Q'| := abs_pos.mpr hm
  unfold shiftAir shiftThermo
  rw [neg_div, abs_neg, abs_div, abs_div, abs_one, abs_of_nonneg (by linarith : 0 ≤ 1 - Q),
    div_le_iff₀ hδa]
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h hA.le
    rw [← mul_assoc, ← mul_assoc, mul_one_div_cancel (ne_of_gt hA),
      mul_div_cancel₀ _ (ne_of_gt hA)] at this
    linarith
  · intro h
    have h2 : 1 / |(T0 - Ta) * Q'| * δT ≤ 1 / |(T0 - Ta) * Q'| * ((1 - Q) * δa) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    calc 1 / |(T0 - Ta) * Q'| * δT ≤ 1 / |(T0 - Ta) * Q'| * ((1 - Q) * δa) := h2
      _ = (1 - Q) / |(T0 - Ta) * Q'| * δa := by ring

/-! ### ヘンスゲの式 -/

/-- ヘンスゲの式 Q_H(t) = 1.25 e^(Bt) − 0.25 e^(5Bt)。 -/
noncomputable def QH (B t : ℝ) : ℝ := 1.25 * exp (B * t) - 0.25 * exp (5 * B * t)

/-- dQ_H/dt = 1.25 B (e^(Bt) − e^(5Bt))。 -/
noncomputable def dQH (B t : ℝ) : ℝ := 1.25 * B * (exp (B * t) - exp (5 * B * t))

theorem hasDerivAt_QH (B t : ℝ) : HasDerivAt (QH B) (dQH B t) t := by
  have h1 : HasDerivAt (fun s => exp (B * s)) (exp (B * t) * (B * 1)) t :=
    ((hasDerivAt_id' t).const_mul B).exp
  have h2 : HasDerivAt (fun s => exp (5 * B * s)) (exp (5 * B * t) * (5 * B * 1)) t :=
    ((hasDerivAt_id' t).const_mul (5 * B)).exp
  have := (h1.const_mul 1.25).sub (h2.const_mul 0.25)
  unfold QH dQH
  convert this using 1
  ring

theorem QH_zero (B : ℝ) : QH B 0 = 1 := by norm_num [QH]

theorem QH_pos {B t : ℝ} (hB : B < 0) (ht : 0 ≤ t) : 0 < QH B t := by
  unfold QH
  have : exp (5 * B * t) ≤ exp (B * t) := exp_le_exp.mpr (by nlinarith)
  have := exp_pos (5 * B * t)
  linarith

theorem deriv_QH_neg {B t : ℝ} (hB : B < 0) (ht : 0 < t) : dQH B t < 0 := by
  unfold dQH
  have : exp (5 * B * t) < exp (B * t) := exp_lt_exp.mpr (by nlinarith)
  have h2 : 0 < exp (B * t) - exp (5 * B * t) := by linarith
  have : 1.25 * B < 0 := by linarith
  exact mul_neg_of_neg_of_pos this h2

theorem dQH_zero (B : ℝ) : dQH B 0 = 0 := by simp [dQH]

theorem QH_strictAntiOn {B : ℝ} (hB : B < 0) : StrictAntiOn (QH B) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact fun t _ => (hasDerivAt_QH B t).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    rw [(hasDerivAt_QH B t).deriv]
    exact deriv_QH_neg hB ht

/-- 体重は時間の尺度だけを変える：Q_H(B, t) = Q_H(−1, |B|t)。 -/
theorem QH_scale {B : ℝ} (hB : B < 0) (t : ℝ) : QH B t = QH (-1) (|B| * t) := by
  unfold QH
  rw [abs_of_neg hB]
  ring_nf

/-- 傾きの大きさ k(x) = e^(−x) − e^(−5x)（x = |B|t）。 -/
noncomputable def k (x : ℝ) : ℝ := exp (-x) - exp (-5 * x)

theorem hasDerivAt_k (x : ℝ) :
    HasDerivAt k (-exp (-x) + 5 * exp (-5 * x)) x := by
  have h1 := (hasDerivAt_neg x).exp
  have h2 : HasDerivAt (fun y => exp (-5 * y)) (exp (-5 * x) * (-5 * 1)) x :=
    ((hasDerivAt_id' x).const_mul (-5)).exp
  have := h1.sub h2
  unfold k
  convert this using 1
  ring

/-- k′(x) = e^(−5x)(5 − e^(4x))。 -/
theorem k_deriv_eq (x : ℝ) :
    -exp (-x) + 5 * exp (-5 * x) = exp (-5 * x) * (5 - exp (4 * x)) := by
  have : exp (-5 * x) * exp (4 * x) = exp (-x) := by rw [← exp_add]; ring_nf
  rw [mul_sub, this]; ring

theorem x_star_pos : 0 < log 5 / 4 := by
  have : 0 < log 5 := log_pos (by norm_num)
  positivity

theorem exp_four_lt {x : ℝ} (hx : x < log 5 / 4) : exp (4 * x) < 5 := by
  have : 4 * x < log 5 := by linarith
  calc exp (4 * x) < exp (log 5) := exp_lt_exp.mpr this
    _ = 5 := exp_log (by norm_num)

theorem exp_four_gt {x : ℝ} (hx : log 5 / 4 < x) : 5 < exp (4 * x) := by
  have : log 5 < 4 * x := by linarith
  calc (5 : ℝ) = exp (log 5) := (exp_log (by norm_num)).symm
    _ < exp (4 * x) := exp_lt_exp.mpr this

theorem k_strictMonoOn : StrictMonoOn k (Iic (log 5 / 4)) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic _)
  · exact fun x _ => (hasDerivAt_k x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Iic] at hx
    rw [(hasDerivAt_k x).deriv, k_deriv_eq]
    exact mul_pos (exp_pos _) (by linarith [exp_four_lt (mem_Iio.mp hx)])

theorem k_strictAntiOn : StrictAntiOn k (Ici (log 5 / 4)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · exact fun x _ => (hasDerivAt_k x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_k x).deriv, k_deriv_eq]
    exact mul_neg_of_pos_of_neg (exp_pos _) (by linarith [exp_four_gt (mem_Ioi.mp hx)])

theorem k_lt_max {x : ℝ} (hx : x ≠ log 5 / 4) : k x < k (log 5 / 4) := by
  rcases lt_or_gt_of_ne hx with h | h
  · exact k_strictMonoOn (mem_Iic.mpr h.le) (mem_Iic.mpr le_rfl) h
  · exact k_strictAntiOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr h.le) h

theorem abs_dQH {B t : ℝ} (hB : B < 0) (ht : 0 ≤ t) :
    |dQH B t| = 1.25 * |B| * k (|B| * t) := by
  unfold dQH k
  rw [abs_of_neg hB]
  have e1 : -(-B * t) = B * t := by ring
  have e2 : -5 * (-B * t) = 5 * B * t := by ring
  rw [e1, e2]
  have : exp (5 * B * t) ≤ exp (B * t) := exp_le_exp.mpr (by nlinarith)
  rw [abs_of_nonpos (by nlinarith)]; ring

/-- (3) |dQ_H/dt| は t* = ln 5/(4|B|) でただ一つの最大をとる。 -/
theorem steepest {B t : ℝ} (hB : B < 0) (ht0 : 0 ≤ t) (ht : t ≠ log 5 / (4 * |B|)) :
    |dQH B t| < |dQH B (log 5 / (4 * |B|))| := by
  have hBa : 0 < |B| := abs_pos.mpr (ne_of_lt hB)
  have hs : 0 ≤ log 5 / (4 * |B|) := by have := x_star_pos; positivity
  rw [abs_dQH hB ht0, abs_dQH hB hs]
  have hx : |B| * t ≠ log 5 / 4 := by
    intro h; apply ht; field_simp; linarith
  have e : |B| * (log 5 / (4 * |B|)) = log 5 / 4 := by field_simp
  rw [e]
  have := k_lt_max hx
  have : 0 < 1.25 * |B| := by positivity
  nlinarith

/-- (3) 温度計の一次のずれ δT/((T0 − Ta)|Q_H′|) は t* でただ一つの最小をとる（t > 0）。 -/
theorem thermometer_min {B T0 Ta δT t : ℝ} (hB : B < 0) (hT : Ta < T0) (hδT : 0 < δT)
    (ht : 0 < t) (hne : t ≠ log 5 / (4 * |B|)) :
    δT / ((T0 - Ta) * |dQH B (log 5 / (4 * |B|))|) < δT / ((T0 - Ta) * |dQH B t|) := by
  have h1 : 0 < |dQH B t| := abs_pos.mpr (ne_of_lt (deriv_QH_neg hB ht))
  have h2 := steepest hB ht.le hne
  have hd : 0 < T0 - Ta := by linarith
  apply div_lt_div_of_pos_left hδT (by positivity)
  exact mul_lt_mul_of_pos_left h2 hd

/-! ### 平坦部を無視したずれ -/

/-- (4) 同じ B のニュートンの冷却則 e^(Bt_N) = Q_H(t) で読んだ時刻のずれ。 -/
theorem newton_shift {B t : ℝ} (hB : B < 0) (ht : 0 ≤ t) :
    log (QH B t) / B - t = log (1.25 - 0.25 * exp (4 * B * t)) / B := by
  have hpos := QH_pos hB ht
  have hfac : QH B t = exp (B * t) * (1.25 - 0.25 * exp (4 * B * t)) := by
    unfold QH
    rw [show 5 * B * t = B * t + 4 * B * t by ring, exp_add]
    ring
  have hq : 0 < 1.25 - 0.25 * exp (4 * B * t) := by
    have : exp (4 * B * t) ≤ 1 := by rw [exp_le_one_iff]; nlinarith
    linarith
  have hB0 : B ≠ 0 := ne_of_lt hB
  rw [hfac, log_mul (exp_pos _).ne' hq.ne', log_exp]
  field_simp
  ring

theorem newton_shift_tendsto {B : ℝ} (hB : B < 0) :
    Tendsto (fun t => log (1.25 - 0.25 * exp (4 * B * t)) / B) atTop (𝓝 (log 1.25 / B)) := by
  have h1 : Tendsto (fun t => 4 * B * t) atTop atBot := by
    apply tendsto_id.const_mul_atTop_of_neg (by linarith)
  have h2 : Tendsto (fun t => exp (4 * B * t)) atTop (𝓝 0) := tendsto_exp_atBot.comp h1
  have h3 : Tendsto (fun t => 1.25 - 0.25 * exp (4 * B * t)) atTop (𝓝 (1.25 - 0.25 * 0)) :=
    tendsto_const_nhds.sub (h2.const_mul 0.25)
  rw [show (1.25 : ℝ) - 0.25 * 0 = 1.25 by norm_num] at h3
  have h4 := (h3.log (by norm_num)).div_const B
  exact h4

end Paper798

end Yamagishi
