/-
論文455『どこまで乾かすかで、律速が入れ替わる』の格上げ（一般の形）。

原稿（455_yamagishi_how_dry_you_want_it_decides_the_limit/…_jp.tex）は、
定率期 dW/dt = −R（W ≥ W_c）と線形の減率期 dW/dt = −R(W − W_e)/(W_c − W_e)（W < W_c）の模型を
W₀ = 0.60、W_c = 0.20、W_e = 0.02、R = 0.05 毎時の一組で数え、定率期 8 時間、五つの目標での減率期、
入れ替わりの含水率 W× = 0.039506（閉じた式）と、その ±5 % で長短が入れ替わることを示している。
境目がただ一つであることと、R によらないことは、一組の数で見ただけ。

ここで証明した言明（W_e < W_c < W₀、R > 0 のどの値でも）：
  (1) `const_period_of_ode`：dW/dt = −R の解が W₀ から W_c に達した時刻は (W₀ − W_c)/R。
  (2) `falling_time_of_ode`：減率期の方程式の解が W_e より上のまま W_c から W に達した時刻は
      t_f(W) = ((W_c − W_e)/R)·ln((W_c − W_e)/(W − W_e))。微分方程式から直接に導いた。
      `falling_solution`：その解は実際にあり、どの時刻でも W_e より上（平衡には有限の時間で届かない）。
  (3) `tFall_strictAntiOn`：t_f は W について狭義に減る。`tFall_Wc`：t_f(W_c) = 0。
  (4) `Wcross_mem`：W× = W_e + (W_c − W_e)·exp(−(W₀ − W_c)/(W_c − W_e)) は (W_e, W_c) の中にある。
      `falling_longer_iff`・`falling_eq_iff`・`falling_shorter_iff`：目標 W > W_e について、
      減率期が長い ⇔ W < W×、等しい ⇔ W = W×、短い ⇔ W > W×。
  (5) `cross_indep_R`：W× の定義に R は入らず、R を c 倍すると二つの期間はどちらも 1/c 倍になる。
  (6) `removal_time_strictAnti`：同じ量 δ を抜く時間は、乾いているほど（W が小さいほど）長い。
足した仮定：W_e < W_c < W₀、R > 0（模型の仮定は原稿と同じ）。解は区間の端を含めて微分できるとした。
形式化していないもの：表の数値そのもの、浮動小数で残差が消える時刻、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）

In the two-stage drying model (constant rate, then linear falling rate), the falling stage outlasts
the constant stage exactly when the target moisture is below one crossover value, which lies between
the equilibrium and critical moistures and does not depend on the drying rate R.
-/
import Mathlib

namespace Yamagishi

namespace Paper455

open Real Set

/-- 定率期の長さ (W₀ − W_c)/R。 -/
noncomputable def tConst (W0 Wc R : ℝ) : ℝ := (W0 - Wc) / R

/-- 減率期で W_c から W までにかかる時間 ((W_c − W_e)/R)·ln((W_c − W_e)/(W − W_e))。 -/
noncomputable def tFall (Wc We R W : ℝ) : ℝ := (Wc - We) / R * log ((Wc - We) / (W - We))

/-- 二つの期間が等しくなる含水率 W×。 -/
noncomputable def Wcross (W0 Wc We : ℝ) : ℝ := We + (Wc - We) * exp (-((W0 - Wc) / (Wc - We)))

/-- (1) 定率期の長さを微分方程式から導く。 -/
theorem const_period_of_ode {W0 Wc R τ : ℝ} (W : ℝ → ℝ) (hR : 0 < R) (hτ : 0 ≤ τ)
    (hode : ∀ t ∈ Icc 0 τ, HasDerivAt W (-R) t) (h0 : W 0 = W0) (h1 : W τ = Wc) :
    τ = tConst W0 Wc R := by
  set φ : ℝ → ℝ := fun t => W t + R * t
  have hφ : ∀ t ∈ Icc 0 τ, HasDerivAt φ 0 t := by
    intro t ht
    have h2 := (hode t ht).add ((hasDerivAt_id' t).const_mul R)
    convert h2 using 1; ring
  have hcont : ContinuousOn φ (Icc 0 τ) := fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  have hc := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hφ t (Ico_subset_Icc_self ht)).hasDerivWithinAt) τ ⟨hτ, le_refl τ⟩
  simp only [φ, h0, h1, mul_zero, add_zero] at hc
  unfold tConst
  field_simp
  linarith

/-- (2) 減率期の時間を微分方程式から導く：解が W_e より上のまま W_c から W に達したなら、
その時刻は t_f(W)。 -/
theorem falling_time_of_ode {Wc We R τ Wt : ℝ} (W : ℝ → ℝ) (hR : 0 < R) (hec : We < Wc)
    (hτ : 0 ≤ τ) (hpos : ∀ t ∈ Icc 0 τ, We < W t)
    (hode : ∀ t ∈ Icc 0 τ, HasDerivAt W (-(R * (W t - We) / (Wc - We))) t)
    (h0 : W 0 = Wc) (h1 : W τ = Wt) : τ = tFall Wc We R Wt := by
  have hD : 0 < Wc - We := sub_pos.mpr hec
  set φ : ℝ → ℝ := fun t => log (W t - We) + R / (Wc - We) * t
  have hφ : ∀ t ∈ Icc 0 τ, HasDerivAt φ 0 t := by
    intro t ht
    have hx : 0 < W t - We := sub_pos.mpr (hpos t ht)
    have h2 := ((hode t ht).sub_const We).log hx.ne'
    have h3 := h2.add ((hasDerivAt_id' t).const_mul (R / (Wc - We)))
    convert h3 using 1
    field_simp
    ring
  have hcont : ContinuousOn φ (Icc 0 τ) := fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  have hc := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hφ t (Ico_subset_Icc_self ht)).hasDerivWithinAt) τ ⟨hτ, le_refl τ⟩
  simp only [φ, h0, h1, mul_zero, add_zero] at hc
  have hWt : 0 < Wt - We := by rw [← h1]; exact sub_pos.mpr (hpos τ ⟨hτ, le_refl τ⟩)
  unfold tFall
  rw [log_div hD.ne' hWt.ne']
  field_simp
  field_simp at hc
  linarith

/-- (2) 解は実際にある：W(t) = W_e + (W_c − W_e)·exp(−R t/(W_c − W_e)) は方程式を満たし、
W(0) = W_c、どの時刻でも W_e より上、目標 W ∈ (W_e, W_c] には時刻 t_f(W) で達する。 -/
theorem falling_solution {Wc We R : ℝ} (hR : 0 < R) (hec : We < Wc) :
    let S : ℝ → ℝ := fun t => We + (Wc - We) * exp (-(R / (Wc - We)) * t)
    S 0 = Wc ∧ (∀ t, We < S t) ∧ (∀ t, HasDerivAt S (-(R * (S t - We) / (Wc - We))) t) ∧
    (∀ W, We < W → S (tFall Wc We R W) = W) := by
  intro S
  have hD : 0 < Wc - We := sub_pos.mpr hec
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [S]
  · intro t; simp only [S]; have := exp_pos (-(R / (Wc - We)) * t); nlinarith
  · intro t
    have h0 : HasDerivAt (fun t => -(R / (Wc - We)) * t) (-(R / (Wc - We))) t := by
      simpa using (hasDerivAt_id' t).const_mul (-(R / (Wc - We)))
    have h2 := (h0.exp.const_mul (Wc - We)).const_add We
    convert h2 using 1
    simp only [S]
    field_simp
    ring
  · intro W hW
    have hx : 0 < W - We := sub_pos.mpr hW
    simp only [S, tFall]
    have e : -(R / (Wc - We)) * ((Wc - We) / R * log ((Wc - We) / (W - We)))
        = log ((W - We) / (Wc - We)) := by
      rw [log_div hx.ne' hD.ne', log_div hD.ne' hx.ne']
      field_simp
      ring
    rw [e, exp_log (div_pos hx hD)]
    field_simp
    ring

/-- t_f(W_c) = 0。 -/
theorem tFall_Wc (Wc We R : ℝ) (hec : We < Wc) : tFall Wc We R Wc = 0 := by
  have hD : (Wc - We) ≠ 0 := (sub_pos.mpr hec).ne'
  simp [tFall, div_self hD]

/-- (3) t_f は W について狭義に減る（W > W_e の範囲で）。 -/
theorem tFall_strictAntiOn {Wc We R : ℝ} (hR : 0 < R) (hec : We < Wc) :
    StrictAntiOn (tFall Wc We R) (Ioi We) := by
  intro a ha b hb hab
  have hD : 0 < Wc - We := sub_pos.mpr hec
  have hxa : 0 < a - We := sub_pos.mpr ha
  have hxb : 0 < b - We := sub_pos.mpr hb
  unfold tFall
  apply mul_lt_mul_of_pos_left _ (div_pos hD hR)
  rw [log_lt_log_iff (div_pos hD hxb) (div_pos hD hxa)]
  exact div_lt_div_of_pos_left hD hxa (by linarith)

/-- 芯：W > W_e について、K = (W₀ − W_c)/(W_c − W_e) と ln((W_c − W_e)/(W − W_e)) の大小は、
W× と W の大小の逆。 -/
theorem K_lt_log_iff {W0 Wc We W : ℝ} (hec : We < Wc) (hW : We < W) :
    (W0 - Wc) / (Wc - We) < log ((Wc - We) / (W - We)) ↔ W < Wcross W0 Wc We := by
  have hD : 0 < Wc - We := sub_pos.mpr hec
  have hx : 0 < W - We := sub_pos.mpr hW
  set K := (W0 - Wc) / (Wc - We)
  have hX : 0 < Wcross W0 Wc We - We := by
    unfold Wcross; have := exp_pos (-K); simp only [add_sub_cancel_left]; positivity
  have hlogX : log (Wcross W0 Wc We - We) = log (Wc - We) - K := by
    unfold Wcross
    simp only [add_sub_cancel_left]
    rw [log_mul hD.ne' (exp_pos _).ne', log_exp]; ring
  rw [log_div hD.ne' hx.ne']
  have : K < log (Wc - We) - log (W - We) ↔ log (W - We) < log (Wcross W0 Wc We - We) := by
    rw [hlogX]; constructor <;> intro h <;> linarith
  rw [this, log_lt_log_iff hx hX]
  constructor <;> intro h <;> linarith

/-- 同じく等号の場合。 -/
theorem K_eq_log_iff {W0 Wc We W : ℝ} (hec : We < Wc) (hW : We < W) :
    log ((Wc - We) / (W - We)) = (W0 - Wc) / (Wc - We) ↔ W = Wcross W0 Wc We := by
  have hD : 0 < Wc - We := sub_pos.mpr hec
  have hx : 0 < W - We := sub_pos.mpr hW
  set K := (W0 - Wc) / (Wc - We)
  have hX : 0 < Wcross W0 Wc We - We := by
    unfold Wcross; have := exp_pos (-K); simp only [add_sub_cancel_left]; positivity
  have hlogX : log (Wcross W0 Wc We - We) = log (Wc - We) - K := by
    unfold Wcross
    simp only [add_sub_cancel_left]
    rw [log_mul hD.ne' (exp_pos _).ne', log_exp]; ring
  rw [log_div hD.ne' hx.ne']
  constructor
  · intro h
    have h2 : log (W - We) = log (Wcross W0 Wc We - We) := by rw [hlogX]; linarith
    have := log_injOn_pos (mem_Ioi.mpr hx) (mem_Ioi.mpr hX) h2
    linarith
  · intro h
    rw [h, hlogX]; ring

/-- 二つの期間を同じ因子 (W_c − W_e)/R でくくる。 -/
theorem tConst_eq {W0 Wc We R : ℝ} (hec : We < Wc) :
    tConst W0 Wc R = (Wc - We) / R * ((W0 - Wc) / (Wc - We)) := by
  have hD : (Wc - We) ≠ 0 := (sub_pos.mpr hec).ne'
  unfold tConst; field_simp

/-- (4) 減率期のほうが長い ⇔ W < W×。 -/
theorem falling_longer_iff {W0 Wc We R W : ℝ} (hR : 0 < R) (hec : We < Wc) (hW : We < W) :
    tConst W0 Wc R < tFall Wc We R W ↔ W < Wcross W0 Wc We := by
  have hD : 0 < Wc - We := sub_pos.mpr hec
  rw [tConst_eq hec, tFall, ← K_lt_log_iff hec hW]
  exact ⟨fun h => lt_of_mul_lt_mul_left h (div_pos hD hR).le,
    fun h => mul_lt_mul_of_pos_left h (div_pos hD hR)⟩

/-- (4) 二つの期間が等しい ⇔ W = W×。 -/
theorem falling_eq_iff {W0 Wc We R W : ℝ} (hR : 0 < R) (hec : We < Wc) (hW : We < W) :
    tFall Wc We R W = tConst W0 Wc R ↔ W = Wcross W0 Wc We := by
  have hD : 0 < Wc - We := sub_pos.mpr hec
  rw [tConst_eq hec, tFall, mul_right_inj' (div_pos hD hR).ne']
  exact K_eq_log_iff hec hW

/-- (4) 減率期のほうが短い ⇔ W > W×。 -/
theorem falling_shorter_iff {W0 Wc We R W : ℝ} (hR : 0 < R) (hec : We < Wc) (hW : We < W) :
    tFall Wc We R W < tConst W0 Wc R ↔ Wcross W0 Wc We < W := by
  constructor
  · intro h
    rcases lt_trichotomy W (Wcross W0 Wc We) with h1 | h1 | h1
    · exact absurd ((falling_longer_iff hR hec hW).mpr h1) (lt_asymm h)
    · exact absurd ((falling_eq_iff hR hec hW).mpr h1) (ne_of_lt h)
    · exact h1
  · intro h
    rcases lt_trichotomy (tFall Wc We R W) (tConst W0 Wc R) with h1 | h1 | h1
    · exact h1
    · exact absurd ((falling_eq_iff hR hec hW).mp h1) (ne_of_gt h)
    · exact absurd ((falling_longer_iff hR hec hW).mp h1) (lt_asymm h)

/-- (4) W× は (W_e, W_c) の中にある（W₀ > W_c のとき）。 -/
theorem Wcross_mem {W0 Wc We : ℝ} (hec : We < Wc) (hc0 : Wc < W0) :
    We < Wcross W0 Wc We ∧ Wcross W0 Wc We < Wc := by
  have hD : 0 < Wc - We := sub_pos.mpr hec
  have hK : 0 < (W0 - Wc) / (Wc - We) := div_pos (sub_pos.mpr hc0) hD
  have h1 : exp (-((W0 - Wc) / (Wc - We))) < 1 := exp_lt_one_iff.mpr (by linarith)
  have h0 := exp_pos (-((W0 - Wc) / (Wc - We)))
  unfold Wcross
  constructor <;> nlinarith

/-- (5) W× は R を含まず、R を c 倍すると二つの期間はどちらも 1/c 倍になる。 -/
theorem cross_indep_R (W0 Wc We R c W : ℝ) :
    tConst W0 Wc (c * R) = tConst W0 Wc R / c ∧ tFall Wc We (c * R) W = tFall Wc We R W / c := by
  unfold tConst tFall
  constructor
  · rw [div_div, mul_comm R c]
  · ring

/-- (6) 同じ量 δ > 0 を W から抜く時間 t_f(W − δ) − t_f(W) は、W が小さいほど長い。 -/
theorem removal_time_strictAnti {Wc We R δ a b : ℝ} (hR : 0 < R) (hec : We < Wc) (hδ : 0 < δ)
    (ha : We < a - δ) (hab : a < b) :
    tFall Wc We R (b - δ) - tFall Wc We R b < tFall Wc We R (a - δ) - tFall Wc We R a := by
  have hD : 0 < Wc - We := sub_pos.mpr hec
  have hb : We < b - δ := by linarith
  have pa : 0 < a - δ - We := by linarith
  have pa' : 0 < a - We := by linarith
  have pb : 0 < b - δ - We := by linarith
  have pb' : 0 < b - We := by linarith
  have key : ∀ x y : ℝ, 0 < x - We → 0 < y - We →
      tFall Wc We R x - tFall Wc We R y = (Wc - We) / R * log ((y - We) / (x - We)) := by
    intro x y hx hy
    unfold tFall
    rw [← mul_sub, log_div hD.ne' hx.ne', log_div hD.ne' hy.ne', log_div hy.ne' hx.ne']
    ring
  rw [key _ _ pb pb', key _ _ pa pa']
  apply mul_lt_mul_of_pos_left _ (div_pos hD hR)
  rw [log_lt_log_iff (div_pos pb' pb) (div_pos pa' pa), div_lt_div_iff₀ pb pa]
  nlinarith

end Paper455

end Yamagishi
