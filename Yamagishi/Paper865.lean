/-
論文865『一つの分子が空に居る時間と、足した分が消える時間は別である』の格上げ（一般の形）。

日本語の一文：大気と相手の箱を一次の速さ k1・k2・ks でつないだ線形の模型では、どの正の値でも、足した
余分の遅い減りの速さ λs は k1ks/(k1 + k2 + ks) < λs < k1ks/(k1 + k2) を満たし、速い減りの速さは
max(k1 + k2, ks) より大きく、余分は分子の滞在から見込む e^(−k1t) よりいつも多く残る。
English: In the linear two-box model with first-order rates k1, k2, ks > 0, the slow decay rate of
an added excess satisfies k1ks/(k1 + k2 + ks) < λs < k1ks/(k1 + k2) (so λs < min(k1, ks)), the fast
rate exceeds max(k1 + k2, ks), and the excess in the air always stays above e^(−k1t).

原稿（865_yamagishi_molecule_time_is_not_excess_time/…_jp.tex）は、k1 = 0.25、k2 = k1/3、ks = 0 と
0.002 の二通りで、4・20・100 年後の余分、閉じた箱の厳密な解 1/4 + (3/4)e^(−(k1+k2)t)、出口つきの
二つの時定数（2.995486 年・667.671180 年）と遅いほうの係数 0.252260 を、式とルンゲ＝クッタで出している。
時定数の上下の限界は書いていない。

ここで証明した言明（k1, k2, ks > 0。S = k1 + k2 + ks、P = k1ks、p(λ) = λ² − Sλ + P）：
  (1) `disc_pos`：p の判別式は正。λs < λf を p の二つの根とする（`p_lamS`・`p_lamF`）。
      `eigvec`：p(λ) = 0 なら (k2, k1 − λ)e^(−λt) は模型の式の解（λ は減りの速さ）。
  (2) `solution`：はじめに大気にだけ余分 1 を置いた解は
      A(t) = ((λf − k1)e^(−λs t) + (k1 − λs)e^(−λf t))/(λf − λs)、
      O(t) = k1(e^(−λs t) − e^(−λf t))/(λf − λs) で、模型の式とはじめの値を満たす。
      `slow_coeff_pos`：遅いほうの係数 (λf − k1)/(λf − λs) は 0 と 1 のあいだ。
  (3) `slow_bounds`：k1ks/(k1 + k2 + ks) < λs < k1ks/(k1 + k2)。`slow_lt_min`：λs < k1、λs < ks。
      `fast_bounds`：λf > k1 + k2、λf > ks。
      `slow_time_bounds`：遅い時定数 1/λs は 1/k1 より、1/ks より、(1 + k2/k1)/ks より長い。
  (4) `paper_slow_time`：原稿の一組で遅い時定数は 666.66 年と 670.67 年のあいだ（原稿 667.671180 年）。
      `excess_gt_molecule`：t > 0 で A(t) > e^(−k1t)（余分は分子の滞在から見込むより多く残る）。
  (5) `closed_box`：ks = 0 なら A(t) = k2/(k1 + k2) + (k1/(k1 + k2))e^(−(k1+k2)t) が模型の解で、
      余分の k2/(k1 + k2) は消えずに残る（減りの時定数 1/(k1 + k2) は 1/k1 より短い）。
足した仮定：一次の線形の箱が二つで、はじめの余分を大気にだけ置く（原稿と同じ）。模型の式は
dA/dt = −k1A + k2O、dO/dt = k1A − (k2 + ks)O として定義に置いた（解がこれ一つであることは
形式化していない）。
形式化していないもの：原稿の数表（667.671180 年などの数値）、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper865

open Real

variable {k1 k2 ks : ℝ}

/-- 特性多項式 p(λ) = λ² − (k1 + k2 + ks)λ + k1ks。 -/
def p (k1 k2 ks x : ℝ) : ℝ := x ^ 2 - (k1 + k2 + ks) * x + k1 * ks

/-- 判別式 Δ = (k1 + k2 + ks)² − 4k1ks。 -/
def disc (k1 k2 ks : ℝ) : ℝ := (k1 + k2 + ks) ^ 2 - 4 * k1 * ks

theorem disc_pos (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 ≤ ks) : 0 < disc k1 k2 ks := by
  unfold disc
  nlinarith [sq_nonneg (k1 - ks)]

/-- 遅い根 λs と速い根 λf。 -/
noncomputable def lamS (k1 k2 ks : ℝ) : ℝ := ((k1 + k2 + ks) - √(disc k1 k2 ks)) / 2
noncomputable def lamF (k1 k2 ks : ℝ) : ℝ := ((k1 + k2 + ks) + √(disc k1 k2 ks)) / 2

theorem sqrt_disc_sq (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 ≤ ks) :
    √(disc k1 k2 ks) ^ 2 = disc k1 k2 ks := sq_sqrt (disc_pos h1 h2 hs).le

theorem p_factor (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 ≤ ks) (x : ℝ) :
    p k1 k2 ks x = (x - lamS k1 k2 ks) * (x - lamF k1 k2 ks) := by
  have := sqrt_disc_sq h1 h2 hs
  unfold p lamS lamF
  unfold disc at this ⊢
  nlinarith [this]

theorem p_lamS (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 ≤ ks) : p k1 k2 ks (lamS k1 k2 ks) = 0 := by
  rw [p_factor h1 h2 hs]; ring

theorem p_lamF (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 ≤ ks) : p k1 k2 ks (lamF k1 k2 ks) = 0 := by
  rw [p_factor h1 h2 hs]; ring

theorem lamS_lt_lamF (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 ≤ ks) :
    lamS k1 k2 ks < lamF k1 k2 ks := by
  have := Real.sqrt_pos.mpr (disc_pos h1 h2 hs)
  unfold lamS lamF; linarith

theorem vieta_sum (k1 k2 ks : ℝ) : lamS k1 k2 ks + lamF k1 k2 ks = k1 + k2 + ks := by
  unfold lamS lamF; ring

theorem vieta_prod (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 ≤ ks) :
    lamS k1 k2 ks * lamF k1 k2 ks = k1 * ks := by
  have := sqrt_disc_sq h1 h2 hs
  have hd : disc k1 k2 ks = (k1 + k2 + ks) ^ 2 - 4 * k1 * ks := rfl
  unfold lamS lamF
  nlinarith [this, hd]

/-- p(x) < 0 なら x は二つの根のあいだ。 -/
theorem between_of_p_neg (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 ≤ ks) {x : ℝ}
    (hx : p k1 k2 ks x < 0) : lamS k1 k2 ks < x ∧ x < lamF k1 k2 ks := by
  rw [p_factor h1 h2 hs] at hx
  have hlt := lamS_lt_lamF h1 h2 hs
  constructor
  · by_contra hc; push Not at hc
    have : 0 ≤ (x - lamS k1 k2 ks) * (x - lamF k1 k2 ks) := by nlinarith
    linarith
  · by_contra hc; push Not at hc
    have : 0 ≤ (x - lamS k1 k2 ks) * (x - lamF k1 k2 ks) := by nlinarith
    linarith

theorem p_k1 : p k1 k2 ks k1 = -(k1 * k2) := by unfold p; ring
theorem p_ks : p k1 k2 ks ks = -(k2 * ks) := by unfold p; ring
theorem p_k12 : p k1 k2 ks (k1 + k2) = -(k2 * ks) := by unfold p; ring

theorem p_cks (h1 : 0 < k1) (h2 : 0 < k2) :
    p k1 k2 ks (k1 * ks / (k1 + k2)) =
      -(k1 / (k1 + k2)) * (1 - k1 / (k1 + k2)) * ks ^ 2 := by
  have : k1 + k2 ≠ 0 := by linarith
  unfold p
  field_simp
  ring

/-- (3) 遅い根の上下の限界。 -/
theorem slow_bounds (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 < ks) :
    k1 * ks / (k1 + k2 + ks) < lamS k1 k2 ks ∧ lamS k1 k2 ks < k1 * ks / (k1 + k2) := by
  have hc : 0 < k1 / (k1 + k2) := by positivity
  have hc1 : k1 / (k1 + k2) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hneg : p k1 k2 ks (k1 * ks / (k1 + k2)) < 0 := by
    rw [p_cks h1 h2]
    have : 0 < k1 / (k1 + k2) * (1 - k1 / (k1 + k2)) * ks ^ 2 := by
      apply mul_pos (mul_pos hc (by linarith)) (by positivity)
    linarith
  refine ⟨?_, (between_of_p_neg h1 h2 hs.le hneg).1⟩
  -- λs = P/λf、λf < S
  have hS := vieta_sum k1 k2 ks
  have hP := vieta_prod h1 h2 hs.le
  have hsl : 0 < lamS k1 k2 ks := by
    by_contra hc; push Not at hc
    have : lamS k1 k2 ks * lamF k1 k2 ks ≤ 0 := by
      have hf : 0 < lamF k1 k2 ks := by
        have := (between_of_p_neg h1 h2 hs.le (show p k1 k2 ks k1 < 0 by
          rw [p_k1]; nlinarith)).2
        linarith
      nlinarith
    nlinarith
  have hf : lamF k1 k2 ks < k1 + k2 + ks := by linarith
  have hf0 : 0 < lamF k1 k2 ks := by linarith [lamS_lt_lamF h1 h2 hs.le]
  rw [div_lt_iff₀ (by linarith)]
  rw [← hP]
  exact mul_lt_mul_of_pos_left hf hsl

theorem slow_lt_min (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 < ks) :
    lamS k1 k2 ks < k1 ∧ lamS k1 k2 ks < ks := by
  have a := (between_of_p_neg h1 h2 hs.le (show p k1 k2 ks k1 < 0 by rw [p_k1]; nlinarith)).1
  have b := (between_of_p_neg h1 h2 hs.le (show p k1 k2 ks ks < 0 by rw [p_ks]; nlinarith)).1
  exact ⟨a, b⟩

theorem fast_bounds (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 < ks) :
    k1 + k2 < lamF k1 k2 ks ∧ ks < lamF k1 k2 ks := by
  have a := (between_of_p_neg h1 h2 hs.le (show p k1 k2 ks (k1 + k2) < 0 by
    rw [p_k12]; nlinarith)).2
  have b := (between_of_p_neg h1 h2 hs.le (show p k1 k2 ks ks < 0 by rw [p_ks]; nlinarith)).2
  exact ⟨a, b⟩

theorem lamS_pos (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 < ks) : 0 < lamS k1 k2 ks := by
  have := (slow_bounds h1 h2 hs).1
  have : 0 < k1 * ks / (k1 + k2 + ks) := by positivity
  linarith

/-- (3) 遅い時定数は 1/k1、1/ks、(1 + k2/k1)/ks のどれよりも長い。 -/
theorem slow_time_bounds (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 < ks) :
    1 / k1 < 1 / lamS k1 k2 ks ∧ 1 / ks < 1 / lamS k1 k2 ks ∧
      (1 + k2 / k1) / ks < 1 / lamS k1 k2 ks := by
  have hp := lamS_pos h1 h2 hs
  obtain ⟨a, b⟩ := slow_lt_min h1 h2 hs
  have c := (slow_bounds h1 h2 hs).2
  refine ⟨one_div_lt_one_div_of_lt hp a, one_div_lt_one_div_of_lt hp b, ?_⟩
  have e : (1 + k2 / k1) / ks = 1 / (k1 * ks / (k1 + k2)) := by
    field_simp
  rw [e]
  exact one_div_lt_one_div_of_lt hp c

/-! ### 模型の式と解 -/

/-- 模型の式の右辺。 -/
def rhsA (k1 k2 : ℝ) (A O : ℝ) : ℝ := -k1 * A + k2 * O
def rhsO (k1 k2 ks : ℝ) (A O : ℝ) : ℝ := k1 * A - (k2 + ks) * O

/-- (1) p(λ) = 0 なら (k2, k1 − λ)e^(−λt) は解。 -/
theorem eigvec {lam : ℝ} (hp : p k1 k2 ks lam = 0) (t : ℝ) :
    HasDerivAt (fun s => k2 * exp (-lam * s))
        (rhsA k1 k2 (k2 * exp (-lam * t)) ((k1 - lam) * exp (-lam * t))) t ∧
      HasDerivAt (fun s => (k1 - lam) * exp (-lam * s))
        (rhsO k1 k2 ks (k2 * exp (-lam * t)) ((k1 - lam) * exp (-lam * t))) t := by
  have hd : HasDerivAt (fun s => exp (-lam * s)) (exp (-lam * t) * (-lam * 1)) t :=
    ((hasDerivAt_id' t).const_mul (-lam)).exp
  unfold p at hp
  constructor
  · convert hd.const_mul k2 using 1
    unfold rhsA; ring
  · convert hd.const_mul (k1 - lam) using 1
    unfold rhsO
    have : (k1 * k2 - (k2 + ks) * (k1 - lam)) = -lam * (k1 - lam) := by nlinarith
    linear_combination exp (-lam * t) * this

/-- (2) はじめに大気にだけ余分 1 を置いた解。 -/
noncomputable def solA (k1 k2 ks t : ℝ) : ℝ :=
  ((lamF k1 k2 ks - k1) * exp (-lamS k1 k2 ks * t) +
    (k1 - lamS k1 k2 ks) * exp (-lamF k1 k2 ks * t)) / (lamF k1 k2 ks - lamS k1 k2 ks)

noncomputable def solO (k1 k2 ks t : ℝ) : ℝ :=
  k1 * (exp (-lamS k1 k2 ks * t) - exp (-lamF k1 k2 ks * t)) /
    (lamF k1 k2 ks - lamS k1 k2 ks)

/-- 解の形の芯：a + b = k1 + k2 + ks、ab = k1ks、a ≠ b なら、この二つの式は模型の解。 -/
theorem sol_core {a b : ℝ} (hab : a ≠ b) (hS : a + b = k1 + k2 + ks) (hP : a * b = k1 * ks)
    (t : ℝ) :
    HasDerivAt (fun s => ((b - k1) * exp (-a * s) + (k1 - a) * exp (-b * s)) / (b - a))
        (rhsA k1 k2 (((b - k1) * exp (-a * t) + (k1 - a) * exp (-b * t)) / (b - a))
          (k1 * (exp (-a * t) - exp (-b * t)) / (b - a))) t ∧
      HasDerivAt (fun s => k1 * (exp (-a * s) - exp (-b * s)) / (b - a))
        (rhsO k1 k2 ks (((b - k1) * exp (-a * t) + (k1 - a) * exp (-b * t)) / (b - a))
          (k1 * (exp (-a * t) - exp (-b * t)) / (b - a))) t := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have ha : HasDerivAt (fun s => exp (-a * s)) (exp (-a * t) * (-a * 1)) t :=
    ((hasDerivAt_id' t).const_mul (-a)).exp
  have hb : HasDerivAt (fun s => exp (-b * s)) (exp (-b * t) * (-b * 1)) t :=
    ((hasDerivAt_id' t).const_mul (-b)).exp
  constructor
  · have := ((ha.const_mul (b - k1)).add (hb.const_mul (k1 - a))).div_const (b - a)
    convert this using 1
    unfold rhsA
    generalize exp (-a * t) = ea
    generalize exp (-b * t) = eb
    rw [eq_div_iff hne]
    field_simp
    linear_combination (eb - ea) * (k1 * hS - hP)
  · have := ((ha.sub hb).const_mul k1).div_const (b - a)
    convert this using 1
    unfold rhsO
    generalize exp (-a * t) = ea
    generalize exp (-b * t) = eb
    rw [eq_div_iff hne]
    field_simp
    linear_combination (ea - eb) * k1 * hS

theorem solution (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 ≤ ks) (t : ℝ) :
    solA k1 k2 ks 0 = 1 ∧ solO k1 k2 ks 0 = 0 ∧
      HasDerivAt (solA k1 k2 ks) (rhsA k1 k2 (solA k1 k2 ks t) (solO k1 k2 ks t)) t ∧
      HasDerivAt (solO k1 k2 ks) (rhsO k1 k2 ks (solA k1 k2 ks t) (solO k1 k2 ks t)) t := by
  have hlt := lamS_lt_lamF h1 h2 hs
  have hne : lamF k1 k2 ks - lamS k1 k2 ks ≠ 0 := by linarith
  have hc := sol_core (ne_of_lt hlt) (vieta_sum k1 k2 ks) (vieta_prod h1 h2 hs) t
  refine ⟨?_, ?_, hc.1, hc.2⟩
  · unfold solA
    simp only [mul_zero, exp_zero, mul_one]
    rw [div_eq_one_iff_eq hne]; ring
  · unfold solO; simp

/-- (2) 遅いほうの係数は 0 と 1 のあいだ。 -/
theorem slow_coeff_pos (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 ≤ ks) :
    0 < (lamF k1 k2 ks - k1) / (lamF k1 k2 ks - lamS k1 k2 ks) ∧
      (lamF k1 k2 ks - k1) / (lamF k1 k2 ks - lamS k1 k2 ks) < 1 := by
  have hb := between_of_p_neg h1 h2 hs (show p k1 k2 ks k1 < 0 by rw [p_k1]; nlinarith)
  have hd : 0 < lamF k1 k2 ks - lamS k1 k2 ks := by linarith
  constructor
  · exact div_pos (by linarith) hd
  · rw [div_lt_one hd]; linarith

/-- O(t) > 0（t > 0）。 -/
theorem solO_pos (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 ≤ ks) {t : ℝ} (ht : 0 < t) :
    0 < solO k1 k2 ks t := by
  have hlt := lamS_lt_lamF h1 h2 hs
  unfold solO
  apply div_pos _ (by linarith)
  apply mul_pos h1
  have : exp (-lamF k1 k2 ks * t) < exp (-lamS k1 k2 ks * t) := exp_lt_exp.mpr (by nlinarith)
  linarith

/-- (4) t > 0 で A(t) > e^(−k1t)。 -/
theorem excess_gt_molecule (h1 : 0 < k1) (h2 : 0 < k2) (hs : 0 ≤ ks) {t : ℝ} (ht : 0 < t) :
    exp (-k1 * t) < solA k1 k2 ks t := by
  -- F(s) = A(s) e^(k1 s) は狭義に増える
  set F := fun s => solA k1 k2 ks s * exp (k1 * s) with hF
  have hderiv : ∀ s, HasDerivAt F (k2 * solO k1 k2 ks s * exp (k1 * s)) s := by
    intro s
    have hA := (solution h1 h2 hs s).2.2.1
    have he : HasDerivAt (fun s => exp (k1 * s)) (exp (k1 * s) * (k1 * 1)) s :=
      ((hasDerivAt_id' s).const_mul k1).exp
    have := hA.mul he
    convert this using 1
    unfold rhsA; ring
  have hmono : StrictMonoOn F (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun s _ => (hderiv s).continuousAt.continuousWithinAt
    · intro s hs'
      rw [interior_Ici] at hs'
      rw [(hderiv s).deriv]
      exact mul_pos (mul_pos h2 (solO_pos h1 h2 hs hs')) (exp_pos _)
  have h0 : F 0 = 1 := by simp [hF, (solution h1 h2 hs 0).1]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht.le) ht
  rw [h0] at this
  simp only [hF] at this
  have he : exp (-k1 * t) * exp (k1 * t) = 1 := by rw [← exp_add]; simp
  have hpos := exp_pos (k1 * t)
  nlinarith

/-- (5) 閉じた箱（ks = 0）の解。 -/
theorem closed_box (h1 : 0 < k1) (h2 : 0 < k2) (t : ℝ) :
    HasDerivAt (fun s => k2 / (k1 + k2) + k1 / (k1 + k2) * exp (-(k1 + k2) * s))
      (rhsA k1 k2 (k2 / (k1 + k2) + k1 / (k1 + k2) * exp (-(k1 + k2) * t))
        (k1 / (k1 + k2) - k1 / (k1 + k2) * exp (-(k1 + k2) * t))) t ∧
    HasDerivAt (fun s => k1 / (k1 + k2) - k1 / (k1 + k2) * exp (-(k1 + k2) * s))
      (rhsO k1 k2 0 (k2 / (k1 + k2) + k1 / (k1 + k2) * exp (-(k1 + k2) * t))
        (k1 / (k1 + k2) - k1 / (k1 + k2) * exp (-(k1 + k2) * t))) t ∧
    k2 / (k1 + k2) + k1 / (k1 + k2) * exp (-(k1 + k2) * 0) = 1 ∧
    (k2 / (k1 + k2) < k2 / (k1 + k2) + k1 / (k1 + k2) * exp (-(k1 + k2) * t)) ∧
    1 / (k1 + k2) < 1 / k1 := by
  have hne : k1 + k2 ≠ 0 := by linarith
  have hd : HasDerivAt (fun s => exp (-(k1 + k2) * s))
      (exp (-(k1 + k2) * t) * (-(k1 + k2) * 1)) t :=
    ((hasDerivAt_id' t).const_mul (-(k1 + k2))).exp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := (hd.const_mul (k1 / (k1 + k2))).const_add (k2 / (k1 + k2))
    convert this using 1
    unfold rhsA; field_simp; ring
  · have := (hd.const_mul (k1 / (k1 + k2))).const_sub (k1 / (k1 + k2))
    convert this using 1
    unfold rhsO; field_simp; ring
  · simp only [mul_zero, exp_zero, mul_one]
    rw [← add_div, div_eq_one_iff_eq hne]; ring
  · have : 0 < k1 / (k1 + k2) * exp (-(k1 + k2) * t) := by positivity
    linarith
  · exact one_div_lt_one_div_of_lt h1 (by linarith)

/-- 原稿の一組（k1 = 0.25、k2 = k1/3、ks = 0.002）で、遅い時定数は 666.66 年と 670.67 年のあいだ
（原稿の 667.671180 年）。 -/
theorem paper_slow_time :
    (666.66 : ℝ) < 1 / lamS 0.25 (0.25 / 3) 0.002 ∧ 1 / lamS 0.25 (0.25 / 3) 0.002 < 670.67 := by
  obtain ⟨h1, h2⟩ := slow_bounds (k1 := 0.25) (k2 := 0.25 / 3) (ks := 0.002)
    (by norm_num) (by norm_num) (by norm_num)
  have hp : 0 < lamS 0.25 (0.25 / 3) 0.002 := lamS_pos (by norm_num) (by norm_num) (by norm_num)
  norm_num at h1 h2
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith


end Paper865

end Yamagishi
